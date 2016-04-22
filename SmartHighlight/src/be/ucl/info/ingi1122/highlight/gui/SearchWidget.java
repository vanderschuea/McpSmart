package be.ucl.info.ingi1122.highlight.gui;

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import javax.swing.DefaultListModel;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;

import be.ucl.info.ingi1122.highlight.tools.Tools;


public class SearchWidget {

  public static void main(String args[]) {
    final JFrame frame = new JFrame("Smart highlight");
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    final Container contentPane = frame.getContentPane();
    
    // * The text field *
    final JTextField text = new JTextField();
    contentPane.add(text, BorderLayout.NORTH);

    // * The list box *
    // The list needs a model...
    final DefaultListModel<String> source = new DefaultListModel<String>();
    loadFile(source);
    // ... filtered according to the content of the textbox.
    final FilteredListModel<String> filteredListModel = new FilteredListModel<String>(source);
    
    // The list itself...
    final JList<String> list = new JList<String>(filteredListModel);
    filteredListModel.setFilter(new FilteredListModel.Filter<String>() {
        public boolean accept(String element) {
        	ArrayList<char[]> mots = new ArrayList<>();
    		for (String mot : text.getText().split(" ")) {
    			if (!mot.isEmpty()){
    				mots.add(mot.toCharArray());
    			}
    		} 
            return Tools.correspond(element.toCharArray(), mots.toArray(new char[mots.size()][]));
        }
    });
    list.setCellRenderer(new HighlightCellRenderer(text));
    // ...wrapped in a scroll pane.
    final JScrollPane listScroller = new JScrollPane(list);
    contentPane.add(listScroller, BorderLayout.CENTER);
    
    // * COnnect the events *
    // Update the list on text changes.
    text.getDocument().addDocumentListener(new DocumentListener() {
		public void removeUpdate(DocumentEvent e)  { filteredListModel.update(); }
		public void insertUpdate(DocumentEvent e)  { filteredListModel.update(); }
		public void changedUpdate(DocumentEvent e) { filteredListModel.update(); }
	});
    
    text.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) { 
			source.addElement(text.getText());
			text.setText("");
		}
	});
    
    source.addListDataListener(new ListDataListener() {
		public void intervalRemoved(ListDataEvent e) { saveFile(source); }
		public void intervalAdded(ListDataEvent e)   { saveFile(source); }
		public void contentsChanged(ListDataEvent e) { saveFile(source); }
	});

    frame.pack();
    frame.setSize(300, 400);
    frame.setLocationRelativeTo(null);
    frame.setVisible(true);
  }
  
  static void loadFile(DefaultListModel<String> model) {
	  List<String> lines = Arrays.asList(
		"cheval",
	    "valise",
	    "chevalise",
	    "tata",
	    "tatatatata",
	    "tataatat",
	    "tatamoppop",
	    "taratata"
	  );
	  try {
		  lines = Files.readAllLines(Paths.get("lines.txt"), Charset.forName("UTF-8"));
	  } catch (IOException e) {
		  System.err.println(e.getLocalizedMessage());
	  }
	  lines = new ArrayList<String>(new HashSet<String>(lines));
	  for (String line : lines) {
		  model.addElement(line);
	  }
  }
  
  static void saveFile(DefaultListModel<String> model) {
	  try {
		  Files.write(Paths.get("lines.txt"),
				  Collections.list(model.elements()),
				  Charset.forName("UTF-8"));
	  } catch ( IOException e ) {
		  System.err.println(e.getLocalizedMessage());
	  }
  }
  
}