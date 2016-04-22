package be.ucl.info.ingi1122.highlight.gui;

import java.awt.Component;
import java.util.ArrayList;

import javax.swing.JList;
import javax.swing.JTextField;
import javax.swing.ListCellRenderer;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Highlighter;

import be.ucl.info.ingi1122.highlight.tools.Portion;
import be.ucl.info.ingi1122.highlight.tools.Tools;

@SuppressWarnings("serial")
public class HighlightCellRenderer extends JTextField implements ListCellRenderer<String> {

	private final JTextField text;
	
	public HighlightCellRenderer(JTextField text) {
		this.text = text;
		//setOpaque(true);
		//setEnabled(false);
		setEditable(false);
		setHighlighter(new DefaultHighlighter());
		setBorder(null);
	}

	@Override
	public Component getListCellRendererComponent(
			JList<? extends String> list, String value, int index,
			boolean isSelected, boolean cellHasFocus) {

		setText(value);

		Highlighter.HighlightPainter painter = new DefaultHighlighter.DefaultHighlightPainter(getSelectionColor());
		
		ArrayList<char[]> mots = new ArrayList<>();
		for (String mot : text.getText().split(" ")) {
			if (!mot.isEmpty()){
				mots.add(mot.toCharArray());
			}
		} 
		Portion[] matches = Tools.quoiSurligner(value.toCharArray(), mots.toArray(new char[mots.size()][]));
		try {
			int check = -1;
			for (Portion i : matches) {
				assert i.getBegin() > check : "Votre liste de portions devrait être triée.";
				assert i.getEnd() > i.getBegin() : "Votre portion est étrange, ou vide.";
				assert text.getText().length() >= i.getEnd() : "Votre portion dépasse du texte, étrange...";
				check = i.getEnd();
				getHighlighter().addHighlight(i.getBegin(), i.getEnd(), painter);
			}
		} catch (BadLocationException ble) {
			System.out.println(ble.getMessage());
		}

		return this;
	}

}