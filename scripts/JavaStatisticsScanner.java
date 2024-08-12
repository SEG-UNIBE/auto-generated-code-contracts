package de.ubt.ai1.mvmt.util;

import java.util.*;



import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.FileVisitResult;
import java.nio.file.FileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.LinkedList;
import java.util.List;

/**
*
* The JavaStatisticsScanner can analyze a given directory and count the number of lines of code, words, characters in Java files.
* Furthermore, it can count the number of OpenJML pre- and postconditions. 
*
* @author Sandra Greiner
*
*/
public class JavaStatisticsScanner {

	public static void main(String[] args) throws FileNotFoundException {

	    if (args.length <= 0){
         	   System.out.println( "please specify the path of the project that should be analysed relative from to where this file is executed as argument");
            return;
        }

		List<String> mvFiles = extractFilesFromPath(args[0]);//new LinkedList<String>();
		// get multi-variant source files

		long lineCT = 0;
		long annotationCt = 0;

		for (String f : mvFiles) {
			File file = new File(f);
			Scanner in = new Scanner(file);

			int words = 0;
			int lines = 0;
			int chars = 0;
			int ensures = 0;
			int requires = 0;

			String res = "";

			while (in.hasNextLine()) {
				res = in.nextLine();
				if (res.length() > 0)
					lines++;
				String[] wordArray = res.split(" ");
				for (String s : wordArray) {
					if (s.length() > 1)
						words++;
					chars += s.length();
				}
				if (res.startsWith("//@ ensures"))
                    ensures++;
                else if (res.startsWith("//@ requires"))
                    requires++;
			}

			lineCT += lines;
			annotationCt += (ensures+requires);
			in.close();
		}
		System.out.println(" ##################  Summary  ################## " + lineCT);
		System.out.println("Number of lines: " + lineCT);
		System.out.println("Number of annotations: " + (annotationCt));

	}

	public static List<String> extractFilesFromPath(String path) {

		List<String> mvFiles = new LinkedList<String>();
		// get multi-variant source files
		FileIterator<Path> fiMV = new FileIterator<Path>();
		try {
			Files.walkFileTree(Paths.get(path), fiMV);
        } catch (IOException e) {
			e.printStackTrace();
		}
		// store the java-files
		for (Path srcFile : fiMV.getRegFiles()) {
			String fileName = srcFile.getFileName().toString();
			if (fileName.lastIndexOf(".") > -1 && fileName.substring(fileName.lastIndexOf(".")).equals(".java")) {
				mvFiles.add(srcFile.toString());
			}
		}
		return mvFiles;
	}

	static class FileIterator<Path> implements FileVisitor<Path> {
        private List<Path> regFiles = new LinkedList<Path>();

        @Override
        public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
                return FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult visitFile(Path file, BasicFileAttributes attr) throws IOException {
            if (attr.isSymbolicLink()) {
                    System.out.format("Symbolic link: %s ", file);
                } else if (attr.isRegularFile()) {
                    regFiles.add(file);
                } else {
                    System.out.format("Other: %s ", file);
                }
                System.out.println("(" + attr.size() + "bytes)");

                return FileVisitResult.CONTINUE;

        }


        public List<Path> getRegFiles() {
            return regFiles;
        }

        public URL[] getFileURIs() {
            URL[] list = new URL[regFiles.size()];
            for (int i = 0; i < regFiles.size(); i++) {
                Path p = regFiles.get(i);
                try {
                    list[i] = new URL(p.toString());
                } catch (MalformedURLException e) {
                    e.printStackTrace();
                }
            }

            return list;
        }

        @Override
        public FileVisitResult visitFileFailed(Path file, IOException exc) throws IOException {
            return FileVisitResult.CONTINUE;
        }
        @Override
        public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
            return FileVisitResult.CONTINUE;
        }
    }
}
