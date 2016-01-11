# Project Name

Open Source Project – Improve Bixie Accuracy

# Installation

(1) Down load the BIXIE source code from https://github.com/martinschaef/bixie

(2) Replace the bixie/src with the src directory

(3) To compile: ./gradlew jar

(4) To run: 
			cd build/libs/

			wget http://martinschaef.github.io/bixie/Demo.java

			mkdir classes

			javac Demo.java -d classes/

			java -Xms2g -Xss4m -jar bixie.jar -j classes/

## Work

All my work is located at bixie/src/main/java/bixie/checker/inconsistency_checker/MyChecker.java

Software testing tool to detect inconsistencies in Java code

1.Aimed to handle more inconsistent Java code cases to improve accuracy

2.Implemented symbolic execution to detect unreachable codes

3.Evaluated and compared cases coverage of Bixie with modified code

## License

Weijie Huo