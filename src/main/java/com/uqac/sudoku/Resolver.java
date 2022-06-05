package com.uqac.sudoku;

import org.sat4j.pb.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ISolver;
import stev.booleans.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Resolver {
    /**
     * 5 3 4 | 6 7 8 | 9 1 2
     * 6 7 2 | 1 9 5 | 3 4 8
     * 1 9 8 | 3 4 2 | 5 6 7
     * ======+=======+======
     * 8 5 9 | 7 6 1 | 4 2 3
     * 4 2 6 | 8 5 3 | 7 9 1
     * 7 1 3 | 9 2 4 | 8 5 6
     * ======+=======+======
     * 9 6 1 | 5 3 7 | 2 8 4
     * 2 8 7 | 4 1 9 | 6 3 5
     * 3 4 5 | 2 8 6 | 1 7 9
     */
    public static int[][] GRID_TO_SOLVE = {
            {5, 3, 0, 0, 7, 0, 0, 0, 0},
            {6, 0, 0, 1, 9, 5, 0, 0, 0},
            {0, 9, 8, 0, 4, 0, 0, 6, 0},
            {8, 0, 0, 0, 6, 0, 0, 0, 3},
            {4, 0, 0, 8, 0, 3, 0, 0, 1},
            {7, 0, 0, 0, 2, 6, 0, 0, 6},
            {0, 6, 0, 3, 0, 0, 2, 8, 0},
            {0, 0, 0, 4, 1, 9, 0, 0, 5},
            {0, 0, 0, 0, 8, 0, 0, 7, 9},
    };
    // #26###81#3##7#8##64###5###7#5#1#7#9###39#51###4#3#2#5#1###3###25##2#4##9#38###46#

    /**
     * Florian Paumier : PAUF24049702
     * Alex Demars :     DEMA13039906
     * Thomas Metral :   METT22040000
     */
    public static void main(String[] args) {
        ISolver solver = SolverFactory.newDefault();
        Reader reader = new DimacsReader(solver);

        /* Variable Propositionnelle */
        /**
         *  1 - La case X doit contenir un chiffre entre 1 et 9
         *  2 - la row R doit contenir un ensemble de chiffre unique entre 1 et 9
         *  3 - la col C doit contenir un ensemble de chiffre unique entre 1 et 9
         *  4 - le block B doit contenir un ensemble de chiffre unique entre 1 et 9
         *  5 - la case XR ne doit pas contenir un chiffre existant dans la ligne
         *  6 - la case XC ne doit pas contenir un chiffre existant dans la colonne
         *  7 - la case XRC ne doit pas contenir un chiffre existant dans le block
         */

        /**
         * (a ∨ ¬b ∨ c) ∧ (b ∨ ¬c ∨ ¬d ∨ e)
         * 1 -2 3
         * 2 -3 4 5
         */

        //Comme j'ai mis le "" au début ça concatène et ça additionne pas

        // ROW COLUMN NUMBER || 0 pour NUMBER => case vide
        // 110 111 112 113 114 115 116 117 118 119
        // 120 121 122 123 124 125 126 127 128 129
        // ...

        // Contrainte chaque case a une seule valeur (110 et 115 à True pas possible par exemple) à rajouter
        //((((((((l1 & l2) & l3) & l4) & l5) & l6) & l7) & l8) & l9)

        PropositionalVariable[][][] propVars = new PropositionalVariable[9][9][10];
        for (int row = 0; row < 9; row++)
            for (int column = 0; column < 9; column++)
                for (int number = 0; number < 10; number++)
                    propVars[row][column][number] = new PropositionalVariable("" + row + column + number);

        /* CONTRAINTES (formules) */

        List<BooleanFormula> cnfFormulas = new ArrayList<>();

        for (int row = 0; row < 9; row++) {
            for (int column = 0; column < 9; column++) {
                PropositionalVariable[] cellVars = propVars[row][column];

                Not cellNotEmpty = new Not(cellVars[0]);
                cnfFormulas.add(cellNotEmpty);

                for (int number = 1; number < 10; number++) {
                    String varName = "" + row + column + number;

                    //Une option par case (soit nombre soit vide)
                    Not[] nots = Arrays.stream(cellVars).filter(variable -> !variable.toString().equals(varName)).map(Not::new).toArray(Not[]::new);
                    And and = new And(nots);

                    Equivalence oneOptionPerCell = new Equivalence(and, cellVars[number]);

                    BooleanFormula cnfOneOptionPerCell = BooleanFormula.toCnf(oneOptionPerCell);
                    cnfFormulas.add(cnfOneOptionPerCell);

                    // Check pour les lignes et colonnes
                    List<Not> notsRow = new ArrayList<>();
                    List<Not> notsColumn = new ArrayList<>();

                    for (int count = 1; count < 10; count++) {
                        // Une seule fois par row
                        if (count != column) {
                            Not notSameNbRow = new Not(propVars[row][count][number]);
                            notsRow.add(notSameNbRow);
                        }
                        // Une seule fois par column
                        if (count != row) {
                            Not notSameNbCol = new Not(propVars[count][column][number]);
                            notsColumn.add(notSameNbCol);
                        }
                    }
                    PropositionalVariable currentVar = propVars[row][column][number];
                    And rowAnds = new And(notsRow.toArray(new Not[0]));
                    Equivalence rowEq = new Equivalence(currentVar, rowAnds);
                    And colAnds = new And(notsColumn.toArray(new Not[0]));
                    Equivalence colEq = new Equivalence(currentVar, colAnds);

                }
            }
        }

        List<PropositionalVariable> blocV = new ArrayList<>();
        for (int i = 0; i < 9; i++) {
            blocV.add(new PropositionalVariable("b"+i));
        }
        // Une ligne n'a pas de cases vides && Aucun chiffre pareil

        // Une colonne n'a pas de cases vides && Aucun chiffre pareil

        // Un bloc n'a pas de chiffre pareil

    }
}
