package com.uqac.sudoku;

import stev.booleans.PropositionalVariable;

public class Resolver {

    void main(String[] args){
        PropositionalVariable p = new PropositionalVariable("p");
        p.getClauses();
        System.out.println(p);
    }
}
