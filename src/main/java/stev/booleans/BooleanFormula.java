/*
    Simple manipulation of Boolean formulas
    Copyright (C) 2020 Sylvain Hallé
    
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published
    by the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    
    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.
    
    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package stev.booleans;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Abstract class designating an arbitrary propositional logic formula.
 * It provides a few utility methods to manipulate formulas, such as
 * {@link #toCnf(BooleanFormula)} to convert a formula in Conjunctive Normal
 * Form (CNF).
 * @author Sylvain Hallé
 */
public abstract class BooleanFormula
{
	/**
	 * Creates a new boolean formula
	 */
	public BooleanFormula()
	{
		super();
	}

	/**
	 * Gets the value of the formula.
	 * @param v The valuation used to give values to variables
	 * @return The value of the formula
	 */
	public abstract boolean evaluate(Valuation v);

	/**
	 * Converts the formula into conjunctive normal form (CNF).
	 * @param phi The input formula
	 * @return A new formula equivalent to the current one, but in
	 * CNF.
	 */
	public static final BooleanFormula toCnf(BooleanFormula phi)
	{
		BooleanFormula n_phi = phi.keepAndOrNot();
		n_phi = n_phi.pushNegations();
		BooleanFormula cnf_phi = toCnfRecursive(n_phi);
		return simplify(cnf_phi);
	}

	/**
	 * Simplifies a CNF formula by applying identities on its clauses.
	 * @param phi The formula to simplify
	 * @return The simplfiied formula
	 */
	protected static BooleanFormula simplify(BooleanFormula phi)
	{
		if (phi instanceof PropositionalVariable || phi instanceof Not)
		{
			// Nothing to do
			return phi;
		}
		if (phi instanceof Or)
		{
			// phi is a single clause
			return simplifyClause((Or) phi);
		}
		if (phi instanceof And)
		{
			And big_and = new And();
			for (BooleanFormula bf : ((And) phi).m_operands)
			{
				if (bf instanceof Or)
				{
					BooleanFormula simplified = simplifyClause((Or) bf);
					if (simplified != null)
					{
						big_and.addOperand(simplified);
					}
				}
				else
				{
					big_and.addOperand(bf);
				}
			}
			if (big_and.m_operands.size() == 1)
			{
				return big_and.m_operands.get(0);
			}
			return big_and;
		}
		throw new BooleanFormulaException("Error simplifying formula");
	}

	/**
	 * Simplifies a single clause of a formula in CNF. Two simplification
	 * identities are applied:
	 * <ol>
	 * <li>If the same atom appears twice, duplicates are eliminated</li>
	 * <li>If the same variable appears both positively and negatively inside the
	 * clause, the whole clause can be deleted from the formula that contains it.
	 * In such a case, the method returns <tt>null</tt></li>
	 * </ol>
	 * @param o The clause
	 * @return The simplified clause, or <tt>null</tt>
	 */
	protected static BooleanFormula simplifyClause(Or o)
	{
		Set<PropositionalVariable> positive = new HashSet<PropositionalVariable>();
		Set<PropositionalVariable> negative = new HashSet<PropositionalVariable>();
		Or new_o = new Or();
		for (BooleanFormula bf : o.m_operands)
		{
			if (bf instanceof PropositionalVariable)
			{
				if (!positive.contains((PropositionalVariable) bf))
				{
					positive.add((PropositionalVariable) bf);
					new_o.addOperand(bf);
				}
				if (negative.contains((PropositionalVariable) bf))
				{
					// Variable exists in both positive and negative in clause:
					// the whole clause disappears
					return null;
				}
			}
			else if (bf instanceof Not)
			{
				BooleanFormula not_child = ((Not) bf).m_operand;
				if (not_child instanceof PropositionalVariable)
				{
					if (!negative.contains((PropositionalVariable) not_child))
					{
						negative.add((PropositionalVariable) not_child);
						new_o.addOperand(bf);
					}
					if (positive.contains((PropositionalVariable) not_child))
					{
						// Variable exists in both positive and negative in clause:
						// the whole clause disappears
						return null;
					}
				}
				else
				{
					new_o.addOperand(bf);
				}
			}
		}
		if (new_o.m_operands.size() == 1)
		{
			return new_o.m_operands.get(0);
		}
		return new_o;
	}

	/**
	 * Recursively converts a formula into conjunctive normal form (CNF).
	 * @param n_phi The formula to put in CNF
	 * @return A new formula equivalent to the current one, but in
	 * CNF.
	 */
	protected static BooleanFormula toCnfRecursive(BooleanFormula n_phi)
	{
		if (n_phi instanceof PropositionalVariable)
		{
			// n_phi is a single variable
			return n_phi;
		}
		if (n_phi instanceof Not)
		{
			// n_phi is a single negated variable
			return n_phi; 
		}
		if (n_phi instanceof And)
		{
			And a = new And();
			for (BooleanFormula child : ((And) n_phi).m_operands)
			{
				a.addOperand(toCnf(child));
			}
			return a.flatten();
		}
		if (n_phi instanceof Or)
		{
			int num_terms = ((Or) n_phi).m_operands.size();
			List<BooleanFormula> new_list = new ArrayList<BooleanFormula>(num_terms);
			int[] sizes = new int[num_terms];
			int[] cursor = new int[num_terms];
			for (int i = 0; i < num_terms; i++)
			{
				cursor[i] = 0;
				BooleanFormula bf = ((Or) n_phi).m_operands.get(i);
				BooleanFormula n_bf = toCnf(bf);
				new_list.add(n_bf);
				sizes[i] = 1;
				if (bf instanceof And)
				{
					sizes[i] = ((And) bf).m_operands.size();
				}
			}
			boolean run = true;
			And big_and = new And();
			while (run)
			{
				Or clause = new Or();
				for (int i = 0; i < num_terms; i++)
				{
					BooleanFormula bf = new_list.get(i);
					if (bf instanceof And)
					{
						clause.addOperand(((And) bf).m_operands.get(cursor[i]));
					}
					else
					{
						clause.addOperand(bf);
					}
				}
				big_and.addOperand(clause);
				int reset = 0;
				for (int i = 0; i < num_terms; i++)
				{
					cursor[i]++;
					if (cursor[i] == sizes[i])
					{
						cursor[i] = 0;
						reset++;
					}
					else
					{
						break;
					}
				}
				if (reset == num_terms)
				{
					// We enumerated them all
					run = false;
				}
			}
			return big_and.flatten();
		}
		throw new BooleanFormulaException("Error converting to CNF");
	}

	/**
	 * Gets the mapping between variables and integers representing each
	 * of them in a formula
	 * @return The mapping
	 */
	/*@ non_null @*/ public final Map<String,Integer> getVariablesMap()
	{
		Map<String,Integer> map = new HashMap<String,Integer>();
		setVariablesMap(map);
		return map;
	}

	/**
	 * Recursively populates the map between variables and integers
	 * representing each of them in a formula
	 * @param map The map
	 */
	protected abstract void setVariablesMap(/*@ non_null @*/ Map<String,Integer> map);

	/**
	 * Determines if the current formula is in conjunctive normal form
	 * (CNF).
	 * @return <tt>true</tt> if the formula is in CNF, <tt>false</tt>
	 * otherwise
	 */
	public abstract boolean isCnf();

	/**
	 * Checks if the current operator is a clause in conjunctive normal
	 * form (CNF).
	 * @return <tt>true</tt> if it is a clause, <tt>false</tt> otherwise
	 */
	protected abstract boolean isClause();

	/**
	 * Gets an array of clauses in DIMACS format for this formula
	 * @return The array of clauses
	 */
	public abstract int[][] getClauses();

	/**
	 * Checks if the current operator is an atom.
	 * @return <tt>true</tt> if it is an atom, <tt>false</tt> otherwise
	 */
	protected abstract boolean isAtom();

	/**
	 * Pushes negations on atoms
	 * @return A boolean formula with negations pushed on atoms
	 */
	/*@ non_null @*/ protected abstract BooleanFormula pushNegations();

	/**
	 * Transforms the formula to keep only and, or and not as
	 * connectives. 
	 * @return A transformed Boolean formula
	 */
	/*@ non_null @*/ protected abstract BooleanFormula keepAndOrNot();

	/**
	 * Flattens a formula.
	 * @return The flattened formula
	 */
	/*@ non_null @*/ protected abstract BooleanFormula flatten();
}
