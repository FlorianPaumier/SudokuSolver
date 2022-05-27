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
import java.util.List;
import java.util.Map;

/**
 * Representation of the logical negation connective.
 * @author Sylvain Hallé
 */
public class Not extends BooleanFormula
{
	/*@ non_null @*/ protected BooleanFormula m_operand;
	
	/**
	 * Creates a new empty negation
	 */
	public Not(/*@ non_null @*/ BooleanFormula f)
	{
		super();
		m_operand = f;
	}
	
	/**
	 * Sets the formula to negate
	 * @param f The formula
	 */
	public void setOperand(/*@ non_null @*/ BooleanFormula f)
	{
		m_operand = f;
	}
	
	@Override
	public int[][] getClauses()
	{
		Map<String,Integer> var_dict = getVariablesMap();
		int[] clause = toClause(var_dict);
		int[][] clauses = new int[1][];
		clauses[0] = clause;
		return clauses;
	}
	
	/**
	 * Gets the DIMACS clause associated to this formula
	 * @return The DIMACS clause in the form of an array of integers
	 */
	protected int[] toClause(Map<String,Integer> var_dict)
	{
		if (!(m_operand instanceof PropositionalVariable))
		{
			throw new BooleanFormulaException("Formula is not in CNF");
		}
		PropositionalVariable p = (PropositionalVariable) m_operand;
		int index = var_dict.get(p.m_variableName);
		return new int[] {-index};
	}
	
	@Override
	public boolean isCnf()
	{
		return isClause();
	}
	
	@Override
	protected boolean isClause()
	{
		return isAtom();
	}
	
	@Override
	protected boolean isAtom()
	{
		return m_operand instanceof PropositionalVariable;
	}
	
	@Override
	public boolean evaluate(/*@ non_null @*/ Valuation v)
	{
		return !m_operand.evaluate(v);
	}
	
	@Override
	public String toString()
	{
		return "!" + m_operand;
	}
	
	@Override
	protected BooleanFormula pushNegations()
	{
		if (m_operand instanceof Implies)
		{
			Implies imp = (Implies) m_operand;
			return new And(imp.m_left.pushNegations(), new Not(imp.m_right).pushNegations());
		}
		if (m_operand instanceof Equivalence)
		{
			Equivalence imp = (Equivalence) m_operand;
			return new Equivalence(imp.m_left.pushNegations(), new Not(imp.m_right).pushNegations());
		}
		if (m_operand instanceof PropositionalVariable)
		{
			return new Not(m_operand);
		}
		if (m_operand instanceof And)
		{
			And and = (And) m_operand;
			List<BooleanFormula> new_list = new ArrayList<BooleanFormula>(and.m_operands.size());
			for (BooleanFormula f : and.m_operands)
			{
				new_list.add(new Not(f).pushNegations());
			}
			return new Or(new_list);
		}
		if (m_operand instanceof Or)
		{
			Or and = (Or) m_operand;
			List<BooleanFormula> new_list = new ArrayList<BooleanFormula>(and.m_operands.size());
			for (BooleanFormula f : and.m_operands)
			{
				new_list.add(new Not(f).pushNegations());
			}
			return new And(new_list);
		}
		if (m_operand instanceof Not)
		{
			return ((Not) m_operand).m_operand.pushNegations();
		}
		// Not supposed to happen
		throw new BooleanFormulaException("Unknown connective: " + m_operand);
	}
	
	@Override
	protected Not keepAndOrNot()
	{
		return new Not(m_operand.keepAndOrNot());
	}
	
	@Override
	protected BooleanFormula flatten()
	{
		BooleanFormula operand = m_operand.flatten();
		if (operand instanceof Not)
		{
			return operand;
		}
		return new Not(operand);
	}

	@Override
	protected void setVariablesMap(Map<String, Integer> map)
	{
		m_operand.setVariablesMap(map);
	}
}