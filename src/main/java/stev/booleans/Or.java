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
 * Representation of the logical disjunction connective.
 * @author Sylvain Hallé
 */
public class Or extends NaryConnective
{
	public static Or or(/*@ non_null @*/ BooleanFormula ... operands)
	{
		return new Or(operands);
	}
	
	public Or(/*@ non_null @*/ List<BooleanFormula> operands)
	{
		super(operands);
	}
	
	public Or(/*@ non_null @*/ BooleanFormula ... operands)
	{
		super(operands);
	}
	
	@Override
	public boolean evaluate(Valuation v)
	{
		for (BooleanFormula bf : m_operands)
		{
			if (bf.evaluate(v))
			{
				return true;
			}
		}
		return false;
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
		int len = m_operands.size();
		int[] clause = new int[len];
		for (int i = 0; i < len; i++)
		{
			BooleanFormula bf = m_operands.get(i);
			if (bf instanceof PropositionalVariable)
			{
				PropositionalVariable p = (PropositionalVariable) bf;
				clause[i] = var_dict.get(p.m_variableName);
			}
			else if (bf instanceof Not && ((Not) bf).m_operand instanceof PropositionalVariable)
			{
				PropositionalVariable p = (PropositionalVariable) ((Not) bf).m_operand;
				clause[i] = -var_dict.get(p.m_variableName);
			}
			else
			{
				throw new BooleanFormulaException("Formula is not a clause");
			}
		}
		return clause;
	}
	
	@Override
	public boolean isCnf()
	{
		for (BooleanFormula bf : m_operands)
		{
			if (!bf.isAtom())
			{
				return false;
			}
		}
		return true;
	}
	
	@Override
	protected boolean isClause()
	{
		for (BooleanFormula bf : m_operands)
		{
			if (!bf.isAtom())
			{
				return false;
			}
		}
		return true;
	}
	
	@Override
	protected boolean isAtom()
	{
		return false;
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("(");
		for (int i = 0; i < m_operands.size(); i++)
		{
			if (i > 0)
			{
				out.append(" | ");
			}
			out.append(m_operands.get(i).toString());
		}
		out.append(")");
		return out.toString();
	}
	
	@Override
	protected Or pushNegations()
	{
		List<BooleanFormula> new_list = new ArrayList<BooleanFormula>(m_operands.size());
		for (BooleanFormula f : m_operands)
		{
			new_list.add(f.pushNegations());
		}
		return new Or(new_list);
	}
	
	@Override
	protected BooleanFormula flatten()
	{
		List<BooleanFormula> new_list = new ArrayList<BooleanFormula>();
		for (BooleanFormula f : m_operands)
		{
			BooleanFormula flattened = f.flatten();
			if (flattened instanceof Or)
			{
				new_list.addAll(((Or) flattened).m_operands);
			}
			else
			{
				new_list.add(flattened);
			}
		}
		if (new_list.size() == 1)
		{
			return new_list.get(0);
		}
		return new Or(new_list);
	}
	
	@Override
	protected Or keepAndOrNot()
	{
		List<BooleanFormula> new_list = new ArrayList<BooleanFormula>(m_operands.size());
		for (BooleanFormula f : m_operands)
		{
			new_list.add(f.keepAndOrNot());
		}
		return new Or(new_list);
	}
}
