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
 * Representation of the logical conjunction connective.
 * @author Sylvain Hallé
 */
public class And extends NaryConnective
{
	public And(/*@ non_null @*/ List<BooleanFormula> operands)
	{
		super(operands);
	}
	
	public And(/*@ non_null @*/ BooleanFormula ... operands)
	{
		super(operands);
	}

	@Override
	public boolean evaluate(/*@ non_null @*/ Valuation v)
	{
		for (BooleanFormula bf : m_operands)
		{
			if (!bf.evaluate(v))
			{
				return false;
			}
		}
		return true;
	}
	
	@Override
	public int[][] getClauses()
	{
		Map<String,Integer> var_dict = getVariablesMap();
		int[][] clauses = new int[m_operands.size()][];
		for (int i = 0; i < m_operands.size(); i++)
		{
			BooleanFormula bf = m_operands.get(i);
			if (!bf.isClause())
			{
				throw new BooleanFormulaException("Formula is not in CNF");
			}
			if (bf instanceof Or)
			{
				Or o = (Or) bf;
				clauses[i] = o.toClause(var_dict);
			}
			else if (bf instanceof Not)
			{
				PropositionalVariable p = (PropositionalVariable) ((Not) bf).m_operand;
				clauses[i] = new int[] {-var_dict.get(p.m_variableName)};
			}
			else if (bf instanceof PropositionalVariable)
			{
				PropositionalVariable p = (PropositionalVariable) bf;
				clauses[i] = new int[] {var_dict.get(p.m_variableName)};
			}
		}
		return clauses;
	}
	
	@Override
	public boolean isCnf()
	{
		for (BooleanFormula op : m_operands)
		{
			if (!op.isClause())
			{
				return false;
			}
		}
		return true;
	}
	
	@Override
	public boolean isClause()
	{
		return false;
	}
	
	@Override
	public boolean isAtom()
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
				out.append(" & ");
			}
			out.append(m_operands.get(i).toString());
		}
		out.append(")");
		return out.toString();
	}
	
	@Override
	protected And pushNegations()
	{
		List<BooleanFormula> new_list = new ArrayList<BooleanFormula>(m_operands.size());
		for (BooleanFormula f : m_operands)
		{
			new_list.add(f.pushNegations());
		}
		return new And(new_list);
	}
	
	@Override
	protected And keepAndOrNot()
	{
		List<BooleanFormula> new_list = new ArrayList<BooleanFormula>(m_operands.size());
		for (BooleanFormula f : m_operands)
		{
			new_list.add(f.keepAndOrNot());
		}
		return new And(new_list);
	}
	
	@Override
	protected BooleanFormula flatten()
	{
		List<BooleanFormula> new_list = new ArrayList<BooleanFormula>();
		for (BooleanFormula f : m_operands)
		{
			BooleanFormula flattened = f.flatten();
			if (flattened instanceof And)
			{
				And af = (And) flattened;
				new_list.addAll(af.m_operands);
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
		return new And(new_list);
	}
}
