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

public abstract class NaryConnective extends BooleanFormula
{
	/*@ non_null @*/ protected List<BooleanFormula> m_operands;
	
	/**
	 * Creates a new empty connective.
	 */
	public NaryConnective()
	{
		super();
		m_operands = new ArrayList<BooleanFormula>(2);
	}
	
	/**
	 * Creates a new connective from a list of operands.
	 * @param operands The list of operands
	 */
	public NaryConnective(/*@ non_null @*/ List<BooleanFormula> operands)
	{
		super();
		m_operands = new ArrayList<BooleanFormula>(operands.size());
		m_operands.addAll(operands);
	}
	
	/**
	 * Creates a new connective from a list of operands.
	 * @param operands The list of operands
	 */
	public NaryConnective(/*@ non_null @*/ BooleanFormula ... operands)
	{
		super();
		m_operands = new ArrayList<BooleanFormula>(operands.length);
		for (BooleanFormula bf : operands)
		{
			m_operands.add(bf);	
		}
	}
	
	/**
	 * Adds an operand to the connective
	 * @param f The operand
	 */
	public void addOperand(/*@ non_null @*/ BooleanFormula f)
	{
		if (!m_operands.contains(f))
		{
			m_operands.add(f);
		}
	}
	
	@Override
	protected void setVariablesMap(Map<String, Integer> map)
	{
		for (BooleanFormula op : m_operands)
		{
			op.setVariablesMap(map);
		}
	}
}
