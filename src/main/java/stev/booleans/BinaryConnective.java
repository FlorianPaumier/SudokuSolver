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

import java.util.Map;

public abstract class BinaryConnective extends BooleanFormula
{
	/*@ non_null @*/ protected BooleanFormula m_left;
	
	/*@ non_null @*/ protected BooleanFormula m_right;
	
	/**
	 * Creates a new binary connective and specifies its two
	 * operands.
	 * @param left The left operand
	 * @param right The right operand
	 */
	public BinaryConnective(/*@ non_null @*/ BooleanFormula left, /*@ non_null @*/ BooleanFormula right)
	{
		super();
		m_left = left;
		m_right = right;
	}
	
	/**
	 * Sets the left operand of the connective
	 * @param f The operand
	 */
	public void setLeft(/*@ non_null @*/ BooleanFormula f)
	{
		m_left = f;
	}
	
	/**
	 * Sets the right operand of the connective
	 * @param f The operand
	 */
	public void setRight(/*@ non_null @*/ BooleanFormula f)
	{
		m_right = f;
	}
	
	@Override
	protected void setVariablesMap(Map<String, Integer> map)
	{
		m_left.setVariablesMap(map);
		m_right.setVariablesMap(map);
	}
}
