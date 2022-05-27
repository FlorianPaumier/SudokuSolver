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

/**
 * Representation of the logical implication connective.
 * @author Sylvain Hallé
 */
public class Implies extends BinaryConnective 
{
	public Implies(/*@ non_null @*/ BooleanFormula left, /*@ non_null @*/ BooleanFormula right)
	{
		super(left, right);
	}
	
	@Override
	public boolean evaluate(Valuation v)
	{
		return !m_left.evaluate(v) || m_right.evaluate(v);
	}
	
	@Override
	public boolean isCnf()
	{
		return false;
	}
	
	@Override
	protected boolean isClause()
	{
		return false;
	}
	
	@Override
	protected boolean isAtom()
	{
		return false;
	}

	@Override
	public String toString()
	{
		return "(" + m_left + " -> " + m_right + ")";
	}
	
	@Override
	protected Implies pushNegations()
	{
		return new Implies(m_left.pushNegations(), m_right.pushNegations());
	}
	
	@Override
	protected Implies flatten()
	{
		return new Implies(m_left.flatten(), m_right.flatten());
	}
	
	@Override
	protected Or keepAndOrNot()
	{
		return new Or(new Not(m_left.keepAndOrNot()), m_right.keepAndOrNot());
	}

	@Override
	public int[][] getClauses()
	{
		throw new BooleanFormulaException("Formula is not in CNF");
	}
}
