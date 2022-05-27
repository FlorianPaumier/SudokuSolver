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
 * Generic exception that can be thrown by some operations on Boolean formulas.
 * @author Sylvain Hallé
 */
public class BooleanFormulaException extends RuntimeException
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Creates an exception from a message
	 * @param message The message
	 */
	public BooleanFormulaException(String message)
	{
		super(message);
	}
	
	/**
	 * Creates an exception from a throwable
	 * @param t The throwable
	 */
	public BooleanFormulaException(Throwable t)
	{
		super(t);
	}
}
