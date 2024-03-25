/* Space
 * Author: Muthula Alwis
 * Creation date: 18/12/2023
 */
MACHINE
    Space
    
CONSTANTS
    Rows,
    Columns,
    SpaceGrid,
    Homebase,
    Starbase,
    Asteroids
    
PROPERTIES
    Rows <: NAT1 & Rows = 1..12 &
    Columns <: NAT1 & Columns =  1..7 &
    SpaceGrid : GRID & SpaceGrid =  Rows * Columns &
    Asteroids : GRID & Asteroids = { ( 3 |-> 2 ), ( 3 |-> 5 ), ( 5 |-> 4 ), ( 6 |-> 7 ), ( 7 |-> 1 ), ( 7 |-> 5 ), ( 7 |-> 7 ), ( 8 |-> 3 ), ( 10 |-> 6 ), ( 11 |-> 2 ), ( 12 |-> 5 ) } &
    Homebase : GRID & Homebase = { ( 1 |-> 1 ) } &
    Starbase : GRID & Starbase = { ( 6 |-> 4 ) }

DEFINITIONS
    GRID == POW( NAT1 * NAT1 )
    
END
