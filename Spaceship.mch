/* Spaceship
 * Author: Muthula Alwis
 * Creation date: 18/12/2023
 */
MACHINE
    Spaceship

SEES
    Space
    
SETS
    RESULTS = { SUCCESSFUL_MOVE, FAILED_MOVE, FAILED_MOVE_OUT_OF_BOUND, FAILED_MOVE_ASTEROID_COLLISION, FAILED_MOVE_INSUFFICIENT_POWER, SUCCESSFUL_WARP_DRIVE, FAILED_WARP_DRIVE, FAILED_WARP_DRIVE_OUT_OF_BOUND, FAILED_WARP_DRIVE_ASTEROID_COLLISION, FAILED_WARP_DRIVE_INSUFFICIENT_POWER, DIRECT_WARPING_TO_STARBASE_IS_NOT_ALLOWED, SPACESHIP_IS_AT_STARBASE, SPACESHIP_IS_NOT_AT_STARBASE, GAME_WON, GAME_LOST, GAME_NOT_OVER, START_A_NEW_GAME } ;
    STATUS = { GameWon, GameLost, GameNotOver }
    
DEFINITIONS
    isSpaceshipInsideGrid( xx, yy ) == ( ( xx |-> yy ) : SpaceGrid ) ;
    isCollision( xx, yy ) == ( ( xx |-> yy ) : Asteroids )
    
CONSTANTS
    NormalMovePowerConsumption,
    WarpDrivePowerConsumption,
    CollisionPowerConsumption
    
PROPERTIES    
    NormalMovePowerConsumption : NAT1 & NormalMovePowerConsumption = 5 &
    WarpDrivePowerConsumption : NAT1 & WarpDrivePowerConsumption = 20 &
    CollisionPowerConsumption : NAT1 & CollisionPowerConsumption = 10
    
VARIABLES
    spaceshipRow,
    spaceshipColumn,
    spaceshipPower,
    asteroidCollisionsCount,
    currentPosition,
    spaceshipRoute,
    gameStatus
    
INVARIANT
    spaceshipRow : Rows &
    spaceshipColumn : Columns &
    spaceshipPower : INTEGER &
    asteroidCollisionsCount : NAT &
    currentPosition : SpaceGrid &
    spaceshipRoute : seq( SpaceGrid ) &
    gameStatus <: STATUS
    
INITIALISATION
    spaceshipRow := 1
    || spaceshipColumn := 1
    || spaceshipPower := 120
    || asteroidCollisionsCount := 0
    || currentPosition := ( 1 |-> 1 ) 
    || spaceshipRoute := [ ( 1 |-> 1 ) ] 
    || gameStatus := { GameNotOver }
    
OPERATIONS

    /* Spaceship moves one square in up direction */
    results <-- MoveUp = 
    PRE
        results : RESULTS   
    THEN
        /* Checks the game status */
        IF
            ( GameNotOver : gameStatus )
        THEN
            /* Checks if the power is enough for a normal move */
            IF
                ( spaceshipPower >= NormalMovePowerConsumption )
            THEN
                /* Checks if the spaceship is inside the space grid and has not met up with a collision */ 
                IF
                    ( isSpaceshipInsideGrid( spaceshipRow, succ( spaceshipColumn ) ) & not( isCollision( spaceshipRow, succ( spaceshipColumn ) ) ) )
                THEN
                    /* Checks if the move is causing the game to win */
                    IF
                        ( ( spaceshipRow |-> succ( spaceshipColumn) ) : Starbase )
                    THEN
                        spaceshipRow, spaceshipColumn := spaceshipRow, succ( spaceshipColumn )
                        || currentPosition := ( spaceshipRow |-> succ( spaceshipColumn ) ) 
                        || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                        || spaceshipRoute := spaceshipRoute ^ [ spaceshipRow |-> succ( spaceshipColumn ) ]
                        || gameStatus := { GameWon }
                        || results := GAME_WON
                    ELSE
                        /* Checks the power level to continue with the game after this move */
                        IF
                            ( (spaceshipPower - NormalMovePowerConsumption) >= NormalMovePowerConsumption )
                        THEN
                            spaceshipRow, spaceshipColumn := spaceshipRow, succ( spaceshipColumn )
                            || currentPosition := ( spaceshipRow |-> succ( spaceshipColumn ) )
                            || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ spaceshipRow |-> succ( spaceshipColumn ) ]
                            || gameStatus := { GameNotOver }
                            || results := SUCCESSFUL_MOVE
                        ELSE
                            spaceshipRow, spaceshipColumn := spaceshipRow, succ( spaceshipColumn )
                            || currentPosition := ( spaceshipRow |-> succ( spaceshipColumn ) )
                            || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ spaceshipRow |-> succ( spaceshipColumn ) ]
                            || gameStatus := { GameLost }
                            || results := GAME_LOST
                        END
                    END
                /* Checks for collisions */
                ELSIF
                    ( isCollision( spaceshipRow, succ( spaceshipColumn ) ) )
                THEN
                    /* Checks the power level to continue with the game after the collision */
                    IF
                        ( ( spaceshipPower - CollisionPowerConsumption ) >= NormalMovePowerConsumption )
                    THEN
                        gameStatus := { GameNotOver }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || spaceshipPower  := spaceshipPower - CollisionPowerConsumption
                        || results := FAILED_MOVE_ASTEROID_COLLISION
                    ELSE
                        gameStatus := { GameLost }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || spaceshipPower  := spaceshipPower - CollisionPowerConsumption
                        || results := GAME_LOST
                    END
                /* Checks if the spaceship is not inside the grid */     
                ELSIF
                    ( not( isSpaceshipInsideGrid( spaceshipRow, succ( spaceshipColumn ) ) ) )
                THEN
                    results := FAILED_MOVE_OUT_OF_BOUND
                ELSE
                    results := FAILED_MOVE
                END
            /* If the power is not enough, sets the game status to lost */    
            ELSE
                gameStatus := { GameLost }
                || results := FAILED_MOVE_INSUFFICIENT_POWER
            END
        /* Checks the game status */    
        ELSIF 
            ( GameWon : gameStatus or GameLost :  gameStatus )
        THEN
            results := START_A_NEW_GAME
        END
    END;
    
    /* Spaceship moves one square in down direction */
    results <-- MoveDown = 
    PRE
        results : RESULTS    
    THEN
        /* Checks the game status */
        IF
            ( GameNotOver : gameStatus )
        THEN
            /* Checks if the power is enough for a normal move */
            IF
                ( spaceshipPower >= NormalMovePowerConsumption )
            THEN
                /* Checks if the spaceship is inside the space grid and has not met up with a collision */ 
                IF
                    ( isSpaceshipInsideGrid( spaceshipRow, pred( spaceshipColumn ) ) & not( isCollision( spaceshipRow, pred( spaceshipColumn ) ) ) )
                THEN
                    /* Checks if the move is causing the game to win */
                    IF
                        ( ( spaceshipRow |-> pred( spaceshipColumn) ) : Starbase )
                    THEN
                        spaceshipRow, spaceshipColumn := spaceshipRow, pred( spaceshipColumn )
                        || currentPosition := ( spaceshipRow |-> pred( spaceshipColumn ) )
                        || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                        || spaceshipRoute := spaceshipRoute ^ [ spaceshipRow |-> pred( spaceshipColumn ) ]
                        || gameStatus := { GameWon }
                        || results := GAME_WON
                    ELSE
                        /* Checks the power level to continue with the game after this move */
                        IF
                            ( (spaceshipPower - NormalMovePowerConsumption) >= NormalMovePowerConsumption )
                        THEN
                            spaceshipRow, spaceshipColumn := spaceshipRow, pred( spaceshipColumn )
                            || currentPosition := ( spaceshipRow |-> pred( spaceshipColumn ) )
                            || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ spaceshipRow |-> pred( spaceshipColumn ) ]
                            || gameStatus := { GameNotOver }
                            || results := SUCCESSFUL_MOVE
                        ELSE
                            spaceshipRow, spaceshipColumn := spaceshipRow, pred( spaceshipColumn )
                            || currentPosition := ( spaceshipRow |-> pred( spaceshipColumn ) )
                            || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ spaceshipRow |-> pred( spaceshipColumn ) ]
                            || gameStatus := { GameLost }
                            || results := GAME_LOST
                        END
                    END
                /* Checks for collisions */    
                ELSIF
                    ( isCollision( spaceshipRow, pred( spaceshipColumn ) ) )
                THEN
                    /* Checks the power level to continue with the game after the collision */
                    IF
                        ( ( spaceshipPower - CollisionPowerConsumption ) >= NormalMovePowerConsumption )
                    THEN
                        gameStatus := { GameNotOver }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || spaceshipPower  := spaceshipPower - CollisionPowerConsumption
                        || results := FAILED_MOVE_ASTEROID_COLLISION
                    ELSE
                        gameStatus := { GameLost }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || spaceshipPower  := spaceshipPower - CollisionPowerConsumption
                        || results := GAME_LOST
                    END
                /* Checks if the spaceship is not inside the grid */     
                ELSIF
                    ( not( isSpaceshipInsideGrid( spaceshipRow, pred( spaceshipColumn ) ) ) )
                THEN
                    results := FAILED_MOVE_OUT_OF_BOUND
                ELSE
                    results := FAILED_MOVE
                END
            /* If the power is not enough, sets the game status to lost */    
            ELSE
                gameStatus := { GameLost }
                || results := FAILED_MOVE_INSUFFICIENT_POWER
            END
        /* Checks the game status */    
        ELSIF 
            ( GameWon : gameStatus or GameLost :  gameStatus )
        THEN
            results := START_A_NEW_GAME
        END
    END;
    
    /* Spaceship moves one square in left direction */
    results <-- MoveLeft = 
    PRE
        results : RESULTS  
    THEN
        /* Checks the game status */
        IF
            ( GameNotOver : gameStatus )
        THEN
            /* Checks if the power is enough for a normal move */
            IF
                ( spaceshipPower >= NormalMovePowerConsumption )
            THEN
                /* Checks if the spaceship is inside the space grid and has not met up with a collision */ 
                IF
                    ( isSpaceshipInsideGrid( pred( spaceshipRow ), spaceshipColumn ) & not( isCollision( pred( spaceshipRow ), spaceshipColumn ) ) )
                THEN
                    /* Checks if the move is causing the game to win */
                    IF
                        ( ( pred( spaceshipRow ) |-> spaceshipColumn ) : Starbase )
                    THEN
                        spaceshipRow, spaceshipColumn := pred( spaceshipRow ), spaceshipColumn
                        || currentPosition := ( pred( spaceshipRow ) |-> spaceshipColumn )
                        || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                        || spaceshipRoute := spaceshipRoute ^ [ pred( spaceshipRow ) |-> spaceshipColumn ]
                        || gameStatus := { GameWon }
                        || results := GAME_WON
                    ELSE
                        /* Checks the power level to continue with the game after this move */
                        IF
                            ( (spaceshipPower - NormalMovePowerConsumption) >= NormalMovePowerConsumption )
                        THEN
                            spaceshipRow, spaceshipColumn := pred( spaceshipRow ), spaceshipColumn
                            || currentPosition := ( pred( spaceshipRow ) |-> spaceshipColumn )
                            || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ pred( spaceshipRow ) |-> spaceshipColumn ]
                            || gameStatus := { GameNotOver }
                            || results := SUCCESSFUL_MOVE
                        ELSE
                            spaceshipRow, spaceshipColumn := pred( spaceshipRow ), spaceshipColumn
                            || currentPosition := ( pred( spaceshipRow ) |-> spaceshipColumn )
                            || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ pred( spaceshipRow ) |-> spaceshipColumn ]
                            || gameStatus := { GameLost }
                            || results := GAME_LOST
                        END
                    END
                /* Checks for collisions */
                ELSIF
                    ( isCollision( pred( spaceshipRow ), spaceshipColumn ) )
                THEN
                    /* Checks the power level to continue with the game after the collision */
                    IF
                        ( ( spaceshipPower - CollisionPowerConsumption ) >= NormalMovePowerConsumption )
                    THEN
                        gameStatus := { GameNotOver }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || spaceshipPower  := spaceshipPower - CollisionPowerConsumption
                        || results := FAILED_MOVE_ASTEROID_COLLISION
                    ELSE
                        gameStatus := { GameLost }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || spaceshipPower  := spaceshipPower - CollisionPowerConsumption
                        || results := GAME_LOST
                    END
                /* Checks if the spaceship is not inside the grid */     
                ELSIF
                    ( not( isSpaceshipInsideGrid( pred( spaceshipRow ), spaceshipColumn ) ) ) 
                THEN
                    results := FAILED_MOVE_OUT_OF_BOUND
                ELSE
                    results := FAILED_MOVE
                END
            /* If the power is not enough, sets the game status to lost */    
            ELSE 
                gameStatus := { GameLost }
                || results := FAILED_MOVE_INSUFFICIENT_POWER
            END
        /* Checks the game status */    
        ELSIF 
            ( GameWon : gameStatus or GameLost :  gameStatus )
        THEN
            results := START_A_NEW_GAME
        END
    END;
    
    /* Spaceship moves one square in right direction */
    results <-- MoveRight = 
    PRE
        results : RESULTS  
    THEN
        /* Checks the game status */
        IF
            ( GameNotOver : gameStatus ) 
        THEN
            /* Checks if the power is enough for a normal move */
            IF
                ( spaceshipPower >= NormalMovePowerConsumption )
            THEN
                /* Checks if the spaceship is inside the space grid and has not met up with a collision */ 
                IF
                    ( isSpaceshipInsideGrid( succ( spaceshipRow ), spaceshipColumn ) & not( isCollision( succ( spaceshipRow ), spaceshipColumn ) ) ) 
                THEN
                    /* Checks if the move is causing the game to win */
                    IF
                        ( ( succ( spaceshipRow ) |-> spaceshipColumn ) : Starbase ) 
                    THEN
                        spaceshipRow, spaceshipColumn := succ( spaceshipRow ), spaceshipColumn
                        || currentPosition := ( succ( spaceshipRow ) |-> spaceshipColumn )
                        || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                        || spaceshipRoute := spaceshipRoute ^ [ succ( spaceshipRow ) |-> spaceshipColumn ]
                        || gameStatus := { GameWon }
                        || results := GAME_WON
                    ELSE
                        /* Checks the power level to continue with the game after this move */
                        IF
                            ( (spaceshipPower - NormalMovePowerConsumption) >= NormalMovePowerConsumption ) 
                        THEN
                            spaceshipRow, spaceshipColumn := succ( spaceshipRow ), spaceshipColumn
                            || currentPosition := ( succ( spaceshipRow ) |-> spaceshipColumn )
                            || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ succ( spaceshipRow ) |-> spaceshipColumn ]
                            || gameStatus := { GameNotOver }
                            || results := SUCCESSFUL_MOVE
                        ELSE
                            spaceshipRow, spaceshipColumn := succ( spaceshipRow ), spaceshipColumn
                            || currentPosition := ( succ( spaceshipRow ) |-> spaceshipColumn )
                            || spaceshipPower := spaceshipPower - NormalMovePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ succ( spaceshipRow ) |-> spaceshipColumn ]
                            || gameStatus := { GameLost }
                            || results := GAME_LOST
                        END
                    END
                /* Checks for collisions */    
                ELSIF
                    ( isCollision( succ( spaceshipRow ), spaceshipColumn ) )
                THEN
                    /* Checks the power level to continue with the game after the collision */
                    IF
                        ( ( spaceshipPower - CollisionPowerConsumption ) >= NormalMovePowerConsumption )
                    THEN
                        gameStatus := { GameNotOver }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || spaceshipPower  := spaceshipPower - CollisionPowerConsumption
                        || results := FAILED_MOVE_ASTEROID_COLLISION
                    ELSE
                        gameStatus := { GameLost }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || spaceshipPower  := spaceshipPower - CollisionPowerConsumption
                        || results := GAME_LOST
                    END
                /* Checks if the spaceship is not inside the grid */
                ELSIF
                    ( not( isSpaceshipInsideGrid( succ( spaceshipRow ), spaceshipColumn ) ) )
                THEN
                    results := FAILED_MOVE_OUT_OF_BOUND
                ELSE
                    results := FAILED_MOVE
                END
            /* If the power is not enough, sets the game status to lost */    
            ELSE
                gameStatus := { GameLost }
                || results := FAILED_MOVE_INSUFFICIENT_POWER
            END
        /* Checks the game status */    
        ELSIF
            ( GameWon : gameStatus or GameLost :  gameStatus )
        THEN
            results := START_A_NEW_GAME
        END
    END;
    
    
    /* Spaceship engages in Warp Drive */
    results <-- EngageWarpDrive ( xx, yy ) = 
    PRE
        results : RESULTS & xx : 1..12 & yy : 1..7
        THEN
        /* Checks the game status */
        IF
            ( GameNotOver : gameStatus ) 
        THEN
            /* Checks if the power is enough for a normal move */
            IF
                ( spaceshipPower >= WarpDrivePowerConsumption )
            THEN
                /* Checks if the spaceship is inside the space grid and has not met up with a collision */ 
                IF
                    ( isSpaceshipInsideGrid( xx, yy ) & not( isCollision( xx, yy ) ) & not( currentPosition : Homebase & ( xx |-> yy ) : Starbase ) ) 
                THEN
                    /* Checks if the move is causing the game to win */
                    IF
                        ( ( xx |-> yy ) : Starbase ) 
                    THEN
                        spaceshipRow, spaceshipColumn := xx, yy
                        || currentPosition := ( xx |-> yy )
                        || spaceshipPower := spaceshipPower - WarpDrivePowerConsumption
                        || spaceshipRoute := spaceshipRoute ^ [ xx |-> yy ]
                        || gameStatus := { GameWon }
                        || results := GAME_WON
                    ELSE
                        /* Checks the power level to continue with the game after this move */
                        IF
                            ( ( spaceshipPower - WarpDrivePowerConsumption ) >= NormalMovePowerConsumption ) 
                        THEN
                            spaceshipRow, spaceshipColumn := xx, yy
                            || currentPosition := ( xx |-> yy )
                            || spaceshipPower := spaceshipPower - WarpDrivePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ xx |-> yy ]
                            || gameStatus := { GameNotOver }
                            || results := SUCCESSFUL_MOVE
                        ELSE
                            spaceshipRow, spaceshipColumn := xx, yy
                            || currentPosition := ( xx |-> yy )
                            || spaceshipPower := spaceshipPower - WarpDrivePowerConsumption
                            || spaceshipRoute := spaceshipRoute ^ [ xx |-> yy ]
                            || gameStatus := { GameLost }
                            || results := GAME_LOST
                        END
                    END
                /* Checks if the user tries to warp directly from home base to star base */
                ELSIF
                    ( currentPosition : Homebase & ( xx |-> yy ) : Starbase ) 
                THEN
                    results := DIRECT_WARPING_TO_STARBASE_IS_NOT_ALLOWED
                /* Checks for collisions */
                ELSIF
                    ( isCollision( xx, yy ) )
                THEN
                    /* Checks the power level to continue with the game after the collision */
                    IF
                        ( ( spaceshipPower - CollisionPowerConsumption ) >= NormalMovePowerConsumption )
                    THEN
                        gameStatus := { GameNotOver }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || results := FAILED_WARP_DRIVE_ASTEROID_COLLISION
                    ELSE
                        gameStatus := { GameLost }
                        || asteroidCollisionsCount := asteroidCollisionsCount + 1
                        || results := GAME_LOST
                    END
                /* Checks if the spaceship is not inside the grid */
                ELSIF
                    ( not( isSpaceshipInsideGrid( xx, yy ) ) )
                THEN
                    results := FAILED_WARP_DRIVE_OUT_OF_BOUND
                ELSE
                    results := FAILED_WARP_DRIVE
                END
            /* If the power is not enough, sets the game status to lost */    
            ELSE
                results := FAILED_WARP_DRIVE_INSUFFICIENT_POWER
            END
         /* Checks the game status */    
        ELSIF
            ( GameWon : gameStatus or GameLost :  gameStatus )
        THEN
            results := START_A_NEW_GAME
        END
    END;
    
    
    /* Checks the status of the spaceship */
    location, power, collisions <-- MissionStatus =
    BEGIN
        location := currentPosition
        || power := spaceshipPower
        || collisions := asteroidCollisionsCount
    END;
    
    /* Checks the route of the spaceship */
    results <-- MissionRoute =
    BEGIN
        results := spaceshipRoute
    END;
    
    /* Checks the Star base status */
    results <-- DockedAtStarbase =
    PRE
        results : RESULTS  
    THEN
        /* Compares the current position with the star base location */ 
        IF
            ( currentPosition : Starbase )
        THEN
            results := SPACESHIP_IS_AT_STARBASE
        ELSE
            results := SPACESHIP_IS_NOT_AT_STARBASE
        END
    END;
    
    /* Checks the game status */
    results <-- GameStatus =
    PRE
        results : RESULTS  
    THEN
        /* Compares game status */
        IF
            ( GameWon : gameStatus )
        THEN
            results := GAME_WON
        ELSIF
            ( GameLost : gameStatus )
        THEN
            results := GAME_LOST
        ELSIF
            ( GameNotOver : gameStatus )
        THEN
            results := GAME_NOT_OVER
        END
    END;
    
    /* Start a new game. According to the power level selected in the parameter, it will multiply by 10 and give out the power */
    StartNewGame(power) = 
    PRE
        power : 10..20
    THEN
        /* Checks if the game has ended */
        IF
            ( GameWon : gameStatus or GameLost :  gameStatus )
        THEN
            spaceshipRow := 1
            || spaceshipColumn := 1
            || spaceshipPower := power * 10
            || asteroidCollisionsCount := 0
            || currentPosition := ( 1 |-> 1 ) 
            || spaceshipRoute := [ ( 1 |-> 1 ) ] 
            || gameStatus := { GameNotOver }
        END
    END        
END