module Main

import Data.Vect

data Box = X | O | Empty

isEmpty : Box -> Bool
isEmpty Empty = True
isEmpty _ = False

Board : (size : Nat) -> Type
Board size = Vect size (Vect size Box)

newBoard : (size : Nat) -> Board size
newBoard size = replicate size (replicate size Empty)

markColumn : Box -> Vect x Box -> Fin x -> Maybe (Vect x Box)
markColumn mark (x :: xs) FZ = case x of
                                    Empty => Just (mark :: xs)
                                    _ => Nothing
markColumn mark (x :: xs) (FS y) = case markColumn mark xs y of
                                        Nothing => Nothing
                                        Just rest => Just (x :: rest)

markSquare : Vect x (Vect y Box) -> Box -> Fin x -> Fin y -> Maybe (Vect x (Vect y Box))
markSquare (x :: xs) mark FZ j = case markColumn mark x j of
                                      Nothing => Nothing
                                      Just new_x => Just (new_x :: xs)
markSquare (x :: xs) mark (FS i) j = case markSquare xs mark i j of
                                          Nothing => Nothing
                                          Just rest => Just (x :: rest)

checkVect : Vect x Box -> Maybe Box
checkVect [] = Just Empty
checkVect (x :: xs) = let rest = checkVect xs in
                          match x rest where
                           match : Box -> Maybe Box -> Maybe Box
                           match x Nothing = Nothing
                           match X (Just X) = Just X
                           match X (Just O) = Nothing
                           match X (Just Empty) = Just X
                           match O (Just X) = Nothing
                           match O (Just O) = Just O
                           match O (Just Empty) = Just O
                           match Empty (Just y) = Nothing

checkRows : Vect x (Vect y Box) -> Maybe Box
checkRows [] = Nothing
checkRows (x :: xs) = case checkVect x of
                           Just X => Just X
                           Just Y => Just Y
                           _ => checkRows xs


checkCols : Vect x (Vect y Box) -> Maybe Box
checkCols board = checkRows (transpose board)

checkDiags : Board size -> Maybe Box
checkDiags {size} board = case checkVect (diag board) of
                              Just a => Just a
                              Nothing => case checkVect (diag (reverse board)) of
                                              Just a => Just a
                                              Nothing => Nothing

findLegalMoves : Vect x (Vect y Box) -> Nat -> List (Nat, Nat)
findLegalMoves [] i = []
findLegalMoves (x :: xs) i = let hits = the (List Nat) (findIndices isEmpty (toList x)) in
                                 (zip (replicate (length hits) i) hits) ++ (findLegalMoves xs (i+1))


checkDraw : Board size -> Bool
checkDraw board  = (length (findLegalMoves board 0)) == 0


checkVictory : Board size -> Maybe Box
checkVictory b = case checkRows b of
                      Just X => Just X
                      Just O => Just O
                      Nothing => case checkCols b of
                                      Just X => Just X
                                      Just O => Just O
                                      Nothing => case checkDiags b of
                                                      Just X => Just X
                                                      Just O => Just O
                                                      Nothing => case checkDraw b of
                                                                      True => Just Empty
                                                                      False => Nothing
readNumber : IO (Maybe Nat)
readNumber = do input <- getLine
                if all isDigit (unpack input)
                   then pure (Just (cast input))
                   else pure Nothing

getMove : Board size -> IO (Fin size, Fin size)
getMove board {size} = do putStr "Enter row: "
                          Just row <- readNumber | Nothing => getMove board
                          let fRow = natToFin row size
                          putStr "Enter col: "
                          Just col <- readNumber | Nothing => getMove board
                          let fCol = natToFin col size
                          case finalizeMove fRow fCol of
                               Nothing => getMove board
                               Just move => pure move
            where
              finalizeMove : Maybe (Fin b) -> Maybe (Fin b) -> Maybe (Fin b, Fin b)
              finalizeMove Nothing y = Nothing
              finalizeMove (Just x) Nothing = Nothing
              finalizeMove (Just x) (Just y) = Just (x, y)


formattedRow : Vect n String -> String
formattedRow [] = ""
formattedRow (x :: xs) = x ++ (formattedRow xs)

stringify : Box -> String
stringify X = "X"
stringify O = "O"
stringify Empty = " "

showBoard : Vect n (Vect m Box) -> String
showBoard [] = ""
showBoard (x :: xs) {m} = (formattedRow (intersperse "|" (map stringify x))) ++ "\n" ++
                        rest xs where
                        rest : Vect n' (Vect m Box) -> String
                        rest [] = showBoard xs
                        rest xs = (formattedRow (replicate (2 * m) "-")) ++ "\n" ++ (showBoard xs)


flipPlayer : Box -> Box
flipPlayer X = O
flipPlayer O = X
flipPlayer Empty = Empty

runGame : Board size -> Box -> IO ()
runGame [] player  = putStrLn "weird board!"
runGame board player = do putStrLn (showBoard board)
                          putStrLn ((stringify player) ++ "'s turn: ")
                          move <- getMove board
                          case markSquare board player (fst move) (snd move) of
                               Nothing => runGame board player
                               Just new_board => case checkVictory new_board of
                                                      Nothing => runGame new_board (flipPlayer player)
                                                      Just Empty => putStrLn "Draw"
                                                      Just b => putStrLn ((stringify b) ++ " wins!")

main : IO ()
main = do runGame (newBoard 3) X
