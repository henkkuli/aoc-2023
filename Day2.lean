import «Aoc2023»

open Lean

structure Sample where
  red : Nat
  green : Nat
  blue : Nat
deriving Repr

partial def Sample.parser.loop (res : Sample) : Parsec Sample := do
    let count ← Nat.parser
    let tryColor (color : String) (res : Sample) : Parsec Sample :=
      Parsec.skipString (" "++color) >>= fun () => Parsec.pure res
    let res ← tryColor "red" {res with red := count} <|>
              tryColor "green" {res with green := count} <|>
              tryColor "blue" {res with blue := count}
    -- Try to parse next color, or stop
    (Parsec.skipString ", " >>= fun () => loop res) <|> Parsec.pure res

def Sample.parser : Parsec Sample :=
  Sample.parser.loop ⟨0, 0, 0⟩

def Sample.max (a b : Sample) : Sample :=
  {
    red := Nat.max a.red b.red,
    green := Nat.max a.green b.green,
    blue := Nat.max a.blue b.blue,
  }

def Sample.power (s : Sample) : Nat := s.red * s.green * s.blue

-- example : Sample.parser.run "foo" = Except.error "" := by rfl

-- def Sample.fromStr (s : Substring) : Option Sample :=
--   let rec loop (res : Sample) (s : List Substring) : Option Sample :=
--     match s with
--     | [] => res
--     | x :: xs =>
--       if let some (count, color) := x.splitOnce " " then
--         if let some count := count.toNat? then
--           -- if color == "red" then loop {res with red := count} xs
--           -- else if color == "green" then loop {res with green := count} xs
--           -- else if color == "blue" then loop {res with blue := count} xs
--           -- else panic s!"Color {color} is invalid"
--           loop res xs
--         else
--           panic s!"Count '{count}' '{color}' ('{x}') is not a number"
--       else
--         panic s!"Could not split {x}"

--   loop ⟨0, 0, 0⟩ (s.splitOn ", ")

structure Game where
  index : Nat
  samples : Array Sample
deriving Repr

-- def Game.fromStr (s : Substring) : Option Game :=
--   if let some s := s.dropPrefix? "Game " then
--     if let some (index, samples) := s.splitOnce ": " then
--       let index := index.toNat?.get!
--       let samples := (samples.splitOn "; ").filterMap Sample.fromStr
--       some ⟨index, samples⟩
--     else
--       none
--   else
--     none

def Game.parser : Parsec Game := do
  let _ ← Parsec.skipString "Game "
  let index ← Nat.parser
  let _ ← Parsec.skipString ": "
  Parsec.pure {index, samples := (← Parsec.separated (Parsec.skipString "; ") Sample.parser)}

def Game.isValid (g : Game) : Bool :=
  g.samples.all (fun s => s.red <= 12 ∧ s.green <= 13 ∧ s.blue <= 14)

-- #eval Game.parser.run "Game 3: 17 red; 3 blue"

-- #eval Sample.fromStr "3 blue, 4 red"
-- #eval ("3 blue, 4 red".splitOn ", ")[1].splitOnce " "
-- #eval  "4 red".splitOnce " "

-- example : Game.fromStr ("Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue;")  =  some ⟨1, []⟩ := by rfl

def main : IO Unit := do
  let input ← readInput
  let games := input.mapM Game.parser.run
  match games with
  | .ok games =>
    let validGames := games.filter Game.isValid
    let res1 := (validGames.map fun g => g.index).foldl (. + .) 0
    IO.println s!"{res1}"

    let maxSamples := games.map fun g => g.samples.foldl Sample.max ⟨0, 0, 0⟩
    let res2 := (maxSamples.map Sample.power).foldl (. + .) 0
    IO.println s!"{res2}"

  | .error err => IO.println s!"Error {err}"
