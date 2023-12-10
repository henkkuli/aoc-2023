import «Aoc2023»

open Lean
open Std

structure Card where
  index : Nat
  winning : Array Nat
  own : Array Nat
deriving Repr

def Card.parser : Parsec Card :=
  let p1 := Parsec.skipString "Card" *> Parsec.ws *> Nat.parser <* (Parsec.skipString ":")
  let p2 := Parsec.many $ Parsec.attempt $ Parsec.ws *> Nat.parser
  let p3 := Parsec.skipString " |"
  let p4 := Parsec.many $ Parsec.attempt $ Parsec.ws *> Nat.parser
  p1 >>= fun index =>
    p2 <* p3 >>= fun winning =>
      p4 <* Parsec.eof >>= fun own =>
        Parsec.pure {index, winning, own}


def main : IO Unit := do
  let input ← readInput
  match input.mapM Card.parser.run with
  | .ok cards =>
    let mut res := 0
    for card in cards do
      let intersection := card.own.toList ∩ card.winning.toList
      let points := if intersection.length > 0 then 2 ^ (intersection.length-1) else 0
      res := res + points

    IO.println s!"Part 1: {res}"

    let rec loop : List Card → List Nat
    | [] => []
    | card :: cards =>
      let tail := loop cards
      let points := (card.own.toList ∩ card.winning.toList).length
      let cardCount := (tail.take points).foldl (· + ·) 1

      cardCount :: tail

    res := (loop cards).foldl (· + ·) 0
    IO.println s!"Part 2: {res}"

  | .error err => IO.println s!"Failed to parse input: {err}"
