import «Aoc2023»

open Lean

structure Part where
  type : Char
  x : Nat
  y : Nat
deriving Repr

structure Number where
  val : Nat
  x : Nat × Nat
  y : Nat
deriving Repr


def dotCounter : Parsec Nat :=
  (fun (count, _) => count) <$> Parsec.withLength (Parsec.many $ Parsec.pchar '.')

def Part.parser (x y : Nat) : Parsec Part :=
  (Part.mk · x y) <$> Parsec.satisfy fun c => c ≠ '.' ∧ ¬c.isDigit

def Number.parser (x y : Nat) : Parsec Number :=
  (fun (len, val) => Number.mk val (x, x+len) y) <$> Parsec.withLength Nat.parser

abbrev LineParserReader := ReaderT (Nat × Array Part × Array Number) Parsec $ Array Part × Array Number

partial def lineParser.loop (y : Nat) : LineParserReader := do
  let dots ← dotCounter
  if dots > 0 then
    return ←withReader (fun (idx, parts, numbers) => (idx + dots, parts, numbers)) (loop y)
  let (idx, parts, numbers) ← read
  let part : LineParserReader := Parsec.withLength (Part.parser idx y) >>= fun (len, part) =>
    withReader (fun (idx, parts, numbers) => (idx + len, parts.push part, numbers)) (loop y)
  let num : LineParserReader := Parsec.withLength (Number.parser idx y) >>= fun (len, number) =>
    withReader (fun (idx, parts, numbers) => (idx + len, parts, numbers.push number)) (loop y)
  let eof : LineParserReader := Parsec.eof >>= fun () => pure (parts, numbers)
  part <|> num <|> eof
  -- sorry

def lineParser (y : Nat) : Parsec $ Array Part × Array Number :=
  lineParser.loop y (0, #[], #[])

abbrev adjacent (n : Number) (p : Part) : Prop :=
  n.x.1 - 1 <= p.x ∧ p.x < n.x.2 + 1 ∧
  n.y - 1 <= p.y ∧ p.y <= n.y + 1


-- #eval (lineParser 5).run "..43x...573y"

def main : IO Unit := do
  let input ← readInput
  match input.enum.mapM fun (y, l) => (lineParser y).run l with
  | .ok lines =>
    let (parts, numbers) := lines.unzip
    let parts := parts.foldl Array.append #[]
    let numbers := numbers.foldl Array.append #[]

    let mut res := 0
    for num in numbers do
      if (parts.find? $ adjacent num).isSome then
        res := res + num.val

    IO.println s!"Part 1: {res}"

    res := 0
    for part in parts do
      if part.type = '*' then
        let adj := numbers.filter (adjacent · part)
        if h : adj.size = 2 then
          have _ : 0 < adj.size := by simp [h]
          have _ : 1 < adj.size := by simp [h]
          res := res + adj[0].val * adj[1].val

    IO.println s!"Part 2: {res}"
  | .error err => IO.println s!"Error parsing input: {err}"
