import «Aoc2023»
import Mathlib

open Lean

inductive Card where
| joker
| two
| three
| four
| five
| six
| seven
| eight
| nine
| ten
| jack
| queen
| king
| ace
deriving Repr, Inhabited, Ord, DecidableEq

instance : LT Card where
  lt (a b : Card) := Ord.compare a b == Ordering.lt

instance : BEq Card where
  beq (a b : Card) := Ord.compare a b == Ordering.eq

instance : LE Card where
  le (a b : Card) := a < b ∨ a = b

def Card.parser : Parsec Card :=
  let p (c : Char) (card : Card) := Parsec.pchar c >>= fun _ => pure card
  p 'A' .ace <|> p 'K' .king <|> p 'Q' .queen <|> p 'J' .jack <|>
  p 'T' .ten <|> p '9' .nine <|> p '8' .eight <|> p '7' .seven <|>
  p '6' .six <|> p '5' .five <|> p '4' .four <|> p '3' .three <|>
  p '2' .two

def Hand := { a : Array Card // a.size = 5 }
deriving Repr

def Hand.cards (h : Hand) := h.val

def Hand.parser : Parsec Hand := do
  let cards ← Parsec.many Card.parser
  if h : cards.size = 5 then
    return ⟨cards, h⟩
  else
    Parsec.fail ""

instance : Inhabited Hand where
  default := ⟨#[Inhabited.default, Inhabited.default, Inhabited.default, Inhabited.default, Inhabited.default], rfl⟩

@[reducible]
def Array.count (p : α → Bool) (as : Array α) : Nat := (as.filter p).size

@[reducible]
def FiveOfKind (h : Hand) (c : Card) : Prop := h.cards.count (· = c) = 5

@[reducible]
def FourOfKind (h : Hand) (c : Card) : Prop := h.cards.count (· = c) = 4

@[reducible]
def FullHouse (h : Hand) (c₁ c₂ : Card) {_ : c₁ ≠ c₂} : Prop := h.cards.count (· = c₁) = 2 ∧ h.cards.count (· = c₂) = 3

@[reducible]
def ThreeOfKind (h : Hand) (c : Card) : Prop := h.cards.count (· = c) = 3 ∧ h.cards.toList.toFinset.card ≥ 3

@[reducible]
def TwoPair (h : Hand) (c₁ c₂ : Card) {_ : c₁ ≠ c₂} : Prop := h.cards.count (· = c₁) = 2 ∧ h.cards.count (· = c₂) = 2

@[reducible]
def OnePair (h : Hand) (c : Card) : Prop := h.cards.count (· = c) = 2 ∧ h.cards.toList.toFinset.card ≥ 4

@[reducible]
def High (h : Hand) : Prop := h.cards.toList.toFinset.card ≥ 5

-- Classify hand by its type
def type (h : Hand) : Nat := Id.run do
  if High h then
    return 0
  for c in h.cards do
    if OnePair h c then
      return 1
    else if ThreeOfKind h c then
      return 3
    else if FourOfKind h c then
      return 5
    else if FiveOfKind h c then
      return 6
  for c₁ in h.cards do
    for c₂ in h.cards do
      if h' : c₁ = c₂ then
        continue
      else if @TwoPair h c₁ c₂ h' then
        return 2
      else if @FullHouse h c₁ c₂ h' then
        return 4
  assert! false
  return 0

def arrcmp {α : Type} [Ord α] (a b : List α) : Ordering :=
  match a, b with
  | [], [] => Ordering.eq
  | _, [] => Ordering.gt
  | [], _ => Ordering.lt
  | x :: xs, y :: ys =>
    let o := Ord.compare x y
    if o = Ordering.eq then
      arrcmp xs ys
    else
      o

def Hand.compare1 (a b : Hand) : Ordering :=
  let a_type := type a
  let b_type := type b
  if a_type = b_type then
    arrcmp a.cards.toList b.cards.toList
  else
    Ord.compare a_type b_type

def Hand.jacksToJokers (h : Hand) : Hand :=
  let cards := h.val.map fun c => match c with
    | .jack => Card.joker
    | c => c
  have h : cards.size = 5 := by
    have h' : cards.size = h.val.size := Array.size_map _ h.val
    simp [h', h.property]
  ⟨cards, h⟩

def Card.allNonJoker : List Card := [.two, .three, .four, .five, .six, .seven, .eight, .nine, .ten, .queen, .king, .ace]
def Hand.allJokerAssignmentsAux : List Card → List (List Card)
| [] => []
| c :: [] => match c with
  | .joker => ([·]) <$> Card.allNonJoker
  | c => [[c]]
| c :: cs => match c with
  | .joker => Card.allNonJoker >>= fun c => ((c :: ·) <$> Hand.allJokerAssignmentsAux cs)
  | c => (c :: ·) <$> Hand.allJokerAssignmentsAux cs

def Hand.allJokerAssignments (h : Hand) : List Hand :=
  let cards := Hand.allJokerAssignmentsAux h.cards.data
  cards.map fun h => ⟨h.toArray, by sorry⟩

def Hand.compare2 (a b : Hand) : Ordering :=
  let a := a.jacksToJokers
  let b := b.jacksToJokers
  let aj := a.allJokerAssignments
  let bj := b.allJokerAssignments

  let a_type := aj.map type |>.maximum
  let b_type := bj.map type |>.maximum
  if a_type = b_type then
    arrcmp a.cards.toList b.cards.toList
  else
    Ord.compare a_type b_type

structure HandWithBid where
  hand : Hand
  bid : Nat
deriving Repr, Inhabited

def HandWithBid.parser : Parsec HandWithBid := do
  let hand ← Hand.parser
  let _ ← Parsec.ws
  let bid ← Nat.parser
  let _ ← Parsec.pchar '\n'
  return { hand, bid }

def HandWithBid.jacksToJokers (h : HandWithBid) : HandWithBid := { h with hand := h.hand.jacksToJokers }

def main : IO Unit := do
  let input ← readAll
  match (Parsec.many HandWithBid.parser <* Parsec.eof).run input with
  | .ok hands =>
    let hands_in_order := hands.qsort (fun a b => Hand.compare1 a.hand b.hand = Ordering.lt)|>.toList
    let res1 := hands_in_order.enum.map (fun (idx, h) => (idx+1)*h.bid) |>.foldr (· + ·) 0
    IO.println s!"Part 1: {res1}"

    let hands_in_order := hands.qsort (fun a b => Hand.compare2 a.hand b.hand = Ordering.lt)|>.toList
    let res2 := hands_in_order.enum.map (fun (idx, h) => (idx+1)*h.bid) |>.foldr (· + ·) 0
    IO.println s!"Part 2: {res2}"
  | .error err => IO.println s!"Failed ot parse input: {err}"
