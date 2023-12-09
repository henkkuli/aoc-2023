import Lean

open Lean

partial def Parsec.separated.loop (sep : Parsec Unit) (p : Parsec α) (acc : Array α): Parsec (Array α) := do
  let acc := acc.push $ ←p
  (sep >>= fun () => loop sep p acc) <|> Parsec.pure acc

def Parsec.separated (sep : Parsec Unit) (p : Parsec α) : Parsec (Array α) :=
  Parsec.separated.loop sep p #[]

def Nat.parser : Parsec Nat :=
  Parsec.many1Chars Parsec.digit >>=
    fun v => match v.toNat? with
             | none => Parsec.fail s!"Invalid number {v}"
             | some v => Parsec.pure v
