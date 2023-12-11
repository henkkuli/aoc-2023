import «Aoc2023»

open Lean

structure Range where
  start : Nat
  stop : Nat
deriving Repr, Inhabited

abbrev RangeSet := List Range

structure PartiallyMappedRangeSet where
  unmapped : RangeSet
  mapped : RangeSet
deriving Repr, Inhabited

def PartiallyMappedRangeSet.pure (u : RangeSet) : PartiallyMappedRangeSet :=
  { unmapped := u, mapped := [] }

structure Mapping where
  src : Nat
  dest : Nat
  len : Nat
deriving Repr, Inhabited

def Mapping.parser : Parsec Mapping :=
  Nat.parser <* Parsec.ws >>= fun dest =>
  Nat.parser <* Parsec.ws >>= fun src =>
  Nat.parser <* Parsec.pstring "\n" >>= fun len =>
  pure {src, dest, len}

def Mapping.map? (m : Mapping) (v : Nat) : Option Nat :=
  if m.src <= v ∧ v <= m.src + m.len then
    m.dest + (v - m.src)
  else
    none

def Mapping.mapRange (m : Mapping) (r : PartiallyMappedRangeSet) : PartiallyMappedRangeSet :=
  let rec loop : List Range → PartiallyMappedRangeSet
    | [] => { mapped := [], unmapped := [] }
    | x :: xs =>
      let r := loop xs
      if x.stop <= m.src ∨ m.src + m.len <= x.start then
        {
          mapped := r.mapped,
          unmapped := x :: r.unmapped,
        }
      else
        let u1 : RangeSet := if x.start < m.src then [⟨x.start, m.src⟩] else []
        let u2 : RangeSet := if x.stop > m.src + m.len then [⟨m.src + m.len, x.stop⟩] else []
        let m : RangeSet := [⟨m.dest + (x.start - m.src), m.dest + min (x.stop - m.src) m.len⟩]
        {
          mapped := m ++ r.mapped,
          unmapped := u1 ++ u2 ++ r.unmapped
        }

  let mapped := loop r.unmapped
  {
    mapped := mapped.mapped ++ r.mapped,
    unmapped := mapped.unmapped
  }

-- #eval (Mapping.mk 50 52 48).mapRange $ PartiallyMappedRangeSet.pure [⟨79, 79+14⟩, ⟨55, 55+13⟩, ⟨1, 51⟩]

structure CategoryMapping where
  source : String
  target : String
  mappings : Array Mapping
deriving Repr, Inhabited

def CategoryMapping.parser : Parsec CategoryMapping :=
  Parsec.many1Chars (Parsec.satisfy (· != '-')) <* Parsec.pstring "-to-" >>= fun source =>
  Parsec.many1Chars (Parsec.satisfy (· != ' ')) <* Parsec.pstring " map:\n" >>= fun target =>
  Parsec.many1 Mapping.parser >>= fun mappings =>
  pure {source, target, mappings}

def CategoryMapping.map (m : CategoryMapping) (v : Nat) : Nat :=
  (m.mappings.findSome? (Mapping.map? · v)).getD v

def CategoryMapping.mapRange (m : CategoryMapping) (r : RangeSet) : RangeSet :=
  let r := PartiallyMappedRangeSet.pure r
  let rec loop (m : List Mapping) (r : PartiallyMappedRangeSet) : PartiallyMappedRangeSet :=
    match m with
    | [] => r
    | x :: xs =>
      loop xs $ x.mapRange r

  let r := loop m.mappings.toList r
  r.mapped ++ r.unmapped

structure Almanach where
  seeds : Array Nat
  mappings : Array CategoryMapping
deriving Repr, Inhabited

def Almanach.mapSeed (a : Almanach) (v : Nat) : Nat :=
  let rec loop (type : String) (mapping : List CategoryMapping) (v : Nat) :=
    match mapping with
    | [] =>
      assert! type == "location"
      v
    | x :: xs =>
      assert! x.source == type
      let v := x.map v
      loop x.target xs v
  loop "seed" a.mappings.toList v

def Almanach.mapSeedRange (a : Almanach) (v : RangeSet) : RangeSet :=
  let rec loop (type : String) (mapping : List CategoryMapping) (v : RangeSet) :=
    match mapping with
    | [] =>
      assert! type == "location"
      v
    | x :: xs =>
      assert! x.source == type
      let v := x.mapRange v
      loop x.target xs v
  loop "seed" a.mappings.toList v

def Almanach.parser : Parsec Almanach :=
  Parsec.pstring "seeds:" *> Parsec.many (Parsec.attempt $ Parsec.ws *> Nat.parser) >>= fun seeds =>
  Parsec.many (Parsec.ws *> CategoryMapping.parser) >>= fun mappings =>
  pure {seeds, mappings}

def main : IO Unit := do
  let input ← readAll
  match Almanach.parser.run input with
  | .ok input =>
    let r1 := (input.seeds.map input.mapSeed).toList.minimum?.getD 0
    IO.println s!"Part 1: {r1}"

    let rec range : List Nat → RangeSet
      | [] => []
      | [_] => []
      | x :: y :: xs => ⟨x, x+y⟩ :: range xs
    let seeds := range input.seeds.toList
    let r2 := input.mapSeedRange seeds
    let r2 := (r2.map (·.start)).minimum?.getD 0
    IO.println s!"Part 2: {r2}"

  | .error err => IO.println s!"Failed ot parse input: {err}"
