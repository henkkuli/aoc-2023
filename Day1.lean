import «Aoc2023»

def takeDigits (line : String) : List Nat :=
  List.filterMap (fun c => c.toString.toNat?) line.toList

def takeWordDigits (line : String) : List Nat :=
  let rec loop (s : List Char) : List Nat :=
    match s with
    | c :: rest =>
      if "one".toList.isPrefixOf s then
        1 :: loop rest
      else if "two".toList.isPrefixOf s then
        2 :: loop rest
      else if "three".toList.isPrefixOf s then
        3 :: loop rest
      else if "four".toList.isPrefixOf s then
        4 :: loop rest
      else if "five".toList.isPrefixOf s then
        5 :: loop rest
      else if "six".toList.isPrefixOf s then
        6 :: loop rest
      else if "seven".toList.isPrefixOf s then
        7 :: loop rest
      else if "eight".toList.isPrefixOf s then
        8 :: loop rest
      else if "nine".toList.isPrefixOf s then
        9 :: loop rest
      else if let some v := c.toString.toNat? then
        v :: loop rest
      else
        loop rest
    | [] => []

  loop line.data

def main : IO Unit := do
  let input ← readInput

  let mut sum := 0
  let mut sum2 := 0
  for line in input do
    let digits := takeDigits line
    sum := sum + digits.head! * 10 + digits.getLast!
    let digits := takeWordDigits line
    sum2 := sum2 + digits.head! * 10 + digits.getLast!

  IO.println s!"{sum}"
  IO.println s!"{sum2}"
