import «Aoc2023»

partial def readInput : IO String := do
  let rec loop (stream : IO.FS.Stream) (res : String) : IO String := do
    let buf ← stream.getLine
    if buf.isEmpty then
      pure res
    else
      loop stream (res ++ buf)
  loop (←IO.getStdin) ""

def main : IO Unit := do
  let input ← readInput
  IO.println s!"{input}"

-- #eval main
