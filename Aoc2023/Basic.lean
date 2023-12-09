import «Std»

partial def readInput : IO (List String) := do
  let rec loop (stream : IO.FS.Stream) (res : (List String)) : IO (List String) := do
    let buf ← stream.getLine
    if buf.isEmpty then
      pure res
    else
      let buf := buf.dropRightWhile Char.isWhitespace
      loop stream (buf :: res)
  pure (←loop (←IO.getStdin) List.nil).reverse


def String.splitOnce (s : String) (sep : String) : Option (String × String) :=
  let index := s.findSubstr? sep
  index.map (fun i => (s.extract 0 i.startPos, s.extract i.stopPos s.endPos))

def Substring.splitOnce (s : Substring) (sep : Substring) : Option (Substring × Substring) :=
  let index := s.findSubstr? sep
  index.map (fun i => ⟨s.extract 0 i.startPos, s.extract i.stopPos s.stopPos⟩)

-- theorem String_splitOnce_eq_Substring_splitOnce :
--     ∀ (s set : String), s.splitOnce sep = s.toSubstring.splitOnce sep :=
--   -- by simp_all
--   sorry
