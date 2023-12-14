import Lake
open Lake DSL

package «aoc-2023» where
  -- add package configuration options here

lean_lib «Aoc2023» where
  -- add library configuration options here

require std from git
   "https://github.com/leanprover/std4/" @ "v4.3.0"

require mathlib from git
   "https://github.com/leanprover-community/mathlib4" @ "v4.3.0"

@[default_target]
lean_exe «day1» where
  root := `Day1

@[default_target]
lean_exe «day2» where
  root := `Day2

@[default_target]
lean_exe «day3» where
  root := `Day3

@[default_target]
lean_exe «day4» where
  root := `Day4

@[default_target]
lean_exe «day5» where
  root := `Day5

@[default_target]
lean_exe «day6» where
  root := `Day6
