import «Aoc2023»
import Mathlib
import Mathlib.Data.Real.NNReal

open Lean
open NNReal

structure Race where
  time : Nat
  distance : Nat
deriving Repr, Inhabited

def Race.parseMany : Parsec $ Array Race :=
  Parsec.pstring "Time:" *> Parsec.many (Parsec.attempt $ Parsec.ws *> Nat.parser) <* Parsec.pstring "\n" >>= fun times =>
  Parsec.pstring "Distance:" *> Parsec.many (Parsec.attempt $ Parsec.ws *> Nat.parser) <* Parsec.pstring "\n" <* Parsec.eof >>= fun distances =>
  Parsec.pure $ (times.zip distances).map fun (time, distance) => { time, distance }

def Race.parseOne : Parsec Race :=
  let numParser : Parsec Nat := Parsec.manyChars (Parsec.many (Parsec.satisfy (· == ' ')) *> Parsec.digit) >>= fun n =>
    match n.toNat? with
    | some n => Parsec.pure n
    | none => Parsec.fail s!"Invalid number {n}"
  Parsec.pstring "Time:" *> numParser <* Parsec.pstring "\n" >>= fun time =>
  Parsec.pstring "Distance:" *> numParser <* Parsec.pstring "\n" <* Parsec.eof >>= fun distance =>
  Parsec.pure { time, distance }


def dt (x t : Nat) : Nat := x * (t - x)
noncomputable def dtℝ' (x t : ℝ≥0) : ℝ≥0 := x * (t - x)
noncomputable def dtℝ (x t : ℝ) : ℝ := x * (t - x)

theorem dt_eq_dtℝ' : ∀ x t : ℕ, dt x t = dtℝ' x t := by simp [dt, dtℝ']
theorem dtℝ'_eq_dtℝ : ∀ x t : ℝ≥0, x ≤ t → dtℝ' x t = dtℝ x t := by
  intros x t h
  simp [dtℝ, dtℝ', h]

noncomputable def dtLbℝ (t d : ℝ) : ℝ := t/2 - (t^2 / 4 - d).sqrt
noncomputable def dtUbℝ (t d : ℝ) : ℝ := t/2 + (t^2 / 4 - d).sqrt


theorem lt_of_lt_sub_nonneg {a b c : ℝ} (h₁ : 0 ≤ c) (h₂ : a ≤ b - c) : a ≤ b := by
  have h' : b - c ≤ b := by simp [h₁]
  exact @le_trans _ _ a (b-c) b h₂ h'

theorem lt_of_add_nonneg_lt {a b c : ℝ} (h₁ : 0 ≤ c) (h₂ : a + c ≤ b) : a ≤ b := by
  have h' : a ≤ a + c  := by simp [h₁]
  exact @le_trans _ _ a (a+c) b h' h₂

theorem dtLbℝ_is_lb : ∀ x t d : ℝ, x ≤ dtLbℝ t d → dtℝ x t ≤ d := by
  intros x t d h
  simp [dtLbℝ] at h

  have x_lt_t_half : x ≤ t/2 := by
    exact lt_of_lt_sub_nonneg (Real.sqrt_nonneg _) h

  have h : Real.sqrt (t ^ 2 / 4 - d) ≤ t / 2 - x := by
    rw [←add_le_add_iff_right $ x - Real.sqrt (t ^ 2 / 4 - d)]
    simp
    exact h
  have h : t ^ 2 / 4 - d ≤ (t / 2 - x) ^ 2 := by
    have h' : t / 2 - x ≥ 0 := by simp [x_lt_t_half]
    rw [←Real.sqrt_le_left h']
    exact h

  -- have foo : ∀ x : ℝ, x ^ 2 = x * x := by
  --   intros x
  --   sorry

  -- -- repeat rw [foo] at h
  -- -- rw [mul_sub, sub_mul, sub_mul] at h
  -- -- have h : t * t / 4 - d ≤ t * t / 4 - x * t + x * x := by
  -- --   linarith [h]

  -- -- have h : t * t / 4 + -d ≤ t * t / 4 + (-x * t + x * x) := by
  -- --   rw [←sub_eq_add_neg, ←add_assoc, neg_mul,  ←sub_eq_add_neg]
  -- --   exact h
  -- -- have h : -d ≤ -x * t + x * x := by simp_all
  -- -- have h : -d ≤ -(x * t - x * x) := by simp_all
  -- have h : -d ≤ -(x * t - x * x) := by linarith [h]
  -- -- have h : d ≥ x * t - x * x := by
  -- --   rw [GE.ge]
  -- --   rw [←neg_le_neg_iff]
  -- --   exact h
  -- -- have h : d ≥ x * (t - x) := by
  -- --   rw [mul_sub]
  -- --   exact h

  -- -- simp [dtℝ, h]
  rw [dtℝ]
  linarith [h]

theorem dtUbℝ_is_ub : ∀ x t d : ℝ, dtUbℝ t d ≤ x → dtℝ x t ≤ d := by
  intros x t d h
  simp [dtUbℝ] at h

  have x_gt_t_half : t/2 ≤ x := by
    exact lt_of_add_nonneg_lt (Real.sqrt_nonneg _) h

  have h : Real.sqrt (t ^ 2 / 4 - d) ≤ x - t/2 := by linarith [h]
  have h : t ^ 2 / 4 - d ≤ (x - t/2) ^ 2 := by
    have h' : x - t/2 ≥ 0 := by simp [x_gt_t_half]
    rw [←Real.sqrt_le_left h']
    exact h

  rw [dtℝ]
  linarith [h]

theorem dtUbℝ_is_ub2 : ∀ x t d : ℝ, dtUbℝ t d ≤ x → dtℝ x t ≤ d := by
  intros x t d h
  simp [dtUbℝ] at h
  -- have h : Real.sqrt (t ^ 2 / 4 - d) ≤ x - t/2 := by linarith [h]
  have h : t ^ 2 / 4 - d ≤ (x - t/2) ^ 2 := by
    have h' : x - t/2 ≥ 0 := by nlinarith! [Real.sqrt_nonneg (t ^ 2 / 4 - d)]
    rw [←Real.sqrt_le_left h']
    nlinarith! (config := {transparency := .all })

  rw [dtℝ]
  nlinarith! (config := {transparency := .all }) [h, Real.sqrt_nonneg]

theorem foo : ∀ x t d : ℝ, dtLbℝ t d ≤ x → x ≤ dtUbℝ t d → dtℝ x t ≥ d := by
  intros x t d h₁ h₂
  rw [dtLbℝ] at h₁
  rw [dtUbℝ] at h₂
  rw [dtℝ]

  have h₁ : t / 2 - x ≤ Real.sqrt (t ^ 2 / 4 - d) := by linarith
  have h₂ : x - t / 2 ≤ Real.sqrt (t ^ 2 / 4 - d) := by linarith
  have h₁ : (t / 2 - x) ^ 2 ≤ t ^ 2 / 4 - d := by
    rw [Real.sq_le]
    sorry
    -- have h : x ≤ t/2 ∨ x ≥ t/2 := by sorry

    -- have h' : x - t/2 ≥ 0 := by sorry -- nlinarith! [Real.sqrt_nonneg (t ^ 2 / 4 - d)]
    -- rw [←Real.le_sqrt]
    -- linarith
    -- linarith

    sorry

  sorry

def dtLb (t d : ℕ) : ℕ :=
  let x := t/2 - (t^2 / 4 - d).sqrt
  if dt x t ≤ d then
    x + 1
  else
    x

def dtUb (t d : ℕ) : ℕ :=
  let x := (t+1)/2 + (t^2 / 4 - d).sqrt
  if dt x t ≤ d then
    x - 1
  else
    x

theorem dt_symmetric : ∀ t x : ℕ, x ≤ t → dt x t = dt (t - x) t := by
  intros t x h
  repeat rw [dt]
  rw [Nat.sub_sub_self h]
  ring

theorem dtLb_sufficient : ∀ x t d : ℕ, dtLb t d ≤ x → x ≤ dtUb t d → dt x t > d := by
  intros x t d h₁ h₂
  rw [dt]
  cases Classical.em (x ≤ t/2)
  case inl h =>
    rw [dtLb] at h₁
    sorry
  · sorry

def waysToWin (r : Race) : ℕ := 1 + dtUb r.time r.distance - dtLb r.time r.distance

def main : IO Unit := do
  let input ← readAll
  match Race.parseMany.run input with
  | .ok races =>
    let res := races |>.map waysToWin |>.foldr (· * ·) 1
    IO.println s!"{res}"
  | .error err => IO.println s!"Failed ot parse input: {err}"
  match Race.parseOne.run input with
  | .ok race =>
    let res := waysToWin race
    IO.println s!"{res}"
  | .error err => IO.println s!"Failed ot parse input: {err}"
