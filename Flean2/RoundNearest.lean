module

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Qify
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Field.Defs

variable {X : Type*} [Field X] [LinearOrder X] [FloorRing X] [IsStrictOrderedRing X]

public def round_near (q : X) : ℤ :=
  let i1 := ⌊q⌋
  let i2 := ⌈q⌉
  if Int.fract q < 2⁻¹ then
    i1
  else if 2⁻¹ < Int.fract q then
    i2
  else if i1 % 2 = 0 then
    i1
  else
    i2

/-
Round nearest preserves order.

Suppose q1 and q2 are far enough away (⌈q1⌉ ≤ ⌊q2⌋), then it is obviously
true in all cases.

If ⌈q1⌉ > ⌊q2⌋, then ⌈q1⌉ = ⌈q2⌉ and ⌊q1⌋ = ⌊q2⌋, then we have
Int.frac q1 ≤ Int.frac q2.

If Int.frac q1 < 1/2, then we round to ⌊q1⌋,
and
-/

public lemma round_near_monotone : Monotone (round_near (X := X)) := by
  intro x y h
  by_cases xy_eq : x = y
  · exact (congrArg round_near xy_eq).le
  unfold round_near
  -- These can't really automatically be found.
  have floor_x_le_ceil_x : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_le_floor h
  have ceil_x_le_ceil_y : ⌈x⌉ ≤ ⌈y⌉ := Int.ceil_le_ceil h
  have floor_x_le_ceil_y : ⌊x⌋ ≤ ⌈y⌉ :=
    (Int.cast_le (R := X)).1 <|
      (Int.floor_le x).trans <| h.trans  <| Int.le_ceil y
  by_cases h' : ⌈x⌉ ≤ ⌊y⌋
  · grind -- a lot of annoying casework using local hypotheses
  replace h' := show ⌊y⌋ < ⌈x⌉ by simpa using h'
  have floor_y_eq_floor_x : ⌊y⌋ = ⌊x⌋ :=
    le_antisymm (Int.le_floor.mpr (Int.lt_ceil.mp h').le)
      (Int.floor_le_floor h)
  -- Essentially floor_y_eq_floor_x ▸ sub_lt_sub_right h ↑⌊x⌋
  have fract_x_lt_fract_y : Int.fract x < Int.fract y := by grind only [Int.fract]
  grind only -- It's all casework from here.

@[grind .]
public lemma round_near_eq_of (x : X) (z : ℤ) (h1 : z - 2⁻¹ < x) (h2 : x < z + 2⁻¹) :
    round_near x = z := by
  if h3 : z ≤ x then
    have : Int.fract x = x - z := Int.fract_eq_iff.mpr (by grind only)
    grind [round_near, Int.floor_eq_iff]
  else
    replace h3 := lt_of_not_ge h3
    have floor_eq : ⌊x⌋ = z - 1 := by
      grind [Int.floor_add_one, Int.floor_eq_iff]
    have fract_eq : Int.fract x = x - (z - 1) := by simp [Int.fract, floor_eq]
    suffices z = ⌈x⌉ by grind [round_near]
    exact (Int.ceil_eq_iff.mpr ⟨by linarith, le_of_lt h3⟩).symm

lemma fract_eq_ceil_of_pos {q : X} (h : 0 < Int.fract q) :
  Int.fract q = q + 1 - ⌈q⌉ := by
  grind [Int.fract_eq_zero_or_add_one_sub_ceil]

public lemma round_near_le (q : X) :
  -2⁻¹ ≤ round_near q - q ∧ (round_near q - q) ≤ 2⁻¹ := by
  unfold round_near
  grind only [fract_eq_ceil_of_pos, !Int.fract_nonneg, !Int.le_ceil, !Int.self_sub_floor]

public lemma round_near_leftInverse : Function.LeftInverse round_near ((↑) : ℤ → X) :=
  fun x => by simp [round_near, Int.fract_intCast]

@[simp, grind =]
public lemma round_near_of_int (z : ℤ) : round_near (z : X) = z :=
  round_near_leftInverse z


@[simp, grind =]
public lemma round_near_add_half (z : ℤ) (h : z % 2 = 0) :
  round_near ((z : X) + 2⁻¹) = z := by
  unfold round_near
  have t1 : Int.fract 2⁻¹ = (2⁻¹ : X) := by norm_num
  have t2 : ⌊(2⁻¹ : X)⌋ = 0 := by norm_num
  grind only [Int.fract_intCast_add, Int.floor_intCast_add]

@[simp, grind =]
public lemma round_near_sub_half (z : ℤ) (h : z % 2 = 0) :
  round_near ((z : X) - 2⁻¹) = z := by
  have t1 : Int.fract (-2⁻¹) = (2⁻¹ : X) := by norm_num
  have t2 : ⌊(-2⁻¹ : X)⌋ = -1 := by norm_num
  have t3 : ⌈(-2⁻¹ : X)⌉ = 0 := by norm_num
  unfold round_near
  grind only [sub_eq_add_neg, Int.fract_intCast_add, Int.floor_intCast_add, Int.ceil_intCast_add]

public lemma round_of_add_half (z : ℤ) : round_near ((z : X) + 2⁻¹) % 2 = 0 := by
  rw [round_near, show Int.fract (z + 2⁻¹ : X) = 2⁻¹ by norm_num]
  have : ⌈(2⁻¹ : X)⌉ = 1 := by norm_num
  have : ⌊(2⁻¹ : X)⌋ = 0 := by norm_num
  grind [Int.floor_intCast_add, Int.ceil_intCast_add]
