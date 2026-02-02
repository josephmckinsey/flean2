import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Qify

variable {X : Type*} [Field X] [LinearOrder X] [FloorRing X] [IsStrictOrderedRing X]

def round_near (q : X) : ℤ :=
  let i1 := ⌊q⌋
  let i2 := ⌈q⌉
  if Int.fract q < 1/2 then
    i1
  else if 1/2 < Int.fract q then
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

lemma round_near_monotone : Monotone (round_near (X := X)) := by
  intro x y h
  by_cases xy_eq : x = y
  · exact (congrArg round_near xy_eq).le
  unfold round_near
  have floor_x_le_ceil_y : ⌊x⌋ ≤ ⌈y⌉ :=
    (Int.cast_le (R := X)).1 <|
      (Int.floor_le x).trans <| h.trans  <| Int.le_ceil y
  by_cases h' : ⌈x⌉ ≤ ⌊y⌋
  · dsimp; split_ifs <;>
      (try exact Int.floor_le_floor h) <;> (try exact Int.ceil_le_ceil h) <;>
      (try exact floor_x_le_ceil_y) <;> (try exact h')
  replace h' := show ⌊y⌋ < ⌈x⌉ by simpa using h'
  have floor_y_eq_floor_x : ⌊y⌋ = ⌊x⌋ :=
    le_antisymm (Int.le_floor.mpr (Int.lt_ceil.mp h').le)
      (Int.floor_le_floor h)
  replace h := lt_of_le_of_ne h xy_eq
  have fract_x_lt_fract_y : Int.fract x < Int.fract y := by
    unfold Int.fract
    exact floor_y_eq_floor_x ▸ sub_lt_sub_right h ↑⌊x⌋
  if h1 : Int.fract x < 1/2 then
    simp only [h1, reduceIte]
    split_ifs <;> (try exact Int.floor_le_floor h.le) <;>
      (try exact floor_x_le_ceil_y)
  else
    have fract_y : 1/2 < Int.fract y := by grind
    have not_fract_y : ¬(Int.fract y < 1/2) := by grind
    rw [if_neg not_fract_y, if_pos fract_y]
    dsimp; split_ifs <;>
      (try exact floor_x_le_ceil_y) <;>
      (try exact Int.ceil_le_ceil h.le)

lemma round_near_eq_of (x : X) (z : ℤ) (h1 : z - 1 / 2 < x) (h2 : x < z + 1 / 2) :
    z = round_near x := by
  if h3 : z ≤ x then
    have : Int.fract x = x - z := by
      apply Int.fract_eq_iff.mpr
      grind
    rw [round_near, this]
    simp_rw [sub_lt_iff_lt_add, add_comm, h2]
    simp only [↓reduceIte]
    apply (Int.floor_eq_iff.mpr ⟨h3, lt_trans h2 (by linarith)⟩).symm
  else
    replace h3 := lt_of_not_ge h3
    have floor_eq : ⌊x⌋ = z - 1 := by
      suffices ⌊x⌋ + 1 = z from
        (Int.sub_eq_iff_eq_add.mpr this.symm).symm
      rw [<-Int.floor_add_one]
      exact Int.floor_eq_iff.mpr ⟨by linarith, (add_lt_add_iff_right 1).mpr h3⟩
    have fract_eq : Int.fract x = x - (z - 1) := by
      rw [Int.fract]
      suffices (⌊x⌋ : X) = z - 1 by linarith
      norm_cast
    rw [round_near, fract_eq]
    have : 1/2 < x - (z - 1) := by linarith
    simp_rw [if_neg (not_lt_of_gt this), if_pos this]
    exact (Int.ceil_eq_iff.mpr ⟨by linarith, le_of_lt h3⟩).symm

lemma fract_eq_ceil_of_pos {q : X} (h : 0 < Int.fract q) :
  Int.fract q = q + 1 - ⌈q⌉ := by
  rcases Int.fract_eq_zero_or_add_one_sub_ceil q
  · linarith
  assumption

lemma round_near_le (q : X) :
  |round_near q - q| ≤ 1/2 := by
  unfold round_near
  simp only [Int.cast_ite]
  split_ifs with h1 h2 h3
  · rw [abs_sub_comm, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg q)]
    exact le_of_lt h1
  · rw [abs_of_nonneg (by linarith [Int.le_ceil q])]
    rw [fract_eq_ceil_of_pos (by linarith)] at h2
    linarith
  · rw [abs_sub_comm, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg q),
      le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)]
  have : Int.fract q = 1/2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
  rw [abs_of_nonneg (by linarith [Int.le_ceil q])]
  rw [fract_eq_ceil_of_pos (by linarith)] at this
  linarith

lemma round_near_of_int (z : ℤ) : round_near (z : X) = z := by
  simp [round_near, Int.fract_intCast]

lemma round_near_add_half (z : ℤ) (h : z % 2 = 0) :
  round_near ((z : X) + 1/2) = z := by
  rw [round_near]
  simp only [show Int.fract (1 / 2 : X) = (1/2 : X) by norm_num,
    Int.fract_intCast_add, lt_self_iff_false, ↓reduceIte, Int.floor_intCast_add,
    show ⌊(1 / 2 : X)⌋ = 0 by norm_num]
  simp [h]

lemma round_near_sub_half (z : ℤ) (h : z % 2 = 0) :
  round_near ((z : X) - 1/2) = z := by
  rw [sub_eq_add_neg, round_near]
  simp only [Int.fract_intCast_add, reduceIte, lt_self_iff_false,
    Int.floor_intCast_add,
    show Int.fract (-(1 / 2) : X) = (1 / 2 : X) by norm_num,
    show ⌊-(1 / 2 : X)⌋ = -1 by norm_num]
  rw [if_neg (by grind), add_comm, Int.ceil_add_intCast,
    show ⌈-(1/2 : X)⌉ = 0 by norm_num, zero_add]

lemma round_of_add_half (z : ℤ) : round_near ((z : X) + 1/2) % 2 = 0 := by
  rw [round_near, show Int.fract (z + 1/2 : X) = 1/2 by norm_num]
  simp only [lt_self_iff_false, ↓reduceIte, Int.floor_intCast_add]
  rw [add_comm (z : X), Int.ceil_add_intCast, show ⌊(1 : X) / 2⌋ = 0 by norm_num, add_zero]
  split_ifs with h
  · assumption
  rw [show ⌈(1 : X) / 2⌉ = 1 by norm_num]
  grind
