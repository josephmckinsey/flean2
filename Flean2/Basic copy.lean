import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Rify
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Module.Basic

structure DyadicPos where
  m : ℤ
  e : ℤ

def DyadicPos.interpret : DyadicPos → ℚ
  | ⟨m, e⟩ => m / 2^e


/-!
# Three options

1. We can go to Dyadic as in https://leanprover-community.github.io/mathlib4_docs/Init/Data/Dyadic/Basic.html#Dyadic
  m becomes odd, or the dyadic is 0.
2. We can go to floating point representations where 2^prec ≤ p < 2^(prec+1)
3. We can construct computable reals
-/

def CloseToReal (m : ℤ) (e : ℤ) (x : ℝ) : Prop :=
  |m - x * 2^(-e)| < 1


def IsComputableReal (seq : ℤ → ℤ) (x : ℝ) : Prop :=
  ∀e, CloseToReal (seq e) e x


lemma CloseToReal.eq' (m e : ℤ) (x : ℝ) : CloseToReal m e x ↔ |m * 2^e - x| < 2^e := by
  unfold CloseToReal
  rw [<-mul_lt_mul_iff_left₀ (by positivity : 0 < (2 : ℝ)^e), one_mul]
  nth_rw 1 [<-abs_of_pos (by positivity : 0 < (2 : ℝ)^e)]
  rw [<-abs_mul, sub_mul, zpow_neg, mul_assoc, inv_mul_cancel₀, mul_one]
  positivity

lemma CloseToReal.eq'' (m e : ℤ) (x : ℝ) : CloseToReal m e x ↔ dist (m * (2 : ℝ)^e) x < 2^e := by
  rw [CloseToReal.eq', Real.dist_eq]

/-
Forall x and e, there exists at most two possible values of m.
-/
lemma closeToEq_floor_or_ceil (m e : ℤ) (x : ℝ)
    : CloseToReal m e x ↔ m = ⌊x * 2^(-e)⌋ ∨ m = ⌈x * 2^(-e)⌉ := by
  unfold CloseToReal
  constructor
  · intro h
    suffices ⌊x * 2^(-e)⌋ = m ∨ ⌈x * 2^(-e)⌉ = m by grind only
    rw [Int.floor_eq_iff, Int.ceil_eq_iff]
    grind [abs_sub_lt_iff]
  rw [abs_sub_lt_iff]
  set s := x * 2^(-e)
  rintro (rfl | rfl)
  · constructor
    · grind only [!Int.floor_le]
    have := Int.lt_floor_add_one s
    linarith
  constructor
  · grind only [Int.ceil_lt_add_one]
  linarith [Int.le_ceil s]

/-
If (m, e) is close to x, then ∃ε, m 2^e = x + ε with |ε| < 2^e
-/
lemma CloseToReal.eq_exists_eps (m e : ℤ) (x : ℝ)
    : CloseToReal m e x ↔ ∃ε, |ε| < (2 : ℝ)^e ∧ m * 2^e = x + ε := by
  rw [CloseToReal.eq']
  refine ⟨fun h ↦ ⟨m * 2^e - x, h, by simp⟩, ?_⟩
  intro ⟨ε, h1, h2⟩
  rw [h2, add_sub_cancel_left]
  exact h1

def Int.scaleBy (n scale : ℤ) : ℤ :=
  match scale with
  | .ofNat s => n <<< s
  | .negSucc s => (n >>> s + 1) >>> 1

-- General because ℚ is the initial field for strictly ordered rings
lemma round_div2 (x : ℤ) : round (x/(2 : ℚ)) = (x + 1) / 2 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl]
  rw [<-Rat.floor_intCast_div_natCast, round_eq]
  grind

theorem Int.scaleBy_eq (n scale : ℤ) : n.scaleBy scale = round (n * (2 : ℚ)^scale):= by
  unfold Int.scaleBy
  rcases scale with s | s
  · simp only [shiftLeft_eq, ofNat_eq_natCast, zpow_natCast]
    rw [show (n : ℚ) * 2^s = (n * 2 ^s : ℤ) by norm_cast]
    exact (round_intCast (n * 2 ^ s)).symm
  suffices (n / 2 ^ s + 1) / 2 = round (↑n * ((2 : ℚ) ^ (s + 1))⁻¹) by
    simpa [shiftRight_eq_div_pow]
  rw [<-round_div2]
  rw [show (2^s : ℤ) = ((2^s : ℕ) : ℤ) by rfl]
  rw [<-Rat.floor_intCast_div_natCast]
  rw [pow_succ, mul_inv, <-mul_assoc, Nat.cast_pow, Nat.cast_ofNat]
  rw [<-div_eq_mul_inv, <-div_eq_mul_inv]
  set x := (n : ℚ) / 2^s
  rw [round_eq, round_eq, <-add_div, <-add_div]
  rw [show (2 : ℚ) = (2 : ℕ) by rfl]
  rw [Int.floor_div_natCast, Int.floor_div_natCast]
  simp

theorem Int.abs_scaleBy_sub (n scale : ℤ) :
    |n.scaleBy scale - n * (2 : ℚ)^scale| ≤ 1/2 := by
  rw [Int.scaleBy_eq]
  rw [abs_sub_comm]
  exact abs_sub_round _

-- Very funny
def Int.toCompReal (n : ℤ) (prec : ℤ) : ℤ := n.scaleBy (-prec)

lemma isComputableReal_CompRealOfInt (n : ℤ) : IsComputableReal n.toCompReal n := by
  intro prec
  unfold CloseToReal Int.toCompReal
  have := Int.abs_scaleBy_sub n (-prec)
  rify at this
  linarith

def CompReal.add (s1 s2 : ℤ → ℤ) (prec : ℤ) : ℤ :=
  (s1 (prec - 1) + s2 (prec - 1)) / 4

-- This can be better.
def CompReal.recip (s : ℤ → ℤ) (prec : ℤ) (e : ℤ := -prec) : Option ℤ :=
  let m := s e
  if (2^(e + prec) : ℚ) < m^2 - 1 then
    .some (round ((2 : ℚ)^(e + prec) / m))
  else CompReal.recip s prec (e - 1)
partial_fixpoint

def hello := "world"
