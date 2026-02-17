import Mathlib.Algebra.Order.Field.Power
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Flean2.MathlibLemmas

abbrev interp_pair (X : Type*) [Field X] (f : ℤ × ℤ) : X := f.1 * (2 : X)^f.2
def interp_e {X : Type*} [Field X] (e : ℤ) (f : ℤ) : X := ↑f * 2^e

-- This one is a partial order.
@[ext]
structure NormalNumber (p : ℕ) where
  m : ℤ
  e : ℤ
  bound : 2^p <= m ∧ m < 2^(p + 1) := by simp

def NormalNumber.interp {p : ℕ} (X : Type*) [Field X] (f : NormalNumber p) : X :=
  f.m * 2^f.e

def NormalNumber.interp_pos {p : ℕ} (X : Type*) [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] (f : NormalNumber p) : 0 < f.interp X :=
   mul_pos (Int.cast_pos.mpr (lt_of_lt_of_le (by positivity) f.bound.1)) (by positivity)

theorem NormalNumber.interp_bound {p : ℕ} (X : Type*) [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] [FloorRing X] (f : NormalNumber p) :
    2^(f.e + p) ≤ f.interp X ∧ f.interp X < 2^(f.e + p + 1):= by
  unfold interp
  constructor
  · rw [add_comm, zpow_add₀ (by norm_num)]
    apply (mul_le_mul_iff_left₀ (by positivity)).mpr
    exact_mod_cast f.bound.1
  rw [add_assoc, add_comm, zpow_add₀ (by norm_num)]
  apply (mul_lt_mul_iff_left₀ (by positivity)).mpr
  exact_mod_cast f.bound.2

def NormalNumber.proj (f : NormalNumber p) : ℤ × ℤ := (f.m, f.e)

theorem NormalNumber.interp_proj [Field X] {f : NormalNumber p} :
    f.interp X = interp_pair X f.proj := by
  simp [interp_pair, interp, proj]

theorem NormalNumber.interp_e_proj [Field X] {f : NormalNumber p} :
    f.interp X = interp_e f.e f.m := by
  simp [interp_e, interp]

theorem NormalNumber.log2_interp {p : ℕ} (X : Type*) [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] [FloorRing X] (f : NormalNumber p) :
    Int.log 2 (f.interp X) = f.e + p := by
  apply (Int.log_eq_iff (by norm_num) (by exact_mod_cast f.interp_pos X)).mpr
  exact_mod_cast f.interp_bound X

theorem NormalNumber.interp_injective {p : ℕ} (X : Type*)
    [Field X] [LinearOrder X] [IsStrictOrderedRing X] [FloorRing X] :
    Function.Injective (NormalNumber.interp X (p := p)) := by
  intro f1 f2 h
  have e_eq: f1.e = f2.e := by
    rw [<-add_left_inj, <-log2_interp X f1, <-log2_interp X f2, h]
  rw [interp, interp, e_eq,
    mul_right_cancel_iff_of_pos (by positivity), Int.cast_inj] at h
  exact NormalNumber.ext h e_eq

instance : PartialOrder (NormalNumber p) where
  le x y := x.interp ℚ <= y.interp ℚ
  le_refl := by simp
  le_trans _ _ _ ha hb := le_trans ha hb
  le_antisymm a b ha hb := NormalNumber.interp_injective ℚ
    (le_antisymm ha hb)

theorem NormalNumber.interp_X_rat (X : Type*)
    [Field X] [LinearOrder X] [IsStrictOrderedRing X]
    (f : NormalNumber p) : (interp ℚ f : X) = interp X f := by
  simp [interp]

theorem NormalNumber.le_def (X : Type*)
    [Field X] [LinearOrder X] [IsStrictOrderedRing X]
    (f1 f2 : NormalNumber p) : f1 <= f2 ↔ f1.interp X <= f2.interp X := by
  change f1.interp ℚ <= f2.interp ℚ ↔ f1.interp X <= f2.interp X
  rw [<-f1.interp_X_rat X, <- f2.interp_X_rat X, Rat.cast_le]

theorem NormalNumber.interp_strictMono (X : Type*)
    [Field X] [LinearOrder X] [IsStrictOrderedRing X] [FloorRing X] :
    StrictMono (NormalNumber.interp X (p := p)) :=
  Monotone.strictMono_of_injective
    (fun x y h ↦ (le_def X x y).mp h)
    (interp_injective X)
