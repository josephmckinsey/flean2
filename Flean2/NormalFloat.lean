import Mathlib.Algebra.Order.Field.Power
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Bound
import Flean2.MathlibLemmas

def interp_e {X : Type*} [Field X] (e : ℤ) (f : ℤ) : X := ↑f * 2^e
abbrev interp_pair (X : Type*) [Field X] (f : ℤ × ℤ) := interp_e (X := X) f.2 f.1

@[simp, grind =]
theorem interp_e_2pow {X : Type*} [Field X] [two_ne_zero : NeZero (2 : X)] (e : ℤ) (m : ℕ) :
    interp_e e (2 ^ m) = (2 : X) ^ (e + m) := by
  rw [add_comm]
  simp [interp_e, zpow_add₀ (a := (2 : X)) (two_ne_zero.out)]

theorem interp_e_strictMono {X : Type*} [Field X] [LinearOrder X] [IsStrictOrderedRing X]
    (e : ℤ) : StrictMono (interp_e (X := X) e) :=
  Int.cast_strictMono.mul_const (by positivity)

theorem interp_e_Ico [Field X] [LinearOrder X] [IsStrictOrderedRing X] (e : ℤ)
    {m : ℤ} {p : ℕ} (h : m ∈ Set.Ico (2 ^ p) (2 ^ (p + 1))) :
  interp_e e m ∈ Set.Ico ((2 : X) ^ (e + p)) (2 ^ (e + p + 1)) := by
  grind [(interp_e_strictMono (X := X) e).mapsTo_Ico h]

theorem interp_e_Icc [Field X] [LinearOrder X] [IsStrictOrderedRing X] (e : ℤ)
    {m : ℤ} {p : ℕ} (h : m ∈ Set.Icc (2 ^ p) (2 ^ (p + 1))) :
    interp_e e m ∈ Set.Icc ((2 : X) ^ (e + p)) (2 ^ (e + p + 1)) := by
  grind [(interp_e_strictMono (X := X) e).monotone.mapsTo_Icc h]

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
    2^(f.e + p) ≤ f.interp X ∧ f.interp X < 2^(f.e + p + 1) :=
  interp_e_Ico f.e (Set.mem_Ico.mpr f.bound)

def NormalNumber.proj (f : NormalNumber p) : ℤ × ℤ := (f.m, f.e)

theorem NormalNumber.interp_e_proj [Field X] {f : NormalNumber p} :
    f.interp X = interp_e f.e f.m := by
  simp [interp_e, interp]

@[simp]
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
  le x y := x.interp ℚ ≤ y.interp ℚ
  le_refl := by simp
  le_trans _ _ _ ha hb := le_trans ha hb
  le_antisymm a b ha hb := NormalNumber.interp_injective ℚ (le_antisymm ha hb)

@[grind =]
theorem NormalNumber.interp_X_rat (X : Type*)
    [Field X] [LinearOrder X] [IsStrictOrderedRing X]
    (f : NormalNumber p) : (interp ℚ f : X) = interp X f := by
  simp [interp]

@[grind =_]
theorem NormalNumber.le_def (X : Type*)
    [Field X] [LinearOrder X] [IsStrictOrderedRing X]
    {f1 f2 : NormalNumber p} : f1 ≤ f2 ↔ f1.interp X ≤ f2.interp X := by
  change f1.interp ℚ ≤ f2.interp ℚ ↔ f1.interp X ≤ f2.interp X
  rw [<-f1.interp_X_rat X, <- f2.interp_X_rat X, Rat.cast_le]

theorem NormalNumber.interp_strictMono (X : Type*)
    [Field X] [LinearOrder X] [IsStrictOrderedRing X] [FloorRing X] :
    StrictMono (NormalNumber.interp X (p := p)) :=
  Monotone.strictMono_of_injective
    (fun _ _ h ↦ (le_def X).mp h)
    (interp_injective X)

def ulp [Field X] [LinearOrder X] [IsStrictOrderedRing X] [FloorRing X]
    (p : ℕ) (x : X) : X := 2^(Int.log 2 x - p)

theorem ulp_pos [Field X] [LinearOrder X] [IsStrictOrderedRing X] [FloorRing X]
    (p : ℕ) (x : X) : 0 < ulp p x := by unfold ulp; positivity

def NormalNumber.ulp [Field X] {p : ℕ} (f : NormalNumber p) : X := 2^f.e

theorem NormalNumber.ulp_pos [Field X] [LinearOrder X] [IsStrictOrderedRing X] [FloorRing X]
    {p : ℕ} (f : NormalNumber p) : (0 : X) < f.ulp := by unfold ulp; positivity

theorem ulp_interp [Field X] [LinearOrder X] [IsStrictOrderedRing X] [FloorRing X]
    {p : ℕ} (f : NormalNumber p) : ulp p (f.interp X) = f.ulp := by
  simp [ulp, NormalNumber.ulp]
