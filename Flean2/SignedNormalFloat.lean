import Flean2.NormalFloatRounding
import Mathlib.Data.Sign.Defs

inductive SignedNormal (p : ℕ) where
  | pos : NormalNumber p → SignedNormal p
  | zero : SignedNormal (p : ℕ)
  | neg : NormalNumber p → SignedNormal p

def SignedNormal.interp (X : Type*) [Field X] : SignedNormal p → X
  | pos f => f.interp X
  | zero => 0
  | neg f => -f.interp X

@[simp, grind =]
theorem SignedNormal.interp_zero {X : Type*} [Field X] :
    ((SignedNormal.zero (p := p)).interp X) = 0 := by unfold interp; simp

@[simp, grind =]
theorem SignedNormal.interp_pos_normal {X : Type*} [Field X] (f : NormalNumber p) :
    ((SignedNormal.pos f).interp X) = f.interp X := by unfold interp; simp

@[simp, grind =]
theorem SignedNormal.interp_neg_normal {X : Type*} [Field X] (f : NormalNumber p) :
    ((SignedNormal.neg f).interp X) = -f.interp X := by unfold interp; simp

def SignedNormal.interp_injective {p : ℕ} (X : Type*) [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] [FloorRing X] :
    Function.Injective (SignedNormal.interp X (p := p)) := by
  intro a b h
  have interp_inj : ∀a b : NormalNumber p, a.interp X = b.interp X → a = b := fun a b h ↦
    NormalNumber.interp_injective X h
  have interp_pos : ∀a : NormalNumber p, 0 < a.interp X := fun a ↦ a.interp_pos (X := X)
  unfold interp at h
  grind

instance : PartialOrder (SignedNormal p) where
  le x y := x.interp ℚ ≤ y.interp ℚ
  le_refl := by simp
  le_trans _ _ _ ha hb := le_trans ha hb
  le_antisymm a b ha hb := SignedNormal.interp_injective ℚ (le_antisymm ha hb)

@[grind =]
theorem SignedNormal.interp_X_rat (X : Type*)
    [Field X] [LinearOrder X] [IsStrictOrderedRing X]
    (f : SignedNormal p) : (interp ℚ f : X) = interp X f := by
  unfold interp
  grind [Rat.cast_zero, Rat.cast_neg]

theorem SignedNormal.le_def (X : Type*) [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] {f1 f2 : SignedNormal p} :
    f1 ≤ f2 ↔ f1.interp X ≤ f2.interp X := by
  change f1.interp ℚ ≤ f2.interp ℚ ↔ f1.interp X ≤ f2.interp X
  rw [<-f1.interp_X_rat X, <-f2.interp_X_rat X, Rat.cast_le]

theorem SignedNormal.interp_strictMono (X : Type*)
    [Field X] [LinearOrder X] [IsStrictOrderedRing X] [FloorRing X] :
    StrictMono (SignedNormal.interp X (p := p)) :=
  Monotone.strictMono_of_injective
    (fun _ _ h ↦ (le_def X).mp h) (interp_injective X)

variable {X : Type*} [Field X] [LinearOrder X] [FloorRing X] [IsStrictOrderedRing X]

def round_signed_normal (r_neg r_pos : X → ℤ) [ValidRounder ((↑) : ℤ → X) r_neg]
    [ValidRounder ((↑) : ℤ → X) r_pos] (p : ℕ) (x : X) : SignedNormal p :=
  match SignType.sign x with
  | .neg => .neg (round_normal r_neg p (-x))
  | .zero => .zero
  | .pos => .pos (round_normal r_pos p x)

variable {r_neg r_pos : X → ℤ} [ValidRounder ((↑) : ℤ → X) r_neg]
variable [ValidRounder ((↑) : ℤ → X) r_pos]

@[grind =]
theorem round_signed_normal_pos {p : ℕ} {x : X} (h : 0 < x) :
    (round_signed_normal r_neg r_pos p x) = SignedNormal.pos (round_normal r_pos p x) := by
  rw [round_signed_normal, sign_eq_one_iff.mpr h]

@[grind =]
theorem round_signed_normal_neg {p : ℕ} {x : X} (h : x < 0) :
    (round_signed_normal r_neg r_pos p x) = SignedNormal.neg (round_normal r_neg p (-x)) := by
  rw [round_signed_normal, sign_eq_neg_one_iff.mpr h]

@[simp, grind =]
theorem round_signed_normal_zero {p : ℕ} :
    (round_signed_normal r_neg r_pos p (0 : X)) = SignedNormal.zero := by
  rw [round_signed_normal, sign_zero]

-- Simplify these so they don't need le_def
def SignedNormal.pos_strictMono {p : ℕ} : StrictMono (SignedNormal.pos (p := p)) :=
  Monotone.strictMono_of_injective
    (fun _ _ h ↦ (le_def ℚ).mpr <| (interp_pos_normal (X := ℚ) _) ▸ (NormalNumber.le_def ℚ).mp h)
    (fun _ _ h ↦ SignedNormal.pos.inj h)

def SignedNormal.neg_strictMono {p : ℕ} : StrictAnti (SignedNormal.neg (p := p)) :=
  Antitone.strictAnti_of_injective
    (fun _ _ h ↦ (le_def ℚ).mpr <|
      interp_neg_normal (X := ℚ) _ ▸ neg_le_neg ((NormalNumber.le_def ℚ).mp h))
    (fun _ _ h ↦ SignedNormal.neg.inj h)

/-!

# Informal proof

We can use the same monotone gluing lemmas, but now we have that
round_signed_normal is a valid rounder on 0 < x. Unfortunately, r '' {0 < x} = NormalNumber p
must be explicitly recorded somehow... right?

To show that it's a valid rounder on x > 0, we need
1. round_signed_normal = .pos (round_normal r_pos p x) for x > 0.
2. .pos preserves rounding somehow. It's strictly mono.
3. interp (.pos x) = interp x

-/

def round_signed_normal_interp : Function.LeftInverse
    (round_signed_normal r_neg r_pos p) (SignedNormal.interp X) := by
  intro x
  rcases x with x | _ | x
  · rw [SignedNormal.interp_pos_normal, round_signed_normal_pos, round_normal_interp]
    exact NormalNumber.interp_pos X x
  · simp
  rw [SignedNormal.interp_neg_normal, round_signed_normal_neg, neg_neg, round_normal_interp]
  exact neg_neg_iff_pos.mpr (NormalNumber.interp_pos X x)

def round_signed_normal_monoPos : MonotoneOn (round_signed_normal r_neg r_pos p)
    (Set.Ioi (0 : X)) :=
  fun _ xh _ yh h ↦
    round_signed_normal_pos (r_neg := r_neg) (r_pos := r_pos) xh ▸
    round_signed_normal_pos (r_neg := r_neg) (r_pos := r_pos) yh ▸
      SignedNormal.pos_strictMono.monotone (round_normal_monoOn _ xh yh h)

-- I need the MapsTo lemmas still.
