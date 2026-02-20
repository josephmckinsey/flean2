import Flean2.NormalFloatRounding
import Mathlib.Data.Sign.Defs


inductive SignedNumber (F1 F2 : Type*) where
  | pos : F1 → SignedNumber F1 F2
  | zero : SignedNumber F1 F2
  | neg : F2 → SignedNumber F1 F2

variable {F1 F2 : Type*} {X : Type*} [Field X]

def SignedNumber.interp (i1 : F1 → X) (i2 : F2 → X) : SignedNumber F1 F2 → X
  | pos f => i1 f
  | zero => 0
  | neg f => -i2 f

variable {i1 : F1 → X} {i2 : F2 → X}

@[simp, grind =]
theorem SignedNumber.interp_zero :
    (SignedNumber.zero.interp i1 i2) = (0 : X) := by rfl

@[simp, grind =]
theorem SignedNumber.interp_pos_normal (f : F1) :
    ((SignedNumber.pos f).interp i1 i2) = (i1 f : X) := by rfl

@[simp, grind =]
theorem SignedNumber.interp_neg_normal (f : F2) :
    ((SignedNumber.neg f).interp i1 i2) = (-i2 f : X) := by rfl

def SignedNumber.interp_injective (h1 : Function.Injective i1) (h2 : Function.Injective i2)
    [PartialOrder X] [IsOrderedAddMonoid X] (l1 : ∀ f, 0 < i1 f) (l2 : ∀ f, 0 < i2 f)
    : Function.Injective (SignedNumber.interp i1 i2) := by
  intro a b h
  unfold interp at h
  unfold Function.Injective at h1 h2
  grind

instance [PartialOrder F1] [PartialOrder F2] : PartialOrder (SignedNumber F1 F2) where
  le x y := match x, y with
    | .pos x', .pos y' => x' ≤ y'
    | .pos _, .zero => False
    | .pos _, .neg _ => False
    | .neg x', .neg y' => y' ≤ x'
    | .neg _ , .zero => True
    | .neg _ , .pos _ => True
    | .zero, .zero => True
    | .zero, .pos _ => True
    | .zero, .neg _ => False
  le_refl := by grind
  le_trans _ _ _ ha hb := by grind
  le_antisymm a b ha hb := by grind [le_antisymm]

/-

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
-/
variable [PartialOrder X] [DecidableLT X]

def round_signed (r1 : X → F1) (r2 : X → F2) (x : X) : SignedNumber F1 F2 :=
  match SignType.sign x with
  | .neg => .neg (r2 (-x))
  | .zero => .zero
  | .pos => .pos (r1 x)

theorem round_signed_EqOn_pos {r1 : X → F1} {r2 : X → F2} :
    Set.EqOn (round_signed r1 r2) (SignedNumber.pos ∘ r1) (Set.Ioi 0) := by
  intro x xh
  unfold round_signed
  rw [sign_eq_one_iff.mpr xh]
  rfl

theorem round_signed_EqOn_neg {r1 : X → F1} {r2 : X → F2} :
    Set.EqOn (round_signed r1 r2) (SignedNumber.neg ∘ r2 ∘ Neg.neg) (Set.Iio 0) := by
  intro x xh
  unfold round_signed
  rw [sign_eq_neg_one_iff.mpr xh]
  rfl

@[simp]
theorem round_signed_zero {r1 : X → F1} {r2 : X → F2} :
    round_signed r1 r2 0 = SignedNumber.zero := by unfold round_signed; rw [sign_zero]

section

variable {r1 : X → F1} {r2 : X → F2} {s1 s2 : Set X}

@[grind =]
theorem round_signed_image_pos_eq (h1 : s1 ⊆ Set.Ioi 0) :
    round_signed r1 r2 '' s1 = SignedNumber.pos '' (r1 '' s1) :=
  Set.image_image SignedNumber.pos r1 _  ▸ Set.image_congr (round_signed_EqOn_pos.mono h1)

@[grind =]
theorem round_signed_image_neg_eq [IsOrderedAddMonoid X] (h1 : s2 ⊆ Set.Ioi 0) :
    round_signed r1 r2 '' (-s2) = SignedNumber.neg '' (r2 '' s2) :=
  let : SignedNumber.neg (F1 := F1) '' (r2 '' s2) =
      (fun x ↦ SignedNumber.neg (r2 (-x))) '' (-s2) := by
    simp_rw [Set.image_image, <-Set.image_neg_eq_neg, Set.image_image, neg_neg]
  this ▸ Set.image_congr (round_signed_EqOn_neg.mono
    (Set.neg_subset.mpr (Set.neg_Iio (0 : X) ▸ neg_zero (G := X).symm ▸ h1))
  )

@[simp, grind =]
theorem round_signed_image_zero_eq : round_signed r1 r2 '' {0} = {SignedNumber.zero} := by simp

variable [PartialOrder F1] [PartialOrder F2]

def round_signed_image_eq [IsOrderedAddMonoid X] (h1 : s1 ⊆ Set.Ioi 0) (h2 : s2 ⊆ Set.Ioi 0) :
    SignedNumber.pos '' (r1 '' s1) ∪ SignedNumber.neg '' (r2 '' s2) ∪ {.zero} =
    (round_signed r1 r2 '' (s1 ∪ (-s2) ∪ {0})) := by
  grind only [Set.image_union, = round_signed_image_zero_eq, = round_signed_image_pos_eq,
    = round_signed_image_neg_eq]

theorem SignedNumber.pos_mono : StrictMono (SignedNumber.pos (F1 := F1) (F2 := F2)) :=
  Monotone.strictMono_of_injective (fun _ _ h ↦ h) (fun _ _ h => SignedNumber.pos.inj h)

theorem round_signed_mono_pos [approx1 : PartialRounder i1 r1 s1] (h1 : s1 ⊆ Set.Ioi 0) :
    MonotoneOn (round_signed r1 r2) s1 :=
  (SignedNumber.pos_mono.monotone.comp_monotoneOn approx1.r_mono).congr
    (round_signed_EqOn_pos.symm.mono h1)

end

variable {r1 : X → F1} {r2 : X → F2} {s1 s2 : Set X} [LinearOrder F1] [PartialOrder F2]

theorem interp_pos_image_eq [approx1 : PartialRounder i1 r1 s1] :
    (SignedNumber.interp i1 i2) '' (.pos '' (r1 '' s1))  = i1 '' (r1 '' s1) := by
  rw [Set.image_image]
  exact Set.image_congr fun x xh ↦ SignedNumber.interp_pos_normal x

theorem interp_mono_pos [approx1 : PartialRounder i1 r1 s1] :
    MonotoneOn (SignedNumber.interp i1 i2) (.pos '' (r1 '' s1)) := by
  intro x ⟨f, xh⟩ y ⟨g, yh⟩ h
  rw [<-xh.2, <-yh.2, SignedNumber.interp_pos_normal]
  apply approx1.i_mono
  · exact xh.1
  · exact yh.1
  rw [<-xh.2, <-yh.2] at h
  exact SignedNumber.pos_mono.le_iff_le.mp h


-- Use iUnion from SignType to (-s2), {}, s1
-- Those three map to .neg '' (r2 '' s2), {0}, .pos '' (r1 '' s2)
-- Make monotoneOn for (-s2), {}, s1
-- left inverse should be relatively easy with a normal case split + image eq lemmas

/-
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

-/
