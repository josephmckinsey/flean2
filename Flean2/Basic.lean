import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Rify
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Module.Basic

section

variable {X : Type*} {F : Type*} [PartialOrder X] [PartialOrder F]

structure ValidRounder (i : X → F) (r : F → X) : Prop where
  r_mono : Monotone r
  i_mono : Monotone i
  left_inverse : Function.LeftInverse r i

variable {r : X → F} {i : F → X}

@[simp]
theorem ValidRounder.r_of_i_eq (approx : ValidRounder i r) (f : F) :
    r (i f) = f := by rw [approx.left_inverse]


theorem ValidRounder.i_strictMono (approx : ValidRounder i r) : StrictMono i :=
  Monotone.strictMono_of_injective approx.i_mono approx.left_inverse.injective

def ValidRounder.id : ValidRounder (id : X → X) (id : X → X) where
  r_mono := fun ⦃_ _⦄ h ↦ h
  i_mono := fun ⦃_ _⦄ h ↦ h
  left_inverse := congrFun rfl

def ValidRounder.comp {F' : Type*} [PartialOrder F'] (r' : F → F') (i' : F' → F)
    (approx : ValidRounder i r) (approx' : ValidRounder i' r')
    : ValidRounder (i.comp i') (r'.comp r) where
  r_mono := Monotone.comp approx'.r_mono approx.r_mono
  i_mono := Monotone.comp approx.i_mono approx'.i_mono
  left_inverse := Function.LeftInverse.comp approx.left_inverse approx'.left_inverse

def ValidRounder.ofGaloisInsertion {conn : GaloisInsertion r i} : ValidRounder i r where
  r_mono := conn.gc.monotone_l
  i_mono := conn.gc.monotone_u
  left_inverse := conn.leftInverse_l_u

def ValidRounder.ofGaloisCoinsertion {conn : GaloisCoinsertion i r} : ValidRounder i r where
  r_mono := conn.gc.monotone_u
  i_mono := conn.gc.monotone_l
  left_inverse := conn.u_l_leftInverse

@[grind .]
theorem ValidRounder.l_le_r_of_f_le_x (approx : ValidRounder i r) {x : X} {f : F}
    (h : i f ≤ x) : f ≤ r x :=
  approx.r_of_i_eq f ▸ approx.r_mono h

@[grind .]
theorem ValidRounder.r_le_f_of_x_le_f (approx : ValidRounder i r) {x : X} {f : F}
    (h : x ≤ i f) : r x ≤ f :=
  -- this is cute
  approx.r_of_i_eq f ▸ approx.r_mono h


-- If x <= min F, then r x = min F.
-- If x >= max F, then r x = max F.

-- Ceil is a GaloisInsertion (not needed)
-- Floor is a GaloisCoinsertion (not needed)

end

section

variable {X : Type*} {F : Type*} [PartialOrder X]
variable [CompleteLinearOrder F] {i : F → X}

def round_down (i : F → X) : X → F :=
  fun x ↦ sSup { f : F | i f <= x }

def round_down_mono : Monotone (round_down i) := by
  unfold round_down
  intro x y h
  grind only [sSup_le_sSup_of_subset_insert_bot, = Set.subset_def, = Set.mem_insert_iff,
    usr Set.mem_setOf_eq]

def round_down_ValidRounder (i_strictMono : StrictMono i) : ValidRounder i (round_down i) where
  r_mono := round_down_mono
  i_mono := i_strictMono.monotone
  left_inverse := by
    unfold round_down
    intro f
    simp_rw [i_strictMono.le_iff_le]
    rw [Set.Iic_def]
    exact csSup_Iic

def round_up (i : F → X) : X → F :=
  fun x ↦ sInf { f : F | x <= i f}

def round_up_mono : Monotone (round_up i) := by
  unfold round_up
  intro x y h
  simp only [le_sInf_iff, Set.mem_setOf_eq]
  intro f h'
  apply sInf_le_of_le (b := f) ?_ le_rfl
  grind

def round_up_ValidRounder (i_strictMono : StrictMono i) : ValidRounder i (round_up i) where
  r_mono := round_up_mono
  i_mono := i_strictMono.monotone
  left_inverse := by
    unfold round_up
    intro f
    simp_rw [i_strictMono.le_iff_le]
    rw [Set.Ici_def]
    exact csInf_Ici

@[grind! .]
theorem validRounder_le_round_up (approx : ValidRounder i r) (x : X) :
    r x ≤ round_up i x := by
  unfold round_up
  rw [@le_sInf_iff]
  intro f h
  simp only [Set.mem_setOf_eq] at h
  rw [show f = r (i f) by rw [approx.r_of_i_eq]]
  exact approx.r_mono h

@[grind! .]
theorem round_down_le_validRounder (approx : ValidRounder i r) (x : X) :
    round_down i x ≤ r x := by
  unfold round_down
  rw [@sSup_le_iff]
  intro f h
  simp only [Set.mem_setOf_eq] at h
  rw [show f = r (i f) by rw [approx.r_of_i_eq]]
  exact approx.r_mono h

@[grind .]
theorem validRounder_eq_round_down_of_r_le_x (approx : ValidRounder i r) (x : X)
    (h : i (r x) <= x) : r x = round_down i x := by
  unfold round_down
  apply le_antisymm
  · exact CompleteLattice.le_sSup {f | i f ≤ x} (r x) h
  simp_rw [sSup_le_iff, Set.mem_setOf_eq]
  grind

@[grind .]
theorem validRounder_eq_round_up_of_x_le_r (approx : ValidRounder i r) (x : X)
    (h : x <= i (r x)) : r x = round_up i x := by
  unfold round_up
  apply le_antisymm
  · simp_rw [le_sInf_iff, Set.mem_setOf_eq]
    grind
  exact CompleteLattice.sInf_le {f | x ≤ i f} (r x) h

end

section

variable {X : Type*} {F : Type*} [LinearOrder X]
variable [CompleteLinearOrder F] {i : F → X}

theorem validRounder_eq_round_up_or_round_down (approx : ValidRounder i r)
    (x : X) : r x = round_up i x ∨ r x = round_down i x := by
  cases le_total (i (r x)) x with
  | inl h => grind
  | inr h => grind

-- Still need to prove that round_down and round_up are equal to floor and ceiling
-- so we get the same lemmas for FloorRings.

#check FloorRing.gc_coe_floor

#check FloorRing.floor

#check Real.exists_floor


-- Why isn't grind automatically accessing the member elements of approx?

-- TODO List:
-- [ ] Invertible monotone functions are valid rounders
-- [ ] Ring operations on rounders (addition, multiplication)
-- [ ] Figure out why grind isn't unpacking approx elements automatically.
-- [ ] FloorRings have round_down = floor and round_up = ceil.
-- [ ] Minimum and maximum element lemmas
-- [ ] Gluing operations: binary and Σ based.
-- [ ] Adding new bottom and top elements (not a priority, may be unnecessary)

end
