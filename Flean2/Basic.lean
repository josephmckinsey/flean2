import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Rify
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Floor.Div
import Flean2.RoundNearest

section

variable {X : Type*} {F : Type*}

structure ValidRounder [Preorder X] [Preorder F] (i : F → X) (r : X → F) : Prop where
  r_mono : Monotone r
  i_mono : Monotone i
  left_inverse : Function.LeftInverse r i

variable {r : X → F} {i : F → X} [PartialOrder X] [PartialOrder F]

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

def ValidRounder.ofGaloisInsertion (conn : GaloisInsertion r i) : ValidRounder i r where
  r_mono := conn.gc.monotone_l
  i_mono := conn.gc.monotone_u
  left_inverse := conn.leftInverse_l_u

def ValidRounder.ofGaloisCoinsertion (conn : GaloisCoinsertion i r) : ValidRounder i r where
  r_mono := conn.gc.monotone_u
  i_mono := conn.gc.monotone_l
  left_inverse := conn.u_l_leftInverse

def ValidRounder.ofOrderIso (iso : OrderIso X F) : ValidRounder iso.symm iso where
  r_mono := iso.monotone
  i_mono := iso.symm.monotone
  left_inverse := iso.right_inv

--@[grind .]
theorem ValidRounder.f_le_r_of_f_le_x (approx : ValidRounder i r) {x : X} {f : F}
    (h : i f ≤ x) : f ≤ r x :=
  approx.r_of_i_eq f ▸ approx.r_mono h

--@[grind .]
theorem ValidRounder.r_le_f_of_x_le_f (approx : ValidRounder i r) {x : X} {f : F}
    (h : x ≤ i f) : r x ≤ f :=
  -- this is cute
  approx.r_of_i_eq f ▸ approx.r_mono h

theorem ValidRounder.r_le_bot [botInst : OrderBot F] (approx : ValidRounder i r) {x : X}
    (h : x ≤ i ⊥) : r x = ⊥ := le_bot_iff.mp (r_le_f_of_x_le_f approx h)

theorem ValidRounder.top_le_r [topInst : OrderTop F] (approx : ValidRounder i r) {x : X}
    (h : i ⊤ ≤ x) : r x = ⊤ := top_le_iff.mp (f_le_r_of_f_le_x approx h)


/-
The usual definition of rounding down relies on the existence of some suprema.
We can avoid this in certain cases:

sSup { f : F | i f <= x } = f'
iff ∀g s.t. (∀f, i f <= x → f <= g), then f' <= g,
  and ∀f, i f <= x → f <= f'  (trivially satisfied for all rounders)

So we only need the "least" part of "least upper bound"
-/
def IsRoundDown (i : F → X) (r : X → F) : Prop :=
  ∀x, ∀g, (∀ f, i f <= x → f <= g) → r x <= g

def IsRoundUp (i : F → X) (r : X → F) : Prop :=
  ∀x, ∀g, (∀ f, x <= i f → g <= f) → g <= r x

-- "True" Ceil is a GaloisInsertion
-- "True" Floor is a GaloisCoinsertion

def ValidRounder.toGaloisInsertion (approx : ValidRounder i r) (h : ∀ x, x <= i (r x)) :
    GaloisInsertion r i :=
  .monotoneIntro approx.i_mono approx.r_mono h approx.left_inverse

def ValidRounder.toGaloisCoinsertion (approx : ValidRounder i r) (h : ∀ x, i (r x) <= x) :
    GaloisCoinsertion i r :=
  .monotoneIntro approx.r_mono approx.i_mono h approx.left_inverse

def IsRoundDown.of_i_r_le (h : ∀ x, i (r x) ≤ x) : IsRoundDown i r :=
  fun x _ a ↦ a (r x) (h x)

def IsRoundUp.of_le_i_r (h : ∀ x, x ≤ i (r x)) : IsRoundUp i r :=
  fun x _ a ↦ a (r x) (h x)

def IsRoundDown.ofGaloisConnection (conn : GaloisConnection i r) : IsRoundDown i r :=
  .of_i_r_le conn.l_u_le

def IsRoundUp.ofGaloisConnection (conn : GaloisConnection r i) : IsRoundUp i r :=
  .of_le_i_r conn.le_u_l

theorem IsRoundUp.le {r_up : X → F} (is_up : IsRoundUp i r_up)
    (approx : ValidRounder i r) (x : X) : r x ≤ r_up x :=
  is_up x _ (fun _ a ↦ approx.r_le_f_of_x_le_f a)

theorem IsRoundDown.le {r_down : X → F} (is_down : IsRoundDown i r_down)
    (approx : ValidRounder i r) (x : X) : r_down x ≤ r x :=
  is_down x _ (fun _ a ↦ approx.f_le_r_of_f_le_x a)

@[grind .]
theorem validRounder_eq_round_down_of_r_le_x (approx : ValidRounder i r) (x : X)
    {r' : X → F} (approx_down : ValidRounder i r') (is_down : IsRoundDown i r')
    (h : i (r x) <= x) : r x = r' x :=
  le_antisymm
    (approx_down.f_le_r_of_f_le_x h)
    (is_down x _ (fun _ a ↦ approx.f_le_r_of_f_le_x a))

@[grind .]
theorem validRounder_eq_round_up_of_x_le_r (approx : ValidRounder i r) (x : X)
    {r' : X → F} (approx_up : ValidRounder i r') (is_up : IsRoundUp i r')
    (h : x <= i (r x)) : r x = r' x :=
  le_antisymm
    (is_up x _ (fun _ a ↦ approx.r_le_f_of_x_le_f a))
    (approx_up.r_le_f_of_x_le_f h)

theorem IsRoundUp.unique {r r' : X → F} (approx : ValidRounder i r) (is_up : IsRoundUp i r)
    (approx' : ValidRounder i r') (is_up' : IsRoundUp i r') : r = r' :=
  funext fun x ↦ le_antisymm (is_up'.le approx x) (is_up.le approx' x)

theorem IsRoundDown.unique {r r' : X → F} (approx : ValidRounder i r) (is_down : IsRoundDown i r)
    (approx' : ValidRounder i r') (is_down' : IsRoundDown i r') : r = r' :=
  funext fun x ↦ le_antisymm (is_down.le approx' x) (is_down'.le approx x)

end

section

variable {X : Type*} {F : Type*} [Preorder X]
variable {i : F → X}

def round_down [SupSet F] (i : F → X) : X → F :=
  fun x ↦ sSup { f : F | i f <= x }

def round_up [InfSet F] (i : F → X) : X → F :=
  fun x ↦ sInf { f : F | x <= i f}

end

section

variable {X : Type*} {F : Type*} [PartialOrder X]
variable [CompleteLinearOrder F] {i : F → X}

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

def round_down_IsRoundDown : IsRoundDown i (round_down i) :=
  fun _ _ h ↦ sSup_le h

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

def round_up_IsRoundUp : IsRoundUp i (round_up i) :=
  fun _ _ h ↦ le_sInf h

@[grind! .]
theorem validRounder_le_round_up (approx : ValidRounder i r) (x : X) :
    r x ≤ round_up i x :=
  round_up_IsRoundUp.le approx x

@[grind! .]
theorem round_down_le_validRounder (approx : ValidRounder i r) (x : X) :
    round_down i x ≤ r x :=
  round_down_IsRoundDown.le approx x

end

section

variable {X : Type*} {F : Type*} [LinearOrder X]
variable [PartialOrder F] {i : F → X}

theorem validRounder_eq_round_up_or_round_down (approx : ValidRounder i r)
    {r_down : X → F} (approx_down : ValidRounder i r_down) (is_down : IsRoundDown i r_down)
    {r_up : X → F} (approx_up : ValidRounder i r_up) (is_up : IsRoundUp i r_up)
    (x : X) : r x = r_down x ∨ r x = r_up x := by
  cases le_total (i (r x)) x with
  | inl h => grind
  | inr h => grind

end

section

variable {X : Type*} {F : Type*} [Preorder X] [Preorder F]

structure PartialRounder (i : F → X) (r : X → F) (s : Set X) (t : Set F) : Prop where
  r_mono : MonotoneOn r s
  i_mono : MonotoneOn i t
  left_inverse : Set.LeftInvOn r i t
  r_map : s.MapsTo r t
  i_map : t.MapsTo i s

variable {i : F → X} {r : X → F} {s : Set X} {t : Set F}

def PartialRounder.restrict (approx : PartialRounder i r s t) :
    ValidRounder approx.i_map.restrict approx.r_map.restrict where
  r_mono := by
    intro ⟨x, xh⟩ ⟨y, yh⟩
    rw [Subtype.mk_le_mk, Subtype.mk_le_mk]
    exact approx.r_mono xh yh
  i_mono := by
    intro ⟨x, xh⟩ ⟨y, yh⟩
    rw [Subtype.mk_le_mk, Subtype.mk_le_mk]
    exact approx.i_mono xh yh
  left_inverse := by
    intro ⟨x, xh⟩
    rw [Subtype.mk.injEq]
    exact approx.left_inverse xh

def ValidRounder.toPartialRounderOfImageEq (approx : ValidRounder i r) (h : s.MapsTo r t)
    (h' : t.MapsTo i s) : PartialRounder i r s t where
  r_mono := Monotone.monotoneOn approx.r_mono s
  i_mono := Monotone.monotoneOn approx.i_mono t
  left_inverse x _ := approx.left_inverse x
  r_map _ xh := Set.mem_preimage.mp (h xh)
  i_map _ fh := Set.mem_preimage.mp (h' fh)

def ValidRounder.iff_PartialRounder : ValidRounder i r ↔ PartialRounder i r .univ .univ where
  mpr approx := {
    r_mono := monotoneOn_univ.mp approx.r_mono
    i_mono := monotoneOn_univ.mp approx.i_mono
    left_inverse := fun f ↦ approx.left_inverse (Set.mem_univ f)
  }
  mp approx := {
    r_mono := approx.r_mono.monotoneOn _
    i_mono := approx.i_mono.monotoneOn _
    left_inverse x _ := approx.left_inverse x
    r_map x _ := Set.mem_univ (r x)
    i_map f _ := Set.mem_univ (i f)
  }

theorem PartialRounder.r_s_eq_t (approx : PartialRounder i r s t) : r '' s = t :=
  subset_antisymm (Set.image_subset_iff.mpr approx.r_map)
    fun f fh ↦ ⟨i f, approx.i_map fh, approx.left_inverse fh⟩


/-
def PartialRounder.mono {s₂ : Set X} {t₂ : Set F} (approx : PartialRounder i r s t)
    (h : s₂ ⊆ s) (h' : t₂ ⊆ t) : PartialRounder i r s₂ t₂ where
  r_mono := sorry
  i_mono := sorry
  left_inverse := sorry
  r_map := sorry
  i_map := approx.i_map.mono h' h

-/


end

section

variable {X : Type*} {F : Type*} [PartialOrder X] [PartialOrder F]

variable {i : F → X} {r : X → F} {s : Set X} {t : Set F}

def MonotoneOn.union_lowerBound {s1 s2 : Set X} (le1 : s1 ⊆ lowerBounds s2) {t1 t2}
    (le2 : t1 ⊆ lowerBounds t2) (mono1 : MonotoneOn r s1) (mono2 : MonotoneOn r s2)
    (map1 : s1.MapsTo r t1) (map2 : s2.MapsTo r t2) :
    MonotoneOn r (s1 ∪ s2) := by
  intro x xh y yh h
  rw [Set.mem_union] at xh
  rw [Set.mem_union] at yh
  rcases xh with (xh | xh) <;> rcases yh with (yh| yh)
  · exact mono1 xh yh h
  · exact le2 (map1 xh) (map2 yh)
  · rw [le_antisymm h (le1 yh xh)]
  exact mono2 xh yh h

def PartialRounder.union {s1 s2 : Set X} (h : s1 ⊆ lowerBounds s2) {t1 t2}
    (h' : t1 ⊆ lowerBounds t2) (a1 : PartialRounder i r s1 t1)
    (a2 : PartialRounder i r s2 t2) : PartialRounder i r (s1 ∪ s2) (t1 ∪ t2) where
  r_mono := .union_lowerBound h h' a1.r_mono a2.r_mono a1.r_map a2.r_map
  i_mono := .union_lowerBound h' h a1.i_mono a2.i_mono a1.i_map a2.i_map
  left_inverse x := by
    rintro (xh | xh)
    · exact a1.left_inverse xh
    · exact a2.left_inverse xh
  r_map := a1.r_map.union_union a2.r_map
  i_map := a1.i_map.union_union a2.i_map

def PartialRounder.iUnion {ι : Type*} [Preorder ι] {s : ι → Set X} {t : ι → Set F}
    (s_mono : ∀ i j, i < j → s i ⊆ lowerBounds (s j))
    (t_mono : ∀ i j, i < j → t i ⊆ lowerBounds (t j))
    (ha : ∀ j : ι, PartialRounder i r (s j) (t j)) :
    PartialRounder i r (⋃ j, s j) (⋃ j, t j) where
  r_mono := sorry
  i_mono := sorry
  left_inverse := sorry
  r_map := sorry
  i_map := sorry


end

/-!
# Why no Add instance?

Since ValidRounder is a predicate, we can't get Add, SMul, etc without bundling
`r` and `x`.

I currently am uncertain how useful bundling will actually be for floating point
operations, so I'm leaving those out for now.

It should be clear that rounders have a ring action from X when X is a strictly ordered
Semifield, but they do not form a module.
-/

section

variable {X : Type*} {F : Type*}
variable {i : F → X}
variable [LinearOrder X] [Semifield X] [Preorder F] [IsStrictOrderedRing X]

def ValidRounder.mul (approx : ValidRounder i r) {s : X}
    (spos : 0 < s) : ValidRounder (fun f ↦ i f * s) (fun x ↦ r (x / s)) where
  r_mono := approx.r_mono.comp (monotone_div_right_of_nonneg (a := s) spos.le)
  i_mono := approx.i_mono.mul_const spos.le
  left_inverse f := by
    dsimp
    rw [mul_div_cancel_right₀ (i f) spos.ne.symm]
    exact approx.left_inverse f

def ValidRounder.div (approx : ValidRounder i r) {s : X}
    (spos : 0 < s) : ValidRounder (fun f ↦ i f / s) (fun x ↦ r (x * s)) where
  r_mono := approx.r_mono.comp (monotone_mul_right_of_nonneg (a := s) spos.le)
  i_mono := approx.i_mono.div_const spos.le
  left_inverse f := by
    dsimp
    rw [div_mul_cancel₀ (i f) spos.ne.symm]
    exact approx.left_inverse f

end

section

variable {X : Type*} {F : Type*} {r : X → F} {i : F → X}
variable [Preorder X] [Preorder F] [AddGroup X] [AddRightMono X]

def ValidRounder.add (approx : ValidRounder i r) (c : X) :
    ValidRounder (fun f ↦ i f + c) (fun x ↦ r (x - c)) where
  r_mono := approx.r_mono.comp (fun _ _↦ (sub_le_sub_iff_right c).mpr)
  i_mono := approx.i_mono.add_const c
  left_inverse f := by simp [approx.left_inverse f]

def ValidRounder.sub (approx : ValidRounder i r) (c : X) :
    ValidRounder (fun f ↦ i f - c) (fun x ↦ r (x + c)) where
  r_mono := approx.r_mono.comp add_left_mono
  i_mono := by
    simp_rw [sub_eq_add_neg]
    exact approx.i_mono.add_const (-c)
  left_inverse f := by simp [approx.left_inverse f]

end

section

variable {X : Type*} {r : X → ℤ} {i : ℤ → X}
variable [LinearOrder X] [Ring X] [FloorRing X] [IsStrictOrderedRing X]

/- Should these be added to mathlib? -/
def gci_floor_coe : GaloisCoinsertion ((↑) : ℤ → X) Int.floor :=
  Int.gc_coe_floor.toGaloisCoinsertion (fun x ↦ (Int.floor_intCast x).le)

def gi_coe_ceil : GaloisInsertion Int.ceil ((↑) : ℤ → X) :=
  Int.gc_ceil_coe.toGaloisInsertion (fun x ↦ (Int.ceil_intCast x).ge)

def ValidRounder.ofFloor : ValidRounder ((↑) : ℤ → X) Int.floor :=
  .ofGaloisCoinsertion gci_floor_coe

def ValidRounder.ofCeil : ValidRounder ((↑) : ℤ → X) Int.ceil :=
  .ofGaloisInsertion gi_coe_ceil

def IsRoundDown.ofFloor : IsRoundDown ((↑) : ℤ → X) Int.floor :=
  .ofGaloisConnection Int.gc_coe_floor

def IsRoundUp.ofCeil : IsRoundUp ((↑) : ℤ → X) Int.ceil :=
  .ofGaloisConnection Int.gc_ceil_coe

-- Why isn't grind automatically accessing the member elements of approx?

-- TODO List:
-- [X] Ring operations on rounders (addition, multiplication)
-- [ ] Figure out why grind isn't unpacking approx elements automatically.
-- [X] FloorRings have round_down = floor and round_up = ceil.
-- [X] Minimum and maximum element lemmas
-- [ ] Gluing operations: binary and Σ based.
-- [ ] Adding new bottom and top elements (not a priority, may be unnecessary)
-- [ ] Bound with an interval

end

section

/-
Let 𝐹 have a cover {𝐹𝑛 }𝑛∈𝐼 such that 𝐹𝑖 ≤ 𝐹𝑗 when 𝑖 < 𝑗. We’ll have retractions 𝑟𝑛 : 𝑋 → 𝐹𝑛 , and
a monotone selection function 𝑠 : 𝑋 → 𝐼. Assuming the inclusions are compatible and lift to 𝑖 :
𝐹 → 𝑋 and 𝑓 ∈ 𝐹𝑠(𝑖(𝑓)) for all 𝑓 ∈ 𝐹 , then 𝑟(𝑥) ≔ 𝑟𝑠(𝑥) (𝑥) is a retraction.
For Lean, we will be dealing with 𝐹𝑛 which have monotone inclusions into 𝐹 instead, which slightly
𝑔𝑛
complicates the proof. Luckily (𝑓 : 𝐹 ) → 𝐹𝑠(𝑖(𝑓)) → 𝐹 for provides an explicit surjectivity
requirement, cutting down on the assumptions still.
-/

structure GlueData (ι : Type) [Preorder ι] (X : Type) [Preorder X] (F : Type)
    [Preorder F] (i : F → X) : Type where
  Fj : ι → Set F
  separation (i j : ι) (h : i < j) (x y : F) (h : x ∈ Fj i) (h' : y ∈ Fj j) : x ≤ y
  s : X → ι
  s_spec : ∀f, f ∈ Fj (s (i f))
  s_mono : Monotone s
  rj : (j : ι) → (X → Fj j)
  approx_i : ∀j, ValidRounder ((Fj j).restrict i) (rj j)

structure GlueData' (ι : Type) [Preorder ι] (X : Type) [Preorder X] (F : Type)
    [Preorder F] (i : F → X) : Type 1 where
  Fj : ι → Type
  Fj_preorder : ∀{j}, Preorder (Fj j)
  gj : {j : ι} → Fj j  → F
  gj_strictMono : ∀j, StrictMono (gj (j := j))
  separation (i j : ι) (h : i < j) (x : Fj i) (y : Fj j) : gj x ≤ gj y
  s : X → ι
  s_spec : ∀f, ∃f' : Fj (s (i f)), gj f' = f -- could decompose the choice function
  s_mono : Monotone s
  rj : (j : ι) → (X → Fj j)
  ij : {j : ι} → (Fj j → X)
  ij_compat : ∀j f, ij (j := j) f = i (gj f)
  approx_i : ∀j, ValidRounder ij (rj j)

structure WeakGlueData (ι : Type) [Preorder ι] (X : Type) [Preorder X] (F : Type)
    [Preorder F] (i : F → X) : Type 1 where
  Fj : ι → Set F
  separation (i j : ι) (h : i < j) (x y : F) (h : x ∈ Fj i) (h' : y ∈ Fj j) : x ≤ y
  s : X → ι
  s_spec : ∀f, ∃f' ∈ Fj (s (i f)), i f = i f' -- could decompose the choice function
  s_mono : Monotone s
  rj : (j : ι) → (X → Fj j)
  approx_i : ∀j, ValidRounder ((Fj j).restrict i) (rj j)

end

section

variable {X : Type*} [Field X] [LinearOrder X] [FloorRing X] [IsStrictOrderedRing X]

def validRounder_round_near : ValidRounder ((↑) : ℤ → X) round_near where
  r_mono := round_near_monotone
  i_mono := Int.cast_mono
  left_inverse := round_near_leftInverse

def validRounder_fixedPoint (prec : ℕ) := validRounder_round_near.div (
  show 0 < (2 : X)^(prec) by norm_num
)

end
