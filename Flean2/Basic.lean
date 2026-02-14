import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Rify
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Int.Log
import Flean2.RoundNearest
import Mathlib.Data.Int.SuccPred
import Mathlib.Order.Interval.Set.SurjOn

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

structure PartialRounder (i : F → X) (r : X → F) (s : Set X) : Prop where
  r_mono : MonotoneOn r s
  i_mono : MonotoneOn i (r '' s)
  left_inverse : Set.LeftInvOn r i (r '' s)
  i_r_map : s.MapsTo (i ∘ r) s

variable {i : F → X} {r : X → F} {s : Set X}

def PartialRounder.i_map (approx : PartialRounder i r s) : (r '' s).MapsTo i s :=
  Set.mapsTo_image_iff.mpr approx.i_r_map

def PartialRounder.r_map (_ : PartialRounder i r s) : s.MapsTo r (r '' s) :=
  Set.mapsTo_image r s

def PartialRounder.ofMapTo {i : F → X} {r : X → F} {s : Set X} {t : Set F}
    (r_mono : MonotoneOn r s) (i_mono : MonotoneOn i t)
    (left_inverse : Set.LeftInvOn r i t) (i_map : t.MapsTo i s) (r_map : s.MapsTo r t)
    : PartialRounder i r s where
  r_mono := r_mono
  i_mono := r_s_eq_t ▸ i_mono
  left_inverse := r_s_eq_t ▸ left_inverse
  i_r_map := Set.MapsTo.comp i_map r_map
  where
    r_s_eq_t := subset_antisymm (Set.image_subset_iff.mpr r_map)
      fun f fh ↦ ⟨i f, i_map fh, left_inverse fh⟩

def PartialRounder.restrict (approx : PartialRounder i r s) :
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

def ValidRounder.toPartialRounderOfMapTo (approx : ValidRounder i r)
    (h : s.MapsTo (i ∘ r) s) : PartialRounder i r s where
  r_mono := Monotone.monotoneOn approx.r_mono s
  i_mono := Monotone.monotoneOn approx.i_mono (r '' s)
  left_inverse x _ := approx.left_inverse x
  i_r_map := h

def ValidRounder.toPartialRounderOfMapTo' {t : Set F} (approx : ValidRounder i r)
    (r_map : s.MapsTo r t) (i_map : t.MapsTo i s) : PartialRounder i r s :=
  approx.toPartialRounderOfMapTo (i_map.comp r_map)

def ValidRounder.toPartialRounder (approx : ValidRounder i r) : PartialRounder i r .univ :=
  approx.toPartialRounderOfMapTo (Set.mapsTo_univ _ _)

def PartialRounder.toValidRounder (approx : PartialRounder i r .univ)
    (h : Function.Surjective r) : ValidRounder i r where
  r_mono := monotoneOn_univ.mp approx.r_mono
  i_mono := monotoneOn_univ.mp ((Set.image_univ_of_surjective h) ▸ approx.i_mono)
  left_inverse x := approx.left_inverse (Set.image_univ_of_surjective h ▸ Set.mem_univ x)

def PartialRounder.mono {s' : Set X} (approx : PartialRounder i r s)
    (h : s' ⊆ s) (h' : s'.MapsTo (i ∘ r) s') : PartialRounder i r s' where
  r_mono := approx.r_mono.mono h
  i_mono := approx.i_mono.mono (Set.image_mono h)
  left_inverse := approx.left_inverse.mono (Set.image_mono h)
  i_r_map := h'

end

section

variable {X : Type*} {F : Type*} [PartialOrder X]

variable {i : F → X} {r : X → F}

def MonotoneOn.union_lowerBound [Preorder F] {s1 s2 : Set X} (le1 : s1 ⊆ lowerBounds s2) {t1 t2}
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

def MonotoneOn.iUnion_lowerBound {ι : Type*} [LinearOrder ι]
    [Preorder F] {s : ι → Set X} (s_mono : ∀ i j, i < j → s i ⊆ lowerBounds (s j))
    {t : ι → Set F} (t_mono : ∀ i j, i < j → t i ⊆ lowerBounds (t j))
    (r_mono_i : ∀ i, MonotoneOn r (s i)) (r_map : ∀ i, (s i).MapsTo r (t i)) :
    MonotoneOn r (⋃ i, s i) := by
  intro x xh y yh h
  rw [Set.mem_iUnion] at xh yh
  rcases xh with ⟨i, xh⟩
  rcases yh with ⟨j, yh⟩
  rcases lt_trichotomy i j with h' | h' | h'
  · exact t_mono i j h' (r_map i xh) (r_map j yh)
  · exact r_mono_i i xh (h' ▸ yh) h
  rw [le_antisymm h (s_mono j i h' yh xh)]


variable [PartialOrder F] -- needed for i

def PartialRounder.union {s1 s2 : Set X} (h : s1 ⊆ lowerBounds s2)
    (h' : (r '' s1) ⊆ lowerBounds (r '' s2)) (a1 : PartialRounder i r s1)
    (a2 : PartialRounder i r s2) : PartialRounder i r (s1 ∪ s2) where
  r_mono := .union_lowerBound h h' a1.r_mono a2.r_mono a1.r_map a2.r_map
  i_mono := Set.image_union r s1 s2 ▸
      .union_lowerBound h' h a1.i_mono a2.i_mono a1.i_map a2.i_map
  left_inverse x := by
    rw [Set.image_union]
    rintro (xh | xh)
    · exact a1.left_inverse xh
    · exact a2.left_inverse xh
  i_r_map := a1.i_r_map.union_union a2.i_r_map

def PartialRounder.iUnion {ι : Type*} [Preorder ι] {s : ι → Set X} {t : ι → Set F}
    (s_mono : ∀ i j, i < j → s i ⊆ lowerBounds (s j))
    (ha : ∀ j : ι, PartialRounder i r (s j)) :
    PartialRounder i r (⋃ j, s j) where
  r_mono := sorry
  i_mono := sorry
  left_inverse := sorry
  i_r_map := sorry

end

section

variable {X : Type*} {F : Type*} [LinearOrder X] [PartialOrder F]
variable {i : F → X} {r : X → F}

theorem ValidRounder.mapsTo_Icc {a b : F} (approx : ValidRounder i r) :
    Set.MapsTo r (Set.Icc (i a) (i b)) (Set.Icc a b) := by
  nth_rw 2 [<-approx.left_inverse a, <-approx.left_inverse b]
  exact approx.r_mono.mapsTo_Icc

theorem ValidRounder.Icc {a b : F} (approx : ValidRounder i r) (h : a ≤ b) :
    r '' (Set.Icc (i a) (i b)) = Set.Icc a b := by
  rw [@Set.image_eq_iff_surjOn_mapsTo]
  constructor
  · nth_rw 2 [<-approx.left_inverse a, <-approx.left_inverse b]
    exact surjOn_Icc_of_monotone_surjective approx.r_mono approx.left_inverse.surjective
      (approx.i_mono h)
  exact approx.mapsTo_Icc

theorem PartialRounder.r_le_f_of_x_le_f (approx : PartialRounder i r s) {x : X} {f : F}
    (hx : x ∈ s) (hf : f ∈ r '' s) (h : x ≤ i f) : r x ≤ f :=
  approx.left_inverse hf ▸ approx.r_mono hx (approx.i_map hf) h

theorem PartialRounder.mapsTo_Icc {a b : F} (approx : PartialRounder i r s)
    (ha : a ∈ r '' s) (hb : b ∈ r '' s) (hs : Set.Icc (i a) (i b) ⊆ s) :
    Set.MapsTo r (Set.Icc (i a) (i b)) (Set.Icc a b) := by
  nth_rw 2 [<-approx.left_inverse ha, <-approx.left_inverse hb]
  exact (approx.r_mono.mono hs).mapsTo_Icc

theorem PartialRounder.Icc_ofSurjOn {a b : F} (approx : PartialRounder i r s)
    (h : Set.SurjOn r s .univ) (hs : Set.Icc (i a) (i b) ⊆ s)
    : r '' (Set.Icc (i a) (i b)) = (Set.Icc a b) := by
  let target : ∀{a}, a ∈ r '' s := fun {f} ↦ h (Set.mem_univ f)
  rw [@Set.image_eq_iff_surjOn_mapsTo]
  exact And.intro
    (fun f fh ↦
      ⟨i f, ⟨approx.i_mono target target fh.1, approx.i_mono target target fh.2⟩,
        approx.left_inverse target⟩)
    (approx.mapsTo_Icc target target hs)

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

end

section

variable {X : Type*} [Field X] [LinearOrder X] [FloorRing X] [IsStrictOrderedRing X]

def validRounder_round_near : ValidRounder ((↑) : ℤ → X) round_near where
  r_mono := round_near_monotone
  i_mono := Int.cast_mono
  left_inverse := round_near_leftInverse


/-
TODO: m 2^e with 2^prec <= m < 2^(prec+1)
TODO: Make a round_fixed_point
-/

def round_near_e (e : ℤ) (x : X) : ℤ := round_near (x / 2^e)
def interp_e (e : ℤ) (f : ℤ) : X := ↑f * 2^e

def validRounder_round_near_e (e : ℤ) :
    ValidRounder (interp_e e (X := X)) (round_near_e e) :=
  validRounder_round_near.mul (by positivity)

def mantissaPartialRounder_round_near (e : ℤ) (prec : ℕ) :
    PartialRounder (interp_e e) (round_near_e e)
    (Set.Icc ((2 : X)^(prec + e)) (2^(prec + e + 1))) := by
  rw [show (2 : X)^(prec + e) = (2^prec : ℤ) * (2 : X)^e by
    rw [zpow_add₀ (by norm_num)]
    simp,
    show (2 : X)^(prec + e + 1) = (2^(prec + 1): ℤ) * (2 : X)^e by
    rw [add_assoc, add_comm e 1, <-add_assoc, zpow_add₀ (by norm_num)]
    norm_cast
  ]
  have approx := validRounder_round_near_e e (X := X)
  exact ValidRounder.toPartialRounderOfMapTo approx fun x xh ↦
    ⟨approx.i_mono (approx.f_le_r_of_f_le_x xh.1),
    approx.i_mono (approx.r_le_f_of_x_le_f xh.2)⟩

-- TODO: Generalize
theorem round_near_image (a b : ℤ) (h : a ≤ b) :
    round_near '' (Set.Icc (a : X) (b : X)) = Set.Icc a b :=
  (validRounder_round_near (X := X)).Icc h

theorem round_near_e_image (prec : ℕ) :
    (round_near_e e) '' (Set.Icc ((2 : X)^(prec + e)) (2^(prec + e + 1))) =
    Set.Icc (2^prec) (2^(prec + 1)) := by
  suffices round_near_e (X := X) e ''
      Set.Icc (interp_e e (2 ^ prec)) (interp_e e (2 ^ (prec + 1))) =
      Set.Icc (2 ^ prec) (2 ^ (prec + 1)) by
    rw [interp_e, interp_e] at this
    convert this
    · simp [Int.cast_pow, zpow_add₀]
    rw [zpow_add_one₀ (by norm_num), zpow_add₀ (by norm_num), pow_succ]
    field_simp
    norm_cast
  exact (validRounder_round_near_e e).Icc (pow_le_pow_right₀ (by norm_num) (by linarith))

abbrev interp_pair (X : Type*) [Field X] (f : ℤ × ℤ) : X := f.1 * (2 : X)^f.2

def normalize_edge (prec : ℕ) : ℤ × ℤ → ℤ × ℤ := fun ⟨m, e⟩ ↦
  if m = 2^(prec+1) then ⟨2^prec, e + 1⟩ else ⟨m, e⟩

theorem normalize_edge_cast_comm [Field k] [NeZero (2 : k)] (prec : ℕ)
    (f : ℤ × ℤ) : (interp_pair k (normalize_edge prec f)) = interp_pair k f := by
  unfold normalize_edge interp_pair
  if h : f.1 = 2^(prec + 1) then
    simp only [h, reduceIte, Int.cast_pow, Int.cast_ofNat]
    rw [pow_add, zpow_add₀ two_ne_zero]
    field_simp
  else
    simp_rw [if_neg h]

theorem normalize_edge_narrows_prec_upper [Field k] [CharZero k] (prec : ℕ)
    {f : ℤ × ℤ} (h : f.1 ≤ 2 ^ (prec + 1)) : (normalize_edge prec f).1 < 2^(prec+1) := by
  unfold normalize_edge
  grind [pow_right_inj₀]

theorem normalize_edge_narrows_prec_lower [Field k] [CharZero k] (prec : ℕ)
    {f : ℤ × ℤ} (h : 2 ^ prec ≤ f.1) : 2^prec ≤ (normalize_edge prec f).1 := by
  unfold normalize_edge
  grind only

def round_near_all (prec : ℕ) := fun (x : X) ↦
  let e := Int.log 2 x - prec
  -- 2^(e + prec) <= x < 2^(e + prec + 1) for x ≠ 0
  -- So 2^prec <= round_near (x / 2^e) <= 2^(prec + 1)
  -- Normalization trims off the edge to [2^prec, 2^(prec + 1))
  normalize_edge prec ⟨round_near_e e x, e⟩

theorem round_near_e_mantissa (prec : ℕ) {x : X} (h : 0 < x) :
    2^prec ≤ (x / 2^(Int.log 2 x - prec)) ∧
    (x / 2^(Int.log 2 x - prec)) < 2^(prec+1) := by
  set y := x / 2^(Int.log 2 x - prec) with y_def
  rw [sub_eq_add_neg, div_eq_mul_inv, <-zpow_neg, neg_add_rev, neg_neg,
    zpow_add₀ (by norm_num), mul_comm, mul_assoc, mul_comm _ x, zpow_neg] at y_def
  have rhs : x * (2^(Int.log 2 x))⁻¹ < 2 := by
    rw [mul_inv_lt_iff₀ (by positivity), mul_comm,
      <-zpow_add_one₀ (by norm_num)]
    exact Int.lt_zpow_succ_log_self (by norm_num) x
  have lhs : 1 ≤ x * (2^(Int.log 2 x))⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity), mul_comm, mul_one]
    apply Int.zpow_log_le_self (by norm_num) h
  suffices 1 ≤ x * (2^(Int.log 2 x))⁻¹ ∧ x * (2^(Int.log 2 x))⁻¹ < 2 by
    simpa [pow_succ, y_def]
  exact ⟨lhs, rhs⟩


theorem round_near_all_mantissa [NeZero (2 : X)] (prec : ℕ) {x : X} (h : 0 < x) :
    2^prec <= (round_near_all prec x).1 ∧ (round_near_all prec x).1 < 2^(prec + 1) := by
  constructor
  · apply normalize_edge_narrows_prec_lower (k := X)
    apply validRounder_round_near.f_le_r_of_f_le_x
    exact_mod_cast (round_near_e_mantissa prec h).1
  apply normalize_edge_narrows_prec_upper (k := X)
  apply validRounder_round_near.r_le_f_of_x_le_f
  exact_mod_cast le_of_lt (round_near_e_mantissa prec h).2

theorem Int.log_eq_iff {R : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} (hb : 1 < b) {x : ℤ}
    {r : R} (hr : 0 < r) : Int.log b r = x ↔ b^x <= r ∧ r < b^(x+1) :=
  Iff.intro
    (fun h ↦ h.symm ▸ ⟨zpow_log_le_self hb hr, lt_zpow_succ_log_self hb r⟩)
    (fun ⟨h1, h2⟩ ↦ le_antisymm
      (Order.le_of_lt_add_one <| (lt_zpow_iff_log_lt hb hr).mp h2)
      ((zpow_le_iff_le_log hb hr).mp h1))

theorem round_near_e_zpow_eq (e : ℤ) (p : ℕ) : round_near_e e ((2 : X) ^ (e + p)) = 2^p :=
  let i_eq : (2 : X) ^ (e + p) = interp_e e (2^p) := by
    unfold interp_e
    rw [add_comm]
    simp [zpow_add₀]
  i_eq ▸ (validRounder_round_near_e e).left_inverse _


theorem round_near_all_top_eq (p : ℕ) (e : ℤ)
    : interp_pair X (round_near_all p ((2 : X) ^ (e + ↑p + 1))) =
      interp_pair X (2^p, e + 1) := by
  rw [round_near_all, normalize_edge_cast_comm]
  apply congr_arg
  set x := (2 : X)^(e + p + 1) with x_def
  have : Int.log 2 x - p = e + 1 := by
    rw [x_def, show (2 : X) = ((2 : ℕ) : X) by norm_num,
      Int.log_zpow (b := 2) (by norm_num)]
    ring
  rw [this, x_def, add_assoc, add_comm (p : ℤ) 1, <-add_assoc]
  rw_mod_cast [round_near_e_zpow_eq (e + 1) p]
  norm_cast

theorem round_near_all_at_places (prec : ℕ) (e : ℤ) (x : X)
    (h : 2 ^ (e + prec) <= x ∧ x ≤ 2 ^ (e + prec + 1)) :
    interp_pair X (round_near_all prec x) = interp_e e (round_near_e e x) := by
  by_cases x_eq : x = 2^(e + prec + 1)
  · rw [x_eq, add_assoc]
    rw_mod_cast [round_near_e_zpow_eq (X := X) e (prec + 1 )]
    rw [Nat.cast_add, Nat.cast_one, <-add_assoc, round_near_all_top_eq,
      interp_pair,interp_e, pow_succ, zpow_add_one₀ (by norm_num)]
    field_simp
    norm_cast
  have xpos : 0 < x := lt_of_lt_of_le (by positivity) h.1
  have : Int.log 2 x = e + prec := by
    rw [Int.log_eq_iff (by norm_num) xpos]
    exact ⟨h.1, lt_of_le_of_ne h.2 x_eq⟩
  rw [round_near_all, normalize_edge_cast_comm, this, add_sub_cancel_right]
  rfl

-- For each i f ∈ X_i, there is a f' ∈ r_i '' X_i s.t. i' f' = i f.
-- We need to take each f and assign it the original f' in X_i for all X_i that its a part of.
-- They should agree on their intersections essentially.
-- ι → F → Fi (here Fi are actually types (in our case ℤ))

-- (m, e) → 2^(e+prec) <= m 2^e <= 2^(e+prec+1), and f ∈ r '' Xj, so we can choose
-- round_near (x / 2^e), which can then use normalization to show is equal. Details
-- are fuzzy, especially in the general case.

-- i r = i' r' on each X_i instead of having a selection function directly.
-- We need the partial order on F still for the i to be mono, but we could also
-- just assert i is mono since it's obvious.
-- This lets us get i r i = i, and then we can use the strict nature of i to remove it.
-- i r i f = i' r' i f = i' r' i' f' = i' f' = i f

-- Since r' i' f = f, then i r (i' f) = i' r' i' f = i' f,


-- This is a proof by cases on the boundary.


-- PartialRounder i (round_near (x / 2^e), e) should be equivalent to PartialRounder i round_near (...)
-- with a fixed e on the interval [2^prec, 2^(prec + 1)] since there is an invertible map
-- between r '' [2^prec, 2^(prec+1)] and r1 '' [2^prec, 2^(prec + 1)]
-- φ ∘ r = r1
--
end

section

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

-- I would like to prove that round_near_all' is a valid rounder on
-- union e, 2^(e + prec) <= x <= 2^(e + prec + 1) = (0, infty)
-- Our monotone selection function Int.log 2 x - prec is monotone on (0, infty)
-- First, we remove the normalization step.
-- Looking at [2^(e+prec), 2^(e+prec+1)], our rounder inherits
-- monotonicity from the individual rounders.
-- Since i maps to (0, infty), our i_r_map property is satisfied.
-- Now for r (i f), we have that i (r (i f)) = i f for each [2^(e+prec), 2^(e+prec+1)]
-- by removing the normalization. Since i is injective on NormalNumbers, we then have
-- that r (i f) = f.


-- Finally, we can compose with

-- Now we want to glue these together, so we want to take
-- round_near_exp e and round_near (e+1) and glue them together.
-- which should be possible as long as i is monotone everywhere and s1 <= s2

-- TODO: Do we need IsRoundUpOn and IsRoundDownOn?
-- TODO: Do we need that gluing preserves IsRoundUp and IsRoundDown?

end

-- Why isn't grind automatically accessing the member elements of approx?

-- TODO List:
-- [X] Ring operations on rounders (addition, multiplication)
-- [ ] Figure out why grind isn't unpacking approx elements automatically.
-- [X] FloorRings have round_down = floor and round_up = ceil.
-- [X] Minimum and maximum element lemmas
-- [ ] Gluing operations: binary and Σ based.
-- [ ] Adding new bottom and top elements (not a priority, may be unnecessary)
-- [ ] Bound with an interval

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
  Fj : ι → Set F -- Fj = r '' Xj
  Xj : ι → Set X
  separation (i j : ι) (h : i < j) (x y : F) (h : x ∈ Fj i) (h' : y ∈ Fj j) : x ≤ y
  s : X → ι
  s_spec : ∀f, f ∈ Fj (s (i f))
  s_mono : Monotone s
  rj : ι → (X → F)
  approx_i : ∀j, PartialRounder i (rj j) (Xj j)

def glue_round (rj : ι → X → F) (s : X → ι) : X → F := fun x ↦ rj (s x) x


theorem t [Preorder X] [Preorder F] {s : X → ι} (Xj : ι → Set X)
    {rj : ι → X → F} (approx_i : ∀ j, PartialRounder i (rj j) (Xj j))
    {f : F} (fh : f ∈ rj (s (i f)) '' Xj (s (i f)))
    :  i ((glue_round rj s) (i f)) = i f := by
  unfold glue_round
  have := (approx_i (s (i f))).left_inverse fh
  sorry
    /-
    MonotoneOn (glue_round rj s) (s⁻¹' {j} ∩ Xj j) := by
  apply MonotoneOn.congr ((monotone_i ))
    where
  r_mono := by
    apply MonotoneOn.congr ((approx_i j).r_mono.mono Set.inter_subset_right)
    intro x xh
    unfold glue_round
    rw [show s x = j by grind]
  i_mono := by
    have : (glue_round rj s '' (s ⁻¹' {j} ∩ Xj j)) ⊆ (rj j '' Xj j) := by grind [glue_round]
    apply MonotoneOn.congr ((approx_i j).i_mono.mono this)
    unfold glue_round
    intro f fh
    simp only
  left_inverse f fh := by -- not true
    have t := (approx_i j).left_inverse
    have : f ∈ rj j '' Xj j := by grind [glue_round]
    replace t := t this
    have : i f ∈ Xj j := by apply (approx_i j).i_map this
    have t' := (approx_i j).i_r_map this
    --simp [] at t'
    unfold glue_round
    -- For each f ∈ rj j '' Xj j, f ∈ rj (s (i f)) '' Xj (s (i f))
    have : s (i f) = j := by
      unfold glue_round at fh
      simp at fh
    rw [this, t]
  i_r_map := sorry




structure GlueData'' (ι : Type) [Preorder ι] (X : Type) [Preorder X] (F : Type)
    [Preorder F] (i : F → X) : Type where
  Fj : ι → Set F -- Fj = r '' Xj
  Xj : ι → Set X
  separation (i j : ι) (h : i < j) (x y : F) (h : x ∈ Fj i) (h' : y ∈ Fj j) : x ≤ y
  s : X → ι
  s_spec : ∀f, f ∈ Fj (s (i f))
  s_mono : Monotone s
  rj : ι → (X → F)
  approx_i : ∀j, PartialRounder i (rj j) (Xj j)


-/

structure GlueData' (ι : Type) [Preorder ι] (X : Type) [Preorder X] (F : Type)
    [Preorder F] (i : F → X) : Type 1 where
  r : X → F
  i : F → X
  Xj : ι → Set X
  Fj : ι → Type
  rj : (j : ι) → (X → Fj j)
  ij : (j : ι) → (Fj j → X)
  separation (i j : ι) (h : i < j) (x y : X) (h : x ∈ Xj i) (h' : x ∈ Xj j) : x ≤ y
  agreement : ∀j, ∀x ∈ Xj j, i (r x) = ij j (rj j x)
  pick_f : (j : ι) → (f : F) → (h : f ∈ r '' (Xj j)) → Fj j
  pick_f_spec : ∀j f h, ij j (pick_f j f h) = i f
  Fj_preorder : ∀{j}, Preorder (Fj j)
  approx_i : ∀j, PartialRounder (ij j) (rj j) (Xj j)

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

def round_near_normal [Field X] [LinearOrder X] [IsStrictOrderedRing X] [FloorRing X]
    (p : ℕ) (x : X) : NormalNumber p :=
  if h : 0 < x then
    match f_eq : round_near_all p x with
    | ⟨m, e⟩ => .mk m e (by
      have := round_near_all_mantissa (X := X) p h
      rwa [f_eq] at this
    )
  else
    .mk (2^p) (-p : ℤ) (by simp [pow_succ]) -- I chose 1 as junk

theorem round_near_normal_eq [Field X] [LinearOrder X] [IsStrictOrderedRing X]
    [FloorRing X] (p : ℕ) {x : X} (h : 0 < x) :
    (round_near_normal p x).interp X = interp_pair X (round_near_all p x) := by
  -- I love you grind
  grind [NormalNumber.interp, round_near_normal]

theorem round_normal_interp [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] [FloorRing X] (p : ℕ) :
    Function.LeftInverse (round_near_normal p) (NormalNumber.interp X) := by
  intro f
  apply NormalNumber.interp_injective (X := X)
  rw [round_near_normal_eq _ (f.interp_pos X),
    round_near_all_at_places p f.e _ (by grind [NormalNumber.interp_bound]),
    f.interp_e_proj, (validRounder_round_near_e (X := X) f.e).left_inverse f.m]

theorem interp_round_near_all_image [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] [FloorRing X] (p : ℕ) {x : X} {i : ℤ}
    (h : x ∈ Set.Icc (2 ^ i) (2 ^ (i + 1))) :
    (round_near_normal p x).interp X ∈ Set.Icc (2 ^ i) (2 ^ (i + 1)) := by
  have xpos : 0 < x := lt_of_lt_of_le (by positivity) h.1
  rw [round_near_normal_eq _ xpos, round_near_all_at_places p (i - p)]
  · have : round_near_e (i - p) x ∈ Set.Icc (2 ^ p) (2 ^ (p + 1)) := by
      rw [<-round_near_e_image (e := i - p) p (X := X)]
      use x
      simpa
    rw [interp_e]
    set m := round_near_e (i - p) x
    -- There's _some_ overlap here with interp_bound
    constructor
    · rw [zpow_sub₀ (by norm_num), mul_div, le_div_iff₀' (by positivity)]
      apply (mul_le_mul_iff_left₀ (by positivity)).mpr
      exact_mod_cast this.1
    rw [zpow_sub₀ (by norm_num), mul_div, div_le_iff₀' (by positivity),
      add_comm, zpow_add₀ (by positivity), <-mul_assoc, <-zpow_add₀ (by positivity)]
    apply (mul_le_mul_iff_left₀ (by positivity)).mpr
    exact_mod_cast this.2
  simp only [sub_add_cancel]
  exact h

theorem Ioi_zero_eq_iUnion_Ico_zpow [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] [Archimedean X] {b : X} (hy : 1 < b) :
    Set.Ioi 0 = ⋃ n : ℤ, Set.Ico ((b : X) ^ n) (b ^ (n + 1)) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioi, Set.mem_Ico]
  exact ⟨fun xh ↦ exists_mem_Ico_zpow xh (by norm_cast),
    fun ⟨n, xh'⟩ ↦ lt_of_lt_of_le (by positivity) xh'.1⟩

theorem Ioi_zero_eq_iUnion_Icc_zpow [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] [Archimedean X] {b : X} (hy : 1 < b) :
    Set.Ioi 0 = ⋃ n : ℤ, Set.Icc ((b : X) ^ n) (b ^ (n + 1)) := by
  apply subset_antisymm (Ioi_zero_eq_iUnion_Ico_zpow hy ▸
      Set.iUnion_mono (fun i ↦ Set.Ico_subset_Icc_self))
  intro n
  rw [Set.mem_iUnion]
  exact fun ⟨i, h⟩ ↦ lt_of_lt_of_le (by positivity) h.1

theorem zpow_lowerBounds [Field X] [LinearOrder X] [IsStrictOrderedRing X] {i j : ℤ}
    (h : i < j) : Set.Icc ((2 : X) ^ i) (2 ^ (i + 1)) ⊆
    lowerBounds (Set.Icc (2 ^ j) (2 ^ (j + 1))) :=
  fun _ xh _ yh ↦ xh.2.trans ((zpow_le_zpow_right₀ (by norm_num) h).trans yh.1)

-- TODO: clean up
theorem round_normal_monoOn [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] [FloorRing X] (p : ℕ) :
    MonotoneOn (round_near_normal p) (Set.Ioi (0 : X)) := by
  rw [Ioi_zero_eq_iUnion_Icc_zpow (b := (2 : X)) (by norm_num)]
  apply MonotoneOn.iUnion_lowerBound
    (t := fun e ↦ round_near_normal p '' Set.Icc ((2 : X)^e) (2^(e+1)))
  case s_mono =>
    apply zpow_lowerBounds
  · intro i j h
    have := zpow_lowerBounds h (X := X)
    intro f ⟨x, xh⟩ f' ⟨y, yh⟩
    rw [NormalNumber.le_def X]
    rw [<-xh.2, <-yh.2]
    apply this
    · apply interp_round_near_all_image _ xh.1
    apply interp_round_near_all_image _ yh.1
  · intro i x xh y yh h
    rw [NormalNumber.le_def X]
    have xpos : 0 < x := lt_of_lt_of_le (by positivity) xh.1
    have ypos : 0 < y := lt_of_lt_of_le (by positivity) yh.1
    rw [round_near_normal_eq _ xpos, round_near_all_at_places p (i - p) x (by simpa)]
    rw [round_near_normal_eq _ ypos, round_near_all_at_places p (i - p) y (by simpa)]
    exact (validRounder_round_near_e _).i_mono ((validRounder_round_near_e _).r_mono h)
  exact fun i ↦ Set.mapsTo_image (round_near_normal p) (Set.Icc (2 ^ i) (2 ^ (i + 1)))

def partialRounder_round_near_normal [Field X] [LinearOrder X]
    [IsStrictOrderedRing X] [FloorRing X] (p : ℕ) :
    PartialRounder (NormalNumber.interp X) (round_near_normal p) (Set.Ioi 0) where
  r_mono := round_normal_monoOn p
  i_mono := (NormalNumber.interp_strictMono X).monotone.monotoneOn _
  left_inverse := (round_normal_interp p).leftInvOn _
  i_r_map := fun _ _  ↦ NormalNumber.interp_pos _ _

-- If i (r (i f)) = i f, and r' (i' f') = f', then
--
-- i i' r' r i i' f

-- If I have a weak rounder X → F, then I replace F with i '' F.
-- Now I just need to show that my "normalized" version is isomorphic to i '' F.
-- So let φ : F → F', then i'(φ(f)) = i(f) and φ is monotone
-- with a right inverse φ⁻¹ and monotone i'.

-- Then i' (φ r) i' f' = i r i' f' = i r i' φ φ⁻¹ f' = i r i φ⁻¹ f' = i φ⁻¹ f' = i' φ φ⁻¹ f = i' f
-- So we get our weak gluing property again.


-- Alternatively, I could try and show our gluing property, where we try and show that
