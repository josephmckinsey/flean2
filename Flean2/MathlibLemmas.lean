import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Int.Log
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Field.Power

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


theorem Int.log_eq_iff {R : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} (hb : 1 < b) {x : ℤ}
    {r : R} (hr : 0 < r) : Int.log b r = x ↔ b^x <= r ∧ r < b^(x+1) :=
  Iff.intro
    (fun h ↦ h.symm ▸ ⟨zpow_log_le_self hb hr, lt_zpow_succ_log_self hb r⟩)
    (fun ⟨h1, h2⟩ ↦ le_antisymm
      (Order.le_of_lt_add_one <| (lt_zpow_iff_log_lt hb hr).mp h2)
      ((zpow_le_iff_le_log hb hr).mp h1))

variable {X : Type*} [Field X] [LinearOrder X] [IsStrictOrderedRing X]

theorem Ioi_zero_eq_iUnion_Ico_zpow [Archimedean X] {b : X} (hy : 1 < b) :
    Set.Ioi 0 = ⋃ n : ℤ, Set.Ico ((b : X) ^ n) (b ^ (n + 1)) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioi, Set.mem_Ico]
  exact ⟨fun xh ↦ exists_mem_Ico_zpow xh (by norm_cast),
    fun ⟨n, xh'⟩ ↦ lt_of_lt_of_le (by positivity) xh'.1⟩

theorem Ioi_zero_eq_iUnion_Icc_zpow [Archimedean X] {b : X} (hy : 1 < b) :
    Set.Ioi 0 = ⋃ n : ℤ, Set.Icc ((b : X) ^ n) (b ^ (n + 1)) := by
  apply subset_antisymm (Ioi_zero_eq_iUnion_Ico_zpow hy ▸
      Set.iUnion_mono (fun i ↦ Set.Ico_subset_Icc_self))
  intro n
  rw [Set.mem_iUnion]
  exact fun ⟨i, h⟩ ↦ lt_of_lt_of_le (by positivity) h.1

theorem zpow_lowerBounds {i j : ℤ} (h : i < j) : Set.Icc ((2 : X) ^ i) (2 ^ (i + 1)) ⊆
    lowerBounds (Set.Icc (2 ^ j) (2 ^ (j + 1))) :=
  fun _ xh _ yh ↦ xh.2.trans ((zpow_le_zpow_right₀ (by norm_num) h).trans yh.1)
