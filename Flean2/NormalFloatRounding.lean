import Flean2.Basic
import Flean2.NormalFloat
import Flean2.RoundNearest

/-! ## Normalize edge case -/

/-- Normalize mantissa when it equals `2^(prec+1)` by shifting to `2^prec`
with incremented exponent. -/
def normalize_edge (prec : ℕ) : ℤ × ℤ → ℤ × ℤ := fun ⟨m, e⟩ ↦
  if m = 2^(prec+1) then ⟨2^prec, e + 1⟩ else ⟨m, e⟩

theorem normalize_edge_cast_comm [Field k] [NeZero (2 : k)] (prec : ℕ)
    (f : ℤ × ℤ) : (interp_pair k (normalize_edge prec f)) = interp_pair k f := by
  grind [normalize_edge]

theorem normalize_edge_narrows_prec_upper [Field k] [CharZero k] (prec : ℕ)
    {f : ℤ × ℤ} (h : f.1 ≤ 2 ^ (prec + 1)) : (normalize_edge prec f).1 < 2^(prec+1) := by
  unfold normalize_edge
  grind [pow_right_inj₀]

theorem normalize_edge_narrows_prec_lower [Field k] [CharZero k] (prec : ℕ)
    {f : ℤ × ℤ} (h : 2 ^ prec ≤ f.1) : 2^prec ≤ (normalize_edge prec f).1 := by
  unfold normalize_edge
  grind only

/-! ## Generic rounder scaled by 2^e -/

section

variable {X : Type*} [Field X] [LinearOrder X] [IsStrictOrderedRing X]

/-- Scale any integer rounder `r` by `2^e`: rounds `x` to an integer multiple of `2^e`. -/
def rounder_e (r : X → ℤ) (e : ℤ) (x : X) : ℤ := r (x / 2^e)

/-- Any `ValidRounder Int.cast r` induces a `ValidRounder (interp_e e) (rounder_e r e)`. -/
def validRounder_rounder_e (e : ℤ) (approx : ValidRounder ((↑) : ℤ → X) r) :
    ValidRounder (interp_e e (X := X)) (rounder_e r e) :=
  approx.mul (by positivity)

variable {r : X → ℤ} [approx : ValidRounder ((↑) : ℤ → X) r]

def mantissaPartialRounder (e : ℤ) (prec : ℕ) [NeZero (2 : X)] :
    PartialRounder (interp_e e) (rounder_e r e)
    (Set.Icc ((2 : X)^(e + prec)) (2^(e + prec + 1))) := by
  rw [←interp_e_2pow, add_assoc, ←Int.natCast_add_one, ←interp_e_2pow]
  have h := validRounder_rounder_e (r := r) e (X := X) approx
  exact h.toPartialRounderOfMapTo fun _ ⟨lo, hi⟩ ↦
    ⟨h.i_mono (h.f_le_r_of_f_le_x lo), h.i_mono (h.r_le_f_of_x_le_f hi)⟩

theorem rounder_e_image (prec : ℕ) [NeZero (2 : X)] :
    (rounder_e r e) '' (Set.Icc ((2 : X)^(prec + e)) (2^(prec + e + 1))) =
    Set.Icc (2^prec) (2^(prec + 1)) := by
  suffices rounder_e r (X := X) e ''
      Set.Icc (interp_e e (2 ^ prec)) (interp_e e (2 ^ (prec + 1))) =
      Set.Icc (2 ^ prec) (2 ^ (prec + 1)) by grind
  exact (validRounder_rounder_e e approx).Icc (pow_le_pow_right₀ (by norm_num) (by linarith))

@[simp]
theorem rounder_e_zpow_eq (e : ℤ) (p : ℕ) [NeZero (2 : X)] :
    rounder_e r e ((2 : X) ^ (e + p)) = 2^p :=
  (interp_e_2pow (X := X) e p).symm ▸ (validRounder_rounder_e e approx).left_inverse _

end

/-! ## Mantissa bounds from logarithm -/

section

variable {X : Type*} [Field X] [LinearOrder X] [FloorRing X] [IsStrictOrderedRing X]

/-- For positive `x`, the scaled value `x / 2^(Int.log 2 x - prec)`
lies in `[2^prec, 2^(prec+1))`. -/
theorem scaled_mantissa_bounds (prec : ℕ) {x : X} (h : 0 < x) :
    2^prec ≤ (x / 2^(Int.log 2 x - prec)) ∧
    (x / 2^(Int.log 2 x - prec)) < 2^(prec+1) := by
  constructor
  · rw [le_div_iff₀ (by positivity), ←zpow_natCast (2 : X) prec, ←zpow_add₀ two_ne_zero]
    convert Int.zpow_log_le_self (b := 2) (by norm_num) h using 2
    ring
  · rw [div_lt_iff₀ (by positivity), ←zpow_natCast (2 : X) (prec + 1), ←zpow_add₀ two_ne_zero]
    convert Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x using 2
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-! ## Full rounding to (mantissa, exponent) pairs -/

variable {r : X → ℤ} [approx : ValidRounder ((↑) : ℤ → X) r]

/-- Round a positive real to a normalized (mantissa, exponent) pair using rounder `r`. -/
def round_all (r : X → ℤ) (prec : ℕ) := fun (x : X) ↦
  let e := Int.log 2 x - prec
  -- 2^(e + prec) <= x < 2^(e + prec + 1) for x ≠ 0
  -- So 2^prec <= r (x / 2^e) <= 2^(prec + 1)
  -- Normalization trims off the edge to [2^prec, 2^(prec + 1))
  normalize_edge prec ⟨rounder_e r e x, e⟩

theorem round_all_mantissa [NeZero (2 : X)] (prec : ℕ) {x : X} (h : 0 < x) :
    2^prec <= (round_all r prec x).1 ∧ (round_all r prec x).1 < 2^(prec + 1) := by
  constructor
  · apply normalize_edge_narrows_prec_lower (k := X)
    apply approx.f_le_r_of_f_le_x
    exact_mod_cast (scaled_mantissa_bounds prec h).1
  apply normalize_edge_narrows_prec_upper (k := X)
  apply approx.r_le_f_of_x_le_f
  exact_mod_cast le_of_lt (scaled_mantissa_bounds prec h).2

theorem round_all_top_eq (p : ℕ) (e : ℤ)
    : interp_pair X (round_all r p ((2 : X) ^ (e + ↑p + 1))) =
      interp_pair X (2^p, e + 1) := by
  rw [round_all, normalize_edge_cast_comm]
  apply congr_arg
  set x := (2 : X)^(e + p + 1) with x_def
  have : Int.log 2 x - p = e + 1 := by
    rw [x_def, show (2 : X) = ((2 : ℕ) : X) by norm_num,
      Int.log_zpow (b := 2) (by norm_num)]
    ring
  rw [this, x_def, add_assoc, add_comm (p : ℤ) 1, ← add_assoc]
  simp

theorem round_all_at_places (prec : ℕ) (e : ℤ) (x : X)
    (h : 2 ^ (e + prec) <= x ∧ x ≤ 2 ^ (e + prec + 1)) :
    interp_pair X (round_all r prec x) = interp_e e (rounder_e r e x) := by
  by_cases x_eq : x = 2^(e + prec + 1)
  · rw [x_eq, add_assoc]
    rw_mod_cast [rounder_e_zpow_eq (r := r) (X := X) e (prec + 1)]
    rw [Nat.cast_add, Nat.cast_one, ←add_assoc, round_all_top_eq]
    grind
  have xpos : 0 < x := lt_of_lt_of_le (by positivity) h.1
  have : Int.log 2 x = e + prec := by
    rw [Int.log_eq_iff (by norm_num) xpos]
    exact ⟨h.1, lt_of_le_of_ne h.2 x_eq⟩
  rw [round_all, normalize_edge_cast_comm, this, add_sub_cancel_right]

/-- Round a positive real to a NormalNumber using rounder `r`. -/
def round_normal (r : X → ℤ) [ValidRounder ((↑) : ℤ → X) r] (p : ℕ) (x : X) : NormalNumber p :=
  if h : 0 < x then
    match f_eq : round_all r p x with
    | ⟨m, e⟩ => .mk m e (by
      have := round_all_mantissa (r := r) (X := X) p h
      rwa [f_eq] at this
    )
  else
    .mk (2^p) (-p : ℤ) (by simp [pow_succ]) -- I chose 1 as junk

theorem round_normal_eq (p : ℕ) {x : X} (h : 0 < x) :
    (round_normal r p x).interp X = interp_pair X (round_all r p x) := by
  -- I love you grind
  grind [NormalNumber.interp, interp_e, round_normal]

theorem round_normal_interp (p : ℕ) :
    Function.LeftInverse (round_normal r p) (NormalNumber.interp X) := by
  intro f
  apply NormalNumber.interp_injective (X := X)
  rw [round_normal_eq _ (f.interp_pos X),
    round_all_at_places p f.e _ (by grind [NormalNumber.interp_bound]),
    f.interp_e_proj, (validRounder_rounder_e (X := X) f.e approx).left_inverse f.m]

theorem interp_round_all_image (p : ℕ) {x : X} {i : ℤ}
    (h : x ∈ Set.Icc (2 ^ i) (2 ^ (i + 1))) :
    (round_normal r p x).interp X ∈ Set.Icc (2 ^ i) (2 ^ (i + 1)) := by
  have xpos : 0 < x := lt_of_lt_of_le (by positivity) h.1
  rw [round_normal_eq _ xpos, round_all_at_places p (i - p)]
  · have hm : rounder_e r (i - p) x ∈ Set.Icc (2 ^ p) (2 ^ (p + 1)) := by
      rw [<-rounder_e_image (r := r) (e := i - p) p (X := X)]
      exact ⟨x, by simpa⟩
    convert interp_e_Icc (X := X) (i - p) hm <;> simp
  simp only [sub_add_cancel]
  exact h

theorem round_normal_monoOn (p : ℕ) :
    MonotoneOn (round_normal r p) (Set.Ioi (0 : X)) := by
  rw [Ioi_zero_eq_iUnion_Icc_zpow (b := (2 : X)) (by norm_num)]
  apply MonotoneOn.iUnion_lowerBound
    (t := fun e ↦ round_normal r p '' Set.Icc ((2 : X)^e) (2^(e+1)))
  case s_mono =>
    apply zpow_lowerBounds
  · intro i j h f ⟨x, xh⟩ f' ⟨y, yh⟩
    rw [NormalNumber.le_def X, <-xh.2, <-yh.2]
    exact zpow_lowerBounds h
      (interp_round_all_image _ xh.1)
      (interp_round_all_image _ yh.1)
  · intro i x xh y yh h
    rw [NormalNumber.le_def X]
    have xpos : 0 < x := lt_of_lt_of_le (by positivity) xh.1
    have ypos : 0 < y := lt_of_lt_of_le (by positivity) yh.1
    rw [round_normal_eq _ xpos, round_all_at_places p (i - p) x (by simpa)]
    rw [round_normal_eq _ ypos, round_all_at_places p (i - p) y (by simpa)]
    have h_approx := validRounder_rounder_e (r := r) (X := X) (i - p) approx
    exact h_approx.i_mono (h_approx.r_mono h)
  exact fun i ↦ Set.mapsTo_image (round_normal r p) (Set.Icc (2 ^ i) (2 ^ (i + 1)))

def partialRounder_round_normal (p : ℕ) :
    PartialRounder (NormalNumber.interp X) (round_normal r p) (Set.Ioi 0) where
  r_mono := round_normal_monoOn p
  i_mono := (NormalNumber.interp_strictMono X).monotone.monotoneOn _
  left_inverse := (round_normal_interp p).leftInvOn _
  i_r_map _ _ := NormalNumber.interp_pos _ _

end

/-! ## Concrete instances for specific rounders -/

section RoundNear

variable {X : Type*} [Field X] [LinearOrder X] [FloorRing X] [IsStrictOrderedRing X]

instance validRounder_round_near : ValidRounder ((↑) : ℤ → X) round_near where
  r_mono := round_near_monotone
  i_mono := Int.cast_mono
  left_inverse := round_near_leftInverse

/-- Round to nearest, scaling by 2^e. -/
abbrev round_near_e (e : ℤ) : X → ℤ := rounder_e round_near e

/-- Round a positive real to a NormalNumber using round-to-nearest. -/
abbrev round_near_normal (p : ℕ) : X → NormalNumber p := round_normal round_near p

/-- Round a positive real to a (mantissa, exponent) pair using round-to-nearest. -/
abbrev round_near_all (p : ℕ) : X → ℤ × ℤ := round_all round_near p

end RoundNear
