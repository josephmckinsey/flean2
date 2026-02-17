import Flean2.Basic
import Flean2.NormalFloat

section

variable {X : Type*} [Field X] [LinearOrder X] [FloorRing X] [IsStrictOrderedRing X]

instance validRounder_round_near : ValidRounder ((↑) : ℤ → X) round_near where
  r_mono := round_near_monotone
  i_mono := Int.cast_mono
  left_inverse := round_near_leftInverse

def round_near_e (e : ℤ) (x : X) : ℤ := round_near (x / 2^e)

instance validRounder_round_near_e (e : ℤ) :
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
  exact ValidRounder.toPartialRounderOfMapTo fun x xh ↦
    ⟨approx.i_mono (approx.f_le_r_of_f_le_x xh.1),
    approx.i_mono (approx.r_le_f_of_x_le_f xh.2)⟩

theorem round_near_e_image (prec : ℕ) :
    (round_near_e e) '' (Set.Icc ((2 : X)^(prec + e)) (2^(prec + e + 1))) =
    Set.Icc (2^prec) (2^(prec + 1)) := by
  suffices round_near_e (X := X) e ''
      Set.Icc (interp_e e (2 ^ prec)) (interp_e e (2 ^ (prec + 1))) =
      Set.Icc (2 ^ prec) (2 ^ (prec + 1)) by grind
  exact (validRounder_round_near_e e).Icc (pow_le_pow_right₀ (by norm_num) (by linarith))

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

def round_near_all (prec : ℕ) := fun (x : X) ↦
  let e := Int.log 2 x - prec
  -- 2^(e + prec) <= x < 2^(e + prec + 1) for x ≠ 0
  -- So 2^prec <= round_near (x / 2^e) <= 2^(prec + 1)
  -- Normalization trims off the edge to [2^prec, 2^(prec + 1))
  normalize_edge prec ⟨round_near_e e x, e⟩

-- TODO: Better name
theorem round_near_e_mantissa (prec : ℕ) {x : X} (h : 0 < x) :
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


theorem round_near_all_mantissa [NeZero (2 : X)] (prec : ℕ) {x : X} (h : 0 < x) :
    2^prec <= (round_near_all prec x).1 ∧ (round_near_all prec x).1 < 2^(prec + 1) := by
  constructor
  · apply normalize_edge_narrows_prec_lower (k := X)
    apply validRounder_round_near.f_le_r_of_f_le_x
    exact_mod_cast (round_near_e_mantissa prec h).1
  apply normalize_edge_narrows_prec_upper (k := X)
  apply validRounder_round_near.r_le_f_of_x_le_f
  exact_mod_cast le_of_lt (round_near_e_mantissa prec h).2

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
    rw [Nat.cast_add, Nat.cast_one, <-add_assoc, round_near_all_top_eq]
    grind
  have xpos : 0 < x := lt_of_lt_of_le (by positivity) h.1
  have : Int.log 2 x = e + prec := by
    rw [Int.log_eq_iff (by norm_num) xpos]
    exact ⟨h.1, lt_of_le_of_ne h.2 x_eq⟩
  rw [round_near_all, normalize_edge_cast_comm, this, add_sub_cancel_right]

-- TODO: Do we need IsRoundUpOn and IsRoundDownOn?
-- TODO: Do we need that gluing preserves IsRoundUp and IsRoundDown?

-- Why isn't grind automatically accessing the member elements of approx?

-- TODO List:
-- [X] Ring operations on rounders (addition, multiplication)
-- [ ] Figure out why grind isn't unpacking approx elements automatically.
-- [X] FloorRings have round_down = floor and round_up = ceil.
-- [X] Minimum and maximum element lemmas
-- [X] Gluing operations: binary and Σ based.
-- [ ] Adding new bottom and top elements (not a priority, may be unnecessary)
-- [X] Bound with an interval [a, b]
-- [ ] Fix todos
-- [ ] Try bound tactic at each line

def round_near_normal (p : ℕ) (x : X) : NormalNumber p :=
  if h : 0 < x then
    match f_eq : round_near_all p x with
    | ⟨m, e⟩ => .mk m e (by
      have := round_near_all_mantissa (X := X) p h
      rwa [f_eq] at this
    )
  else
    .mk (2^p) (-p : ℤ) (by simp [pow_succ]) -- I chose 1 as junk

theorem round_near_normal_eq (p : ℕ) {x : X} (h : 0 < x) :
    (round_near_normal p x).interp X = interp_pair X (round_near_all p x) := by
  -- I love you grind
  grind [NormalNumber.interp, interp_e, round_near_normal]

theorem round_normal_interp (p : ℕ) :
    Function.LeftInverse (round_near_normal p) (NormalNumber.interp X) := by
  intro f
  apply NormalNumber.interp_injective (X := X)
  rw [round_near_normal_eq _ (f.interp_pos X),
    round_near_all_at_places p f.e _ (by grind [NormalNumber.interp_bound]),
    f.interp_e_proj, (validRounder_round_near_e (X := X) f.e).left_inverse f.m]

theorem interp_round_near_all_image (p : ℕ) {x : X} {i : ℤ}
    (h : x ∈ Set.Icc (2 ^ i) (2 ^ (i + 1))) :
    (round_near_normal p x).interp X ∈ Set.Icc (2 ^ i) (2 ^ (i + 1)) := by
  have xpos : 0 < x := lt_of_lt_of_le (by positivity) h.1
  rw [round_near_normal_eq _ xpos, round_near_all_at_places p (i - p)]
  · have hm : round_near_e (i - p) x ∈ Set.Icc (2 ^ p) (2 ^ (p + 1)) := by
      rw [<-round_near_e_image (e := i - p) p (X := X)]
      exact ⟨x, by simpa⟩
    convert interp_e_Icc (X := X) (i - p) hm <;> simp
  simp only [sub_add_cancel]
  exact h

theorem round_normal_monoOn (p : ℕ) :
    MonotoneOn (round_near_normal p) (Set.Ioi (0 : X)) := by
  rw [Ioi_zero_eq_iUnion_Icc_zpow (b := (2 : X)) (by norm_num)]
  apply MonotoneOn.iUnion_lowerBound
    (t := fun e ↦ round_near_normal p '' Set.Icc ((2 : X)^e) (2^(e+1)))
  case s_mono =>
    apply zpow_lowerBounds
  · intro i j h f ⟨x, xh⟩ f' ⟨y, yh⟩
    rw [NormalNumber.le_def X, <-xh.2, <-yh.2]
    exact zpow_lowerBounds h
      (interp_round_near_all_image _ xh.1)
      (interp_round_near_all_image _ yh.1)
  · intro i x xh y yh h
    rw [NormalNumber.le_def X]
    have xpos : 0 < x := lt_of_lt_of_le (by positivity) xh.1
    have ypos : 0 < y := lt_of_lt_of_le (by positivity) yh.1
    rw [round_near_normal_eq _ xpos, round_near_all_at_places p (i - p) x (by simpa)]
    rw [round_near_normal_eq _ ypos, round_near_all_at_places p (i - p) y (by simpa)]
    exact (validRounder_round_near_e _).i_mono ((validRounder_round_near_e _).r_mono h)
  exact fun i ↦ Set.mapsTo_image (round_near_normal p) (Set.Icc (2 ^ i) (2 ^ (i + 1)))

def partialRounder_round_near_normal (p : ℕ) :
    PartialRounder (NormalNumber.interp X) (round_near_normal p) (Set.Ioi 0) where
  r_mono := round_normal_monoOn p
  i_mono := (NormalNumber.interp_strictMono X).monotone.monotoneOn _
  left_inverse := (round_normal_interp p).leftInvOn _
  i_r_map _ _ := NormalNumber.interp_pos _ _

end
