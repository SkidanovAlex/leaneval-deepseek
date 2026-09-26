import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign2

namespace Work.Drive.EpsForm

open Set

noncomputable section

/-!
# Injectivity of the corrected profile `profX t` on `[0,1]`

`profX t` is the three-piece polyline `W1 -> W2c t -> W3c t -> W5c t` at the levels
`0 -> sig1c t -> sig2c t -> 1` (see `WaypointDesign2.lean`).  We prove that for every
`t in (-pi, pi]` the map `s |-> profX t s` is injective on `[0,1]`, and that `W1` is
attained only at `s = 0`.

Compared with the five-waypoint profile `profW` of `WaypointDesign.lean`, the last piece is the
chord `[W3c t, W5c t]` joining two points of the unit circle instead of the two radial segments
`[W3c t, W4]`, `[W4, W5c t]`; that chord runs strictly inside the disc except at its endpoints,
and we establish the corresponding elementary facts about it (`pf35` and its theory in
sections 8-9 below).

The material of sections 1-7 (`dot2`, `det2`, `n2` and the norm/segment/trigonometry facts for
the first two pieces) is reproduced from `profW_injOn.lean`, which cannot be imported alongside
`WaypointDesign2`: the three trigonometric identities `phLift_eq`, `cos_phLift`, `sin_phLift`
are declared both there and in `profW_levels.lean`, and Lean rejects two modules declaring the
same name.  The three overlapping identities are therefore taken from `profW_levels.lean`.
-/
/-! ## 1. Elementary plane algebra -/

/-- Scalar product of two vectors of the plane. -/
def dot2 (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- Determinant of two vectors of the plane. -/
def det2 (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Squared Euclidean norm of a vector of the plane. -/
def n2 (u : ℝ × ℝ) : ℝ := u.1 ^ 2 + u.2 ^ 2

theorem det2_skew (u v : ℝ × ℝ) : det2 u v = -det2 v u := by simp only [det2]; ring

theorem det2_self (u : ℝ × ℝ) : det2 u u = 0 := by simp only [det2]; ring

theorem det2_add_left (u v w : ℝ × ℝ) : det2 (u + v) w = det2 u w + det2 v w := by
  simp only [det2, Prod.fst_add, Prod.snd_add]; ring

theorem det2_add_right (u v w : ℝ × ℝ) : det2 u (v + w) = det2 u v + det2 u w := by
  simp only [det2, Prod.fst_add, Prod.snd_add]; ring

theorem det2_smul_left (c : ℝ) (u v : ℝ × ℝ) : det2 (c • u) v = c * det2 u v := by
  simp only [det2, Prod.smul_fst, Prod.smul_snd]; ring

theorem det2_smul_right (c : ℝ) (u v : ℝ × ℝ) : det2 u (c • v) = c * det2 u v := by
  simp only [det2, Prod.smul_fst, Prod.smul_snd]; ring

theorem det2_neg_right (u v : ℝ × ℝ) : det2 u (-v) = -det2 u v := by
  simp only [det2, Prod.fst_neg, Prod.snd_neg]; ring

theorem det2_cos_sin (x y : ℝ) :
    det2 (Real.cos x, Real.sin x) (Real.cos y, Real.sin y) = Real.sin (y - x) := by
  simp only [det2, Real.sin_sub]; ring

theorem dot2_comm (u v : ℝ × ℝ) : dot2 u v = dot2 v u := by simp only [dot2]; ring

theorem n2_smul (c : ℝ) (u : ℝ × ℝ) : n2 (c • u) = c ^ 2 * n2 u := by
  simp only [n2, Prod.smul_fst, Prod.smul_snd]; ring

theorem n2_conv (c d : ℝ) (u v : ℝ × ℝ) :
    n2 (c • u + d • v) = c ^ 2 * n2 u + 2 * c * d * dot2 u v + d ^ 2 * n2 v := by
  simp only [n2, dot2, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]; ring

theorem n2_sub (u v : ℝ × ℝ) : n2 (u - v) = n2 u - 2 * dot2 u v + n2 v := by
  simp only [n2, dot2, Prod.fst_sub, Prod.snd_sub]; ring

theorem n2_nonneg (u : ℝ × ℝ) : 0 ≤ n2 u := by
  simp only [n2]; nlinarith [sq_nonneg u.1, sq_nonneg u.2]

theorem dot2_le_one {u v : ℝ × ℝ} (hu : n2 u = 1) (hv : n2 v = 1) : dot2 u v ≤ 1 := by
  have h := n2_nonneg (u - v)
  rw [n2_sub, hu, hv] at h
  linarith

theorem smul_eq_zero_of_ne {c : ℝ} {v : ℝ × ℝ} (hv : v ≠ 0) (h : c • v = 0) : c = 0 := by
  have h1 : c * v.1 = 0 := by simpa using congrArg Prod.fst h
  have h2 : c * v.2 = 0 := by simpa using congrArg Prod.snd h
  rcases eq_or_ne v.1 0 with hv1 | hv1
  · rcases mul_eq_zero.mp h2 with hc | h2'
    · exact hc
    · exact absurd (Prod.ext hv1 h2') hv
  · exact (mul_eq_zero.mp h1).resolve_right hv1

theorem smul_eq_zero_of_scalar_ne {c : ℝ} {v : ℝ × ℝ} (hc : c ≠ 0) (h : c • v = 0) : v = 0 := by
  have h1 : c * v.1 = 0 := by simpa using congrArg Prod.fst h
  have h2 : c * v.2 = 0 := by simpa using congrArg Prod.snd h
  exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hc) ((mul_eq_zero.mp h2).resolve_left hc)

/-! ## 2. The segment map -/

theorem seg_apply (P Q : ℝ × ℝ) (a b s : ℝ) :
    seg P Q a b s = (1 - (s - a) / (b - a)) • P + ((s - a) / (b - a)) • Q := by
  ext <;> simp only [seg, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] <;> ring

theorem seg_eq_left (P Q : ℝ × ℝ) (a b : ℝ) : seg P Q a b a = P := by
  rw [seg_apply]; simp

theorem seg_eq_right {P Q : ℝ × ℝ} {a b : ℝ} (hab : a ≠ b) : seg P Q a b b = Q := by
  rw [seg_apply]
  have h : (b - a) / (b - a) = 1 := div_self (sub_ne_zero.mpr (Ne.symm hab))
  rw [h]; simp

theorem seg_sub_left (P Q : ℝ × ℝ) (a b s : ℝ) :
    seg P Q a b s - P = ((s - a) / (b - a)) • (Q - P) := by
  rw [seg_apply]
  ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
    Prod.snd_sub] <;> ring

theorem seg_injective {P Q : ℝ × ℝ} (hPQ : P ≠ Q) {a b : ℝ} (hab : a ≠ b) :
    Function.Injective (seg P Q a b) := by
  intro s s' h
  have hsub : ((s - a) / (b - a) - (s' - a) / (b - a)) • (Q - P) = 0 := by
    have h' : seg P Q a b s - P = seg P Q a b s' - P := by rw [h]
    rw [seg_sub_left, seg_sub_left] at h'
    rw [sub_smul, h', sub_self]
  have hQ : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
  have h0 : (s - a) / (b - a) - (s' - a) / (b - a) = 0 := smul_eq_zero_of_ne hQ hsub
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h1 : (s - a) / (b - a) = (s' - a) / (b - a) := by linarith
  rw [div_eq_div_iff hba hba] at h1
  have h2 : s - a = s' - a := mul_right_cancel₀ hba h1
  linarith

theorem seg_eq_left_iff {P Q : ℝ × ℝ} (hPQ : P ≠ Q) {a b : ℝ} (hab : a ≠ b) {s : ℝ} :
    seg P Q a b s = P ↔ s = a := by
  constructor
  · intro h
    have hsub : ((s - a) / (b - a)) • (Q - P) = 0 := by
      have h' : seg P Q a b s - P = 0 := by rw [h, sub_self]
      rwa [seg_sub_left] at h'
    have hQ : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
    have h0 : (s - a) / (b - a) = 0 := smul_eq_zero_of_ne hQ hsub
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have h1 : (s - a) / (b - a) * (b - a) = 0 := by rw [h0, zero_mul]
    rw [div_mul_cancel₀ _ hba] at h1
    linarith
  · intro h
    rw [h, seg_eq_left]

/-! ## 3. Trigonometry of the waypoint design -/

theorem dlt_eq_cos (t : ℝ) : dlt t = (1 / 2) * Real.cos (3 * t / 4) := by
  unfold dlt
  rw [bump_eq_cos]

theorem three_halves (t : ℝ) : t - phLift t = 3 * t / 2 + Real.pi := by
  rw [phLift_eq]; ring

theorem three_halves_sub (t : ℝ) :
    t - (phLift t + dlt t) = 3 * t / 2 - dlt t + Real.pi := by
  rw [phLift_eq]; ring

/-- `W2c t` in explicit coordinates (inside the chord range). -/
theorem W2c_expl {t : ℝ} (hin : inRange t) :
    W2c t = (-Real.cos (t / 2), Real.sin (t / 2)) := by
  rw [W2c, if_pos hin, cos_phLift, sin_phLift]

theorem n2_W5c (t : ℝ) : n2 (W5c t) = 1 := by
  simp only [W5c, n2]
  rw [Real.cos_sq_add_sin_sq]

theorem n2_W2c (t : ℝ) : n2 (W2c t) = 1 := by
  by_cases h : inRange t
  · rw [W2c, if_pos h]
    simp only [n2]
    rw [Real.cos_sq_add_sin_sq]
  · rw [W2c, if_neg h]
    exact n2_W5c t

theorem n2_W3c (t : ℝ) : n2 (W3c t) = 1 := by
  by_cases h : inRange t
  · rw [W3c, if_pos h]
    simp only [n2]
    rw [Real.cos_sq_add_sin_sq]
  · rw [W3c, if_neg h]
    exact n2_W5c t

theorem W1_ne_W2c (t : ℝ) : W1 ≠ W2c t := by
  intro h
  have h1 := n2_W2c t
  rw [← h] at h1
  simp only [W1, n2] at h1
  norm_num at h1

theorem W2c_ne_W1 (t : ℝ) : W2c t ≠ W1 := (W1_ne_W2c t).symm

theorem W3c_ne_W4 (t : ℝ) : W3c t ≠ W4 := by
  intro h
  have h1 := n2_W3c t
  rw [h] at h1
  simp only [W4, n2] at h1
  norm_num at h1

theorem W4_ne_W5c (t : ℝ) : W4 ≠ W5c t := by
  intro h
  have h1 := n2_W5c t
  rw [← h] at h1
  simp only [W4, n2] at h1
  norm_num at h1

/-- `inRange` for `t` strictly inside the chord range. -/
theorem inRange_of {t : ℝ} (hu : u0 < t) (hv : t < v0) : inRange t :=
  ⟨le_of_lt hu, le_of_lt hv⟩

theorem cos_half_gt_half {t : ℝ} (hu : u0 < t) (hv : t < v0) :
    1 / 2 < Real.cos (t / 2) := by
  have hu' : -(2 * Real.pi) / 3 < t := by simpa [u0] using hu
  have hv' : t < (2 * Real.pi) / 3 := by simpa [v0] using hv
  have hlt : |t / 2| < Real.pi / 3 := by
    rw [abs_lt]
    constructor <;> linarith [Real.pi_pos]
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := |t / 2|) (y := Real.pi / 3)
    (abs_nonneg _) (by linarith [Real.pi_pos]) hlt
  rw [Real.cos_pi_div_three] at h
  rwa [Real.cos_abs] at h

theorem dlt_pos {t : ℝ} (hu : u0 < t) (hv : t < v0) : 0 < dlt t := by
  rw [dlt_eq_cos]
  have hu' : -(2 * Real.pi) / 3 < t := by simpa [u0] using hu
  have hv' : t < (2 * Real.pi) / 3 := by simpa [v0] using hv
  have h1 : -(Real.pi / 2) < 3 * t / 4 := by linarith [Real.pi_pos]
  have h2 : 3 * t / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have := Real.cos_pos_of_mem_Ioo (show 3 * t / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
    from ⟨h1, h2⟩)
  linarith

theorem dlt_le_half (t : ℝ) : dlt t ≤ 1 / 2 := by
  rw [dlt_eq_cos]
  linarith [Real.cos_le_one (3 * t / 4)]

theorem sin_dlt_pos {t : ℝ} (hu : u0 < t) (hv : t < v0) : 0 < Real.sin (dlt t) :=
  Real.sin_pos_of_pos_of_lt_pi (dlt_pos hu hv) (by linarith [dlt_le_half t, Real.pi_gt_three])

/-- The key inequality of the design: `dlt t < 3t/2 + π` on the open chord range. -/
theorem dlt_lt_threeHalves_add_pi {t : ℝ} (hu : u0 < t) (hv : t < v0) :
    dlt t < 3 * t / 2 + Real.pi := by
  have hu' : -(2 * Real.pi) / 3 < t := by simpa [u0] using hu
  have hv' : t < (2 * Real.pi) / 3 := by simpa [v0] using hv
  have h1 : -(Real.pi / 2) < 3 * t / 4 := by linarith [Real.pi_pos]
  have h2 : 3 * t / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsin : Real.sin (3 * t / 4 + Real.pi / 2) = Real.cos (3 * t / 4) :=
    Real.sin_add_pi_div_two (3 * t / 4)
  have hv0 : 0 < 3 * t / 4 + Real.pi / 2 := by linarith [Real.pi_pos]
  rw [dlt_eq_cos, ← hsin]
  have h2' : 3 * t / 2 + Real.pi = 2 * (3 * t / 4 + Real.pi / 2) := by ring
  rw [h2']
  by_cases hv4 : 3 * t / 4 + Real.pi / 2 ≤ 1 / 4
  · have := Real.sin_lt hv0
    linarith
  · push_neg at hv4
    have := Real.sin_le_one (3 * t / 4 + Real.pi / 2)
    linarith

/-- The only nontrivial trigonometric inequality of the design. -/
theorem sin_key {t : ℝ} (hu : u0 < t) (hv : t < v0) :
    Real.sin (3 * t / 2 - dlt t) - Real.sin (3 * t / 2) < Real.sin (dlt t) := by
  have hu' : -(2 * Real.pi) / 3 < t := by simpa [u0] using hu
  have hv' : t < (2 * Real.pi) / 3 := by simpa [v0] using hv
  have hδ : 0 < dlt t := dlt_pos hu hv
  have hkey : dlt t < 3 * t / 2 + Real.pi := dlt_lt_threeHalves_add_pi hu hv
  have e1 : Real.sin (3 * t / 2 - dlt t) - Real.sin (3 * t / 2)
      = -2 * Real.sin (dlt t / 2) * Real.cos (3 * t / 2 - dlt t / 2) := by
    rw [Real.sin_sub_sin]
    have h1 : (3 * t / 2 - dlt t - 3 * t / 2) / 2 = -(dlt t / 2) := by ring
    have h2 : (3 * t / 2 - dlt t + 3 * t / 2) / 2 = 3 * t / 2 - dlt t / 2 := by ring
    rw [h1, h2, Real.sin_neg]
    ring
  have e2 : Real.sin (dlt t) = 2 * Real.sin (dlt t / 2) * Real.cos (dlt t / 2) := by
    rw [← Real.sin_two_mul]
    congr 1
    ring
  have hmain : 0 < Real.cos (3 * t / 2 - dlt t / 2) + Real.cos (dlt t / 2) := by
    rw [Real.cos_add_cos]
    have h1 : (3 * t / 2 - dlt t / 2 + dlt t / 2) / 2 = 3 * t / 4 := by ring
    have h2 : (3 * t / 2 - dlt t / 2 - dlt t / 2) / 2 = 3 * t / 4 - dlt t / 2 := by ring
    rw [h1, h2]
    have hc1 : 0 < Real.cos (3 * t / 4) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hc2 : 0 < Real.cos (3 * t / 4 - dlt t / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hkey], by linarith [Real.pi_pos, hδ]⟩
    exact mul_pos (by linarith) hc2
  have hsin2 : 0 < Real.sin (dlt t / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos, hδ]
  have hstep : 0 < 2 * Real.sin (dlt t / 2)
      * (Real.cos (3 * t / 2 - dlt t / 2) + Real.cos (dlt t / 2)) :=
    mul_pos (by linarith) hmain
  rw [e1, e2]
  nlinarith [hstep]

/-! ## 4. Determinant identities for the waypoints -/

theorem det2_W2c_W3c {t : ℝ} (hin : inRange t) :
    det2 (W2c t) (W3c t) = Real.sin (dlt t) := by
  rw [W2c, if_pos hin, W3c, if_pos hin, det2_cos_sin]
  congr 1
  ring

theorem det2_W2c_W5c {t : ℝ} (hin : inRange t) :
    det2 (W2c t) (W5c t) = -Real.sin (3 * t / 2) := by
  rw [W2c, if_pos hin]
  unfold W5c
  rw [det2_cos_sin, three_halves, Real.sin_add_pi]

theorem det2_W3c_W5c {t : ℝ} (hin : inRange t) :
    det2 (W3c t) (W5c t) = -Real.sin (3 * t / 2 - dlt t) := by
  rw [W3c, if_pos hin]
  unfold W5c
  rw [det2_cos_sin, three_halves_sub, Real.sin_add_pi]

theorem det2_W5c_diff {t : ℝ} (hin : inRange t) :
    det2 (W5c t) (W3c t - W2c t)
      = Real.sin (3 * t / 2 - dlt t) - Real.sin (3 * t / 2) := by
  rw [sub_eq_add_neg, det2_add_right, det2_neg_right]
  rw [det2_skew (W5c t) (W3c t), det2_W3c_W5c hin]
  rw [det2_skew (W5c t) (W2c t), det2_W2c_W5c hin]
  ring

theorem det2_W5c_diff_lt {t : ℝ} (hu : u0 < t) (hv : t < v0) :
    det2 (W5c t) (W3c t - W2c t) < Real.sin (dlt t) := by
  rw [det2_W5c_diff (inRange_of hu hv)]
  exact sin_key hu hv

theorem W2c_ne_W3c {t : ℝ} (hu : u0 < t) (hv : t < v0) : W2c t ≠ W3c t := by
  intro h
  have hd := det2_W2c_W3c (inRange_of hu hv)
  rw [h, det2_self] at hd
  exact absurd hd.symm (ne_of_gt (sin_dlt_pos hu hv))

/-- `W2c t ≠ W5c t` on the open chord range. -/
theorem W2c_ne_W5c {t : ℝ} (hu : u0 < t) (hv : t < v0) : W2c t ≠ W5c t := by
  intro h
  have h1 : -Real.cos (t / 2) = Real.cos t := by
    have := congrArg Prod.fst h
    simpa only [W2c_expl (inRange_of hu hv), W5c] using this
  have h2 : Real.cos (2 * (t / 2)) = 2 * Real.cos (t / 2) ^ 2 - 1 := Real.cos_two_mul (t / 2)
  rw [show (2 : ℝ) * (t / 2) = t by ring] at h2
  have hc := cos_half_gt_half hu hv
  have hcl := Real.cos_le_one (t / 2)
  have hfac : 2 * Real.cos (t / 2) ^ 2 - 1 + Real.cos (t / 2)
      = (2 * Real.cos (t / 2) - 1) * (Real.cos (t / 2) + 1) := by ring
  have hpos : 0 < (2 * Real.cos (t / 2) - 1) * (Real.cos (t / 2) + 1) := by
    apply mul_pos <;> linarith
  linarith

/-! ## 5. The four straight pieces of the profile -/

/-- The piece from `W1` to `W2c t`. -/
def pf1 (t l : ℝ) : ℝ × ℝ := (1 - l) • W1 + l • W2c t

/-- The chord from `W2c t` to `W3c t`. -/
def pf2 (t l : ℝ) : ℝ × ℝ := (1 - l) • W2c t + l • W3c t

/-- The piece from `W3c t` to the core point `W4`. -/
def pf3 (t l : ℝ) : ℝ × ℝ := (1 - l) • W3c t + l • W4

/-- The piece from the core point `W4` to the boundary point `W5c t`. -/
def pf4 (t l : ℝ) : ℝ × ℝ := (1 - l) • W4 + l • W5c t

theorem pf3_eq_smul (t l : ℝ) : pf3 t l = (1 - l) • W3c t := by
  rw [pf3, show W4 = (0 : ℝ × ℝ) from rfl, smul_zero, add_zero]

theorem pf4_eq_smul (t l : ℝ) : pf4 t l = l • W5c t := by
  rw [pf4, show W4 = (0 : ℝ × ℝ) from rfl, smul_zero, zero_add]

theorem seg_eq_pf1 (t s : ℝ) : seg W1 (W2c t) 0 (sig1 t) s = pf1 t (s / sig1 t) := by
  ext <;> simp only [seg, pf1, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] <;> ring

theorem seg_eq_pf2 (t s : ℝ) :
    seg (W2c t) (W3c t) (sig1 t) (sig2 t) s = pf2 t ((s - sig1 t) / (sig2 t - sig1 t)) := by
  ext <;> simp only [seg, pf2, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] <;> ring

theorem seg_eq_pf3 (t s : ℝ) :
    seg (W3c t) W4 (sig2 t) (tauP t) s = pf3 t ((s - sig2 t) / (tauP t - sig2 t)) := by
  ext <;> simp only [seg, pf3, W4, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] <;> ring

theorem seg_eq_pf4 (t s : ℝ) :
    seg W4 (W5c t) (tauP t) 1 s = pf4 t ((s - tauP t) / (1 - tauP t)) := by
  ext <;> simp only [seg, pf4, W4, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] <;> ring

theorem pf_inj {u v : ℝ × ℝ} (h : u ≠ v) :
    Function.Injective (fun l : ℝ => (1 - l) • u + l • v) := by
  intro l l' hl
  have hl' : (1 - l) • u + l • v = (1 - l') • u + l' • v := hl
  have h1 : (l - l') • (v - u) = 0 := by
    have hsub : (1 - l) • u + l • v - ((1 - l') • u + l' • v) = (l - l') • (v - u) := by
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
        Prod.snd_sub] <;> ring
    rw [← hsub, hl', sub_self]
  have hv : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have := smul_eq_zero_of_ne hv h1
  linarith

theorem pf1_inj (t : ℝ) : Function.Injective (pf1 t) := pf_inj (W1_ne_W2c t)

theorem pf2_inj {t : ℝ} (hu : u0 < t) (hv : t < v0) : Function.Injective (pf2 t) :=
  pf_inj (W2c_ne_W3c hu hv)

theorem pf3_inj (t : ℝ) : Function.Injective (pf3 t) := pf_inj (W3c_ne_W4 t)

theorem pf4_inj (t : ℝ) : Function.Injective (pf4 t) := pf_inj (W4_ne_W5c t)

/-! ## 6. Geometry of the four pieces -/

theorem n2_pf1_sub_one {t : ℝ} (hu : u0 < t) (hv : t < v0) (l : ℝ) :
    n2 (pf1 t l) - 1
      = (1 - l) * (2 * (2 * Real.cos (t / 2) - 1) + (1 - l) * n2 (W1 - W2c t)) := by
  have hd : dot2 W1 (W2c t) = 2 * Real.cos (t / 2) := by
    rw [W2c_expl (inRange_of hu hv)]
    simp only [dot2, W1]
    ring
  have hW1 : n2 W1 = 4 := by simp only [W1, n2]; norm_num
  have hsub : n2 (W1 - W2c t) = 5 - 4 * Real.cos (t / 2) := by
    rw [W2c_expl (inRange_of hu hv)]
    simp only [n2, W1, Prod.fst_sub, Prod.snd_sub]
    nlinarith [Real.cos_sq_add_sin_sq (t / 2)]
  rw [pf1, n2_conv, hd, n2_W2c t, hW1, hsub]
  ring

theorem n2_pf1_ge_one {t : ℝ} (hu : u0 < t) (hv : t < v0) {l : ℝ} (hl : l ≤ 1) :
    1 ≤ n2 (pf1 t l) := by
  have hc : 1 / 2 < Real.cos (t / 2) := cos_half_gt_half hu hv
  have hnn := n2_nonneg (W1 - W2c t)
  have hbr : 0 < 2 * (2 * Real.cos (t / 2) - 1) + (1 - l) * n2 (W1 - W2c t) := by nlinarith
  have h1 : 0 ≤ 1 - l := by linarith
  have h2 : 0 ≤ (1 - l) * (2 * (2 * Real.cos (t / 2) - 1) + (1 - l) * n2 (W1 - W2c t)) :=
    mul_nonneg h1 hbr.le
  linarith [n2_pf1_sub_one hu hv l]

theorem n2_pf1_eq_one_iff {t : ℝ} (hu : u0 < t) (hv : t < v0) {l : ℝ} (hl : l ≤ 1) :
    n2 (pf1 t l) = 1 ↔ l = 1 := by
  have hc : 1 / 2 < Real.cos (t / 2) := cos_half_gt_half hu hv
  have hnn := n2_nonneg (W1 - W2c t)
  have hbr : 0 < 2 * (2 * Real.cos (t / 2) - 1) + (1 - l) * n2 (W1 - W2c t) := by nlinarith
  have hsub := n2_pf1_sub_one hu hv l
  constructor
  · intro h
    have hz : (1 - l) * (2 * (2 * Real.cos (t / 2) - 1) + (1 - l) * n2 (W1 - W2c t)) = 0 := by
      linarith
    have := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hbr)
    linarith
  · intro h
    subst h
    simp [pf1, n2_W2c t]

theorem n2_pf2_le_one (t : ℝ) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : n2 (pf2 t l) ≤ 1 := by
  have hdot := dot2_le_one (n2_W2c t) (n2_W3c t)
  have h0 : 0 ≤ l * (1 - l) := mul_nonneg hl.1 (by linarith [hl.2])
  have hmul : 2 * l * (1 - l) * dot2 (W2c t) (W3c t) ≤ 2 * l * (1 - l) * 1 :=
    mul_le_mul_of_nonneg_left hdot (by linarith)
  rw [pf2, n2_conv, n2_W2c t, n2_W3c t]
  nlinarith [hmul]

theorem n2_pf3_le_one (t : ℝ) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : n2 (pf3 t l) ≤ 1 := by
  rw [pf3_eq_smul, n2_smul, n2_W3c t]
  nlinarith [hl.1, hl.2]

theorem n2_pf4_le_one (t : ℝ) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : n2 (pf4 t l) ≤ 1 := by
  rw [pf4_eq_smul, n2_smul, n2_W5c t]
  nlinarith [hl.1, hl.2]

theorem det2_conv_snd (c d : ℝ) (u v : ℝ × ℝ) :
    det2 (c • u + d • v) v = c * det2 u v := by
  simp only [det2, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]; ring

theorem det2_conv_sub (c d : ℝ) (u v : ℝ × ℝ) :
    det2 (c • u + d • v) (v - u) = (c + d) * det2 u v := by
  simp only [det2, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
    Prod.snd_sub]; ring

/-- The segment `[W1, W2c t]` meets the chord `[W2c t, W3c t]` only in `W2c t`. -/
theorem pf1_pf2 {t : ℝ} (hu : u0 < t) (hv : t < v0) {l l' : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (hl' : l' ∈ Icc (0 : ℝ) 1) (h : pf1 t l = pf2 t l') :
    l = 1 ∧ l' = 0 := by
  have hge := n2_pf1_ge_one hu hv hl.2
  have hle := n2_pf2_le_one t hl'
  have hn := congrArg n2 h
  have hl1 : l = 1 := (n2_pf1_eq_one_iff hu hv hl.2).mp (by linarith)
  refine ⟨hl1, ?_⟩
  have hA : W2c t = pf2 t l' := by rw [← h, hl1]; simp [pf1]
  have hsub : pf2 t l' - W2c t = l' • (W3c t - W2c t) := by
    ext <;> simp only [pf2, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub] <;> ring
  have hz : l' • (W3c t - W2c t) = 0 := by rw [← hsub, hA, sub_self]
  exact smul_eq_zero_of_ne (sub_ne_zero.mpr (Ne.symm (W2c_ne_W3c hu hv))) hz

/-- The segment `[W1, W2c t]` misses the radial segment `[W3c t, W4]`. -/
theorem pf1_pf3 {t : ℝ} (hu : u0 < t) (hv : t < v0) {l l' : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (hl' : l' ∈ Icc (0 : ℝ) 1) (h : pf1 t l = pf3 t l') : False := by
  have hge := n2_pf1_ge_one hu hv hl.2
  have hle := n2_pf3_le_one t hl'
  have hn := congrArg n2 h
  have hl1 : l = 1 := (n2_pf1_eq_one_iff hu hv hl.2).mp (by linarith)
  have hA : W2c t = (1 - l') • W3c t := by
    rw [← pf3_eq_smul t l', ← h, hl1]
    simp [pf1]
  have h2 : n2 (W2c t) = n2 ((1 - l') • W3c t) := congrArg n2 hA
  rw [n2_W2c t, n2_smul, n2_W3c t] at h2
  have hsq : (1 - l') ^ 2 = 1 := by linarith [h2]
  have h1ml : 1 - l' = 1 := by
    rcases sq_eq_one_iff.mp hsq with h3 | h3
    · exact h3
    · linarith [hl'.2]
  exact W2c_ne_W3c hu hv (by rw [hA, h1ml, one_smul])

/-- The segment `[W1, W2c t]` misses the radial segment `[W4, W5c t]`. -/
theorem pf1_pf4 {t : ℝ} (hu : u0 < t) (hv : t < v0) {l l' : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (hl' : l' ∈ Icc (0 : ℝ) 1) (h : pf1 t l = pf4 t l') : False := by
  have hge := n2_pf1_ge_one hu hv hl.2
  have hle := n2_pf4_le_one t hl'
  have hn := congrArg n2 h
  have hl1 : l = 1 := (n2_pf1_eq_one_iff hu hv hl.2).mp (by linarith)
  have hA : W2c t = l' • W5c t := by
    rw [← pf4_eq_smul t l', ← h, hl1]
    simp [pf1]
  have h2 : n2 (W2c t) = n2 (l' • W5c t) := congrArg n2 hA
  rw [n2_W2c t, n2_smul, n2_W5c t] at h2
  have hsq : l' ^ 2 = 1 := by linarith [h2]
  have hl'1 : l' = 1 := by
    rcases sq_eq_one_iff.mp hsq with h3 | h3
    · exact h3
    · linarith [hl'.1]
  exact W2c_ne_W5c hu hv (by rw [hA, hl'1, one_smul])

/-- The chord `[W2c t, W3c t]` meets the radial segment `[W3c t, W4]` only in `W3c t`. -/
theorem pf2_pf3 {t : ℝ} (hu : u0 < t) (hv : t < v0) {l l' : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (hl' : l' ∈ Icc (0 : ℝ) 1) (h : pf2 t l = pf3 t l') :
    l = 1 ∧ l' = 0 := by
  have hin : inRange t := inRange_of hu hv
  have hsin := sin_dlt_pos hu hv
  have hdet := congrArg (fun w => det2 w (W3c t)) h
  rw [pf2, det2_conv_snd, det2_W2c_W3c hin, pf3_eq_smul, det2_smul_left, det2_self, mul_zero]
    at hdet
  have hl1 : l = 1 := by
    have := (mul_eq_zero.mp hdet).resolve_right (ne_of_gt hsin)
    linarith
  refine ⟨hl1, ?_⟩
  have hB : W3c t = (1 - l') • W3c t := by
    rw [← pf3_eq_smul, ← h, hl1]
    simp [pf2]
  have hn := congrArg n2 hB
  rw [n2_smul, n2_W3c t] at hn
  have hsq : (1 - l') ^ 2 = 1 := by linarith [hn]
  have h1ml : 1 - l' = 1 := by
    rcases sq_eq_one_iff.mp hsq with h3 | h3
    · exact h3
    · linarith [hl'.2]
  linarith

/-- The chord `[W2c t, W3c t]` misses the radial segment `[W4, W5c t]` (the crux). -/
theorem pf2_pf4 {t : ℝ} (hu : u0 < t) (hv : t < v0) {l l' : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (hl' : l' ∈ Icc (0 : ℝ) 1) (h : pf2 t l = pf4 t l') : False := by
  have hin : inRange t := inRange_of hu hv
  have hsin := sin_dlt_pos hu hv
  have hD := det2_W5c_diff_lt hu hv
  have hdet := congrArg (fun w => det2 w (W3c t - W2c t)) h
  rw [pf2, det2_conv_sub, det2_W2c_W3c hin, pf4_eq_smul, det2_smul_left] at hdet
  simp only [sub_add_cancel, one_mul] at hdet
  have hmu_pos : 0 < l' := by
    rcases eq_or_lt_of_le hl'.1 with h0 | h0
    · rw [← h0, zero_mul] at hdet
      exact absurd hdet (ne_of_gt hsin)
    · exact h0
  have hDpos : 0 < det2 (W5c t) (W3c t - W2c t) := by nlinarith [hdet, hsin, hmu_pos]
  have hle : Real.sin (dlt t) ≤ det2 (W5c t) (W3c t - W2c t) := by
    rw [hdet]
    nlinarith [hl'.2, hmu_pos, hDpos]
  linarith [hD]

/-- `W3c t ≠ W5c t` on the open chord range. -/
theorem W3c_ne_W5c {t : ℝ} (hu : u0 < t) (hv : t < v0) : W3c t ≠ W5c t := by
  intro h
  have h1 : pf2 t 1 = pf4 t 1 := by
    rw [pf2, pf4, show W4 = (0 : ℝ × ℝ) from rfl]
    simp only [one_smul, sub_self, zero_smul, zero_add]
    exact h
  exact pf2_pf4 hu hv (by norm_num) (by norm_num) h1

/-- The two radial segments `[W3c t, W4]` and `[W4, W5c t]` meet only in `W4`. -/
theorem pf3_pf4 {t : ℝ} (hu : u0 < t) (hv : t < v0) {l l' : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (hl' : l' ∈ Icc (0 : ℝ) 1) (h : pf3 t l = pf4 t l') :
    l = 1 ∧ l' = 0 := by
  rw [pf3_eq_smul, pf4_eq_smul] at h
  have hn := congrArg n2 h
  rw [n2_smul, n2_smul, n2_W3c t, n2_W5c t] at hn
  have h1 : 1 - l = l' := by
    have hsq : (1 - l) ^ 2 = l' ^ 2 := by linarith [hn]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h3 | h3
    · exact h3
    · linarith [hl.2, hl'.1]
  have h5 : (1 - l) • W3c t = (1 - l) • W5c t := by simpa [h1] using h
  have h2 : (1 - l) • (W3c t - W5c t) = 0 := by
    rw [smul_sub, sub_eq_zero]
    exact h5
  have h3 : 1 - l = 0 :=
    smul_eq_zero_of_ne (sub_ne_zero.mpr (W3c_ne_W5c hu hv)) h2
  exact ⟨by linarith, by linarith⟩

/-! ## 7. Parameter ranges of the four branches -/

theorem par1_mem {t s : ℝ} (hu : u0 < t) (hv : t < v0) (hs : 0 ≤ s) (h : s ≤ sig1 t) :
    s / sig1 t ∈ Icc (0 : ℝ) 1 := by
  have h1 : 0 < sig1 t := (waypoint_levels.1 t hu hv).1
  exact ⟨div_nonneg hs h1.le, (div_le_one h1).mpr h⟩

theorem par2_mem {t s : ℝ} (hu : u0 < t) (hv : t < v0) (h1 : sig1 t < s) (h2 : s ≤ sig2 t) :
    (s - sig1 t) / (sig2 t - sig1 t) ∈ Icc (0 : ℝ) 1 := by
  have hlev := waypoint_levels.1 t hu hv
  have hpos : 0 < sig2 t - sig1 t := by linarith [hlev.2.1]
  exact ⟨div_nonneg (by linarith [hlev.1]) hpos.le, (div_le_one hpos).mpr (by linarith)⟩

theorem par3_mem {t s : ℝ} (hu : u0 < t) (hv : t < v0) (h1 : sig2 t < s) (h2 : s ≤ tauP t) :
    (s - sig2 t) / (tauP t - sig2 t) ∈ Icc (0 : ℝ) 1 := by
  have hlev := waypoint_levels.1 t hu hv
  have hpos : 0 < tauP t - sig2 t := by linarith [hlev.2.2.1]
  exact ⟨div_nonneg (by linarith [hlev.2.1]) hpos.le, (div_le_one hpos).mpr (by linarith)⟩

theorem par4_mem {t s : ℝ} (hu : u0 < t) (hv : t < v0) (hs : s ≤ 1) (h1 : tauP t < s) :
    (s - tauP t) / (1 - tauP t) ∈ Icc (0 : ℝ) 1 := by
  have hlev := waypoint_levels.1 t hu hv
  have hpos : 0 < 1 - tauP t := by linarith [hlev.2.2.2]
  exact ⟨div_nonneg (by linarith [hlev.2.2.1]) hpos.le, (div_le_one hpos).mpr (by linarith)⟩

theorem profW_eq_pf1 {t s : ℝ} (hin : inRange t) (h : s ≤ sig1 t) :
    profW t s = pf1 t (s / sig1 t) := by
  have h' : s ≤ sig1c t := by rw [sig1c, if_pos hin]; exact h
  rw [profW, if_pos h']
  rw [sig1c, if_pos hin]
  exact seg_eq_pf1 t s

theorem profW_eq_pf2 {t s : ℝ} (hin : inRange t) (h1 : ¬ s ≤ sig1 t) (h2 : s ≤ sig2 t) :
    profW t s = pf2 t ((s - sig1 t) / (sig2 t - sig1 t)) := by
  have h1' : ¬ s ≤ sig1c t := by rw [sig1c, if_pos hin]; exact h1
  have h2' : s ≤ sig2c t := by rw [sig2c, if_pos hin]; exact h2
  rw [profW, if_neg h1', if_pos h2']
  rw [sig1c, if_pos hin, sig2c, if_pos hin]
  exact seg_eq_pf2 t s

theorem profW_eq_pf3 {t s : ℝ} (hin : inRange t) (h1 : ¬ s ≤ sig1 t) (h2 : ¬ s ≤ sig2 t)
    (h3 : s ≤ tauP t) :
    profW t s = pf3 t ((s - sig2 t) / (tauP t - sig2 t)) := by
  have h1' : ¬ s ≤ sig1c t := by rw [sig1c, if_pos hin]; exact h1
  have h2' : ¬ s ≤ sig2c t := by rw [sig2c, if_pos hin]; exact h2
  have h3' : s ≤ tauc t := by rw [tauc, if_pos hin]; exact h3
  rw [profW, if_neg h1', if_neg h2', if_pos h3']
  rw [sig2c, if_pos hin, tauc, if_pos hin]
  exact seg_eq_pf3 t s

theorem profW_eq_pf4 {t s : ℝ} (hin : inRange t) (h1 : ¬ s ≤ sig1 t) (h2 : ¬ s ≤ sig2 t)
    (h3 : ¬ s ≤ tauP t) :
    profW t s = pf4 t ((s - tauP t) / (1 - tauP t)) := by
  have h1' : ¬ s ≤ sig1c t := by rw [sig1c, if_pos hin]; exact h1
  have h2' : ¬ s ≤ sig2c t := by rw [sig2c, if_pos hin]; exact h2
  have h3' : ¬ s ≤ tauc t := by rw [tauc, if_pos hin]; exact h3
  rw [profW, if_neg h1', if_neg h2', if_neg h3']
  rw [tauc, if_pos hin]
  exact seg_eq_pf4 t s

/-! ## 8. The third piece `[W3c t, W5c t]` of the corrected profile -/

/-- The chord from `W3c t` to `W5c t`. -/
def pf35 (t l : ℝ) : ℝ × ℝ := (1 - l) • W3c t + l • W5c t

theorem seg_eq_pf35 (t a b s : ℝ) :
    seg (W3c t) (W5c t) a b s = pf35 t ((s - a) / (b - a)) := by
  ext <;> simp only [seg, pf35, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
    <;> ring

theorem pf35_zero (t : ℝ) : pf35 t 0 = W3c t := by simp [pf35]

theorem pf35_one (t : ℝ) : pf35 t 1 = W5c t := by simp [pf35]

theorem pf35_inj {t : ℝ} (hu : u0 < t) (hv : t < v0) : Function.Injective (pf35 t) :=
  pf_inj (W3c_ne_W5c hu hv)

/-! ## 9. Norm of a convex combination of unit vectors -/

theorem n2_eq_zero {u : ℝ × ℝ} (h : n2 u = 0) : u = 0 := by
  simp only [n2] at h
  have h1 : u.1 ^ 2 = 0 := by nlinarith [sq_nonneg u.2]
  have h2 : u.2 ^ 2 = 0 := by nlinarith [sq_nonneg u.1]
  exact Prod.ext (sq_eq_zero_iff.mp h1) (sq_eq_zero_iff.mp h2)

/-- Two unit vectors have scalar product `1` exactly when they are equal. -/
theorem dot2_eq_one_iff {u v : ℝ × ℝ} (hu : n2 u = 1) (hv : n2 v = 1) :
    dot2 u v = 1 ↔ u = v := by
  constructor
  · intro h
    have h0 : n2 (u - v) = 0 := by rw [n2_sub, hu, hv, h]; ring
    exact sub_eq_zero.mp (n2_eq_zero h0)
  · intro h
    subst h
    have h' : dot2 u u = n2 u := by simp only [dot2, n2, pow_two]
    rw [h', hu]

theorem det2_sub_left (u v w : ℝ × ℝ) : det2 (u - v) w = det2 u w - det2 v w := by
  simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring

theorem det2_sub_right (u v w : ℝ × ℝ) : det2 u (v - w) = det2 u v - det2 u w := by
  simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring

/-- A convex combination of two unit vectors has norm at most `1`. -/
theorem n2_conv_le_one {u v : ℝ × ℝ} (hu : n2 u = 1) (hv : n2 v = 1) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) : n2 ((1 - l) • u + l • v) ≤ 1 := by
  have hdot := dot2_le_one hu hv
  have h0 : 0 ≤ 2 * l * (1 - l) := by nlinarith [hl.1, hl.2]
  have hmul := mul_le_mul_of_nonneg_left hdot h0
  rw [n2_conv, hu, hv]
  nlinarith [hmul]

/-- A convex combination, with parameter strictly between `0` and `1`, of two *distinct*
unit vectors has norm strictly less than `1` (strict convexity of the disc). -/
theorem n2_conv_lt_one {u v : ℝ × ℝ} (hu : n2 u = 1) (hv : n2 v = 1) (huv : u ≠ v)
    {l : ℝ} (h0 : 0 < l) (h1 : l < 1) : n2 ((1 - l) • u + l • v) < 1 := by
  have hne : dot2 u v ≠ 1 := fun hc => huv ((dot2_eq_one_iff hu hv).mp hc)
  have hlt : dot2 u v < 1 := lt_of_le_of_ne (dot2_le_one hu hv) hne
  have hfac : 0 < 2 * l * (1 - l) := by nlinarith
  have hpos : 0 < 2 * l * (1 - l) * (1 - dot2 u v) := mul_pos hfac (by linarith)
  rw [n2_conv, hu, hv]
  nlinarith [hpos]

theorem n2_pf35_le_one (t : ℝ) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : n2 (pf35 t l) ≤ 1 := by
  rw [pf35]
  exact n2_conv_le_one (n2_W3c t) (n2_W5c t) hl

theorem n2_pf35_lt_one {t : ℝ} (hu : u0 < t) (hv : t < v0) {l : ℝ} (h0 : 0 < l)
    (h1 : l < 1) : n2 (pf35 t l) < 1 := by
  rw [pf35]
  exact n2_conv_lt_one (n2_W3c t) (n2_W5c t) (W3c_ne_W5c hu hv) h0 h1

theorem n2_pf2_lt_one {t : ℝ} (hu : u0 < t) (hv : t < v0) {l : ℝ} (h0 : 0 < l)
    (h1 : l < 1) : n2 (pf2 t l) < 1 := by
  rw [pf2]
  exact n2_conv_lt_one (n2_W2c t) (n2_W3c t) (W2c_ne_W3c hu hv) h0 h1

theorem n2_pf35_eq_one_iff {t : ℝ} (hu : u0 < t) (hv : t < v0) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) : n2 (pf35 t l) = 1 ↔ l = 0 ∨ l = 1 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h0 : 0 < l := lt_of_le_of_ne hl.1 (Ne.symm hc.1)
    have h1 : l < 1 := lt_of_le_of_ne hl.2 hc.2
    have := n2_pf35_lt_one hu hv h0 h1
    linarith
  · rintro (rfl | rfl)
    · rw [pf35_zero, n2_W3c t]
    · rw [pf35_one, n2_W5c t]

/-! ## 10. The third piece against the first two -/

/-- The segment `[W1, W2c t]` misses the chord `[W3c t, W5c t]`. -/
theorem pf1_pf35 {t : ℝ} (hu : u0 < t) (hv : t < v0) {l l' : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (hl' : l' ∈ Icc (0 : ℝ) 1) (h : pf1 t l = pf35 t l') :
    False := by
  have hge := n2_pf1_ge_one hu hv hl.2
  have hle := n2_pf35_le_one t hl'
  have hl1 : l = 1 := (n2_pf1_eq_one_iff hu hv hl.2).mp (by
    have hn := congrArg n2 h
    linarith)
  have hW : W2c t = pf35 t l' := by rw [← h, hl1]; simp [pf1]
  have hn2 : n2 (pf35 t l') = 1 := by rw [← hW]; exact n2_W2c t
  rcases (n2_pf35_eq_one_iff hu hv hl').mp hn2 with h0 | h1
  · exact W2c_ne_W3c hu hv (by rw [hW, h0, pf35_zero])
  · exact W2c_ne_W5c hu hv (by rw [hW, h1, pf35_one])

/-- The chord `[W2c t, W3c t]` meets the chord `[W3c t, W5c t]` only in `W3c t`. -/
theorem pf2_pf35 {t : ℝ} (hu : u0 < t) (hv : t < v0) {l l' : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (hl' : l' ∈ Icc (0 : ℝ) 1) (h : pf2 t l = pf35 t l') :
    l = 1 ∧ l' = 0 := by
  have hin : inRange t := inRange_of hu hv
  have hD : det2 (W2c t - W3c t) (W5c t - W3c t) < 0 := by
    have e1 : det2 (W2c t - W3c t) (W5c t - W3c t)
        = det2 (W2c t) (W5c t) - det2 (W2c t) (W3c t)
          - det2 (W3c t) (W5c t) + det2 (W3c t) (W3c t) := by
      simp only [det2_sub_left, det2_sub_right]; ring
    rw [e1, det2_self, det2_W2c_W5c hin, det2_W3c_W5c hin, det2_W2c_W3c hin]
    linarith [sin_key hu hv]
  have hA : pf2 t l - W3c t = (1 - l) • (W2c t - W3c t) := by
    ext <;> simp only [pf2, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub] <;> ring
  have hB : pf35 t l' - W3c t = l' • (W5c t - W3c t) := by
    ext <;> simp only [pf35, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub] <;> ring
  have hEq : (1 - l) • (W2c t - W3c t) = l' • (W5c t - W3c t) := by
    rw [← hA, ← hB, h]
  by_cases hl1 : l = 1
  · subst hl1
    have hz : l' • (W5c t - W3c t) = 0 := by rw [← hEq]; simp
    have hne : W5c t - W3c t ≠ 0 := sub_ne_zero.mpr (Ne.symm (W3c_ne_W5c hu hv))
    exact ⟨rfl, smul_eq_zero_of_ne hne hz⟩
  · exfalso
    have hdet := congrArg (fun w => det2 w (W5c t - W3c t)) hEq
    rw [det2_smul_left, det2_smul_left, det2_self, mul_zero] at hdet
    have hne : (1 : ℝ) - l ≠ 0 := fun h0 => hl1 (by linarith)
    rcases mul_eq_zero.mp hdet with h3 | h3
    · exact absurd h3 hne
    · linarith

/-! ## 11. The main statement -/

/-- **Injectivity of the corrected profile in the radial parameter.**  For `t ∈ (-π,π]`,
`s ↦ profX t s` is injective on `[0,1]`, and `W1` is attained only at `s = 0`.

Route: the three pieces are the segments `[W1, W2c t]`, `[W2c t, W3c t]`, `[W3c t, W5c t]`
on the levels `[0,sig1c t]`, `[sig1c t,sig2c t]`, `[sig2c t,1]`.  A point of the first
piece has norm `≥ 1` with equality only at `s = sig1c t` (because `(W2c t).1 ≤ -1/2`),
points of the second have norm `≤ 1`, and points of the third have norm `< 1` for
`sig2c t < s < 1` and norm `1` at the two ends.  Hence two pieces can only meet at a
shared endpoint, and each piece is injective in `s`.  Finally `W1` has norm `2`, and every
other point of the profile has norm `< 2`. -/
theorem profX_injOn {t : ℝ} (ht : -Real.pi < t) (ht' : t ≤ Real.pi) :
    Set.InjOn (fun s => profX t s) (Set.Icc 0 1) ∧
    (∀ s ∈ Set.Icc 0 1, profX t s = W1 → s = 0) := by
  by_cases hge : (1 : ℝ) ≤ sig1c t
  · -- Degenerate case: `sig1c t = 1`, the whole profile is the single segment `[W1, W2c t]`.
    have hs1 : sig1c t = 1 := le_antisymm (sig1c_le_one t) hge
    have hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, profX t x = seg W1 (W2c t) 0 1 x := by
      intro x hx
      have hx1 : x ≤ sig1c t := by rw [hs1]; exact hx.2
      rw [profX_br1 hx1, hs1]
    refine ⟨?_, ?_⟩
    · intro s hs s' hs' heq
      have heq' : profX t s = profX t s' := heq
      rw [hf s hs, hf s' hs'] at heq'
      exact seg_injective (W1_ne_W2c t) (by norm_num) heq'
    · intro s hs heq
      rw [hf s hs] at heq
      exact (seg_eq_left_iff (W1_ne_W2c t) (by norm_num : (0 : ℝ) ≠ 1)).mp heq
  · -- Open case: `sig1c t < 1`, so `u0 < t < v0` and the three pieces are genuine.
    have hlt : sig1c t < 1 := not_le.mp hge
    have hin : inRange t := by
      by_contra hco
      rw [sig1c, if_neg hco] at hlt
      exact absurd hlt (lt_irrefl 1)
    have hsig1 : sig1c t = sig1 t := by rw [sig1c, if_pos hin]
    have hsig2 : sig2c t = sig2 t := by rw [sig2c, if_pos hin]
    have hbump : 0 < bump t := by
      have h : sig1 t < 1 := by rw [← hsig1]; exact hlt
      unfold sig1 at h
      linarith
    have hopen := (bump_pos_iff hin).mp hbump
    have hu : u0 < t := hopen.1
    have hv : t < v0 := hopen.2
    have hlev := waypoint_levels.1 t hu hv
    have hpos1 : 0 < sig1 t := hlev.1
    have hlt12 : sig1 t < sig2 t := hlev.2.1
    have hlt2 : sig2 t < 1 := lt_trans hlev.2.2.1 hlev.2.2.2
    -- the three branches of `profX`
    have hb1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, s ≤ sig1 t → profX t s = pf1 t (s / sig1 t) := by
      intro s hs h
      have h' : s ≤ sig1c t := by rw [hsig1]; exact h
      rw [profX_br1 h', hsig1]
      exact seg_eq_pf1 t s
    have hb2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, sig1 t < s → s ≤ sig2 t →
        profX t s = pf2 t ((s - sig1 t) / (sig2 t - sig1 t)) := by
      intro s hs h1 h2
      have h1' : ¬ s ≤ sig1c t := by rw [hsig1]; exact not_le.mpr h1
      have h2' : s ≤ sig2c t := by rw [hsig2]; exact h2
      rw [profX_br2 h1' h2', hsig1, hsig2]
      exact seg_eq_pf2 t s
    have hb3 : ∀ s ∈ Set.Icc (0 : ℝ) 1, sig2 t < s →
        profX t s = pf35 t ((s - sig2 t) / (1 - sig2 t)) := by
      intro s hs h2
      have h1' : ¬ s ≤ sig1c t := by
        rw [hsig1]; exact not_le.mpr (lt_trans hlt12 h2)
      have h2' : ¬ s ≤ sig2c t := by rw [hsig2]; exact not_le.mpr h2
      rw [profX_br3 h1' h2', hsig2]
      exact seg_eq_pf35 t (sig2 t) 1 s
    have hbranch : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (s ≤ sig1 t ∧ profX t s = pf1 t (s / sig1 t)) ∨
        (sig1 t < s ∧ s ≤ sig2 t ∧
          profX t s = pf2 t ((s - sig1 t) / (sig2 t - sig1 t))) ∨
        (sig2 t < s ∧ profX t s = pf35 t ((s - sig2 t) / (1 - sig2 t))) := by
      intro s hs
      by_cases h1 : s ≤ sig1 t
      · exact Or.inl ⟨h1, hb1 s hs h1⟩
      · have h1' : sig1 t < s := not_le.mp h1
        by_cases h2 : s ≤ sig2 t
        · exact Or.inr (Or.inl ⟨h1', h2, hb2 s hs h1' h2⟩)
        · exact Or.inr (Or.inr ⟨not_le.mp h2, hb3 s hs (not_le.mp h2)⟩)
    have hpar1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, s ≤ sig1 t → s / sig1 t ∈ Set.Icc (0 : ℝ) 1 := by
      intro s hs h
      exact ⟨div_nonneg hs.1 hpos1.le, (div_le_one hpos1).mpr h⟩
    have hpar2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, sig1 t ≤ s → s ≤ sig2 t →
        (s - sig1 t) / (sig2 t - sig1 t) ∈ Set.Icc (0 : ℝ) 1 := by
      intro s hs h1 h2
      have hp : 0 < sig2 t - sig1 t := by linarith
      exact ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith)⟩
    have hpar3 : ∀ s ∈ Set.Icc (0 : ℝ) 1, sig2 t ≤ s →
        (s - sig2 t) / (1 - sig2 t) ∈ Set.Icc (0 : ℝ) 1 := by
      intro s hs h1
      have hp : 0 < 1 - sig2 t := by linarith
      exact ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith [hs.2])⟩
    have hmain : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ s' ∈ Set.Icc (0 : ℝ) 1, s < s' →
        profX t s ≠ profX t s' := by
      intro s hs s' hs' hlt' heq
      rcases hbranch s hs with ⟨ha, hEa⟩ | ⟨ha1, ha2, hEa⟩ | ⟨ha1, hEa⟩
      · rcases hbranch s' hs' with ⟨hb, hEb⟩ | ⟨hb1, hb2, hEb⟩ | ⟨hb1, hEb⟩
        · have h' : pf1 t (s / sig1 t) = pf1 t (s' / sig1 t) := by
            rw [← hEa, ← hEb]; exact heq
          have h2 := pf1_inj t h'
          have h3 : s = s' := by
            rw [div_eq_div_iff (ne_of_gt hpos1) (ne_of_gt hpos1)] at h2
            exact mul_right_cancel₀ (ne_of_gt hpos1) h2
          exact absurd h3 (ne_of_lt hlt')
        · have h' : pf1 t (s / sig1 t) = pf2 t ((s' - sig1 t) / (sig2 t - sig1 t)) := by
            rw [← hEa, ← hEb]; exact heq
          obtain ⟨_, e2⟩ :=
            pf1_pf2 hu hv (hpar1 s hs ha) (hpar2 s' hs' (le_of_lt hb1) hb2) h'
          have hne : sig2 t - sig1 t ≠ 0 := by linarith
          have h0 : s' - sig1 t = 0 := (div_eq_zero_iff.mp e2).resolve_right hne
          linarith
        · have h' : pf1 t (s / sig1 t) = pf35 t ((s' - sig2 t) / (1 - sig2 t)) := by
            rw [← hEa, ← hEb]; exact heq
          exact pf1_pf35 hu hv (hpar1 s hs ha) (hpar3 s' hs' (le_of_lt hb1)) h'
      · rcases hbranch s' hs' with ⟨hb, hEb⟩ | ⟨hb1, hb2, hEb⟩ | ⟨hb1, hEb⟩
        · linarith
        · have h' : pf2 t ((s - sig1 t) / (sig2 t - sig1 t))
              = pf2 t ((s' - sig1 t) / (sig2 t - sig1 t)) := by
            rw [← hEa, ← hEb]; exact heq
          have h2 := pf2_inj hu hv h'
          have hne : sig2 t - sig1 t ≠ 0 := by linarith
          have h3 : s = s' := by
            rw [div_eq_div_iff hne hne] at h2
            have := mul_right_cancel₀ hne h2
            linarith
          exact absurd h3 (ne_of_lt hlt')
        · have h' : pf2 t ((s - sig1 t) / (sig2 t - sig1 t))
              = pf35 t ((s' - sig2 t) / (1 - sig2 t)) := by
            rw [← hEa, ← hEb]; exact heq
          obtain ⟨_, e2⟩ :=
            pf2_pf35 hu hv (hpar2 s hs (le_of_lt ha1) ha2) (hpar3 s' hs' (le_of_lt hb1)) h'
          have hne : 1 - sig2 t ≠ 0 := by linarith
          have h0 : s' - sig2 t = 0 := (div_eq_zero_iff.mp e2).resolve_right hne
          linarith
      · rcases hbranch s' hs' with ⟨hb, hEb⟩ | ⟨hb1, hb2, hEb⟩ | ⟨hb1, hEb⟩
        · linarith
        · linarith
        · have h' : pf35 t ((s - sig2 t) / (1 - sig2 t))
              = pf35 t ((s' - sig2 t) / (1 - sig2 t)) := by
            rw [← hEa, ← hEb]; exact heq
          have h2 := pf35_inj hu hv h'
          have hne : 1 - sig2 t ≠ 0 := by linarith
          have h3 : s = s' := by
            rw [div_eq_div_iff hne hne] at h2
            have := mul_right_cancel₀ hne h2
            linarith
          exact absurd h3 (ne_of_lt hlt')
    refine ⟨?_, ?_⟩
    · intro s hs s' hs' heq
      rcases le_total s s' with hle | hle
      · rcases lt_or_eq_of_le hle with hlti | heqi
        · exact absurd heq (hmain s hs s' hs' hlti)
        · exact heqi
      · rcases lt_or_eq_of_le hle with hlti | heqi
        · exact absurd heq.symm (hmain s' hs' s hs hlti)
        · exact heqi.symm
    · intro s hs heq
      rcases hbranch s hs with ⟨ha, hEa⟩ | ⟨ha1, ha2, hEa⟩ | ⟨ha1, hEa⟩
      · have h2 : pf1 t (s / sig1 t) = W1 := by rw [← hEa]; exact heq
        have h3 : pf1 t (s / sig1 t) = pf1 t 0 := by rw [h2]; simp [pf1]
        have h4 := pf1_inj t h3
        exact (div_eq_zero_iff.mp h4).resolve_right (ne_of_gt hpos1)
      · have h2 : pf2 t ((s - sig1 t) / (sig2 t - sig1 t)) = W1 := by rw [← hEa]; exact heq
        have hle := n2_pf2_le_one t (hpar2 s hs (le_of_lt ha1) ha2)
        have hW1 : n2 W1 = 4 := by simp only [W1, n2]; norm_num
        have := congrArg n2 h2
        rw [hW1] at this
        linarith
      · have h2 : pf35 t ((s - sig2 t) / (1 - sig2 t)) = W1 := by rw [← hEa]; exact heq
        have hle := n2_pf35_le_one t (hpar3 s hs (le_of_lt ha1))
        have hW1 : n2 W1 = 4 := by simp only [W1, n2]; norm_num
        have := congrArg n2 h2
        rw [hW1] at this
        linarith

end

end Work.Drive.EpsForm
