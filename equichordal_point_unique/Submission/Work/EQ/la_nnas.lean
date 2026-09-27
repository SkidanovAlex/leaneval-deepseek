import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.axis_ratio_quarter
import Submission.Work.EQ.cpow_neg_half_near_one

set_option maxHeartbeats 1000000

/-! # `LaNnas`: collision-free copy of `no_near_axis_segment`

The file `Submission/Work/EQ/no_near_axis_segment.lean` defines a top-level lemma
`Work.EQ.norm_sub_le_add` which collides with the (differently stated) `Work.EQ.norm_sub_le_add`
of `Submission/Work/EQ/H0_section_local.lean`, making it impossible to import both
`no_near_axis_segment` and anything that transitively imports `H0_section_local` (in particular
`Work.EQ.H0_structure` and `Work.EQ.exists_regular_of_family`) in one file.  Since Rychlik's
Theorem 8 needs both the parity separation (`no_near_axis_segment`) and the analytic sections
(`H0_structure`), this file carries the same mathematical content in the namespace
`Work.EQ.LaNnas`, where no name collides with anything.  Nothing else is changed.
-/

namespace Work.EQ.LaNnas

open Complex

noncomputable section

/-! ## The two near-axis predicates -/

/-- `P` is *stable-near* an axis centre of the coset `-1/2 + 2ℤ` with radius `r`: its first
coordinate is within `r` of such a centre and `|y| ≤ r·|x - a/2|`. -/
def SnNear (a : ℝ) (P : ℂ × ℂ) (r : ℝ) : Prop :=
  ∃ Y : ℤ, ‖P.1 - (-1 / 2 + 2 * Y)‖ ≤ r ∧ ‖P.2‖ ≤ r * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖

/-- `P` is *unstable-near* an axis centre of the coset `1/2 + 2ℤ` with radius `r`: its first
coordinate is within `r` of such a centre and `|y| ≤ r·|x + a/2|`. -/
def UnNear (a : ℝ) (P : ℂ × ℂ) (r : ℝ) : Prop :=
  ∃ X : ℤ, ‖P.1 - (1 / 2 + 2 * X)‖ ≤ r ∧ ‖P.2‖ ≤ r * ‖P.1 + ((a / 2 : ℝ) : ℂ)‖

lemma SnNear.mono {a : ℝ} {P : ℂ × ℂ} {r r' : ℝ} (h : SnNear a P r) (h' : r ≤ r') :
    SnNear a P r' := by
  obtain ⟨Y, h1, h2⟩ := h
  exact ⟨Y, le_trans h1 h', le_trans h2 (mul_le_mul_of_nonneg_right h' (norm_nonneg _))⟩

lemma UnNear.mono {a : ℝ} {P : ℂ × ℂ} {r r' : ℝ} (h : UnNear a P r) (h' : r ≤ r') :
    UnNear a P r' := by
  obtain ⟨X, h1, h2⟩ := h
  exact ⟨X, le_trans h1 h', le_trans h2 (mul_le_mul_of_nonneg_right h' (norm_nonneg _))⟩

/-! ## The uniform constants -/

/-- The uniform constant `2/λ + 1` of the near-axis step estimates, `λ = (1-a)/(1+a)`. -/
def nnK (a : ℝ) : ℝ := 2 * ((1 + a) / (1 - a)) + 1

/-- The near-axis threshold `(1-a)/8`. -/
def nnD (a : ℝ) : ℝ := (1 - a) / 8

/-- The uniform growth factor of the near-axis radius in one step. -/
def nnC (a : ℝ) : ℝ := 1 + 2 * nnK a ^ 2 * nnD a

lemma nnD_pos {a : ℝ} (ha1 : a < 1) : 0 < nnD a := by
  rw [nnD]; linarith

lemma nnD_le_quarter {a : ℝ} (_ha0 : 0 < a) : nnD a ≤ 1 / 4 := by
  rw [nnD]; linarith

lemma nnK_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < nnK a := by
  have h : 0 < (1 + a) / (1 - a) := by positivity
  rw [nnK]; linarith

lemma nnK_ge_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 1 ≤ nnK a := by
  have h : 1 ≤ (1 + a) / (1 - a) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - a)]; linarith
  rw [nnK]; linarith

lemma nnC_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < nnC a := by
  have h := nnK_pos ha0 ha1
  have h2 := nnD_pos ha1
  rw [nnC]; nlinarith

lemma nnC_ge_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 1 ≤ nnC a := by
  have h := nnK_pos ha0 ha1
  have h2 := nnD_pos ha1
  rw [nnC]; nlinarith

/-- `nnK a · nnD a = (3+a)/8 ≤ 1/2`: the semi-projective ratio at a near-axis point of radius
`nnD a` is at most `1/2`. -/
lemma nnK_mul_nnD_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : nnK a * nnD a ≤ 1 / 2 := by
  have h1a : (0:ℝ) < 1 - a := by linarith
  have h : nnK a * nnD a = (3 + a) / 8 := by
    rw [nnK, nnD]; field_simp; ring
  rw [h]; linarith

lemma nnK_le_nnC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : nnK a ≤ nnC a := by
  have h1a : (0:ℝ) < 1 - a := by linarith
  have hK : nnK a = (3 + a) / (1 - a) := by rw [nnK]; field_simp; ring
  have hD : nnD a = (1 - a) / 8 := rfl
  rw [nnC, hK, hD]
  have h2 : 1 + 2 * ((3 + a) / (1 - a)) ^ 2 * ((1 - a) / 8)
      = 1 + (3 + a) ^ 2 / (4 * (1 - a)) := by
    field_simp; ring
  rw [h2, div_le_iff₀ h1a]
  have h3 : (1 + (3 + a) ^ 2 / (4 * (1 - a))) * (1 - a) = (1 - a) + (3 + a) ^ 2 / 4 := by
    field_simp
  rw [h3]
  nlinarith [sq_nonneg (1 - a)]

/-! ## Norms of real numbers -/

lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h1 : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rw [← Real.sqrt_sq (norm_nonneg (r : ℂ)), h1, Real.sqrt_sq_eq_abs]

lemma norm_sub_le_add (x y z : ℂ) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  have h := norm_add_le (x - y) (y - z)
  rwa [sub_add_sub_cancel] at h



/-! ## Axis bounds around a near-axis centre -/

/-- Every point of the coset `-1/2 + 2ℤ` has modulus at least `1/2`. -/
lemma abs_neg_half_add_two_mul (Y : ℤ) : (1 : ℝ) / 2 ≤ |-(1 : ℝ) / 2 + 2 * (Y : ℝ)| := by
  rcases le_or_gt (1 : ℤ) Y with hY | hY
  · have hY' : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hY' : (Y : ℝ) ≤ 0 := by
      have h : Y ≤ 0 := by omega
      exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **The axis bounds.** If `P` is within `r ≤ nnD a` of the axis centre `1/2 + 2X`, then its
distances to `± a/2` are both `≥ nnD a`, and they are comparable with the uniform constant
`nnK a`. (The coset `-1/2 + 2ℤ` is `1/2 + 2ℤ` shifted by `-1`, so this covers both cosets.) -/
lemma axis_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {P : ℂ × ℂ} {r x₀ : ℝ}
    (hr : r ≤ nnD a) (hx0 : (1 : ℝ) / 2 ≤ |x₀|) (hX : ‖P.1 - (x₀ : ℂ)‖ ≤ r) :
    nnD a ≤ ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ ∧ nnD a ≤ ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ ∧
      ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ ≤ nnK a * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ ∧
      ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ ≤ nnK a * ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by
  obtain ⟨h1', h2', h3', h4'⟩ := quarter_ratio_le_abs ha0 ha1 hx0
  have hcast' : (x₀ : ℂ) - ((a / 2 : ℝ) : ℂ) = ((x₀ - a / 2 : ℝ) : ℂ) := by push_cast; ring
  have hcast'' : (x₀ : ℂ) + ((a / 2 : ℝ) : ℂ) = ((x₀ + a / 2 : ℝ) : ℂ) := by push_cast; ring
  have hX' : ‖P.1 - (x₀ : ℂ)‖ ≤ r := hX
  have htb : ‖(x₀ : ℂ) - ((a / 2 : ℝ) : ℂ)‖ = |x₀ - a / 2| := by
    rw [hcast', norm_ofReal_eq_abs]
  have htb' : ‖(x₀ : ℂ) + ((a / 2 : ℝ) : ℂ)‖ = |x₀ + a / 2| := by
    rw [hcast'', norm_ofReal_eq_abs]
  have hD : nnD a = (1 - a) / 8 := rfl
  have htri1 : ‖(x₀ : ℂ) - ((a / 2 : ℝ) : ℂ)‖ ≤ r + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
    calc ‖(x₀ : ℂ) - ((a / 2 : ℝ) : ℂ)‖
        ≤ ‖(x₀ : ℂ) - P.1‖ + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
          have h := norm_add_le ((x₀ : ℂ) - P.1) (P.1 - ((a / 2 : ℝ) : ℂ))
          simpa [sub_add_sub_cancel] using h
      _ = ‖P.1 - (x₀ : ℂ)‖ + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
            rw [norm_sub_rev (x₀ : ℂ) P.1]
      _ ≤ r + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := add_le_add_left hX' _
  have htri2 : ‖(x₀ : ℂ) + ((a / 2 : ℝ) : ℂ)‖ ≤ r + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by
    calc ‖(x₀ : ℂ) + ((a / 2 : ℝ) : ℂ)‖
        ≤ ‖(x₀ : ℂ) - P.1‖ + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by
          have h := norm_add_le ((x₀ : ℂ) - P.1) (P.1 + ((a / 2 : ℝ) : ℂ))
          have h2 : (x₀ : ℂ) - P.1 + (P.1 + ((a / 2 : ℝ) : ℂ)) = (x₀ : ℂ) + ((a / 2 : ℝ) : ℂ) := by
            ring
          rwa [h2] at h
      _ = ‖P.1 - (x₀ : ℂ)‖ + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by
            rw [norm_sub_rev (x₀ : ℂ) P.1]
      _ ≤ r + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := add_le_add_left hX' _
  have hb1 : nnD a ≤ ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
    have h : (1 - a) / 2 - r ≤ ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
      have h2 := htri1
      rw [htb] at h2
      linarith [h3']
    rw [hD]; linarith
  have hb2 : nnD a ≤ ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by
    have h : (1 - a) / 2 - r ≤ ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by
      have h2 := htri2
      rw [htb'] at h2
      linarith [h4']
    rw [hD]; linarith
  have hK : nnK a = 2 * ((1 + a) / (1 - a)) + 1 := rfl
  have hratio : 0 ≤ (1 + a) / (1 - a) := by positivity
  have hrle : r ≤ ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := le_trans hr hb1
  have hrle' : r ≤ ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := le_trans hr hb2
  have htbA : ‖(x₀ : ℂ) - ((a / 2 : ℝ) : ℂ)‖ ≤ r + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
    calc ‖(x₀ : ℂ) - ((a / 2 : ℝ) : ℂ)‖
        = ‖(x₀ : ℂ) - P.1 + (P.1 - ((a / 2 : ℝ) : ℂ))‖ := by congr 1; ring
      _ ≤ ‖(x₀ : ℂ) - P.1‖ + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖P.1 - (x₀ : ℂ)‖ + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
            rw [norm_sub_rev (x₀ : ℂ) P.1]
      _ ≤ r + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := add_le_add_left hX' _
  have htbB : ‖(x₀ : ℂ) + ((a / 2 : ℝ) : ℂ)‖ ≤ r + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by
    calc ‖(x₀ : ℂ) + ((a / 2 : ℝ) : ℂ)‖
        = ‖(x₀ : ℂ) - P.1 + (P.1 + ((a / 2 : ℝ) : ℂ))‖ := by congr 1; ring
      _ ≤ ‖(x₀ : ℂ) - P.1‖ + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖P.1 - (x₀ : ℂ)‖ + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by
            rw [norm_sub_rev (x₀ : ℂ) P.1]
      _ ≤ r + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := add_le_add_left hX' _
  have htbA' : |x₀ - a / 2| ≤ r + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by rw [← htb]; exact htbA
  have htbB' : |x₀ + a / 2| ≤ r + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by rw [← htb']; exact htbB
  have htriA : ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ ≤ r + ‖(x₀ : ℂ) - ((a / 2 : ℝ) : ℂ)‖ := by
    calc ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ = ‖(P.1 - (x₀ : ℂ)) + ((x₀ : ℂ) - ((a / 2 : ℝ) : ℂ))‖ := by
          congr 1; ring
      _ ≤ ‖P.1 - (x₀ : ℂ)‖ + ‖(x₀ : ℂ) - ((a / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ r + ‖(x₀ : ℂ) - ((a / 2 : ℝ) : ℂ)‖ := add_le_add_left hX' _
  have htriB : ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ ≤ r + ‖(x₀ : ℂ) + ((a / 2 : ℝ) : ℂ)‖ := by
    calc ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ = ‖(P.1 - (x₀ : ℂ)) + ((x₀ : ℂ) + ((a / 2 : ℝ) : ℂ))‖ := by
          congr 1; ring
      _ ≤ ‖P.1 - (x₀ : ℂ)‖ + ‖(x₀ : ℂ) + ((a / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ r + ‖(x₀ : ℂ) + ((a / 2 : ℝ) : ℂ)‖ := add_le_add_left hX' _
  have hkeyA : ‖(x₀ : ℂ) + ((a / 2 : ℝ) : ℂ)‖
      ≤ ((1 + a) / (1 - a)) * (r + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖) := by
    rw [htb']
    calc |x₀ + a / 2| ≤ ((1 + a) / (1 - a)) * |x₀ - a / 2| := h1'
      _ ≤ ((1 + a) / (1 - a)) * (r + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left htbA' hratio
  have hkeyB : ‖(x₀ : ℂ) - ((a / 2 : ℝ) : ℂ)‖
      ≤ ((1 + a) / (1 - a)) * (r + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖) := by
    rw [htb]
    calc |x₀ - a / 2| ≤ ((1 + a) / (1 - a)) * |x₀ + a / 2| := h2'
      _ ≤ ((1 + a) / (1 - a)) * (r + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left htbB' hratio
  have hfinA : ((1 + a) / (1 - a)) * (r + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖) + r
      ≤ (2 * ((1 + a) / (1 - a)) + 1) * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
    have h1 : r + ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ ≤ 2 * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hratio
    linarith
  have hfinB : ((1 + a) / (1 - a)) * (r + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖) + r
      ≤ (2 * ((1 + a) / (1 - a)) + 1) * ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by
    have h1 : r + ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ ≤ 2 * ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hratio
    linarith
  refine ⟨hb1, hb2, ?_, ?_⟩
  · rw [hK]
    linarith [htriB, hkeyA, hfinA]
  · rw [hK]
    linarith [htriA, hkeyB, hfinB]

/-! ## Algebra of a regular step -/

lemma subO2_ne_zero {a : ℝ} {P : ℂ × ℂ} (h : bsq (subO2 a P) ≠ 0) : subO2 a P ≠ 0 := by
  intro h0; exact h (by rw [h0]; simp [bsq])

lemma subO1_ne_zero {a : ℝ} {Q : ℂ × ℂ} (h : bsq (subO1 a Q) ≠ 0) : subO1 a Q ≠ 0 := by
  intro h0; exact h (by rw [h0]; simp [bsq])

/-- **Forward branch form.** A regular pair determines `Q` from `P` up to the branch sign. -/
lemma fwd_decomp {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) (hP : bsq (subO2 a P) ≠ 0) :
    ∃ c : ℂ, c ^ 2 * bsq (subO2 a P) = 1 ∧ Q = -P + c • subO2 a P := by
  have hpar : par (P + Q) (subO2 a P) := by
    rw [par, subO2]
    simp only [Prod.fst_add, Prod.snd_add]
    linear_combination h.2
  obtain ⟨c, hc⟩ := exists_smul_of_par ((par_comm (X := subO2 a P) (Y := P + Q)).mpr hpar)
    (subO2_ne_zero hP)
  refine ⟨c, ?_, ?_⟩
  · have hbsq : bsq (P + Q) = c ^ 2 * bsq (subO2 a P) := by rw [hc, bsq_smul]
    have h2 : (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 = c ^ 2 * bsq (subO2 a P) := by
      have h := hbsq
      simp only [bsq, subO2, Prod.fst_add, Prod.snd_add] at h ⊢
      linear_combination h
    rw [← h2]; exact h.1
  · rw [← hc]; abel

/-- **Backward branch form.** A regular pair determines `P` from `Q` up to the branch sign. -/
lemma bwd_decomp {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) (hQ : bsq (subO1 a Q) ≠ 0) :
    ∃ c : ℂ, c ^ 2 * bsq (subO1 a Q) = 1 ∧ P = -Q + c • subO1 a Q := by
  obtain ⟨h1, h2⟩ := (eqRelC_iff_reverse P Q).mp h
  obtain ⟨c, hc⟩ := exists_smul_of_par ((par_comm (X := subO1 a Q) (Y := P + Q)).mpr h2)
    (subO1_ne_zero hQ)
  refine ⟨c, ?_, ?_⟩
  · have hbsq : bsq (P + Q) = c ^ 2 * bsq (subO1 a Q) := by rw [hc, bsq_smul]
    rw [← hbsq]; exact h1
  · rw [← hc]; abel

/-! ## The core estimate: `c·X` is `±1 + O(w²)` -/

/-- **The core near-axis estimate.** If `c²(X² + y²) = 1` with `X ≠ 0` and `w = y/X` of squared
modulus `≤ 1/2`, then `c·X` is within `2‖w‖²` of `1` or of `-1`.  This is the `x`-displacement
`x ↦ -x ± 1 + O(w²)` of one equichordal step in semi-projective terms. -/
lemma cpow_shift_core {X y c : ℂ} (hX : X ≠ 0) (hc : c ^ 2 * (X ^ 2 + y ^ 2) = 1)
    (hw : ‖y / X‖ ^ 2 ≤ 1 / 2) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ ‖c * X - σ‖ ≤ 2 * ‖y / X‖ ^ 2 := by
  set w : ℂ := y / X with hwdef
  have hyw : y = w * X := by rw [hwdef, div_mul_cancel₀ _ hX]
  have hwne : 1 + w ^ 2 ≠ 0 := by
    intro h
    have h2 : w ^ 2 = -1 := by linear_combination h
    have hnorm : ‖w‖ ^ 2 = 1 := by
      have := congrArg (norm : ℂ → ℝ) h2
      simpa [norm_neg, norm_one, norm_pow] using this
    nlinarith [hw, norm_nonneg w]
  have hbs : X ^ 2 + y ^ 2 = X ^ 2 * (1 + w ^ 2) := by rw [hyw]; ring
  have hmain : (c * X) ^ 2 * (1 + w ^ 2) = 1 := by
    have h := hc
    rw [hbs] at h
    linear_combination h
  have hcx2 : (c * X) ^ 2 = (1 + w ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact hmain)
  set R : ℂ := (1 + w ^ 2) ^ (-(1 / 2) : ℂ) with hR
  have hR2 : R ^ 2 = (1 + w ^ 2)⁻¹ := by
    rw [hR, sq]
    have hsum : (-(1 / 2) : ℂ) + (-(1 / 2) : ℂ) = -1 := by norm_num
    rw [← Complex.cpow_add (-(1 / 2)) (-(1 / 2)) hwne, hsum, Complex.cpow_neg_one]
  have hfac : (c * X - R) * (c * X + R) = 0 := by
    have h : (c * X) ^ 2 - R ^ 2 = 0 := by rw [hcx2, hR2]; ring
    linear_combination h
  have hw2 : ‖w ^ 2‖ ≤ 1 / 2 := by rw [norm_pow]; exact hw
  have hbound : ‖R - 1‖ ≤ 2 * ‖w ^ 2‖ := cpow_neg_half_near_one hw2
  rcases mul_eq_zero.mp hfac with hcase | hcase
  · refine ⟨1, Or.inl rfl, ?_⟩
    have hcx : c * X = R := by linear_combination hcase
    rw [hcx, ← norm_pow]
    exact hbound
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hcx : c * X = -R := by linear_combination hcase
    rw [hcx, show -R - -1 = -(R - 1) by ring, norm_neg, ← norm_pow]
    exact hbound


/-! ## One step of the propagation -/

/-- **Forward step.** A regular pair advances an unstable-near point to an unstable-near point
with radius multiplied by the uniform constant `nnC a`. -/
lemma step_fwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {P Q : ℂ × ℂ} {r : ℝ}
    (hreg : RegPair a P Q) (hr0 : 0 ≤ r) (hr : r ≤ nnD a) (hP : UnNear a P r) :
    UnNear a Q (nnC a * r) := by
  unfold RegPair at hreg
  obtain ⟨hrel, hPne, hQne⟩ := hreg
  have hPne' : bsq (subO2 a P) ≠ 0 := by simpa [bsq, subO2] using hPne
  obtain ⟨X, hX, hratio⟩ := hP
  have hx0 : (1 : ℝ) / 2 ≤ |(1 : ℝ) / 2 + 2 * (X : ℝ)| := abs_half_add_two_mul X
  have hX0 : ‖P.1 - ((((1 : ℝ) / 2 + 2 * (X : ℝ)) : ℝ) : ℂ)‖ ≤ r := by
    have hc : (1 / 2 + 2 * X : ℂ) = ((((1 : ℝ) / 2 + 2 * (X : ℝ)) : ℝ) : ℂ) := by
      push_cast; ring
    rwa [hc] at hX
  obtain ⟨hb1, hb2, hb3, hb4⟩ := axis_bounds ha0 ha1 hr hx0 hX0
  obtain ⟨c, hc1, hc2⟩ := fwd_decomp hrel hPne'
  have hQ1 : Q.1 = -P.1 + c * (P.1 - ((a / 2 : ℝ) : ℂ)) := by
    have := congrArg Prod.fst hc2
    simpa [Prod.fst_add, Prod.smul_fst, subO2, smul_eq_mul] using this
  have hQ2 : Q.2 = -P.2 + c * P.2 := by
    have := congrArg Prod.snd hc2
    simpa [Prod.snd_add, Prod.smul_snd, subO2, smul_eq_mul] using this
  have hc1' : c ^ 2 * ((P.1 - ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2) = 1 := by
    simpa [bsq, subO2] using hc1
  have hdp : 0 < nnD a := nnD_pos ha1
  have hXb : P.1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have := hb1
    rw [h0, norm_zero] at this
    linarith
  have hun : ‖P.2 / (P.1 - ((a / 2 : ℝ) : ℂ))‖ ≤ nnK a * r := by
    rw [norm_div]
    rw [div_le_iff₀ (lt_of_lt_of_le hdp hb1)]
    calc ‖P.2‖ ≤ r * ‖P.1 + ((a / 2 : ℝ) : ℂ)‖ := hratio
      _ ≤ r * (nnK a * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hb3 hr0
      _ = nnK a * r * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by ring
  have hu2 : ‖P.2 / (P.1 - ((a / 2 : ℝ) : ℂ))‖ ^ 2 ≤ 1 / 2 := by
    have h1 := hun
    have h2 : nnK a * r ≤ nnK a * nnD a := mul_le_mul_of_nonneg_left hr (le_of_lt (nnK_pos ha0 ha1))
    have h3 := nnK_mul_nnD_le ha0 ha1
    nlinarith [norm_nonneg (P.2 / (P.1 - ((a / 2 : ℝ) : ℂ)))]
  obtain ⟨σ, hσ, herr⟩ := cpow_shift_core hXb hc1' hu2
  have hKpos : 0 ≤ nnK a := le_of_lt (nnK_pos ha0 ha1)
  have herr1 : ‖Q.1 + P.1 - σ‖ ≤ 2 * ‖P.2 / (P.1 - ((a / 2 : ℝ) : ℂ))‖ ^ 2 := by
    have h : Q.1 + P.1 - σ = c * (P.1 - ((a / 2 : ℝ) : ℂ)) - σ := by rw [hQ1]; ring
    rw [h]
    exact herr
  have herr2 : ‖Q.1 + P.1 - σ‖ ≤ 2 * (nnK a * r) ^ 2 := by
    refine le_trans herr1 ?_
    have := hun
    nlinarith [norm_nonneg (P.2 / (P.1 - ((a / 2 : ℝ) : ℂ))), hKpos, hr0]
  have hstep : 2 * (nnK a * r) ^ 2 ≤ 2 * (nnK a) ^ 2 * nnD a * r := by
    have hrr : r * r ≤ nnD a * r := mul_le_mul_of_nonneg_right hr hr0
    have h2 : 0 ≤ 2 * (nnK a) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hrr h2
    nlinarith [this]
  have hCeq : r + 2 * (nnK a) ^ 2 * nnD a * r = nnC a * r := by rw [nnC]; ring
  -- the ratio bound at `Q`
  have hratQ : ‖Q.2‖ ≤ (nnC a * r) * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ := by
    have hQ1b : Q.1 + ((a / 2 : ℝ) : ℂ) = (c - 1) * (P.1 - ((a / 2 : ℝ) : ℂ)) := by
      rw [hQ1]; ring
    have hQ2' : Q.2 = (c - 1) * P.2 := by rw [hQ2]; ring
    calc ‖Q.2‖ = ‖c - 1‖ * ‖P.2‖ := by rw [hQ2', norm_mul]
      _ ≤ ‖c - 1‖ * (r * ‖P.1 + ((a / 2 : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
      _ ≤ ‖c - 1‖ * (r * (nnK a * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb3 hr0) (norm_nonneg _)
      _ = (nnK a * r) * ‖(c - 1) * (P.1 - ((a / 2 : ℝ) : ℂ))‖ := by
          rw [norm_mul]; ring
      _ = (nnK a * r) * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ := by rw [hQ1b]
      _ ≤ (nnC a * r) * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (nnK_le_nnC ha0 ha1) hr0)
            (norm_nonneg _)
  rcases hσ with hσ | hσ
  · subst hσ
    refine ⟨-X, ?_, hratQ⟩
    have hcenter : (1 / 2 + 2 * ((-X : ℤ) : ℂ) : ℂ) = -((1 / 2 + 2 * X : ℂ)) + 1 := by
      push_cast; ring
    have hle : ‖Q.1 - (1 / 2 + 2 * ((-X : ℤ) : ℂ))‖ ≤ r + 2 * (nnK a * r) ^ 2 := by
      rw [hcenter]
      calc ‖Q.1 - (-((1 / 2 + 2 * X : ℂ)) + 1)‖
          = ‖(Q.1 + P.1 - 1) - (P.1 - (1 / 2 + 2 * X))‖ := by congr 1; ring
        _ ≤ ‖Q.1 + P.1 - 1‖ + ‖P.1 - (1 / 2 + 2 * X)‖ := norm_sub_le _ _
        _ ≤ r + 2 * (nnK a * r) ^ 2 := by linarith [herr2, hX]
    calc ‖Q.1 - (1 / 2 + 2 * ((-X : ℤ) : ℂ))‖ ≤ r + 2 * (nnK a * r) ^ 2 := hle
      _ ≤ r + 2 * (nnK a) ^ 2 * nnD a * r := by linarith [hstep]
      _ = nnC a * r := hCeq
  · subst hσ
    refine ⟨-1 - X, ?_, hratQ⟩
    have hcenter : (1 / 2 + 2 * ((-1 - X : ℤ) : ℂ) : ℂ) = -((1 / 2 + 2 * X : ℂ)) - 1 := by
      push_cast; ring
    have hle : ‖Q.1 - (1 / 2 + 2 * ((-1 - X : ℤ) : ℂ))‖ ≤ r + 2 * (nnK a * r) ^ 2 := by
      rw [hcenter]
      have h1 : Q.1 + P.1 + 1 = Q.1 + P.1 - -1 := by ring
      calc ‖Q.1 - (-((1 / 2 + 2 * X : ℂ)) - 1)‖
          = ‖(Q.1 + P.1 + 1) - (P.1 - (1 / 2 + 2 * X))‖ := by congr 1; ring
        _ ≤ ‖Q.1 + P.1 + 1‖ + ‖P.1 - (1 / 2 + 2 * X)‖ := norm_sub_le _ _
        _ ≤ r + 2 * (nnK a * r) ^ 2 := by
            rw [h1]; linarith [herr2, hX]
    calc ‖Q.1 - (1 / 2 + 2 * ((-1 - X : ℤ) : ℂ))‖ ≤ r + 2 * (nnK a * r) ^ 2 := hle
      _ ≤ r + 2 * (nnK a) ^ 2 * nnD a * r := by linarith [hstep]
      _ = nnC a * r := hCeq

/-- **Backward step.** A regular pair pulls a stable-near point back to a stable-near point with
radius multiplied by the uniform constant `nnC a`. -/
lemma step_bwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {P Q : ℂ × ℂ} {r : ℝ}
    (hreg : RegPair a P Q) (hr0 : 0 ≤ r) (hr : r ≤ nnD a) (hQ : SnNear a Q r) :
    SnNear a P (nnC a * r) := by
  unfold RegPair at hreg
  obtain ⟨hrel, hPne, hQne⟩ := hreg
  have hQne' : bsq (subO1 a Q) ≠ 0 := by simpa [bsq, subO1] using hQne
  obtain ⟨Y, hY, hratio⟩ := hQ
  have hx0 : (1 : ℝ) / 2 ≤ |-(1 : ℝ) / 2 + 2 * (Y : ℝ)| := abs_neg_half_add_two_mul Y
  have hY0 : ‖Q.1 - (((-(1 : ℝ) / 2 + 2 * (Y : ℝ)) : ℝ) : ℂ)‖ ≤ r := by
    have hc : (-1 / 2 + 2 * Y : ℂ) = (((-(1 : ℝ) / 2 + 2 * (Y : ℝ)) : ℝ) : ℂ) := by
      push_cast; ring
    rwa [hc] at hY
  obtain ⟨hb1, hb2, hb3, hb4⟩ := axis_bounds ha0 ha1 hr hx0 hY0
  obtain ⟨c, hc1, hc2⟩ := bwd_decomp hrel hQne'
  have hP1 : P.1 = -Q.1 + c * (Q.1 + ((a / 2 : ℝ) : ℂ)) := by
    have := congrArg Prod.fst hc2
    simpa [Prod.fst_add, Prod.smul_fst, subO1, smul_eq_mul] using this
  have hP2 : P.2 = -Q.2 + c * Q.2 := by
    have := congrArg Prod.snd hc2
    simpa [Prod.snd_add, Prod.smul_snd, subO1, smul_eq_mul] using this
  have hc1' : c ^ 2 * ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) = 1 := by
    simpa [bsq, subO1] using hc1
  have hdp : 0 < nnD a := nnD_pos ha1
  have hXb : Q.1 + ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have := hb2
    rw [h0, norm_zero] at this
    linarith
  have hun : ‖Q.2 / (Q.1 + ((a / 2 : ℝ) : ℂ))‖ ≤ nnK a * r := by
    rw [norm_div]
    rw [div_le_iff₀ (lt_of_lt_of_le hdp hb2)]
    calc ‖Q.2‖ ≤ r * ‖Q.1 - ((a / 2 : ℝ) : ℂ)‖ := hratio
      _ ≤ r * (nnK a * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hb4 hr0
      _ = nnK a * r * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ := by ring
  have hu2 : ‖Q.2 / (Q.1 + ((a / 2 : ℝ) : ℂ))‖ ^ 2 ≤ 1 / 2 := by
    have h1 := hun
    have h2 : nnK a * r ≤ nnK a * nnD a := mul_le_mul_of_nonneg_left hr (le_of_lt (nnK_pos ha0 ha1))
    have h3 := nnK_mul_nnD_le ha0 ha1
    nlinarith [norm_nonneg (Q.2 / (Q.1 + ((a / 2 : ℝ) : ℂ)))]
  obtain ⟨σ, hσ, herr⟩ := cpow_shift_core hXb hc1' hu2
  have hKpos : 0 ≤ nnK a := le_of_lt (nnK_pos ha0 ha1)
  have herr1 : ‖P.1 + Q.1 - σ‖ ≤ 2 * ‖Q.2 / (Q.1 + ((a / 2 : ℝ) : ℂ))‖ ^ 2 := by
    have h : P.1 + Q.1 - σ = c * (Q.1 + ((a / 2 : ℝ) : ℂ)) - σ := by rw [hP1]; ring
    rw [h]
    exact herr
  have herr2 : ‖P.1 + Q.1 - σ‖ ≤ 2 * (nnK a * r) ^ 2 := by
    refine le_trans herr1 ?_
    have := hun
    nlinarith [norm_nonneg (Q.2 / (Q.1 + ((a / 2 : ℝ) : ℂ))), hKpos, hr0]
  have hstep : 2 * (nnK a * r) ^ 2 ≤ 2 * (nnK a) ^ 2 * nnD a * r := by
    have hrr : r * r ≤ nnD a * r := mul_le_mul_of_nonneg_right hr hr0
    have h2 : 0 ≤ 2 * (nnK a) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hrr h2
    nlinarith [this]
  have hCeq : r + 2 * (nnK a) ^ 2 * nnD a * r = nnC a * r := by rw [nnC]; ring
  have hratP : ‖P.2‖ ≤ (nnC a * r) * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
    have hP1b : P.1 - ((a / 2 : ℝ) : ℂ) = (c - 1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) := by
      rw [hP1]; ring
    have hP2' : P.2 = (c - 1) * Q.2 := by rw [hP2]; ring
    calc ‖P.2‖ = ‖c - 1‖ * ‖Q.2‖ := by rw [hP2', norm_mul]
      _ ≤ ‖c - 1‖ * (r * ‖Q.1 - ((a / 2 : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
      _ ≤ ‖c - 1‖ * (r * (nnK a * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb4 hr0) (norm_nonneg _)
      _ = (nnK a * r) * ‖(c - 1) * (Q.1 + ((a / 2 : ℝ) : ℂ))‖ := by
          rw [norm_mul]; ring
      _ = (nnK a * r) * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by rw [hP1b]
      _ ≤ (nnC a * r) * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (nnK_le_nnC ha0 ha1) hr0)
            (norm_nonneg _)
  rcases hσ with hσ | hσ
  · subst hσ
    refine ⟨1 - Y, ?_, hratP⟩
    have hcenter : (-1 / 2 + 2 * ((1 - Y : ℤ) : ℂ) : ℂ) = -(-1 / 2 + 2 * Y : ℂ) + 1 := by
      push_cast; ring
    have hle : ‖P.1 - (-1 / 2 + 2 * ((1 - Y : ℤ) : ℂ))‖ ≤ r + 2 * (nnK a * r) ^ 2 := by
      rw [hcenter]
      calc ‖P.1 - (-(-1 / 2 + 2 * Y : ℂ) + 1)‖
          ≤ ‖P.1 - (-Q.1 + 1)‖ + ‖(-Q.1 + 1) - (-(-1 / 2 + 2 * Y : ℂ) + 1)‖ :=
            norm_sub_le_add _ _ _
        _ = ‖P.1 + Q.1 - 1‖ + ‖Q.1 - (-1 / 2 + 2 * Y)‖ := by
            have h1 : P.1 - (-Q.1 + 1) = P.1 + Q.1 - 1 := by ring
            have h2 : (-Q.1 + 1) - (-(-1 / 2 + 2 * Y : ℂ) + 1)
                = -(Q.1 - (-1 / 2 + 2 * Y : ℂ)) := by ring
            rw [h1, h2, norm_neg]
        _ ≤ r + 2 * (nnK a * r) ^ 2 := by linarith [herr2, hY]
    calc ‖P.1 - (-1 / 2 + 2 * ((1 - Y : ℤ) : ℂ))‖ ≤ r + 2 * (nnK a * r) ^ 2 := hle
      _ ≤ r + 2 * (nnK a) ^ 2 * nnD a * r := by linarith [hstep]
      _ = nnC a * r := hCeq
  · subst hσ
    refine ⟨-Y, ?_, hratP⟩
    have hcenter : (-1 / 2 + 2 * ((-Y : ℤ) : ℂ) : ℂ) = -(-1 / 2 + 2 * Y : ℂ) - 1 := by
      push_cast; ring
    have hle : ‖P.1 - (-1 / 2 + 2 * ((-Y : ℤ) : ℂ))‖ ≤ r + 2 * (nnK a * r) ^ 2 := by
      rw [hcenter]
      have h1 : P.1 + Q.1 + 1 = P.1 + Q.1 - -1 := by ring
      calc ‖P.1 - (-(-1 / 2 + 2 * Y : ℂ) - 1)‖
          ≤ ‖P.1 - (-Q.1 - 1)‖ + ‖(-Q.1 - 1) - (-(-1 / 2 + 2 * Y : ℂ) - 1)‖ :=
            norm_sub_le_add _ _ _
        _ = ‖P.1 + Q.1 + 1‖ + ‖Q.1 - (-1 / 2 + 2 * Y)‖ := by
            have h1 : P.1 - (-Q.1 - 1) = P.1 + Q.1 + 1 := by ring
            have h2 : (-Q.1 - 1) - (-(-1 / 2 + 2 * Y : ℂ) - 1)
                = -(Q.1 - (-1 / 2 + 2 * Y : ℂ)) := by ring
            rw [h1, h2, norm_neg]
        _ ≤ r + 2 * (nnK a * r) ^ 2 := by rw [h1]; linarith [herr2, hY]
    calc ‖P.1 - (-1 / 2 + 2 * ((-Y : ℤ) : ℂ))‖ ≤ r + 2 * (nnK a * r) ^ 2 := hle
      _ ≤ r + 2 * (nnK a) ^ 2 * nnD a * r := by linarith [hstep]
      _ = nnC a * r := hCeq

/-! ## Propagation over `N` steps -/

/-- **Forward propagation.** If the whole chain of radii stays below `nnD a`, then an `UnNear`
point at index `0` gives an `UnNear` point at index `N` with radius multiplied by `nnC a ^ N`. -/
lemma propagate_fwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ (N : ℕ) (P : ℕ → ℂ × ℂ) (η : ℝ), (∀ j < N, RegPair a (P j) (P (j + 1))) →
      0 ≤ η → (∀ n ≤ N, η * nnC a ^ n ≤ nnD a) → UnNear a (P 0) η →
      UnNear a (P N) (η * nnC a ^ N) := by
  intro N
  induction N with
  | zero => intro P η _ _ _ h0; simpa using h0
  | succ N ih =>
      intro P η hreg hη0 hη h0
      have hreg' : ∀ j < N, RegPair a (P j) (P (j + 1)) := fun j hj => hreg j (by omega)
      have hη' : ∀ n ≤ N, η * nnC a ^ n ≤ nnD a := fun n hn => hη n (by omega)
      have hPN : UnNear a (P N) (η * nnC a ^ N) := ih P η hreg' hη0 hη' h0
      have hr : η * nnC a ^ N ≤ nnD a := hη N (by omega)
      have hr0 : 0 ≤ η * nnC a ^ N :=
        mul_nonneg hη0 (pow_nonneg (le_of_lt (nnC_pos ha0 ha1)) N)
      have hstep := step_fwd (P := P N) (Q := P (N + 1)) (r := η * nnC a ^ N)
        ha0 ha1 (hreg N (by omega)) hr0 hr hPN
      have heq : nnC a * (η * nnC a ^ N) = η * nnC a ^ (N + 1) := by rw [pow_succ]; ring
      rwa [heq] at hstep

/-- **Backward propagation.** Dually, an `SnNear` point at index `N` pulls the condition back to
index `0` with radius multiplied by `nnC a ^ N`. -/
lemma propagate_bwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ (N : ℕ) (P : ℕ → ℂ × ℂ) (η : ℝ), (∀ j < N, RegPair a (P j) (P (j + 1))) →
      0 ≤ η → (∀ n ≤ N, η * nnC a ^ n ≤ nnD a) → SnNear a (P N) η →
      SnNear a (P 0) (η * nnC a ^ N) := by
  intro N
  induction N with
  | zero => intro P η _ _ _ hN; simpa using hN
  | succ N ih =>
      intro P η hreg hη0 hη hN
      have hreg' : ∀ j < N, RegPair a (P j) (P (j + 1)) := fun j hj => hreg j (by omega)
      have hr : η ≤ nnD a := by simpa using hη 0 (Nat.zero_le _)
      have hstep := step_bwd (P := P N) (Q := P (N + 1)) (r := η)
        ha0 ha1 (hreg N (by omega)) hη0 hr hN
      have hη' : ∀ n ≤ N, (nnC a * η) * nnC a ^ n ≤ nnD a := by
        intro n hn
        have h := hη (n + 1) (by omega)
        have heq : (nnC a * η) * nnC a ^ n = η * nnC a ^ (n + 1) := by rw [pow_succ]; ring
        rwa [heq]
      have hη0' : 0 ≤ nnC a * η := mul_nonneg (le_of_lt (nnC_pos ha0 ha1)) hη0
      have hres := ih P (nnC a * η) hreg' hη0' hη' hstep
      have heq : (nnC a * η) * nnC a ^ N = η * nnC a ^ (N + 1) := by rw [pow_succ]; ring
      rwa [heq] at hres

/-! ## Separation of the two cosets -/

/-- A point cannot be simultaneously close (in the `x`-coordinate, with total radius `< 1`) to a
centre of each of the two cosets `±1/2 + 2ℤ`: the distance between the cosets is `1`. -/
lemma not_un_and_sn {a : ℝ} {P : ℂ × ℂ} {r s : ℝ} (hrs : r + s < 1)
    (h1 : UnNear a P r) (h2 : SnNear a P s) : False := by
  obtain ⟨X, hX, -⟩ := h1
  obtain ⟨Y, hY, -⟩ := h2
  have htri : ‖(-1 / 2 + 2 * Y : ℂ) - (1 / 2 + 2 * X)‖ ≤ r + s := by
    calc ‖(-1 / 2 + 2 * Y : ℂ) - (1 / 2 + 2 * X)‖
        ≤ ‖(-1 / 2 + 2 * Y : ℂ) - P.1‖ + ‖P.1 - (1 / 2 + 2 * X)‖ := norm_sub_le_add _ _ _
      _ = ‖P.1 - (-1 / 2 + 2 * Y)‖ + ‖P.1 - (1 / 2 + 2 * X)‖ := by
            rw [norm_sub_rev ((-1 / 2 + 2 * Y : ℂ)) P.1]
      _ ≤ r + s := by linarith
  have hval : (-1 / 2 + 2 * Y : ℂ) - (1 / 2 + 2 * X)
      = ((((2 * (Y - X) - 1 : ℤ)) : ℝ) : ℂ) := by push_cast; ring
  have hge : (1 : ℝ) ≤ ‖(-1 / 2 + 2 * Y : ℂ) - (1 / 2 + 2 * X)‖ := by
    rw [hval, norm_ofReal_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (by omega : 2 * (Y - X) - 1 ≠ 0)
  linarith

/-! ## The target -/

/-- **Parity separation survives a bounded segment (closes the shrinking-fan case of Rychlik
Thms 8, 11).** A chain segment of `N` regular steps cannot join a point very near a stable
axis centre (`-1/2 + 2ℤ`, measured with `w = y/(x - a/2)`) to a point `1/4`-near an unstable
centre (`1/2 + 2ℤ`, measured with `y/(x + a/2)`), nor the reverse. -/
theorem no_near_axis_segment {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (P : ℕ → ℂ × ℂ), (∀ j < N, RegPair a (P j) (P (j + 1))) →
      ∀ X Y : ℤ,
        ¬ ((‖(P 0).1 - (1 / 2 + 2 * X)‖ ≤ 1 / 4 ∧
              ‖(P 0).2‖ ≤ ‖(P 0).1 + ((a / 2 : ℝ) : ℂ)‖ / 4) ∧
            ‖(P N).1 - (-1 / 2 + 2 * Y)‖ ≤ η ∧
              ‖(P N).2‖ ≤ η * ‖(P N).1 - ((a / 2 : ℝ) : ℂ)‖) ∧
        ¬ ((‖(P 0).1 - (1 / 2 + 2 * X)‖ ≤ η ∧
              ‖(P 0).2‖ ≤ η * ‖(P 0).1 + ((a / 2 : ℝ) : ℂ)‖) ∧
            ‖(P N).1 - (-1 / 2 + 2 * Y)‖ ≤ 1 / 4 ∧
              ‖(P N).2‖ ≤ ‖(P N).1 - ((a / 2 : ℝ) : ℂ)‖ / 4) := by
  have hC1 : 1 ≤ nnC a := nnC_ge_one ha0 ha1
  have hCpos : 0 < nnC a := nnC_pos ha0 ha1
  have hDpos : 0 < nnD a := nnD_pos ha1
  have hDq : nnD a ≤ 1 / 4 := nnD_le_quarter ha0
  refine ⟨nnD a / nnC a ^ N, div_pos hDpos (pow_pos hCpos N), ?_⟩
  intro P hreg X Y
  have hη0 : 0 ≤ nnD a / nnC a ^ N := le_of_lt (div_pos hDpos (pow_pos hCpos N))
  have hrng : ∀ n ≤ N, (nnD a / nnC a ^ N) * nnC a ^ n ≤ nnD a := by
    intro n hn
    have hpow : nnC a ^ n ≤ nnC a ^ N := pow_le_pow_right₀ hC1 hn
    have hpos : 0 < nnC a ^ N := pow_pos hCpos N
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left hpow (le_of_lt hDpos)
  have hval : (nnD a / nnC a ^ N) * nnC a ^ N = nnD a := by
    rw [div_mul_cancel₀]
    exact pow_ne_zero N (ne_of_gt hCpos)
  constructor
  · rintro ⟨⟨h0x, h0y⟩, hNx, hNy⟩
    have h0 : UnNear a (P 0) (1 / 4) := by
      refine ⟨X, h0x, ?_⟩
      have hdiv : ‖(P 0).1 + ((a / 2 : ℝ) : ℂ)‖ / 4
          = (1 / 4) * ‖(P 0).1 + ((a / 2 : ℝ) : ℂ)‖ := by ring
      rwa [hdiv] at h0y
    have hN : SnNear a (P N) (nnD a / nnC a ^ N) := ⟨Y, hNx, hNy⟩
    have := propagate_bwd ha0 ha1 N P (nnD a / nnC a ^ N) hreg hη0 hrng hN
    rw [hval] at this
    exact not_un_and_sn (by linarith) h0 this
  · rintro ⟨⟨h0x, h0y⟩, hNx, hNy⟩
    have h0 : UnNear a (P 0) (nnD a / nnC a ^ N) := ⟨X, h0x, h0y⟩
    have hN : SnNear a (P N) (1 / 4) := by
      refine ⟨Y, hNx, ?_⟩
      have hdiv : ‖(P N).1 - ((a / 2 : ℝ) : ℂ)‖ / 4
          = (1 / 4) * ‖(P N).1 - ((a / 2 : ℝ) : ℂ)‖ := by ring
      rwa [hdiv] at hNy
    have := propagate_fwd ha0 ha1 N P (nnD a / nnC a ^ N) hreg hη0 hrng h0
    rw [hval] at this
    exact not_un_and_sn (by linarith) this hN

end

end Work.EQ.LaNnas

