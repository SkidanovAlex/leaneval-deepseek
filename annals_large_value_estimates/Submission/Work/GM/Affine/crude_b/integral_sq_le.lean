import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup

/-!
# GM §9, the crude bound for `∫ J²` (region `b`)

The "crude" estimate for the affine sum
`J(u) = Σ_{|m₁| ∼ M₁} Σ_{m₂ ∼ M₂} Σ_{|m₃| ≤ K M₃} f((m₁ u + m₃)/m₂)`:

if `0 ≤ J ≤ P` pointwise and `f` is supported in `[1/C₀, C₀]`, then

`∫ J(u)² du ≤ 2 * ((2 C₀ M₂ + K M₃)/M₁) * P²`.

The point is purely geometric: every term of `J` can only be nonzero when
`u ∈ [-L, L]` with `L = (2 C₀ M₂ + K M₃)/M₁` (because some `(m₁ u + m₃)/m₂` lies in
`[1/C₀, C₀]`, whence `|m₁ u + m₃| ≤ C₀ m₂ ≤ 2 C₀ M₂` and `|m₃| ≤ K M₃`, so
`|u| ≤ (2 C₀ M₂ + K M₃)/|m₁| < L`).  Since `0 ≤ J ≤ P`, an integration over that interval
of length `2 L` gives the claim.
-/

open MeasureTheory

namespace Work.GM.Affine.crude_b

/-- Element bound for the `m₁`-range `R1`: `|m₁| > M₁`. -/
lemma lt_abs_of_mem_R1 {M₁ : ℝ} {m : ℤ} (hm : m ∈ R1 M₁) : M₁ < |(m : ℝ)| :=
  (Finset.mem_filter.mp hm).2

/-- Element bounds for the `m₂`-range `R2`: `0 < m₂` and `m₂ ≤ 2 M₂`. -/
lemma mem_R2_bounds {M₂ : ℝ} {m : ℤ} (hm : m ∈ R2 M₂) :
    0 < (m : ℝ) ∧ (m : ℝ) ≤ 2 * M₂ := by
  rw [R2, Finset.mem_filter] at hm
  obtain ⟨hmI, _⟩ := hm
  rw [Finset.mem_Icc] at hmI
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmI.1
  have h2 : ((⌊2 * M₂⌋ : ℤ) : ℝ) ≤ 2 * M₂ := Int.floor_le (2 * M₂)
  have h3 : ((m : ℤ) : ℝ) ≤ ((⌊2 * M₂⌋ : ℤ) : ℝ) := by exact_mod_cast hmI.2
  exact ⟨by linarith, by linarith⟩

/-- Element bound for the `m₃`-range `R3`: `|m₃| ≤ K M₃`. -/
lemma abs_le_of_mem_R3 {K M₃ : ℝ} (_hK : 0 < K) (_hM₃ : 0 < M₃) {m : ℤ}
    (hm : m ∈ R3 K M₃) : |(m : ℝ)| ≤ K * M₃ := by
  rw [R3, Finset.mem_Icc] at hm
  have hfloor : ((⌊K * M₃⌋ : ℤ) : ℝ) ≤ K * M₃ := Int.floor_le (K * M₃)
  have h1 : ((m : ℤ) : ℝ) ≤ K * M₃ := by
    have : ((m : ℤ) : ℝ) ≤ ((⌊K * M₃⌋ : ℤ) : ℝ) := by exact_mod_cast hm.2
    linarith
  have h2 : -(K * M₃) ≤ ((m : ℤ) : ℝ) := by
    have : (((-⌊K * M₃⌋ : ℤ)) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast hm.1
    push_cast at this
    linarith
  rw [abs_le]
  exact ⟨h2, h1⟩

/-- **Geometric core.**  If the term `f((m₁ u + m₃)/m₂)` is nonzero for indices in the
ranges `R1, R2, R3`, then `|u| < (2 C₀ M₂ + K M₃)/M₁`: the argument of `f` lies in
`[1/C₀, C₀]`, so `|m₁ u + m₃| ≤ C₀ m₂ ≤ 2 C₀ M₂`, while `|m₃| ≤ K M₃` and `|m₁| > M₁`. -/
lemma abs_lt_of_term_ne_zero {K C₀ M₁ M₂ M₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hsupp : SuppHyp C₀ f)
    {u : ℝ} {m₁ m₂ m₃ : ℤ} (hm₁ : m₁ ∈ R1 M₁) (hm₂ : m₂ ∈ R2 M₂) (hm₃ : m₃ ∈ R3 K M₃)
    (hf : f (((m₁ : ℝ) * u + m₃) / m₂) ≠ 0) :
    |u| < (2 * C₀ * M₂ + K * M₃) / M₁ := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hC₀inv : 0 < 1 / C₀ := one_div_pos.mpr hC₀pos
  have habs1 : M₁ < |(m₁ : ℝ)| := lt_abs_of_mem_R1 hm₁
  have hm₁abs : 0 < |(m₁ : ℝ)| := lt_trans hM₁ habs1
  obtain ⟨hm₂pos, hm₂le⟩ := mem_R2_bounds hm₂
  have hm₃le : |(m₃ : ℝ)| ≤ K * M₃ := abs_le_of_mem_R3 hK hM₃ hm₃
  set v : ℝ := ((m₁ : ℝ) * u + m₃) / m₂ with hv
  have hfv : f v ≠ 0 := by rw [hv]; exact hf
  have hvmem : v ∈ Set.Icc (1 / C₀) C₀ := hsupp v hfv
  have hvpos : 0 < v := lt_of_lt_of_le hC₀inv hvmem.1
  have hvabs : |v| ≤ C₀ := by rw [abs_of_pos hvpos]; exact hvmem.2
  have hm₂ne : (m₂ : ℝ) ≠ 0 := ne_of_gt hm₂pos
  have hprod : v * (m₂ : ℝ) = (m₁ : ℝ) * u + m₃ := by
    rw [hv]; exact div_mul_cancel₀ _ hm₂ne
  have hstep : |(m₁ : ℝ) * u + m₃| ≤ 2 * C₀ * M₂ := by
    rw [← hprod, abs_mul, abs_of_pos hm₂pos]
    have h1 : |v| * (m₂ : ℝ) ≤ C₀ * (m₂ : ℝ) :=
      mul_le_mul_of_nonneg_right hvabs (le_of_lt hm₂pos)
    have h2 : C₀ * (m₂ : ℝ) ≤ C₀ * (2 * M₂) :=
      mul_le_mul_of_nonneg_left hm₂le (le_of_lt hC₀pos)
    linarith
  have htri : |(m₁ : ℝ) * u| ≤ |(m₁ : ℝ) * u + m₃| + |(m₃ : ℝ)| := by
    have h := abs_sub_le ((m₁ : ℝ) * u + (m₃ : ℝ)) 0 (m₃ : ℝ)
    have e : ((m₁ : ℝ) * u + (m₃ : ℝ)) - (m₃ : ℝ) = (m₁ : ℝ) * u := by ring
    rw [e, sub_zero, zero_sub, abs_neg] at h
    exact h
  have h4 : |(m₁ : ℝ)| * |u| ≤ 2 * C₀ * M₂ + K * M₃ := by
    rw [abs_mul] at htri
    linarith
  have hBpos : 0 < 2 * C₀ * M₂ + K * M₃ := by
    have : 0 < 2 * C₀ * M₂ := by nlinarith
    nlinarith [mul_pos hK hM₃]
  have h5 : |u| ≤ (2 * C₀ * M₂ + K * M₃) / |(m₁ : ℝ)| := by
    rw [le_div_iff₀ hm₁abs]
    linarith
  have h6 : (2 * C₀ * M₂ + K * M₃) / |(m₁ : ℝ)| < (2 * C₀ * M₂ + K * M₃) / M₁ :=
    div_lt_div_of_pos_left hBpos hM₁ habs1
  linarith

/-- The affine sum vanishes off the interval `[-L, L]`, `L = (2 C₀ M₂ + K M₃)/M₁`. -/
lemma affineSum_eq_zero_of_notMem {K C₀ M₁ M₂ M₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hsupp : SuppHyp C₀ f)
    {u : ℝ}
    (hu : u ∉ Set.Icc (-((2 * C₀ * M₂ + K * M₃) / M₁)) ((2 * C₀ * M₂ + K * M₃) / M₁)) :
    Submission.GM.affineSum K M₁ M₂ M₃ f u = 0 := by
  rw [Work.GM.Affine.affineSum_eq]
  apply Finset.sum_eq_zero
  intro m₁ hm₁
  apply Finset.sum_eq_zero
  intro m₂ hm₂
  apply Finset.sum_eq_zero
  intro m₃ hm₃
  by_contra hf
  have habs := abs_lt_of_term_ne_zero hC₀ hK hM₁ hM₂ hM₃ hsupp hm₁ hm₂ hm₃ hf
  apply hu
  have h := abs_lt.mp habs
  rw [Set.mem_Icc]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The affine sum is nonnegative when `f` is. -/
lemma affineSum_nonneg {K M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u) (u : ℝ) :
    0 ≤ Submission.GM.affineSum K M₁ M₂ M₃ f u := by
  rw [Work.GM.Affine.affineSum_eq]
  exact Finset.sum_nonneg fun m₁ _ =>
    Finset.sum_nonneg fun m₂ _ => Finset.sum_nonneg fun m₃ _ => hnn _

theorem integral_sq_le {K C₀ M₁ M₂ M₃ P : ℝ} {f : ℝ → ℝ}
    (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hnn : ∀ u, 0 ≤ f u) (hsupp : SuppHyp C₀ f) (hP : 0 ≤ P)
    (hpt : ∀ u, Submission.GM.affineSum K M₁ M₂ M₃ f u ≤ P) :
    ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u)^2 ≤
      2 * ((2 * C₀ * M₂ + K * M₃) / M₁) * P^2 := by
  set L : ℝ := (2 * C₀ * M₂ + K * M₃) / M₁ with hL
  have hLpos : 0 < L := by
    rw [hL]
    exact div_pos (by nlinarith [le_of_lt hK, le_of_lt hM₃, hC₀, le_of_lt hM₂]) hM₁
  have hbound : ∀ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u)^2 ≤
      (Set.Icc (-L) L).indicator (fun _ => P ^ 2) u := by
    intro u
    by_cases hu : u ∈ Set.Icc (-L) L
    · rw [Set.indicator_of_mem hu]
      have h1 : Submission.GM.affineSum K M₁ M₂ M₃ f u ≤ P := hpt u
      have h2 : 0 ≤ Submission.GM.affineSum K M₁ M₂ M₃ f u := affineSum_nonneg hnn u
      have h3 : 0 ≤ (P - Submission.GM.affineSum K M₁ M₂ M₃ f u) *
          (P + Submission.GM.affineSum K M₁ M₂ M₃ f u) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [h3]
    · rw [Set.indicator_of_notMem hu]
      have h0 : Submission.GM.affineSum K M₁ M₂ M₃ f u = 0 := by
        apply affineSum_eq_zero_of_notMem hC₀ hK hM₁ hM₂ hM₃ hsupp
        rwa [hL] at hu
      rw [h0]
      norm_num
  have hInt : Integrable (fun u => (Set.Icc (-L) L).indicator (fun _ => P ^ 2) u) volume := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (s := Set.Icc (-L) L) (C := P ^ 2)
      (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hmono : ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u)^2 ≤
      ∫ u, (Set.Icc (-L) L).indicator (fun _ => P ^ 2) u :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) hInt
      (Filter.Eventually.of_forall hbound)
  have hval : ∫ u, (Set.Icc (-L) L).indicator (fun _ => P ^ 2) u = 2 * L * P ^ 2 := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    have hreal : volume.real (Set.Icc (-L) L) = 2 * L := by
      rw [MeasureTheory.Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hreal, smul_eq_mul]
  calc ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u)^2
      ≤ ∫ u, (Set.Icc (-L) L).indicator (fun _ => P ^ 2) u := hmono
    _ = 2 * L * P ^ 2 := hval

end Work.GM.Affine.crude_b
