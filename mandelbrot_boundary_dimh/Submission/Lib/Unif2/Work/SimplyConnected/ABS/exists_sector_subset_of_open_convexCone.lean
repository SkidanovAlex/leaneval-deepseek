import Mathlib

namespace Work.SimplyConnected.ABS

noncomputable section

/-!
# A non-empty open convex cone in `ℂ` contains a sector

The proof is elementary and two-dimensional.  Write `crossL p : ℂ →L[ℝ] ℝ` for the real-linear
functional `z ↦ p.re * z.im - p.im * z.re` (the cross product with `p`).  If `p, q` are vectors
with `crossL p q > 0` (i.e. `q` is counter-clockwise from `p` by an angle in `(0, π)`), then

  `{z | 0 < crossL p z ∧ 0 < crossL q z}`  is precisely the open cone `{a • p + b • q | a, b > 0}`.

Indeed, writing `z = a • p + b • q` (possible because `p, q` are linearly independent) one has
`crossL p z = b * crossL p q` and `crossL q z = -a * crossL p q`, and conversely a positive
combination of two points of `C` lies in `C` because `C` is a convex cone.

So it suffices to produce two points `p, q ∈ C` with `crossL p q > 0`: take any non-zero `w ∈ C`
and rotate it infinitesimally, `q = w + δ • (I * w)`, which still lies in `C` by openness.
-/

/-- The real-linear functional `z ↦ p.re * z.im - p.im * z.re` (the cross product with `p`). -/
private noncomputable def crossL (p : ℂ) : ℂ →L[ℝ] ℝ :=
  p.re • Complex.imCLM - p.im • Complex.reCLM

private lemma crossL_apply (p q : ℂ) : crossL p q = p.re * q.im - p.im * q.re := by
  simp [crossL]

private lemma crossL_self (p : ℂ) : crossL p p = 0 := by
  rw [crossL_apply]; ring

private lemma crossL_swap (p q : ℂ) : crossL q p = -crossL p q := by
  rw [crossL_apply, crossL_apply]; ring

private lemma crossL_I_mul_self (p : ℂ) : crossL p (Complex.I * p) = Complex.normSq p := by
  rw [crossL_apply]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

private lemma crossL_ne_zero {p : ℂ} (hp : p ≠ 0) : crossL p ≠ 0 := by
  intro h
  have h1 : crossL p (Complex.I * p) = 0 := by rw [h]; simp
  rw [crossL_I_mul_self] at h1
  exact hp (Complex.normSq_eq_zero.mp h1)

/-- Two non-zero vectors of `ℂ` are proportional as soon as their cross product vanishes. -/
private lemma exists_smul_of_crossL_eq_zero {p x : ℂ} (hp : p ≠ 0) (h : crossL p x = 0) :
    ∃ s : ℝ, x = s • p := by
  rw [crossL_apply] at h
  rcases eq_or_ne p.re 0 with hre | hre
  · have him : p.im ≠ 0 := by
      intro him
      exact hp (Complex.ext (by simpa using hre) (by simpa using him))
    refine ⟨x.im / p.im, ?_⟩
    have hxre : x.re = 0 := by
      rw [hre, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left him
    apply Complex.ext
    · simp [Complex.real_smul, hxre, hre]
    · simp [Complex.real_smul, him]
  · refine ⟨x.re / p.re, ?_⟩
    apply Complex.ext
    · simp [Complex.real_smul, hre]
    · rw [Complex.real_smul, Complex.im_ofReal_mul]
      have hh : p.re * x.im = p.im * x.re := by linarith [h]
      field_simp
      linarith [hh]

/-- **A nonempty open convex cone in `ℂ` contains a sector.**  If `C ⊆ ℂ` is open, convex, closed
under positive scalings and nonempty, then there are non-zero real-linear functionals `L₁ L₂` whose
nonempty sector `{w | 0 < L₁ w ∧ 0 < L₂ w}` is contained in `C`. -/
theorem exists_sector_subset_of_open_convexCone (C : Set ℂ) (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    (hCcone : ∀ w ∈ C, ∀ t : ℝ, 0 < t → t • w ∈ C) (hCne : C.Nonempty) :
    ∃ L₁ L₂ : ℂ →L[ℝ] ℝ, L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ w : ℂ, 0 < L₁ w → 0 < L₂ w → w ∈ C := by
  -- A non-zero point of `C`.
  have hex : ∃ w ∈ C, w ≠ 0 := by
    obtain ⟨w, hw⟩ := hCne
    by_cases hw0 : w = 0
    · subst hw0
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCopen 0 hw
      refine ⟨((ε / 2 : ℝ) : ℂ), hball ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        linarith
      · rw [ne_eq, Complex.ofReal_eq_zero]; linarith
    · exact ⟨w, hw, hw0⟩
  obtain ⟨w, hwC, hwne⟩ := hex
  -- `C` is closed under addition (convex + closed under positive scalings).
  have hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C := by
    intro x hx y hy
    have h1 : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ C :=
      hCconv hx hy (by norm_num) (by norm_num) (by norm_num)
    have h2 := hCcone _ h1 2 (by norm_num)
    convert h2 using 1
    simp [Complex.real_smul]
  -- A second point of `C`, infinitesimally rotated from `w`.
  obtain ⟨ρ, hρ, hballρ⟩ := Metric.isOpen_iff.mp hCopen w hwC
  set δ : ℝ := ρ / (2 * (‖w‖ + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  set p : ℂ := w with hpdef
  set q : ℂ := w + δ • (Complex.I * w) with hqdef
  have hp_mem : p ∈ C := by rw [hpdef]; exact hwC
  have hq_mem : q ∈ C := by
    rw [hqdef, hpdef] at *
    apply hballρ
    rw [Metric.mem_ball, dist_eq_norm]
    have hqw : (w + δ • (Complex.I * w)) - w = δ • (Complex.I * w) := by ring
    rw [hqw, norm_smul, norm_mul, Complex.norm_I, one_mul,
      Real.norm_of_nonneg hδpos.le, hδdef]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖w‖ + 1))]
    nlinarith [hρ, norm_nonneg w]
  have hpne : p ≠ 0 := by rw [hpdef]; exact hwne
  have hpq : 0 < crossL p q := by
    have h1 : crossL p q = crossL p p + δ * crossL p (Complex.I * p) := by
      rw [hqdef]
      simp only [map_add, map_smul, smul_eq_mul]
      rw [hpdef]
    rw [h1, crossL_self, zero_add, crossL_I_mul_self]
    exact mul_pos hδpos (Complex.normSq_pos.mpr hpne)
  have hqne : q ≠ 0 := by
    intro h
    rw [h, map_zero] at hpq
    exact lt_irrefl 0 hpq
  refine ⟨crossL p, -crossL q, crossL_ne_zero hpne, neg_ne_zero.mpr (crossL_ne_zero hqne),
    ⟨p + q, ?_, ?_⟩, ?_⟩
  · -- the sector is non-empty: `p + q` lies in it
    have h : crossL p (p + q) = crossL p q := by
      rw [map_add, crossL_self, zero_add]
    rw [h]; exact hpq
  · have h : crossL q (p + q) = crossL q p := by rw [map_add, crossL_self, add_zero]
    rw [neg_apply, h, crossL_swap p q, neg_neg]
    exact hpq
  · -- every point of the sector is a positive combination of `p` and `q`, hence lies in `C`
    intro z h1 h2
    have h2' : 0 < -crossL q z := by simpa using h2
    set β : ℝ := crossL p z / crossL p q with hβdef
    have hβpos : 0 < β := by rw [hβdef]; exact div_pos h1 hpq
    have hy : crossL p (z - β • q) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, hβdef, div_mul_cancel₀ _ (ne_of_gt hpq)]
      ring
    obtain ⟨s, hs⟩ := exists_smul_of_crossL_eq_zero hpne hy
    have hs_pos : 0 < s := by
      have h3 : crossL q (z - β • q) = -(s * crossL p q) := by
        rw [hs, map_smul, smul_eq_mul, crossL_swap p q]; ring
      have h4 : crossL q (z - β • q) = crossL q z := by
        rw [map_sub, map_smul, smul_eq_mul, crossL_self, mul_zero, sub_zero]
      have h5 : -(s * crossL p q) = crossL q z := by rw [← h3, h4]
      have h6 : 0 < s * crossL p q := by linarith [h2', h5]
      exact pos_of_mul_pos_left h6 hpq.le
    have hz : z = s • p + β • q := by
      rw [← hs]
      abel
    rw [hz]
    exact hadd _ (hCcone p hp_mem s hs_pos) _ (hCcone q hq_mem β hβpos)

end

end Work.SimplyConnected.ABS
