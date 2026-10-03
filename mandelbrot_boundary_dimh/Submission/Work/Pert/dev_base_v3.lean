import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.Qm_slice

set_option linter.unusedVariables false

namespace Work.Pert

open Complex Metric MandelDim MeasureTheory intervalIntegral
open scoped ComplexConjugate

noncomputable section

/-!
# Geometry of the gate `Qm ξ α`: the two margins and the clearance

`Qm ξ α = {z | m_A z > 0 ∧ m_B z > 0}` where the *linear* margins are

* `margA ξ α z = z.re - ξ + (1/α).re + |z.im + (1/α).im|` (the √2-signed distance to the cone
  with apex `ξ - 1/α`),
* `margB ξ α z = |z.im| - ξ - z.re` (the √2-signed distance to the cone with apex `-ξ`).

Every point of `Qm` has clearance `≥ min margA margB / √2`; the *sum*
`margA + margB = (1/α).re - 2ξ + |z.im| + |z.im + (1/α).im|` depends only on the height.
-/

/-- The `A`-margin of the gate. -/
def margA (ξ : ℝ) (α z : ℂ) : ℝ := z.re - ξ + (1 / α).re + |z.im + (1 / α).im|

/-- The `B`-margin of the gate. -/
def margB (ξ : ℝ) (α z : ℂ) : ℝ := |z.im| - ξ - z.re

lemma mem_Qm_iff_marg (ξ : ℝ) (α z : ℂ) :
    z ∈ Qm ξ α ↔ 0 < margA ξ α z ∧ 0 < margB ξ α z := by
  rw [Qm_mem_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simp only [margA]; linarith, by simp only [margB]; linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by simp only [margA] at h1; linarith, by simp only [margB] at h2; linarith⟩

lemma marg_add (ξ : ℝ) (α z : ℂ) :
    margA ξ α z + margB ξ α z
      = (1 / α).re - 2 * ξ + |z.im| + |z.im + (1 / α).im| := by
  simp only [margA, margB]; ring

lemma margA_eq_sub_sliceLo (ξ : ℝ) (α z : ℂ) :
    margA ξ α z = z.re - sliceLo ξ α z.im := by
  unfold margA sliceLo; ring

lemma margB_eq_sliceHi_sub (ξ : ℝ) (α z : ℂ) :
    margB ξ α z = sliceHi ξ z.im - z.re := by
  unfold margB sliceHi; ring

/-- A point outside the gate (used for the nonemptiness of the complement). -/
lemma exists_not_mem_Qm (ξ : ℝ) (α : ℂ) : ∃ u : ℂ, u ∉ Qm ξ α := by
  refine ⟨((|ξ| + |(1 / α).re| + 1 : ℝ) : ℂ), ?_⟩
  intro hmem
  rw [Qm_mem_iff] at hmem
  have h2 := hmem.2
  have hre : (((|ξ| + |(1 / α).re| + 1 : ℝ) : ℂ)).re = |ξ| + |(1 / α).re| + 1 := by simp
  have him : (((|ξ| + |(1 / α).re| + 1 : ℝ) : ℂ)).im = 0 := by simp
  rw [hre, him, abs_zero] at h2
  have h3 : (0 : ℝ) ≤ |(1 / α).re| := abs_nonneg _
  have h4 : ξ ≤ |ξ| := le_abs_self ξ
  have h5 : -ξ ≤ |ξ| := neg_le_abs ξ
  linarith

/-- Every point outside the gate is at distance at least `min margA margB / √2`. -/
lemma min_marg_div_le_dist {ξ : ℝ} {α z u : ℂ} (hz : z ∈ Qm ξ α) (hu : u ∉ Qm ξ α) :
    min (margA ξ α z) (margB ξ α z) / Real.sqrt 2 ≤ dist z u := by
  have hz' : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) ∈ Qm ξ α := by simpa using hz
  have h := Qm_sep (α := α) (ξ := ξ) (x := z.re) (t := z.im) hz' u hu
  have hz'' : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := by simp
  rw [hz''] at h
  rw [margA_eq_sub_sliceLo, margB_eq_sliceHi_sub]
  exact h

/-- The clearance of a point of the gate. -/
lemma min_marg_div_le_infDist {ξ : ℝ} {α z : ℂ} (hz : z ∈ Qm ξ α) :
    min (margA ξ α z) (margB ξ α z) / Real.sqrt 2 ≤ Metric.infDist z ((Qm ξ α)ᶜ) := by
  obtain ⟨u₀, hu₀⟩ := exists_not_mem_Qm ξ α
  refine (Metric.le_infDist ⟨u₀, hu₀⟩).mpr ?_
  intro u hu
  exact min_marg_div_le_dist hz (by simpa using hu)

/-- If both margins at `z` are at least `√2 R` with `R ≥ 0`, the ball of radius `R` around `z`
lies in the gate. -/
lemma ball_subset_Qm_of_marg_le {ξ : ℝ} {α z : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : Real.sqrt 2 * R ≤ min (margA ξ α z) (margB ξ α z)) :
    Metric.ball z R ⊆ Qm ξ α := by
  rcases eq_or_lt_of_le hR with h0 | hpos
  · intro u hu
    rw [Metric.mem_ball, ← h0] at hu
    exact absurd hu (not_lt.mpr dist_nonneg)
  · have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hmin : 0 < min (margA ξ α z) (margB ξ α z) := by nlinarith [h, hs]
    have hz : z ∈ Qm ξ α := (mem_Qm_iff_marg ξ α z).mpr
      ⟨lt_of_lt_of_le hmin (min_le_left _ _), lt_of_lt_of_le hmin (min_le_right _ _)⟩
    have hkey := min_marg_div_le_infDist hz
    intro u hu
    by_contra huc
    have h1 : R ≤ min (margA ξ α z) (margB ξ α z) / Real.sqrt 2 := by
      rw [le_div_iff₀ hs]; linarith [h]
    have h2 : dist z u < R := by
      rw [Metric.mem_ball, dist_comm] at hu; exact hu
    have h3 : Metric.infDist z ((Qm ξ α)ᶜ) ≤ dist z u :=
      Metric.infDist_le_dist_of_mem (by simpa using huc)
    linarith [hkey, h1, h2, h3]

/-- `hder` transported into a pointwise bound on `deriv Φ` at points of the gate whose margins
are at least `√2 R₁`. -/
lemma deriv_sub_one_le {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ : ℝ} (hR₁ : 0 < R₁)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    {z : ℂ} (h : Real.sqrt 2 * R₁ ≤ min (margA ξ₁ α z) (margB ξ₁ α z)) :
    ‖deriv Φ z - 1‖ ≤ Real.sqrt 2 * C₂ / min (margA ξ₁ α z) (margB ξ₁ α z) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hmin : 0 < min (margA ξ₁ α z) (margB ξ₁ α z) := by nlinarith [h, hs, hR₁]
  have hR₁R : R₁ ≤ min (margA ξ₁ α z) (margB ξ₁ α z) / Real.sqrt 2 := by
    rw [le_div_iff₀ hs]; linarith [h]
  have hball : Metric.ball z (min (margA ξ₁ α z) (margB ξ₁ α z) / Real.sqrt 2) ⊆ Qm ξ₁ α := by
    refine ball_subset_Qm_of_marg_le (by positivity) ?_
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hs)]
  have h1 := hder z (min (margA ξ₁ α z) (margB ξ₁ α z) / Real.sqrt 2) hR₁R hball
  have hDne : min (margA ξ₁ α z) (margB ξ₁ α z) ≠ 0 := ne_of_gt hmin
  convert h1 using 1
  rw [div_div_eq_mul_div]
  ring



/-- The pin hypothesis `ball z₀ (M/8) ⊆ Qm` forces both margins at `z₀` to be at least `M/8`.
(The stronger `√2 * M / 8` is FALSE: `M = 8`, `z₀ = -7`, `ξ₁ = 5.8`, `α = 1/160`.) -/
lemma marg_pin_ge {ξ₁ M : ℝ} {α z₀ : ℂ} (hM : 8 ≤ M)
    (hz₀c : Metric.ball z₀ (M / 8) ⊆ Qm ξ₁ α) :
    M / 8 ≤ margA ξ₁ α z₀ ∧ M / 8 ≤ margB ξ₁ α z₀ := by
  have hMpos : 0 < M / 8 := by linarith
  obtain ⟨hAz, hBz⟩ := (mem_Qm_iff_marg ξ₁ α z₀).mp (hz₀c (Metric.mem_ball_self hMpos))
  have hz : ((z₀.re : ℝ) : ℂ) + (z₀.im : ℂ) * Complex.I = z₀ := Complex.re_add_im z₀
  have keyA : ∀ r : ℝ, 0 < r → r < M / 8 → margA ξ₁ α z₀ > r := by
    intro r hr hrM
    have hmem : ((z₀.re - r : ℝ) : ℂ) + (z₀.im : ℂ) * Complex.I ∈ Qm ξ₁ α := by
      apply hz₀c
      have hsub : ((z₀.re - r : ℝ) : ℂ) + (z₀.im : ℂ) * Complex.I - z₀ = ((-r : ℝ) : ℂ) := by
        rw [sub_eq_iff_eq_add, ← hz]
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          add_zero, zero_add]
        push_cast
        ring
      rw [Metric.mem_ball, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, abs_of_pos hr]
      exact hrM
    obtain ⟨h1, -⟩ := (mem_Qm_iff_marg ξ₁ α _).mp hmem
    have e1 : margA ξ₁ α (((z₀.re - r : ℝ) : ℂ) + (z₀.im : ℂ) * Complex.I)
        = margA ξ₁ α z₀ - r := by
      simp only [margA, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, zero_add]
      ring
    rw [e1] at h1
    linarith
  have keyB : ∀ r : ℝ, 0 < r → r < M / 8 → margB ξ₁ α z₀ > r := by
    intro r hr hrM
    have hmem : ((z₀.re + r : ℝ) : ℂ) + (z₀.im : ℂ) * Complex.I ∈ Qm ξ₁ α := by
      apply hz₀c
      have hsub : ((z₀.re + r : ℝ) : ℂ) + (z₀.im : ℂ) * Complex.I - z₀ = ((r : ℝ) : ℂ) := by
        rw [sub_eq_iff_eq_add, ← hz]
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          add_zero, zero_add]
        push_cast
        ring
      rw [Metric.mem_ball, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
      exact hrM
    obtain ⟨-, h2⟩ := (mem_Qm_iff_marg ξ₁ α _).mp hmem
    have e2 : margB ξ₁ α (((z₀.re + r : ℝ) : ℂ) + (z₀.im : ℂ) * Complex.I)
        = margB ξ₁ α z₀ - r := by
      simp only [margB, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, zero_add]
      ring
    rw [e2] at h2
    linarith
  refine ⟨?_, ?_⟩
  · by_contra h
    have h' : margA ξ₁ α z₀ < M / 8 := not_le.mp h
    have hr : 0 < (margA ξ₁ α z₀ + M / 8) / 2 := by linarith
    have hrM : (margA ξ₁ α z₀ + M / 8) / 2 < M / 8 := by linarith
    have := keyA _ hr hrM
    linarith
  · by_contra h
    have h' : margB ξ₁ α z₀ < M / 8 := not_le.mp h
    have hr : 0 < (margB ξ₁ α z₀ + M / 8) / 2 := by linarith
    have hrM : (margB ξ₁ α z₀ + M / 8) / 2 < M / 8 := by linarith
    have := keyB _ hr hrM
    linarith


/-! ## Inlined fundamental-theorem-of-calculus segment bound

The same lemma as `Work.Pert.dev_seg_le` (delegated, proved in
`Submission/Work/Pert/dev_seg_le.lean`), reproduced here **renamed** so that this file can use it
without an import cycle (that module imports this one). -/
set_option maxHeartbeats 1000000 in
/-- Continuity of the `A`-margin of the gate. -/
lemma segaux_continuous_margA (ξ : ℝ) (α : ℂ) : Continuous (fun z : ℂ => margA ξ α z) := by
  unfold margA; fun_prop

set_option maxHeartbeats 1000000 in
/-- Continuity of the `B`-margin of the gate. -/
lemma segaux_continuous_margB (ξ : ℝ) (α : ℂ) : Continuous (fun z : ℂ => margB ξ α z) := by
  unfold margB; fun_prop

/-- **Displacement bound along a segment through the gate.**

If `Φ` is differentiable on the segment `[p, q]`, its derivative is continuous there and within
`C₂/R` of `1` on every ball of radius `R ≥ R₁` contained in the gate `Qm ξ₁ α`, and every point
`p + t • (q - p)` of the segment has margin `min (margA) (margB) ≥ √2 R₁`, then

  `‖(Φ q - q) - (Φ p - p)‖ ≤ √2 C₂ ‖q - p‖ ∫₀¹ dt / min (margA (p + t•(q-p))) (margB (p + t•(q-p)))`.

The proof is the fundamental theorem of calculus for `t ↦ Φ (p + t•(q-p)) - (p + t•(q-p))`
together with the pointwise bound `Work.Pert.deriv_sub_one_le`, and the triangle inequality for
the integral. -/
theorem dev_seg_le_internal {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ : ℝ} {p q : ℂ} (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hclear : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt 2 * R₁ ≤
      min (Work.Pert.margA ξ₁ α (p + t • (q - p))) (Work.Pert.margB ξ₁ α (p + t • (q - p))))
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ Φ (p + t • (q - p)))
    (hcont : ContinuousOn (deriv Φ) {z : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1, z = p + t • (q - p)}) :
    ‖(Φ q - q) - (Φ p - p)‖ ≤ Real.sqrt 2 * C₂ * ‖q - p‖ *
      (∫ t in (0 : ℝ)..1, (1 / min (Work.Pert.margA ξ₁ α (p + t • (q - p)))
        (Work.Pert.margB ξ₁ α (p + t • (q - p))))) := by
  have hmargA : Continuous (fun z : ℂ => Work.Pert.margA ξ₁ α z) := segaux_continuous_margA ξ₁ α
  have hmargB : Continuous (fun z : ℂ => Work.Pert.margB ξ₁ α z) := segaux_continuous_margB ξ₁ α
  -- the direction of the segment and the parametrisation
  set h : ℂ := q - p with hh_def
  set γ : ℝ → ℂ := fun t => p + (t : ℂ) * h with hγ_def
  have hγ_eq : ∀ t : ℝ, p + t • (q - p) = γ t := by
    intro t; simp only [hγ_def, hh_def, Complex.real_smul]
  have hγ1 : γ 1 = q := by simp [hγ_def, hh_def]
  have hγ0 : γ 0 = p := by simp [hγ_def]
  have hγ_cont : Continuous γ := by
    rw [show γ = fun t : ℝ => p + (t : ℂ) * h from by funext s; simp [hγ_def]]
    fun_prop
  -- the margin along the segment
  set m : ℝ → ℝ := fun t => min (Work.Pert.margA ξ₁ α (γ t)) (Work.Pert.margB ξ₁ α (γ t))
    with hm_def
  have hm_pos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < m t := by
    intro t ht
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hh := hclear t ht
    rw [hγ_eq t] at hh
    have : 0 < min (Work.Pert.margA ξ₁ α (γ t)) (Work.Pert.margB ξ₁ α (γ t)) := by
      nlinarith [hh, hs, hR₁]
    simpa [hm_def] using this
  -- the pointwise derivative bound along the segment
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv Φ (γ t) - 1‖ ≤ Real.sqrt 2 * C₂ / m t := by
    intro t ht
    have hh := hclear t ht
    rw [hγ_eq t] at hh
    have h := deriv_sub_one_le hR₁ hder hh
    simpa [hm_def] using h
  -- the curve is differentiable with derivative `h`
  have hline : ∀ t : ℝ, HasDerivAt γ h t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * h) (1 * h) t := h1.mul_const h
    have h3 : HasDerivAt (fun s : ℝ => p + (s : ℂ) * h) (1 * h) t := h2.const_add p
    simpa [hγ_def] using h3
  -- the derivative of `Φ ∘ γ - γ`
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Φ (γ s) - γ s) ((deriv Φ (γ t) - 1) * h) t := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hdt : DifferentiableAt ℂ Φ (γ t) := by
      have := hdiff t htI
      rwa [hγ_eq t] at this
    have hΦd : HasDerivAt Φ (deriv Φ (γ t)) (γ t) := hdt.hasDerivAt
    have hcomp := hΦd.comp t (hline t)
    have hsub := hcomp.sub (hline t)
    have hder : deriv Φ (γ t) * h - h = (deriv Φ (γ t) - 1) * h := by ring
    rwa [hder] at hsub
  -- the segment lies in the domain on which `deriv Φ` is continuous
  have hmap : Set.MapsTo γ (Set.Icc (0 : ℝ) 1)
      {z : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1, z = p + t • (q - p)} := by
    intro t ht
    exact ⟨t, ht, by rw [← hγ_eq t]⟩
  have hdΦcont : ContinuousOn (fun t => deriv Φ (γ t)) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hcont.comp hγ_cont.continuousOn hmap
  have hint : IntervalIntegrable (fun t : ℝ => (deriv Φ (γ t) - 1) * h) volume (0 : ℝ) 1 :=
    ((hdΦcont.sub continuousOn_const).mul continuousOn_const).intervalIntegrable
  -- the fundamental theorem of calculus
  have hFTC : (∫ t in (0 : ℝ)..1, (deriv Φ (γ t) - 1) * h)
      = (Φ (γ 1) - γ 1) - (Φ (γ 0) - γ 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hmain : ‖(Φ q - q) - (Φ p - p)‖
      ≤ ∫ t in (0 : ℝ)..1, ‖(deriv Φ (γ t) - 1) * h‖ := by
    rw [← hγ1, ← hγ0, ← hFTC]
    exact intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)
  have hInt1 : IntervalIntegrable (fun t : ℝ => ‖(deriv Φ (γ t) - 1) * h‖) volume (0 : ℝ) 1 :=
    (((hdΦcont.sub continuousOn_const).mul continuousOn_const).norm).intervalIntegrable
  have hm_cont : Continuous m := by
    rw [hm_def]
    exact (hmargA.comp hγ_cont).min (hmargB.comp hγ_cont)
  have hInt2 : IntervalIntegrable (fun t : ℝ => (Real.sqrt 2 * C₂ / m t) * ‖h‖)
      volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    refine (ContinuousOn.div continuousOn_const hm_cont.continuousOn ?_).mul continuousOn_const
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact ne_of_gt (hm_pos t htI)
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(deriv Φ (γ t) - 1) * h‖ ≤ (Real.sqrt 2 * C₂ / m t) * ‖h‖ := by
    intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg h)
  have hstep2 : (∫ t in (0 : ℝ)..1, ‖(deriv Φ (γ t) - 1) * h‖)
      ≤ ∫ t in (0 : ℝ)..1, (Real.sqrt 2 * C₂ / m t) * ‖h‖ :=
    intervalIntegral.integral_mono_on (by norm_num) hInt1 hInt2 hpoint
  have h3 : (∫ t in (0 : ℝ)..1, (Real.sqrt 2 * C₂ / m t) * ‖h‖)
      = (Real.sqrt 2 * C₂ * ‖h‖) * ∫ t in (0 : ℝ)..1, 1 / m t := by
    have hcongr : Set.EqOn (fun t : ℝ => (Real.sqrt 2 * C₂ / m t) * ‖h‖)
        (fun t : ℝ => (Real.sqrt 2 * C₂ * ‖h‖) * (1 / m t)) (Set.uIcc (0 : ℝ) 1) := by
      intro t _
      simp only [div_eq_mul_inv]
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
  have h2 : (∫ t in (0 : ℝ)..1, 1 / m t)
      = ∫ t in (0 : ℝ)..1, 1 / min (Work.Pert.margA ξ₁ α (p + t • (q - p)))
          (Work.Pert.margB ξ₁ α (p + t • (q - p))) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hm_def]
    rw [hγ_eq t]
  calc ‖(Φ q - q) - (Φ p - p)‖ ≤ ∫ t in (0 : ℝ)..1, ‖(deriv Φ (γ t) - 1) * h‖ := hmain
    _ ≤ ∫ t in (0 : ℝ)..1, (Real.sqrt 2 * C₂ / m t) * ‖h‖ := hstep2
    _ = (Real.sqrt 2 * C₂ * ‖h‖) * ∫ t in (0 : ℝ)..1, 1 / m t := h3
    _ = Real.sqrt 2 * C₂ * ‖q - p‖ *
        (∫ t in (0 : ℝ)..1, (1 / min (Work.Pert.margA ξ₁ α (p + t • (q - p)))
          (Work.Pert.margB ξ₁ α (p + t • (q - p))))) := by
      rw [hh_def, h2]


lemma margB_eval (ξ : ℝ) (α : ℂ) (x y : ℝ) :
    margB ξ α (x + y * Complex.I) = |y| - ξ - x := by
  simp only [margB, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    zero_add]
  ring

lemma margA_eval (ξ : ℝ) (α : ℂ) (x y : ℝ) :
    margA ξ α (x + y * Complex.I) = x - ξ + (1/α).re + |y + (1/α).im| := by
  simp only [margA, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    zero_add]
  ring

lemma isOpen_Qm_ (ξ : ℝ) (α : ℂ) : IsOpen (Qm ξ α) := by
  rw [show Qm ξ α = {z : ℂ | ξ - (1/α).re - |z.im + (1/α).im| < z.re ∧ z.re < |z.im| - ξ}
    from Set.ext (fun z => Qm_mem_iff)]
  exact IsOpen.and (isOpen_lt (by fun_prop) (by fun_prop)) (isOpen_lt (by fun_prop) (by fun_prop))

lemma contOn_deriv_of_diffOn {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ : ℝ}
    (hΦ : DifferentiableOn ℂ Φ (Qm ξ₁ α)) : ContinuousOn (deriv Φ) (Qm ξ₁ α) := by
  have hopen : IsOpen (Qm ξ₁ α) := isOpen_Qm_ ξ₁ α
  have han : AnalyticOn ℂ Φ (Qm ξ₁ α) := hΦ.analyticOn hopen
  exact (han.contDiffOn hopen.uniqueDiffOn).continuousOn_deriv_of_isOpen hopen le_top

lemma integral_inv_affine {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..1, (1 : ℝ) / (a + b * t)) = Real.log ((a + b) / a) / b := by
  have hne : b ≠ 0 := ne_of_gt hb
  have hmem : (0 : ℝ) ∉ Set.uIcc a (b + a) := by
    rw [Set.uIcc_of_le (by linarith : a ≤ b + a), Set.mem_Icc, not_and]
    intro h; linarith
  have key := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := (1 : ℝ)) (c := b)
      (f := fun x : ℝ => x⁻¹) hne a
  rw [show (∫ t in (0 : ℝ)..1, (1 : ℝ) / (a + b * t))
        = ∫ t in (0 : ℝ)..1, (b * t + a)⁻¹ by
        apply intervalIntegral.integral_congr
        intro t _
        show (1 : ℝ) / (a + b * t) = (b * t + a)⁻¹
        rw [one_div, add_comm]]
  rw [key, smul_eq_mul, mul_zero, mul_one, zero_add, integral_inv hmem]
  rw [inv_mul_eq_div]
  congr 1
  rw [add_comm]

/-- **Deviation bound along a segment with a designated minimum margin.**
If `m` is a positive lower bound of both margins along the segment and `√2 R₁ ≤ m` there, then the
deviation is bounded by `√2 C₂ ‖q - p‖ ∫₀¹ dt / m t`. -/
theorem dev_seg_of_designated {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ : ℝ} {p q : ℂ} {m : ℝ → ℝ}
    (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hmc : Continuous m)
    (hclear : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt 2 * R₁ ≤ m t)
    (hminA : ∀ t ∈ Set.Icc (0 : ℝ) 1, m t ≤ margA ξ₁ α (p + t • (q - p)))
    (hminB : ∀ t ∈ Set.Icc (0 : ℝ) 1, m t ≤ margB ξ₁ α (p + t • (q - p)))
    (hcont : ContinuousOn (deriv Φ) {z : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1, z = p + t • (q - p)})
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ Φ (p + t • (q - p))) :
    ‖(Φ q - q) - (Φ p - p)‖ ≤
      Real.sqrt 2 * C₂ * ‖q - p‖ * (∫ t in (0 : ℝ)..1, (1 : ℝ) / m t) := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < m t := fun t ht => by
    nlinarith [hclear t ht, mul_pos hs2 hR₁]
  have h := dev_seg_le_internal (p := p) (q := q) hR₁ hC₂ hder
    (fun t ht => le_trans (hclear t ht) (le_min (hminA t ht) (hminB t ht)))
    hdiff hcont
  refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hγ : Continuous (fun t : ℝ => p + t • (q - p)) := by fun_prop
  have hcm : Continuous
      (fun t : ℝ => min (margA ξ₁ α (p + t • (q - p))) (margB ξ₁ α (p + t • (q - p)))) :=
    ((segaux_continuous_margA ξ₁ α).comp hγ).min ((segaux_continuous_margB ξ₁ α).comp hγ)
  have hposmin : ∀ t ∈ Set.Icc (0:ℝ) 1,
      0 < min (margA ξ₁ α (p + t • (q - p))) (margB ξ₁ α (p + t • (q - p))) :=
    fun t ht => lt_of_lt_of_le (hpos t ht) (le_min (hminA t ht) (hminB t ht))
  have hInt1 : IntervalIntegrable
      (fun t : ℝ => (1 : ℝ) / (min (margA ξ₁ α (p + t • (q - p)))
        (margB ξ₁ α (p + t • (q - p))))) volume (0:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ContinuousOn.div continuousOn_const hcm.continuousOn
      (fun t ht => ne_of_gt (hposmin t ht))
  have hInt2 : IntervalIntegrable (fun t : ℝ => (1:ℝ)/(m t)) volume (0:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ContinuousOn.div continuousOn_const hmc.continuousOn
      (fun t ht => ne_of_gt (hpos t ht))
  refine intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hInt1 hInt2 ?_
  intro t ht
  exact one_div_le_one_div_of_le (hpos t ht) (le_min (hminA t ht) (hminB t ht))


/-- Deviation bound along a segment where the designated margin is affine, `m t = a + b t`
with `a, b > 0`. -/
theorem dev_seg_affine {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ : ℝ} {p q : ℂ} {m : ℝ → ℝ} {a b : ℝ}
    (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hmc : Continuous m)
    (ha : 0 < a) (hb : 0 < b) (hcl : Real.sqrt 2 * R₁ ≤ a)
    (haff : ∀ t ∈ Set.Icc (0 : ℝ) 1, m t = a + b * t)
    (hminA : ∀ t ∈ Set.Icc (0 : ℝ) 1, m t ≤ margA ξ₁ α (p + t • (q - p)))
    (hminB : ∀ t ∈ Set.Icc (0 : ℝ) 1, m t ≤ margB ξ₁ α (p + t • (q - p)))
    (hcont : ContinuousOn (deriv Φ) {z : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1, z = p + t • (q - p)})
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ Φ (p + t • (q - p))) :
    ‖(Φ q - q) - (Φ p - p)‖ ≤
      Real.sqrt 2 * C₂ * ‖q - p‖ * (Real.log ((a + b) / a) / b) := by
  have hclear : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt 2 * R₁ ≤ m t := by
    intro t ht
    have ht' : (0:ℝ) ≤ t := ht.1
    have h1 : 0 ≤ b * t := mul_nonneg (le_of_lt hb) ht'
    rw [haff t ht]
    nlinarith [hcl, h1]
  have h := dev_seg_of_designated hR₁ hC₂ hder hmc hclear hminA hminB hcont hdiff
  refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have heq : (∫ t in (0:ℝ)..1, (1:ℝ)/m t) = ∫ t in (0:ℝ)..1, (1:ℝ)/(a + b*t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show (1:ℝ)/m t = (1:ℝ)/(a + b*t)
    rw [haff t (by rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht)]
  rw [heq, integral_inv_affine ha hb]

/-- Deviation bound along a segment where the designated margin is constant `a > 0`. -/
theorem dev_seg_const {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ : ℝ} {p q : ℂ} {m : ℝ → ℝ} {a : ℝ}
    (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hmc : Continuous m)
    (ha : 0 < a) (hcl : Real.sqrt 2 * R₁ ≤ a)
    (haff : ∀ t ∈ Set.Icc (0 : ℝ) 1, m t = a)
    (hminA : ∀ t ∈ Set.Icc (0 : ℝ) 1, m t ≤ margA ξ₁ α (p + t • (q - p)))
    (hminB : ∀ t ∈ Set.Icc (0 : ℝ) 1, m t ≤ margB ξ₁ α (p + t • (q - p)))
    (hcont : ContinuousOn (deriv Φ) {z : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1, z = p + t • (q - p)})
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ Φ (p + t • (q - p))) :
    ‖(Φ q - q) - (Φ p - p)‖ ≤ Real.sqrt 2 * C₂ * ‖q - p‖ / a := by
  have hclear : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt 2 * R₁ ≤ m t := by
    intro t ht; rw [haff t ht]; exact hcl
  have h := dev_seg_of_designated hR₁ hC₂ hder hmc hclear hminA hminB hcont hdiff
  refine le_trans h (le_of_eq ?_)
  have hcongr : (∫ t in (0 : ℝ)..1, (1:ℝ)/ m t) = ∫ t in (0:ℝ)..1, (1:ℝ)/a := by
    apply intervalIntegral.integral_congr
    intro t ht
    show (1:ℝ)/m t = (1:ℝ)/a
    rw [haff t (by rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht)]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  ring


/-- The point of the segment `[p,q]` at parameter `t`, in coordinates. -/
lemma seg_point (p q : ℂ) (t : ℝ) :
    p + t • (q - p) =
      ((p.re + t * (q.re - p.re) : ℝ) : ℂ) + ((p.im + t * (q.im - p.im) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

/-- The vertical segment point at parameter `t`, as a height. -/
lemma seg_point_vert (x₀ y₁ y₂ t : ℝ) :
    (((x₀:ℂ) + (y₁:ℂ)*Complex.I) + t • (((x₀:ℂ) + (y₂:ℂ)*Complex.I)
      - ((x₀:ℂ) + (y₁:ℂ)*Complex.I)))
      = (x₀:ℂ) + ((y₁ + t*(y₂-y₁) : ℝ):ℂ)*Complex.I := by
  rw [seg_point]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    zero_add]
  ring_nf

/-- **Vertical piece** `x₀ + i y`, `y ∈ [y₁, y₂] ⊆ [0,∞)`: `margB` is the smallest margin and
increases at unit rate, so the cost is `√2 log (margB q / margB p)`. -/
theorem dev_vert {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ x₀ y₁ y₂ : ℝ}
    (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hdiff : DifferentiableOn ℂ Φ (Qm ξ₁ α)) (hcont : ContinuousOn (deriv Φ) (Qm ξ₁ α))
    (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂)
    (hminA : ∀ y ∈ Set.Icc y₁ y₂,
      margB ξ₁ α ((x₀:ℂ) + (y:ℂ)*Complex.I) ≤ margA ξ₁ α ((x₀:ℂ) + (y:ℂ)*Complex.I))
    (hcl : Real.sqrt 2 * R₁ ≤ margB ξ₁ α ((x₀:ℂ) + (y₁:ℂ)*Complex.I)) :
    ‖(Φ ((x₀:ℂ) + (y₂:ℂ)*Complex.I) - ((x₀:ℂ) + (y₂:ℂ)*Complex.I))
        - (Φ ((x₀:ℂ) + (y₁:ℂ)*Complex.I) - ((x₀:ℂ) + (y₁:ℂ)*Complex.I))‖ ≤
      Real.sqrt 2 * C₂ * Real.log (margB ξ₁ α ((x₀:ℂ) + (y₂:ℂ)*Complex.I)
        / margB ξ₁ α ((x₀:ℂ) + (y₁:ℂ)*Complex.I)) := by
  set p : ℂ := (x₀:ℂ) + (y₁:ℂ)*Complex.I with hp
  set q : ℂ := (x₀:ℂ) + (y₂:ℂ)*Complex.I with hq
  rcases lt_or_eq_of_le hy with hlt | heq
  · have hb : 0 < y₂ - y₁ := by linarith
    have hbne : y₂ - y₁ ≠ 0 := ne_of_gt hb
    set m : ℝ → ℝ := fun t => margB ξ₁ α (p + t • (q - p)) with hm
    have hpt : ∀ t : ℝ, p + t • (q - p) = (x₀:ℂ) + ((y₁ + t*(y₂-y₁) : ℝ):ℂ)*Complex.I := by
      intro t
      rw [show p + t • (q - p) = (((x₀:ℂ) + (y₁:ℂ)*Complex.I) + t •
        (((x₀:ℂ) + (y₂:ℂ)*Complex.I) - ((x₀:ℂ) + (y₁:ℂ)*Complex.I))) from by rw [hp, hq],
        seg_point_vert]
    have hbounded : ∀ t ∈ Set.Icc (0:ℝ) 1, y₁ ≤ y₁ + t*(y₂-y₁) ∧ y₁ + t*(y₂-y₁) ≤ y₂ := by
      intro t ht; constructor <;> nlinarith [ht.1, ht.2, hb]
    have hypos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ y₁ + t*(y₂-y₁) :=
      fun t ht => le_trans hy₁ (hbounded t ht).1
    have hmc : Continuous m := by
      rw [hm]
      exact (segaux_continuous_margB ξ₁ α).comp (by fun_prop)
    have hp_e : margB ξ₁ α p = y₁ - ξ₁ - x₀ := by
      have : p = (x₀:ℂ) + (y₁:ℂ)*Complex.I := hp
      rw [this, margB_eval, abs_of_nonneg hy₁]
    have hq_e : margB ξ₁ α q = y₂ - ξ₁ - x₀ := by
      have : q = (x₀:ℂ) + (y₂:ℂ)*Complex.I := hq
      rw [this, margB_eval, abs_of_nonneg (le_trans hy₁ hy)]
    have haff : ∀ t ∈ Set.Icc (0:ℝ) 1, m t = margB ξ₁ α p + (y₂ - y₁) * t := by
      intro t ht
      have h1 : m t = margB ξ₁ α ((x₀:ℂ) + ((y₁ + t*(y₂-y₁) : ℝ):ℂ)*Complex.I) := by
        simp only [hm]; congr 1; exact hpt t
      rw [h1, margB_eval, abs_of_nonneg (hypos t ht)]
      rw [hp_e]
      ring
    have ha : 0 < margB ξ₁ α p := by
      have h1 : 0 < Real.sqrt 2 * R₁ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR₁
      linarith [hcl]
    have hminAm : ∀ t ∈ Set.Icc (0:ℝ) 1, m t ≤ margA ξ₁ α (p + t • (q - p)) := by
      intro t ht
      simp only [hm]
      rw [hpt t]
      exact hminA _ (hbounded t ht)
    have hminBm : ∀ t ∈ Set.Icc (0:ℝ) 1, m t ≤ margB ξ₁ α (p + t • (q - p)) :=
      fun t ht => le_of_eq rfl
    have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, p + t • (q - p) ∈ Qm ξ₁ α := by
      intro t ht
      rw [mem_Qm_iff_marg]
      have hmb : 0 < margB ξ₁ α (p + t • (q - p)) := by
        have h2 : margB ξ₁ α p ≤ margB ξ₁ α (p + t • (q - p)) := by
          rw [hp_e, hpt t, margB_eval, abs_of_nonneg (hypos t ht)]
          linarith [(hbounded t ht).1]
        linarith [ha, h2]
      exact ⟨lt_of_lt_of_le hmb (hminAm t ht), hmb⟩
    have hcont' : ContinuousOn (deriv Φ)
        {z : ℂ | ∃ t ∈ Set.Icc (0:ℝ) 1, z = p + t • (q - p)} :=
      hcont.mono (fun z hz => by
        obtain ⟨t, ht, rfl⟩ := hz
        exact hseg t ht)
    have hdiff' : ∀ t ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℂ Φ (p + t • (q - p)) := fun t ht =>
      (hdiff _ (hseg t ht)).differentiableAt ((isOpen_Qm_ ξ₁ α).mem_nhds (hseg t ht))
    have hres := dev_seg_affine (p := p) (q := q) (m := m) (a := margB ξ₁ α p) (b := y₂ - y₁)
      hR₁ hC₂ hder hmc ha hb hcl haff hminAm hminBm hcont' hdiff'
    have hnorm : ‖q - p‖ = y₂ - y₁ := by
      have hqp : q - p = ((y₂ - y₁ : ℝ) : ℂ) * Complex.I := by
        rw [show q = (x₀:ℂ) + (y₂:ℂ)*Complex.I from hq,
            show p = (x₀:ℂ) + (y₁:ℂ)*Complex.I from hp]
        push_cast; ring
      rw [hqp, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hb]
    have hratio : (margB ξ₁ α p + (y₂ - y₁)) / margB ξ₁ α p
        = margB ξ₁ α q / margB ξ₁ α p := by
      congr 1
      rw [hp_e, hq_e]; ring
    have hsimple : Real.sqrt 2 * C₂ * (y₂ - y₁) *
        (Real.log (margB ξ₁ α q / margB ξ₁ α p) / (y₂ - y₁))
        = Real.sqrt 2 * C₂ * Real.log (margB ξ₁ α q / margB ξ₁ α p) := by
      field_simp
    rw [hnorm, hratio, hsimple] at hres
    exact hres
  · subst heq
    have hpq : p = q := by rw [hp, hq]
    have hcl' : Real.sqrt 2 * R₁ ≤ margB ξ₁ α q := by rw [← hpq]; exact hcl
    rw [hpq]
    have hne : margB ξ₁ α q ≠ 0 := by
      have h1 : 0 < Real.sqrt 2 * R₁ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR₁
      linarith [hcl']
    rw [sub_self, norm_zero, div_self hne, Real.log_one, mul_zero]


-- helper: the segment point in coordinates, for concrete point shapes
lemma seg_point_xy (x₁ y₁ x₂ y₂ t : ℝ) :
    (((x₁:ℂ) + (y₁:ℂ)*Complex.I) + t • (((x₂:ℂ) + (y₂:ℂ)*Complex.I)
      - ((x₁:ℂ) + (y₁:ℂ)*Complex.I)))
      = (x₁ + t*(x₂-x₁) : ℝ) + ((y₁ + t*(y₂-y₁) : ℝ))*Complex.I := by
  rw [seg_point]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    zero_add]
  ring_nf

/-- **Horizontal piece** from `x₁ + i y` to `x₂ + i y` with `x₂ ≤ x₁`, `y ≥ 0`: `margB`
increases at unit rate as `x` decreases. -/
theorem dev_horiz {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ x₁ x₂ y : ℝ}
    (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hdiff : DifferentiableOn ℂ Φ (Qm ξ₁ α)) (hcont : ContinuousOn (deriv Φ) (Qm ξ₁ α))
    (hy : 0 ≤ y) (hx : x₂ ≤ x₁)
    (hminA : ∀ x ∈ Set.Icc x₂ x₁,
      margB ξ₁ α ((x:ℂ) + (y:ℂ)*Complex.I) ≤ margA ξ₁ α ((x:ℂ) + (y:ℂ)*Complex.I))
    (hcl : Real.sqrt 2 * R₁ ≤ margB ξ₁ α ((x₁:ℂ) + (y:ℂ)*Complex.I)) :
    ‖(Φ ((x₂:ℂ) + (y:ℂ)*Complex.I) - ((x₂:ℂ) + (y:ℂ)*Complex.I))
        - (Φ ((x₁:ℂ) + (y:ℂ)*Complex.I) - ((x₁:ℂ) + (y:ℂ)*Complex.I))‖ ≤
      Real.sqrt 2 * C₂ * Real.log (margB ξ₁ α ((x₂:ℂ) + (y:ℂ)*Complex.I)
        / margB ξ₁ α ((x₁:ℂ) + (y:ℂ)*Complex.I)) := by
  set p : ℂ := (x₁:ℂ) + (y:ℂ)*Complex.I with hp
  set q : ℂ := (x₂:ℂ) + (y:ℂ)*Complex.I with hq
  rcases lt_or_eq_of_le hx with hlt | heq
  · have hb : 0 < x₁ - x₂ := by linarith
    set m : ℝ → ℝ := fun t => margB ξ₁ α (p + t • (q - p)) with hm
    have hpt : ∀ t : ℝ, p + t • (q - p) = (x₁ + t*(x₂-x₁) : ℝ) + (y:ℂ)*Complex.I := by
      intro t
      rw [show p + t • (q - p) = (((x₁:ℂ) + (y:ℂ)*Complex.I) + t •
        (((x₂:ℂ) + (y:ℂ)*Complex.I) - ((x₁:ℂ) + (y:ℂ)*Complex.I))) from by rw [hp, hq],
        seg_point_xy]
      norm_num
    have hbounded : ∀ t ∈ Set.Icc (0:ℝ) 1, x₂ ≤ x₁ + t*(x₂-x₁) ∧ x₁ + t*(x₂-x₁) ≤ x₁ := by
      intro t ht; constructor <;> nlinarith [ht.1, ht.2, hb]
    have hmc : Continuous m := by
      rw [hm]; exact (segaux_continuous_margB ξ₁ α).comp (by fun_prop)
    have hp_e : margB ξ₁ α p = y - ξ₁ - x₁ := by
      rw [show p = (x₁:ℂ) + (y:ℂ)*Complex.I from hp, margB_eval, abs_of_nonneg hy]
    have hq_e : margB ξ₁ α q = y - ξ₁ - x₂ := by
      rw [show q = (x₂:ℂ) + (y:ℂ)*Complex.I from hq, margB_eval, abs_of_nonneg hy]
    have haff : ∀ t ∈ Set.Icc (0:ℝ) 1, m t = margB ξ₁ α p + (x₁ - x₂) * t := by
      intro t ht
      have h1 : m t = margB ξ₁ α ((x₁ + t*(x₂-x₁) : ℝ) + (y:ℂ)*Complex.I) := by
        simp only [hm]; congr 1; exact hpt t
      rw [h1, margB_eval, abs_of_nonneg hy, hp_e]
      ring
    have ha : 0 < margB ξ₁ α p := by
      have h1 : 0 < Real.sqrt 2 * R₁ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR₁
      linarith [hcl]
    have hminAm : ∀ t ∈ Set.Icc (0:ℝ) 1, m t ≤ margA ξ₁ α (p + t • (q - p)) := by
      intro t ht
      simp only [hm]
      rw [hpt t]
      exact hminA _ (hbounded t ht)
    have hminBm : ∀ t ∈ Set.Icc (0:ℝ) 1, m t ≤ margB ξ₁ α (p + t • (q - p)) :=
      fun t ht => le_of_eq rfl
    have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, p + t • (q - p) ∈ Qm ξ₁ α := by
      intro t ht
      rw [mem_Qm_iff_marg]
      have hmb : 0 < margB ξ₁ α (p + t • (q - p)) := by
        have h2 : margB ξ₁ α p ≤ margB ξ₁ α (p + t • (q - p)) := by
          rw [hp_e, hpt t, margB_eval, abs_of_nonneg hy]
          linarith [(hbounded t ht).2]
        linarith [ha, h2]
      exact ⟨lt_of_lt_of_le hmb (hminAm t ht), hmb⟩
    have hcont' : ContinuousOn (deriv Φ)
        {z : ℂ | ∃ t ∈ Set.Icc (0:ℝ) 1, z = p + t • (q - p)} :=
      hcont.mono (fun z hz => by obtain ⟨t, ht, rfl⟩ := hz; exact hseg t ht)
    have hdiff' : ∀ t ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℂ Φ (p + t • (q - p)) := fun t ht =>
      (hdiff _ (hseg t ht)).differentiableAt ((isOpen_Qm_ ξ₁ α).mem_nhds (hseg t ht))
    have hres := dev_seg_affine (p := p) (q := q) (m := m) (a := margB ξ₁ α p) (b := x₁ - x₂)
      hR₁ hC₂ hder hmc ha hb hcl haff hminAm hminBm hcont' hdiff'
    have hnorm : ‖q - p‖ = x₁ - x₂ := by
      have hqp : q - p = ((x₂ - x₁ : ℝ) : ℂ) := by
        rw [show q = (x₂:ℂ) + (y:ℂ)*Complex.I from hq,
            show p = (x₁:ℂ) + (y:ℂ)*Complex.I from hp]
        push_cast; ring
      rw [hqp, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : x₂ - x₁ < 0)]
      ring
    have hratio : (margB ξ₁ α p + (x₁ - x₂)) / margB ξ₁ α p
        = margB ξ₁ α q / margB ξ₁ α p := by
      congr 1; rw [hp_e, hq_e]; ring
    have hsimple : Real.sqrt 2 * C₂ * (x₁ - x₂) *
        (Real.log (margB ξ₁ α q / margB ξ₁ α p) / (x₁ - x₂))
        = Real.sqrt 2 * C₂ * Real.log (margB ξ₁ α q / margB ξ₁ α p) := by
      field_simp
    rw [hnorm, hratio, hsimple] at hres
    exact hres
  · subst heq
    have hpq : p = q := by rw [hp, hq]
    have hcl' : Real.sqrt 2 * R₁ ≤ margB ξ₁ α q := by rw [← hpq]; exact hcl
    rw [hpq]
    have hne : margB ξ₁ α q ≠ 0 := by
      have h1 : 0 < Real.sqrt 2 * R₁ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR₁
      linarith [hcl']
    rw [sub_self, norm_zero, div_self hne, Real.log_one, mul_zero]

/-- The `A`-margin in the flat region `0 ≤ y ≤ D` (with `(1/α).im = -D`). -/
lemma margA_eval_flat (ξ : ℝ) (α : ℂ) (D x y : ℝ) (hd : (1/α).im = -D)
    (hy0 : 0 ≤ y) (hyD : y ≤ D) :
    margA ξ α ((x:ℂ) + (y:ℂ)*Complex.I) = x - ξ + (1/α).re + D - y := by
  rw [margA_eval, hd, abs_of_nonpos (by linarith : y + -D ≤ 0)]
  ring

/-- **Diagonal (up-left) piece** from `x₀ + i y₀` to `x₀ - t + i (y₀ + t)`, `y₀ ≥ 0`: `margB`
increases at double rate. -/
theorem dev_diag {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ x₀ y₀ t : ℝ}
    (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hdiff : DifferentiableOn ℂ Φ (Qm ξ₁ α)) (hcont : ContinuousOn (deriv Φ) (Qm ξ₁ α))
    (hy₀ : 0 ≤ y₀) (ht : 0 < t)
    (hminA : ∀ u ∈ Set.Icc (0:ℝ) 1, margB ξ₁ α ((x₀ - u*t:ℝ) + ((y₀ + u*t):ℝ)*Complex.I)
      ≤ margA ξ₁ α ((x₀ - u*t:ℝ) + ((y₀ + u*t):ℝ)*Complex.I))
    (hcl : Real.sqrt 2 * R₁ ≤ margB ξ₁ α ((x₀:ℂ) + (y₀:ℂ)*Complex.I)) :
    ‖(Φ (((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I)
          - (((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I))
        - (Φ ((x₀:ℂ) + (y₀:ℂ)*Complex.I) - ((x₀:ℂ) + (y₀:ℂ)*Complex.I))‖ ≤
      C₂ * Real.log (margB ξ₁ α (((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I)
        / margB ξ₁ α ((x₀:ℂ) + (y₀:ℂ)*Complex.I)) := by
  set p : ℂ := (x₀:ℂ) + (y₀:ℂ)*Complex.I with hp
  set q : ℂ := ((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I with hq
  have hb : 0 < 2 * t := by linarith
  set m : ℝ → ℝ := fun s => margB ξ₁ α (p + s • (q - p)) with hm
  have hpt : ∀ s : ℝ, p + s • (q - p) = ((x₀ - s*t:ℝ):ℂ) + ((y₀ + s*t:ℝ):ℂ)*Complex.I := by
    intro s
    rw [show p + s • (q - p) = (((x₀:ℂ) + (y₀:ℂ)*Complex.I) + s •
      ((((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I) - ((x₀:ℂ) + (y₀:ℂ)*Complex.I))) from by
        rw [hp, hq]]
    rw [seg_point]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      zero_add]
    ring_nf
  have hbounded : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ y₀ + s*t := by
    intro s hs; nlinarith [hs.1, ht]
  have hmc : Continuous m := by
    rw [hm]; exact (segaux_continuous_margB ξ₁ α).comp (by fun_prop)
  have hp_e : margB ξ₁ α p = y₀ - ξ₁ - x₀ := by
    rw [show p = (x₀:ℂ) + (y₀:ℂ)*Complex.I from hp, margB_eval, abs_of_nonneg hy₀]
  have hq_e : margB ξ₁ α q = y₀ + t - ξ₁ - (x₀ - t) := by
    rw [show q = ((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I from hq, margB_eval,
      abs_of_nonneg (by linarith)]
  have haff : ∀ s ∈ Set.Icc (0:ℝ) 1, m s = margB ξ₁ α p + (2*t) * s := by
    intro s hs
    have h1 : m s = margB ξ₁ α (((x₀ - s*t:ℝ):ℂ) + ((y₀ + s*t:ℝ):ℂ)*Complex.I) := by
      simp only [hm]; congr 1; exact hpt s
    rw [h1, margB_eval, abs_of_nonneg (hbounded s hs), hp_e]
    ring
  have ha : 0 < margB ξ₁ α p := by
    have h1 : 0 < Real.sqrt 2 * R₁ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR₁
    linarith [hcl]
  have hminAm : ∀ s ∈ Set.Icc (0:ℝ) 1, m s ≤ margA ξ₁ α (p + s • (q - p)) := by
    intro s hs
    simp only [hm]
    rw [hpt s]
    exact hminA s hs
  have hminBm : ∀ s ∈ Set.Icc (0:ℝ) 1, m s ≤ margB ξ₁ α (p + s • (q - p)) :=
    fun s hs => le_of_eq rfl
  have hseg : ∀ s ∈ Set.Icc (0:ℝ) 1, p + s • (q - p) ∈ Qm ξ₁ α := by
    intro s hs
    rw [mem_Qm_iff_marg]
    have hmb : 0 < margB ξ₁ α (p + s • (q - p)) := by
      have h2 : margB ξ₁ α p ≤ margB ξ₁ α (p + s • (q - p)) := by
        rw [hp_e, hpt s, margB_eval, abs_of_nonneg (hbounded s hs)]
        nlinarith [hs.1, ht]
      linarith [ha, h2]
    exact ⟨lt_of_lt_of_le hmb (hminAm s hs), hmb⟩
  have hcont' : ContinuousOn (deriv Φ)
      {z : ℂ | ∃ s ∈ Set.Icc (0:ℝ) 1, z = p + s • (q - p)} :=
    hcont.mono (fun z hz => by obtain ⟨s, hs, rfl⟩ := hz; exact hseg s hs)
  have hdiff' : ∀ s ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℂ Φ (p + s • (q - p)) := fun s hs =>
    (hdiff _ (hseg s hs)).differentiableAt ((isOpen_Qm_ ξ₁ α).mem_nhds (hseg s hs))
  have hres := dev_seg_affine (p := p) (q := q) (m := m) (a := margB ξ₁ α p) (b := 2*t)
    hR₁ hC₂ hder hmc ha hb hcl haff hminAm hminBm hcont' hdiff'
  have hnorm : ‖q - p‖ = Real.sqrt 2 * t := by
    have hqp : q - p = (-t : ℝ) + t*Complex.I := by
      rw [show q = ((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I from hq,
          show p = (x₀:ℂ) + (y₀:ℂ)*Complex.I from hp]
      push_cast; ring
    rw [hqp]
    have hnorm_pt : ‖((-t:ℝ):ℂ) + (t:ℝ)*Complex.I‖ = Real.sqrt 2 * t := by
      have hn : Complex.normSq ((-t:ℝ) + t*Complex.I) = 2*t*t := by
        simp [Complex.normSq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      have hsq : ‖((-t:ℝ):ℂ) + (t:ℝ)*Complex.I‖^2 = 2*t*t := by
        rw [Complex.sq_norm, hn]
      have hsqrt_eq : ‖((-t:ℝ):ℂ) + (t:ℝ)*Complex.I‖
          = Real.sqrt (2*t*t) := by
        rw [← Real.sqrt_sq (norm_nonneg _), hsq]
      rw [hsqrt_eq, show (2:ℝ)*t*t = 2*t^2 by ring,
        Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_sq (le_of_lt ht)]
    rw [hnorm_pt]
  have hratio : (margB ξ₁ α p + (2*t)) / margB ξ₁ α p = margB ξ₁ α q / margB ξ₁ α p := by
    rw [hp_e, hq_e]; ring
  have hsimple : Real.sqrt 2 * C₂ * (Real.sqrt 2 * t) *
      (Real.log (margB ξ₁ α q / margB ξ₁ α p) / (2*t))
      = C₂ * Real.log (margB ξ₁ α q / margB ξ₁ α p) := by
    have h2 : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)
    have hne : (2:ℝ)*t ≠ 0 := by positivity
    field_simp
    all_goals try (exact hne)
    rw [h2]; ring
  rw [hnorm, hratio, hsimple] at hres
  simpa [norm_sub_rev] using hres

/-- **Ridge piece** (in the flat region `0 ≤ y ≤ D`): moving along `(1,1)` keeps both margins
constant. -/
theorem dev_ridge {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ x₀ y₀ t D : ℝ}
    (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hdiff : DifferentiableOn ℂ Φ (Qm ξ₁ α)) (hcont : ContinuousOn (deriv Φ) (Qm ξ₁ α))
    (hd : (1/α).im = -D) (hy₀ : 0 ≤ y₀) (hyD : y₀ + t ≤ D) (ht : 0 < t)
    (hminA : margB ξ₁ α ((x₀:ℂ) + (y₀:ℂ)*Complex.I) ≤ margA ξ₁ α ((x₀:ℂ) + (y₀:ℂ)*Complex.I))
    (hcl : Real.sqrt 2 * R₁ ≤ margB ξ₁ α ((x₀:ℂ) + (y₀:ℂ)*Complex.I)) :
    ‖(Φ (((x₀ + t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I)
          - (((x₀ + t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I))
        - (Φ ((x₀:ℂ) + (y₀:ℂ)*Complex.I) - ((x₀:ℂ) + (y₀:ℂ)*Complex.I))‖
      ≤ 2 * C₂ * t / margB ξ₁ α ((x₀:ℂ) + (y₀:ℂ)*Complex.I) := by
  set p : ℂ := (x₀:ℂ) + (y₀:ℂ)*Complex.I with hp
  set q : ℂ := ((x₀ + t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I with hq
  set m : ℝ → ℝ := fun s => margB ξ₁ α (p + s • (q - p)) with hm
  have hpt : ∀ s : ℝ, p + s • (q - p) = ((x₀ + s*t:ℝ):ℂ) + ((y₀ + s*t:ℝ):ℂ)*Complex.I := by
    intro s
    rw [show p + s • (q - p) = (((x₀:ℂ) + (y₀:ℂ)*Complex.I) + s •
      ((((x₀ + t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I) - ((x₀:ℂ) + (y₀:ℂ)*Complex.I))) from by
        rw [hp, hq]]
    rw [seg_point]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      zero_add]
    ring_nf
  have hbounded : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ y₀ + s*t ∧ y₀ + s*t ≤ D := by
    intro s hs; constructor <;> nlinarith [hs.1, hs.2, ht, hy₀, hyD]
  have hmc : Continuous m := by
    rw [hm]; exact (segaux_continuous_margB ξ₁ α).comp (by fun_prop)
  have hp_e : margB ξ₁ α p = y₀ - ξ₁ - x₀ := by
    rw [show p = (x₀:ℂ) + (y₀:ℂ)*Complex.I from hp, margB_eval, abs_of_nonneg hy₀]
  have haff : ∀ s ∈ Set.Icc (0:ℝ) 1, m s = margB ξ₁ α p := by
    intro s hs
    have h1 : m s = margB ξ₁ α (((x₀ + s*t:ℝ):ℂ) + ((y₀ + s*t:ℝ):ℂ)*Complex.I) := by
      simp only [hm]; congr 1; exact hpt s
    rw [h1, margB_eval, abs_of_nonneg (hbounded s hs).1, hp_e]
    ring
  have hminAm : ∀ s ∈ Set.Icc (0:ℝ) 1, m s ≤ margA ξ₁ α (p + s • (q - p)) := by
    intro s hs
    have h1 : m s = margB ξ₁ α (((x₀ + s*t:ℝ):ℂ) + ((y₀ + s*t:ℝ):ℂ)*Complex.I) := by
      simp only [hm]; congr 1; exact hpt s
    rw [h1, hpt s, margB_eval, abs_of_nonneg (hbounded s hs).1]
    have h2 : margA ξ₁ α (((x₀ + s*t:ℝ):ℂ) + ((y₀ + s*t:ℝ):ℂ)*Complex.I)
        = (x₀ + s*t) - ξ₁ + (1/α).re + D - (y₀ + s*t) :=
      margA_eval_flat ξ₁ α D _ _ hd (hbounded s hs).1 (hbounded s hs).2
    rw [h2]
    have h3 : margB ξ₁ α p ≤ margA ξ₁ α ((x₀:ℂ) + (y₀:ℂ)*Complex.I) := hminA
    rw [hp_e] at h3
    rw [margA_eval_flat ξ₁ α D x₀ y₀ hd hy₀ (le_trans (le_add_of_nonneg_right (le_of_lt ht)) hyD)]
      at h3
    linarith
  have hminBm : ∀ s ∈ Set.Icc (0:ℝ) 1, m s ≤ margB ξ₁ α (p + s • (q - p)) :=
    fun s hs => le_of_eq rfl
  have ha : 0 < margB ξ₁ α p := by
    have h1 : 0 < Real.sqrt 2 * R₁ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR₁
    linarith [hcl]
  have hseg : ∀ s ∈ Set.Icc (0:ℝ) 1, p + s • (q - p) ∈ Qm ξ₁ α := by
    intro s hs
    rw [mem_Qm_iff_marg]
    have hmb : 0 < margB ξ₁ α (p + s • (q - p)) := by
      have h1 : margB ξ₁ α (p + s • (q - p)) = margB ξ₁ α p := haff s hs
      rw [h1]; exact ha
    exact ⟨lt_of_lt_of_le hmb (hminAm s hs), hmb⟩
  have hcont' : ContinuousOn (deriv Φ)
      {z : ℂ | ∃ s ∈ Set.Icc (0:ℝ) 1, z = p + s • (q - p)} :=
    hcont.mono (fun z hz => by obtain ⟨s, hs, rfl⟩ := hz; exact hseg s hs)
  have hdiff' : ∀ s ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℂ Φ (p + s • (q - p)) := fun s hs =>
    (hdiff _ (hseg s hs)).differentiableAt ((isOpen_Qm_ ξ₁ α).mem_nhds (hseg s hs))
  have hres := dev_seg_const (p := p) (q := q) (m := m) (a := margB ξ₁ α p)
    hR₁ hC₂ hder hmc ha hcl haff hminAm hminBm hcont' hdiff'
  have hnorm : ‖q - p‖ = Real.sqrt 2 * t := by
    have hqp : q - p = (t:ℝ) + t*Complex.I := by
      rw [show q = ((x₀ + t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I from hq,
          show p = (x₀:ℂ) + (y₀:ℂ)*Complex.I from hp]
      push_cast; ring
    rw [hqp]
    have hn : Complex.normSq ((t:ℝ) + t*Complex.I) = 2*t*t := by
      simp [Complex.normSq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    have hsq : ‖(t:ℝ) + t*Complex.I‖^2 = 2*t*t := by rw [Complex.sq_norm, hn]
    have hsqrt_eq : ‖(t:ℝ) + t*Complex.I‖ = Real.sqrt (2*t*t) := by
      rw [← Real.sqrt_sq (norm_nonneg _), hsq]
    rw [hsqrt_eq, show (2:ℝ)*t*t = 2*t^2 by ring,
      Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_sq (le_of_lt ht)]
  rw [hnorm, hp_e] at hres
  have hsimple : Real.sqrt 2 * C₂ * (Real.sqrt 2 * t) / (y₀ - ξ₁ - x₀)
      = 2 * C₂ * t / (y₀ - ξ₁ - x₀) := by
    have h2 : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)
    field_simp
    rw [h2]; ring
  rw [hsimple] at hres
  have hp_e' : margB ξ₁ α ((x₀:ℂ) + (y₀:ℂ)*Complex.I) = y₀ - ξ₁ - x₀ := by
    rw [margB_eval, abs_of_nonneg hy₀]
  rw [hp_e']
  exact hres

/-- **Diagonal (up-left) piece, `margA`-designated (past the ridge), in the flat region.** -/
theorem dev_diagA {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ x₀ y₀ t D : ℝ}
    (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hdiff : DifferentiableOn ℂ Φ (Qm ξ₁ α)) (hcont : ContinuousOn (deriv Φ) (Qm ξ₁ α))
    (hd : (1/α).im = -D) (hy₀ : 0 ≤ y₀) (hyD : y₀ + t ≤ D) (ht : 0 < t)
    (hminA : ∀ u ∈ Set.Icc (0:ℝ) 1, margA ξ₁ α ((x₀ - u*t:ℝ) + ((y₀ + u*t):ℝ)*Complex.I)
      ≤ margB ξ₁ α ((x₀ - u*t:ℝ) + ((y₀ + u*t):ℝ)*Complex.I))
    (hcl : Real.sqrt 2 * R₁ ≤ margA ξ₁ α (((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I)) :
    ‖(Φ (((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I)
          - (((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I))
        - (Φ ((x₀:ℂ) + (y₀:ℂ)*Complex.I) - ((x₀:ℂ) + (y₀:ℂ)*Complex.I))‖ ≤
      C₂ * Real.log (margA ξ₁ α ((x₀:ℂ) + (y₀:ℂ)*Complex.I)
        / margA ξ₁ α (((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I)) := by
  set p : ℂ := (x₀:ℂ) + (y₀:ℂ)*Complex.I with hp
  set q : ℂ := ((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I with hq
  have hb : 0 < 2 * t := by linarith
  set m : ℝ → ℝ := fun s => margA ξ₁ α (q + s • (p - q)) with hm
  have hpt : ∀ s : ℝ, q + s • (p - q) = ((x₀ - t + s*t:ℝ):ℂ) + ((y₀ + t - s*t:ℝ):ℂ)*Complex.I := by
    intro s
    rw [show q + s • (p - q) = ((((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I) + s •
      (((x₀:ℂ) + (y₀:ℂ)*Complex.I) - (((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I))) from by
        rw [hp, hq]]
    rw [seg_point]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      zero_add]
    ring_nf
  have hbounded : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ y₀ + t - s*t ∧ y₀ + t - s*t ≤ D := by
    intro s hs; constructor <;> nlinarith [hs.1, hs.2, ht, hy₀, hyD]
  have hmc : Continuous m := by
    rw [hm]; exact (segaux_continuous_margA ξ₁ α).comp (by fun_prop)
  have hq_e : margA ξ₁ α q = (x₀ - t) - ξ₁ + (1/α).re + D - (y₀ + t) :=
    margA_eval_flat ξ₁ α D (x₀ - t) (y₀ + t) hd (by linarith) hyD
  have hp_e : margA ξ₁ α p = x₀ - ξ₁ + (1/α).re + D - y₀ :=
    margA_eval_flat ξ₁ α D x₀ y₀ hd hy₀
      (le_trans (le_add_of_nonneg_right (le_of_lt ht)) hyD)
  have haff : ∀ s ∈ Set.Icc (0:ℝ) 1, m s = margA ξ₁ α q + (2*t) * s := by
    intro s hs
    have h1 : m s = margA ξ₁ α (((x₀ - t + s*t:ℝ):ℂ) + ((y₀ + t - s*t:ℝ):ℂ)*Complex.I) := by
      simp only [hm]; congr 1; exact hpt s
    rw [h1, margA_eval_flat ξ₁ α D _ _ hd (hbounded s hs).1 (hbounded s hs).2, hq_e]
    ring
  have ha : 0 < margA ξ₁ α q := by
    have h1 : 0 < Real.sqrt 2 * R₁ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR₁
    linarith [hcl]
  have hminAm : ∀ s ∈ Set.Icc (0:ℝ) 1, m s ≤ margA ξ₁ α (q + s • (p - q)) :=
    fun s hs => le_of_eq rfl
  have hminBm : ∀ s ∈ Set.Icc (0:ℝ) 1, m s ≤ margB ξ₁ α (q + s • (p - q)) := by
    intro s hs
    have h1 : m s = margA ξ₁ α (((x₀ - t + s*t:ℝ):ℂ) + ((y₀ + t - s*t:ℝ):ℂ)*Complex.I) := by
      simp only [hm]; congr 1; exact hpt s
    have hmem : (1 - s) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hs.1, hs.2]
    have h2 := hminA (1 - s) hmem
    rw [h1, hpt s]
    convert h2 using 2 <;> push_cast <;> ring
  have hseg : ∀ s ∈ Set.Icc (0:ℝ) 1, q + s • (p - q) ∈ Qm ξ₁ α := by
    intro s hs
    rw [mem_Qm_iff_marg]
    have hmb : 0 < margA ξ₁ α (q + s • (p - q)) := by
      have h2 : margA ξ₁ α q ≤ margA ξ₁ α (q + s • (p - q)) := by
        rw [hpt s, hq_e, margA_eval_flat ξ₁ α D _ _ hd (hbounded s hs).1 (hbounded s hs).2]
        nlinarith [hs.1, ht]
      linarith [ha, h2]
    exact ⟨hmb, lt_of_lt_of_le hmb (hminBm s hs)⟩
  have hcont' : ContinuousOn (deriv Φ)
      {z : ℂ | ∃ s ∈ Set.Icc (0:ℝ) 1, z = q + s • (p - q)} :=
    hcont.mono (fun z hz => by obtain ⟨s, hs, rfl⟩ := hz; exact hseg s hs)
  have hdiff' : ∀ s ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℂ Φ (q + s • (p - q)) := fun s hs =>
    (hdiff _ (hseg s hs)).differentiableAt ((isOpen_Qm_ ξ₁ α).mem_nhds (hseg s hs))
  have hres := dev_seg_affine (p := q) (q := p) (m := m) (a := margA ξ₁ α q) (b := 2*t)
    hR₁ hC₂ hder hmc ha hb hcl haff hminAm hminBm hcont' hdiff'
  have hnorm : ‖p - q‖ = Real.sqrt 2 * t := by
    have hpq : p - q = (t:ℝ) + (-t)*Complex.I := by
      rw [show q = ((x₀ - t:ℝ):ℂ) + ((y₀ + t:ℝ):ℂ)*Complex.I from hq,
          show p = (x₀:ℂ) + (y₀:ℂ)*Complex.I from hp]
      push_cast; ring
    rw [hpq]
    have hn : Complex.normSq ((t:ℝ) + (-t)*Complex.I) = 2*t*t := by
      simp [Complex.normSq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    have hsq : ‖(t:ℝ) + (-t)*Complex.I‖^2 = 2*t*t := by rw [Complex.sq_norm, hn]
    have hsqrt_eq : ‖(t:ℝ) + (-t)*Complex.I‖ = Real.sqrt (2*t*t) := by
      rw [← Real.sqrt_sq (norm_nonneg _), hsq]
    rw [hsqrt_eq, show (2:ℝ)*t*t = 2*t^2 by ring,
      Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_sq (le_of_lt ht)]
  have hratio : (margA ξ₁ α q + (2*t)) / margA ξ₁ α q
      = margA ξ₁ α p / margA ξ₁ α q := by
    rw [hq_e, hp_e]; ring
  have hsimple : Real.sqrt 2 * C₂ * (Real.sqrt 2 * t) *
      (Real.log (margA ξ₁ α p / margA ξ₁ α q) / (2*t))
      = C₂ * Real.log (margA ξ₁ α p / margA ξ₁ α q) := by
    have h2 : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)
    have hne : (2:ℝ)*t ≠ 0 := by positivity
    field_simp
    all_goals try (exact hne)
    rw [h2]; ring
  rw [hnorm, hratio, hsimple] at hres
  simpa [norm_sub_rev] using hres

/-- **Initial up-left move across the axis** (from `a + i b` with `b ≤ 0` to `(a+b) + 0i`):
`margB` is constant along it. -/
theorem dev_phase0 {Φ : ℂ → ℂ} {α : ℂ} {ξ₁ C₂ R₁ a b : ℝ}
    (hR₁ : 0 < R₁) (hC₂ : 0 ≤ C₂)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hdiff : DifferentiableOn ℂ Φ (Qm ξ₁ α)) (hcont : ContinuousOn (deriv Φ) (Qm ξ₁ α))
    (hb : b ≤ 0)
    (hminA : ∀ u ∈ Set.Icc (0:ℝ) 1, margB ξ₁ α ((a + u*b:ℝ) + ((b - u*b):ℝ)*Complex.I)
      ≤ margA ξ₁ α ((a + u*b:ℝ) + ((b - u*b):ℝ)*Complex.I))
    (hcl : Real.sqrt 2 * R₁ ≤ margB ξ₁ α ((a:ℂ) + (b:ℂ)*Complex.I)) :
    ‖(Φ (((a + b:ℝ):ℂ)) - (((a + b:ℝ):ℂ)))
        - (Φ ((a:ℂ) + (b:ℂ)*Complex.I) - ((a:ℂ) + (b:ℂ)*Complex.I))‖
      ≤ 2 * C₂ * (-b) / margB ξ₁ α ((a:ℂ) + (b:ℂ)*Complex.I) := by
  set p : ℂ := (a:ℂ) + (b:ℂ)*Complex.I with hp
  set q : ℂ := ((a + b:ℝ):ℂ) with hq
  set m : ℝ → ℝ := fun s => margB ξ₁ α (p + s • (q - p)) with hm
  have hpt : ∀ s : ℝ, p + s • (q - p) = ((a + s*b:ℝ):ℂ) + ((b - s*b:ℝ):ℂ)*Complex.I := by
    intro s
    rw [show p + s • (q - p) = (((a:ℂ) + (b:ℂ)*Complex.I) + s •
      ((((a + b:ℝ):ℂ)) - ((a:ℂ) + (b:ℂ)*Complex.I))) from by rw [hp, hq]]
    rw [seg_point]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      zero_add]
    ring_nf
  have hbounded : ∀ s ∈ Set.Icc (0:ℝ) 1, b - s*b ≤ 0 := by
    intro s hs; nlinarith [hs.1, hs.2, hb]
  have hmc : Continuous m := by
    rw [hm]; exact (segaux_continuous_margB ξ₁ α).comp (by fun_prop)
  have hp_e : margB ξ₁ α p = -b - ξ₁ - a := by
    rw [show p = (a:ℂ) + (b:ℂ)*Complex.I from hp, margB_eval, abs_of_nonpos hb]
  have haff : ∀ s ∈ Set.Icc (0:ℝ) 1, m s = margB ξ₁ α p := by
    intro s hs
    have h1 : m s = margB ξ₁ α (((a + s*b:ℝ):ℂ) + ((b - s*b:ℝ):ℂ)*Complex.I) := by
      simp only [hm]; congr 1; exact hpt s
    rw [h1, margB_eval, abs_of_nonpos (hbounded s hs), hp_e]
    ring
  have ha : 0 < margB ξ₁ α p := by
    have h1 : 0 < Real.sqrt 2 * R₁ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR₁
    linarith [hcl]
  have hminAm : ∀ s ∈ Set.Icc (0:ℝ) 1, m s ≤ margA ξ₁ α (p + s • (q - p)) := by
    intro s hs
    have h1 : m s = margB ξ₁ α (((a + s*b:ℝ):ℂ) + ((b - s*b:ℝ):ℂ)*Complex.I) := by
      simp only [hm]; congr 1; exact hpt s
    rw [h1, hpt s]
    exact hminA s hs
  have hminBm : ∀ s ∈ Set.Icc (0:ℝ) 1, m s ≤ margB ξ₁ α (p + s • (q - p)) :=
    fun s hs => le_of_eq rfl
  have hseg : ∀ s ∈ Set.Icc (0:ℝ) 1, p + s • (q - p) ∈ Qm ξ₁ α := by
    intro s hs
    rw [mem_Qm_iff_marg]
    have hmb : 0 < margB ξ₁ α (p + s • (q - p)) := by
      have h1 : margB ξ₁ α (p + s • (q - p)) = margB ξ₁ α p := haff s hs
      rw [h1]; exact ha
    exact ⟨lt_of_lt_of_le hmb (hminAm s hs), hmb⟩
  have hcont' : ContinuousOn (deriv Φ)
      {z : ℂ | ∃ s ∈ Set.Icc (0:ℝ) 1, z = p + s • (q - p)} :=
    hcont.mono (fun z hz => by obtain ⟨s, hs, rfl⟩ := hz; exact hseg s hs)
  have hdiff' : ∀ s ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℂ Φ (p + s • (q - p)) := fun s hs =>
    (hdiff _ (hseg s hs)).differentiableAt ((isOpen_Qm_ ξ₁ α).mem_nhds (hseg s hs))
  have hres := dev_seg_const (p := p) (q := q) (m := m) (a := margB ξ₁ α p)
    hR₁ hC₂ hder hmc ha hcl haff hminAm hminBm hcont' hdiff'
  have hnorm : ‖q - p‖ = Real.sqrt 2 * (-b) := by
    have hqp : q - p = (b:ℝ) + (-b)*Complex.I := by
      rw [show q = ((a + b:ℝ):ℂ) from hq, show p = (a:ℂ) + (b:ℂ)*Complex.I from hp]
      push_cast; ring
    rw [hqp]
    have hn : Complex.normSq ((b:ℝ) + (-b)*Complex.I) = 2*b*b := by
      simp [Complex.normSq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    have hsq : ‖(b:ℝ) + (-b)*Complex.I‖^2 = 2*b*b := by rw [Complex.sq_norm, hn]
    have hsqrt_eq : ‖(b:ℝ) + (-b)*Complex.I‖ = Real.sqrt (2*b*b) := by
      rw [← Real.sqrt_sq (norm_nonneg _), hsq]
    have hb2 : (2:ℝ)*b*b = 2*(-b)^2 := by ring
    rw [hsqrt_eq, hb2, Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num),
      Real.sqrt_sq (by linarith : (0:ℝ) ≤ -b)]
  have hden : margB ξ₁ α ((a:ℂ) + (b:ℂ)*Complex.I) = -b - ξ₁ - a := by
    rw [margB_eval, abs_of_nonpos hb]
  rw [hnorm, hden] at hres
  have hsimple : Real.sqrt 2 * C₂ * (Real.sqrt 2 * (-b)) / (-b - ξ₁ - a)
      = 2 * C₂ * (-b) / (-b - ξ₁ - a) := by
    have h2 : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)
    field_simp
    ring_nf
    rw [h2]; ring
  rw [hsimple] at hres
  rw [hden]
  exact hres

/-- `√2 * R₁ ≤ M / 8` under the standing hypotheses. -/
lemma sqrt2_R1_le {M R₁ : ℝ} (hM : 8 ≤ M) (hR₁ : 0 < R₁) (hMR₁ : 16 * R₁ ≤ M) :
    Real.sqrt 2 * R₁ ≤ M / 8 := by
  have h2 : Real.sqrt 2 ≤ (2 : ℝ) := by
    have h4 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    rwa [show Real.sqrt 4 = (2:ℝ) by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h4
  have h3 : Real.sqrt 2 * R₁ ≤ 2 * R₁ := mul_le_mul_of_nonneg_right h2 (le_of_lt hR₁)
  linarith

/-- The `A`-margin of a point at or below the axis, in the case `(1/α).im = -D` with `D ≥ 0`. -/
lemma margA_eval_low (ξ : ℝ) (α : ℂ) (D x y : ℝ) (hd : (1/α).im = -D) (hy : y ≤ D) :
    margA ξ α ((x:ℂ) + (y:ℂ)*Complex.I) = x - ξ + (1/α).re + D - y := by
  rw [margA_eval, hd, abs_of_nonpos (by linarith : y + -D ≤ 0)]
  ring


/-- The function `y ↦ y - |y + t|` is nondecreasing. -/
lemma sub_abs_mono {t : ℝ} {a b : ℝ} (h : a ≤ b) : a - |a + t| ≤ b - |b + t| := by
  by_cases h1 : 0 ≤ a + t
  · by_cases h2 : 0 ≤ b + t
    · rw [abs_of_nonneg h1, abs_of_nonneg h2]; linarith
    · rw [abs_of_nonneg h1, abs_of_neg (not_le.mp h2)]; linarith
  · by_cases h2 : 0 ≤ b + t
    · rw [abs_of_neg (not_le.mp h1), abs_of_nonneg h2]; linarith
    · rw [abs_of_neg (not_le.mp h1), abs_of_neg (not_le.mp h2)]; linarith

/-- `margB - margA` at a point of the upper half plane, in coordinates. -/
lemma margB_sub_margA_eq (ξ : ℝ) (α : ℂ) (x y : ℝ) (hy : 0 ≤ y) :
    margB ξ α ((x : ℂ) + (y : ℂ) * Complex.I) - margA ξ α ((x : ℂ) + (y : ℂ) * Complex.I)
      = y - 2 * x - (1 / α).re - |y + (1 / α).im| := by
  rw [margB_eval, margA_eval, abs_of_nonneg hy]
  ring

/-- `√2 R ≤ 3 R + 2` for `R > 0`. -/
lemma sqrt2_mul_le_three_mul_add {R₁ : ℝ} (hR₁ : 0 < R₁) :
    Real.sqrt 2 * R₁ ≤ 3 * R₁ + 2 := by
  have h2 : Real.sqrt 2 ≤ (3 : ℝ) := by
    have h3 := Real.sqrt_le_sqrt (show (2:ℝ) ≤ 9 by norm_num)
    rwa [show Real.sqrt 9 = (3:ℝ) by
      rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h3
  nlinarith [hR₁]

/-- The gate is invariant under conjugation with `α` conjugated. -/
lemma margA_conj_eq (ξ : ℝ) (α : ℂ) (z : ℂ) : margA ξ (conj α) z = margA ξ α (conj z) := by
  rw [margA, margA]
  rw [show (1 / conj α) = conj (1 / α) from by rw [one_div, one_div, map_inv₀]]
  simp only [Complex.conj_re, Complex.conj_im]
  rw [show z.im + -(1 / α).im = -(-z.im + (1 / α).im) by ring, abs_neg]

lemma margB_conj_eq (ξ : ℝ) (α : ℂ) (z : ℂ) : margB ξ (conj α) z = margB ξ α (conj z) := by
  rw [margB, margB]
  simp only [Complex.conj_re, Complex.conj_im, abs_neg]

end

end Work.Pert
