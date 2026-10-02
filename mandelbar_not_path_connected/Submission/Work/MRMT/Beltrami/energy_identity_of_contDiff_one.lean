import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

noncomputable section
open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution Pointwise

namespace Work.MRMT.Beltrami

open Work.MRMT

/-!
# The energy identity `∫ ‖∂φ‖² = ∫ ‖∂̄φ‖²` for compactly supported `C¹` functions

Reduction of the `C¹` case to the `C²` case by mollification.  We convolve `φ` with a sequence of
normalised bump functions `ρₙ` whose outer radii tend to `0`.  The mollified functions
`φₙ = ρₙ * φ` are `C^∞` with compact support, so the energy identity holds for them by hypothesis.
Both `∂φₙ` and `∂̄φₙ` are the mollifications `ρₙ * ∂φ`, `ρₙ * ∂̄φ` of the continuous compactly
supported functions `∂φ`, `∂̄φ`, and mollification of a continuous compactly supported function
converges to it in `L²`; passing to the limit gives the identity for `φ`.
-/

/-- The bilinear map `(r, z) ↦ r • z` of real scalar multiplication on `ℂ`, a continuous
right-inverse-scalar-multiplication `lsmul` with its scalar field `ℝ` made explicit. -/
private def eL : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ

/-- `precompR` of `eL`: the bilinear map underlying `fderiv (ρ * φ) = ρ * fderiv φ`. -/
private def ePR : ℝ →L[ℝ] ((ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ)) :=
  ContinuousLinearMap.precompR ℂ eL

private lemma ePR_apply (r : ℝ) (ψ : ℂ →L[ℝ] ℂ) : ePR r ψ = (eL r).comp ψ := rfl

/-! ## The Wirtinger derivatives as continuous linear functionals of `fderiv ℝ f z` -/

private def edzCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) (2 : ℂ)⁻¹).comp
    (ContinuousLinearMap.apply ℝ ℂ (1:ℂ) -
      ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))

private def edzbarCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) (2 : ℂ)⁻¹).comp
    (ContinuousLinearMap.apply ℝ ℂ (1:ℂ) +
      ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))

private lemma edzCLM_apply (L : ℂ →L[ℝ] ℂ) :
    edzCLM L = (L 1 - Complex.I * L Complex.I) / 2 := by
  simp only [edzCLM, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.apply_apply]
  simp only [map_sub]; simp; ring

private lemma edzbarCLM_apply (L : ℂ →L[ℝ] ℂ) :
    edzbarCLM L = (L 1 + Complex.I * L Complex.I) / 2 := by
  simp only [edzbarCLM, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.apply_apply]
  simp only [map_add]; simp; ring

private lemma dz_eq_edzCLM (f : ℂ → ℂ) (z : ℂ) : dz f z = edzCLM (fderiv ℝ f z) := by
  rw [edzCLM_apply]; rfl

private lemma dzbar_eq_edzbarCLM (f : ℂ → ℂ) (z : ℂ) :
    dzbar f z = edzbarCLM (fderiv ℝ f z) := by
  rw [edzbarCLM_apply]; rfl

private lemma edzCLM_precompR (r : ℝ) (ψ : ℂ →L[ℝ] ℂ) :
    edzCLM ((ContinuousLinearMap.lsmul ℝ ℝ r).comp ψ) = (r : ℂ) * edzCLM ψ := by
  rw [edzCLM_apply, edzCLM_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply]
  rw [Complex.real_smul, Complex.real_smul]
  ring

private lemma edzbarCLM_precompR (r : ℝ) (ψ : ℂ →L[ℝ] ℂ) :
    edzbarCLM ((ContinuousLinearMap.lsmul ℝ ℝ r).comp ψ) = (r : ℂ) * edzbarCLM ψ := by
  rw [edzbarCLM_apply, edzbarCLM_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply]
  rw [Complex.real_smul, Complex.real_smul]
  ring

/-- The derivative of a mollification against a real kernel, in terms of the mollification of
the derivative: for a continuous linear functional `A` of the Fréchet derivative which is
`ℝ`-homogeneous (`A ((r •) ∘ ψ) = r * A ψ` for real `r`),
`A (fderiv ℝ (ρ * φ) z) = (ρ * (fun w => A (fderiv ℝ φ w))) z`. -/
private lemma edz_moll_eq (A : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ)
    (hA : ∀ (r : ℝ) (ψ : ℂ →L[ℝ] ℂ),
      A ((ContinuousLinearMap.lsmul ℝ ℝ r).comp ψ) = (r : ℂ) * A ψ)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hρcs : HasCompactSupport ρ)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hφcs : HasCompactSupport φ) (z : ℂ) :
    A (fderiv ℝ (Weyl.moll ρ φ) z) = Weyl.moll ρ (fun w => A (fderiv ℝ φ w)) z := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hρli : LocallyIntegrable ρ volume := hρ.continuous.locallyIntegrable
  have hfd_cont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hfd_cs : HasCompactSupport (fderiv ℝ φ) := hφcs.fderiv ℝ
  have hD : HasFDerivAt (Weyl.moll ρ φ) ((ρ ⋆[ePR, volume] fderiv ℝ φ) z) z :=
    HasCompactSupport.hasFDerivAt_convolution_right (L := eL) hφcs hρli hφ z
  have hInt : Integrable (fun t : ℂ => ePR (ρ t) (fderiv ℝ φ (z - t))) volume :=
    (HasCompactSupport.convolutionExists_right (μ := volume) (L := ePR)
      hfd_cs hρli hfd_cont) z
  have hkey : ∀ t : ℂ,
      A (ePR (ρ t) (fderiv ℝ φ (z - t))) = (ρ t : ℂ) * A (fderiv ℝ φ (z - t)) := by
    intro t
    rw [ePR_apply]
    exact hA (ρ t) (fderiv ℝ φ (z - t))
  calc A (fderiv ℝ (Weyl.moll ρ φ) z)
      = A ((ρ ⋆[ePR, volume] fderiv ℝ φ) z) := by rw [hD.fderiv]
    _ = A (∫ t, ePR (ρ t) (fderiv ℝ φ (z - t))) := by rw [MeasureTheory.convolution_def]
    _ = ∫ t, A (ePR (ρ t) (fderiv ℝ φ (z - t))) :=
          (ContinuousLinearMap.integral_comp_comm A hInt).symm
    _ = ∫ t, (ρ t : ℂ) * A (fderiv ℝ φ (z - t)) := by
          refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
          exact hkey t
    _ = Weyl.moll ρ (fun w => A (fderiv ℝ φ w)) z := by rw [Weyl.moll_apply]

/-- The `∂`-derivative of a mollification of a compactly supported `C¹` function is the
mollification of its `∂`-derivative. -/
private lemma dz_moll_eq {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρcs : HasCompactSupport ρ) {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hφcs : HasCompactSupport φ) :
    dz (Weyl.moll ρ φ) = Weyl.moll ρ (dz φ) := by
  funext z
  have hfun : (fun w => edzCLM (fderiv ℝ φ w)) = dz φ :=
    funext (fun w => (dz_eq_edzCLM φ w).symm)
  have h := edz_moll_eq edzCLM edzCLM_precompR hρ hρcs hφ hφcs z
  rw [hfun] at h
  rw [dz_eq_edzCLM (Weyl.moll ρ φ) z]
  exact h

/-- The `∂̄`-derivative of a mollification of a compactly supported `C¹` function is the
mollification of its `∂̄`-derivative. -/
private lemma dzbar_moll_eq {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρcs : HasCompactSupport ρ) {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hφcs : HasCompactSupport φ) :
    dzbar (Weyl.moll ρ φ) = Weyl.moll ρ (dzbar φ) := by
  funext z
  have hfun : (fun w => edzbarCLM (fderiv ℝ φ w)) = dzbar φ :=
    funext (fun w => (dzbar_eq_edzbarCLM φ w).symm)
  have h := edz_moll_eq edzbarCLM edzbarCLM_precompR hρ hρcs hφ hφcs z
  rw [hfun] at h
  rw [dzbar_eq_edzbarCLM (Weyl.moll ρ φ) z]
  exact h

/-- `∂f` is continuous as soon as `f` is `C^n` with `n ≠ 0`. -/
private lemma continuous_dz_of_contDiff {f : ℂ → ℂ} {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hc : ContDiff ℝ n f) : Continuous (dz f) := by
  have hd : Continuous (fderiv ℝ f) := hc.continuous_fderiv hn
  show Continuous (fun z : ℂ => (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2)
  exact ((hd.clm_apply continuous_const).sub
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

/-- `∂̄f` is continuous as soon as `f` is `C^n` with `n ≠ 0`. -/
private lemma continuous_dzbar_of_contDiff {f : ℂ → ℂ} {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hc : ContDiff ℝ n f) : Continuous (dzbar f) := by
  have hd : Continuous (fderiv ℝ f) := hc.continuous_fderiv hn
  show Continuous (fun z : ℂ => (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2)
  exact ((hd.clm_apply continuous_const).add
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

private lemma hasCompactSupport_moll {ρ : ℂ → ℝ} (hρ : HasCompactSupport ρ)
    {f : ℂ → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (Weyl.moll ρ f) :=
  HasCompactSupport.convolution (L := eL) hρ hf

/-- **Mollification of a continuous compactly supported function converges in `L²`.**

For `g : ℂ → ℂ` continuous with compact support and `ρₙ` the normalised bump functions of
`Work.MRMT.Weyl.bump` (whose outer radii tend to `0`), the squared `L²` norms of the mollifications
`ρₙ * g` converge to that of `g`. -/
private lemma tendsto_integral_normSq_moll (g : ℂ → ℂ) (hg : Continuous g)
    (hcs : HasCompactSupport g) :
    Tendsto (fun n : ℕ => ∫ z, ‖Weyl.moll ((Weyl.bump n).normed volume) g z‖ ^ 2 ∂volume)
      atTop (𝓝 (∫ z, ‖g z‖ ^ 2 ∂volume)) := by
  classical
  have hrOut_le : ∀ n : ℕ, (Weyl.bump n).rOut ≤ 1 := by
    intro n
    show (1:ℝ) / ((n:ℝ) + 1) ≤ 1
    rw [one_div]
    exact inv_le_one_of_one_le₀ (by simp)
  -- the compact set outside of which all mollifications vanish
  set K' : Set ℂ := Metric.closedBall (0:ℂ) 1 + tsupport g with hK'def
  have hK' : IsCompact K' := (isCompact_closedBall (0:ℂ) 1).add hcs.isCompact
  have hvanish : ∀ n z, z ∉ K' → Weyl.moll ((Weyl.bump n).normed volume) g z = 0 := by
    intro n z hz
    rw [Weyl.moll_apply]
    refine integral_eq_zero_of_ae (Eventually.of_forall (fun y => ?_))
    show (↑(((Weyl.bump n).normed volume) y) : ℂ) * g (z - y) = 0
    by_cases hy : ((Weyl.bump n).normed volume) y = 0
    · simp [hy]
    · have hyball : y ∈ Metric.ball (0:ℂ) (Weyl.bump n).rOut := by
        have h : y ∈ Function.support ((Weyl.bump n).normed volume) := hy
        rwa [ContDiffBump.support_normed_eq] at h
      have hyn : ‖y‖ < 1 := by
        have h1 : ‖y‖ < (Weyl.bump n).rOut := by
          simpa [Metric.mem_ball, dist_eq_norm] using hyball
        linarith [hrOut_le n]
      have hymem : y ∈ Metric.closedBall (0:ℂ) 1 := by
        simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hyn.le
      have hzy : z - y ∉ tsupport g := by
        intro hcon
        exact hz (by
          have hzeq : z = y + (z - y) := by ring
          rw [hzeq]
          exact Set.add_mem_add hymem hcon)
      rw [image_eq_zero_of_notMem_tsupport hzy, mul_zero]
  -- a slightly larger compact set, and a bound for `g` on it
  set K'' : Set ℂ := K' + Metric.closedBall (0:ℂ) 1 with hK''def
  have hK'' : IsCompact K'' := hK'.add (isCompact_closedBall (0:ℂ) 1)
  obtain ⟨C, hC⟩ := hK''.exists_bound_of_continuousOn hg.continuousOn
  set B : ℝ := max C 1 with hBdef
  have hCB : C ≤ B := le_max_left _ _
  have hgB : ∀ z ∈ K'', ‖g z‖ ≤ B := fun z hz => (hC z hz).trans hCB
  have hK'sub : K' ⊆ K'' := by
    intro z hz
    rw [hK''def]
    simpa using Set.add_mem_add hz
      (show (0:ℂ) ∈ Metric.closedBall (0:ℂ) 1 from Metric.mem_closedBall_self (by norm_num))
  have hmollB : ∀ n z, z ∈ K' → ‖Weyl.moll ((Weyl.bump n).normed volume) g z‖ ≤ 3 * B := by
    intro n z hz
    have hdist : dist (Weyl.moll ((Weyl.bump n).normed volume) g z) (g z) ≤ 2 * B := by
      have hmain := ContDiffBump.dist_normed_convolution_le (μ := volume) (φ := Weyl.bump n)
        (g := g) (x₀ := z) (ε := 2 * B) hg.aestronglyMeasurable ?_
      · simpa only [Weyl.moll] using hmain
      · intro x hx
        have hx1 : ‖x - z‖ < 1 := by
          have h2 : dist x z < (Weyl.bump n).rOut := hx
          rw [dist_eq_norm] at h2
          linarith [hrOut_le n]
        have hxK'' : x ∈ K'' := by
          rw [hK''def]
          have hxeq : x = z + (x - z) := by ring
          rw [hxeq]
          exact Set.add_mem_add hz (by
            simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hx1.le)
        calc dist (g x) (g z) ≤ ‖g x‖ + ‖g z‖ := dist_le_norm_add_norm _ _
          _ ≤ B + B := add_le_add (hgB x hxK'') (hgB z (hK'sub hz))
          _ = 2 * B := by ring
    calc ‖Weyl.moll ((Weyl.bump n).normed volume) g z‖
        = dist (Weyl.moll ((Weyl.bump n).normed volume) g z) 0 := by rw [dist_zero_right]
      _ ≤ dist (Weyl.moll ((Weyl.bump n).normed volume) g z) (g z) + dist (g z) 0 :=
          dist_triangle _ _ _
      _ = dist (Weyl.moll ((Weyl.bump n).normed volume) g z) (g z) + ‖g z‖ := by
          rw [dist_zero_right]
      _ ≤ 2 * B + B := add_le_add hdist (hgB z (hK'sub hz))
      _ = 3 * B := by ring
  have hbound_int : Integrable (K'.indicator (fun _ => (3 * B) ^ 2)) volume := by
    rw [integrable_indicator_iff hK'.measurableSet]
    exact integrableOn_const hK'.measure_lt_top.ne (by finiteness)
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun n z => ‖Weyl.moll ((Weyl.bump n).normed volume) g z‖ ^ 2)
    (f := fun z => ‖g z‖ ^ 2)
    (K'.indicator (fun _ => (3 * B) ^ 2)) ?_ ?_ hbound_int ?_
  · filter_upwards with n
    exact (((Weyl.contDiff_moll (N := (⊤ : ℕ∞))
      (ContDiffBump.contDiff_normed (n := (⊤ : ℕ∞)) (Weyl.bump n))
      (ContDiffBump.hasCompactSupport_normed (Weyl.bump n)) hg.locallyIntegrable).continuous).norm.pow 2).aestronglyMeasurable
  · filter_upwards with n
    filter_upwards with z
    by_cases hz : z ∈ K'
    · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hmollB n z hz) 2
    · rw [hvanish n z hz, Set.indicator_of_notMem hz]
      simp
  · filter_upwards with z
    have hconv := ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume) (φ := Weyl.bump) (g := g) Weyl.tendsto_rOut_bump hg z
    have hcont : Continuous (fun w : ℂ => ‖w‖ ^ 2) := by fun_prop
    have := (hcont.tendsto (g z)).comp hconv
    simpa only [Function.comp_def, Weyl.moll] using this

/-- The energy identity `∫ ‖∂φ‖² = ∫ ‖∂̄φ‖²` for compactly supported `C¹` functions, deduced from
the `C²` case by mollification. -/
theorem energy_identity_of_contDiff_one
    (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hsmooth : ∀ ψ : ℂ → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      ∫ z, ‖Work.MRMT.dz ψ z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ)
        = ∫ z, ‖Work.MRMT.dzbar ψ z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    ∫ z, ‖Work.MRMT.dz φ z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ)
      = ∫ z, ‖Work.MRMT.dzbar φ z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  have hdz_cont : Continuous (dz φ) := continuous_dz_of_contDiff (by norm_num) hφ
  have hdzbar_cont : Continuous (dzbar φ) := continuous_dzbar_of_contDiff (by norm_num) hφ
  have hdz_cs : HasCompactSupport (dz φ) := by
    have h := (hs.fderiv ℝ).comp_left (g := edzCLM) (by simp [edzCLM_apply])
    rwa [show (edzCLM ∘ (fderiv ℝ φ)) = dz φ from
      funext (fun z => (dz_eq_edzCLM φ z).symm)] at h
  have hdzbar_cs : HasCompactSupport (dzbar φ) := by
    have h := (hs.fderiv ℝ).comp_left (g := edzbarCLM) (by simp [edzbarCLM_apply])
    rwa [show (edzbarCLM ∘ (fderiv ℝ φ)) = dzbar φ from
      funext (fun z => (dzbar_eq_edzbarCLM φ z).symm)] at h
  have hlim1 := tendsto_integral_normSq_moll (dz φ) hdz_cont hdz_cs
  have hlim2 := tendsto_integral_normSq_moll (dzbar φ) hdzbar_cont hdzbar_cs
  have hcontdiff : ∀ n : ℕ,
      ContDiff ℝ 2 (Weyl.moll ((Weyl.bump n).normed volume) φ) := fun n =>
    (Weyl.contDiff_moll (N := (⊤ : ℕ∞))
      (ContDiffBump.contDiff_normed (n := (⊤ : ℕ∞)) (Weyl.bump n))
      (ContDiffBump.hasCompactSupport_normed (Weyl.bump n))
      hφ.continuous.locallyIntegrable).of_le (by simp)
  have hsupp : ∀ n : ℕ, HasCompactSupport (Weyl.moll ((Weyl.bump n).normed volume) φ) := fun n =>
    hasCompactSupport_moll (ContDiffBump.hasCompactSupport_normed (Weyl.bump n)) hs
  have hsm : ∀ n : ℕ,
      ∫ z, ‖dz (Weyl.moll ((Weyl.bump n).normed volume) φ) z‖ ^ 2 ∂volume
        = ∫ z, ‖dzbar (Weyl.moll ((Weyl.bump n).normed volume) φ) z‖ ^ 2 ∂volume :=
    fun n => hsmooth _ (hcontdiff n) (hsupp n)
  have hkey1 : ∀ n : ℕ,
      ∫ z, ‖dz (Weyl.moll ((Weyl.bump n).normed volume) φ) z‖ ^ 2 ∂volume
        = ∫ z, ‖Weyl.moll ((Weyl.bump n).normed volume) (dz φ) z‖ ^ 2 ∂volume := by
    intro n
    rw [dz_moll_eq (ContDiffBump.contDiff_normed (n := (⊤ : ℕ∞)) (Weyl.bump n))
      (ContDiffBump.hasCompactSupport_normed (Weyl.bump n)) hφ hs]
  have hkey2 : ∀ n : ℕ,
      ∫ z, ‖dzbar (Weyl.moll ((Weyl.bump n).normed volume) φ) z‖ ^ 2 ∂volume
        = ∫ z, ‖Weyl.moll ((Weyl.bump n).normed volume) (dzbar φ) z‖ ^ 2 ∂volume := by
    intro n
    rw [dzbar_moll_eq (ContDiffBump.contDiff_normed (n := (⊤ : ℕ∞)) (Weyl.bump n))
      (ContDiffBump.hasCompactSupport_normed (Weyl.bump n)) hφ hs]
  have ht1 : Tendsto
      (fun n : ℕ => ∫ z, ‖dz (Weyl.moll ((Weyl.bump n).normed volume) φ) z‖ ^ 2 ∂volume)
      atTop (𝓝 (∫ z, ‖dz φ z‖ ^ 2 ∂volume)) :=
    hlim1.congr' (Eventually.of_forall (fun n => (hkey1 n).symm))
  have ht2 : Tendsto
      (fun n : ℕ => ∫ z, ‖dzbar (Weyl.moll ((Weyl.bump n).normed volume) φ) z‖ ^ 2 ∂volume)
      atTop (𝓝 (∫ z, ‖dzbar φ z‖ ^ 2 ∂volume)) :=
    hlim2.congr' (Eventually.of_forall (fun n => (hkey2 n).symm))
  have ht2' : Tendsto
      (fun n : ℕ => ∫ z, ‖dz (Weyl.moll ((Weyl.bump n).normed volume) φ) z‖ ^ 2 ∂volume)
      atTop (𝓝 (∫ z, ‖dzbar φ z‖ ^ 2 ∂volume)) :=
    ht2.congr' (Eventually.of_forall (fun n => (hsm n).symm))
  exact tendsto_nhds_unique ht1 ht2'

end Work.MRMT.Beltrami
