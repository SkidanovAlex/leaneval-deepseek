import Mathlib
import Submission.Work.MRMT.Weyl.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Mollification preserves the weak Cauchy--Riemann equation

We prove `Work.MRMT.Weyl.isDbarDeriv_moll`: if `f` satisfies `∂̄ f = 0` in the distributional
sense (`IsDbarDeriv f 0`) then so does its mollification `ρ ⋆ f` against a real-valued kernel `ρ`.

The argument is the one used for Weyl's lemma: the molification `F = ρ ⋆ f` is smooth, and its
pointwise Wirtinger derivative can be written as the convolution of the smooth compactly supported
kernel `∂̄ρ` with `f`:

  `∂̄F(z) = ∫ t, ∂̄ρ(t) · f(z - t) dt`.

Substituting `t = z - u` and using the chain rule `∂̄(ρ(z - ·))(u) = -∂̄ρ(z - u)` turns this into
`-∫ u, f(u) · ∂̄ψ(u) du` for the test function `ψ(u) = ρ(z - u)`; the weak equation `∂̄f = 0`
tested against `ψ` makes this vanish.  Since `F` is smooth, `∂̄F` is continuous, so `∂̄F ≡ 0`
pointwise and `IsDbarDeriv F 0` follows from integration by parts (`isDbarDeriv_dzbar`).

Note that the kernel hypothesis `ContDiff ℝ ⊤ ρ` is real analyticity in Lean's order
`ℕ∞ω = WithTop ℕ∞` (not `C^∞`); the proof below only ever uses the `C^∞` information
`ContDiff ℝ ↑(⊤ : ℕ∞) ρ` extracted from it, so the result is the `n = ⊤` instance of the honest
statement for smooth kernels.
-/

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.Weyl

noncomputable section

open Work.MRMT

set_option maxHeartbeats 4000000 in
/-- `∂̄` of a real-valued function, coerced to `ℂ`, computed from the real Fréchet derivative. -/
theorem moll_aux_dzbar_ofReal (φ : ℂ → ℝ) (z : ℂ) (h : DifferentiableAt ℝ φ z) :
    dzbar (fun w => (φ w : ℂ)) z
      = ((fderiv ℝ φ z 1 : ℂ) + Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2 := by
  have h1 : fderiv ℝ (fun w => (φ w : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ φ z) := by
    have h2 : HasFDerivAt (fun w => (φ w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ φ z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z h.hasFDerivAt
    exact h2.fderiv
  rw [dzbar, h1]
  simp

/-- Chain rule for `∂̄` under the reflection `y ↦ c - y`. -/
theorem moll_aux_dzbar_comp_sub (g : ℂ → ℂ) (c y : ℂ) (hg : DifferentiableAt ℝ g (c - y)) :
    dzbar (fun y => g (c - y)) y = - dzbar g (c - y) := by
  have hd : DifferentiableAt ℝ (fun y : ℂ => c - y) y := by fun_prop
  have h1 : HasFDerivAt (fun y : ℂ => g (c - y))
      ((fderiv ℝ g (c - y)).comp (fderiv ℝ (fun y : ℂ => c - y) y)) y :=
    hg.hasFDerivAt.comp y hd.hasFDerivAt
  have h2 : fderiv ℝ (fun y : ℂ => c - y) y = -1 := by
    rw [fderiv_const_sub]
    rw [show (fun y : ℂ => y) = id from rfl]
    rw [fderiv_id]
    rfl
  rw [dzbar, dzbar, h1.fderiv, h2]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg, one_apply_eq_self]
  ring

/-- Substitution `t ↦ x - t` in a Lebesgue integral over `ℂ` (measure preserving). -/
theorem moll_aux_integral_comp_sub {g : ℂ → ℂ}
    (hg : AEStronglyMeasurable g (volume : Measure ℂ)) (x : ℂ) :
    ∫ t, g (x - t) = ∫ u, g u := by
  have hg' : AEStronglyMeasurable g (Measure.map (fun t : ℂ => x - t) (volume : Measure ℂ)) := by
    rwa [Measure.measurePreserving_sub_left (volume : Measure ℂ) x |>.map_eq]
  conv_rhs => rw [← Measure.measurePreserving_sub_left (volume : Measure ℂ) x |>.map_eq]
  rw [MeasureTheory.integral_map]
  · exact (continuous_const.sub continuous_id).aemeasurable
  · exact hg'

set_option maxHeartbeats 4000000 in
/-- `∂̄` of a `C^n` function (`n ≠ 0`) is continuous. -/
theorem moll_aux_continuous_dzbar {u : ℂ → ℂ} {n : WithTop ℕ∞} (hu : ContDiff ℝ n u)
    (hn : n ≠ 0) : Continuous (dzbar u) := by
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv hn
  unfold dzbar
  exact ((hd.clm_apply continuous_const).add
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

set_option maxHeartbeats 4000000 in
/-- **The heart of the argument.**  If `∂̄ f = 0` distributionally, then the pointwise Wirtinger
derivative of `f`'s mollification against `ρ` vanishes identically. -/
theorem moll_aux_dzbar_eq_zero {f : ℂ → ℂ} (hf : IsDbarDeriv f (fun _ => 0))
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ⊤ ρ) (hρcs : HasCompactSupport ρ) (z : ℂ) :
    dzbar (moll ρ f) z = 0 := by
  let ρc : ℂ → ℂ := fun w => (ρ w : ℂ)
  have hρc : ContDiff ℝ ⊤ ρc := by
    show ContDiff ℝ ⊤ (fun w => (ρ w : ℂ))
    exact Complex.ofRealCLM.contDiff.comp hρ
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hρcN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρc := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (ρ w : ℂ))
    exact Complex.ofRealCLM.contDiff.comp (hρ.of_le le_top)
  have hρcs_c : HasCompactSupport ρc := hρcs.comp_left (g := Complex.ofRealCLM) (by simp)
  have hfdρ_cont : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by simp)
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le le_top
  -- the Fréchet derivative of the mollification, via the convolution representation
  have hFd : HasFDerivAt (moll ρ f)
      ((fderiv ℝ ρ ⋆[ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ),
          (volume : Measure ℂ)] f) z) z := by
    have h := hρcs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ1 hf.1 z
    simpa only [moll] using h
  have hKint : Integrable (fun t : ℂ =>
      (ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ) (fderiv ℝ ρ t))
        (f (z - t))) volume :=
    HasCompactSupport.convolutionExists_left (f := fderiv ℝ ρ) (g := f)
      (L := ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ))
      (hρcs.fderiv ℝ) hfdρ_cont hf.1 z
  have hD1 : ((fderiv ℝ ρ ⋆[ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ),
        (volume : Measure ℂ)] f) z) 1 = ∫ t, ((fderiv ℝ ρ t) 1) • f (z - t) := by
    rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hKint]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  have hDI : ((fderiv ℝ ρ ⋆[ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ),
        (volume : Measure ℂ)] f) z) Complex.I = ∫ t, ((fderiv ℝ ρ t) Complex.I) • f (z - t) := by
    rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hKint]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  have hA1cs : HasCompactSupport (fun t : ℂ => (fderiv ℝ ρ t) 1) :=
    (hρcs.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L 1) (by simp)
  have hA1cont : Continuous (fun t : ℂ => (fderiv ℝ ρ t) 1) := hfdρ_cont.clm_apply continuous_const
  have hA1int : Integrable (fun t : ℂ => ((fderiv ℝ ρ t) 1) • f (z - t)) volume :=
    HasCompactSupport.convolutionExists_left (f := fun t : ℂ => (fderiv ℝ ρ t) 1) (g := f)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hA1cs hA1cont hf.1 z
  have hAIcs : HasCompactSupport (fun t : ℂ => (fderiv ℝ ρ t) Complex.I) :=
    (hρcs.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L Complex.I) (by simp)
  have hAIcont : Continuous (fun t : ℂ => (fderiv ℝ ρ t) Complex.I) :=
    hfdρ_cont.clm_apply continuous_const
  have hAIint : Integrable (fun t : ℂ => ((fderiv ℝ ρ t) Complex.I) • f (z - t)) volume :=
    HasCompactSupport.convolutionExists_left (f := fun t : ℂ => (fderiv ℝ ρ t) Complex.I) (g := f)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hAIcs hAIcont hf.1 z
  have hdzform : dzbar (moll ρ f) z = ∫ t, (dzbar ρc) t * f (z - t) := by
    rw [dzbar, hFd.fderiv, hD1, hDI]
    rw [← integral_const_mul, ← integral_add hA1int (hAIint.const_mul Complex.I)]
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    dsimp only
    rw [show (dzbar ρc) t =
        ((fderiv ℝ ρ t 1 : ℂ) + Complex.I * (fderiv ℝ ρ t Complex.I : ℂ)) / 2 from
      moll_aux_dzbar_ofReal ρ t (hρ.differentiable (by simp)).differentiableAt]
    simp only [Complex.real_smul]
    ring
  rw [hdzform]
  -- substitute `t ↦ z - u`
  have hsub : ∫ t, (dzbar ρc) t * f (z - t) = ∫ u, (dzbar ρc) (z - u) * f u := by
    have hcont : Continuous (dzbar ρc) := moll_aux_continuous_dzbar hρcN hne
    have hg : AEStronglyMeasurable (fun u : ℂ => (dzbar ρc) (z - u) * f u) volume :=
      (((hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
        hf.1.aestronglyMeasurable)
    have h2 := moll_aux_integral_comp_sub
      (g := fun u : ℂ => (dzbar ρc) (z - u) * f u) hg z
    simpa only [sub_sub_cancel] using h2
  rw [hsub]
  -- the reflected kernel is a test function
  have hψcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℂ => ρc (z - u)) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℂ => z - u) := by fun_prop
    exact hρcN.comp h1
  have hψcs : HasCompactSupport (fun u : ℂ => ρc (z - u)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (fun u : ℂ => z - u) '' tsupport ρc) ?_ ?_
    · exact hρcs_c.isCompact.image (continuous_const.sub continuous_id)
    · intro u hu
      rw [Function.mem_support] at hu
      exact ⟨z - u, subset_tsupport ρc (fun hz => hu (by simp [hz])), by simp⟩
  let ψ : 𝓓(⊤, ℂ) := ⟨fun u : ℂ => ρc (z - u), hψcd, hψcs, fun _ _ => trivial⟩
  have hψcoe : (ψ : ℂ → ℂ) = fun u : ℂ => ρc (z - u) := rfl
  have hweak : ∫ u, f u * dzbar (ψ : ℂ → ℂ) u = 0 := by
    have hw := (hf.2.2 ψ).2.2
    simpa using hw
  have hfin : ∫ u, (dzbar ρc) (z - u) * f u = 0 := by
    have hpt : ∀ u : ℂ, (dzbar ρc) (z - u) * f u = -((dzbar (ψ : ℂ → ℂ)) u * f u) := by
      intro u
      have h1 : (dzbar (ψ : ℂ → ℂ)) u = -(dzbar ρc) (z - u) := by
        rw [hψcoe]
        exact moll_aux_dzbar_comp_sub ρc z u (hρcN.differentiable hne (z - u))
      rw [h1]; ring
    rw [show (∫ u, (dzbar ρc) (z - u) * f u)
        = ∫ u, -((dzbar (ψ : ℂ → ℂ)) u * f u) from
      integral_congr_ae (Eventually.of_forall hpt)]
    rw [integral_neg]
    have h2 : ∫ u, dzbar (ψ : ℂ → ℂ) u * f u = 0 := by
      rw [show (fun u => dzbar (ψ : ℂ → ℂ) u * f u)
          = (fun u => f u * dzbar (ψ : ℂ → ℂ) u) from funext (fun u => mul_comm _ _)]
      exact hweak
    rw [h2, neg_zero]
  exact hfin

set_option maxHeartbeats 4000000 in
/-- If `f` satisfies the weak Cauchy--Riemann equation `∂̄ f = 0` in the distributional sense
(`IsDbarDeriv f 0`), then so does its mollification against any smooth compactly supported real
kernel `ρ`. Proof by Fubini: for a test function `ψ`,
`∫ (ρ ⋆ f)(z) ∂̄ψ(z) dz = ∫ ρ(y) (∫ f(w) ∂̄(ψ(· + y))(w) dw) dy = 0`,
using that `w ↦ ψ(w + y)` is again a test function and that `∂̄` commutes with translations. -/
theorem isDbarDeriv_moll {f : ℂ → ℂ} (hf : Work.MRMT.IsDbarDeriv f (fun _ => 0))
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ⊤ ρ) (hρcs : HasCompactSupport ρ) :
    Work.MRMT.IsDbarDeriv (Work.MRMT.Weyl.moll ρ f) (fun _ => 0) := by
  have hloc : LocallyIntegrable f volume := hf.1
  have hρN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := hρ.of_le le_top
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (moll ρ f) :=
    contDiff_moll (N := (⊤ : ℕ∞)) hρN hρcs hloc
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hD := isDbarDeriv_dzbar hcd hne
  have hz : dzbar (moll ρ f) = fun _ => 0 :=
    funext (fun z => moll_aux_dzbar_eq_zero hf hρ hρcs z)
  rw [hz] at hD
  exact hD

end

end Work.MRMT.Weyl
