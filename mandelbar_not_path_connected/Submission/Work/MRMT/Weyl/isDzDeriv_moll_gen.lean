import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Mollification commutes with the weak `∂`-derivative

We prove `Work.MRMT.Weyl.isDzDeriv_moll_gen`: if `k` is a weak (distributional) `∂`-derivative of
`u` (`Work.MRMT.IsDzDeriv u k`), then mollification against a smooth compactly supported real
kernel `ρ` produces a weak `∂`-derivative of the mollification,

`IsDzDeriv (ρ ⋆ u) (ρ ⋆ k)`.

The argument is the standard one for Weyl-type lemmas.  The mollification `ρ ⋆ u` is smooth, its
pointwise Wirtinger derivative can be written as `∂(ρ ⋆ u)(z) = ∫ t, ∂ρ(t) · u(z - t)` (differentiate
under the integral sign in the smooth factor `ρ`), and after the substitution `t ↦ z - w` and the
chain rule `∂(ρ(z - ·)) = -∂ρ(z - ·)` this becomes `-∫ w, u(w) ∂ψ(w)` for the test function
`ψ(w) = ρ(z - w)`.  The defining identity of `IsDzDeriv u k` tested against `ψ` turns this into
`∫ w, k(w) ρ(z - w) = (ρ ⋆ k)(z)`.  Composing with the integration-by-parts description
`IsDzDeriv v (∂v)` of smooth `v` (`isDzDeriv_dz`) and a pointwise congruence finishes the proof.
-/

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.Weyl

noncomputable section

open Work.MRMT

set_option maxHeartbeats 4000000

/-! ## Elementary facts about `∂` -/

/-- `∂` of a real-valued function, coerced to `ℂ`, computed from the real Fréchet derivative. -/
theorem moll_aux_dz_ofReal (φ : ℂ → ℝ) (z : ℂ) (h : DifferentiableAt ℝ φ z) :
    dz (fun w => (φ w : ℂ)) z
      = ((fderiv ℝ φ z 1 : ℂ) - Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2 := by
  have h1 : fderiv ℝ (fun w => (φ w : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ φ z) := by
    have h2 : HasFDerivAt (fun w => (φ w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ φ z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z h.hasFDerivAt
    exact h2.fderiv
  rw [dz, h1]
  simp

/-- Chain rule for `∂` under the reflection `y ↦ c - y`. -/
theorem moll_aux_dz_comp_sub (g : ℂ → ℂ) (c y : ℂ) (hg : DifferentiableAt ℝ g (c - y)) :
    dz (fun y => g (c - y)) y = - dz g (c - y) := by
  have hd : DifferentiableAt ℝ (fun y : ℂ => c - y) y := by fun_prop
  have h1 : HasFDerivAt (fun y : ℂ => g (c - y))
      ((fderiv ℝ g (c - y)).comp (fderiv ℝ (fun y : ℂ => c - y) y)) y :=
    hg.hasFDerivAt.comp y hd.hasFDerivAt
  have h2 : fderiv ℝ (fun y : ℂ => c - y) y = -1 := by
    rw [fderiv_const_sub]
    rw [show (fun y : ℂ => y) = id from rfl]
    rw [fderiv_id]
    rfl
  rw [dz, dz, h1.fderiv, h2]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg, one_apply_eq_self]
  ring

/-- `∂` of a `C^n` function (`n ≠ 0`) is continuous. -/
theorem moll_aux_continuous_dz {u : ℂ → ℂ} {n : WithTop ℕ∞} (hu : ContDiff ℝ n u)
    (hn : n ≠ 0) : Continuous (dz u) := by
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv hn
  unfold dz
  exact ((hd.clm_apply continuous_const).sub
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

/-- For a smooth function `u` (no support hypothesis is needed, since test functions are compactly
supported), the distributional `∂`-derivative of `u` is the pointwise Wirtinger derivative
`dz u`.  This is integration by parts in the two real directions `1` and `I`. -/
theorem isDzDeriv_dz {u : ℂ → ℂ} {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) (hn : n ≠ 0) :
    IsDzDeriv u (dz u) := by
  have hdzu_cont : Continuous (dz u) := moll_aux_continuous_dz hu hn
  refine ⟨hu.continuous.locallyIntegrable, hdzu_cont.locallyIntegrable, ?_⟩
  intro ψ
  set ψf : ℂ → ℂ := (ψ : ℂ → ℂ) with hψf
  have hψ_cont : Continuous ψf := by rw [hψf]; exact ψ.continuous
  have hψ_cs : HasCompactSupport ψf := by rw [hψf]; exact ψ.hasCompactSupport
  have hfψ_cont : Continuous (fun z => fderiv ℝ ψf z) := by
    rw [hψf]; exact ψ.contDiff.continuous_fderiv (by simp)
  have hfψ_diff : ∀ z, DifferentiableAt ℝ ψf z := by
    intro z; rw [hψf]; exact (ψ.contDiff.differentiable (by simp)).differentiableAt
  have hfψ_deriv_cs : HasCompactSupport (fun z => fderiv ℝ ψf z) := hψ_cs.fderiv ℝ
  have hfu_cont : Continuous (fun z => fderiv ℝ u z) := hu.continuous_fderiv hn
  have hfu_diff : ∀ z, DifferentiableAt ℝ u z := fun z => (hu.differentiable hn).differentiableAt
  have heval_cs (v : ℂ) : HasCompactSupport (fun z => fderiv ℝ ψf z v) :=
    hfψ_deriv_cs.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) (by simp)
  have hint_uψ : Integrable (fun z => u z * ψf z) :=
    Continuous.integrable_of_hasCompactSupport (hu.continuous.mul hψ_cont) hψ_cs.mul_left
  have hint_duψ (v : ℂ) : Integrable (fun z => fderiv ℝ u z v * ψf z) :=
    Continuous.integrable_of_hasCompactSupport
      ((hfu_cont.clm_apply continuous_const).mul hψ_cont) hψ_cs.mul_left
  have hint_udψ (v : ℂ) : Integrable (fun z => u z * fderiv ℝ ψf z v) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous.mul (hfψ_cont.clm_apply continuous_const)) (heval_cs v).mul_left
  have hIBP (v : ℂ) :
      ∫ z, u z * fderiv ℝ ψf z v = - ∫ z, fderiv ℝ u z v * ψf z :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure ℂ))
      (hint_duψ v) (hint_udψ v) (hint_uψ) (fun z _ => hfu_diff z) (fun z _ => hfψ_diff z)
  have hptL : (fun z => u z * dz ψf z) =
      (fun z => (u z * fderiv ℝ ψf z 1 - Complex.I * (u z * fderiv ℝ ψf z Complex.I)) *
        (2 : ℂ)⁻¹) := by
    funext z; simp only [dz]; ring
  have hptR : (fun z => dz u z * ψf z) =
      (fun z => (fderiv ℝ u z 1 * ψf z - Complex.I * (fderiv ℝ u z Complex.I * ψf z)) *
        (2 : ℂ)⁻¹) := by
    funext z; simp only [dz]; ring
  have hint1 : Integrable (fun z => u z * dz ψf z) := by
    rw [hptL]
    exact ((hint_udψ 1).sub ((hint_udψ Complex.I).const_mul Complex.I)).mul_const _
  have hint2 : Integrable (fun z => dz u z * ψf z) := by
    rw [hptR]
    exact ((hint_duψ 1).sub ((hint_duψ Complex.I).const_mul Complex.I)).mul_const _
  refine ⟨hint1, hint2, ?_⟩
  have hL : ∫ z, u z * dz ψf z =
      ((∫ z, u z * fderiv ℝ ψf z 1) - Complex.I * ∫ z, u z * fderiv ℝ ψf z Complex.I) *
        (2 : ℂ)⁻¹ := by
    rw [hptL, integral_mul_const,
      integral_sub (hint_udψ 1) ((hint_udψ Complex.I).const_mul Complex.I), integral_const_mul]
  have hR : ∫ z, dz u z * ψf z =
      ((∫ z, fderiv ℝ u z 1 * ψf z) - Complex.I * ∫ z, fderiv ℝ u z Complex.I * ψf z) *
        (2 : ℂ)⁻¹ := by
    rw [hptR, integral_mul_const,
      integral_sub (hint_duψ 1) ((hint_duψ Complex.I).const_mul Complex.I), integral_const_mul]
  rw [hL, hR, hIBP 1, hIBP Complex.I]
  ring

/-- The weak `∂`-derivative relation is insensitive to changing the representing function on the
nose. -/
theorem isDzDeriv_congr {f g g' : ℂ → ℂ} (h : IsDzDeriv f g) (hgg' : ∀ z, g z = g' z) :
    IsDzDeriv f g' := by
  refine ⟨h.1, h.2.1.congr (Filter.Eventually.of_forall (fun z => hgg' z)), ?_⟩
  intro φ
  obtain ⟨h1, h2, h3⟩ := h.2.2 φ
  refine ⟨h1, h2.congr (Filter.Eventually.of_forall (fun z => ?_)), ?_⟩
  · show g z * (φ : ℂ → ℂ) z = g' z * (φ : ℂ → ℂ) z
    rw [hgg' z]
  · rw [h3]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      show g z * (φ : ℂ → ℂ) z = g' z * (φ : ℂ → ℂ) z
      rw [hgg' z])

/-! ## The pointwise computation `∂(ρ ⋆ u) = ρ ⋆ k` -/

/-- **The heart of the argument.**  If `k` is the weak `∂`-derivative of `u`, then the pointwise
Wirtinger derivative of the mollification of `u` against `ρ` is the mollification of `k`. -/
theorem moll_aux_dz_eq {u k : ℂ → ℂ} (hu : Work.MRMT.IsDzDeriv u k) {ρ : ℂ → ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : HasCompactSupport ρ) (z : ℂ) :
    dz (moll ρ u) z = moll ρ k z := by
  let ρc : ℂ → ℂ := fun w => (ρ w : ℂ)
  have hρcN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρc := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (ρ w : ℂ))
    exact Complex.ofRealCLM.contDiff.comp hρ
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hρcs_c : HasCompactSupport ρc := hρs.comp_left (g := Complex.ofRealCLM) (by simp)
  have hfdρ_cont : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by simp)
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  -- the Fréchet derivative of the mollification, via differentiating in the smooth factor
  have hFd : HasFDerivAt (moll ρ u)
      ((fderiv ℝ ρ ⋆[ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ),
          (volume : Measure ℂ)] u) z) z := by
    have h := hρs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ1 hu.1 z
    simpa only [moll] using h
  have hKint : Integrable (fun t : ℂ =>
      (ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ) (fderiv ℝ ρ t))
        (u (z - t))) volume :=
    HasCompactSupport.convolutionExists_left (f := fderiv ℝ ρ) (g := u)
      (L := ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ))
      (hρs.fderiv ℝ) hfdρ_cont hu.1 z
  have hD1 : ((fderiv ℝ ρ ⋆[ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ),
        (volume : Measure ℂ)] u) z) 1 = ∫ t, ((fderiv ℝ ρ t) 1) • u (z - t) := by
    rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hKint]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  have hDI : ((fderiv ℝ ρ ⋆[ContinuousLinearMap.precompL ℂ (ContinuousLinearMap.lsmul ℝ ℝ),
        (volume : Measure ℂ)] u) z) Complex.I = ∫ t, ((fderiv ℝ ρ t) Complex.I) • u (z - t) := by
    rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hKint]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  have hA1cs : HasCompactSupport (fun t : ℂ => (fderiv ℝ ρ t) 1) :=
    (hρs.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L 1) (by simp)
  have hA1cont : Continuous (fun t : ℂ => (fderiv ℝ ρ t) 1) := hfdρ_cont.clm_apply continuous_const
  have hA1int : Integrable (fun t : ℂ => ((fderiv ℝ ρ t) 1) • u (z - t)) volume :=
    HasCompactSupport.convolutionExists_left (f := fun t : ℂ => (fderiv ℝ ρ t) 1) (g := u)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hA1cs hA1cont hu.1 z
  have hAIcs : HasCompactSupport (fun t : ℂ => (fderiv ℝ ρ t) Complex.I) :=
    (hρs.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L Complex.I) (by simp)
  have hAIcont : Continuous (fun t : ℂ => (fderiv ℝ ρ t) Complex.I) :=
    hfdρ_cont.clm_apply continuous_const
  have hAIint : Integrable (fun t : ℂ => ((fderiv ℝ ρ t) Complex.I) • u (z - t)) volume :=
    HasCompactSupport.convolutionExists_left (f := fun t : ℂ => (fderiv ℝ ρ t) Complex.I) (g := u)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hAIcs hAIcont hu.1 z
  -- `∂(ρ ⋆ u)(z) = ∫ t, ∂ρ(t) · u(z - t)`
  have hdzform : dz (moll ρ u) z = ∫ t, (dz ρc) t * u (z - t) := by
    rw [dz, hFd.fderiv, hD1, hDI]
    rw [← integral_const_mul, ← integral_sub hA1int (hAIint.const_mul Complex.I)]
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    dsimp only
    rw [show (dz ρc) t =
        ((fderiv ℝ ρ t 1 : ℂ) - Complex.I * (fderiv ℝ ρ t Complex.I : ℂ)) / 2 from
      moll_aux_dz_ofReal ρ t (hρ.differentiable (by simp)).differentiableAt]
    simp only [Complex.real_smul]
    ring
  rw [hdzform]
  -- substitute `t ↦ z - w` in the integral
  have hsub : ∫ t, (dz ρc) t * u (z - t) = ∫ w, (dz ρc) (z - w) * u w := by
    have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) z).integral_comp
      (Homeomorph.measurableEmbedding (Homeomorph.subLeft z))
      (g := fun w : ℂ => (dz ρc) (z - w) * u w)
    simpa only [sub_sub_cancel] using h
  rw [hsub]
  -- the reflected kernel is a test function
  have hψcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => ρc (z - w)) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => z - w) := by fun_prop
    exact hρcN.comp h1
  have hψcs : HasCompactSupport (fun w : ℂ => ρc (z - w)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (fun w : ℂ => z - w) '' tsupport ρc) ?_ ?_
    · exact hρcs_c.isCompact.image (continuous_const.sub continuous_id)
    · intro w hw
      rw [Function.mem_support] at hw
      exact ⟨z - w, subset_tsupport ρc (fun hz => hw (by simp [hz])), by simp⟩
  let ψ : 𝓓(⊤, ℂ) := ⟨fun w : ℂ => ρc (z - w), hψcd, hψcs, fun _ _ => trivial⟩
  have hψcoe : (ψ : ℂ → ℂ) = fun w : ℂ => ρc (z - w) := rfl
  have hweak : ∫ w, u w * dz (ψ : ℂ → ℂ) w = - ∫ w, k w * (ψ : ℂ → ℂ) w := (hu.2.2 ψ).2.2
  -- the target integral is the mollification of `k`
  have hmollk : ∫ w, k w * ρc (z - w) = moll ρ k z := by
    have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) z).integral_comp
      (Homeomorph.measurableEmbedding (Homeomorph.subLeft z))
      (g := fun w : ℂ => ρc (z - w) * k w)
    simp only [sub_sub_cancel] at h
    rw [moll_apply, h]
    exact integral_congr_ae (Eventually.of_forall (fun w => mul_comm _ _))
  have hpt : ∀ w : ℂ, (dz ρc) (z - w) * u w = - (dz (ψ : ℂ → ℂ) w * u w) := by
    intro w
    have h1 : dz (ψ : ℂ → ℂ) w = -(dz ρc) (z - w) := by
      rw [hψcoe]
      exact moll_aux_dz_comp_sub ρc z w (hρcN.differentiable hne (z - w))
    rw [h1]; ring
  have e1 : ∫ w, (dz ρc) (z - w) * u w = ∫ w, - (dz (ψ : ℂ → ℂ) w * u w) :=
    integral_congr_ae (Eventually.of_forall hpt)
  have e2 : ∫ w, dz (ψ : ℂ → ℂ) w * u w = ∫ w, u w * dz (ψ : ℂ → ℂ) w :=
    integral_congr_ae (Eventually.of_forall (fun w => mul_comm _ _))
  have e3 : ∫ w, k w * (ψ : ℂ → ℂ) w = ∫ w, k w * ρc (z - w) :=
    integral_congr_ae (Eventually.of_forall (fun w => by rw [hψcoe]))
  rw [e1, integral_neg, e2, hweak, neg_neg, e3, hmollk]

/-! ## The main theorem -/

theorem isDzDeriv_moll_gen {u k : ℂ → ℂ} (hu : Work.MRMT.IsDzDeriv u k) {ρ : ℂ → ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρs : HasCompactSupport ρ) :
    Work.MRMT.IsDzDeriv (Work.MRMT.Weyl.moll ρ u) (Work.MRMT.Weyl.moll ρ k) := by
  have hloc : LocallyIntegrable u volume := hu.1
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (moll ρ u) := contDiff_moll hρ hρs hloc
  have hD : IsDzDeriv (moll ρ u) (dz (moll ρ u)) := isDzDeriv_dz hcd (by simp)
  exact isDzDeriv_congr hD (fun z => moll_aux_dz_eq hu hρ hρs z)

end

end Work.MRMT.Weyl
