/-
# Openness of the set of "good" values of the modular lambda function

`FiberGood w` (see `Submission/Work/Rigidity/LambdaFiberDefs.lean`) says that the fibre of the
modular lambda function `λ = θ₁₀⁴/θ₀₀⁴` over `w` is a single `Γ(2)`-orbit.  This file proves
that `{w | FiberGood w}` is open at every `w ∉ {0,1}`: the fibres of nearby values are again
single orbits.

The argument is the standard one.

* Let `A = {τ ∈ FDom | λ τ = w}` be the fibre of `w` inside the fundamental domain.  It is
  finite (`lambda_fiber_finite`) and, by hypothesis, contained in a single `Γ(2)`-orbit.
* Fix `ρ₀ ∈ A` and a radius `r > 0` on which `λ` is injective (`λ` is a local biholomorphism,
  `lambda_local_injective_aux` below).  For `ρ ∈ A` let `g ρ ∈ Γ(2)` with `g ρ • ρ = ρ₀`.
* Since the action of `Γ(2)` on `ℍ` is continuous, `g ρ` maps a small ball around `ρ` into the
  injectivity ball `B (ρ₀, r)`; a finite minimum over `A` gives a single radius `η > 0` working
  for all `ρ ∈ A`.
* By `lambda_fiber_close`, for `w'` close enough to `w` every point `σ ∈ FDom` with `λ σ = w'`
  is within `η` of some `ρ ∈ A`.  Then `g ρ • σ ∈ B (ρ₀, r)` and `λ (g ρ • σ) = w'`, so by
  injectivity of `λ` on `B (ρ₀, r)` all those transported points coincide: two fibre points of
  `w'` inside `FDom` are always `Γ(2)`-conjugate.
* Reducing an arbitrary fibre point of `w'` into `FDom` (`lambda_fdom_reduction`) and using the
  `Γ(2)`-invariance of `λ` gives the same for arbitrary fibre points, i.e. `FiberGood w'`.

If the fibre of `w` does not meet `FDom` at all, then by `lambda_fiber_close` neither does the
fibre of any nearby value, and `FiberGood` holds vacuously.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaFiberDefs
import Submission.Work.Rigidity.lambda_fiber_close
import Submission.Work.Rigidity.lambda_fiber_finite
import Submission.Work.Rigidity.lambda_local_inverse
import Submission.Work.Rigidity.lambda_fdom_reduction

namespace Work.Rigidity

open UpperHalfPlane ModularGroup Matrix Filter Topology
open scoped MatrixGroups

noncomputable section

open Work.Kernels Work.Kernels.LogLambda

/-! ## Local injectivity of `λ` -/

/-- **`λ` is locally injective.**  Since `λ` is a local biholomorphism (its derivative
`λ' = c λ (1 - λ) θ₀₀⁴` vanishes nowhere with `c ≠ 0`, `exists_rho_const`, `LambdaDerivDefs`),
the analytic inverse function theorem gives a local inverse of `λ` whose values form a left
inverse of `λ` near any given point. -/
private lemma lambda_local_injective_aux (τ₀ : ℍ) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ τ' : ℍ, dist (τ : ℂ) (τ₀ : ℂ) < r →
      dist (τ' : ℂ) (τ₀ : ℂ) < r → lambdaFun τ = lambdaFun τ' → τ = τ' := by
  obtain ⟨c, hc⟩ := exists_rho_const
  have hc0 : c ≠ 0 := rho_const_ne_zero hc
  set z₀ : ℂ := (τ₀ : ℂ) with hz₀
  have hz₀pos : 0 < z₀.im := τ₀.im_pos
  have hderiv : deriv lamC z₀ ≠ 0 := by
    rw [deriv_lamC_eq_const hc z₀ hz₀pos]
    exact mul_ne_zero hc0 (rhoC_denom_ne_zero z₀ hz₀pos)
  have hAna : AnalyticAt ℂ lamC z₀ :=
    differentiableOn_lamC.analyticAt (isOpen_U.mem_nhds hz₀pos)
  set φ : ℂ → ℂ := HasStrictDerivAt.localInverse lamC (deriv lamC z₀) z₀
    hAna.hasStrictDerivAt hderiv with hφdef
  have hleft : ∀ᶠ z in 𝓝 z₀, φ (lamC z) = z :=
    hAna.hasStrictDerivAt.eventually_left_inverse hderiv
  obtain ⟨v, hv, hball⟩ := Filter.Eventually.exists_mem hleft
  obtain ⟨r, hr, hrv⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨r, hr, ?_⟩
  intro τ τ' hτ hτ' heq
  have hmem : ∀ σ : ℍ, dist (σ : ℂ) z₀ < r → φ (lamC (σ : ℂ)) = (σ : ℂ) :=
    fun σ hσ => hball _ (hrv (by simpa [hz₀] using hσ))
  have h1 : φ (lamC (τ : ℂ)) = (τ : ℂ) := hmem τ (by simpa [hz₀] using hτ)
  have h2 : φ (lamC (τ' : ℂ)) = (τ' : ℂ) := hmem τ' (by simpa [hz₀] using hτ')
  rw [lamC_coe τ] at h1
  rw [lamC_coe τ'] at h2
  have : (τ : ℂ) = (τ' : ℂ) := by rw [← h1, ← h2, heq]
  exact UpperHalfPlane.ext this

/-! ## Openness -/

theorem fiberGood_open (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (h : Work.Rigidity.FiberGood w) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w' : ℂ, ‖w' - w‖ < ε → Work.Rigidity.FiberGood w' := by
  -- the fibre of `w` inside the fundamental domain
  set A : Set ℍ := {τ : ℍ | τ ∈ FDom ∧ lambdaFun τ = w} with hAdef
  have hAfin : A.Finite := lambda_fiber_finite w hw0 hw1
  by_cases hAne : A.Nonempty
  · -- main case: the fibre of `w` meets `FDom`
    obtain ⟨ρ₀, hρ₀A⟩ := hAne
    obtain ⟨r, hrpos, hrinj⟩ := lambda_local_injective_aux ρ₀
    -- transport every point of `A` to `ρ₀`
    have hg : ∀ ρ : ℍ, ∃ γ : SL(2, ℤ),
        ρ ∈ A → γ ∈ CongruenceSubgroup.Gamma 2 ∧ γ • ρ = ρ₀ := by
      intro ρ
      by_cases hρ : ρ ∈ A
      · obtain ⟨γ, hγ, hγeq⟩ := h ρ ρ₀ hρ.2 hρ₀A.2
        exact ⟨γ, fun _ => ⟨hγ, hγeq⟩⟩
      · exact ⟨1, fun hc => absurd hc hρ⟩
    choose g hgprop using hg
    -- continuity of the action at each point of `A`
    have hcont : ∀ ρ : ℍ, ∃ δ : ℝ, ρ ∈ A → 0 < δ ∧ ∀ τ : ℍ,
        dist (τ : ℂ) (ρ : ℂ) < δ →
        dist ((((g ρ) • τ : ℍ)) : ℂ) (ρ₀ : ℂ) < r := by
      intro ρ
      by_cases hρ : ρ ∈ A
      · have hc1 : Continuous fun τ : ℍ => (g ρ) • τ := by
          simpa only [sl_moeb] using continuous_const_smul (g ρ : GL (Fin 2) ℝ)
        have hc : Continuous fun τ : ℍ => ((((g ρ) • τ : ℍ)) : ℂ) :=
          UpperHalfPlane.continuous_coe.comp hc1
        have hval : (fun τ : ℍ => ((((g ρ) • τ : ℍ)) : ℂ)) ρ = (ρ₀ : ℂ) := by
          show ((((g ρ) • ρ : ℍ)) : ℂ) = (ρ₀ : ℂ)
          rw [(hgprop ρ hρ).2]
        have hpre : (fun τ : ℍ => ((((g ρ) • τ : ℍ)) : ℂ)) ⁻¹'
            (Metric.ball (ρ₀ : ℂ) r) ∈ 𝓝 ρ := by
          have h1 : Metric.ball (ρ₀ : ℂ) r ∈
              𝓝 ((fun τ : ℍ => ((((g ρ) • τ : ℍ)) : ℂ)) ρ) := by
            rw [hval]
            exact Metric.ball_mem_nhds (ρ₀ : ℂ) hrpos
          exact hc.continuousAt h1
        rw [UpperHalfPlane.isEmbedding_coe.isInducing.nhds_eq_comap, Filter.mem_comap] at hpre
        obtain ⟨S, hS, hSsub⟩ := hpre
        obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp hS
        refine ⟨δ, fun _ => ⟨hδpos, fun τ hτ => ?_⟩⟩
        have hτS : (τ : ℂ) ∈ S := hδball (by rw [Metric.mem_ball]; exact hτ)
        exact hSsub hτS
      · exact ⟨1, fun hc => absurd hc hρ⟩
    choose δ hδ using hcont
    -- a single radius working for every `ρ ∈ A`
    obtain ⟨η, hηpos, hηle⟩ : ∃ η : ℝ, 0 < η ∧ ∀ ρ ∈ A, η ≤ δ ρ := by
      have hne' : (hAfin.toFinset.image δ).Nonempty :=
        ⟨δ ρ₀, Finset.mem_image.mpr ⟨ρ₀, (hAfin.mem_toFinset).mpr hρ₀A, rfl⟩⟩
      refine ⟨(hAfin.toFinset.image δ).min' hne', ?_, ?_⟩
      · obtain ⟨ρ, hρs, hρeq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne')
        rw [← hρeq]
        exact (hδ ρ ((hAfin.mem_toFinset).mp hρs)).1
      · intro ρ hρA
        exact Finset.min'_le _ _
          (Finset.mem_image.mpr ⟨ρ, (hAfin.mem_toFinset).mpr hρA, rfl⟩)
    obtain ⟨ε, hεpos, hε⟩ := lambda_fiber_close w hw0 hw1 η hηpos
    refine ⟨ε, hεpos, fun w' hw' => ?_⟩
    by_cases hfib : ∃ σ : ℍ, σ ∈ FDom ∧ lambdaFun σ = w'
    · -- every fibre point of `w'` inside `FDom` is `Γ(2)`-conjugate to any other
      have hpair : ∀ σ σ' : ℍ, σ ∈ FDom → σ' ∈ FDom → lambdaFun σ = w' →
          lambdaFun σ' = w' → ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • σ' = σ := by
        intro σ σ' hσFD hσ'FD hσw' hσ'w'
        obtain ⟨ρ, hρFD, hρw, hρdist⟩ := hε w' hw' σ hσFD hσw'
        obtain ⟨ρ', hρ'FD, hρ'w, hρ'dist⟩ := hε w' hw' σ' hσ'FD hσ'w'
        have hρA : ρ ∈ A := ⟨hρFD, hρw⟩
        have hρ'A : ρ' ∈ A := ⟨hρ'FD, hρ'w⟩
        have hfar : dist ((((g ρ) • σ : ℍ)) : ℂ) (ρ₀ : ℂ) < r := by
          refine (hδ ρ hρA).2 σ ?_
          rw [dist_comm]
          exact lt_of_lt_of_le hρdist (hηle ρ hρA)
        have hfar' : dist ((((g ρ') • σ' : ℍ)) : ℂ) (ρ₀ : ℂ) < r := by
          refine (hδ ρ' hρ'A).2 σ' ?_
          rw [dist_comm]
          exact lt_of_lt_of_le hρ'dist (hηle ρ' hρ'A)
        have heq : (g ρ) • σ = (g ρ') • σ' := by
          refine hrinj ((g ρ) • σ) ((g ρ') • σ') hfar hfar' ?_
          rw [lambdaFun_gamma2_invariant (g ρ) (hgprop ρ hρA).1 σ,
            lambdaFun_gamma2_invariant (g ρ') (hgprop ρ' hρ'A).1 σ', hσw', hσ'w']
        refine ⟨(g ρ)⁻¹ * (g ρ'), mul_mem (inv_mem (hgprop ρ hρA).1) (hgprop ρ' hρ'A).1, ?_⟩
        rw [mul_smul, ← heq, inv_smul_smul]
      -- an arbitrary fibre point of `w'`
      intro τ τ' hτ hτ'
      obtain ⟨γ₁, hγ₁, h1FD⟩ := lambda_fdom_reduction τ
      obtain ⟨γ₂, hγ₂, h2FD⟩ := lambda_fdom_reduction τ'
      have hlam1 : lambdaFun (γ₁ • τ) = w' := by
        rw [lambdaFun_gamma2_invariant γ₁ hγ₁ τ, hτ]
      have hlam2 : lambdaFun (γ₂ • τ') = w' := by
        rw [lambdaFun_gamma2_invariant γ₂ hγ₂ τ', hτ']
      obtain ⟨γ, hγ, hγeq⟩ := hpair (γ₁ • τ) (γ₂ • τ') h1FD h2FD hlam1 hlam2
      have htau : τ = (γ₁⁻¹ * γ * γ₂) • τ' := by
        rw [mul_smul, mul_smul, hγeq, inv_smul_smul]
      refine ⟨γ₂⁻¹ * γ⁻¹ * γ₁, mul_mem (mul_mem (inv_mem hγ₂) (inv_mem hγ)) hγ₁, ?_⟩
      rw [htau, ← mul_smul,
        show (γ₂⁻¹ * γ⁻¹ * γ₁) * (γ₁⁻¹ * γ * γ₂) = 1 by group, one_smul]
    · -- the fibre of `w'` is empty: vacuous
      intro τ τ' hτ _
      obtain ⟨γ, hγ, hγFD⟩ := lambda_fdom_reduction τ
      exact absurd ⟨γ • τ, hγFD, by rw [lambdaFun_gamma2_invariant γ hγ τ, hτ]⟩ hfib
  · -- degenerate case: the fibre of `w` is empty, hence so is that of every nearby `w'`
    obtain ⟨ε, hεpos, hε⟩ := lambda_fiber_close w hw0 hw1 1 one_pos
    refine ⟨ε, hεpos, fun w' hw' => ?_⟩
    intro τ τ' hτ _
    obtain ⟨γ, hγ, hγFD⟩ := lambda_fdom_reduction τ
    have hlam : lambdaFun (γ • τ) = w' := by rw [lambdaFun_gamma2_invariant γ hγ τ, hτ]
    obtain ⟨ρ, hρFD, hρw, _⟩ := hε w' hw' (γ • τ) hγFD hlam
    exact absurd ⟨ρ, hρFD, hρw⟩ hAne

end

end Work.Rigidity
