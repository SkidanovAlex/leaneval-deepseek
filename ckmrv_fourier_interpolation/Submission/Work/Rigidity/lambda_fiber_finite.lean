/-
# Finiteness of the fibres of `λ` over `ℂ ∖ {0,1}` inside the fundamental domain

The modular lambda function `λ = θ₁₀⁴/θ₀₀⁴ = Work.Kernels.lambdaFun` takes the value `w`
only finitely often on the closed fundamental domain
`FDom = {τ | |Re τ| ≤ 1, ‖τ‖² ≥ |Re τ|}` of `Γ(2)`, for every `w ∉ {0,1}`.

The proof has three ingredients.

* **Containment in a compact piece of `FDom`.**  A point `τ ∈ FDom` with `λ τ = w ≠ 0` cannot
  have large imaginary part (`λ → 0` at the cusp `i∞`, `lambdaFun_norm_lt_of_im_large`), and
  since `w ≠ 1` it cannot approach the real axis either (`λ → 1` at the cusp `0` and
  `|λ| → ∞` at the cusps `±1`, giving the lower bound `FDom_im_lower_bound`).  Hence the
  fibre lies in `KF δ (max R 1 + 1)`, which is compact and contained in `ℍ`.
* **Isolation of the fibre points.**  `λ` is a local biholomorphism
  (`lambda_local_injective_aux`, obtained from the classical identity
  `λ' = c λ (1-λ) θ₀₀⁴` with `c ≠ 0` proved in `lambda_local_inverse`), so two distinct points
  of the fibre cannot be arbitrarily close: every fibre point is isolated.
* **Compactness.**  An infinite fibre would therefore give a sequence of distinct points in the
  compact set `KF δ (max R 1 + 1)`; a convergent subsequence would have a limit `p` with
  `λ p = w` (continuity of `λ`), and local injectivity at `p` would force two distinct terms of
  the subsequence to be equal -- a contradiction.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaFiberDefs
import Submission.Work.Rigidity.lambda_fdom_reduction
import Submission.Work.Rigidity.lambdaFun_div_qParam_tendsto
import Submission.Work.Rigidity.lambdaFun_eq_lambdaSeries
import Submission.Work.Rigidity.lambda_local_surjective
import Submission.Work.Rigidity.lambda_local_inverse
import Submission.Work.Rigidity.lambda_fiber_close

namespace Work.Rigidity

open UpperHalfPlane ModularGroup Matrix Filter Topology
open scoped MatrixGroups

noncomputable section

open Work.Kernels Work.Kernels.LogLambda

/-! ## Local injectivity of `λ` -/

/-- **`λ` is locally injective.**  Since `λ` is a local biholomorphism (its derivative
`λ' = c λ (1 - λ) θ₀₀⁴` vanishes nowhere, `c ≠ 0`), every point of `ℍ` has a neighbourhood on
which `λ` is injective.  Explicitly: the local inverse `φ` of `λ` at `τ₀` provided by the
strict differentiability of `λ` at `τ₀` satisfies `φ (λ z) = z` near `τ₀`. -/
private lemma lambda_local_injective_aux (τ₀ : ℍ) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ : ℍ, dist (τ : ℂ) (τ₀ : ℂ) < r →
      ∀ τ' : ℍ, dist (τ' : ℂ) (τ₀ : ℂ) < r → lambdaFun τ = lambdaFun τ' → τ = τ' := by
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
  intro τ hτ τ' hτ' heq
  have hmem : ∀ σ : ℍ, dist (σ : ℂ) z₀ < r → φ (lamC (σ : ℂ)) = (σ : ℂ) :=
    fun σ hσ => hball _ (hrv (by simpa [hz₀] using hσ))
  have h1 : φ (lamC (τ : ℂ)) = (τ : ℂ) := hmem τ (by simpa [hz₀] using hτ)
  have h2 : φ (lamC (τ' : ℂ)) = (τ' : ℂ) := hmem τ' (by simpa [hz₀] using hτ')
  rw [lamC_coe τ] at h1
  rw [lamC_coe τ'] at h2
  have : (τ : ℂ) = (τ' : ℂ) := by rw [← h1, ← h2, heq]
  exact UpperHalfPlane.ext this

/-! ## Finiteness of the fibre -/

theorem lambda_fiber_finite (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    {τ : UpperHalfPlane | τ ∈ Work.Rigidity.FDom ∧ Work.Kernels.lambdaFun τ = w}.Finite := by
  set S : Set ℍ := {τ : ℍ | τ ∈ FDom ∧ lambdaFun τ = w} with hSdef
  by_contra hSfin
  have hSinf : S.Infinite := hSfin
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  -- a fibre point cannot go to the cusp `i∞` ...
  obtain ⟨R, hR⟩ := lambdaFun_norm_lt_of_im_large (‖w‖/2) (by linarith)
  -- ... nor to the real axis (cusps `0`, `±1`)
  obtain ⟨d, hdpos, δ, hδpos, hlow⟩ := FDom_im_lower_bound w hw0 hw1
  have him_lt_R : ∀ τ : ℍ, τ ∈ S → τ.im < R := by
    intro τ hτ
    by_contra hcon
    push_neg at hcon
    have h1 := hR τ hcon
    rw [hτ.2] at h1
    linarith
  have him_ge_δ : ∀ τ : ℍ, τ ∈ S → δ ≤ τ.im := by
    intro τ hτ
    have h1 : ‖lambdaFun τ - w‖ < d := by rw [hτ.2, sub_self, norm_zero]; exact hdpos
    exact hlow τ hτ.1 h1
  -- so the fibre is contained in a compact piece of `ℍ`
  have hmemK : ∀ τ : ℍ, τ ∈ S → (τ : ℂ) ∈ KF δ (max R 1 + 1) := by
    intro τ hτ
    refine ⟨hτ.1.1, ?_, ?_, ?_⟩
    · rw [Complex.normSq_eq_norm_sq]; exact hτ.1.2
    · rw [UpperHalfPlane.coe_im]; exact him_ge_δ τ hτ
    · rw [UpperHalfPlane.coe_im]
      have h1 := him_lt_R τ hτ
      have h2 : R ≤ max R 1 + 1 := by linarith [le_max_left R 1]
      linarith
  -- an infinite fibre gives an injective sequence in the compact set
  let e : ℕ ↪ S := Set.Infinite.natEmbedding S hSinf
  let τ : ℕ → ℍ := fun n => (e n : S)
  have hτmem : ∀ n, τ n ∈ S := fun n => (e n).2
  have hτinj : Function.Injective τ := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  obtain ⟨p, hpK, ψ, hψmono, hψtend⟩ :=
    (isCompact_KF δ (max R 1 + 1)).tendsto_subseq
      (x := fun n => ((τ n : ℍ) : ℂ)) (fun n => hmemK (τ n) (hτmem n))
  have hppos : 0 < p.im := lt_of_lt_of_le hδpos hpK.2.2.1
  -- the limit point is again a fibre point, by continuity of `λ`
  have hpFD : (⟨p, hppos⟩ : ℍ) ∈ FDom := by
    show |p.re| ≤ 1 ∧ ‖p‖ ^ 2 ≥ |p.re|
    exact ⟨hpK.1, by simpa [Complex.normSq_eq_norm_sq] using hpK.2.1⟩
  have hcont : ContinuousAt lamC p :=
    ((differentiableOn_lamC.continuousOn).continuousAt (isOpen_U.mem_nhds hppos))
  have hlimL : Tendsto (fun k => lamC (((τ (ψ k)) : ℍ) : ℂ)) atTop (𝓝 (lamC p)) :=
    (hcont.tendsto.comp hψtend).congr (fun k => rfl)
  have hlimR : Tendsto (fun k => lamC (((τ (ψ k)) : ℍ) : ℂ)) atTop (𝓝 w) :=
    (tendsto_const_nhds (x := w)).congr (fun k => by
      show w = lamC (((τ (ψ k)) : ℍ) : ℂ)
      rw [lamC_coe (τ (ψ k)), (hτmem (ψ k)).2])
  have hwp : lamC p = w := tendsto_nhds_unique hlimL hlimR
  have hlam_tp : lambdaFun (⟨p, hppos⟩ : ℍ) = w := by
    rw [← lamC_coe (⟨p, hppos⟩ : ℍ)]
    exact hwp
  -- but local injectivity at the limit point forbids two distinct sequence terms
  obtain ⟨r, hrpos, hinj⟩ := lambda_local_injective_aux (⟨p, hppos⟩ : ℍ)
  have hev : ∀ᶠ k in atTop,
      dist (((τ (ψ k)) : ℍ) : ℂ) (((⟨p, hppos⟩ : ℍ)) : ℂ) < r := by
    filter_upwards [hψtend.eventually (Metric.ball_mem_nhds p hrpos)] with k hk
    exact Metric.mem_ball.mp hk
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 hev
  have hclose : ∀ k : ℕ, k₀ ≤ k →
      dist (((τ (ψ k)) : ℍ) : ℂ) (((⟨p, hppos⟩ : ℍ)) : ℂ) < r :=
    fun k hk => hk₀ k hk
  have hdistp : dist (((⟨p, hppos⟩ : ℍ)) : ℂ) (((⟨p, hppos⟩ : ℍ)) : ℂ) < r := by
    rw [dist_self]; exact hrpos
  have hz1 : τ (ψ k₀) = (⟨p, hppos⟩ : ℍ) :=
    hinj (τ (ψ k₀)) (hclose k₀ le_rfl) (⟨p, hppos⟩ : ℍ) hdistp
      (by rw [(hτmem (ψ k₀)).2, hlam_tp])
  have hz2 : τ (ψ (k₀ + 1)) = (⟨p, hppos⟩ : ℍ) :=
    hinj (τ (ψ (k₀ + 1))) (hclose (k₀ + 1) (by omega)) (⟨p, hppos⟩ : ℍ) hdistp
      (by rw [(hτmem (ψ (k₀ + 1))).2, hlam_tp])
  have h1 : ψ k₀ = ψ (k₀ + 1) := hτinj (hz1.trans hz2.symm)
  have h2 : k₀ = k₀ + 1 := hψmono.injective h1
  omega

end

end Work.Rigidity
