import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.chart_of_good_mem
import Submission.Work.WilE7.CoreStep.localEmbedding_of_injective_strictFDeriv
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv

set_option autoImplicit false

namespace Work.WilE7.Endgame

open Filter Topology
open WilkiesDesign WilkiesDesign.E

/-! ## G2, the local injectivity step

Let `S : Stratum 0 M` be a `Good` absolute stratum, `z ∈ S.X.set`, and let
`A : ℝ^{0+M} →ₗ[ℝ] ℝ^r` be a linear map that is injective on the tangent space
`ker (jac S z)` of `S` at `z`.  Then `A` is injective on `S.X.set` near `z`.

The proof does not need `hdim` (nor a chart of the stratum): consider the map

`ζ w = (eqn w, A w)`,  `eqn w a = eaEval S.X.c (S.h a) w`,

from `ℝ^{S.j} × ℝ^r` to `ℝ^{0+M}`.  Its derivative at `z` is `(jac S z).prod A`, which is injective
by hypothesis, hence (finite-dimensional codomain) admits a continuous linear left inverse `Q`.
Strict differentiability of `eqn` (it is analytic, `eaEval` being analytic) and linearity of `A`
give the hypotheses of `Work.WilE7.CoreStep.localEmbedding_of_injective_strictFDeriv`, so `ζ` is
injective on a neighbourhood `W` of `z`.  Finally, on `S.X.set` the first component `eqn` vanishes
by `S.Good`, so two points of `S.X.set ∩ W` with the same image under `A` have the same image under
`ζ`, hence are equal. -/

theorem g2_injOn_of_kjac_inj {M r : ℕ} (S : WilkiesDesign.E.Stratum 0 M)
    (hS : S.Good) (A : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    (z : Fin (0 + M) → ℝ) (hz : z ∈ S.X.set)
    (hdim : r = M - S.j)
    (hinj : ∀ ξ ∈ LinearMap.ker (Work.WilE7.MainDesign.jac S z), A ξ = 0 → ξ = 0) :
    ∃ O ∈ nhds z, ∀ y₁ ∈ S.X.set ∩ O, ∀ y₂ ∈ S.X.set ∩ O, A y₁ = A y₂ → y₁ = y₂ := by
  classical
  -- the equation map of `S` and its derivative `jac S z`
  set F : (Fin (0 + M) → ℝ) → (Fin S.j → ℝ) := fun w a => eaEval S.X.c (S.h a) w with hF
  -- `A` and the product `(jac S z, A)`, as continuous linear maps
  set A' : (Fin (0 + M) → ℝ) →L[ℝ] (Fin r → ℝ) := LinearMap.toContinuousLinearMap A with hA'
  set L : (Fin (0 + M) → ℝ) →L[ℝ] ((Fin S.j → ℝ) × (Fin r → ℝ)) :=
    (Work.WilE7.MainDesign.jac S z).toContinuousLinearMap.prod A' with hL
  have hA'_apply : ∀ ξ, A' ξ = A ξ := by
    intro ξ
    rw [hA', LinearMap.coe_toContinuousLinearMap']
  have hL_apply : ∀ ξ, L ξ = ((Work.WilE7.MainDesign.jac S z) ξ, A ξ) := by
    intro ξ
    rw [hL, ContinuousLinearMap.prod_apply, hA'_apply, LinearMap.coe_toContinuousLinearMap']
  -- the linear map `(jac S z, A)` is injective: `hinj` plus the first component
  have hL_inj : Function.Injective L := by
    intro ξ η hξη
    have h0 : L (ξ - η) = 0 := by rw [map_sub, hξη, sub_self]
    have h1 : (Work.WilE7.MainDesign.jac S z) (ξ - η) = 0 := by
      have h := congrArg Prod.fst h0
      rw [hL_apply (ξ - η)] at h
      simpa using h
    have h2 : A (ξ - η) = 0 := by
      have h := congrArg Prod.snd h0
      rw [hL_apply (ξ - η)] at h
      simpa using h
    have h3 : ξ - η = 0 := hinj (ξ - η) (by rw [LinearMap.mem_ker]; exact h1) h2
    exact sub_eq_zero.mp h3
  -- `ζ = (F, A)` is strictly differentiable at `z` with derivative `L`
  have hFdiff : HasStrictFDerivAt F ((Work.WilE7.MainDesign.jac S z).toContinuousLinearMap) z := by
    have hF_an : AnalyticAt ℝ F z := by
      rw [hF]
      exact AnalyticAt.pi fun a => Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) z
    have h := hF_an.hasStrictFDerivAt
    have hder : fderiv ℝ F z = (Work.WilE7.MainDesign.jac S z).toContinuousLinearMap := by
      rw [hF, Work.WilE7.DimAPI.jac_eq_fderiv S z]
      ext v
      simp
    rwa [hder] at h
  have hφ : HasStrictFDerivAt (fun w => (F w, A' w)) L z := by
    have h := hFdiff.prodMk A'.hasStrictFDerivAt
    rwa [← hL] at h
  -- an injective linear map into a finite-dimensional space has a continuous left inverse
  obtain ⟨Q, hQ⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hL_inj
  have hQc : Q.comp L = ContinuousLinearMap.id ℝ (Fin (0 + M) → ℝ) :=
    ContinuousLinearMap.ext fun ξ => hQ ξ
  -- hence `ζ` is injective near `z`
  obtain ⟨W, hW, rr, hrc, hrv⟩ :=
    Work.WilE7.CoreStep.localEmbedding_of_injective_strictFDeriv
      (fun w => (F w, A' w)) L z hφ Q hQc
  refine ⟨W, hW, ?_⟩
  intro y₁ hy₁ y₂ hy₂ hAy
  -- on `S.X.set` the equation map vanishes, so `ζ` remembers only `A`
  have hF1 : F y₁ = 0 := by
    rw [hF]
    funext a
    exact (hS y₁ hy₁.1).1 a
  have hF2 : F y₂ = 0 := by
    rw [hF]
    funext a
    exact (hS y₂ hy₂.1).1 a
  have hA'12 : A' y₁ = A' y₂ := by rw [hA'_apply, hA'_apply, hAy]
  have hpair : (F y₁, A' y₁) = (F y₂, A' y₂) := by rw [hF1, hF2, hA'12]
  calc y₁ = rr (F y₁, A' y₁) := (hrv y₁ hy₁.2).symm
    _ = rr (F y₂, A' y₂) := by rw [hpair]
    _ = y₂ := hrv y₂ hy₂.2

end Work.WilE7.Endgame
