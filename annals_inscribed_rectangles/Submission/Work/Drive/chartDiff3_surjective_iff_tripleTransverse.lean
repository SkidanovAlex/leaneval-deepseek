import Mathlib
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.TripleGeneral
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.ChartDeriv

/-!
# The charted difference map of three chains: the linear identification at a triple point

This file supplies the helpers for `Work.Drive.chartDiff3_surjective_iff_tripleTransverse`, the
statement that the surjectivity of the charted difference map of three chains at a triple point is
*equivalent* to the transversality (`Work.Drive.TripleTransverse`) of the three intrinsic derivatives.
The `⟸` half is `Work.Drive.TParity.chartDiff3_surj` in `TParity/ChartDeriv.lean`; here we prove the
converse, which is what a parametric-Sard argument needs in order to turn the surjectivity of the
charted derivative into the hypothesis `Work.Drive.TParity.transHyp` of the counting engine.

The work is linear algebra around the chain rule:

* `Work.Drive.TParity.chartDiff3_mk3CLM` is the *linear* map underlying `mk3` (the block-stacking map
  `(v₀,v₁,v₂) ↦ (v₀,v₁,v₂)` of `ℝ^{3×3}` into `ℝ^9`), with `chartDiff3_mk3CLM_apply` its agreement with the
  combinatorial `mk3` and `chartDiff3_mk3CLM_surjective` its surjectivity (used to lift the surjectivity of the
  charted derivative back to the chart-free difference map `tan3`);
* `Work.Drive.TParity.hasFDerivAt_chartDiff3_mk3` is the chain rule
  `fderiv (chartDiff3 p D ∘ mk3) x = (pUpCLM ∘ tan3 p D (mk3 x)) ∘ chartDiff3_mk3CLM`;
* `Work.Drive.TParity.chartDiff3_tan3_surjective_iff` identifies the surjectivity of `tan3` with
  `TripleTransverse`; both directions use that at a triple point the three change-of-coordinates
  maps `tc` coincide (`tc_eq_of_meet`) and are invertible (`tc_injective`, `tcInv`,
  `tc_comp_tcInv`), so the charted difference map is the chart-free difference map conjugated by one
  invertible linear map.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## The linear map underlying the block-stacking `mk3` -/

/-- The block-stacking map `mk3` (three parameter vectors into the nine-box) as a continuous linear
map.  It is the linear structure underlying `mk3`, which the chain rule needs. -/
def chartDiff3_mk3CLM : (Fin 3 → EuclideanSpace ℝ (Fin 3)) →L[ℝ] Amb 8 :=
  ContinuousLinearMap.comp
    (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 9 => ℝ)).symm :
      (Fin 9 → ℝ) →L[ℝ] Amb 8))
    (ContinuousLinearMap.pi (fun i : Fin 9 =>
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) ⟨i.val % 3, by omega⟩).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin 3))
          ⟨i.val / 3, by omega⟩)))

/-- The coordinates of `chartDiff3_mk3CLM v`. -/
lemma chartDiff3_mk3CLM_apply_coord (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) (i : Fin 9) :
    (chartDiff3_mk3CLM v).ofLp i = (v ⟨i.val / 3, by omega⟩).ofLp ⟨i.val % 3, by omega⟩ := by
  simp only [chartDiff3_mk3CLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    PiLp.proj_apply, ContinuousLinearMap.proj_apply]

/-- `chartDiff3_mk3CLM` is the linear map underlying the block-stacking map `mk3`. -/
lemma chartDiff3_mk3CLM_apply (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) : chartDiff3_mk3CLM v = mk3 v := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [chartDiff3_mk3CLM_apply_coord]
  simp only [mk3, WithLp.ofLp_toLp]

/-- The block-stacking map `mk3` is surjective (it is a linear bijection `ℝ^9 → ℝ^9`). -/
lemma chartDiff3_mk3CLM_surjective : Function.Surjective chartDiff3_mk3CLM := by
  intro X
  refine ⟨fun k => bPartC k X, ?_⟩
  rw [chartDiff3_mk3CLM_apply]
  have h : (fun k => bPartC k X) = (fun k => Work.Drive.bPart k X) := by
    funext k; exact bPartC_eq_bPart k X
  rw [h]
  exact tripleEquiv.left_inv X

/-! ## The chain rule for the charted difference map of three chains -/

/-- **The derivative of the charted difference map of the three chains `D k`, with the three
parameters stacked as a single point of the nine-box.**  On the chart region the charted difference
map is the composite of `chartDiff3 p D` with `chartDiff3_mk3CLM`, so its derivative is
`(pUpCLM ∘ tan3) ∘ chartDiff3_mk3CLM`. -/
theorem hasFDerivAt_chartDiff3_mk3 (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hx : ∀ k, D k (x k) ∈ (Work.Drive.chr p).source) :
    HasFDerivAt (fun y : Fin 3 → EuclideanSpace ℝ (Fin 3) =>
      pUp ((Work.Drive.chr p) (D 0 (y 0)) - (Work.Drive.chr p) (D 1 (y 1)))
        ((Work.Drive.chr p) (D 0 (y 0)) - (Work.Drive.chr p) (D 2 (y 2))))
      ((pUpCLM.comp (tan3 p D (mk3 x))).comp chartDiff3_mk3CLM) x := by
  have hxR : mk3 x ∈ region3 p D := by
    intro k
    rw [bPartC_mk3]
    exact hx k
  have hchart := hasFDerivAt_chartDiff3 p D hD hxR
  have hmk3 : HasFDerivAt mk3 chartDiff3_mk3CLM x := by
    have h : (mk3 : (Fin 3 → EuclideanSpace ℝ (Fin 3)) → Amb 8) = ⇑chartDiff3_mk3CLM := by
      funext v; exact (chartDiff3_mk3CLM_apply v).symm
    rw [h]
    exact chartDiff3_mk3CLM.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : Fin 3 → EuclideanSpace ℝ (Fin 3) => chartDiff3 p D (mk3 y))
      ((pUpCLM.comp (tan3 p D (mk3 x))).comp chartDiff3_mk3CLM) x := hchart.comp x hmk3
  have hfun : (fun y : Fin 3 → EuclideanSpace ℝ (Fin 3) => chartDiff3 p D (mk3 y)) =
      (fun y : Fin 3 → EuclideanSpace ℝ (Fin 3) =>
        pUp ((Work.Drive.chr p) (D 0 (y 0)) - (Work.Drive.chr p) (D 1 (y 1)))
          ((Work.Drive.chr p) (D 0 (y 0)) - (Work.Drive.chr p) (D 2 (y 2)))) := by
    funext y
    simp only [chartDiff3, bPartC_mk3]
  rw [hfun] at hcomp
  exact hcomp

/-! ## The surjectivity of the chart-free difference map -/

/-- The stacking map `pUpCLM` of two `ℝ⁴`s into `ℝ⁸` is injective. -/
lemma chartDiff3_pUpCLM_injective : Function.Injective pUpCLM := by
  intro a b hab
  have h : pUpCLM (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp ((pUpCLM_eq_zero_iff (a - b)).mp h)

/-- **The surjectivity of the chart-free difference map `tan3` is exactly the transversality of the
three intrinsic derivatives.**  At a triple point the three change-of-coordinates maps coincide, so
`tan3` is the intrinsic difference map conjugated by one invertible linear map; surjectivity is
conjugation-invariant.  This is the two-sided version of `chartDiff3_surj`. -/
lemma chartDiff3_tan3_surjective_iff (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) {x : Amb 8}
    (hx : x ∈ region3 p D) (hm : meet3 D x) :
    Function.Surjective (tan3 p D x) ↔
      TripleTransverse (md3 D 0 x) (md3 D 1 x) (md3 D 2 x) := by
  have htc01 : tc p D 0 x = tc p D 1 x := tc_eq_of_meet hm
  have htc02 : tc p D 0 x = tc p D 2 x := tc_eq_of_meet hm
  have htc01inv : tcInv p D 0 x = tcInv p D 1 x := tcInv_eq_of_meet hm
  have htc02inv : tcInv p D 0 x = tcInv p D 2 x := tcInv_eq_of_meet hm
  constructor
  · intro hs w1 w2
    obtain ⟨v, hv⟩ := hs (tc p D 0 x w1, tc p D 0 x w2)
    have hv1 : (tan3 p D x v).1 = tc p D 0 x w1 := by rw [hv]
    have hv2 : (tan3 p D x v).2 = tc p D 0 x w2 := by rw [hv]
    refine ⟨fun k => bPartC k v, ?_, ?_⟩
    · refine tc_injective p D 0 hx ?_
      have h := hv1
      rw [tan3_fst, ← htc01, ← map_sub] at h
      exact h
    · refine tc_injective p D 0 hx ?_
      have h := hv2
      rw [tan3_snd, ← htc02, ← map_sub] at h
      exact h
  · intro htr z
    obtain ⟨z1, z2⟩ := z
    obtain ⟨v, hv1, hv2⟩ := htr (tcInv p D 0 x z1) (tcInv p D 0 x z2)
    refine ⟨mk3 v, ?_⟩
    have hcomp : tan3 p D x (mk3 v) = (z1, z2) := by
      refine Prod.ext ?_ ?_
      · rw [tan3_fst, bPartC_mk3, bPartC_mk3, htc01, ← map_sub, hv1, htc01inv]
        exact tc_comp_tcInv p D 1 hx z1
      · rw [tan3_snd, bPartC_mk3, bPartC_mk3, htc02, ← map_sub, hv2, htc02inv]
        exact tc_comp_tcInv p D 2 hx z2
    rw [hcomp]

end

end Work.Drive.TParity

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

/-- **The charted difference map of three `3`-chains, and the identification of its surjectivity with `TripleTransverse`.**

Let `M` be a smooth `4`-manifold (for the counting route: the capping space with its charted structure), let `D : Fin 3 → ℝ³ → M` be three smooth `3`-chains, let `p : M` be a chart centre and `x` a point of the parameter box at which the three values `D k (x k)` lie in the source of the chart at `p` and **coincide**.  Consider the *charted difference map of the three chains*

> `Ψ y := pUp (χ (D 0 (y 0)) - χ (D 1 (y 1))) (χ (D 0 (y 0)) - χ (D 2 (y 2)))`,

where `χ` is the chart at `p` and `pUp` pairs the two `4`-vectors into `ℝ⁸`.  This is the three-chain analogue of `chartDiff` (which handles a `2`-chain against a `3`-chain, in `ChartBridge.lean`); the *derivative of `Ψ`* is what a parametric-Sard argument controls (`Work.Drive.exists_forall_good_on_compact`), while `TripleTransverse` is the form in which the counting engine states its transversality hypothesis.  The gadget itself is `Work.Drive.TParity.chartDiff3`, whose derivative is computed in `TParity/ChartDeriv.lean` (`hasFDerivAt_chartDiff3`: `fderiv Ψ x = pUpCLM ∘ diag tc ∘ D`), and `chartDiff3_surj` is one half of the claim below.

Because the three values coincide at `x`, one and the same chart — hence one and the same tangent coordinate change — is used for all three chains, so the charted derivative is the intrinsic difference map `(v₀,v₁,v₂) ↦ (d₀v₀ - d₁v₁, d₀v₀ - d₂v₂)` conjugated by one invertible linear map.  Surjectivity being conjugation-invariant:

> `Function.Surjective (fderiv ℝ Ψ x)  ↔  TripleTransverse (mfderiv D 0 (x 0)) (mfderiv D 1 (x 1)) (mfderiv D 2 (x 2))`.

The **⇐ half is `Work.Drive.TParity.chartDiff3_surj`**; the new content is the **converse**, which is what a parametric-Sard argument needs in order to conclude `TParity.transHyp` from the surjectivity of the charted derivative.  The linear-algebra core is the kernel identification `ker (fderiv ℝ Ψ x) = {v | d₀v₀ = d₁v₁ and d₀v₀ = d₂v₂}` (the common tangent directions); the ingredients are `pUpCLM`'s bijectivity, the equality of the three tangent coordinate changes at a meet (`TParity.tc_eq_of_meet`, using `heq`), and their invertibility from `hx` (`ChartDeriv.lean`), together with `tripleTransverseE_comp_of_equiv` (`TripleGeneral.lean`) for the conjugation step. -/
theorem chartDiff3_surjective_iff_tripleTransverse {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hx : ∀ k, D k (x k) ∈ (Work.Drive.chr p).source)
    (heq : D 0 (x 0) = D 1 (x 1) ∧ D 0 (x 0) = D 2 (x 2)) :
    Function.Surjective
      (fderiv ℝ (fun y : Fin 3 → EuclideanSpace ℝ (Fin 3) =>
        Work.Drive.TParity.pUp
          (Work.Drive.chr p (D 0 (y 0)) - Work.Drive.chr p (D 1 (y 1)))
          (Work.Drive.chr p (D 0 (y 0)) - Work.Drive.chr p (D 2 (y 2)))) x) ↔
      Work.Drive.TripleTransverse
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)) := by
  have hxR : Work.Drive.TParity.mk3 x ∈ Work.Drive.TParity.region3 p D := by
    intro k
    rw [Work.Drive.TParity.bPartC_mk3]
    exact hx k
  have hm : Work.Drive.TParity.meet3 D (Work.Drive.TParity.mk3 x) := by
    constructor
    · rw [Work.Drive.TParity.bPartC_mk3, Work.Drive.TParity.bPartC_mk3]
      exact heq.1
    · rw [Work.Drive.TParity.bPartC_mk3, Work.Drive.TParity.bPartC_mk3]
      exact heq.2
  have key : Function.Surjective
      (fderiv ℝ (fun y : Fin 3 → EuclideanSpace ℝ (Fin 3) =>
        Work.Drive.TParity.pUp
          (Work.Drive.chr p (D 0 (y 0)) - Work.Drive.chr p (D 1 (y 1)))
          (Work.Drive.chr p (D 0 (y 0)) - Work.Drive.chr p (D 2 (y 2)))) x) ↔
      Work.Drive.TripleTransverse
        (Work.Drive.TParity.md3 D 0 (Work.Drive.TParity.mk3 x))
        (Work.Drive.TParity.md3 D 1 (Work.Drive.TParity.mk3 x))
        (Work.Drive.TParity.md3 D 2 (Work.Drive.TParity.mk3 x)) := by
    rw [(Work.Drive.TParity.hasFDerivAt_chartDiff3_mk3 p D hD x hx).fderiv]
    constructor
    · intro hsurj
      refine (Work.Drive.TParity.chartDiff3_tan3_surjective_iff p D hxR hm).mp ?_
      intro z
      obtain ⟨y, hy⟩ := hsurj (Work.Drive.TParity.pUpCLM z)
      refine ⟨Work.Drive.TParity.chartDiff3_mk3CLM y, ?_⟩
      have h2 : Work.Drive.TParity.pUpCLM
          (Work.Drive.TParity.tan3 p D (Work.Drive.TParity.mk3 x) (Work.Drive.TParity.chartDiff3_mk3CLM y))
          = Work.Drive.TParity.pUpCLM z := by
        simpa [ContinuousLinearMap.comp_apply] using hy
      exact Work.Drive.TParity.chartDiff3_pUpCLM_injective h2
    · intro htr w
      obtain ⟨w', hw'⟩ := Work.Drive.TParity.pUpCLM_surjective w
      obtain ⟨v, hv⟩ := ((Work.Drive.TParity.chartDiff3_tan3_surjective_iff p D hxR hm).mpr htr) w'
      obtain ⟨y, hy⟩ := Work.Drive.TParity.chartDiff3_mk3CLM_surjective v
      refine ⟨y, ?_⟩
      simp only [ContinuousLinearMap.comp_apply]
      rw [hy, hv, hw']
  rw [key]
  simp only [Work.Drive.TParity.md3]
  rw [Work.Drive.TParity.bPartC_mk3, Work.Drive.TParity.bPartC_mk3, Work.Drive.TParity.bPartC_mk3]

end

end Work.Drive
