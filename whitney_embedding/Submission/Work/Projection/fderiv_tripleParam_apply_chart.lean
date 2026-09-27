import Mathlib
import Submission.Work.Whitney.TripleLocusDefs
import Submission.Work.Projection.fderiv_pairZ_smooth
import Submission.Work.Projection.hasFDerivAt_projVec_bilinear

open scoped Manifold ContDiff
open Topology

namespace Work.Projection

/-- `ab ↦ g ab.2` is differentiable wherever `g` is. -/
private lemma differentiableAt_comp_snd_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) {b : E}
    (hg : DifferentiableAt ℝ g b) (a : E) :
    DifferentiableAt ℝ (fun ab : E × E => g ab.2) (a, b) :=
  hg.comp (a, b) differentiableAt_snd

/-- `ab ↦ g ab.1` is differentiable wherever `g` is. -/
private lemma differentiableAt_comp_fst_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) {a : E}
    (hg : DifferentiableAt ℝ g a) (b : E) :
    DifferentiableAt ℝ (fun ab : E × E => g ab.1) (a, b) :=
  hg.comp (a, b) differentiableAt_fst

private lemma fst_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (y : E × F) :
    (ContinuousLinearMap.fst ℝ E F) y = y.1 := rfl

private lemma snd_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (y : E × F) :
    (ContinuousLinearMap.snd ℝ E F) y = y.2 := rfl

private lemma proj_clm_apply {n : ℕ} (i : Fin 3) (g : Fin 3 → EuclideanSpace ℝ (Fin n)) :
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) i) g
      = g i := rfl

/-- The derivative of the triple parametrisation, evaluated on a direction.

`tripleParam e p q r : ((Fin 3 → ℝ^n) × ℝ^{2n}) → ℝ^{2n} × ℝ^{2n}` is defined in
`Submission.Work.Whitney.TripleLocusDefs` by
`tripleParam e p q r x = (projVec x.2 (pairZ e p q (x.1 0, x.1 1)), projVec x.2 (pairZ e p r (x.1 0, x.1 2)))`,
where `pairZ e p q (a,b) = chartRep e q b - chartRep e p a` and `chartRep e p y = e ((chartAt p).symm y)`.

The hypotheses say that the three parameters `x.1 0, x.1 1, x.1 2` lie in the targets of the charts
at `p`, `q`, `r` respectively (this makes `chartRep e p`, `chartRep e q`, `chartRep e r`
differentiable at those points).

The conclusion is the directional derivative of `tripleParam e p q r` at `x` in the direction
`y = (δv, δu)`: it is the pair whose first component is
`P_u (Dq (δv 1)) - P_u (Dp (δv 0)) - α • δu` and whose second component is
`P_u (Dr (δv 2)) - P_u (Dp (δv 0)) - β • δu`, where `P_u = projVec x.2`,
`Dp = fderiv ℝ (chartRep e p) (x.1 0)`, `Dq = fderiv ℝ (chartRep e q) (x.1 1)`,
`Dr = fderiv ℝ (chartRep e r) (x.1 2)`, `α = (pairZ e p q (x.1 0, x.1 1)) (Fin.last (2*n))` and
`β = (pairZ e p r (x.1 0, x.1 2)) (Fin.last (2*n))`.

Suggested route: `tripleParam e p q r = fun x => (G₁ x, G₂ x)` with
`G₁ x = projVec x.2 (pairZ e p q (x.1 0, x.1 1))`, so `fderiv` of the pair is the pair of the
`fderiv`'s (`fderiv_prod`). For `G₁`, write it as `Φ ∘ Ψ` with
`Φ (u, w) = projVec u w` and `Ψ x = (x.2, pairZ e p q (x.1 0, x.1 1))`; then use
`Work.Projection.hasFDerivAt_projVec_bilinear` (derivative of `Φ` at `(x.2, pairZ e p q (x.1 0, x.1 1))`,
whose derivative is `projVec x.2 ∘ snd - α • fst`), the differentiability of `pairZ e p q` at
`(x.1 0, x.1 1)` (from `Work.Projection.differentiableAt_chartRep`), and
`Work.Projection.fderiv_pairZ_smooth` to rewrite `fderiv ℝ (pairZ e p q) (x.1 0, x.1 1)` as
`Dq ∘L snd - Dp ∘L fst`. -/
theorem fderiv_tripleParam_apply_chart {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q r : M) (x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)))
    (hv0 : x.1 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target)
    (hv1 : x.1 1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    (hv2 : x.1 2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) r).target)
    (y : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))) :
    fderiv ℝ (tripleParam e p q r) x y =
      (projVec x.2 ((fderiv ℝ (chartRep e q) (x.1 1)) (y.1 1))
        - projVec x.2 ((fderiv ℝ (chartRep e p) (x.1 0)) (y.1 0))
        - ((pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n))) • y.2,
       projVec x.2 ((fderiv ℝ (chartRep e r) (x.1 2)) (y.1 2))
        - projVec x.2 ((fderiv ℝ (chartRep e p) (x.1 0)) (y.1 0))
        - ((pairZ e p r (x.1 0, x.1 2)) (Fin.last (2 * n))) • y.2) := by
  have hcq : DifferentiableAt ℝ (chartRep e q) (x.1 1) := differentiableAt_chartRep e he q hv1
  have hcp : DifferentiableAt ℝ (chartRep e p) (x.1 0) := differentiableAt_chartRep e he p hv0
  have hcr : DifferentiableAt ℝ (chartRep e r) (x.1 2) := differentiableAt_chartRep e he r hv2
  -- the derivatives of the two "coordinate" maps `x ↦ (x.1 0, x.1 1)` and `x ↦ (x.1 0, x.1 2)`
  set Lθ : ((Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) 0).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (2 * n))))).prod
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) 1).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (2 * n)))))
    with hLθ
  set Lθ2 : ((Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) 0).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (2 * n))))).prod
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) 2).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (2 * n)))))
    with hLθ2
  have hθ : HasFDerivAt (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
      (x.1 0, x.1 1)) Lθ x := by
    rw [hLθ]
    exact HasFDerivAt.prodMk
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) 0).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (2 * n))))).hasFDerivAt)
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) 1).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (2 * n))))).hasFDerivAt)
  have hθ2 : HasFDerivAt (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
      (x.1 0, x.1 2)) Lθ2 x := by
    rw [hLθ2]
    exact HasFDerivAt.prodMk
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) 0).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (2 * n))))).hasFDerivAt)
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) 2).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (2 * n))))).hasFDerivAt)
  -- differentiability of the two `pairZ` maps
  have hZdiff : DifferentiableAt ℝ (pairZ e p q) (x.1 0, x.1 1) :=
    (differentiableAt_comp_snd_clm (chartRep e q) hcq (x.1 0)).sub
      (differentiableAt_comp_fst_clm (chartRep e p) hcp (x.1 1))
  have hZdiff2 : DifferentiableAt ℝ (pairZ e p r) (x.1 0, x.1 2) :=
    (differentiableAt_comp_snd_clm (chartRep e r) hcr (x.1 0)).sub
      (differentiableAt_comp_fst_clm (chartRep e p) hcp (x.1 2))
  -- HasFDerivAt for the first component `x ↦ projVec x.2 (pairZ e p q (x.1 0, x.1 1))`
  have hG1 : HasFDerivAt
      (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
        projVec x.2 (pairZ e p q (x.1 0, x.1 1)))
      (((projVec x.2).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (2 * n)))
            (EuclideanSpace ℝ (Fin (2 * n + 1))))
          - ((pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n))) •
              ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2 * n)))
                (EuclideanSpace ℝ (Fin (2 * n + 1)))).comp
        ((ContinuousLinearMap.snd ℝ (Fin 3 → EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (2 * n)))).prod
          ((fderiv ℝ (pairZ e p q) (x.1 0, x.1 1)).comp Lθ))) x := by
    have hZ : HasFDerivAt
        ((pairZ e p q) ∘ (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
          (x.1 0, x.1 1)))
        ((fderiv ℝ (pairZ e p q) (x.1 0, x.1 1)).comp Lθ) x :=
      HasFDerivAt.comp x hZdiff.hasFDerivAt hθ
    have hΨ : HasFDerivAt
        (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
          (x.2, pairZ e p q (x.1 0, x.1 1)))
        ((ContinuousLinearMap.snd ℝ (Fin 3 → EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (2 * n)))).prod
          ((fderiv ℝ (pairZ e p q) (x.1 0, x.1 1)).comp Lθ)) x :=
      HasFDerivAt.prodMk hasFDerivAt_snd hZ
    have hΦ : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin (2 * n)) × EuclideanSpace ℝ (Fin (2 * n + 1)) =>
          projVec z.1 z.2)
        ((projVec x.2).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (2 * n)))
            (EuclideanSpace ℝ (Fin (2 * n + 1))))
          - ((pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n))) •
              ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2 * n)))
                (EuclideanSpace ℝ (Fin (2 * n + 1))))
        (x.2, pairZ e p q (x.1 0, x.1 1)) :=
      hasFDerivAt_projVec_bilinear (2 * n) x.2 (pairZ e p q (x.1 0, x.1 1))
    exact hΦ.comp x hΨ
  -- HasFDerivAt for the second component `x ↦ projVec x.2 (pairZ e p r (x.1 0, x.1 2))`
  have hG2 : HasFDerivAt
      (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
        projVec x.2 (pairZ e p r (x.1 0, x.1 2)))
      (((projVec x.2).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (2 * n)))
            (EuclideanSpace ℝ (Fin (2 * n + 1))))
          - ((pairZ e p r (x.1 0, x.1 2)) (Fin.last (2 * n))) •
              ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2 * n)))
                (EuclideanSpace ℝ (Fin (2 * n + 1)))).comp
        ((ContinuousLinearMap.snd ℝ (Fin 3 → EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (2 * n)))).prod
          ((fderiv ℝ (pairZ e p r) (x.1 0, x.1 2)).comp Lθ2))) x := by
    have hZ : HasFDerivAt
        ((pairZ e p r) ∘ (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
          (x.1 0, x.1 2)))
        ((fderiv ℝ (pairZ e p r) (x.1 0, x.1 2)).comp Lθ2) x :=
      HasFDerivAt.comp x hZdiff2.hasFDerivAt hθ2
    have hΨ : HasFDerivAt
        (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
          (x.2, pairZ e p r (x.1 0, x.1 2)))
        ((ContinuousLinearMap.snd ℝ (Fin 3 → EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (2 * n)))).prod
          ((fderiv ℝ (pairZ e p r) (x.1 0, x.1 2)).comp Lθ2)) x :=
      HasFDerivAt.prodMk hasFDerivAt_snd hZ
    have hΦ : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin (2 * n)) × EuclideanSpace ℝ (Fin (2 * n + 1)) =>
          projVec z.1 z.2)
        ((projVec x.2).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (2 * n)))
            (EuclideanSpace ℝ (Fin (2 * n + 1))))
          - ((pairZ e p r (x.1 0, x.1 2)) (Fin.last (2 * n))) •
              ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2 * n)))
                (EuclideanSpace ℝ (Fin (2 * n + 1))))
        (x.2, pairZ e p r (x.1 0, x.1 2)) :=
      hasFDerivAt_projVec_bilinear (2 * n) x.2 (pairZ e p r (x.1 0, x.1 2))
    exact hΦ.comp x hΨ
  -- evaluate the first component on `y`
  have h1 : fderiv ℝ (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
        projVec x.2 (pairZ e p q (x.1 0, x.1 1))) x y
      = projVec x.2 ((fderiv ℝ (chartRep e q) (x.1 1)) (y.1 1))
        - projVec x.2 ((fderiv ℝ (chartRep e p) (x.1 0)) (y.1 0))
        - ((pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n))) • y.2 := by
    rw [hG1.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, sub_apply, smul_apply,
      snd_clm_apply, fst_clm_apply, proj_clm_apply, hLθ]
    rw [fderiv_pairZ_smooth e he p q (x.1 0) (x.1 1) hv0 hv1]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, snd_clm_apply, fst_clm_apply]
    rw [map_sub]
  -- evaluate the second component on `y`
  have h2 : fderiv ℝ (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
        projVec x.2 (pairZ e p r (x.1 0, x.1 2))) x y
      = projVec x.2 ((fderiv ℝ (chartRep e r) (x.1 2)) (y.1 2))
        - projVec x.2 ((fderiv ℝ (chartRep e p) (x.1 0)) (y.1 0))
        - ((pairZ e p r (x.1 0, x.1 2)) (Fin.last (2 * n))) • y.2 := by
    rw [hG2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, sub_apply, smul_apply,
      snd_clm_apply, fst_clm_apply, proj_clm_apply, hLθ2]
    rw [fderiv_pairZ_smooth e he p r (x.1 0) (x.1 2) hv0 hv2]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, snd_clm_apply, fst_clm_apply]
    rw [map_sub]
  -- assemble: the derivative of the pair is the pair of the derivatives
  have hprod : fderiv ℝ
      (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
        ((fun x => projVec x.2 (pairZ e p q (x.1 0, x.1 1))) x,
         (fun x => projVec x.2 (pairZ e p r (x.1 0, x.1 2))) x)) x
      = ((fderiv ℝ (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
            projVec x.2 (pairZ e p q (x.1 0, x.1 1))) x).prod
         (fderiv ℝ (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
            projVec x.2 (pairZ e p r (x.1 0, x.1 2))) x)) :=
    hG1.differentiableAt.fderiv_prodMk hG2.differentiableAt
  rw [show tripleParam e p q r =
      (fun x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)) =>
        ((fun x => projVec x.2 (pairZ e p q (x.1 0, x.1 1))) x,
         (fun x => projVec x.2 (pairZ e p r (x.1 0, x.1 2))) x)) from rfl,
    hprod, ContinuousLinearMap.prod_apply]
  exact Prod.ext h1 h2

end Work.Projection
