import Mathlib
import Submission.Work.Drive.geometricLocality
import Submission.Work.Drive.chartDiffRangeBridge

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The converse transversality bridge for an `ℝ`-parametrised loop

`Work.Drive.range_sup_eq_top_of_chartDiff_surjective` (`chartDiffRangeBridge.lean`) is the converse of
the charted-derivative bridge for a loop parametrised by `ℝ²` and a `3`-chain parametrised by `ℝ³`:
surjectivity of the derivative of the *charted* difference map at a meet forces
`range (mfderiv D) ⊔ range (mfderiv N) = ⊤`.

The design's loop is parametrised by `ℝ` (the core loop `t ↦ Q (exp (iπt))`) and the chain by `ℝ³`,
i.e. by the self-model-corners space `𝓘(ℝ,ℝ)` on the loop side.  This file supplies the same converse
in that setting:

* `Work.Drive.fderiv_chartDiff_real` — the derivative of the charted difference map
  `q ↦ chr c (L q.1) - chr c (D q.2)` at a meet, in the split form in which the change of coordinates
  `tangentCoordChange (𝓡 4) (L p.1) c (L p.1)` is the *same* on both sides;
* `Work.Drive.range_sup_eq_top_of_chartedDiff_surjective_real` — the converse:
  `Function.Surjective (fderiv ℝ (charted difference) p)` forces the intrinsic transversality
  `range (mfderiv L) ⊔ range (mfderiv D) = ⊤`.

The linear algebra is `Work.Drive.range_comp_sub_comp` (`regular_of_transverse.lean`): the two
projections `fst : ℝ × ℝ³ → ℝ` and `snd : ℝ × ℝ³ → ℝ³` are jointly surjective, so the range of the
difference of the two composites is exactly the supremum of the two ranges.  The change of coordinates
is a left inverse of its reverse (`Work.Drive.tangentCoordChange_left_inv`), hence injective, and
`map T S = ⊤` with `T` injective forces `S = ⊤`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) Ctop M]

/-- The derivative of an `ℝ`-parametrised loop at `p.1`, read in the model spaces. -/
def mLoopR (L : ℝ → M) (p : ℝ × EuclideanSpace ℝ (Fin 3)) :
    ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) L p.1

/-- The derivative of a `3`-chain at `p.2`, read in the model spaces. -/
def mChainR (D : EuclideanSpace ℝ (Fin 3) → M) (p : ℝ × EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  mfderiv (𝓡 3) (𝓡 4) D p.2

lemma mLoopR_apply (L : ℝ → M) (p : ℝ × EuclideanSpace ℝ (Fin 3)) (v : ℝ) :
    mLoopR L p v = mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) L p.1 v := rfl

lemma mChainR_apply (D : EuclideanSpace ℝ (Fin 3) → M)
    (p : ℝ × EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3)) :
    mChainR D p v = mfderiv (𝓡 3) (𝓡 4) D p.2 v := rfl

/-- **The derivative of the charted difference map at a meet**, `ℝ`-parametrised form (the analogue of
`Work.Drive.fderiv_chartDiff_apply`).  At a meet `L p.1 = D p.2` the two change-of-coordinates maps of
the two summands are the *same* map, so the derivative is
`T ∘ (mfderiv L) ∘ fst − T ∘ (mfderiv D) ∘ snd`. -/
theorem fderiv_chartDiff_real (c : M) (L : ℝ → M) (D : EuclideanSpace ℝ (Fin 3) → M)
    (hL : ContMDiff (𝓘(ℝ,ℝ)) (𝓡 4) Ctop L)
    (hD : ContMDiff (𝓡 3) (𝓡 4) Ctop D)
    {p : ℝ × EuclideanSpace ℝ (Fin 3)}
    (hcL : L p.1 ∈ (chr c).source) (hcD : D p.2 ∈ (chr c).source) (heq : L p.1 = D p.2) :
    fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
        (chr c : M → EuclideanSpace ℝ (Fin 4)) (L q.1)
          - (chr c : M → EuclideanSpace ℝ (Fin 4)) (D q.2)) p =
      ((tangentCoordChange (𝓡 4) (L p.1) c (L p.1)).comp (mLoopR L p)).comp
          (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
        - ((tangentCoordChange (𝓡 4) (L p.1) c (L p.1)).comp (mChainR D p)).comp
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3))) := by
  classical
  have h1 := fderiv_chart_comp_hasFDerivAt_real L hL c hcL
  have h2 := fderiv_chart_comp_hasFDerivAt D hD c hcD
  have hA : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr c (L q.1))
      (((tangentCoordChange (𝓡 4) (L p.1) c (L p.1)).comp (mLoopR L p)).comp
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) p := by
    have hc := h1.comp p hasFDerivAt_fst
    simpa [Function.comp_def, mLoopR] using hc
  have hB : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr c (D q.2))
      (((tangentCoordChange (𝓡 4) (L p.1) c (L p.1)).comp (mChainR D p)).comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) p := by
    rw [← heq] at h2
    have hc := h2.comp p hasFDerivAt_snd
    simpa [Function.comp_def, mChainR] using hc
  have h := (hA.sub hB).fderiv
  rw [show ((fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr c (L q.1)) -
        (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr c (D q.2)))
      = (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
          (chr c : M → EuclideanSpace ℝ (Fin 4)) (L q.1)
            - (chr c : M → EuclideanSpace ℝ (Fin 4)) (D q.2)) from rfl] at h
  exact h

/-- **The converse of the transversality bridge**, `ℝ`-parametrised form.  At a meet of the loop `L`
and the `3`-chain `D`, surjectivity of the derivative of the charted difference map (in a chart `c`
whose source contains both values) forces the intrinsic transversality of the two maps. -/
theorem range_sup_eq_top_of_chartedDiff_surjective_real {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Work.Drive.Ctop M]
    (c : M) (L : ℝ → M) (D : EuclideanSpace ℝ (Fin 3) → M)
    (hL : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Work.Drive.Ctop L)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Work.Drive.Ctop D)
    {p : ℝ × EuclideanSpace ℝ (Fin 3)}
    (hcL : L p.1 ∈ (Work.Drive.chr c).source) (hcD : D p.2 ∈ (Work.Drive.chr c).source)
    (heq : L p.1 = D p.2)
    (hsurj : Function.Surjective
      (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
        (Work.Drive.chr c : M → EuclideanSpace ℝ (Fin 4)) (L q.1)
          - (Work.Drive.chr c : M → EuclideanSpace ℝ (Fin 4)) (D q.2)) p)) :
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) L p.1).toLinearMap ⊔
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) D p.2).toLinearMap = ⊤ := by
  classical
  change (mLoopR L p).toLinearMap.range ⊔ (mChainR D p).toLinearMap.range = ⊤
  -- the change of coordinates at the meet
  set T : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    tangentCoordChange (𝓡 4) (L p.1) c (L p.1) with hT
  -- the (un-charted) difference of the two derivatives, on `ℝ × ℝ³`
  set A : (ℝ × EuclideanSpace ℝ (Fin 3)) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ((mLoopR L p).comp (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3))))
      - ((mChainR D p).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) with hA
  -- the derivative of the charted difference map
  have hf : fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
        (chr c : M → EuclideanSpace ℝ (Fin 4)) (L q.1)
          - (chr c : M → EuclideanSpace ℝ (Fin 4)) (D q.2)) p = T.comp A := by
    rw [fderiv_chartDiff_real c L D hL hD hcL hcD heq, hT, hA]
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc]
  -- `T` is injective
  have hTinj : Function.Injective T := by
    have hsrc1 : L p.1 ∈ (extChartAt (𝓡 4) (L p.1)).source :=
      mem_extChartAt_source (I := 𝓡 4) (L p.1)
    have hsrc2 : L p.1 ∈ (extChartAt (𝓡 4) c).source := by
      rw [extChartAt_source]; exact hcL
    have hleft := tangentCoordChange_left_inv (x := L p.1) (y := c) (z := L p.1)
      ⟨hsrc1, hsrc2⟩
    exact hleft.injective
  have htopF : LinearMap.range (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
        (chr c : M → EuclideanSpace ℝ (Fin 4)) (L q.1)
          - (chr c : M → EuclideanSpace ℝ (Fin 4)) (D q.2)) p).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hmap : LinearMap.range (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
        (chr c : M → EuclideanSpace ℝ (Fin 4)) (L q.1)
          - (chr c : M → EuclideanSpace ℝ (Fin 4)) (D q.2)) p).toLinearMap
      = Submodule.map T.toLinearMap A.toLinearMap.range := by
    rw [hf, ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.range_comp (f := A.toLinearMap) (g := T.toLinearMap)
  -- injectivity of `T` transfers surjectivity back to `A`
  have htopA : A.toLinearMap.range = ⊤ := by
    refine Submodule.eq_top_iff'.mpr (fun w => ?_)
    have hmem : T w ∈ Submodule.map T.toLinearMap A.toLinearMap.range := by
      rw [← hmap, htopF]
      exact Submodule.mem_top
    obtain ⟨s, hs, hst⟩ := Submodule.mem_map.mp hmem
    have hsw : s = w := hTinj hst
    rw [← hsw]
    exact hs
  -- the range of the difference of the two composites is the supremum of the two ranges
  have hfinal : (mLoopR L p).toLinearMap.range ⊔ (mChainR D p).toLinearMap.range = ⊤ := by
    rw [← range_comp_sub_comp (mLoopR L p) (mChainR D p)
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
      (fun u v => ⟨(u, v), rfl, rfl⟩)]
    rw [← hA]
    exact htopA
  exact hfinal

end

end Work.Drive
