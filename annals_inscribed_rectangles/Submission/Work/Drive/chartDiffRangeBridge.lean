import Mathlib
import Submission.Work.Drive.ChartBridge

/-!
# The converse of the transversality bridge for the charted difference map

`Work.Drive.chartDiff_surjective_of_transverse` (`ChartBridge.lean`) turns the *intrinsic*
transversality of a loop `D : ℝ² → M` and a `3`-chain `N : ℝ³ → M` in a charted `4`-manifold `M`,

> `range (mfderiv D (sqPart x)) ⊔ range (mfderiv N (cbPart x)) = ⊤`

at a meet `D (sqPart x) = N (cbPart x)`, into the surjectivity of the derivative of the *charted*
difference map `chartDiff p D N` at `x`.  Every consumer of the charted side (the flow cover of
`ManifoldParity/InterSetCover.lean`, the parity engines `transverse_inter_boundary_parity`,
`odd_ncard_loopFamMeet_iff`, ...) states the *intrinsic* form as its hypothesis, so a construction of
that hypothesis by a Sard-type argument has to go the other way: from surjectivity of the charted
derivative back to the intrinsic form.

This file supplies that converse, in the sharp form of an equivalence:

* `Work.Drive.fderiv_chartDiff_eq` — the derivative of `chartDiff p D N` at a meet, in the split form
  in which the change of coordinates is the *same* on both sides;
* `Work.Drive.range_sub_eq_sup_range` — the linear-algebraic core: the range of
  `(mfderiv D) ∘ sqPartCLM − (mfderiv N) ∘ cbPartCLM` on `Amb 4` is *exactly* the supremum of the two
  intrinsic ranges (the two projections are jointly surjective, `mkPart`);
* `Work.Drive.range_sup_eq_top_of_chartDiff_surjective` — the converse;
* `Work.Drive.chartDiff_surjective_iff_range_sup_eq_top` — the equivalence.

The wrappers `Work.Drive.mLoop` and `Work.Drive.mChain` read the two manifold derivatives in the
*model* spaces, which is what makes the linear algebra below typecheck (`TangentSpace` is an opaque
`def`, so the two intrinsic ranges are not syntactically the same `Submodule`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- The derivative of the loop `D` at `sqPart x`, read in the model spaces. -/
def mLoop (D : EuclideanSpace ℝ (Fin 2) → M) (x : Amb 4) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  mfderiv (𝓡 2) (𝓡 4) D (sqPart x)

/-- The derivative of the `3`-chain `N` at `cbPart x`, read in the model spaces. -/
def mChain (N : EuclideanSpace ℝ (Fin 3) → M) (x : Amb 4) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  mfderiv (𝓡 3) (𝓡 4) N (cbPart x)

@[simp] lemma mLoop_apply (D : EuclideanSpace ℝ (Fin 2) → M) (x : Amb 4)
    (v : EuclideanSpace ℝ (Fin 2)) :
    mLoop D x v = mfderiv (𝓡 2) (𝓡 4) D (sqPart x) v := rfl

@[simp] lemma mChain_apply (N : EuclideanSpace ℝ (Fin 3) → M) (x : Amb 4)
    (v : EuclideanSpace ℝ (Fin 3)) :
    mChain N x v = mfderiv (𝓡 3) (𝓡 4) N (cbPart x) v := rfl

/-- **The derivative of the charted difference map at a meet, split form.**  At a meet
`D (sqPart x) = N (cbPart x)` the two change-of-coordinates maps of the two summands are the *same*
map. -/
theorem fderiv_chartDiff_eq (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (heq : D (sqPart x) = N (cbPart x)) :
    fderiv ℝ (chartDiff p D N) x =
      (tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x))).comp
          ((mLoop D x).comp sqPartCLM)
        - (tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x))).comp
          ((mChain N x).comp cbPartCLM) := by
  ext v
  rw [fderiv_chartDiff_apply p D N hD hN hx v]
  have hT : tangentCoordChange (𝓡 4) (N (cbPart x)) p (N (cbPart x)) =
      tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x)) := by rw [heq]
  rw [hT]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, mLoop_apply, mChain_apply]

/-- **The range of the difference of the two charted chain derivatives is the supremum of the two
intrinsic ranges.**  The two projections `sqPartCLM : ℝ⁵ → ℝ²` and `cbPartCLM : ℝ⁵ → ℝ³` are jointly
surjective (`mkPart`), which is what makes the `⊆` an equality. -/
theorem range_sub_eq_sup_range (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) (x : Amb 4) :
    LinearMap.range ((mLoop D x).comp sqPartCLM - (mChain N x).comp cbPartCLM).toLinearMap =
      LinearMap.range (mLoop D x).toLinearMap ⊔ LinearMap.range (mChain N x).toLinearMap := by
  classical
  set A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (mLoop D x).toLinearMap with hA
  set B : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (mChain N x).toLinearMap with hB
  have hsub : ((mLoop D x).comp sqPartCLM - (mChain N x).comp cbPartCLM).toLinearMap
      = A.comp sqPartCLM.toLinearMap - B.comp cbPartCLM.toLinearMap := by
    rw [hA, hB, ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_comp]
  rw [hsub, hA, hB]
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro w ⟨v, rfl⟩
    exact Submodule.sub_mem_sup (LinearMap.mem_range.mpr ⟨sqPartCLM v, rfl⟩)
      (LinearMap.mem_range.mpr ⟨cbPartCLM v, rfl⟩)
  · rintro w ⟨u, rfl⟩
    refine LinearMap.mem_range.mpr ⟨mkPart u 0, ?_⟩
    show A (sqPartCLM (mkPart u 0)) - B (cbPartCLM (mkPart u 0)) = A u
    rw [sqPartCLM_mkPart, cbPartCLM_mkPart, map_zero, sub_zero]
  · rintro w ⟨u, rfl⟩
    refine LinearMap.mem_range.mpr ⟨mkPart 0 (-u), ?_⟩
    show A (sqPartCLM (mkPart 0 (-u))) - B (cbPartCLM (mkPart 0 (-u))) = B u
    rw [sqPartCLM_mkPart, cbPartCLM_mkPart, map_zero, map_neg, zero_sub, neg_neg]

/-- **The converse of the transversality bridge.**  At a meet of the loop `D` and the `3`-chain `N`,
surjectivity of the derivative of the charted difference map (in a chart `p` whose source contains both
values) forces the intrinsic transversality of the two chains. -/
theorem range_sup_eq_top_of_chartDiff_surjective (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (heq : D (sqPart x) = N (cbPart x))
    (hsurj : Function.Surjective (fderiv ℝ (chartDiff p D N) x)) :
    LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).toLinearMap = ⊤ := by
  classical
  set T : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x)) with hT
  have hsrc1 : D (sqPart x) ∈ (extChartAt (𝓡 4) (D (sqPart x))).source :=
    mem_extChartAt_source (I := 𝓡 4) (D (sqPart x))
  have hsrc2 : D (sqPart x) ∈ (extChartAt (𝓡 4) p).source := by
    rw [extChartAt_source]; exact hx.1
  have hleft : Function.LeftInverse (tangentCoordChange (𝓡 4) p (D (sqPart x)) (D (sqPart x))) T :=
    tangentCoordChange_left_inv (x := D (sqPart x)) (y := p) (z := D (sqPart x)) ⟨hsrc1, hsrc2⟩
  have hright : Function.LeftInverse T (tangentCoordChange (𝓡 4) p (D (sqPart x)) (D (sqPart x))) :=
    tangentCoordChange_left_inv (x := p) (y := D (sqPart x)) (z := D (sqPart x)) ⟨hsrc2, hsrc1⟩
  have hTinj : Function.Injective T := hleft.injective
  have hTsurj : Function.Surjective T := hright.surjective
  set A : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (mLoop D x).comp sqPartCLM - (mChain N x).comp cbPartCLM with hA
  set S : Submodule ℝ (EuclideanSpace ℝ (Fin 4)) := LinearMap.range A.toLinearMap with hS
  set Ŝ : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 4) := T.comp A with hŜ
  have hf : fderiv ℝ (chartDiff p D N) x = Ŝ := by
    rw [hŜ, hA, fderiv_chartDiff_eq p D N hD hN hx heq, hT, ← ContinuousLinearMap.comp_sub]
  have htop : LinearMap.range Ŝ.toLinearMap = ⊤ := by
    rw [← hf]
    refine Submodule.eq_top_iff'.mpr fun w => ?_
    obtain ⟨v, hv⟩ := hsurj w
    exact LinearMap.mem_range.mpr ⟨v, hv⟩
  have hmap : LinearMap.range Ŝ.toLinearMap = Submodule.map T.toLinearMap S := by
    rw [hŜ, hS, ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.range_comp (f := A.toLinearMap) (g := T.toLinearMap)
  have hmap_top : Submodule.map T.toLinearMap (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 4))) = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hTsurj
  have hStop : S = ⊤ :=
    Submodule.map_injective_of_injective hTinj (by rw [← hmap, htop, hmap_top])
  change LinearMap.range (mLoop D x).toLinearMap ⊔ LinearMap.range (mChain N x).toLinearMap = ⊤
  rw [← range_sub_eq_sup_range D N x, ← hS]
  exact hStop

/-- **The transversality bridge, both directions.**  At a meet of a loop and a `3`-chain in a charted
`4`-manifold, the derivative of the charted difference map is surjective **iff** the two intrinsic
tangent ranges span. -/
theorem chartDiff_surjective_iff_range_sup_eq_top (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (heq : D (sqPart x) = N (cbPart x)) :
    Function.Surjective (fderiv ℝ (chartDiff p D N) x) ↔
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).toLinearMap = ⊤ :=
  ⟨range_sup_eq_top_of_chartDiff_surjective p D N hD hN hx heq,
    chartDiff_surjective_of_transverse p D N hD hN hx heq⟩

end

end Work.Drive
