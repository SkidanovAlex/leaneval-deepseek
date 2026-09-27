import Mathlib
import Submission.Work.Drive.TripleMeetDefs
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.tripleTransverse_comp_continuousLinearEquiv
import Submission.Work.Drive.tripleCommonDir_comp_continuousLinearEquiv

/-!
# The transversality hypothesis of the triple engine, in the coordinates of a chart

`Work.Drive.Meet3Generic` (`Submission/Work/Drive/planeChain.lean`) asks, at every triple point `x`
of three chains `D k : ℝ³ → M` of a charted `4`-manifold, for the transversality of the **manifold**
derivatives:

> `TripleTransverse (mfderiv D 0 (x 0)) (mfderiv D 1 (x 1)) (mfderiv D 2 (x 2))`.

To *check* that for a concrete chain (the capped plane, its radial sweeps) one computes in the charts
of the manifold, i.e. one computes the Fréchet derivative of `chartAt p ∘ D k`.  This file supplies
the bridge, and it is the exact analogue for three chains of what `ChartBridge.lean` does for two:

* `Work.Drive.tangentCoordChange_isBijective` — the change of coordinates between the preferred charts
  at two points is a linear **bijection** on the model space (it has the explicitly given two-sided
  inverse `tangentCoordChange I p q q`);
* `Work.Drive.tangentCoordChangeEquiv` — the same map packaged as a `≃L`;
* **`Work.Drive.tripleTransverse_mfderiv_iff_fderiv_chartAt`** — at a triple point, the manifold
  transversality is *equivalent* to the chart transversality
  `TripleTransverse (fderiv (chartAt p ∘ D 0) (x 0)) …` — since all three points `D k (x k)` are the
  *same* point of `M`, the three change-of-coordinates maps are the same invertible linear map, and
  transversality is invariant under it (`tripleTransverse_comp_continuousLinearEquiv`);
* **`Work.Drive.tripleCommonDir_mfderiv_iff_fderiv_chartAt`** — the same for the common-direction
  condition of the *face* field of `Meet3Generic`.

Together these say: **the genericity data of the concrete chains may be verified in any chart**, which
is what the computation of `Submission/Work/Drive/CONCRETE_CHAINS_STATUS.md` §3 needs.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## 1. The change of coordinates is a linear bijection -/

/-- **The two-sided inverse of the change-of-coordinates map**, in the form in which the three-chain
bridges use it: the composite of the two maps is the identity whenever both charts are defined at the
point. -/
theorem tangentCoordChange_comp_inv' {q p : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) p).source) (v : EuclideanSpace ℝ (Fin 4)) :
    tangentCoordChange (𝓡 4) p q q (tangentCoordChange (𝓡 4) q p q v) = v := by
  have hmem : q ∈ (extChartAt (𝓡 4) q).source ∩ (extChartAt (𝓡 4) p).source :=
    ⟨mem_extChartAt_source q, by rw [extChartAt_source]; exact hq⟩
  exact Work.Drive.tangentCoordChange_comp_inv (x := q) (y := p) (z := q) hmem v

/-- **The change-of-coordinates map is surjective** (the same memberships, the other order). -/
theorem tangentCoordChange_comp_inv'_symm {q p : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) p).source) (v : EuclideanSpace ℝ (Fin 4)) :
    tangentCoordChange (𝓡 4) q p q (tangentCoordChange (𝓡 4) p q q v) = v := by
  have hmem : q ∈ (extChartAt (𝓡 4) p).source ∩ (extChartAt (𝓡 4) q).source :=
    ⟨by rw [extChartAt_source]; exact hq, mem_extChartAt_source q⟩
  exact Work.Drive.tangentCoordChange_comp_inv (x := p) (y := q) (z := q) hmem v

/-- **The change of coordinates between the preferred charts at `q` and at `p`, both evaluated at
`q`, is an invertible linear map** of the model space.  This is the linear map that the chart
derivative of a chain at a point `q` composes with (`Work.Drive.fderiv_chart_comp`), so its
invertibility is what makes transversality chart-independent. -/
theorem tangentCoordChange_isBijective {q p : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) p).source) :
    (tangentCoordChange (𝓡 4) q p q).ker = ⊥ ∧
      (tangentCoordChange (𝓡 4) q p q).range = ⊤ := by
  constructor
  · rw [LinearMap.ker_eq_bot]
    intro v w hvw
    have h1 := tangentCoordChange_comp_inv' (p := p) hq v
    have h2 := tangentCoordChange_comp_inv' (p := p) hq w
    have hvw' : (tangentCoordChange (𝓡 4) q p q) v = (tangentCoordChange (𝓡 4) q p q) w := hvw
    rw [← hvw'] at h2
    exact h1.symm.trans h2
  · rw [LinearMap.range_eq_top]
    intro w
    exact ⟨tangentCoordChange (𝓡 4) p q q w, tangentCoordChange_comp_inv'_symm (p := p) hq w⟩

/-- **The change-of-coordinates map, packaged as a continuous linear equivalence.** -/
noncomputable def tangentCoordChangeEquiv {q p : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) p).source) :
    EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ContinuousLinearEquiv.ofBijective (tangentCoordChange (𝓡 4) q p q)
    (tangentCoordChange_isBijective (p := p) hq).1 (tangentCoordChange_isBijective (p := p) hq).2

@[simp] lemma coe_tangentCoordChangeEquiv {q p : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) p).source) :
    ((tangentCoordChangeEquiv (p := p) hq : EuclideanSpace ℝ (Fin 4) →L[ℝ]
        EuclideanSpace ℝ (Fin 4))) = tangentCoordChange (𝓡 4) q p q := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearEquiv.coe_coe]
  exact congrFun (ContinuousLinearEquiv.coeFn_ofBijective
    (tangentCoordChange (𝓡 4) q p q)
    (tangentCoordChange_isBijective (p := p) hq).1
    (tangentCoordChange_isBijective (p := p) hq).2) v

/-! ## 2. The post-composition transfers -/

/-- Transversality of three derivatives is invariant under composing all three with a linear
equivalence of the target (the `M = 1` case of
`Work.Drive.tripleTransverse_comp_continuousLinearEquiv`). -/
theorem tripleTransverse_comp_continuousLinearEquiv_left
    (L : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4))
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    TripleTransverse ((L : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp f₀)
      ((L : _ →L[ℝ] _).comp f₁) ((L : _ →L[ℝ] _).comp f₂) ↔ TripleTransverse f₀ f₁ f₂ := by
  constructor
  · intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (L w₁) (L w₂)
    have h1' := h1
    have h2' := h2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h1'
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h2'
    refine ⟨v, ?_, ?_⟩
    · refine L.injective ?_
      exact (map_sub (L : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
        (f₀ (v 0)) (f₁ (v 1))).trans h1'
    · refine L.injective ?_
      exact (map_sub (L : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
        (f₀ (v 0)) (f₂ (v 2))).trans h2'
  · intro h w₁ w₂
    obtain ⟨v, h1, h2⟩ := h (L.symm w₁) (L.symm w₂)
    refine ⟨v, ?_, ?_⟩
    · simp only [ContinuousLinearMap.comp_apply]
      rw [← map_sub, h1]
      exact L.apply_symm_apply w₁
    · simp only [ContinuousLinearMap.comp_apply]
      rw [← map_sub, h2]
      exact L.apply_symm_apply w₂

/-- The common-direction condition is invariant under composing all three derivatives with a linear
equivalence of the target. -/
theorem tripleCommonDir_comp_continuousLinearEquiv_left
    (L : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4))
    (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    TripleCommonDir ((L : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp f₀)
      ((L : _ →L[ℝ] _).comp f₁) ((L : _ →L[ℝ] _).comp f₂) v
      ↔ TripleCommonDir f₀ f₁ f₂ v :=
  tripleCommonDir_comp_continuousLinearEquiv L f₀ f₁ f₂ v

/-! ## 3. The bridges -/

/-- **Triple transversality is a chart-local condition.**  At a point `x` of the parameter cubes at
which the three chains meet, the manifold transversality of the three derivatives is *equivalent* to
the transversality of the derivatives of the three charted chains `chartAt p ∘ D k`.  The chart `p`
may be chosen at will (as long as the three points lie in its source). -/
theorem tripleTransverse_mfderiv_iff_fderiv_chartAt
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) (p : M)
    (hsrc : ∀ k, D k (x k) ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) p).source)
    (heq1 : D 0 (x 0) = D 1 (x 1)) (heq2 : D 0 (x 0) = D 2 (x 2)) :
    TripleTransverse (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0))
        (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1)) (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2))
      ↔ TripleTransverse
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 0 u)) (x 0))
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 1 u)) (x 1))
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 2 u)) (x 2)) := by
  have h0 : fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 0 u)) (x 0)
      = (tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0))).comp
        (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0)) := by
    simpa only [Work.Drive.chr] using Work.Drive.fderiv_chart_comp (D 0) (hD 0) p (hsrc 0)
  have h1 : fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 1 u)) (x 1)
      = (tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0))).comp
        (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1)) := by
    have := Work.Drive.fderiv_chart_comp (D 1) (hD 1) p (hsrc 1)
    rw [show Work.Drive.chr p = chartAt (EuclideanSpace ℝ (Fin 4)) p from rfl,
      show tangentCoordChange (𝓡 4) (D 1 (x 1)) p (D 1 (x 1))
        = tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0)) from by rw [← heq1]] at this
    exact this
  have h2 : fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 2 u)) (x 2)
      = (tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0))).comp
        (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2)) := by
    have := Work.Drive.fderiv_chart_comp (D 2) (hD 2) p (hsrc 2)
    rw [show Work.Drive.chr p = chartAt (EuclideanSpace ℝ (Fin 4)) p from rfl,
      show tangentCoordChange (𝓡 4) (D 2 (x 2)) p (D 2 (x 2))
        = tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0)) from by rw [← heq2]] at this
    exact this
  have key := tripleTransverse_comp_continuousLinearEquiv_left
    (tangentCoordChangeEquiv (p := p) (hsrc 0))
    (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0)) (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1))
    (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2))
  rw [coe_tangentCoordChangeEquiv] at key
  rw [h0, h1, h2]
  exact key.symm

/-- **The common-direction condition is a chart-local condition** (the *face* field of
`Work.Drive.Meet3Generic`). -/
theorem tripleCommonDir_mfderiv_iff_fderiv_chartAt
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) (p : M)
    (hsrc : ∀ k, D k (x k) ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) p).source)
    (heq1 : D 0 (x 0) = D 1 (x 1)) (heq2 : D 0 (x 0) = D 2 (x 2))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    TripleCommonDir (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0))
        (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1)) (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2)) v
      ↔ TripleCommonDir
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 0 u)) (x 0))
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 1 u)) (x 1))
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 2 u)) (x 2)) v := by
  have h0 : fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 0 u)) (x 0)
      = (tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0))).comp
        (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0)) := by
    simpa only [Work.Drive.chr] using Work.Drive.fderiv_chart_comp (D 0) (hD 0) p (hsrc 0)
  have h1 : fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 1 u)) (x 1)
      = (tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0))).comp
        (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1)) := by
    have := Work.Drive.fderiv_chart_comp (D 1) (hD 1) p (hsrc 1)
    rw [show Work.Drive.chr p = chartAt (EuclideanSpace ℝ (Fin 4)) p from rfl,
      show tangentCoordChange (𝓡 4) (D 1 (x 1)) p (D 1 (x 1))
        = tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0)) from by rw [← heq1]] at this
    exact this
  have h2 : fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) p (D 2 u)) (x 2)
      = (tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0))).comp
        (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2)) := by
    have := Work.Drive.fderiv_chart_comp (D 2) (hD 2) p (hsrc 2)
    rw [show Work.Drive.chr p = chartAt (EuclideanSpace ℝ (Fin 4)) p from rfl,
      show tangentCoordChange (𝓡 4) (D 2 (x 2)) p (D 2 (x 2))
        = tangentCoordChange (𝓡 4) (D 0 (x 0)) p (D 0 (x 0)) from by rw [← heq2]] at this
    exact this
  have key := tripleCommonDir_comp_continuousLinearEquiv_left
    (tangentCoordChangeEquiv (p := p) (hsrc 0))
    (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0)) (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1))
    (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2)) v
  rw [coe_tangentCoordChangeEquiv] at key
  rw [h0, h1, h2]
  exact key.symm

/-- **The chart-local form of triple transversality, with the chart taken at the triple point.**
This is `Work.Drive.tripleTransverse_mfderiv_iff_fderiv_chartAt` with the chart point `p` chosen to be
the common value `D 0 (x 0)` of the three chains, so that the chart-source hypotheses hold
automatically.  This is the form in which the genericity of concrete chains is verified. -/
theorem tripleTransverse_mfderiv_iff_fderiv_chartAt_self
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (heq1 : D 0 (x 0) = D 1 (x 1)) (heq2 : D 0 (x 0) = D 2 (x 2)) :
    TripleTransverse (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0))
        (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1)) (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2))
      ↔ TripleTransverse
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) (D 0 (x 0)) (D 0 u)) (x 0))
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) (D 0 (x 0)) (D 1 u)) (x 1))
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) (D 0 (x 0)) (D 2 u)) (x 2)) := by
  refine tripleTransverse_mfderiv_iff_fderiv_chartAt D hD x (D 0 (x 0)) ?_ heq1 heq2
  intro k
  have hk : D k (x k) = D 0 (x 0) := by
    fin_cases k
    · rfl
    · exact heq1.symm
    · exact heq2.symm
  rw [hk]
  exact mem_chart_source _ _

/-- The common-direction condition in the chart at the triple point. -/
theorem tripleCommonDir_mfderiv_iff_fderiv_chartAt_self
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (heq1 : D 0 (x 0) = D 1 (x 1)) (heq2 : D 0 (x 0) = D 2 (x 2))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    TripleCommonDir (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0))
        (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1)) (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2)) v
      ↔ TripleCommonDir
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) (D 0 (x 0)) (D 0 u)) (x 0))
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) (D 0 (x 0)) (D 1 u)) (x 1))
          (fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) (D 0 (x 0)) (D 2 u)) (x 2)) v := by
  refine tripleCommonDir_mfderiv_iff_fderiv_chartAt D hD x (D 0 (x 0)) ?_ heq1 heq2 v
  intro k
  have hk : D k (x k) = D 0 (x 0) := by
    fin_cases k
    · rfl
    · exact heq1.symm
    · exact heq2.symm
  rw [hk]
  exact mem_chart_source _ _

end

end Work.Drive
