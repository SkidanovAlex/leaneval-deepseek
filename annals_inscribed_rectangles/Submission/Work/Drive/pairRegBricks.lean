import Mathlib
import Submission.Work.Drive.classLevelTransverse
import Submission.Work.Drive.tripleChartBridge
import Submission.Work.Drive.planeClassDeriv_eq_mfderiv

/-!
# The two linear-algebra / chart bridges of a **pair** regularity

`Work.Drive.PairReg A B` is the *spanning* condition `range A ⊔ range B = ⊤` at every common value,
and the producers of the ends clause reach it from a `(2,3)`-meet transversality in the capping space
(`Work.Drive.LoopBoxData`), through the *charted* block form of the two derivatives.

This file supplies the two transfers that are common to all such producers:

* `Work.Drive.surjective_sub_iff_range_sup_eq_top` — for two linear maps `f`, `g` into one space,
  `Surjective (fun w => f w.1 - g w.2) ↔ f.range ⊔ g.range = ⊤`;
* `Work.Drive.range_sup_eq_top_mfderiv_iff_fderiv_chartAt_self` — the pair analogue of
  `Work.Drive.tripleTransverse_mfderiv_iff_fderiv_chartAt_self`: the intrinsic spanning of the two
  manifold derivatives is equivalent to the spanning of their charted derivatives, read in the **same**
  chart (the one at the common value), and in that chart the change-of-coordinates map is the identity
  (`tangentCoordChange_self`).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The linear-algebra identity -/

/-- **The pair difference map is onto iff the two ranges span.** -/
theorem surjective_sub_iff_range_sup_eq_top
    {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    (f : E →ₗ[ℝ] G) (g : F →ₗ[ℝ] G) :
    Function.Surjective (fun w : E × F => f w.1 - g w.2) ↔ f.range ⊔ g.range = ⊤ := by
  constructor
  · intro h
    rw [Submodule.eq_top_iff']
    intro z
    obtain ⟨w, hw⟩ := h z
    have hmem : f w.1 + g (-w.2) ∈ f.range ⊔ g.range :=
      Submodule.add_mem_sup (LinearMap.mem_range_self f w.1) (LinearMap.mem_range_self g (-w.2))
    have hz : f w.1 + g (-w.2) = z := by
      rw [map_neg] at *
      rw [← hw]
      abel
    rw [← hz]
    exact hmem
  · intro h z
    have hz : z ∈ f.range ⊔ g.range := by rw [h]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    refine ⟨(a', -b'), ?_⟩
    show f a' - g (-b') = z
    have hneg : f a' - g (-b') = f a' + g b' := by rw [map_neg]; abel
    rw [hneg, hab]

/-! ## 2. The pair chart bridge -/

/-- **The pair spanning is chart-free.**  For two smooth maps into a charted `4`-manifold meeting at a
common value `A u = D x`, the intrinsic spanning of the two manifold derivatives is equivalent to the
spanning of their charted derivatives read in the chart at the common value.  (In that chart the
change-of-coordinates map is the identity, by `tangentCoordChange_self`.) -/
theorem range_sup_eq_top_mfderiv_iff_fderiv_chartAt_self
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (A : EuclideanSpace ℝ (Fin 2) → M) (D : EuclideanSpace ℝ (Fin 3) → M)
    (hA : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hD : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3))
    (hval : A u = D x) :
    ((mfderiv (𝓡 2) (𝓡 4) A u).toLinearMap.range ⊔
        (mfderiv (𝓡 3) (𝓡 4) D x).toLinearMap.range = ⊤)
      ↔ ((fderiv ℝ (fun v => chartAt (EuclideanSpace ℝ (Fin 4)) (A u) (A v)) u).toLinearMap.range ⊔
          (fderiv ℝ (fun v => chartAt (EuclideanSpace ℝ (Fin 4)) (A u) (D v)) x).toLinearMap.range
            = ⊤) := by
  have hAu : A u ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) (A u)).source := mem_chart_source _ _
  have hDx : D x ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) (A u)).source := by
    rw [← hval]; exact mem_chart_source _ _
  have h1 := fderiv_chartAt_comp A (hA.contMDiffAt) (A u) hAu
  have h2 := fderiv_chartAt_comp D (hD.contMDiffAt) (A u) hDx
  have hid : tangentCoordChange (𝓡 4) (A u) (A u) (A u)
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.id_apply]
    exact tangentCoordChange_self (I := 𝓡 4) (x := A u) (z := A u) (v := v)
      (mem_extChartAt_source (A u))
  have htc : tangentCoordChange (𝓡 4) (D x) (A u) (D x)
      = tangentCoordChange (𝓡 4) (A u) (A u) (A u) := by rw [hval]
  have h2' : fderiv ℝ (fun v => chartAt (EuclideanSpace ℝ (Fin 4)) (A u) (D v)) x
      = (tangentCoordChange (𝓡 4) (A u) (A u) (A u)) ∘SL (mfderiv (𝓡 3) (𝓡 4) D x) := by
    rw [h2, htc]
  rw [h1, h2', hid]
  simp only [ContinuousLinearMap.id_comp]
  exact Iff.rfl

end

end Work.Drive
