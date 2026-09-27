import Mathlib
import Submission.Work.Projection.exists_countable_chart_cover
import Submission.Work.Projection.mfderiv_chartAt_decomp

namespace Work.Projection

open scoped Manifold ContDiff Topology
open MeasureTheory Filter

/-- The determinant is multiplicative on a composition of continuous linear endomorphisms. -/
lemma det_comp_clm {R M : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (f g : M →L[R] M) : (f.comp g).det = f.det * g.det := by
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

/-- The determinant of the identity continuous linear map is `1`. -/
lemma det_id_clm {R M : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M]
    [Module R M] : (ContinuousLinearMap.id R M).det = 1 := by
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]

/-- The derivative of a chart is invertible, hence has nonzero determinant. -/
lemma chartAt_mfderiv_det_ne_zero {m : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) Z] [IsManifold (𝓡 m) ∞ Z] (q z : Z)
    (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin m)) q).source) :
    (mfderiv (𝓡 m) (𝓡 m) (chartAt (EuclideanSpace ℝ (Fin m)) q) z).det ≠ 0 := by
  set e := chartAt (EuclideanSpace ℝ (Fin m)) q with he
  set A := mfderiv (𝓡 m) (𝓡 m) e.symm (e z) with hA
  set B := mfderiv (𝓡 m) (𝓡 m) e z with hB
  -- the chart followed by its inverse is the identity near `z`
  have hev : (fun w : Z => e.symm (e w)) =ᶠ[𝓝 z] id := by
    filter_upwards [e.open_source.mem_nhds hz] with w hw
    exact e.left_inv hw
  have h1 : mfderiv (𝓡 m) (𝓡 m) (fun w : Z => e.symm (e w)) z
      = ContinuousLinearMap.id ℝ _ := by
    rw [hev.mfderiv_eq, mfderiv_id]; ext v; rfl
  have h2 : mfderiv (𝓡 m) (𝓡 m) (fun w : Z => e.symm (e w)) z = A ∘L B := by
    rw [hA, hB]
    exact mfderiv_comp z (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) (e.map_source hz))
      (mdifferentiableAt_atlas (chart_mem_atlas _ _) hz)
  have hcomp : A ∘L B = ContinuousLinearMap.id ℝ _ := by rw [← h2]; exact h1
  have hdet1 : A.det * B.det = 1 := by
    have hmul := det_comp_clm A B
    have hid1 : (A ∘L B).det = 1 := by
      rw [hcomp]
      exact det_id_clm
    exact hmul.symm.trans hid1
  -- hence `B` has a left inverse, so `det B ≠ 0`
  intro hzero
  have h0 : A.det * B.det = 0 := by rw [hzero, mul_zero]
  exact one_ne_zero (hdet1.symm.trans h0)

/-- The chart representation of a smooth map into `ℝ^m` is differentiable on the chart target. -/
lemma chartRep_differentiableAt {m : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) Z] [IsManifold (𝓡 m) ∞ Z] 
    (p : Z → EuclideanSpace ℝ (Fin m))
    (hp : ContMDiff (𝓡 m) (𝓡 m) ∞ p) (q : Z)
    {y : EuclideanSpace ℝ (Fin m)} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin m)) q).target) :
    DifferentiableAt ℝ (fun y => p ((chartAt (EuclideanSpace ℝ (Fin m)) q).symm y)) y := by
  have hsymm : MDifferentiableAt (𝓡 m) (𝓡 m)
      ((chartAt (EuclideanSpace ℝ (Fin m)) q).symm) y :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) hy
  have hp' : MDifferentiableAt (𝓡 m) (𝓡 m) p
      (((chartAt (EuclideanSpace ℝ (Fin m)) q).symm) y) :=
    (hp _).mdifferentiableAt (by simp)
  have hcomp : MDifferentiableAt (𝓡 m) (𝓡 m)
      (p ∘ (chartAt (EuclideanSpace ℝ (Fin m)) q).symm) y :=
    MDifferentiableAt.comp y hp' hsymm
  exact mdifferentiableAt_iff_differentiableAt.mp hcomp

/-- At a critical point `z` of `p` (in the chart at `q`), the chart representation of `p` has
vanishing determinant of its derivative at `e z`. -/
lemma chartRep_fderiv_det_eq_zero {m : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) Z] [IsManifold (𝓡 m) ∞ Z] 
    (p : Z → EuclideanSpace ℝ (Fin m))
    (hp : ContMDiff (𝓡 m) (𝓡 m) ∞ p) (q z : Z)
    (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin m)) q).source)
    (hcrit : (mfderiv (𝓡 m) (𝓡 m) p z).det = 0) :
    (fderiv ℝ (fun y => p ((chartAt (EuclideanSpace ℝ (Fin m)) q).symm y))
      ((chartAt (EuclideanSpace ℝ (Fin m)) q) z)).det = 0 := by
  set C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fderiv ℝ (fun y => p ((chartAt (EuclideanSpace ℝ (Fin m)) q).symm y))
      ((chartAt (EuclideanSpace ℝ (Fin m)) q) z) with hC
  set B := mfderiv (𝓡 m) (𝓡 m) (chartAt (EuclideanSpace ℝ (Fin m)) q) z with hB
  have hdec : mfderiv (𝓡 m) (𝓡 m) p z = C ∘L B := by
    rw [hB, hC]
    exact mfderiv_chartAt_decomp p hp q z hz
  have hBne : B.det ≠ 0 := by
    rw [hB]
    exact chartAt_mfderiv_det_ne_zero q z hz
  have hdet : C.det * B.det = 0 := by
    have hmul := det_comp_clm C B
    have h0 : (C ∘L B).det = 0 := by rw [← hdec]; exact hcrit
    exact hmul.symm.trans h0
  rcases mul_eq_zero.mp hdet with h | h
  · exact h
  · exact absurd h hBne

/-- The image under `p` of the critical points lying in a single chart has measure zero. -/
lemma image_crit_inter_chart_eq_zero {m : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) Z] [IsManifold (𝓡 m) ∞ Z] 
    (p : Z → EuclideanSpace ℝ (Fin m))
    (hp : ContMDiff (𝓡 m) (𝓡 m) ∞ p) (q : Z) :
    volume (p '' ({z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0} ∩
      (chartAt (EuclideanSpace ℝ (Fin m)) q).source)) = 0 := by
  set e := chartAt (EuclideanSpace ℝ (Fin m)) q with he
  set F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun y => p (e.symm y) with hF
  set A := ({z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0} ∩ e.source) with hA
  have hpe : ∀ z ∈ A, p z = F (e z) := by
    intro z hz
    rw [hF]
    exact congrArg p (e.left_inv hz.2).symm
  have himg : p '' A = F '' (e '' A) := by
    rw [← Set.image_comp]
    exact Set.image_congr hpe
  rw [himg]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
    (s := e '' A) (f := F) (f' := fun y => fderiv ℝ F y) ?_ ?_
  · intro y hy
    obtain ⟨z, hzA, hzy⟩ := hy
    subst hzy
    have hy' : e z ∈ (chartAt (EuclideanSpace ℝ (Fin m)) q).target := e.map_source hzA.2
    have hdiff : DifferentiableAt ℝ F (e z) := by
      rw [hF, he]
      exact chartRep_differentiableAt p hp q hy'
    exact hdiff.hasFDerivAt.hasFDerivWithinAt
  · intro y hy
    obtain ⟨z, hzA, hzy⟩ := hy
    subst hzy
    have hd : (fderiv ℝ F (e z)).det = 0 := by
      rw [hF, he]
      exact chartRep_fderiv_det_eq_zero p hp q z hzA.2 hzA.1
    exact hd

/-- **Sard in equal dimension, for manifolds**: the set of critical values of a smooth map
`p : Z → ℝ^m` from a second countable smooth `m`-manifold into `ℝ^m` — i.e. the image of the set of
points where the derivative is not invertible — has Lebesgue measure zero.

Suggested proof: cover `Z` by countably many chart sources (second countability); on a chart `e`,
with `F = p ∘ e.symm`, one has `det (fderiv F (e z)) = det (mfderiv p z) · det (mfderiv e.symm)`
with `det (mfderiv e.symm) ≠ 0`, so the critical points of `p` in the chart map into the
det-zero set of `F`; apply Mathlib's
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`
(in `Mathlib/MeasureTheory/Function/Jacobian.lean`, stated for `f : E → E` with a given derivative
whose determinant vanishes on the set) and use that a countable union of null sets is null. -/
theorem volume_image_criticalValues_eq_zero {m : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) Z] [IsManifold (𝓡 m) ∞ Z] [T2Space Z]
    [SecondCountableTopology Z]
    (p : Z → EuclideanSpace ℝ (Fin m)) (hp : ContMDiff (𝓡 m) (𝓡 m) ∞ p) :
    volume (p '' {z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0}) = 0 := by
  by_cases hne : Nonempty Z
  · haveI := hne
    obtain ⟨q, hq⟩ := exists_countable_chart_cover m Z
    have hchart : ∀ i : ℕ, volume (p '' ({z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0} ∩
        (chartAt (EuclideanSpace ℝ (Fin m)) (q i)).source)) = 0 :=
      fun i => image_crit_inter_chart_eq_zero p hp (q i)
    have hcover : ({z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0}) ⊆
        ⋃ i, ({z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0} ∩
          (chartAt (EuclideanSpace ℝ (Fin m)) (q i)).source) := by
      intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hq (Set.mem_univ z))
      exact Set.mem_iUnion.mpr ⟨i, hz, hi⟩
    have hle : volume (p '' {z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0}) ≤ 0 :=
      calc volume (p '' {z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0})
        ≤ volume (p '' ⋃ i, ({z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0} ∩
            (chartAt (EuclideanSpace ℝ (Fin m)) (q i)).source)) :=
          measure_mono (Set.image_mono hcover)
      _ = volume (⋃ i, p '' ({z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0} ∩
            (chartAt (EuclideanSpace ℝ (Fin m)) (q i)).source)) := by
          rw [Set.image_iUnion]
      _ ≤ ∑' i, volume (p '' ({z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0} ∩
            (chartAt (EuclideanSpace ℝ (Fin m)) (q i)).source)) := measure_iUnion_le _
      _ = 0 := by simp [hchart]
    exact le_antisymm hle bot_le
  · have hempty : {z : Z | (mfderiv (𝓡 m) (𝓡 m) p z).det = 0} = ∅ := by
      ext z
      exact ⟨fun _ => hne ⟨z⟩, False.elim⟩
    rw [hempty, Set.image_empty, measure_empty]

end Work.Projection
