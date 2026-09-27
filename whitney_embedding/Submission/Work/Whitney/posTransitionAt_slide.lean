import Mathlib
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Whitney.PosTransitionAtAlg

/-!
# Sliding the base point along an arc

`PosTransitionAt e f x` is the positivity of the determinant of the differential, at `e x`, of the
chart transition `f ∘ e.symm`.  This file proves that this sign is *constant* as the base point
slides along a continuous arc staying inside `e.source ∩ f.source`: the transition is a local
diffeomorphism there, so the determinant of its Jacobian is a continuous nowhere-zero function on
a connected set.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The transition sign is unchanged along an arc.**  If `γ` maps `[p,q]` into the common source
of two smooth charts `e`, `f`, then `e` and `f` are positively related at `γ p` iff they are
positively related at `γ q`. -/
theorem posTransitionAt_slide
    {e f : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : Work.Whitney.IsSmoothChart e) (hf : Work.Whitney.IsSmoothChart f)
    {γ : ℝ → M} (hγ : Continuous γ)
    {p q : ℝ} (hpq : p ≤ q) (hsub : γ '' Set.Icc p q ⊆ e.source ∩ f.source) :
    (Work.Whitney.PosTransitionAt e f (γ p) ↔ Work.Whitney.PosTransitionAt e f (γ q)) := by
  rw [Work.Whitney.PosTransitionAt, Work.Whitney.PosTransitionAt]
  set φ : ℝ → ℝ :=
    fun t => (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (e.symm u)) (e (γ t))).det with hφ
  have hmem : ∀ t ∈ Set.Icc p q, γ t ∈ e.source ∩ f.source := fun t ht => hsub ⟨t, ht, rfl⟩
  have hne : ∀ t ∈ Set.Icc p q, φ t ≠ 0 := by
    intro t ht
    have hprod := det_transition_mul he hf (hmem t ht).1 (hmem t ht).2
    intro hzero
    rw [hφ] at hzero
    simp only at hzero
    rw [hzero, zero_mul] at hprod
    exact one_ne_zero hprod.symm
  have hcont : ContinuousOn φ (Set.Icc p q) := by
    intro t0 ht0
    have hm := hmem t0 ht0
    have hG : ContDiffAt ℝ (1 : ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin n) => f (e.symm u)) (e (γ t0)) := by
      have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) f (e.symm (e (γ t0))) := by
        rw [e.left_inv hm.1]
        exact hf.1.contMDiffAt (f.open_source.mem_nhds hm.2)
      have h2 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm
          (e (γ t0)) :=
        he.2.contMDiffAt (e.open_target.mem_nhds (e.map_source hm.1))
      exact ((ContMDiffAt.comp (x := e (γ t0)) h1 h2).contDiffAt).of_le (by simp)
    have hdet : ContinuousAt
        (fun v : EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (e.symm u)) v).det) (e (γ t0)) :=
      ContinuousLinearMap.continuous_det.continuousAt.comp (hG.continuousAt_fderiv (by simp))
    have hγe : ContinuousAt (fun t => e (γ t)) t0 := (e.continuousAt hm.1).comp hγ.continuousAt
    have hcomp : ContinuousAt
        (fun t => (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (e.symm u)) (e (γ t))).det) t0 :=
      ContinuousAt.comp (x := t0) (f := fun t => e (γ t))
        (g := fun v : EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (e.symm u)) v).det) hdet hγe
    rw [hφ]
    exact hcomp.continuousWithinAt
  constructor
  · intro hp
    by_contra hq
    have hq' : φ q < 0 := lt_of_le_of_ne (not_lt.mp hq) (hne q ⟨hpq, le_rfl⟩)
    have hzero : (0 : ℝ) ∈ Set.Icc (φ q) (φ p) := ⟨le_of_lt hq', le_of_lt hp⟩
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hpq hcont hzero
    exact hne c hc hc0
  · intro hq
    by_contra hp
    have hp' : φ p < 0 := lt_of_le_of_ne (not_lt.mp hp) (hne p ⟨le_rfl, hpq⟩)
    have hzero : (0 : ℝ) ∈ Set.Icc (φ p) (φ q) := ⟨le_of_lt hp', le_of_lt hq⟩
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hpq hcont hzero
    exact hne c hc hc0

end Work.Whitney
