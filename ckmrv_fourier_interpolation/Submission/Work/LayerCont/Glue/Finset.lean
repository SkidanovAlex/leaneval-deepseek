/-
# Gluing a **finite** family of charts

`Work.LayerCont.Glue.exists_glue_two_balls'` glues two charts unconditionally.  Here we iterate it
over a finite family: given a finite index set `s`, a ball `B(cᵢ,εᵢ)` and a function `fᵢ`
holomorphic on it for each `i ∈ s`, and *pairwise* agreement
`fᵢ = fⱼ` on `B(cᵢ,εᵢ) ∩ B(cⱼ,εⱼ)`, there is a single holomorphic `K` on the union agreeing with
each `fᵢ` on its ball.  (The pairwise agreement is what the identity theorem
`Work.LayerCont.Glue.eqOn_of_mdifferentiableOn_of_preconnected` produces from "agree on a non-empty
open subset of the intersection", the intersections being preconnected by
`Work.LayerCont.Glue.isPreconnected_inter_ball`.)

The proof is `Finset.induction_on`; the induction step glues the accumulated function with the new
chart via `Work.LayerCont.exists_mdifferentiableOn_glue`, the agreement on the intersection being
read off from the pairwise agreement piece by piece (so no connectedness is needed at this stage).
-/
import Mathlib
import Submission.Work.LayerCont.Glue.ConnBall

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Glue

open Work.Asymptotics Work.LayerCont

/-- **Gluing a finite family of charts.** -/
theorem exists_glue_finset {ι : Type*} (s : Finset ι)
    (c : ι → UpperHalfPlane) (ε : ι → ℝ) (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i ∈ s, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (f i)
      (Metric.ball (c i) (ε i)))
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      Set.EqOn (f i) (f j) (Metric.ball (c i) (ε i) ∩ Metric.ball (c j) (ε j))) :
    ∃ K : UpperHalfPlane → ℂ,
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) K
        (⋃ i ∈ (s : Set ι), Metric.ball (c i) (ε i)) ∧
      (∀ i ∈ s, Set.EqOn K (f i) (Metric.ball (c i) (ε i))) := by
  classical
  revert hf hpair
  refine Finset.induction_on s ?_ ?_
  · intro hf hpair
    refine ⟨0, ?_, ?_⟩
    · intro x hx
      exact absurd hx (by simp)
    · intro i hi
      simp at hi
  · intro a s has ih hf hpair
    have hfs : ∀ i ∈ s, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (f i) (Metric.ball (c i) (ε i)) :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hps : ∀ i ∈ s, ∀ j ∈ s,
        Set.EqOn (f i) (f j) (Metric.ball (c i) (ε i) ∩ Metric.ball (c j) (ε j)) :=
      fun i hi j hj => hpair i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    obtain ⟨K, hK, hKag⟩ := ih hfs hps
    -- the accumulated function agrees with the new chart on the intersection
    have hag : Set.EqOn K (f a) ((⋃ i ∈ (s : Set ι), Metric.ball (c i) (ε i))
        ∩ Metric.ball (c a) (ε a)) := by
      rintro x ⟨hxS, hxa⟩
      simp only [Set.mem_iUnion] at hxS
      obtain ⟨i, hi, hxi⟩ := hxS
      exact (hKag i hi hxi).trans
        (hpair i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s) ⟨hxi, hxa⟩)
    have hSopen : IsOpen (⋃ i ∈ (s : Set ι), Metric.ball (c i) (ε i)) :=
      isOpen_biUnion (fun i _ => Metric.isOpen_ball)
    obtain ⟨F, hF, hF₁, hF₂⟩ := Work.LayerCont.exists_mdifferentiableOn_glue hSopen
      Metric.isOpen_ball hK (hf a (Finset.mem_insert_self a s)) hag
    refine ⟨F, ?_, ?_⟩
    · rw [Finset.coe_insert, Set.biUnion_insert, Set.union_comm]
      exact hF
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hF₂
      · intro x hx
        exact (hF₁ (Set.mem_biUnion hi hx)).trans (hKag i hi hx)

end Work.LayerCont.Glue
