import Mathlib

/-!
# The finite-intersection bookkeeping of the localized pair Sard

A finite family of open sets, each dense in a ball, has an intersection dense in that ball.  This is
the pair-route copy of the (private) helpers of `Work.Drive.localSard`, needed to combine the good
parameter sets of the finitely many pieces into one parameter.
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- A finite family of positive reals has a positive lower bound. -/
lemma exists_pos_le_all {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ρ ≤ f i := by
  classical
  by_cases h : (Finset.univ : Finset ι).Nonempty
  · refine ⟨(Finset.univ : Finset ι).inf' h f, ?_, fun i => Finset.inf'_le f (Finset.mem_univ i)⟩
    rw [Finset.lt_inf'_iff h]
    exact fun i _ => hf i
  · exact ⟨1, one_pos, fun i => absurd ⟨i, Finset.mem_univ i⟩ h⟩

/-- An open set containing the ball of radius `ρ` in its closure, together with another set containing
the ball in its closure, has its intersection doing the same. -/
lemma pp_ball_subset_closure_inter {E : Type*} [PseudoMetricSpace E] [Zero E]
    {A B : Set E} {ρ : ℝ} (hA : IsOpen A) (hdA : Metric.ball 0 ρ ⊆ closure A)
    (hdB : Metric.ball 0 ρ ⊆ closure B) : Metric.ball 0 ρ ⊆ closure (A ∩ B) := by
  intro x hx
  have hxρ : dist x 0 < ρ := by rwa [Metric.mem_ball] at hx
  have hdA' : ∀ ε > 0, ∃ y ∈ A, dist x y < ε := fun ε hε =>
    Metric.mem_closure_iff.mp (hdA hx) ε hε
  have hdB' : ∀ y : E, dist y 0 < ρ → ∀ ε > 0, ∃ z ∈ B, dist y z < ε := by
    intro y hy ε hε
    exact Metric.mem_closure_iff.mp (hdB (by rwa [Metric.mem_ball])) ε hε
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hρx : 0 < ρ - dist x 0 := by linarith
  obtain ⟨y, hyA, hxy⟩ := hdA' (min ε (ρ - dist x 0) / 4)
    (div_pos (lt_min hε hρx) (by norm_num))
  have hyρ : dist y 0 < ρ := by
    have h2 : dist y x < min ε (ρ - dist x 0) / 4 := by rwa [dist_comm] at hxy
    have h3 : min ε (ρ - dist x 0) / 4 < ρ - dist x 0 := by
      have := min_le_right ε (ρ - dist x 0); linarith
    calc dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
      _ < ρ := by linarith
  obtain ⟨η, hηpos, hηsub⟩ := Metric.isOpen_iff.mp hA y hyA
  obtain ⟨z, hzB, hyz⟩ := hdB' y hyρ (min η (min ε (ρ - dist x 0) / 4))
    (lt_min hηpos (div_pos (lt_min hε hρx) (by norm_num)))
  refine ⟨z, ⟨?_, hzB⟩, ?_⟩
  · refine hηsub ?_
    rw [Metric.mem_ball, dist_comm]
    exact lt_of_lt_of_le hyz (min_le_left _ _)
  · have h1 : dist x y < min ε (ρ - dist x 0) / 4 := hxy
    have h2 : dist y z < min ε (ρ - dist x 0) / 4 := lt_of_lt_of_le hyz (min_le_right _ _)
    have h3 : min ε (ρ - dist x 0) ≤ ε := min_le_left _ _
    calc dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ < ε := by linarith

/-- A finite intersection of open sets, each dense in the ball of radius `ρ`, is dense in that
ball. -/
lemma pp_dense_iInter_of_dense_ball {ι : Type*} [Fintype ι]
    {E : Type*} [PseudoMetricSpace E] [Zero E] (A : ι → Set E) (ρ : ℝ)
    (hA : ∀ i, IsOpen (A i)) (hd : ∀ i, Metric.ball 0 ρ ⊆ closure (A i)) :
    Metric.ball 0 ρ ⊆ closure (⋂ i, A i) := by
  classical
  have key : ∀ s : Finset ι, (∀ i ∈ s, IsOpen (A i)) →
      (∀ i ∈ s, Metric.ball 0 ρ ⊆ closure (A i)) →
      Metric.ball 0 ρ ⊆ closure (⋂ i ∈ s, A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ _; simp
    | insert a s ha ih =>
        intro h1 h2
        rw [Finset.set_biInter_insert]
        refine pp_ball_subset_closure_inter (h1 a (Finset.mem_insert_self a s))
          (h2 a (Finset.mem_insert_self a s)) ?_
        exact ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h2 i (Finset.mem_insert_of_mem hi))
  have := key Finset.univ (fun i _ => hA i) (fun i _ => hd i)
  simpa using this

end

end Work.Drive
