import Mathlib

open Classical

namespace Work.TMComp.RedProj.Part2

/-- Auxiliary: the candidate global function, defined by picking, at each point of the
union of the polydiscs, some polydisc that contains it and evaluating the corresponding
`F i j` there; `0` outside the union. -/
noncomputable def glueFun {ι κ : Type*} (E : ι → ℝ) (X : κ → ℝ) (s : ι → ℝ) (t : κ → ℝ)
    (F : ι → κ → ℂ × ℂ → ℂ) (z : ℂ × ℂ) : ℂ :=
  if hz : z ∈ (⋃ i, Metric.ball (E i : ℂ) (s i)) ×ˢ (⋃ j, Metric.ball (X j : ℂ) (t j)) then
    F (Classical.choose (Set.mem_iUnion.mp (Set.mem_prod.mp hz).1))
      (Classical.choose (Set.mem_iUnion.mp (Set.mem_prod.mp hz).2)) z
  else 0

/-- The value of `glueFun` at a point of a polydisc equals the value of the corresponding
`F i j`, thanks to the overlap-agreement hypothesis. -/
lemma glueFun_eq {ι κ : Type*} (E : ι → ℝ) (X : κ → ℝ) (s : ι → ℝ) (t : κ → ℝ)
    (F : ι → κ → ℂ × ℂ → ℂ)
    (hagree : ∀ i j i' j', ((Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j)) ∩
        (Metric.ball (E i' : ℂ) (s i') ×ˢ Metric.ball (X j' : ℂ) (t j'))) ≠ ∅ →
        Set.EqOn (F i j) (F i' j')
          ((Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j)) ∩
           (Metric.ball (E i' : ℂ) (s i') ×ˢ Metric.ball (X j' : ℂ) (t j'))))
    (i : ι) (j : κ) {z : ℂ × ℂ}
    (hz : z ∈ Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j)) :
    glueFun E X s t F z = F i j z := by
  have hzU : z ∈ (⋃ i, Metric.ball (E i : ℂ) (s i)) ×ˢ (⋃ j, Metric.ball (X j : ℂ) (t j)) :=
    Set.prod_mono (Set.subset_iUnion _ i) (Set.subset_iUnion _ j) hz
  have key : ∀ (i' : ι) (j' : κ),
      z.1 ∈ Metric.ball (E i' : ℂ) (s i') → z.2 ∈ Metric.ball (X j' : ℂ) (t j') →
      F i' j' z = F i j z := by
    intro i' j' hi' hj'
    have hzP' : z ∈ Metric.ball (E i' : ℂ) (s i') ×ˢ Metric.ball (X j' : ℂ) (t j') :=
      Set.mem_prod.mpr ⟨hi', hj'⟩
    have hinter : ((Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j)) ∩
        (Metric.ball (E i' : ℂ) (s i') ×ˢ Metric.ball (X j' : ℂ) (t j'))) ≠ ∅ :=
      Set.nonempty_iff_ne_empty.mp ⟨z, hz, hzP'⟩
    exact ((hagree i j i' j' hinter) ⟨hz, hzP'⟩).symm
  unfold glueFun
  rw [dif_pos hzU]
  exact key _ _ (Classical.choose_spec (Set.mem_iUnion.mp (Set.mem_prod.mp hzU).1))
    (Classical.choose_spec (Set.mem_iUnion.mp (Set.mem_prod.mp hzU).2))

theorem GluePolydisc {ι κ : Type*} (E : ι → ℝ) (X : κ → ℝ) (s : ι → ℝ) (t : κ → ℝ)
    (hs : ∀ i, 0 < s i) (ht : ∀ j, 0 < t j) (F : ι → κ → ℂ × ℂ → ℂ)
    (hF : ∀ i j, AnalyticOnNhd ℂ (F i j) (Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j)))
    (hagree : ∀ i j i' j', ((Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j)) ∩
        (Metric.ball (E i' : ℂ) (s i') ×ˢ Metric.ball (X j' : ℂ) (t j'))) ≠ ∅ →
        Set.EqOn (F i j) (F i' j')
          ((Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j)) ∩
           (Metric.ball (E i' : ℂ) (s i') ×ˢ Metric.ball (X j' : ℂ) (t j')))) :
    ∃ G : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ G ((⋃ i, Metric.ball (E i : ℂ) (s i)) ×ˢ (⋃ j, Metric.ball (X j : ℂ) (t j))) ∧
      ∀ i j, Set.EqOn G (F i j) (Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j)) := by
  refine ⟨glueFun E X s t F, ?_, ?_⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := Set.mem_prod.mp hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h2
    have hzij : z ∈ Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j) :=
      Set.mem_prod.mpr ⟨hi, hj⟩
    have hAn : AnalyticOnNhd ℂ (glueFun E X s t F)
        (Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (X j : ℂ) (t j)) :=
      (hF i j).congr (Metric.isOpen_ball.prod Metric.isOpen_ball)
        (fun w hw => (glueFun_eq E X s t F hagree i j hw).symm)
    exact hAn z hzij
  · intro i j z hz
    exact glueFun_eq E X s t F hagree i j hz

end Work.TMComp.RedProj.Part2
