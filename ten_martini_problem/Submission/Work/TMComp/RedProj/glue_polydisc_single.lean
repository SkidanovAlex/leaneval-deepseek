import Mathlib

namespace Work.TMComp.RedProj

/-- Gluing of analytic functions on a family of polydiscs that pairwise agree on
their (nonempty) overlaps.  Since `AnalyticOnNhd` is the local notion
(`∀ x ∈ s, AnalyticAt 𝕜 f x`), no connectedness input is needed: at a point of
the `i`-th polydisc the glued function agrees with `F i` on the whole open
polydisc, hence is analytic there. -/
theorem glue_polydisc_single {ι : Type*} (a b s t : ι → ℝ) (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (F : ι → ℂ × ℂ → ℂ)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)))
    (hagree : ∀ i j, ((Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)) ∩
        (Metric.ball (a j : ℂ) (s j) ×ˢ Metric.ball (b j : ℂ) (t j))).Nonempty →
        Set.EqOn (F i) (F j)
          ((Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)) ∩
           (Metric.ball (a j : ℂ) (s j) ×ˢ Metric.ball (b j : ℂ) (t j)))) :
    ∃ G : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ G (⋃ i, Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)) ∧
      ∀ i, Set.EqOn G (F i) (Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)) := by
  classical
  -- the `i`-th polydisc
  let B : ι → Set (ℂ × ℂ) := fun i => Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)
  -- the glued function: pick any polydisc containing the point
  let G : ℂ × ℂ → ℂ := fun z => if h : ∃ i, z ∈ B i then F (Classical.choose h) z else 0
  -- `G` agrees with `F i` on the `i`-th polydisc
  have hG : ∀ i, Set.EqOn G (F i) (B i) := by
    intro i w hw
    have hp : ∃ j, w ∈ B j := ⟨i, hw⟩
    show (if h : ∃ j, w ∈ B j then F (Classical.choose h) w else 0) = F i w
    rw [dif_pos hp]
    have hspec : w ∈ B (Classical.choose hp) := Classical.choose_spec hp
    exact ((hagree i (Classical.choose hp) ⟨w, hw, hspec⟩) ⟨hw, hspec⟩).symm
  refine ⟨G, fun z hz => ?_, hG⟩
  rw [Set.mem_iUnion] at hz
  obtain ⟨i, hi⟩ := hz
  -- `G = F i` on the open polydisc `B i`, which is a neighbourhood of `z`
  have hopen : IsOpen (B i) := (Metric.isOpen_ball).prod (Metric.isOpen_ball)
  have hEq : G =ᶠ[nhds z] F i := Filter.eventuallyEq_of_mem (hopen.mem_nhds hi) (hG i)
  exact (hF i z hi).congr hEq.symm

end Work.TMComp.RedProj
