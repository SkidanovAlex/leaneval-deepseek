import Mathlib

namespace Work.NN.Final

/-- Auxiliary: a function `g` which agrees with `f` on `Ω` is continuous at `y`, provided
`Ω ∪ H` is a neighbourhood of `y`, every point of `H` is a limit point of `Ω`, and `f` tends
to `g z` along `Ω` at every `z ∈ H`. -/
theorem continuousAt_of_tendsto_nhdsWithin
    {E : Type*} [TopologicalSpace E] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {Ω H : Set E} {f g : E → Z} {y : E}
    (hgΩ : Set.EqOn g f Ω) (hy : y ∈ H)
    (hcover : Ω ∪ H ∈ nhds y)
    (hcl : ∀ z ∈ H, z ∈ closure Ω)
    (hlim : ∀ z ∈ H, Filter.Tendsto f (nhdsWithin z Ω) (nhds (g z))) :
    ContinuousAt g y := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  -- Work with the open ball of radius ε/3 around `g y`.
  have hδpos : (0 : ℝ) < ε / 3 := by linarith
  -- Points of `Ω` close to `y` have `f`-image (hence `g`-image) inside the ball.
  have h1 : f ⁻¹' Metric.ball (g y) (ε / 3) ∈ nhdsWithin y Ω :=
    (hlim y hy) (Metric.ball_mem_nhds (g y) hδpos)
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at h1
  obtain ⟨S0, hS0, hS0sub⟩ := h1
  obtain ⟨O, hOsub, hOopen, hyO⟩ := mem_nhds_iff.mp hS0
  -- It suffices to control `g` on the neighbourhood `O ∩ (Ω ∪ H)` of `y`.
  refine Filter.eventually_of_mem (U := O ∩ (Ω ∪ H))
    (Filter.inter_mem (hOopen.mem_nhds hyO) hcover) ?_
  intro z hz
  obtain ⟨hzO, hzOH⟩ := hz
  have hzS0 : z ∈ S0 := hOsub hzO
  rcases hzOH with hzΩ | hzH
  · -- `z ∈ Ω`: then `g z = f z` and `f z` is close to `g y`.
    rw [hgΩ hzΩ]
    have hzball : f z ∈ Metric.ball (g y) (ε / 3) := hS0sub ⟨hzS0, hzΩ⟩
    have := Metric.mem_ball.mp hzball
    linarith
  · -- `z ∈ H`: `g z` is the limit of `f` along `Ω` at `z`, and `z` is an accumulation
    -- point of `Ω`; choosing `w ∈ Ω` close to both `z` and `y` gives the bound.
    have h2 : f ⁻¹' Metric.ball (g z) (ε / 3) ∈ nhdsWithin z Ω :=
      (hlim z hzH) (Metric.ball_mem_nhds (g z) hδpos)
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at h2
    obtain ⟨Sz, hSz, hSzsub⟩ := h2
    -- `S0` is a neighbourhood of `z` because `O ∋ z` is open and `O ⊆ S0`.
    have hS0z : S0 ∈ nhds z := Filter.mem_of_superset (hOopen.mem_nhds hzO) hOsub
    have hne : ((Sz ∩ S0) ∩ Ω).Nonempty :=
      (mem_closure_iff_nhds.mp (hcl z hzH)) (Sz ∩ S0) (Filter.inter_mem hSz hS0z)
    obtain ⟨w, hwS, hwΩ⟩ := hne
    have hwSz : w ∈ Sz := hwS.1
    have hwS0 : w ∈ S0 := hwS.2
    have hw1 : dist (f w) (g z) < ε / 3 := Metric.mem_ball.mp (hSzsub ⟨hwSz, hwΩ⟩)
    have hw2 : dist (f w) (g y) < ε / 3 := Metric.mem_ball.mp (hS0sub ⟨hwS0, hwΩ⟩)
    calc dist (g z) (g y) ≤ dist (g z) (f w) + dist (f w) (g y) := dist_triangle _ _ _
      _ = dist (f w) (g z) + dist (f w) (g y) := by rw [dist_comm (g z) (f w)]
      _ < ε / 3 + ε / 3 := by linarith
      _ < ε := by linarith

end Work.NN.Final
