import Mathlib
import Submission.Work.NN.Seeley.Glob
import Submission.Work.NN.Seeley.gDN_halfspace_closed_le

namespace Work.NN.Seeley

open Filter Set
open scoped Topology

/-- The analogue of `Work.NN.Seeley.gDN_halfspace_closed_le` for the lower half space
`{p.2 ≤ 0}` (the same proof with `nhdsWithin` below `0` instead of above). -/
theorem gDN_lower_halfspace_closed_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X × ℝ → ℂ} {i : ℕ}
    (hf : ∀ x : X × ℝ, x.2 ≤ 0 → ContDiffAt ℝ (i + 1) f x) :
    Work.NN.Final.gDN i f {p : X × ℝ | p.2 ≤ 0}
      ≤ Work.NN.Final.gDN i f {p : X × ℝ | p.2 < 0} := by
  refine iSup₂_le fun x hx => ?_
  have hx' : x.2 ≤ 0 := hx
  rcases eq_or_lt_of_le hx' with h0 | hneg
  · have hcont : ContinuousAt (iteratedFDeriv ℝ i f) x :=
      (hf x hx').continuousAt_iteratedFDeriv (k := i)
        (by exact_mod_cast Nat.le_succ i)
    have h2 : (x.1, (0 : ℝ)) = x := Prod.ext rfl h0.symm
    have hφ : Tendsto (fun t : ℝ => (x.1, t)) (𝓝[<] (0 : ℝ)) (𝓝 x) := by
      have h1 : Tendsto (fun t : ℝ => (x.1, t)) (𝓝 (0 : ℝ)) (𝓝 ((x.1, (0 : ℝ)))) :=
        (Continuous.prodMk (continuous_const : Continuous fun _ : ℝ => x.1)
          continuous_id).tendsto 0
      rw [h2] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have hiter : Tendsto (fun t : ℝ => iteratedFDeriv ℝ i f (x.1, t)) (𝓝[<] (0 : ℝ))
        (𝓝 (iteratedFDeriv ℝ i f x)) := hcont.tendsto.comp hφ
    have hof : Tendsto (fun t : ℝ => ENNReal.ofReal ‖iteratedFDeriv ℝ i f (x.1, t)‖)
        (𝓝[<] (0 : ℝ)) (𝓝 (ENNReal.ofReal ‖iteratedFDeriv ℝ i f x‖)) :=
      ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hiter
    refine le_of_tendsto hof ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Work.NN.Final.le_gDN i ht
  · exact Work.NN.Final.le_gDN i hneg

end Work.NN.Seeley
