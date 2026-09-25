import Mathlib
import Submission.Work.NN.Seeley.gDN_halfspace_closed_le

namespace Work.NN.Seeley

open Filter Set
open scoped Topology

/-- At a boundary point `x` (`x.2 = 0`) of the open half space `{0 < p.2}`, the value
`ofReal ‖D^i f x‖` is bounded by `gDN i f {0 < p.2}`: the point `x` is the limit of the interior
points `(x.1, t)` with `t → 0+`, at which the bound `le_gDN` holds, and `D^i f` is continuous at
`x` because `f` is `C^{i+1}` there. -/
theorem ofReal_norm_iteratedFDeriv_le_gDN_halfspace {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : X × ℝ → ℂ} {i : ℕ} {x : X × ℝ} (hx : x.2 = 0)
    (hf : ContDiffAt ℝ (i + 1) f x) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ i f x‖
      ≤ Work.NN.Final.gDN i f {p : X × ℝ | 0 < p.2} := by
  have hcont : ContinuousAt (iteratedFDeriv ℝ i f) x :=
    hf.continuousAt_iteratedFDeriv (k := i) (by exact_mod_cast Nat.le_succ i)
  have h2 : (x.1, (0 : ℝ)) = x := Prod.ext rfl hx.symm
  have hφ : Tendsto (fun t : ℝ => (x.1, t)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have h1 : Tendsto (fun t : ℝ => (x.1, t)) (𝓝 (0 : ℝ)) (𝓝 ((x.1, (0 : ℝ)))) :=
      (Continuous.prodMk (continuous_const : Continuous fun _ : ℝ => x.1)
        continuous_id).tendsto 0
    rw [h2] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hiter : Tendsto (fun t : ℝ => iteratedFDeriv ℝ i f (x.1, t)) (𝓝[>] (0 : ℝ))
      (𝓝 (iteratedFDeriv ℝ i f x)) := hcont.tendsto.comp hφ
  have hof : Tendsto (fun t : ℝ => ENNReal.ofReal ‖iteratedFDeriv ℝ i f (x.1, t)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal ‖iteratedFDeriv ℝ i f x‖)) :=
    ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hiter
  refine le_of_tendsto hof ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact Work.NN.Final.le_gDN i ht

end Work.NN.Seeley
