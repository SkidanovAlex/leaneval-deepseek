import Mathlib
import Submission.Work.NN.Seeley.gSN_halfspace_closed_le

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

namespace Work.NN.Seeley

/-- An individual Hölder difference quotient of the global `i`-th iterated derivative of a
function on the closed half space `{0 ≤ p.2}`, evaluated at two points of that closed half space,
is bounded by the `gSN i α` seminorm of the function over the *open* half space `{0 < p.2}`.

The point is that `ContDiffAt ℝ (i+1) f` at `x` and at `y` makes `iteratedFDeriv ℝ i f`
continuous there, so the quotient can be approximated by pushing both points strictly into the
open half space; shifting both by the same positive amount `t` in the second coordinate leaves the
difference `x - y` unchanged, hence leaves the quotient's denominator `‖x - y‖ ^ α` unchanged. -/
theorem ofReal_ratio_le_gSN_halfspace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X × ℝ → ℂ} {i : ℕ} {α : ℝ} {x y : X × ℝ}
    (hx : 0 ≤ x.2) (hy : 0 ≤ y.2) (hxy : x ≠ y)
    (hfx : ContDiffAt ℝ (i + 1) f x) (hfy : ContDiffAt ℝ (i + 1) f y) :
    ENNReal.ofReal (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α)
      ≤ Work.NN.Final.gSN i α f {p : X × ℝ | 0 < p.2} := by
  have hcx : ContinuousAt (iteratedFDeriv ℝ i f) x :=
    hfx.continuousAt_iteratedFDeriv (k := i) (by exact_mod_cast Nat.le_succ i)
  have hcy : ContinuousAt (iteratedFDeriv ℝ i f) y :=
    hfy.continuousAt_iteratedFDeriv (k := i) (by exact_mod_cast Nat.le_succ i)
  have hφ : Tendsto (fun t : ℝ => (x.1, x.2 + t)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have h1 : Tendsto (fun t : ℝ => (x.1, x.2 + t)) (𝓝 (0 : ℝ)) (𝓝 ((x.1, x.2 + 0))) :=
      (continuous_const.prodMk (continuous_const.add continuous_id)).tendsto 0
    simp only [add_zero] at h1
    rw [show ((x.1, x.2) : X × ℝ) = x from Prod.ext rfl rfl] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hψ : Tendsto (fun t : ℝ => (y.1, y.2 + t)) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have h1 : Tendsto (fun t : ℝ => (y.1, y.2 + t)) (𝓝 (0 : ℝ)) (𝓝 ((y.1, y.2 + 0))) :=
      (continuous_const.prodMk (continuous_const.add continuous_id)).tendsto 0
    simp only [add_zero] at h1
    rw [show ((y.1, y.2) : X × ℝ) = y from Prod.ext rfl rfl] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have htx : Tendsto (fun t : ℝ => iteratedFDeriv ℝ i f (x.1, x.2 + t)) (𝓝[>] (0 : ℝ))
      (𝓝 (iteratedFDeriv ℝ i f x)) := hcx.tendsto.comp hφ
  have hty : Tendsto (fun t : ℝ => iteratedFDeriv ℝ i f (y.1, y.2 + t)) (𝓝[>] (0 : ℝ))
      (𝓝 (iteratedFDeriv ℝ i f y)) := hcy.tendsto.comp hψ
  have hlim : Tendsto
      (fun t : ℝ => ‖iteratedFDeriv ℝ i f (x.1, x.2 + t)
        - iteratedFDeriv ℝ i f (y.1, y.2 + t)‖ / ‖x - y‖ ^ α)
      (𝓝[>] (0 : ℝ))
      (𝓝 (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α)) :=
    (htx.sub hty).norm.div_const _
  have hof : Tendsto
      (fun t : ℝ => ENNReal.ofReal (‖iteratedFDeriv ℝ i f (x.1, x.2 + t)
        - iteratedFDeriv ℝ i f (y.1, y.2 + t)‖ / ‖x - y‖ ^ α))
      (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal
        (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α))) :=
    ENNReal.continuous_ofReal.tendsto _ |>.comp hlim
  refine le_of_tendsto hof ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  have hd : ((x.1, x.2 + t) : X × ℝ) - (y.1, y.2 + t) = x - y := by
    ext <;> simp
  rw [← hd]
  refine Work.NN.Final.le_gSN i α (by show 0 < x.2 + t; linarith)
    (by show 0 < y.2 + t; linarith) ?_
  intro h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  exact hxy (Prod.ext h1 (by linarith))

end Work.NN.Seeley
