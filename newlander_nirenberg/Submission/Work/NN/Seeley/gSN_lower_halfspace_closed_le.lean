import Mathlib
import Submission.Work.NN.Seeley.Glob
import Submission.Work.NN.Seeley.gSN_halfspace_closed_le

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedVariables false

namespace Work.NN.Seeley

/-- The analogue of `Work.NN.Seeley.gSN_halfspace_closed_le` for the lower half space. -/
theorem gSN_lower_halfspace_closed_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X × ℝ → ℂ} {i : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hf : ∀ x : X × ℝ, x.2 ≤ 0 → ContDiffAt ℝ (i + 1) f x) :
    Work.NN.Final.gSN i α f {p : X × ℝ | p.2 ≤ 0}
      ≤ Work.NN.Final.gSN i α f {p : X × ℝ | p.2 < 0} := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hx' : x.2 ≤ 0 := hx
  have hy' : y.2 ≤ 0 := hy
  have hcx : ContinuousAt (iteratedFDeriv ℝ i f) x :=
    (hf x hx').continuousAt_iteratedFDeriv (k := i) (by exact_mod_cast Nat.le_succ i)
  have hcy : ContinuousAt (iteratedFDeriv ℝ i f) y :=
    (hf y hy').continuousAt_iteratedFDeriv (k := i) (by exact_mod_cast Nat.le_succ i)
  have hφ : Tendsto (fun t : ℝ => (x.1, x.2 + t)) (𝓝[<] (0 : ℝ)) (𝓝 x) := by
    have h1 : Tendsto (fun t : ℝ => (x.1, x.2 + t)) (𝓝 (0 : ℝ)) (𝓝 ((x.1, x.2 + 0))) :=
      (continuous_const.prodMk (continuous_const.add continuous_id)).tendsto 0
    simp only [add_zero] at h1
    rw [show ((x.1, x.2) : X × ℝ) = x from Prod.ext rfl rfl] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hψ : Tendsto (fun t : ℝ => (y.1, y.2 + t)) (𝓝[<] (0 : ℝ)) (𝓝 y) := by
    have h1 : Tendsto (fun t : ℝ => (y.1, y.2 + t)) (𝓝 (0 : ℝ)) (𝓝 ((y.1, y.2 + 0))) :=
      (continuous_const.prodMk (continuous_const.add continuous_id)).tendsto 0
    simp only [add_zero] at h1
    rw [show ((y.1, y.2) : X × ℝ) = y from Prod.ext rfl rfl] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have htx : Tendsto (fun t : ℝ => iteratedFDeriv ℝ i f (x.1, x.2 + t)) (𝓝[<] (0 : ℝ))
      (𝓝 (iteratedFDeriv ℝ i f x)) := hcx.tendsto.comp hφ
  have hty : Tendsto (fun t : ℝ => iteratedFDeriv ℝ i f (y.1, y.2 + t)) (𝓝[<] (0 : ℝ))
      (𝓝 (iteratedFDeriv ℝ i f y)) := hcy.tendsto.comp hψ
  have hlim : Tendsto
      (fun t : ℝ => ‖iteratedFDeriv ℝ i f (x.1, x.2 + t)
        - iteratedFDeriv ℝ i f (y.1, y.2 + t)‖ / ‖x - y‖ ^ α)
      (𝓝[<] (0 : ℝ))
      (𝓝 (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α)) :=
    (htx.sub hty).norm.div_const _
  have hof : Tendsto
      (fun t : ℝ => ENNReal.ofReal (‖iteratedFDeriv ℝ i f (x.1, x.2 + t)
        - iteratedFDeriv ℝ i f (y.1, y.2 + t)‖ / ‖x - y‖ ^ α))
      (𝓝[<] (0 : ℝ))
      (𝓝 (ENNReal.ofReal
        (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α))) :=
    ENNReal.continuous_ofReal.tendsto _ |>.comp hlim
  refine le_of_tendsto hof ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t < (0 : ℝ) := ht
  have hd : ((x.1, x.2 + t) : X × ℝ) - (y.1, y.2 + t) = x - y := by ext <;> simp
  rw [← hd]
  refine Work.NN.Final.le_gSN i α (by show x.2 + t < 0; linarith)
    (by show y.2 + t < 0; linarith) ?_
  intro h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  exact hxy (Prod.ext h1 (by linarith))

end Work.NN.Seeley
