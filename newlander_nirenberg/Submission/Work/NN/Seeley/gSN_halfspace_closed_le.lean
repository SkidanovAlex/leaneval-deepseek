import Mathlib
import Submission.Work.NN.Seeley.Glob

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedVariables false

namespace Work.NN.Seeley

/-- A `C^{i+1}` function on the closed half space `{0 ≤ p.2}` has its `gSN i α` Hölder seminorm
over the closed half space bounded by the seminorm over the open half space. -/
theorem gSN_halfspace_closed_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X × ℝ → ℂ} {i : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hf : ∀ x : X × ℝ, 0 ≤ x.2 → ContDiffAt ℝ (i + 1) f x) :
    Work.NN.Final.gSN i α f {p : X × ℝ | 0 ≤ p.2}
      ≤ Work.NN.Final.gSN i α f {p : X × ℝ | 0 < p.2} := by
  have hmem : ∀ x : X × ℝ, x ∈ {p : X × ℝ | 0 ≤ p.2} → 0 ≤ x.2 := fun x h => h
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hcx : ContinuousAt (iteratedFDeriv ℝ i f) x :=
    (hf x (hmem x hx)).continuousAt_iteratedFDeriv (k := i) (by exact_mod_cast Nat.le_succ i)
  have hcy : ContinuousAt (iteratedFDeriv ℝ i f) y :=
    (hf y (hmem y hy)).continuousAt_iteratedFDeriv (k := i) (by exact_mod_cast Nat.le_succ i)
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
  refine Work.NN.Final.le_gSN i α (by show 0 < x.2 + t; linarith [hmem x hx, ht'])
    (by show 0 < y.2 + t; linarith [hmem y hy, ht']) ?_
  intro h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  exact hxy (Prod.ext h1 (by linarith))

end Work.NN.Seeley
