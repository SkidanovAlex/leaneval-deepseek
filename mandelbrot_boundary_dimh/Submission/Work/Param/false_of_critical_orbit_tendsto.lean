import Mathlib
import Submission.Work.Param.Basic
import Submission.Work.Param.Setup
import Submission.Work.Param.repelling_eventual_eq
import Submission.Work.Param.baire_closed_cover
import Submission.Work.Param.no_interior_zeros_Z
import Submission.Work.Param.exists_norm_gt_one_mem_ball

namespace Work.Param

open MandelDim Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-- **A disc of parameters whose critical orbits all converge to the continued fixed point is
impossible.**  If `‖l‖ = 1`, `δ > 0`, and for every `t` in `Metric.ball l δ` the critical orbit of
`Tc (cOfLam t)` converges to `t/2`, then `False`.

Details of the intended proof.  Write `g n t = (Tc (cOfLam t))^[n] 0`; this is the value at `t` of a
polynomial in `t` of degree `2 ^ n`.  `t/2` is a fixed point of `Tc (cOfLam t)` of multiplier `t`.
Let `W = {t ∈ Metric.ball l δ | 1 < ‖t‖}`: nonempty and open since `‖l‖ = 1`, `δ > 0`.  For
`t ∈ W` the fixed point `t/2` is repelling and `‖T x - t/2‖ = ‖x - t/2‖ * ‖x + t/2‖`, so an orbit
converging to it must eventually equal it; hence `W` is covered by the closed sets
`Z n = {t ∈ Metric.ball l δ | g n t = t/2}`.  `W` is an open subset of the Baire space `ℂ`
(`IsOpen.baireSpace`), so some `Z n` has nonempty interior; then the polynomial
`t ↦ g n t - t/2` vanishes on a nonempty open set, hence identically, which is impossible because
its degree is `2 ^ n ≥ 2` (and for `n = 0` the polynomial is `-t/2`, of degree `1`). -/
theorem false_of_critical_orbit_tendsto {l : ℂ} (hl : ‖l‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (htend : ∀ t ∈ Metric.ball l δ,
      Filter.Tendsto (fun n : ℕ => (LeanEval.Dynamics.MandelbrotBoundary.Tc (cOfLam t))^[n] 0)
        Filter.atTop (nhds (t / 2))) :
    False := by
  -- `t / 2` is a fixed point of `Tc (cOfLam t)`
  have hfix : ∀ t : ℂ, (t / 2) ^ 2 + cOfLam t = t / 2 := by
    intro t; simp only [cOfLam]; ring
  -- the repelling side is covered by the closed sets `Z n`
  have hcover : {t : ℂ | t ∈ Metric.ball l δ ∧ 1 < ‖t‖} ⊆ ⋃ n, Z n := by
    intro t ht
    obtain ⟨htb, htn⟩ := ht
    have hf : Tc (cOfLam t) = fun z : ℂ => z ^ 2 + cOfLam t := by
      funext z; simp only [Tc]
    have hlim : Filter.Tendsto (fun n : ℕ => (fun z : ℂ => z ^ 2 + cOfLam t)^[n] 0)
        Filter.atTop (nhds (t / 2)) := by
      rw [← hf]; exact htend t htb
    obtain ⟨N, hN⟩ := repelling_eventual_eq (p := t / 2) (c := cOfLam t) (hfix t)
      (by
        have h2 : 2 * (t / 2) = t := by ring
        rw [h2]
        exact htn) hlim
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    rw [Z_iff, hf]
    exact hN
  -- `W` is a nonempty open subset of the Baire space `ℂ`
  have hWopen : IsOpen {t : ℂ | t ∈ Metric.ball l δ ∧ 1 < ‖t‖} :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_norm)
  have hWne : {t : ℂ | t ∈ Metric.ball l δ ∧ 1 < ‖t‖}.Nonempty := by
    obtain ⟨t, ht1, ht2⟩ := exists_norm_gt_one_mem_ball hl hδ
    exact ⟨t, ht2, ht1⟩
  -- Baire: some `Z n` has nonempty interior; but the polynomial `P n` has no interior zeros
  obtain ⟨n, hn⟩ := baire_closed_cover hWopen hWne (fun n => isClosed_Z n) hcover
  exact no_interior_zeros_Z n hn

end

end Work.Param
