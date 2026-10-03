import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic

namespace Work.Analysis.PertCrux

/-- A family of `r`-balls around the points `ζ w`, `w ∈ K`, all of which lie in the gate region
`Qp Ξ' α` with centres of «diameter + 2r» smaller than the lattice spacing `1/‖α‖`, forms an open
set contained in `Qp Ξ' α` on which the universal cover `τ_f = tauC σ α` is injective, and it
contains all the centres `ζ w`.

Proof: the union is open as a union of open balls; it is contained in `Qp Ξ' α` since each ball is
(`hdepth`); the two-centre diameter bound `hdiam` forces the whole union to have diameter `< 1/‖α‖`,
whence `tauC σ α` is injective there (`Work.Pert.tauC_inj_of_dist_lt`); and every centre lies in its
own ball because `r > 0`. -/
theorem QpPrime_props {Ξ' : ℝ} {σ α : ℂ} (hσ : σ ≠ 0) (hα : α ≠ 0) {K : Set ℂ}
    {ζ : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hdepth : ∀ w ∈ K, Metric.ball (ζ w) r ⊆ Work.Pert.Qp Ξ' α)
    (hdiam : ∀ w ∈ K, ∀ w' ∈ K, ‖ζ w - ζ w'‖ + 2 * r < 1 / ‖α‖) :
    IsOpen (⋃ w ∈ K, Metric.ball (ζ w) r) ∧
      (⋃ w ∈ K, Metric.ball (ζ w) r) ⊆ Work.Pert.Qp Ξ' α ∧
      Set.InjOn (Work.Pert.tauC σ α) (⋃ w ∈ K, Metric.ball (ζ w) r) ∧
      (∀ w ∈ K, ζ w ∈ ⋃ w ∈ K, Metric.ball (ζ w) r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun w => isOpen_iUnion fun _ => Metric.isOpen_ball
  · exact Set.iUnion₂_subset fun w hw => hdepth w hw
  · intro x hx y hy hxy
    simp only [Set.mem_iUnion, exists_prop] at hx hy
    obtain ⟨w, hwK, hxw⟩ := hx
    obtain ⟨w', hw'K, hyw'⟩ := hy
    rw [Metric.mem_ball] at hxw hyw'
    have h1 : ‖x - ζ w‖ < r := by rw [← dist_eq_norm]; exact hxw
    have h2 : ‖ζ w' - y‖ < r := by
      rw [← dist_eq_norm, dist_comm]; exact hyw'
    have h3 : ‖x - y‖ ≤ ‖x - ζ w‖ + ‖ζ w - ζ w'‖ + ‖ζ w' - y‖ := by
      have heq : x - y = (x - ζ w) + (ζ w - ζ w') + (ζ w' - y) := by ring
      rw [heq]
      calc ‖(x - ζ w) + (ζ w - ζ w') + (ζ w' - y)‖
          ≤ ‖(x - ζ w) + (ζ w - ζ w')‖ + ‖ζ w' - y‖ := norm_add_le _ _
        _ ≤ (‖x - ζ w‖ + ‖ζ w - ζ w'‖) + ‖ζ w' - y‖ := by
            linarith [norm_add_le (x - ζ w) (ζ w - ζ w')]
        _ = ‖x - ζ w‖ + ‖ζ w - ζ w'‖ + ‖ζ w' - y‖ := by ring
    have h4 := hdiam w hwK w' hw'K
    exact Work.Pert.tauC_inj_of_dist_lt σ α x y hσ hα (by linarith) hxy
  · intro w hw
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, Metric.mem_ball_self hr⟩⟩

end Work.Analysis.PertCrux
