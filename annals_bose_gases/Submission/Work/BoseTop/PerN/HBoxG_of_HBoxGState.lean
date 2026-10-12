import ChallengeDeps
import Submission.Work.BoseTop.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `HBoxGState ⟹ HBoxG`: the per-state handoff for the finite-volume LHY target

`Work.BoseTop.HBoxGState v η₀ Cw` is the *per-state, canonical* shape of the
finite-volume LHY-Background bound: for every small density `ρ`, every large box
side `L` and every admissible particle number `N` (`N ≤ 2ρL³`) the corpus box
energy satisfies

`gcTwoTerm (a v) Cw (1/2 + η₀) ρ · L³ ≤ boxEnergy N L v − 8π (a v) ρ · N`.

`Work.BoseTop.HBoxG v η₀ Cw` is the *grand-canonical, density* shape: eventually
in `ρ → 0⁺`, for all large `L`,

`gcTwoTerm (a v) Cw (1/2 + η₀) ρ ≤ gcDensity v (8π (a v) ρ) (2ρ) L`.

This file proves that the per-state form implies the density form, by taking the
infimum over the admissible particle numbers.  The only ingredients are the
definitions `gcDensity = gcBox / L³`, `gcBox = sInf (gcSet ·)` and the fact that
every element of `gcSet` is `≥ gcTwoTerm · L³` (which is exactly the per-state
hypothesis), together with nonemptiness of `gcSet` (`N = 0` is admissible).
-/

namespace Work.BoseTop.PerN

open Filter
open scoped Topology

theorem HBoxG_of_HBoxGState {v : EuclideanSpace ℝ (Fin 3) → ℝ} {η₀ Cw : ℝ}
    (h : Work.BoseTop.HBoxGState v η₀ Cw) : Work.BoseTop.HBoxG v η₀ Cw := by
  filter_upwards [h, self_mem_nhdsWithin] with ρ hρ hρpos
  rcases hρ with ⟨L₀, hL₀1, hL₀⟩
  refine ⟨L₀, hL₀1, fun L hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hL₀1 hL)
  have hρ0 : 0 < ρ := hρpos
  have hρmax : 0 ≤ 2 * ρ := by linarith
  -- `gcSet` is nonempty (`N = 0` is admissible)
  have hne :
      (Submission.BoseGases.gcSet v (8 * Real.pi * _root_.BoseGases.a v * ρ) (2 * ρ) L).Nonempty :=
    Submission.BoseGases.gcSet_nonempty (v := v)
      (μ := 8 * Real.pi * _root_.BoseGases.a v * ρ) (L := L) hρmax hLpos.le
  -- unfold the density and the infimum, and clear the positive denominator
  rw [show Submission.BoseGases.gcDensity v (8 * Real.pi * _root_.BoseGases.a v * ρ) (2 * ρ) L
        = Submission.BoseGases.gcBox v (8 * Real.pi * _root_.BoseGases.a v * ρ) (2 * ρ) L / L ^ 3
        from rfl,
      show Submission.BoseGases.gcBox v (8 * Real.pi * _root_.BoseGases.a v * ρ) (2 * ρ) L
        = sInf (Submission.BoseGases.gcSet v (8 * Real.pi * _root_.BoseGases.a v * ρ) (2 * ρ) L)
        from rfl]
  rw [le_div_iff₀ (pow_pos hLpos 3)]
  -- every admissible `N` gives `gcTwoTerm · L³ ≤ boxEnergy N L v − μ N`
  refine le_csInf hne ?_
  rintro y ⟨N, hN, rfl⟩
  exact hL₀ L hL N hN

end Work.BoseTop.PerN
