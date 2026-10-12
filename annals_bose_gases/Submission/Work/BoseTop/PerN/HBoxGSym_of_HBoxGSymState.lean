import ChallengeDeps
import Submission.Work.BoseTop.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseTop.PerN

open Filter
open scoped Real

/-- **Infimum over states and particle numbers.**  The per-`N`, per-state
handoff predicate `HBoxGSymState` (every admissible `N` and every symmetric
trial state `Ψ` satisfies `gcTwoTerm·L³ + 8π a v ρ·N ≤ symQuot`) implies the
grand-canonical density form `HBoxGSym`: taking the infimum of `symQuot` over
`Ψ : SymBox N L` gives `symBoxEnergy N L v ≥ gcTwoTerm·L³ + 8π a v ρ·N`;
subtracting the chemical-potential term `8π a v ρ·N` shows that *every* element
of the value set `gcSetSym v (8π a v ρ) (2ρ) L` is at least `gcTwoTerm·L³`, and
since that set is nonempty (`N = 0` is admissible) its infimum `gcBoxSym` is at
least `gcTwoTerm·L³`; dividing by `L³ > 0` (as `L ≥ L₀ ≥ 1`) gives the density
form. -/
theorem HBoxGSym_of_HBoxGSymState {v : EuclideanSpace ℝ (Fin 3) → ℝ} {η₀ Cw : ℝ}
    (h : Work.BoseTop.HBoxGSymState v η₀ Cw) : Work.BoseTop.HBoxGSym v η₀ Cw := by
  unfold Work.BoseTop.HBoxGSym Work.BoseTop.HBoxGSymState at *
  filter_upwards [h, self_mem_nhdsWithin] with ρ hρ hρpos
  rcases hρ with ⟨L₀, hL₀1, hL₀⟩
  refine ⟨L₀, hL₀1, fun L hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) (le_trans hL₀1 hL)
  have hρ0 : 0 < ρ := hρpos
  have hρmax : 0 ≤ 2 * ρ := by linarith
  have hbound :
      Submission.BoseGases.gcTwoTerm (BoseGases.a v) Cw (1 / 2 + η₀) ρ * L ^ 3 ≤
        Work.BoseTop.gcBoxSym v (8 * Real.pi * BoseGases.a v * ρ) (2 * ρ) L := by
    unfold Work.BoseTop.gcBoxSym
    apply le_csInf (Work.BoseTop.gcSetSym_nonempty hρmax hLpos.le)
    rintro y ⟨N, hN, rfl⟩
    have hle : Submission.BoseGases.gcTwoTerm (BoseGases.a v) Cw (1 / 2 + η₀) ρ * L ^ 3
        + (8 * Real.pi * BoseGases.a v * ρ) * (N : ℝ) ≤
          Submission.BoseGases.symBoxEnergy N L v := by
      have hne : Nonempty (Submission.BoseGases.SymBox N L) :=
        Submission.BoseGases.nonempty_SymBox N hLpos
      refine le_ciInf (fun Ψ => ?_)
      exact hL₀ L hL N hN Ψ
    linarith
  unfold Work.BoseTop.gcDensitySym
  rw [le_div_iff₀ (pow_pos hLpos 3)]
  exact hbound

end Work.BoseTop.PerN
