import ChallengeDeps
import Submission.Work.BoseFixB1.fsRegimeAt
import Submission.Work.BoseFixB1B.PerBoxSectorResidual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.BddSector

/-- **The FS parameter regime, in the `PB`-vocabulary of the bounded sector.**

There is a diluteness threshold `ε₀ > 0` such that at every `μ > 0` with
`μ (a v)³ ≤ ε₀` the frozen parameters of `Work.BoseFixB1B` satisfy

* `PBℓ = sideAt μ (a v) > 0` and `PBd > 0` (the box side and the small-box side),
* `PBM = M = 48 ≥ 1`,
* `R ≤ PBℓ·PBd/16` (the small boxes of side `PBd·PBℓ/16` cover the potential support),
* `R ≤ PBℓ·chiR0` (the support-radius condition of the witness ball).

The two radius conditions are `Work.BoseFixB1.regime_sideAt_ge` verbatim; the
three positivity/concreteness conjuncts are unconditional: `PBℓ = K_ℓ (μ a)^{-1/2}`
with `K_ℓ = (μa³)^{-3/646} > 0`, `PBd = (μa³)^{6/323} > 0`, and `PBM = mValue = 48`. -/
theorem regimeBdd {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hav : 0 < _root_.BoseGases.a v) (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      0 < Work.BoseFixB1B.PBℓ v μ ∧ 0 < Work.BoseFixB1B.PBd v μ ∧ 1 ≤ Work.BoseFixB1B.PBM v μ ∧
      R ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ / 16 ∧
      R ≤ Work.BoseFixB1B.PBℓ v μ * Submission.BoseGases.chiR0 := by
  obtain ⟨ε₀, hε₀pos, hε⟩ := Work.BoseFixB1.regime_sideAt_ge (R := R) hav hR
  refine ⟨ε₀, hε₀pos, fun μ hμ hle => ?_⟩
  obtain ⟨h16, hχ⟩ := hε μ hμ hle
  have ha3 : 0 < (_root_.BoseGases.a v) ^ 3 := by positivity
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ ha3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `PBℓ = sideAt μ (a v) = K_ℓ (μ a v)^{-1/2} > 0`
    show 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
    exact Work.BoseBox.boxSide_pos hμ hav (by
      rw [Work.BoseFixB1.Kl_eq_fsXp]
      exact Work.BoseBox.fsXp_pos ht)
  · -- `PBd = (μ a³)^{6/323} > 0`
    show 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_pos ht
  · -- `PBM = mValue = 48 ≥ 1`
    show 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    exact Work.BoseFixB1.M_ge_one μ (_root_.BoseGases.a v)
  · exact h16
  · exact hχ

end Work.BoseFixB1.BddSector
