import ChallengeDeps
import Submission.Work.BoseFixB1.RegimeAux
import Submission.Work.BoseFixB1.WB.banddecay_alg
import Submission.Work.BoseFixB1.WB.rpow_window
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.banddecay_window` — the bad-band decay loss is negligible

The discarded-mass term of the sliding localisation carries the constant

  `12 * (1 + d)² * chiSmallBandDecay M d * (μa³)^{M/3}`

(FS `eq:badset`; see `Work.SmallBoxSliding.bandSet_mass_integral_le_law` at
`M = mValue = 48`).  Here `d = (μa³)^{6/323}` and
`chiSmallBandDecay 48 d = chiSupAbs² · (chiSmallDecay 48)² · d^{-96}`, so the
whole factor is a *decaying* power of the diluteness:

  12·(1+d)² · chiSmallBandDecay 48 d · 2^96 · (μa³)^16
    ≤ C · (μa³)^{4592/323}   (0 < μa³ ≤ 1),   C = 48·chiSupAbs²·(chiSmallDecay 48)²·2^96,

since `16 - 96·(6/323) = 4592/323 > 0`.  The `2^96` and the exponent `16 = 48/3`
are the two numerical inputs of the request, so the statement is the *window* on
`μa³` below which the band-decay loss drops under any prescribed bound `2π/C₁`:

  `μa³ ≤ ε₀  ⟹  12(1+d)²·chiSmallBandDecay 48 d·2^96·(μa³)^16 ≤ 2π/C₁`.

The proof is the two deferred pieces (`rpow_window`, the generic
`t^p → 0` window, and `banddecay_alg`, the exponent arithmetic) glued to the
unfolding `paramsAt μ (a v) = fsParams (μ·(a v)³)` of the parameter block.
-/

namespace Work.BoseFixB1.WB

theorem banddecay_window {v : EuclideanSpace ℝ (Fin 3) → ℝ} {C₁ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC₁ : 0 < C₁) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      12 * (1 + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          * Submission.BoseGases.chiSmallBandDecay (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * 2 ^ 96 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (16 : ℝ)
        ≤ 2 * Real.pi / C₁ := by
  have hK : 0 ≤ 48 * Submission.BoseGases.chiSupAbs ^ 2
      * (Submission.BoseGases.chiSmallDecay 48) ^ 2 * 2 ^ 96 := by positivity
  have hR : 0 < 2 * Real.pi / C₁ := by positivity
  have hp : (0 : ℝ) < 4592 / 323 := by norm_num
  obtain ⟨ε₀, hε₀pos, hε₀le1, hε₀⟩ := rpow_window hK hR hp
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro μ hμ hμle
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hμle hε₀le1
  have hkey := hε₀ (μ * (_root_.BoseGases.a v) ^ 3) ht0 hμle
  have hparM : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = 48 := by
    rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hparD : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6 := by
    rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  rw [hparM, hparD]
  exact le_trans (banddecay_alg ht0 ht1) hkey

end Work.BoseFixB1.WB
