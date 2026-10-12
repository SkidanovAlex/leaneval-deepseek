import ChallengeDeps
import Submission.Work.BoseBoxFock.PotGroupDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.q0word_wLoc_eq` — the all-condensate word at the localised kernels

The Q0 (all-condensate) word of FS `eq:DefQ0`, evaluated at the *localised* kernels
`wLoc ℓ (g₀) 0` / `wLoc ℓ (g₂) 0` (the cell-`u = 0` translates of the χ-renormalised kernels),
equals the explicit value

    `½·ℓ⁻³·(∫g₂)·S₂ − 8πa v·μ·S₁`

with `S₁ = cS1 ℓ Φ`, `S₂ = cS2 ℓ Φ`.

The point is that at `u = 0` the localisation kernel `wLoc ℓ h 0` *is* the χ-renormalised pair
kernel `wPair ℓ h` (`chiU ℓ 0 = chiScale ℓ`), so the corpus's
`Submission.BoseGases.q0_chosen_expect` (`Submission/Q0Ren.lean`), which is stated at the
uncurried kernels `wPairU ℓ (g₀)`, `wPairU ℓ (g₂)` and whose proof uses the two box identities
`w1c_acube_integral` / `w2c_acube_integral` (`∬_{acube²} wPair(g) = ℓ³∫g`, FS `eq:DefU` /
`eq:w2int`), applies verbatim.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- At the translation parameter `u = 0` the localisation kernel `wLoc` is the χ-renormalised
pair kernel `wPair`: `chiU ℓ 0 = chiScale ℓ`. -/
lemma wLoc_zero_eq_wPair (ℓ : ℝ) (h : E3 → ℝ) (x y : E3) :
    Submission.BoseGases.wLoc ℓ h 0 x y = Submission.BoseGases.wPair ℓ h x y := by
  simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wPair, Submission.BoseGases.chiU,
    Submission.BoseGases.chiScale, sub_zero]

theorem q0word_wLoc_eq {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (μ : ℝ) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Submission.BoseGases.q0word (N := N) ℓ μ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) Φ
      = (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g2 v h z)
          * Submission.BoseGases.cS2 ℓ Φ
        - (8 * Real.pi * BoseGases.a v) * μ * Submission.BoseGases.cS1 ℓ Φ := by
  -- the `wLoc 0 = wPairU` dictionary, curried and uncurried
  have hker : ∀ (g : E3 → ℝ) (x y : E3),
      Submission.BoseGases.wLoc ℓ g 0 x y = Submission.BoseGases.wPair ℓ g x y :=
    fun g x y => wLoc_zero_eq_wPair ℓ g x y
  have hpair : ∀ (g : E3 → ℝ) (a b : E3),
      Submission.BoseGases.wLoc ℓ g 0 a b = Submission.BoseGases.wPairU ℓ g (a, b) :=
    fun g a b => hker g a b
  have hfib : ∀ (g : E3 → ℝ) (a : E3),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) a
        = ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wPairU ℓ g (a, y) := by
    intro g a
    unfold Submission.BoseGases.w1Fibre
    apply integral_congr_ae
    filter_upwards with y
    exact hpair g a y
  -- unfold the word and rewrite the kernels
  rw [show Submission.BoseGases.q0word (N := N) ℓ μ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) Φ
      = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2 *
                Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0 (x p.1) (x p.2))
          - μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aP ℓ i Φ x) ^ 2 *
                Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (x i))
      from rfl]
  have hA : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2 *
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0 (x p.1) (x p.2))
      = (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2 *
            Submission.BoseGases.wPairU ℓ (Submission.BoseGases.g2 v h) (x p.1, x p.2)) := by
    apply Finset.sum_congr rfl
    intro p _
    apply integral_congr_ae
    filter_upwards with x
    rw [hpair (Submission.BoseGases.g2 v h) (x p.1) (x p.2)]
  have hB : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i Φ x) ^ 2 *
          Submission.BoseGases.w1Fibre ℓ
            (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (x i))
      = (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i Φ x) ^ 2 *
          (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wPairU ℓ (Submission.BoseGases.g0 v h) (x i, y))) := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards with x
    rw [hfib (Submission.BoseGases.g0 v h) (x i)]
  rw [hA, hB]
  exact Submission.BoseGases.q0_chosen_expect hR hv_nonneg hvrad hv_supp h hℓ hRℓ μ hΦc

end Work.BoseBoxFock
