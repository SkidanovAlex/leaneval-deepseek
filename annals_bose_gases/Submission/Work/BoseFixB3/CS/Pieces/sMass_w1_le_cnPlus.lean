import ChallengeDeps
import Submission.Work.BoseFixB3.CS.Ledger
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.sMass_w1_le_cnPlus` — the `(P Q + Q P)`-pair mass is `n₊`-linear

The `CS`-ledger quantity

  `sMass ℓ w₁ Φ = Σ_{p∈pairSet N} ∫_{Λ}(P_{p.2}Q_{p.1}Φ + Q_{p.2}P_{p.1}Φ)²·|w₁(x_{p.1},x_{p.2})|`

(with `w₁ = wLoc ℓ (g₀ v h) 0` the *chosen-branch* weight, i.e. `wPair ℓ (g₀ v h)`) is bounded by
`C·(ℓ³)⁻¹·N̂·n₊`.  This is FS `eq:BQwQleq` for the three-operator family: each of the two terms of
the square is *constant in one of the two slots* (an `aP`-family), which is exactly the peel that
produces the `(ℓ³)⁻¹` factor; the two terms are combined by the pointwise `(a+b)² ≤ 3(a²+b²+0²)`.

The proof is accounting only: it rewrites `wLoc ℓ h 0 = wPair ℓ h`, splits the square per pair
(`Submission.BoseGases.sq3_mass_pair_le` with third slot `0`), sums, and invokes the corpus mass
bounds `Submission.BoseGases.pq_w1_mass_swap_le_cnPlus` and
`Submission.BoseGases.q_p_w1_mass_le_cnPlus`.

The explicit constant produced is `C = 6·fsqC1 (a v) = 6·chiSup²·2·(8πa)`, i.e. twice the corpus
constant `fsqC1 (a v)` (the factor `2` comes from the two terms of the square).  This matches the
`4C₁(ℓ³)⁻¹N̂·n₊` stated for `sMass` in `CS/SESSION4_HANDOFF.md` §1.5.
-/

noncomputable section

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory Metric
open scoped Topology Real BigOperators

open Submission.BoseGases

theorem sMass_w1_le_cnPlus {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ)
      (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {Φ : Submission.BoseGases.X N → ℝ}
      (hΦc : Continuous Φ),
      Work.BoseFixB3.CS.sMass ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ
        ≤ C * (ℓ ^ 3)⁻¹ * (N : ℝ) * Submission.BoseGases.cnPlus ℓ Φ := by
  classical
  refine ⟨6 * fsqC1 (BoseGases.a v), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ BoseGases.a v := le_of_lt hav
    have h4 : (0 : ℝ) ≤ fsqC1 (BoseGases.a v) := by
      unfold fsqC1
      positivity
    linarith
  · intro N ℓ hℓ hRℓ Φ hΦc
    have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
    have hg0s : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → g0 v h z = 0 :=
      fun z hz => g0_zero_of_norm_ge hv_supp hz h
    -- the weight `wLoc ℓ h 0` *is* `wPair ℓ h`
    have hwloc : ∀ x y : EuclideanSpace ℝ (Fin 3),
        wLoc ℓ (g0 v h) 0 x y = wPair ℓ (g0 v h) x y := by
      intro x y
      simp only [wLoc, wPair, chiU, chiScale, sub_zero]
    -- rewrite `sMass` onto the `wPair` weight
    have hsM : Work.BoseFixB3.CS.sMass ℓ (wLoc ℓ (g0 v h) 0) Φ
        = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
            * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
      change (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
            * |wLoc ℓ (g0 v h) 0 (x p.1) (x p.2)|) = _
      simp only [hwloc]
    -- per pair: `(a+b)² ≤ 3(a²+b²+0²)`
    have hpair : ∀ p ∈ pairSet N,
        (∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
            * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ 3 * ((∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2
                * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
                * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)) := by
      intro p hp
      have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      have hb := sq3_mass_pair_le (N := N) (ℓ := ℓ) (R := R) hℓ (h := g0 v h) hg0i hg0s hRℓ
        (a := fun x => aP ℓ p.2 (aQ ℓ p.1 Φ) x)
        (hac := aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc))
        (b := fun x => aQ ℓ p.2 (aP ℓ p.1 Φ) x)
        (hbc := aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc))
        (c := fun _ => (0 : ℝ)) (hcc := continuous_const) (i := p.1) (j := p.2) hpne
      simpa using hb
    -- sum the per-pair bound
    have hsum : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
            * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ 3 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2
                * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
          + 3 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
                * |wPair ℓ (g0 v h) (x p.1) (x p.2)|) := by
      calc
        (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
              * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
            ≤ ∑ p ∈ pairSet N, 3 * ((∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2
                    * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
                  + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
                    * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)) := Finset.sum_le_sum hpair
        _ = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2
                    * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
                  + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
                    * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)) := by
              rw [← Finset.mul_sum, Finset.sum_add_distrib]
        _ = 3 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2
                    * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
              + 3 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
                    * |wPair ℓ (g0 v h) (x p.1) (x p.2)|) := by ring
    -- the two `(ℓ³)⁻¹`-peeled mass bounds of the corpus
    have hA : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2
            * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ fsqC1 (BoseGases.a v) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
      simpa only [wPairC] using
        pq_w1_mass_swap_le_cnPlus (N := N) (ℓ := ℓ) (v := v) (R := R) hℓ hv hvrad hR hv_supp h hRℓ
          (Φ := Φ) hΦc
    have hB : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2
            * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ fsqC1 (BoseGases.a v) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
      simpa only [wPairC] using
        q_p_w1_mass_le_cnPlus (N := N) (ℓ := ℓ) (v := v) (R := R) hℓ hv hvrad hR hv_supp h hRℓ
          (Φ := Φ) hΦc
    rw [hsM]
    exact le_trans hsum (by nlinarith [hA, hB])

end Work.BoseFixB3.CS.Pieces
