import ChallengeDeps
import Submission.Work.BoseFixB3.CS.Ledger
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `qcross_bar_om_pair_sum_weighted` — the summed (pair-indexed) two-parameter budget

The **sum level** form of `CS/Pieces/qcross_bar_om_pair_weighted`: the per-pair AM–GM bound

  `|∫_Λ F'_p·(q4B_p − ω_p·S_p)·w₁| ≤ (t + 1/(4ε))·∫(F'_p)²|w₁| + (1/(4t))·∫(q4B_p)²w + ε·∫(S_p)²|w₁|`

is summed over the pair set `pairSet N` (`Finset.sum_le_sum` on the `p.1 ≠ p.2` members), and the
two sides are flipped (using `−|x| ≤ x`) so that the resulting bound has the sign and the shape used
by the `CS` ledger, with the three sums recognised as `fMass`, `q4Mass`, `sMass`:

  `2·Σ_p∫_Λ F'_p·(q4B_p − ω_p·S_p)·w₁
     ≥ −2(t + 1/(4ε))·fMass − (1/(2t))·q4Mass − 2ε·sMass`.

Nothing analytic is used beyond the per-pair lemma: this file is the accounting step.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseFixB3.CS.Pieces

open _root_.BoseGases Submission.BoseGases

theorem qcross_bar_om_pair_sum_weighted {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {fc : Work.BoseBoxFix.LowCut} {κ : ℝ} (hκ : 0 < κ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
          * (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
             - Classical.choose h (x p.1 - x p.2)
               * (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
                  + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x))
          * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2))
      ≥ - (2 * (t + 1 / (4 * ε))) *
          (Work.BoseFixB3.CS.fMass fc κ ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ)
        - (1 / (2 * t)) *
          (Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
            (Submission.BoseGases.wLoc ℓ v 0) Φ)
        - (2 * ε) *
          (Work.BoseFixB3.CS.sMass ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ) := by
  classical
  -- `hκ` is part of the requested signature; the per-pair lemma is stated for all `κ`
  have _hκ : 0 < κ := hκ
  let Ip : Fin N × Fin N → ℝ := fun p => ∫ x in Submission.BoseGases.abox N ℓ,
      Work.BoseFixB3.highSlot fc κ ℓ p.2
          (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
        * (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
           - Classical.choose h (x p.1 - x p.2)
             * (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
                + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x))
        * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2)
  let Ap : Fin N × Fin N → ℝ := fun p => ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.BoseFixB3.highSlot fc κ ℓ p.2
          (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x) ^ 2
        * |Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2)|
  let Bp : Fin N × Fin N → ℝ := fun p => ∫ x in Submission.BoseGases.abox N ℓ,
      (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2
        * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2)
  let Cp : Fin N × Fin N → ℝ := fun p => ∫ x in Submission.BoseGases.abox N ℓ,
      (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
          + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
        * |Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2)|
  have eA : (∑ p ∈ Submission.BoseGases.pairSet N, Ap p)
      = Work.BoseFixB3.CS.fMass fc κ ℓ
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ := rfl
  have eB : (∑ p ∈ Submission.BoseGases.pairSet N, Bp p)
      = Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
          (Submission.BoseGases.wLoc ℓ v 0) Φ := rfl
  have eC : (∑ p ∈ Submission.BoseGases.pairSet N, Cp p)
      = Work.BoseFixB3.CS.sMass ℓ
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ := rfl
  -- the per-pair bound, flipped and multiplied by `2`
  have key : ∀ p ∈ Submission.BoseGases.pairSet N,
      -((2 * (t + 1 / (4 * ε))) * Ap p + (1 / (2 * t)) * Bp p + (2 * ε) * Cp p)
        ≤ 2 * Ip p := by
    intro p hp
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hb := qcross_bar_om_pair_weighted (N := N) (ℓ := ℓ) (v := v) (R := R)
      (fc := fc) (κ := κ) (i := p.1) (j := p.2) (Φ := Φ)
      hℓ hv_nonneg hvrad hv1 hR hv_supp h hRℓ hpne hΦc ht hε
    rw [Prod.mk.eta] at hb
    have h1 : -(((t + 1 / (4 * ε)) * Ap p + (1 / (4 * t)) * Bp p) + ε * Cp p) ≤ Ip p :=
      le_trans (neg_le_neg hb) (neg_abs_le (Ip p))
    have h2 : 2 * (-(((t + 1 / (4 * ε)) * Ap p + (1 / (4 * t)) * Bp p) + ε * Cp p))
        ≤ 2 * Ip p := by linarith
    have hid : 2 * (-(((t + 1 / (4 * ε)) * Ap p + (1 / (4 * t)) * Bp p) + ε * Cp p))
        = -((2 * (t + 1 / (4 * ε))) * Ap p + (1 / (2 * t)) * Bp p + (2 * ε) * Cp p) := by
      field_simp
      ring
    rwa [hid] at h2
  have hsum : (∑ p ∈ Submission.BoseGases.pairSet N,
        -((2 * (t + 1 / (4 * ε))) * Ap p + (1 / (2 * t)) * Bp p + (2 * ε) * Cp p))
      ≤ ∑ p ∈ Submission.BoseGases.pairSet N, 2 * Ip p :=
    Finset.sum_le_sum key
  -- recognise the three summed majorants as `fMass`, `q4Mass`, `sMass`
  have hL : (∑ p ∈ Submission.BoseGases.pairSet N,
        -((2 * (t + 1 / (4 * ε))) * Ap p + (1 / (2 * t)) * Bp p + (2 * ε) * Cp p))
      = -((2 * (t + 1 / (4 * ε))) *
            (Work.BoseFixB3.CS.fMass fc κ ℓ
              (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ)
          + (1 / (2 * t)) *
            (Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
              (Submission.BoseGases.wLoc ℓ v 0) Φ)
          + (2 * ε) *
            (Work.BoseFixB3.CS.sMass ℓ
              (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ)) := by
    rw [← eA, ← eB, ← eC, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hR : (∑ p ∈ Submission.BoseGases.pairSet N, 2 * Ip p)
      = 2 * ∑ p ∈ Submission.BoseGases.pairSet N, Ip p := by
    rw [Finset.mul_sum]
  have h' : -((2 * (t + 1 / (4 * ε))) *
            (Work.BoseFixB3.CS.fMass fc κ ℓ
              (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ)
          + (1 / (2 * t)) *
            (Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
              (Submission.BoseGases.wLoc ℓ v 0) Φ)
          + (2 * ε) *
            (Work.BoseFixB3.CS.sMass ℓ
              (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ))
      ≤ 2 * ∑ p ∈ Submission.BoseGases.pairSet N, Ip p := by
    rw [← hL, ← hR]
    exact hsum
  have hfin : -((2 * (t + 1 / (4 * ε))) *
            (Work.BoseFixB3.CS.fMass fc κ ℓ
              (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ)
          + (1 / (2 * t)) *
            (Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
              (Submission.BoseGases.wLoc ℓ v 0) Φ)
          + (2 * ε) *
            (Work.BoseFixB3.CS.sMass ℓ
              (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ))
      = - (2 * (t + 1 / (4 * ε))) *
          (Work.BoseFixB3.CS.fMass fc κ ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ)
        - (1 / (2 * t)) *
          (Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
            (Submission.BoseGases.wLoc ℓ v 0) Φ)
        - (2 * ε) *
          (Work.BoseFixB3.CS.sMass ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ) := by
    ring
  rw [ge_iff_le, ← hfin]
  exact h'

end Work.BoseFixB3.CS.Pieces
