import ChallengeDeps
import Submission.Work.BoseFixB1.Up.Core
import Submission.Work.BoseFixB1S.flatLedgerSharpB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.LedgerKin` — the ledger of `PerBoxF` **with the kinetic supply**

`Work.BoseFixB1S.perBoxF_of_ledger_sharp` reduces `PerBoxF` to four rows (the sharp `F`-row, the
fibre row, the quadratic mean-field pair row and the budget) but it takes

    `hkin : 0 ≤ sbKin` ,

i.e. it throws away the `ε_T`-gap payment that the kinetic word already carries.  By
`Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus` the corpus knows the strictly stronger

    `K₂ · μ · (a v) · n₊(B) ≤ sbKin`      (`K₂ = c'²` **arbitrary**, at the cost of a smaller
                                            `ε₀`, see `Up.gapRegime_of_adm`),

where `n₊(B) = cnPlusBoxInd` is the box excited count.  Feeding that into the *budget* — the row
`Efib + Epair ≤ C·(error bracket) + W₁·(slack)` — gives the budget

    `Efib + Epair ≤ C·(error bracket) + W₁·(slack) + K₂·μ·(a v)·n₊(B)` ,

which is the row this module proves `PerBoxF` from.  The gain is strictly one-sided: every
deviation term of the flat (condensed) branch that is *bounded by the excited count* can now be
paid by the kinetic word instead of by the vanishing error bracket `C·μ²(a v)Γ·χ-mass·N`, and the
whole price is a smaller `ε₀` (which the free-threshold flat branch may take).

`K₂ = 0` recovers `perBoxF_of_ledger_sharp` verbatim (`perBoxF_of_ledger_sharp_of_kin` below) —
it is the same proof with `hkin` replaced by `0 ≤ sbKin`.

The only edit to the arithmetic of the skeleton is the last line: the `K₂·μ·(a v)·n₊` supply
cancels against the `K₂·μ·(a v)·n₊` allowance of the budget, giving exactly the skeleton's
conclusion.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- The box excited count `n₊(B) = cnPlusBoxInd` of the sliding box, in the argument order used
throughout this file. -/
noncomputable def nPlusB (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (n : ℕ) (Φ : X n → ℝ) : ℝ :=
  Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ

theorem perBoxF_of_ledger_kin {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R C μ c₁ K₂ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    {u : EuclideanSpace ℝ (Fin 3)} {Efib Epair V : ℝ}
    (hμ : 0 < μ) (hc₁ : 0 < c₁) (hc₁8 : c₁ ≤ 1 / 8) (hK₂ : 0 ≤ K₂)
    (hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
    (hW1 : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u)
    (hW12 : Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u
      ≤ Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u)
    (hτ : 0 ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
    (hV : 0 ≤ V)
    (hF : Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            * (μ * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
                / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ))
          + 4 * μ ^ 2
              / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ) ^ 2
            * V)
    (hfib : μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) + Efib)
    (hpair : (1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
            (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
          * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) + V)
        ≤ Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + Epair)
    (hsplit : Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = -(μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
    (hkin : K₂ * μ * (_root_.BoseGases.a v) * nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixB1.sbKin (v := v) μ (Work.BoseFixB1.pM v μ) u
        (Φ : Submission.BoseGases.X n → ℝ))
    (hbud : Efib + Epair
      ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                  * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          + μ * (_root_.BoseGases.a v)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u
          * ((Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              * (1 / 2 - c₁ * μ
                  / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ))
            + V * (1 / 2 - 4 * c₁ * μ ^ 2
                / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ) ^ 2))
        + K₂ * μ * (_root_.BoseGases.a v)
            * nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)) :
    Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
  rw [Work.BoseFixB1.PerBoxF, Work.BoseFixB1.sbWord, hsplit]
  have hFb_eq : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u x
            / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u))
      = Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ) := rfl
  rw [hFb_eq]
  set I : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hIdef
  set τ : ℝ := Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hτdef
  set W₁ : ℝ := Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u with hW₁def
  set W₂ : ℝ := Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u with hW₂def
  set Fb : ℝ := Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ) with hFbdef
  set Fs : ℝ := Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hFsdef
  set Ps : ℝ := Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hPsdef
  -- the arithmetic core at `(τ, I, V)`
  have hcore : c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2) + μ * τ * I
      ≤ (1 / 2) * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I :=
    Work.BoseFixB1S.flatArithSharpCore hμ hc₁ hc₁8 hτ hN hV
  -- scale by `W₁ ≤ W₂`, keeping the arithmetic slack
  have hslackid : W₁ * ((1 / 2) * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I)
      - W₁ * (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
          + μ * τ * I)
      = W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
          + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) := by
    have hτμ : τ + μ ≠ 0 := by positivity
    field_simp
    ring
  have hscaled : c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
        + μ * W₁ * τ * I
      ≤ (1 / 2) * W₂ * (τ ^ 2 * I + V) + (1 / 2) * μ ^ 2 * W₁ * I
        - W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
            + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) := by
    have hτ2V : 0 ≤ τ ^ 2 * I + V := by positivity
    have h1 : c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
          + μ * W₁ * τ * I
        = W₁ * (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
            + μ * τ * I) := by ring
    have h6 : (1 / 2) * W₁ * (τ ^ 2 * I + V) ≤ (1 / 2) * W₂ * (τ ^ 2 * I + V) :=
      mul_le_mul_of_nonneg_right (by linarith [hW12]) hτ2V
    have h7 : W₁ * ((1 / 2) * τ ^ 2 * I + (1 / 2) * V + (1 / 2) * μ ^ 2 * I)
        = (1 / 2) * W₁ * (τ ^ 2 * I + V) + (1 / 2) * μ ^ 2 * W₁ * I := by ring
    have h8 : W₁ * (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
            + μ * τ * I)
        = (1 / 2) * W₁ * (τ ^ 2 * I + V) + (1 / 2) * μ ^ 2 * W₁ * I
          - W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
              + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) := by
      rw [h7] at hslackid
      linarith [hslackid]
    have h4 : W₁ * (c₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2)
            + μ * τ * I)
        ≤ (1 / 2) * W₂ * (τ ^ 2 * I + V) + (1 / 2) * μ ^ 2 * W₁ * I
          - W₁ * ((τ - μ) ^ 2 * I * (1 / 2 - c₁ * μ / (τ + μ))
              + V * (1 / 2 - 4 * c₁ * μ ^ 2 / (τ + μ) ^ 2)) := by
      rw [h8]
      linarith [h6]
    linarith [h1, h4]
  have hF' : c₁ * W₁ * Fb
      ≤ c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hF (mul_nonneg hc₁.le hW1)
    have heq : c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 / (τ + μ) ^ 2 * V)
        = c₁ * W₁ * (I * (μ * (τ - μ) ^ 2 / (τ + μ)) + 4 * μ ^ 2 * V / (τ + μ) ^ 2) := by
      ring
    rwa [heq] at h
  have hpair' : (1 / 2) * W₂ * (τ ^ 2 * I + V) - Epair ≤ Ps := by linarith [hpair]
  linarith [hF', hscaled, hfib, hpair', hbud, hkin]



end Work.BoseFixB1.Up
