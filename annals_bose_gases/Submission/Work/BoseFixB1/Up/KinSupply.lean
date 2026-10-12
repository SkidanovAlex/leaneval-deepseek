import ChallengeDeps
import Submission.Work.BoseFixB1.Up.LedgerKin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.KinSupply` — **the kinetic word pays an arbitrary multiple of `μ (a v) n₊`**

This is the *lever* of the flat (condensed) branch.  The corpus knows

* `Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus`:

      `c'² · μ · (a v) · n₊(B) ≤ sbKin`      whenever
      `2(1+π⁻²)(dℓ · c' · √(μ (a v)))² ≤ ε_T` ;

* `Up.gapRegime_of_adm`: for **every** prescribed `c' ≥ 0` there is `ε₀ > 0` making that regime
  hold at every admissible `μ` (the threshold is `ε₀ ≤ (1/(2(1+π⁻²)c'²+1))^{1292/13} > 0`).

Putting the two together (with `c' = √K₂` and `0 ≤ ε_T` ⟸ `Adm`, `0 ≤ tBwordKinInd`) gives the
statement below: **for every prescribed coefficient `K₂ ≥ 0` there is `ε₀ > 0` such that, on the
whole admissible range,**

    `K₂ · μ · (a v) · n₊(B)  ≤  sbKin` .

Since `K₂` is *arbitrary* — the only price is a smaller `ε₀` — this converts `sbKin` from the
"nonnegative" word used by `Work.BoseFixB1S.perBoxF_of_ledger_sharp` (`hkin : 0 ≤ sbKin`) into an
*arbitrarily large* multiple of the box excited count.  Every error row of the flat branch that is
bounded by a constant times `μ (a v) n₊(B)` can therefore be discharged by the kinetic word; the
ledger `Up.perBoxF_of_ledger_kin` is the bookkeeping that consumes it.

Note the direction of the trade: raising `K₂` shrinks `ε₀` but does **not** change any other
constant of the dichotomy, because `Up.gapAtAll` is available at every threshold (the gap branch
is stated with its own `∃ ε₀`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The kinetic supply at an arbitrary prescribed coefficient.**  For every `K₂ ≥ 0` (and every
scattering solution `v` with `a v > 0`) there is `ε₀ > 0` such that, at every admissible `μ` and
every box state,

    `K₂ · μ · (a v) · n₊(B) ≤ sbKin` ,

with `n₊(B) = Up.nPlusB v μ u n Φ = cnPlusBoxInd` of the sliding box. -/
theorem sbKin_ge_K2_mu_av_nPlus {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        K₂ * μ * (_root_.BoseGases.a v) * nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbKin (v := v) μ (paramsAt μ (_root_.BoseGases.a v)).M u
              (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨ε, hε, hreg⟩ :=
    gapRegime_of_adm (v := v) hav (c' := Real.sqrt K₂) (Real.sqrt_nonneg K₂)
  refine ⟨ε, hε, ?_⟩
  intro μ hAdm n Φ u
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < sideAt μ (_root_.BoseGases.a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (_root_.BoseGases.a v)).d := adm_d_pos hAdm
  have hsqrt : (Real.sqrt K₂) ^ 2 = K₂ := Real.sq_sqrt hK₂
  have h := sbKin_ge_mu_av_cnPlus (v := v) (μ := μ) (c' := Real.sqrt K₂)
    (M := (paramsAt μ (_root_.BoseGases.a v)).M) (u := u) (Φ := (Φ : Submission.BoseGases.X n → ℝ))
    (le_of_lt hav) hμ.le (Real.sqrt_nonneg K₂) (mul_pos hd hℓ) (adm_eT_pos hAdm)
    (hreg μ hAdm) (tBwordKinInd_nonneg ((Φ : Submission.BoseGases.X n → ℝ)))
  rw [hsqrt] at h
  simpa only [nPlusB] using h

/-- The `K₂ = 1` case, in the shape most convenient for the flat-branch rows: the kinetic word
dominates the whole `μ (a v) n₊` supply at a single threshold `ε₀`. -/
theorem sbKin_ge_mu_av_nPlus {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        1 * μ * (_root_.BoseGases.a v) * nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbKin (v := v) μ (paramsAt μ (_root_.BoseGases.a v)).M u
              (Φ : Submission.BoseGases.X n → ℝ) :=
  sbKin_ge_K2_mu_av_nPlus hav 1 zero_le_one

end Work.BoseFixB1.Up
