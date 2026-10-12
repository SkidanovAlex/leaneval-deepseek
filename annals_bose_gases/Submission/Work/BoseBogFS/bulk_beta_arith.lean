import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.BogFSCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

-- `hav : 0 < a v` is part of the frozen statement; the arithmetic below only uses the regime
-- structure `hreg` and the domination `hbeta`, so the hypothesis is not referenced explicitly.
set_option linter.unusedVariables false

/-!
# `Work.BoseBogFS.bulk_beta_arith` — the bulk `β`-row of the sharp `I₁` estimate

On the bulk `‖t‖ ≤ T` the `β`-comparison contributes the *nonlinear* bracket

  `Δ·T³/3 + η·T⁴/2 + (B_β + ηT)·(Δ·T + η·T²)`

to the error, where

* `T = bogT v R μ` is FS's momentum cutoff,
* `η = bogEta v R ρ = 16πR√(ρa)` is the Lipschitz constant of the honest `β`,
* `Δ = bogDelta R ℓ C = 16πC(R/ℓ)²` is the `χ⋆χ` Taylor deficit at the box scale,
* `B_β = bogBb R ℓ C = 8π(1 + 2C(R/ℓ)²)` is the bulk upper bound for `β`,
* `C = chiTC` is the *fixed* Taylor constant of `χ⋆χ` (see `BogFSCompare`),

and the error is FS's `lhyEps = ε(μ,ρ_z)`.  The hypothesis `hbeta` is exactly the statement
that FS's error dominates the two quartic rows `ΔT³` and `ηT⁴`; FS's regime (`FsI1Regime`)
supplies the remaining scalar input, namely

* `B_β ≤ 16π`: from the smallness of the Taylor remainder, `C(R/ℓ)² ≤ 1/2` (`hcond`);
* `η ≤ 1` and `ηT ≤ 1` (`hreg.hηT`), together with `T ≥ 1` (`hreg.hT1`).

**Mathematics.**  Let `X := ΔT³ + ηT⁴ ≤ ε`.  Since `T ≥ 1`,

  `ΔT + ηT² = X/T² ≤ X ≤ ε`,

so the whole bracket is bounded by

  `ε/3 + ε/2 + (B_β + ηT)·ε ≤ ε/3 + ε/2 + (16π + 1)·ε ≤ 100ε`

because `16π + 1 + 5/6 < 100`.  (No smallness of `Δ` beyond its sign is used: the `T³`-powers
in the bracket are absorbed by dividing the *single* quartic row `X` by `T²`.)  All `T`-powers
below `1` are harmless because `T ≥ 1`; this is what makes the `10²` constant — rather than an
`O(ε)`-free constant — absorb the bracket.
-/

/-- **The scalar core of `bulk_beta_arith`.**  With `T ≥ 1`, `η, Δ ≥ 0`, `B_β ≥ 0`,
`ηT ≤ 1`, `B_β ≤ 16π` and `ΔT³ + ηT⁴ ≤ E`, the whole bulk `β`-bracket is at most `100·E`.

The only analytic input is the domination of the quartic row `ΔT³ + ηT⁴`; the cubic, linear
and logarithmic-looking rows are all obtained by dividing it by a power of `T ≥ 1`. -/
private lemma bulkBeta_arith_core {Delta eta T Bb E : ℝ}
    (hT : 1 ≤ T) (heta : 0 ≤ eta) (hDelta : 0 ≤ Delta) (hBb0 : 0 ≤ Bb)
    (hetaT : eta * T ≤ 1) (hBb : Bb ≤ 16 * Real.pi) (hE : 0 ≤ E)
    (hX : Delta * T ^ 3 + eta * T ^ 4 ≤ E) :
    Delta * T ^ 3 / 3 + eta * T ^ 4 / 2 + (Bb + eta * T) * (Delta * T + eta * T ^ 2)
      ≤ 100 * E := by
  have hT_pos : 0 < T := lt_of_lt_of_le one_pos hT
  have hT2_ge1 : (1 : ℝ) ≤ T ^ 2 := by nlinarith
  -- the single quartic row controls the linear one
  have hsum_le : Delta * T + eta * T ^ 2 ≤ E := by
    have key : Delta * T + eta * T ^ 2 = (Delta * T ^ 3 + eta * T ^ 4) / T ^ 2 := by
      rw [eq_div_iff (by positivity : T ^ 2 ≠ 0)]
      ring
    rw [key]
    have h1 : (Delta * T ^ 3 + eta * T ^ 4) / T ^ 2 ≤ E / T ^ 2 :=
      div_le_div_of_nonneg_right hX (sq_nonneg T)
    have h2 : E / T ^ 2 ≤ E := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < T ^ 2)]
      nlinarith [hE, hT2_ge1]
    linarith
  -- the cubic and quartic rows
  have hterm1 : Delta * T ^ 3 / 3 ≤ E / 3 := by
    have h3 : Delta * T ^ 3 ≤ E :=
      le_trans (le_add_of_nonneg_right (mul_nonneg heta (pow_nonneg hT_pos.le 4))) hX
    linarith
  have hterm2 : eta * T ^ 4 / 2 ≤ E / 2 := by
    have h4 : eta * T ^ 4 ≤ E :=
      le_trans (le_add_of_nonneg_left (mul_nonneg hDelta (pow_nonneg hT_pos.le 3))) hX
    linarith
  have hterm3 : (Bb + eta * T) * (Delta * T + eta * T ^ 2) ≤ (16 * Real.pi + 1) * E := by
    have hnn : 0 ≤ Bb + eta * T := add_nonneg hBb0 (mul_nonneg heta hT_pos.le)
    have hle : Bb + eta * T ≤ 16 * Real.pi + 1 := by linarith
    calc (Bb + eta * T) * (Delta * T + eta * T ^ 2) ≤ (Bb + eta * T) * E :=
          mul_le_mul_of_nonneg_left hsum_le hnn
      _ ≤ (16 * Real.pi + 1) * E := mul_le_mul_of_nonneg_right hle hE
  have hcoef : (1 : ℝ) / 3 + 1 / 2 + (16 * Real.pi + 1) ≤ 100 := by
    nlinarith [Real.pi_lt_four]
  have hlast : E / 3 + E / 2 + (16 * Real.pi + 1) * E ≤ 100 * E := by
    have heq : E / 3 + E / 2 + (16 * Real.pi + 1) * E
        = E * (1 / 3 + 1 / 2 + (16 * Real.pi + 1)) := by ring
    rw [heq]
    calc E * (1 / 3 + 1 / 2 + (16 * Real.pi + 1)) ≤ E * 100 :=
          mul_le_mul_of_nonneg_left hcoef hE
      _ = 100 * E := by ring
  linarith [hterm1, hterm2, hterm3, hlast]

theorem bulk_beta_arith {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ρ μ : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ)
    (hcond : Work.BoseBogFS.chiTC * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2)
    (hreg : Work.BoseB6Est.FsI1Regime (Work.BoseBogFS.bogKernel v R ρ μ)
      (_root_.BoseGases.a v) R ρ μ
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hbeta : Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
          * (Work.BoseBogFS.bogT v R μ) ^ 3
        + Work.BoseBogFS.bogEta v R ρ * (Work.BoseBogFS.bogT v R μ) ^ 4
        ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) :
    Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
        * (Work.BoseBogFS.bogT v R μ) ^ 3 / 3
      + Work.BoseBogFS.bogEta v R ρ * (Work.BoseBogFS.bogT v R μ) ^ 4 / 2
      + (Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
          + Work.BoseBogFS.bogEta v R ρ * Work.BoseBogFS.bogT v R μ)
        * (Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
              * Work.BoseBogFS.bogT v R μ
          + Work.BoseBogFS.bogEta v R ρ * (Work.BoseBogFS.bogT v R μ) ^ 2)
      ≤ 100 * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  set Kl := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl with hKldef
  set s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hsdef
  set d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set eT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTdef
  set C := Work.BoseBogFS.chiTC with hCdef
  set ell := Work.BoseFixR.ell v μ with helldef
  set Delta := Work.BoseBogFS.bogDelta R ell C with hDeltadef
  set eta := Work.BoseBogFS.bogEta v R ρ with hetadef
  set T := Work.BoseBogFS.bogT v R μ with hTdef
  set Bb := Work.BoseBogFS.bogBb R ell C with hBbdef
  set E := Work.BoseB6.lhyEps (_root_.BoseGases.a v) R eT Kl s d μ with hEdef
  have hC_nn : 0 ≤ C := Work.BoseBogFS.chiTC_nonneg
  have heta_nn : 0 ≤ eta := Work.BoseBogFS.bogEta_nonneg v hR.le hρ.le
  -- `T ≥ 1`: `bogKernel v R ρ μ` is `honKernel (max 0 η) (max 0 T)` and `hT1 : 1 ≤ K.T`
  have hTmax : 1 ≤ max 0 T := by
    have h := hreg.hT1
    rwa [Work.BoseBogFS.bogKernel_T, ← hTdef] at h
  have hTge1 : 1 ≤ T := by
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (max_lt zero_lt_one hcon) (not_lt.mpr hTmax)
  have hT_pos : 0 < T := lt_of_lt_of_le one_pos hTge1
  -- `ηT ≤ 1`
  have hetaT_le1 : eta * T ≤ 1 := by
    have h := hreg.hηT
    rw [Work.BoseBogFS.bogKernel_eta, Work.BoseBogFS.bogKernel_T, ← hetadef, ← hTdef] at h
    rwa [max_eq_right heta_nn, max_eq_right hT_pos.le] at h
  have hDelta_nn : 0 ≤ Delta := by
    rw [hDeltadef, Work.BoseBogFS.bogDelta]
    have : 0 ≤ (R / ell) ^ 2 := sq_nonneg _
    positivity
  have hBb_le : Bb ≤ 16 * Real.pi := by
    have h2 : 0 ≤ (R / ell) ^ 2 := sq_nonneg _
    rw [hBbdef, Work.BoseBogFS.bogBb]
    nlinarith [Real.pi_pos, hcond]
  have hBb_nn : 0 ≤ Bb := by
    rw [hBbdef, Work.BoseBogFS.bogBb]
    have h2 : 0 ≤ (R / ell) ^ 2 := sq_nonneg _
    nlinarith [Real.pi_pos, mul_nonneg hC_nn h2]
  exact bulkBeta_arith_core hTge1 heta_nn hDelta_nn hBb_nn hetaT_le1 hBb_le
    hreg.lhyEps_nonneg hbeta

end Work.BoseBogFS
