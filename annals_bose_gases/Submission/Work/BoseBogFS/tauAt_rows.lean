import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.ZPLatticeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open Work.BoseBox Work.BoseBoxFock Work.BoseFixR

/-!
# `Work.BoseBogFS.tauAt_rows` — the three pointwise rows of the honest symbol `τ`

`tauAt v μ k = tauSm eT s d ℓ k` is a convex combination of two rescaled copies of
the `C^∞` profile `tauProf` with thresholds `(2sℓ)⁻¹` and `(2dsℓ)⁻¹`.  The three
rows are:

* `0 ≤ tauAt v μ k` — both rescaled profile terms are nonnegative;
* `tauAt v μ k ≤ ‖k‖²` — from the profile bound `tauProf r ≤ (max 0 (r-1))²`, i.e.
  `c²·tauProf (x/c) ≤ x²` for `c > 0`;
* `‖k‖² - tauAt v μ k ≤ 2‖k‖/(dsℓ)` — from the profile bound
  `(max 0 (r-2))² ≤ tauProf r` together with `d ≤ 1` (`(sℓ)⁻¹ ≤ (dsℓ)⁻¹`), which
  produces the *sharp* factor `2` (the reverse kink direction costs `4‖k‖/(dsℓ)`).

The parameter facts `0 ≤ ε_T ≤ 1`, `0 < d ≤ 1`, `0 < s` come from FS's parameter
block `paramsAt μ (a v) = fsParams (μ·(a v)³)` and the diluteness
`μ·(a v)³ ≤ 1`: every parameter of `sec:params` here is a power
`(μa³)^{c/323}` with `c ≥ 0`, hence in `(0,1]`.

The two upper rows are exactly `Work.BoseRowsFS.tauSm_rows_core` — the sharp form
of the τ̃-rows (with `x = ‖k‖`, `u = (2sℓ)⁻¹`, `v = (2dsℓ)⁻¹`); the lower row is
the nonnegativity of the two rescaled profile summands.
-/

theorem tauAt_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) (hℓ : 0 < Work.BoseFixR.ell v μ)
    (ht : μ * _root_.BoseGases.a v ^ 3 ≤ 1) :
    (∀ k : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseBogFS.tauAt v μ k) ∧
    (∀ k : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.tauAt v μ k ≤ ‖k‖ ^ 2) ∧
    (∀ k : EuclideanSpace ℝ (Fin 3), ‖k‖ ^ 2 - Work.BoseBogFS.tauAt v μ k
       ≤ 2 * ‖k‖ / ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s * Work.BoseFixR.ell v μ)) := by
  have ht0 : 0 < μ * _root_.BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  have heT0 : 0 ≤ (paramsAt μ (_root_.BoseGases.a v)).eT := le_of_lt (fsXp_pos ht0)
  have heT1 : (paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 := fsXp_le_one ht0 ht (by norm_num)
  have hs : 0 < (paramsAt μ (_root_.BoseGases.a v)).s := fsXp_pos ht0
  have hd : 0 < (paramsAt μ (_root_.BoseGases.a v)).d := fsXp_pos ht0
  have hd1 : (paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := fsXp_le_one ht0 ht (by norm_num)
  have hu : 0 < (2 * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ)⁻¹ :=
    inv_pos.mpr (by positivity)
  have hv : 0 < (2 * (paramsAt μ (_root_.BoseGases.a v)).d
      * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ)⁻¹ :=
    inv_pos.mpr (by positivity)
  have huv : (2 * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ)⁻¹
      ≤ (2 * (paramsAt μ (_root_.BoseGases.a v)).d
          * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ)⁻¹ := by
    refine inv_anti₀ (b := 2 * (paramsAt μ (_root_.BoseGases.a v)).d
      * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ) (by positivity) ?_
    nlinarith [hd1, mul_pos hs hℓ]
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
  · exact tauAt_nonneg heT0 heT1 k
  · have hcore := Work.BoseRowsFS.tauSm_rows_core ‖k‖ (paramsAt μ (_root_.BoseGases.a v)).eT
      (2 * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ)⁻¹
      (2 * (paramsAt μ (_root_.BoseGases.a v)).d
        * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ)⁻¹
      (norm_nonneg k) heT0 heT1 hu hv huv
    rw [tauAt, Work.BoseBoxFock.tauSm]
    linarith [hcore.1]
  · have hcore := Work.BoseRowsFS.tauSm_rows_core ‖k‖ (paramsAt μ (_root_.BoseGases.a v)).eT
      (2 * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ)⁻¹
      (2 * (paramsAt μ (_root_.BoseGases.a v)).d
        * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ)⁻¹
      (norm_nonneg k) heT0 heT1 hu hv huv
    have hconv : 4 * ‖k‖ * (2 * (paramsAt μ (_root_.BoseGases.a v)).d
          * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ)⁻¹
        = 2 * ‖k‖ / ((paramsAt μ (_root_.BoseGases.a v)).d
            * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ) := by
      field_simp
      ring
    rw [tauAt, Work.BoseBoxFock.tauSm]
    linarith [hcore.2, hconv.le]

end Work.BoseBogFS
