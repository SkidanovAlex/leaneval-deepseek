import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseRowQ2.RowsN
import Submission.Work.BoseRowQ2.rowMain_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseRowQ2/rowMainN_honest.lean` — the `RowMainN` row at the honest model

FS `final_v2.tex` l.3240–3262 with the **halved** `ℓ⁻²` credit of the corrected
`MainAtN` (`RowsN.lean`, the lead's ruling 2026-10-08): the freed `b/800` pays the
commutator constant `(C₁/κ_lat)²` of `GchiAtN`.

The proof is `Work.BoseRowQ2.rowMain_honest`'s, verbatim, with two changes:

* the two diluteness thresholds are **strengthened** (`honTAN`, `honTBN`, §0 below),
  because the low-momentum slot of the arithmetic (`rowMain_arith` in
  `rowMain_honest.lean`) is *tight*: it uses the whole `b/400` credit with the identity
  `ρŴ₁ω(0)(2ε + 8κ²R²)(48/π) ≤ (b/400)ℓ⁻²`, so halving the credit needs
  `2·58982400·t^{13/1292} ≤ (1/25600)t^{3/323}` and `8t^{302/323}(R/a)² ≤ (1/25600)t^{3/323}`
  instead of the `1/12800` versions;
* the three `b/400` occurrences (the low-momentum arithmetic, its use, and the charge
  inequality) become `b/800`.

Everything else — `W1omegaFun_bounds`, `honE_W1omega0_row`, `honE_W1omega_bounds`,
`honE_ell_rpow`, `honE_gap2_eq`, `fsEps_eq`, `honKappa_sq`, `qw_finset_sum`,
`etaH_eq_one` — is imported from `rowMain_honest.lean` and not re-proved.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! ## 0. The strengthened diluteness thresholds

`honTAN = 2^{-77520} = (2^{-60})^{1292}` gives `t^{1/1292} ≤ 2^{-60}`, hence
`2304·58982400·t^{13/1292} ≤ (1/25600)t^{3/323}` with a factor `2^{-36}` to spare
(the old `honTA = 2^{-65892}` gives only `t^{1/1292} ≤ 2^{-51}`, a factor `1.3` inside
the *old* `1/12800` slot — exactly the tightness the halving hits).

`honTBN a R = (2^{-31})^{323/299}(a/R)^{646/299}` gives `t^{299/323} ≤ 2^{-31}(a/R)²`,
hence `9216·t^{302/323}(R/a)² ≤ 2^{-15.83}t^{3/323} ≤ (1/25600)t^{3/323}`. -/

noncomputable def honTAN : ℝ := ((1 : ℝ) / 2) ^ (77520 : ℕ)

/-- `(2^{-31})^{323/299}(a/R)^{646/299}`: the second diluteness threshold, at which
`8·t^{302/323}(R/a)² ≤ (1/25600)t^{3/323}` (the low-momentum deficit row). -/
noncomputable def honTBN (a R : ℝ) : ℝ :=
  (((1 : ℝ) / 2) ^ (31 : ℕ)) ^ (323 / 299 : ℝ) * (a / R) ^ (646 / 299 : ℝ)

lemma honTAN_pos : 0 < honTAN := by
  rw [honTAN]; positivity

lemma honTBN_pos {a R : ℝ} (ha : 0 < a) (hR : 0 < R) : 0 < honTBN a R := by
  rw [honTBN]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)

private lemma rpow_honTAN {t e : ℝ} (ht : 0 < t) (h : t ≤ honTAN) (he : 0 ≤ e) :
    t ^ e ≤ ((1 : ℝ) / 2) ^ (77520 * e) := by
  rw [honTAN] at h
  calc t ^ e ≤ (((1 : ℝ) / 2) ^ (77520 : ℕ)) ^ e := Real.rpow_le_rpow ht.le h he
    _ = ((1 : ℝ) / 2) ^ (((77520 : ℕ) : ℝ) * e) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = ((1 : ℝ) / 2) ^ ((77520 : ℝ) * e) := by
        rw [show ((77520 : ℕ) : ℝ) = (77520 : ℝ) by norm_num]

/-- **The arithmetic at the halved credit.**  The four rows the `RowMainN` proof uses:
the `ε`-row is `≤ 1/2`, the two low-momentum terms fit `(1/25600)t^{3/323}` (half of
the `MainAt` slot, which with the factor `1152` of the `(48/π)` bookkeeping is exactly
the `b/800` credit), and the high-momentum (`n₊^H`) row fits `(1/12800)t^{-13/1292}`
(unchanged — the `NH` slot of `MainAtN` is still `b/800`). -/
private lemma rowMainN_arith {t a R : ℝ} (ht : 0 < t) (ha : 0 < a) (hR : 0 < R)
    (hTA : t ≤ honTAN) (hTB : t ≤ honTBN a R) :
    58982400 * t ^ (13 / 1292 : ℝ) ≤ 1 / 2
    ∧ 2304 * (58982400 * t ^ (13 / 1292 : ℝ)) ≤ (1 / 25600) * t ^ (3 / 323 : ℝ)
    ∧ 9216 * (t ^ (302 / 323 : ℝ) * (R / a) ^ 2) ≤ (1 / 25600) * t ^ (3 / 323 : ℝ)
    ∧ 2304 * Real.pi ≤ (1 / 12800) * t ^ (-(13 / 1292) : ℝ) := by
  have hpos3 : 0 < t ^ (3 / 323 : ℝ) := Real.rpow_pos_of_pos ht _
  have hA13 : t ^ (13 / 1292 : ℝ) ≤ ((1 : ℝ) / 2) ^ (780 : ℕ) := by
    have h := rpow_honTAN ht hTA (by norm_num : (0 : ℝ) ≤ 13 / 1292)
    have h780 : ((1 : ℝ) / 2) ^ ((77520 : ℝ) * (13 / 1292)) = ((1 : ℝ) / 2) ^ (780 : ℕ) := by
      rw [show (77520 : ℝ) * (13 / 1292) = ((780 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [h780] at h
  have hA1 : t ^ (1 / 1292 : ℝ) ≤ ((1 : ℝ) / 2) ^ (60 : ℕ) := by
    have h := rpow_honTAN ht hTA (by norm_num : (0 : ℝ) ≤ 1 / 1292)
    have h60 : ((1 : ℝ) / 2) ^ ((77520 : ℝ) * (1 / 1292)) = ((1 : ℝ) / 2) ^ (60 : ℕ) := by
      rw [show (77520 : ℝ) * (1 / 1292) = ((60 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [h60] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h27 : ((1 : ℝ) / 2) ^ (780 : ℕ) ≤ ((1 : ℝ) / 2) ^ (27 : ℕ) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num : 27 ≤ 780)
    have h2 : (58982400 : ℝ) * ((1 : ℝ) / 2) ^ (27 : ℕ) ≤ 1 / 2 := by norm_num
    calc 58982400 * t ^ (13 / 1292 : ℝ)
        ≤ 58982400 * ((1 : ℝ) / 2) ^ (780 : ℕ) :=
          mul_le_mul_of_nonneg_left hA13 (by norm_num)
      _ ≤ 58982400 * ((1 : ℝ) / 2) ^ (27 : ℕ) :=
          mul_le_mul_of_nonneg_left h27 (by norm_num)
      _ ≤ 1 / 2 := h2
  · have hconst : (2304 : ℝ) * 58982400 * ((1 : ℝ) / 2) ^ (60 : ℕ) ≤ 1 / 25600 := by norm_num
    have hsplit : t ^ (13 / 1292 : ℝ) = t ^ (3 / 323 : ℝ) * t ^ (1 / 1292 : ℝ) := by
      rw [show (13 / 1292 : ℝ) = 3 / 323 + 1 / 1292 by norm_num, Real.rpow_add ht]
    calc 2304 * (58982400 * t ^ (13 / 1292 : ℝ))
        = (2304 * 58982400) * (t ^ (3 / 323 : ℝ) * t ^ (1 / 1292 : ℝ)) := by
          rw [hsplit]; ring
      _ ≤ (2304 * 58982400) * (t ^ (3 / 323 : ℝ) * ((1 : ℝ) / 2) ^ (60 : ℕ)) := by
          have h := mul_le_mul_of_nonneg_left hA1 hpos3.le
          exact mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (2304 * 58982400 * ((1 : ℝ) / 2) ^ (60 : ℕ)) * t ^ (3 / 323 : ℝ) := by ring
      _ ≤ (1 / 25600) * t ^ (3 / 323 : ℝ) := mul_le_mul_of_nonneg_right hconst hpos3.le
  · have hTB1 : t ^ (299 / 323 : ℝ) ≤ ((1 : ℝ) / 2) ^ (31 : ℕ) * (a / R) ^ 2 := by
      have h1 : t ^ (299 / 323 : ℝ) ≤ (honTBN a R) ^ (299 / 323 : ℝ) :=
        Real.rpow_le_rpow ht.le hTB (by norm_num)
      have h2 : (honTBN a R) ^ (299 / 323 : ℝ) = ((1 : ℝ) / 2) ^ (31 : ℕ) * (a / R) ^ 2 := by
        rw [honTBN, Real.mul_rpow
          (Real.rpow_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 31) _)
          (Real.rpow_nonneg (div_nonneg ha.le hR.le) _)]
        rw [← Real.rpow_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 31),
          ← Real.rpow_mul (div_nonneg ha.le hR.le)]
        rw [show (323 / 299 : ℝ) * (299 / 323) = (1 : ℝ) by norm_num, Real.rpow_one]
        rw [show (646 / 299 : ℝ) * (299 / 323) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h2] at h1
      exact h1
    have hab : (a / R) ^ 2 * (R / a) ^ 2 = 1 := by
      rw [← mul_pow]
      rw [show a / R * (R / a) = 1 by field_simp]
      norm_num
    have hmain : t ^ (302 / 323 : ℝ) * (R / a) ^ 2
        ≤ ((1 : ℝ) / 2) ^ (31 : ℕ) * t ^ (3 / 323 : ℝ) := by
      have hsplit2 : t ^ (302 / 323 : ℝ) = t ^ (299 / 323 : ℝ) * t ^ (3 / 323 : ℝ) := by
        rw [show (302 / 323 : ℝ) = 299 / 323 + 3 / 323 by norm_num, Real.rpow_add ht]
      rw [hsplit2]
      have h := mul_le_mul_of_nonneg_right hTB1 (pow_nonneg (div_nonneg hR.le ha.le) 2)
      have h' : ((1 : ℝ) / 2) ^ (31 : ℕ) * (a / R) ^ 2 * (R / a) ^ 2
          = ((1 : ℝ) / 2) ^ (31 : ℕ) := by
        rw [mul_assoc, hab, mul_one]
      rw [h'] at h
      calc t ^ (299 / 323 : ℝ) * t ^ (3 / 323 : ℝ) * (R / a) ^ 2
          = (t ^ (299 / 323 : ℝ) * (R / a) ^ 2) * t ^ (3 / 323 : ℝ) := by ring
        _ ≤ ((1 : ℝ) / 2) ^ (31 : ℕ) * t ^ (3 / 323 : ℝ) :=
            mul_le_mul_of_nonneg_right h hpos3.le
    calc 9216 * (t ^ (302 / 323 : ℝ) * (R / a) ^ 2)
        ≤ 9216 * (((1 : ℝ) / 2) ^ (31 : ℕ) * t ^ (3 / 323 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
      _ = (9216 * ((1 : ℝ) / 2) ^ (31 : ℕ)) * t ^ (3 / 323 : ℝ) := by ring
      _ ≤ (1 / 25600) * t ^ (3 / 323 : ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num) hpos3.le
  · have h2 : (2 : ℝ) ^ (780 : ℕ) ≤ t ^ (-(13 / 1292) : ℝ) := by
      have h3 : (2 : ℝ) ^ (780 : ℕ) = (1 : ℝ) / ((1 : ℝ) / 2) ^ (780 : ℕ) := by
        rw [one_div, ← inv_pow]
        norm_num
      rw [h3]
      calc (1 : ℝ) / ((1 : ℝ) / 2) ^ (780 : ℕ)
          ≤ (1 : ℝ) / t ^ (13 / 1292 : ℝ) := one_div_le_one_div_of_le (by positivity) hA13
        _ = t ^ (-(13 / 1292) : ℝ) := by rw [one_div, ← Real.rpow_neg ht.le]
    have h4 : (2304 : ℝ) * Real.pi ≤ (1 / 12800) * (2 : ℝ) ^ (780 : ℕ) := by
      have h5 : (2 : ℝ) ^ (27 : ℕ) ≤ (2 : ℝ) ^ (780 : ℕ) :=
        pow_le_pow_right₀ (by norm_num) (by norm_num : 27 ≤ 780)
      have h6 : (2304 : ℝ) * 4 * 12800 ≤ (2 : ℝ) ^ (27 : ℕ) := by norm_num
      have h7 : (2304 : ℝ) * 4 * 12800 ≤ (2 : ℝ) ^ (780 : ℕ) := le_trans h6 h5
      have h8 : (2304 : ℝ) * 4 ≤ (2 : ℝ) ^ (780 : ℕ) / 12800 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12800)]
        exact h7
      calc (2304 : ℝ) * Real.pi ≤ (2304 : ℝ) * 4 := by linarith [Real.pi_lt_four]
        _ ≤ (2 : ℝ) ^ (780 : ℕ) / 12800 := h8
        _ = (1 / 12800) * (2 : ℝ) ^ (780 : ℕ) := by
            rw [div_eq_mul_inv, one_div]
            exact mul_comm _ _
    calc 2304 * Real.pi ≤ (1 / 12800) * (2 : ℝ) ^ (780 : ℕ) := h4
      _ ≤ (1 / 12800) * t ^ (-(13 / 1292) : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)

/-! ## 7. The row -/

theorem rowMainN_honest {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (εg : ℝ) (hεg : 0 < εg) (hεg1 : εg ≤ 1)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∃ Ng : ℝ → ℕ, ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧
      Work.BoseRowQ2.RowMainN (v := v) (h := h) (fc := fc) (fu := fu) R εg' Ng
        (Work.BoseRowQ2.fsEps v 58982400) := by
  refine ⟨fun _ => 0, min εg (min honTAN (honTBN (_root_.BoseGases.a v) R)),
    lt_min hεg (lt_min honTAN_pos (honTBN_pos hav hR)), min_le_left _ _, ?_⟩
  intro hεg'1 HM hNg μ hμ hμa ρ hρ Ψ
  have hμa3 : μ * _root_.BoseGases.a v ^ 3 ≤ εg := le_trans hμa (min_le_left _ _)
  have htA : μ * _root_.BoseGases.a v ^ 3 ≤ honTAN :=
    le_trans hμa (le_trans (min_le_right _ _) (min_le_left _ _))
  have htB : μ * _root_.BoseGases.a v ^ 3 ≤ honTBN (_root_.BoseGases.a v) R :=
    le_trans hμa (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht0 : 0 < μ * _root_.BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  obtain ⟨har0, har1, har2, har3⟩ := rowMainN_arith ht0 hav hR htA htB
  have hEℓ : (Work.BoseRowsFS.honE v h fc fu HM μ).ell = Work.BoseBoxFock.ellH v μ :=
    Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav
  have hℓEp : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
    rw [hEℓ]; exact Work.BoseBoxFock.ellH_pos v μ
  have hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := (hrég μ hμ hμa3).2
  have hRℓE : R ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).ell * Submission.BoseGases.chiR0 := by
    rw [hEℓ]; exact hRℓ
  obtain ⟨hW0nn, hW0le⟩ := honE_W1omega0_row (v := v) (h := h) (fc := fc) (fu := fu)
    (R := R) (εg := εg) hR hav hv_nonneg hvrad hv_supp hrég HM μ hμ hμa3
  obtain ⟨hwkge, hwkdef⟩ := honE_W1omega_bounds (v := v) (h := h) (fc := fc) (fu := fu)
    (HM := HM) (R := R) (μ := μ) hR hv_nonneg hvrad hv_supp hμ hav hRℓ
  have hμeq : (Work.BoseRowsFS.honE v h fc fu HM μ).mu = μ := rfl
  have hκpos : 0 < honKappa v μ := by
    rw [honKappa]
    refine mul_pos (Real.rpow_pos_of_pos ?_ _) (Real.sqrt_pos.mpr (mul_pos hμ hav))
    exact mul_pos (Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3)))
      (pow_pos (Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3))) 2)
  have heps : Work.BoseRowQ2.fsEps v 58982400 μ
      = 58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ) := fsEps_eq hμ hav
  have hκR : (honKappa v μ) ^ 2 * R ^ 2
      = (μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ) * (R / _root_.BoseGases.a v) ^ 2 := by
    rw [honKappa_sq hμ hav]; ring
  have hell2 : (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
      = (μ * _root_.BoseGases.a v) * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ) :=
    honE_ell_rpow hμ hav
  have hgap2 : (Work.BoseRowsFS.honE v h fc fu HM μ).eT
        * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))
      = (μ * _root_.BoseGases.a v) * (μ * _root_.BoseGases.a v ^ 3) ^ (-(13 / 1292) : ℝ) :=
    honE_gap2_eq hμ hav
  have hb16 : (Work.BoseRowsFS.honE v h fc fu HM μ).b = 1 / 16 :=
    Work.BoseRowsFS.honE_b v h fc fu HM μ
  -- §3 the `Ŵ₁ω` facts at the environment
  have hAunf : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
      = ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) :=
    Work.BoseB7.FockData.qw_allNumOp _ _
  have hQunf : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
      = ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
          ρ * ((Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k
              + (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
    rw [Work.BoseB7.FockData.qw_Q2exAll]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hρ' : (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).rho = ρ :=
      KzEnvAt_rho _ ρ hρ.1 hℓEp
    have hw1 : (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).W1omega
        = (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega := rfl
    have hw0 : (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).W1omega0
        = (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := rfl
    rw [hρ', hw1, hw0]
  have hBessel : ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
      ≤ (48 / Real.pi) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (Work.BoseRowsFS.honT v h fc fu HM μ).N := by
    have hbes := Work.BoseBoxFock.bessel_honest v h fc fu HM μ Ψ
    have hsum : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
            (Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        = ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
            (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
      have hq := Work.BoseB7.FockData.qw_sum_all (Work.BoseRowsFS.honF v h fc fu HM μ) Ψ
        (fun _ => (1 : ℝ)) (fun k => (Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
      simpa using hq
    rw [← hsum]
    exact hbes
  have hNHunf : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        (Work.BoseRowsFS.honT v h fc fu HM μ).NH
      = (1 / 32 : ℝ) * ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          Work.BoseBoxFock.etaH fu (honKappa v μ)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
    have hNHform : (Work.BoseRowsFS.honT v h fc fu HM μ).NH
        = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
            Work.BoseBoxFock.etaH fu (honKappa v μ)
                ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
              • (Work.BoseRowsFS.honF v h fc fu HM μ).nOp k := by
      simp only [Work.BoseRowsFS.honT, Work.BoseRowsFS.honF, Work.BoseBoxFock.HonestBoxFam,
        Work.BoseBoxFock.tildeDataHon, Work.BoseRowQ2.honKappa]
      rfl
    rw [hNHform, Work.BoseB7.FockData.qw_smul, qw_finset_sum]
  have hHle : ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
          ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
        (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
      ≤ 32 * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
    rw [hNHunf]
    have hsub : ∀ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
          ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
        k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨-, hk2⟩ := hk
      rw [Work.BoseB7.excited, Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hk0
      have hkm : (Work.BoseRowsFS.honF v h fc fu HM μ).kmom k = 0 := by
        rw [hk0, Work.BoseRowsFS.honF_kmom]
        exact Work.BoseBoxFock.kmomLab_zero (Work.BoseBoxFock.ellH v μ) (HM μ).N
      rw [hkm, norm_zero] at hk2
      have : (0 : ℝ) < 4 * honKappa v μ := by linarith [hκpos]
      linarith
    have h1 : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          Work.BoseBoxFock.etaH fu (honKappa v μ)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≥ ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
            (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
      rw [ge_iff_le]
      calc ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
            (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
          = ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
              Work.BoseBoxFock.etaH fu (honKappa v μ)
                ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [Finset.mem_filter] at hk
            rw [etaH_eq_one fu hκpos (not_lt.mp hk.2), one_mul]
        _ ≤ _ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
              mul_nonneg (Work.BoseBoxFock.etaH_nonneg fu (honKappa v μ) _)
                (Work.BoseB7.FockData.nOp_qw_nonneg' _ k Ψ))
    rw [show (32 : ℝ) * ((1 / 32) * ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          Work.BoseBoxFock.etaH fu (honKappa v μ)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k))
        = ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          Work.BoseBoxFock.etaH fu (honKappa v μ)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) from by ring]
    linarith [h1]
  -- the two arithmetic estimates
  have hNvnn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
      (Work.BoseRowsFS.honT v h fc fu HM μ).N :=
    (Work.BoseRowsFS.honT v h fc fu HM μ).N_nonneg Ψ
  have hNHvnn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
      (Work.BoseRowsFS.honT v h fc fu HM μ).NH :=
    (Work.BoseRowsFS.honT v h fc fu HM μ).NH_nonneg Ψ
  have hρle : ρ ≤ 3 * μ / 2 := by rw [← hμeq]; exact hρ.2.2
  have heps1 : Work.BoseRowQ2.fsEps v 58982400 μ ≤ 1 / 2 := by
    rw [heps]; exact har0
  have hμapos : 0 < μ * _root_.BoseGases.a v := mul_pos hμ hav
  have ht3nn : 0 ≤ (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ) :=
    Real.rpow_nonneg (le_of_lt ht0) _
  have hW0bound : ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
      ≤ (μ * _root_.BoseGases.a v) * 24 * Real.pi := by
    calc ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        ≤ (3 * μ / 2) * (16 * Real.pi * _root_.BoseGases.a v) :=
          mul_le_mul hρle hW0le hW0nn (by positivity)
      _ = (μ * _root_.BoseGases.a v) * 24 * Real.pi := by ring
  have harith1 : ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (2 * Work.BoseRowQ2.fsEps v 58982400 μ + 8 * (honKappa v μ) ^ 2 * R ^ 2)
        * (48 / Real.pi)
      ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
          * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ)) := by
    rw [hb16, hell2, heps]
    rw [show (2 * (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))
          + 8 * (honKappa v μ) ^ 2 * R ^ 2)
        = (2 * (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))
          + 8 * ((honKappa v μ) ^ 2 * R ^ 2)) by ring]
    rw [hκR]
    have hcoef : 2 * (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))
          + 8 * ((μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ)
              * (R / _root_.BoseGases.a v) ^ 2)
        ≤ ((1 / 12800) * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ)) / 1152 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1152)]
      linarith [har1, har2]
    calc ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          * (2 * (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))
            + 8 * ((μ * _root_.BoseGases.a v ^ 3) ^ (302 / 323 : ℝ)
                * (R / _root_.BoseGases.a v) ^ 2))
          * (48 / Real.pi)
        ≤ ((μ * _root_.BoseGases.a v) * 24 * Real.pi)
            * (((1 / 12800) * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ)) / 1152)
            * (48 / Real.pi) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hW0bound hcoef (by positivity) (by positivity))
            (by positivity)
      _ = (1 / 16 / 800) * ((μ * _root_.BoseGases.a v)
            * (μ * _root_.BoseGases.a v ^ 3) ^ (3 / 323 : ℝ)) := by
          field_simp
          ring
  have harith2 : 3 * 32 * (ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
      ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
          * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                  * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))) := by
    rw [hb16, hgap2]
    calc 3 * 32 * (ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
        ≤ 3 * 32 * ((μ * _root_.BoseGases.a v) * 24 * Real.pi) := by linarith [hW0bound]
      _ = 2304 * Real.pi * (μ * _root_.BoseGases.a v) := by ring
      _ ≤ (1 / 12800) * (μ * _root_.BoseGases.a v ^ 3) ^ (-(13 / 1292) : ℝ)
            * (μ * _root_.BoseGases.a v) :=
          mul_le_mul_of_nonneg_right har3 (le_of_lt hμapos)
      _ = (1 / 16 / 800) * ((μ * _root_.BoseGases.a v)
            * (μ * _root_.BoseGases.a v ^ 3) ^ (-(13 / 1292) : ℝ)) := by ring
  -- the charge inequality
  have hcharge : ρ * (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
        ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k))
      ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
          * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).N
        + (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
          * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                  * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N))
      (fun k => ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)
      (fun k => ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k))
    rw [← hsplit]
    have hcoefnn : 0 ≤ (2 * Work.BoseRowQ2.fsEps v 58982400 μ
        + 8 * (honKappa v μ) ^ 2 * R ^ 2) * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := by
      have he : 0 < Work.BoseRowQ2.fsEps v 58982400 μ := by rw [heps]; positivity
      refine mul_nonneg (by
        have hk2 : 0 ≤ (honKappa v μ) ^ 2 := sq_nonneg _
        have hR2 : 0 ≤ R ^ 2 := sq_nonneg _
        nlinarith [he, mul_nonneg hk2 hR2]) hW0nn
    have hLow : ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)),
          ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ ((2 * Work.BoseRowQ2.fsEps v 58982400 μ + 8 * (honKappa v μ) ^ 2 * R ^ 2)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
          * ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)),
              (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_filter] at hk
      have hklt : ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ := hk.2
      have h1 : (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k
          ≤ (1 / 2) * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2 * R ^ 2
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := hwkdef k
      have h2 : (1 / 2) * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2 * R ^ 2
          ≤ 8 * (honKappa v μ) ^ 2 * R ^ 2 := by
        have hx2 : ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
            < 16 * (honKappa v μ) ^ 2 := by
          nlinarith [hklt, norm_nonneg ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k), hκpos.le]
        nlinarith [hx2, hR]
      have h3 : ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          ≤ (2 * Work.BoseRowQ2.fsEps v 58982400 μ + 8 * (honKappa v μ) ^ 2 * R ^ 2)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := by
        nlinarith [h1, h2, hW0nn]
      exact mul_le_mul_of_nonneg_right h3
        (Work.BoseB7.FockData.nOp_qw_nonneg' _ k Ψ)
    have hHigh : ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
          ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ 3 * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          * ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
              ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
              (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have h1 : -(Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k := hwkge k
      have h3 : ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          ≤ 3 * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := by
        nlinarith [h1, heps1, hW0nn]
      exact mul_le_mul_of_nonneg_right h3
        (Work.BoseB7.FockData.nOp_qw_nonneg' _ k Ψ)
    have hA_low : ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)),
          (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ (48 / Real.pi) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            (Work.BoseRowsFS.honT v h fc fu HM μ).N := by
      calc _ ≤ ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
              (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun k _ _ => Work.BoseB7.FockData.nOp_qw_nonneg' _ k Ψ)
        _ ≤ _ := hBessel
    have hL : ρ * ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ)),
          ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).N := by
      have h1 := mul_le_mul_of_nonneg_left hLow hρ.1
      have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA_low hcoefnn) hρ.1
      have h3 := mul_le_mul_of_nonneg_right harith1 hNvnn
      have h4 : ρ * (((2 * Work.BoseRowQ2.fsEps v 58982400 μ
              + 8 * (honKappa v μ) ^ 2 * R ^ 2)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
            * ((48 / Real.pi) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).N))
          = (ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
              * (2 * Work.BoseRowQ2.fsEps v 58982400 μ + 8 * (honKappa v μ) ^ 2 * R ^ 2)
              * (48 / Real.pi)) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).N := by ring
      linarith [h1, h2, h3, h4]
    have hH : ρ * ∑ k ∈ (Finset.univ.filter (fun k : Work.BoseBoxFock.Lab (HM μ).N =>
            ¬ (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ < 4 * honKappa v μ))),
          ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)
        ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
            * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                    * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
      have h1 := mul_le_mul_of_nonneg_left hHigh hρ.1
      have h2 := mul_le_mul_of_nonneg_left hHle
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hρ.1) hW0nn)
      have h3 := mul_le_mul_of_nonneg_right harith2 hNHvnn
      have h4 : ρ * (3 * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            * (32 * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).NH))
          = (3 * 32 * (ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by ring
      linarith [h1, h2, h3, h4]
    linarith [hL, hH]
  -- the algebraic bridge
  have hbridge : 2 * ρ * (1 + Work.BoseRowQ2.fsEps v 58982400 μ)
        * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
      = (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
              (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
        + ρ * (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
            ((1 + 2 * Work.BoseRowQ2.fsEps v 58982400 μ)
                * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
              - (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega k)
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp k)) := by
    rw [hAunf, hQunf]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  linarith [hcharge, hbridge]

end Work.BoseRowQ2
