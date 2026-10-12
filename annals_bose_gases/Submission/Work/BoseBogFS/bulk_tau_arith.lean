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

/-!
# `Work.BoseBogFS.bulk_tau_arith` — the bulk `τ`-row of the sharp `I₁` estimate

The `τ`-part of the comparison `psiSc ↔ gFun (fsTau …) (K.β) …`
(`FINDING_integral_cleanFun_le`) produces, after integration over the bulk `‖t‖ ≤ T`, the
two scalar rows

  `c₁·B_β²·(1 + log(T/(4c₁)))`  and  `c₁³·B_β²`

(`c₁ = bogC1 v ρ μ` the small kinetic cutoff, `B_β = bogBb R ℓ C = 8π(1 + 2C(R/ℓ)²)` the
`β`-upper bound, `T = bogT v R μ` FS's momentum cutoff).  Both are absorbed in FS's error
`lhyEps` with a comfortable `10⁸` slack: this is the statement below.

The proof is pure scalar arithmetic from the regime fields of `FsI1Regime`:

* `hcond` gives `B_β ≤ 16π`, hence `B_β² ≤ 256π² ≪ 10⁸`;
* `hreg.hc1val` identifies `c₁` with `½(K_ℓs)^{-1}√(μ/ρ)`, so (`hclose1` = FS's `eq:Close`)
  `c₁ ≤ (K_ℓs)^{-1} ≤ 1` and `c₁³ ≤ c₁`;
* writing `c₁ = d·c₂` (the two `c•val` fields), `log(T/c₁) = log(T/c₂) + log d^{-1}`, so
  `1 + log(T/(4c₁)) ≤ (1 + log(T/c₂)) + (1 + log d^{-1})`;
* `hEpsLog` bounds `(K_ℓs)^{-1}(1 + log(T/c₂))` by `lhyEps`, and the explicit summand
  `(K_ℓs)^{-1}(1 + log d^{-1} + log(K_ℓds/(μa³)^{1/2}))` of `lhyEps` (nonnegative, by
  `hlog1`) bounds `(K_ℓs)^{-1}(1 + log d^{-1})`; hence also `(K_ℓs)^{-1} ≤ lhyEps`.
-/

/-- `bogBb R ℓ C ≤ 16π` from FS's `C(R/ℓ)² ≤ 1/2` (`hcond`). -/
private lemma bogBb_le_sixteen_pi {R ℓ C : ℝ} (_hC : 0 ≤ C)
    (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    Work.BoseBogFS.bogBb R ℓ C ≤ 16 * Real.pi := by
  rw [Work.BoseBogFS.bogBb]
  nlinarith [Real.pi_pos, hcond]

/-- `bogBb` is nonnegative. -/
private lemma bogBb_nonneg' {R ℓ C : ℝ} (hC : 0 ≤ C) :
    0 ≤ Work.BoseBogFS.bogBb R ℓ C := by
  rw [Work.BoseBogFS.bogBb]
  have : 0 ≤ C * (R / ℓ) ^ 2 := mul_nonneg hC (sq_nonneg _)
  nlinarith [Real.pi_pos]

/-- The three elementary rows on FS's error `lhyEps`: nonnegativity, the bound
`(K_ℓs)^{-1} ≤ lhyEps` and the bound `(K_ℓs)^{-1}(1 + log d^{-1}) ≤ lhyEps` coming from
the explicit logarithmic summand of `eq:LebesgueError-Total` together with `hlog1`. -/
private lemma lhyEps_rows {a R μ eT Kl s d : ℝ}
    (_ha : 0 < a) (_hR : 0 ≤ R) (_hμ : 0 < μ) (hKl : 0 < Kl) (hs : 0 < s) (hd : 0 < d)
    (heT : 0 ≤ eT) (hd1 : d ≤ 1) (hlog1 : 1 ≤ Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)) :
    (Kl * s)⁻¹ ≤ Work.BoseB6.lhyEps a R eT Kl s d μ ∧
    (Kl * s)⁻¹ * (1 + Real.log d⁻¹) ≤ Work.BoseB6.lhyEps a R eT Kl s d μ ∧
    0 ≤ Work.BoseB6.lhyEps a R eT Kl s d μ := by
  have hKls : 0 < Kl * s := mul_pos hKl hs
  have hinv : 0 ≤ (Kl * s)⁻¹ := inv_nonneg.mpr hKls.le
  have hX : 0 ≤ Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)) := Real.log_nonneg hlog1
  have hlogd : 0 ≤ Real.log d⁻¹ := Real.log_nonneg ((one_le_inv₀ hd).mpr hd1)
  have ht1 : 0 ≤ (μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R :=
    mul_nonneg (Real.rpow_nonneg (by positivity) (1 / 4)) (Real.sqrt_nonneg R)
  have hds : 0 < Kl * d * s := by positivity
  have ht4 : 0 ≤ eT * (Kl * d * s)⁻¹
      * (1 + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) :=
    mul_nonneg (mul_nonneg heT (inv_nonneg.mpr hds.le)) (by linarith)
  have ht3 : (Kl * s)⁻¹ * (1 + Real.log d⁻¹) ≤
      (Kl * s)⁻¹ * (1 + Real.log d⁻¹
        + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hinv
    linarith
  have ht3' : (Kl * s)⁻¹ ≤
      (Kl * s)⁻¹ * (1 + Real.log d⁻¹
        + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) := by
    calc (Kl * s)⁻¹ = (Kl * s)⁻¹ * 1 := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hinv
        linarith
  rw [Work.BoseB6.lhyEps]
  refine ⟨by linarith, by linarith, by linarith⟩

theorem bulk_tau_arith {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R C ρ μ : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hcond : C * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2)
    (hreg : Work.BoseB6Est.FsI1Regime (Work.BoseBogFS.bogKernel v R ρ μ)
      (_root_.BoseGases.a v) R ρ μ
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) :
    Work.BoseBogFS.bogC1 v ρ μ * (Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) C) ^ 2
        * (1 + Real.log (Work.BoseBogFS.bogT v R μ / (4 * Work.BoseBogFS.bogC1 v ρ μ)))
      + (Work.BoseBogFS.bogC1 v ρ μ) ^ 3 * (Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) C) ^ 2
      ≤ 10 ^ 8 * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  set Kl := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl with hKldef
  set s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hsdef
  set d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set eT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTdef
  set c1 := Work.BoseBogFS.bogC1 v ρ μ with hc1def
  set c2 := Work.BoseBogFS.bogC2 v ρ μ with hc2def
  set T := Work.BoseBogFS.bogT v R μ with hTdef2
  set Bb := Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) C with hBbdef
  set E := Work.BoseB6.lhyEps (_root_.BoseGases.a v) R eT Kl s d μ with hEdef
  set bracket := 1 + Real.log (T / (4 * c1)) with hbrdef
  have hc1val : c1 = (1 / 2) * (Kl * s)⁻¹ * Real.sqrt (μ / ρ) := hreg.hc1val
  have hc2val : c2 = (1 / 2) * (Kl * d * s)⁻¹ * Real.sqrt (μ / ρ) := hreg.hc2val
  have hKl_pos : 0 < Kl := hreg.hKl
  have hs_pos : 0 < s := hreg.hs
  have hd_pos : 0 < d := hreg.hd
  have hKls_pos : 0 < Kl * s := mul_pos hKl_pos hs_pos
  have hKls_inv_nn : 0 ≤ (Kl * s)⁻¹ := inv_nonneg.mpr hKls_pos.le
  have hc1_nn : 0 ≤ c1 := hreg.hc1
  have hs2 : Real.sqrt (μ / ρ) ≤ 2 := hreg.sqrt_mu_div_rhoz_le_two
  have hc1_pos : 0 < c1 := by
    rw [hc1val]
    have : 0 < Real.sqrt (μ / ρ) := Real.sqrt_pos.mpr (div_pos hreg.hμ hreg.hρz)
    positivity
  have hc1_le_inv : c1 ≤ (Kl * s)⁻¹ := by
    rw [hc1val]
    calc (1 / 2) * (Kl * s)⁻¹ * Real.sqrt (μ / ρ) ≤ (1 / 2) * (Kl * s)⁻¹ * 2 := by
          apply mul_le_mul_of_nonneg_left hs2
          exact mul_nonneg (by norm_num) hKls_inv_nn
      _ = (Kl * s)⁻¹ := by ring
  have hc1_le_one : c1 ≤ 1 := by
    have h1 : (Kl * s)⁻¹ ≤ 1 := (inv_le_one₀ hKls_pos).mpr hreg.hKl1
    linarith
  have hc2_pos : 0 < c2 := hreg.c2_pos
  have hdc : d * c2 = c1 := by
    rw [hc1val, hc2val]
    rw [show Kl * d * s = (Kl * s) * d from by ring, mul_inv]
    field_simp
  have hTdef : (Work.BoseBogFS.bogKernel v R ρ μ).T = max 0 T := by
    rw [hTdef2]; exact Work.BoseBogFS.bogKernel_T v R ρ μ
  have hTge1 : 1 ≤ T := by
    have h1 : 1 ≤ (Work.BoseBogFS.bogKernel v R ρ μ).T := hreg.hT1
    rw [hTdef] at h1
    by_contra h
    rw [not_le] at h
    have h2 : max 0 T < 1 := max_lt zero_lt_one h
    linarith
  have hT_pos : 0 < T := lt_of_lt_of_le one_pos hTge1
  have hTmax : max 0 T = T := max_eq_right hT_pos.le
  have hTeq : (Work.BoseBogFS.bogKernel v R ρ μ).T = T := by rw [hTdef, hTmax]
  have hE_log' : (Kl * s)⁻¹ * (1 + Real.log (T / c2)) ≤ E := by
    have h := hreg.hEpsLog
    rw [hTeq] at h
    exact h
  have hrows := lhyEps_rows (a := _root_.BoseGases.a v) (R := R) (μ := μ) (eT := eT)
    (Kl := Kl) (s := s) (d := d) hreg.ha hreg.hR hreg.hμ hreg.hKl hreg.hs hreg.hd
    hreg.hε0 hreg.hd1 hreg.hlog1
  obtain ⟨hE_ge_Kls, hE_logd, hE_nn⟩ := hrows
  have hlog_mul : Real.log (T / c1) = Real.log (T / c2) + Real.log d⁻¹ := by
    have hdn : d ≠ 0 := hd_pos.ne'
    have hc2n : c2 ≠ 0 := hc2_pos.ne'
    have hTn : T ≠ 0 := hT_pos.ne'
    have key : T / c1 = (T / c2) * d⁻¹ := by
      rw [← hdc]
      field_simp
    rw [key, Real.log_mul (div_ne_zero hTn hc2n) (inv_ne_zero hdn)]
  have hbracket_le : bracket ≤ (1 + Real.log (T / c2)) + (1 + Real.log d⁻¹) := by
    have h1 : Real.log (T / (4 * c1)) ≤ Real.log (T / c1) := by
      apply Real.log_le_log
      · positivity
      · rw [div_le_div_iff₀ (by positivity) hc1_pos]
        nlinarith [hT_pos, hc1_nn]
    rw [hbrdef]
    linarith [h1, hlog_mul]
  have hBb_le := bogBb_le_sixteen_pi (R := R) (ℓ := Work.BoseFixR.ell v μ) hC hcond
  have hBb_nn := bogBb_nonneg' (R := R) (ℓ := Work.BoseFixR.ell v μ) hC
  have hBb2_nn : 0 ≤ Bb ^ 2 := sq_nonneg Bb
  have hconst : 3 * Bb ^ 2 ≤ 10 ^ 8 := by
    have h3 : Bb ^ 2 ≤ (16 * Real.pi) ^ 2 := pow_le_pow_left₀ hBb_nn hBb_le 2
    nlinarith [h3, Real.pi_pos, Real.pi_lt_four]
  have hc1_3_le_E : c1 ^ 3 ≤ E := by
    have hsq : c1 ^ 2 ≤ 1 := by nlinarith [hc1_nn, hc1_le_one]
    have h1 : c1 ^ 3 ≤ c1 := by
      calc c1 ^ 3 = c1 ^ 2 * c1 := by ring
        _ ≤ 1 * c1 := mul_le_mul_of_nonneg_right hsq hc1_nn
        _ = c1 := by ring
    linarith [h1, hc1_le_inv, hE_ge_Kls]
  have hc1_factor_le : c1 * bracket ≤ 2 * E := by
    by_cases hbr : 0 ≤ bracket
    · calc c1 * bracket ≤ (Kl * s)⁻¹ * bracket := mul_le_mul_of_nonneg_right hc1_le_inv hbr
        _ ≤ (Kl * s)⁻¹ * ((1 + Real.log (T / c2)) + (1 + Real.log d⁻¹)) :=
              mul_le_mul_of_nonneg_left hbracket_le hKls_inv_nn
        _ = (Kl * s)⁻¹ * (1 + Real.log (T / c2))
              + (Kl * s)⁻¹ * (1 + Real.log d⁻¹) := by ring
        _ ≤ E + E := add_le_add hE_log' hE_logd
        _ = 2 * E := by ring
    · rw [not_le] at hbr
      have h0 : c1 * bracket ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc1_nn hbr.le
      linarith [hE_nn, h0]
  have hmain : c1 * Bb ^ 2 * bracket + c1 ^ 3 * Bb ^ 2 ≤ 10 ^ 8 * E := by
    by_cases hbr : 0 ≤ bracket
    · have hA : c1 * Bb ^ 2 * bracket ≤ 2 * E * Bb ^ 2 := by
        have h1 : c1 * Bb ^ 2 * bracket = (c1 * bracket) * Bb ^ 2 := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right hc1_factor_le hBb2_nn
      have hB : c1 ^ 3 * Bb ^ 2 ≤ E * Bb ^ 2 :=
        mul_le_mul_of_nonneg_right hc1_3_le_E hBb2_nn
      have h3 : 3 * E * Bb ^ 2 ≤ 10 ^ 8 * E := by
        have h := mul_le_mul_of_nonneg_left hconst hE_nn
        rw [show E * (3 * Bb ^ 2) = 3 * E * Bb ^ 2 from by ring,
          show E * 10 ^ 8 = 10 ^ 8 * E from by ring] at h
        exact h
      linarith [hA, hB, h3]
    · rw [not_le] at hbr
      have hA : c1 * Bb ^ 2 * bracket ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc1_nn hBb2_nn) hbr.le
      have hB : c1 ^ 3 * Bb ^ 2 ≤ E * Bb ^ 2 :=
        mul_le_mul_of_nonneg_right hc1_3_le_E hBb2_nn
      have h2 : Bb ^ 2 ≤ 10 ^ 8 := by linarith [hBb2_nn, hconst]
      have h3 : E * Bb ^ 2 ≤ 10 ^ 8 * E := by
        calc E * Bb ^ 2 ≤ E * 10 ^ 8 := mul_le_mul_of_nonneg_left h2 hE_nn
          _ = 10 ^ 8 * E := by ring
      linarith [hA, hB, h3]
  exact hmain

end Work.BoseBogFS
