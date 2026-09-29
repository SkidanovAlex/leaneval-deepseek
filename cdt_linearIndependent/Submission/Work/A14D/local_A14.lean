import Mathlib
import Submission.Work.A14D.classZ_defs
import Submission.Work.A14D.chainZDefs

/-!
# A14 — local expansion data at `x = 0` of the classes `clsZ k` (`k ≤ 3`)

`Work.A14D.u2, w2, u3, w3` (`Submission/Work/A14D/classZ_defs.lean`) are the coordinates of the
classes of `∂_y^k` in the `P`-branch module of Zagier's operator
`L_Z y = (P y')' + R y`, `P = x(1−x)(1−9x) = x − 10x² + 9x³`, `R = 9x − 3`,
`∂_y = ρ ∂_x`, `ρ = (x−1)²/(x²−2x)`:

* `clsZ 2 = (u2, v2)`, `clsZ 3 = (u3, v3)` with `v2 = ρ·w2`, `v3 = ρ·w3`.

This file computes the two-term expansions of `u2, w2, v2, u3, w3` at `x = 0`
(`Work.C17.Lead2At f e l m` means `f = x^e(l + mx + O(x²))`, `l ≠ 0`):

  `u2 = x^{-3}(3/4 + 3x + O(x²))`,   `w2 = x^{-2}(1 − 23x/4 + O(x²))`,
  `u3 = x^{-5}(15/8 + O(x²))`,       `w3 = x^{-4}(2 − 121x/8 + O(x²))`.

The engine is the `Work.C17.Exp2` calculus (`Exp2` is `Lead2At` without the requirement `l ≠ 0`,
closed under `+`, `−`, `·`, inversion, `dRat` and order shifts), exactly as in
`Submission/Work/C17/local_dw.lean`; the starting data are the expansions of `ρ`, `dRat ρ` and of
the polynomial coefficients `P, P', R` of `L_Z`, obtained from the polynomial cofactors
`P = X·(1 − 10X + 9X²)`, `P' = 1 − 20X + 27X²`, `R = −3 + 9X` with `Work.C17.lead2At_of_eq`.
-/

namespace Work.A14D

open Commons.FieldTheory.RatFunc

noncomputable section

local notation "algP" => algebraMap (Polynomial ℚ) (RatFunc ℚ)

/-! ## 0. Transport of `Exp2` along equalities -/

private theorem exp2_congr {f g : RatFunc ℚ} {e : ℤ} {l m : ℚ} (h : Work.C17.Exp2 f e l m)
    {e' : ℤ} {l' m' : ℚ} (hf : f = g) (he : e = e') (hl : l = l') (hm : m = m') :
    Work.C17.Exp2 g e' l' m' := by
  rw [hf, he, hl, hm] at h; exact h

/-! ## 1. The polynomial cofactors of `P, P', R` -/

/-- `P/X = 1 − 10X + 9X²`. -/
private def qZq : Polynomial ℚ := 1 - 10 * Polynomial.X + 9 * Polynomial.X ^ 2

private lemma pZq_eq_X_mul_qZq : pZq = Polynomial.X * qZq := by unfold qZq pZq; ring

private lemma qZq_sub : qZq - Polynomial.C (1 : ℚ) - Polynomial.C (-10) * Polynomial.X
    = Polynomial.X ^ 2 * Polynomial.C (9 : ℚ) := by
  unfold qZq
  simp only [map_neg (Polynomial.C), map_ofNat (Polynomial.C), map_one (Polynomial.C)]
  ring

private lemma pZq'_sub : pZq' - Polynomial.C (1 : ℚ) - Polynomial.C (-20) * Polynomial.X
    = Polynomial.X ^ 2 * Polynomial.C (27 : ℚ) := by
  unfold pZq'
  simp only [map_neg (Polynomial.C), map_ofNat (Polynomial.C), map_one (Polynomial.C)]
  ring

private lemma rZq_sub : rZq - Polynomial.C (-3) - Polynomial.C (9 : ℚ) * Polynomial.X
    = Polynomial.X ^ 2 * Polynomial.C (0 : ℚ) := by
  unfold rZq
  simp only [map_neg (Polynomial.C), map_ofNat (Polynomial.C), map_zero (Polynomial.C)]
  ring

/-! ## 2. The local data of `P, P', R` at `x = 0` -/

private theorem lead2_PZQ : Work.C17.Lead2At PZQ 1 1 (-10) := by
  have hPZ : PZQ = Work.C17.xQ * algP qZq := by
    rw [PZQ_eq, pZq_eq_X_mul_qZq, map_mul, Work.C17.xQ_eq_algP]
  have hcan : algP (Polynomial.X : Polynomial ℚ) * algP qZq
      * (algP (Polynomial.X : Polynomial ℚ))⁻¹ = algP qZq := by
    rw [mul_assoc, mul_comm (algP qZq) (algP (Polynomial.X : Polynomial ℚ))⁻¹,
      ← mul_assoc, mul_inv_cancel₀ (Work.C17.algP_ne_zero Polynomial.X_ne_zero), one_mul]
  refine Work.C17.lead2At_of_eq PZQ 1 1 (-10) (by norm_num)
    (g := algP (Polynomial.C (9 : ℚ))) (Work.C17.reg_algebraMap _) ?_
  rw [zpow_neg_one, hPZ, Work.C17.algQ_eq_algP (1 : ℚ), Work.C17.algQ_eq_algP (-10),
    Work.C17.xQ_eq_algP, hcan]
  simp only [← map_mul, ← map_sub, ← map_pow]
  rw [Work.C17.algP_inj_iff, qZq_sub]

private theorem lead2_PZQ' : Work.C17.Lead2At PZQ' 0 1 (-20) := by
  refine Work.C17.lead2At_of_eq PZQ' 0 1 (-20) (by norm_num)
    (g := algP (Polynomial.C (27 : ℚ))) (Work.C17.reg_algebraMap _) ?_
  simp only [neg_zero, zpow_zero, mul_one]
  rw [PZQ'_eq, Work.C17.algQ_eq_algP (1 : ℚ), Work.C17.algQ_eq_algP (-20),
    Work.C17.xQ_eq_algP]
  simp only [← map_mul, ← map_sub, ← map_pow]
  rw [Work.C17.algP_inj_iff, pZq'_sub]

private theorem lead2_RZQ : Work.C17.Lead2At RZQ 0 (-3) 9 := by
  refine Work.C17.lead2At_of_eq RZQ 0 (-3) 9 (by norm_num)
    (g := algP (Polynomial.C (0 : ℚ))) (Work.C17.reg_algebraMap _) ?_
  simp only [neg_zero, zpow_zero, mul_one]
  rw [RZQ_eq, Work.C17.algQ_eq_algP (-3), Work.C17.algQ_eq_algP (9 : ℚ),
    Work.C17.xQ_eq_algP]
  simp only [← map_mul, ← map_sub, ← map_pow]
  rw [Work.C17.algP_inj_iff, rZq_sub]

private theorem lead2_PZQ_inv : Work.C17.Lead2At PZQ⁻¹ (-1) 1 10 := by
  refine Work.C17.Exp2.to_Lead2At ?_ (by norm_num)
  exact exp2_congr (Work.C17.exp2_inv (lead2_PZQ.to_exp2) (by norm_num : (1 : ℚ) ≠ 0))
    rfl (by norm_num) (by simp) (by norm_num)

/-! ## 3. The local data of `ρ = 1/y'` at `x = 0` -/

private theorem exp2_rhos : Work.C17.Exp2 rhos (-1) (-1 / 2) (3 / 4) :=
  Work.C17.lead2_rhoQ.to_exp2

private theorem exp2_dRat_rhos : Work.C17.Exp2 (Submission.CDT.dRat rhos) (-2) (1 / 2) 0 :=
  Work.C17.lead2_dRat_rhoQ.to_exp2

/-! ## 4. The chain of expansions

Each step below is `Exp2 f e l m ↦ Exp2 (dRat f) (e−1) (e·l) ((e+1)·m)` (`exp2_dRat`),
`Exp2 f e l m, Exp2 g e' l' m' ↦ Exp2 (f·g) (e+e') (l·l') (m·l' + l·m')` (`exp2_mul`),
inversion `exp2_inv`, addition/subtraction/negation, and the shift `exp2.shift`. -/

/-- `u2 = −ρ·(ρ·R/P) = x^{-3}(3/4 + 3x + O(x²))`. -/
private theorem exp2_u2 : Work.C17.Exp2 u2 (-3) (3 / 4) 3 := by
  have hρ : Work.C17.Exp2 rhos (-1) (-1 / 2) (3 / 4) := exp2_rhos
  have hR : Work.C17.Exp2 RZQ 0 (-3) 9 := lead2_RZQ.to_exp2
  have hPi : Work.C17.Exp2 PZQ⁻¹ (-1) 1 10 := lead2_PZQ_inv.to_exp2
  have h1 : Work.C17.Exp2 (rhos * RZQ) (-1) (3 / 2) (-27 / 4) :=
    exp2_congr (Work.C17.exp2_mul hρ hR) rfl (by ring) (by ring) (by ring)
  have h2 : Work.C17.Exp2 ((rhos * RZQ) * PZQ⁻¹) (-2) (3 / 2) (33 / 4) :=
    exp2_congr (Work.C17.exp2_mul h1 hPi) rfl (by ring) (by ring) (by ring)
  have h3 : Work.C17.Exp2 (rhos * ((rhos * RZQ) * PZQ⁻¹)) (-3) (-3 / 4) (-3) :=
    exp2_congr (Work.C17.exp2_mul hρ h2) rfl (by ring) (by ring) (by ring)
  exact exp2_congr (Work.C17.Exp2.neg h3) (by rw [u2, div_eq_mul_inv]) (by ring)
    (by ring) (by ring)

/-- `w2 = dRat ρ − ρ·P'/P = x^{-2}(1 − 23x/4 + O(x²))`. -/
private theorem exp2_w2 : Work.C17.Exp2 w2 (-2) 1 (-23 / 4) := by
  have hρ : Work.C17.Exp2 rhos (-1) (-1 / 2) (3 / 4) := exp2_rhos
  have hρ' : Work.C17.Exp2 (Submission.CDT.dRat rhos) (-2) (1 / 2) 0 := exp2_dRat_rhos
  have hP' : Work.C17.Exp2 PZQ' 0 1 (-20) := lead2_PZQ'.to_exp2
  have hPi : Work.C17.Exp2 PZQ⁻¹ (-1) 1 10 := lead2_PZQ_inv.to_exp2
  have h1 : Work.C17.Exp2 (rhos * PZQ') (-1) (-1 / 2) (43 / 4) :=
    exp2_congr (Work.C17.exp2_mul hρ hP') rfl (by ring) (by ring) (by ring)
  have h2 : Work.C17.Exp2 ((rhos * PZQ') * PZQ⁻¹) (-2) (-1 / 2) (23 / 4) :=
    exp2_congr (Work.C17.exp2_mul h1 hPi) rfl (by ring) (by ring) (by ring)
  have h3 : Work.C17.Exp2 (Submission.CDT.dRat rhos - (rhos * PZQ') * PZQ⁻¹)
      (-2) 1 (-23 / 4) :=
    exp2_congr (Work.C17.Exp2.sub hρ' h2) rfl (by ring) (by ring) (by ring)
  exact exp2_congr h3 (by rw [w2, div_eq_mul_inv]) (by ring) (by ring) (by ring)

/-- `v2 = ρ·w2 = x^{-3}(−1/2 + 29x/8 + O(x²))`. -/
private theorem exp2_v2 : Work.C17.Exp2 v2 (-3) (-1 / 2) (29 / 8) := by
  have hρ : Work.C17.Exp2 rhos (-1) (-1 / 2) (3 / 4) := exp2_rhos
  have hw2 : Work.C17.Exp2 w2 (-2) 1 (-23 / 4) := exp2_w2
  exact exp2_congr (Work.C17.exp2_mul hρ hw2) (by rw [v2]) (by ring) (by ring) (by ring)

/-- `u3 = ρ·(dRat u2 − v2·R/P) = x^{-5}(15/8 + O(x²))`. -/
private theorem exp2_u3 : Work.C17.Exp2 u3 (-5) (15 / 8) 0 := by
  have hρ : Work.C17.Exp2 rhos (-1) (-1 / 2) (3 / 4) := exp2_rhos
  have hu2 : Work.C17.Exp2 u2 (-3) (3 / 4) 3 := exp2_u2
  have hv2 : Work.C17.Exp2 v2 (-3) (-1 / 2) (29 / 8) := exp2_v2
  have hR : Work.C17.Exp2 RZQ 0 (-3) 9 := lead2_RZQ.to_exp2
  have hPi : Work.C17.Exp2 PZQ⁻¹ (-1) 1 10 := lead2_PZQ_inv.to_exp2
  have hdU2 : Work.C17.Exp2 (Submission.CDT.dRat u2) (-4) (-9 / 4) (-6) :=
    exp2_congr (Work.C17.exp2_dRat hu2) rfl (by ring) (by ring) (by ring)
  have h1 : Work.C17.Exp2 (v2 * RZQ) (-3) (3 / 2) (-123 / 8) :=
    exp2_congr (Work.C17.exp2_mul hv2 hR) rfl (by ring) (by ring) (by ring)
  have h2 : Work.C17.Exp2 ((v2 * RZQ) * PZQ⁻¹) (-4) (3 / 2) (-3 / 8) :=
    exp2_congr (Work.C17.exp2_mul h1 hPi) rfl (by ring) (by ring) (by ring)
  have h3 : Work.C17.Exp2 (Submission.CDT.dRat u2 - (v2 * RZQ) * PZQ⁻¹)
      (-4) (-15 / 4) (-45 / 8) :=
    exp2_congr (Work.C17.Exp2.sub hdU2 h2) rfl (by ring) (by ring) (by ring)
  have h4 : Work.C17.Exp2 (rhos * (Submission.CDT.dRat u2 - (v2 * RZQ) * PZQ⁻¹))
      (-5) (15 / 8) 0 :=
    exp2_congr (Work.C17.exp2_mul hρ h3) rfl (by ring) (by ring) (by ring)
  exact exp2_congr h4 (by rw [u3, div_eq_mul_inv]) (by ring) (by ring) (by ring)

/-- `w3 = u2 + dRat v2 − v2·P'/P = x^{-4}(2 − 121x/8 + O(x²))`. -/
private theorem exp2_w3 : Work.C17.Exp2 w3 (-4) 2 (-121 / 8) := by
  have hu2 : Work.C17.Exp2 u2 (-3) (3 / 4) 3 := exp2_u2
  have hv2 : Work.C17.Exp2 v2 (-3) (-1 / 2) (29 / 8) := exp2_v2
  have hP' : Work.C17.Exp2 PZQ' 0 1 (-20) := lead2_PZQ'.to_exp2
  have hPi : Work.C17.Exp2 PZQ⁻¹ (-1) 1 10 := lead2_PZQ_inv.to_exp2
  have hdV2 : Work.C17.Exp2 (Submission.CDT.dRat v2) (-4) (3 / 2) (-29 / 4) :=
    exp2_congr (Work.C17.exp2_dRat hv2) rfl (by ring) (by ring) (by ring)
  have h1 : Work.C17.Exp2 (v2 * PZQ') (-3) (-1 / 2) (109 / 8) :=
    exp2_congr (Work.C17.exp2_mul hv2 hP') rfl (by ring) (by ring) (by ring)
  have h2 : Work.C17.Exp2 ((v2 * PZQ') * PZQ⁻¹) (-4) (-1 / 2) (69 / 8) :=
    exp2_congr (Work.C17.exp2_mul h1 hPi) rfl (by ring) (by ring) (by ring)
  have h3 : Work.C17.Exp2 (Submission.CDT.dRat v2 - (v2 * PZQ') * PZQ⁻¹)
      (-4) 2 (-127 / 8) :=
    exp2_congr (Work.C17.Exp2.sub hdV2 h2) rfl (by ring) (by ring) (by ring)
  have h4 : Work.C17.Exp2 u2 (-4) 0 (3 / 4) :=
    exp2_congr (Work.C17.Exp2.shift hu2) rfl (by ring) (by ring) (by ring)
  have h5 : Work.C17.Exp2 (u2 + (Submission.CDT.dRat v2 - (v2 * PZQ') * PZQ⁻¹))
      (-4) 2 (-121 / 8) :=
    exp2_congr (Work.C17.Exp2.add h4 h3) rfl (by ring) (by ring) (by ring)
  exact exp2_congr h5 (by rw [w3, div_eq_mul_inv]; ring) (by ring) (by ring) (by ring)

theorem local_A14 :
    Work.C17.Lead2At Work.A14D.u2 (-3) (3 / 4) 3 ∧
    Work.C17.Lead2At Work.A14D.w2 (-2) 1 (-23 / 4) ∧
    Work.C17.Lead2At Work.A14D.u3 (-5) (15 / 8) 0 ∧
    Work.C17.Lead2At Work.A14D.w3 (-4) 2 (-121 / 8) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact exp2_u2.to_Lead2At (by norm_num)
  · exact exp2_w2.to_Lead2At (by norm_num)
  · exact exp2_u3.to_Lead2At (by norm_num)
  · exact exp2_w3.to_Lead2At (by norm_num)

end

end Work.A14D
