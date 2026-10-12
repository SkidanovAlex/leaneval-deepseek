import ChallengeDeps
import Submission.Work.BoseFixR.All.epsFar_le_inv_eight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixR.All

open Work.BoseBox

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `farTauArith`: the `τ`-arithmetic of FS §9's far leg

At the admissible box data (`Work.BoseBoxFix.Adm`, diluteness `t = μa³ ≤ ε₀ ≤ 10^{-4000}`)
and at any density `ρ` with `μ ≤ 10ρ`, the two slot scales of the smoothed kinetic symbol
`tauSm` of the far leg — `c₁ = (2sℓ)^{-1}` and `c₂ = (2dsℓ)^{-1}` with
`s = X`, `d = X⁶`, `ℓ = A X^{-163}`, `X = (μA³)^{1/323}` — satisfy the two bounds

  `4·((2dsℓ)^{-1})² ≤ ρA·ε^{-1/2}`  and
  `8·((1-ε_T)(2sℓ)^{-1} + ε_T(2dsℓ)^{-1})² ≤ 100√ε·(ρA·ε^{-1/2})`,

with `ε = epsFar v μ ρ = √(𝓜/((ρ+μ)ℓ³))`.

Both are monomial comparisons in `X`: the left sides are `X^{312}/A²` and
`(2/A²)·B²` with `B = (1-ε_T)X^{162} + ε_T X^{156} ≤ 2X^{647/4}`, while the right side is
`ρA·X^{-337/16} ≥ X^{4831/16}/(10A²)` (and `100ρA ≥ 10X^{323}/A²` for the second).  The only
non-trivial numeric input is `10·X^{161/16} ≤ 1`, which follows from
`X^{161/16} ≤ t^{161/5168} ≤ 10^{-4000·161/5168} ≤ 1/10`.
-/

/-- The numeric core: `10·t^{161/5168} ≤ 1` for `0 < t ≤ 10^{-4000}`. -/
private lemma ten_mul_rpow_le_one {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ (10 : ℝ) ^ (-(4000 : ℤ))) : 10 * t ^ (161 / 5168 : ℝ) ≤ 1 := by
  have hmono : t ^ (161 / 5168 : ℝ) ≤ ((10 : ℝ) ^ (-(4000 : ℤ))) ^ (161 / 5168 : ℝ) :=
    Real.rpow_le_rpow ht0.le ht (by norm_num)
  have h4000 : ((10 : ℝ) ^ (-(4000 : ℤ))) ^ (161 / 5168 : ℝ)
      = (10 : ℝ) ^ (((-4000 : ℤ) : ℝ) * (161 / 5168 : ℝ)) := by
    rw [show (10 : ℝ) ^ (-(4000 : ℤ)) = (10 : ℝ) ^ (((-4000 : ℤ) : ℝ)) from
      (Real.rpow_intCast 10 (-4000)).symm]
    exact (Real.rpow_mul (x := 10) (by norm_num) (((-4000 : ℤ) : ℝ)) (161 / 5168 : ℝ)).symm
  have hstep : (10 : ℝ) ^ (((-4000 : ℤ) : ℝ) * (161 / 5168 : ℝ)) ≤ (10 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hmain : t ^ (161 / 5168 : ℝ) ≤ 1 / 10 := by
    refine le_trans (le_trans hmono (le_of_eq h4000)) (le_trans hstep (le_of_eq ?_))
    rw [Real.rpow_neg_one]
    norm_num
  linarith

theorem farTauArith {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < BoseGases.a v)
    {ε₀ μ : ℝ}
    (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ))) (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρm : μ ≤ 10 * ρ) :
    4 * ((2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s * Work.BoseFixR.ell v μ)⁻¹) ^ 2
        ≤ ρ * BoseGases.a v * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ))
    ∧ 8 * ((1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT)
            * (2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s * Work.BoseFixR.ell v μ)⁻¹
          + (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
            * (2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s * Work.BoseFixR.ell v μ)⁻¹) ^ 2
        ≤ 100 * Real.sqrt (Work.BoseFixR.All.epsFar v μ ρ)
            * (ρ * BoseGases.a v * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ))) := by
  set A : ℝ := BoseGases.a v with hAdef
  set t : ℝ := μ * A ^ 3 with htdef
  set eT : ℝ := (Work.BoseBox.paramsAt μ A).eT with heTdef
  have hA : 0 < A := by rw [hAdef]; exact hav
  have hμ : 0 < μ := hAdm.1
  have ht0 : 0 < t := by rw [htdef]; positivity
  have htle : t ≤ (10 : ℝ) ^ (-(4000 : ℤ)) := by
    rw [htdef]; exact le_trans hAdm.2.1 hε₀
  have ht1 : t ≤ 1 := le_trans htle (by
    rw [show (10 : ℝ) ^ (-(4000 : ℤ)) = 1 / 10 ^ 4000 by norm_num, one_div]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10)))
  set X : ℝ := fsXp t 1 with hXdef
  have hX0 : 0 < X := by rw [hXdef]; exact fsXp_pos ht0
  have hX1 : X ≤ 1 := by rw [hXdef]; exact fsXp_le_one ht0 ht1 (by norm_num)
  have hXc : ∀ c : ℝ, X ^ c = fsXp t c := by
    intro c
    rw [hXdef, fsXp_rpow ht0.le, one_mul]
  have hnegX : ∀ c : ℝ, fsXp t (-c) = (X ^ c)⁻¹ := by
    intro c
    have h1 : fsXp t (-c) = (fsXp t c)⁻¹ := by
      rw [← hXc (-c), ← hXc c, Real.rpow_neg hX0.le]
    rw [h1, hXc c]
  have hfs : ∀ c e : ℝ, fsXp t (c + e) = fsXp t c * fsXp t e :=
    fun c e => (fsXp_mul ht0 c e).symm
  have htX : t = X ^ (323 : ℝ) := by
    rw [hXc 323]; exact (Work.BoseFixB1.fsXp_323 t).symm
  have hXnum : 10 * X ^ (161 / 16 : ℝ) ≤ 1 := by
    have hb : X ^ (161 / 16 : ℝ) = t ^ (161 / 5168 : ℝ) := by
      rw [hXdef, fsXp_rpow ht0.le, one_mul, fsXp]
      norm_num
    rw [hb]
    exact ten_mul_rpow_le_one ht0 htle
  have hell : Work.BoseFixR.ell v μ = A * fsXp t (-163) := by
    rw [Work.BoseFixR.ell]
    exact Work.BoseFixB1.sideAt_eq_fsXp hA hμ
  have hℓ0 : 0 < Work.BoseFixR.ell v μ := by
    rw [hell]; exact mul_pos hA (fsXp_pos ht0)
  have hbigM : Work.BoseFixR.bigMV v μ
      = X ^ (337 / 4 : ℝ) * (μ * Work.BoseFixR.ell v μ ^ 3) :=
    Work.BoseFixR.BigMVRatio hav hμ
  have hbigM0 : 0 < Work.BoseFixR.bigMV v μ := by
    rw [hbigM]
    exact mul_pos (Real.rpow_pos_of_pos hX0 _) (mul_pos hμ (pow_pos hℓ0 3))
  have hden0 : 0 < (ρ + μ) * Work.BoseFixR.ell v μ ^ 3 :=
    mul_pos (by linarith) (pow_pos hℓ0 3)
  set Zf : ℝ := Work.BoseFixR.All.epsFar v μ ρ with hZfdef
  set u : ℝ := Work.BoseFixR.bigMV v μ / ((ρ + μ) * Work.BoseFixR.ell v μ ^ 3) with hudef
  have hu0 : 0 < u := by rw [hudef]; exact div_pos hbigM0 hden0
  have hu_le : u ≤ X ^ (337 / 4 : ℝ) := by
    rw [hudef, hbigM, div_le_iff₀ hden0]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by linarith : μ ≤ ρ + μ) (pow_pos hℓ0 3).le)
      (Real.rpow_nonneg hX0.le _)
  have hZf0 : 0 < Zf := by
    rw [hZfdef, Work.BoseFixR.All.epsFar]
    exact Real.sqrt_pos.mpr hu0
  have hZf_eq : Zf = Real.sqrt u := by
    rw [hZfdef, Work.BoseFixR.All.epsFar, hudef]
  have hZf_lb : X ^ (-(337 / 16) : ℝ) ≤ Zf ^ (-(1 / 2) : ℝ) := by
    have h1 : Zf ^ (-(1 / 2) : ℝ) = u ^ (-(1 / 4) : ℝ) := by
      rw [hZf_eq, Real.sqrt_eq_rpow, ← Real.rpow_mul hu0.le (1 / 2) (-(1 / 2))]
      norm_num
    rw [h1]
    have h2 : (X ^ (337 / 4 : ℝ)) ^ (-(1 / 4) : ℝ) ≤ u ^ (-(1 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hu0 hu_le (by norm_num)
    calc X ^ (-(337 / 16) : ℝ) = (X ^ (337 / 4 : ℝ)) ^ (-(1 / 4) : ℝ) := by
          rw [← Real.rpow_mul hX0.le (337 / 4) (-(1 / 4))]
          norm_num
      _ ≤ u ^ (-(1 / 4) : ℝ) := h2
  -- the closed forms of the two slot scales
  have hdsl : 2 * (Work.BoseBox.paramsAt μ A).d * (Work.BoseBox.paramsAt μ A).s
      * Work.BoseFixR.ell v μ = 2 * A * fsXp t (-156) := by
    have hd : (Work.BoseBox.paramsAt μ A).d = fsXp t 6 := rfl
    have hs : (Work.BoseBox.paramsAt μ A).s = fsXp t 1 := rfl
    rw [hd, hs, hell]
    calc 2 * fsXp t 6 * fsXp t 1 * (A * fsXp t (-163))
        = 2 * A * (fsXp t 6 * fsXp t 1 * fsXp t (-163)) := by ring
      _ = 2 * A * fsXp t (-156) := by
            rw [← hfs 6 1, ← hfs (6 + 1) (-163),
              show (6 : ℝ) + 1 + (-163) = -156 by norm_num]
  have h1sl : 2 * (Work.BoseBox.paramsAt μ A).s * Work.BoseFixR.ell v μ
      = 2 * A * fsXp t (-162) := by
    have hs : (Work.BoseBox.paramsAt μ A).s = fsXp t 1 := rfl
    rw [hs, hell]
    calc 2 * fsXp t 1 * (A * fsXp t (-163))
        = 2 * A * (fsXp t 1 * fsXp t (-163)) := by ring
      _ = 2 * A * fsXp t (-162) := by
            rw [← hfs 1 (-163), show (1 : ℝ) + (-163) = -162 by norm_num]
  have hc2 : (2 * (Work.BoseBox.paramsAt μ A).d * (Work.BoseBox.paramsAt μ A).s
      * Work.BoseFixR.ell v μ)⁻¹ = X ^ (156 : ℝ) / (2 * A) := by
    rw [hdsl, hnegX 156]
    rw [show (2 * A * (X ^ (156 : ℝ))⁻¹)⁻¹ = X ^ (156 : ℝ) / (2 * A) from by
      rw [mul_inv, inv_inv, div_eq_mul_inv]; ring]
  have hc1 : (2 * (Work.BoseBox.paramsAt μ A).s * Work.BoseFixR.ell v μ)⁻¹
      = X ^ (162 : ℝ) / (2 * A) := by
    rw [h1sl, hnegX 162]
    rw [show (2 * A * (X ^ (162 : ℝ))⁻¹)⁻¹ = X ^ (162 : ℝ) / (2 * A) from by
      rw [mul_inv, inv_inv, div_eq_mul_inv]; ring]
  -- ## Goal 1
  have hLHS1 : 4 * ((2 * (Work.BoseBox.paramsAt μ A).d * (Work.BoseBox.paramsAt μ A).s
      * Work.BoseFixR.ell v μ)⁻¹) ^ 2 = X ^ (312 : ℝ) / A ^ 2 := by
    rw [hdsl, hnegX 156]
    have hinv : (2 * A * (X ^ (156 : ℝ))⁻¹)⁻¹ = X ^ (156 : ℝ) / (2 * A) := by
      rw [mul_inv, inv_inv, div_eq_mul_inv]; ring
    rw [hinv]
    have hX312 : X ^ (312 : ℝ) = (X ^ (156 : ℝ)) ^ 2 := by
      rw [← Real.rpow_mul_natCast hX0.le (156 : ℝ) 2]
      norm_num
    rw [hX312]
    ring
  have hμA : μ * A = X ^ (323 : ℝ) / A ^ 2 := by
    have h1 : μ * A ^ 3 = X ^ (323 : ℝ) := by rw [← htdef]; exact htX
    rw [eq_div_iff (by positivity : (A : ℝ) ^ 2 ≠ 0)]
    rw [← h1]; ring
  have hcomb : (X ^ (323 : ℝ) / (10 * A ^ 2)) * X ^ (-(337 / 16) : ℝ)
      = X ^ (4831 / 16 : ℝ) / (10 * A ^ 2) := by
    rw [div_mul_eq_mul_div, ← Real.rpow_add hX0]
    norm_num
  have hRHS1 : X ^ (4831 / 16 : ℝ) / (10 * A ^ 2) ≤ ρ * A * Zf ^ (-(1 / 2) : ℝ) := by
    have hρA : μ * A / 10 ≤ ρ * A := by
      have h1 : μ / 10 ≤ ρ := by linarith
      calc μ * A / 10 = (μ / 10) * A := by ring
        _ ≤ ρ * A := mul_le_mul_of_nonneg_right h1 hA.le
    have hXR : 0 ≤ X ^ (-(337 / 16) : ℝ) := Real.rpow_nonneg hX0.le _
    have hstep2 : (μ * A / 10) * X ^ (-(337 / 16) : ℝ)
        ≤ ρ * A * X ^ (-(337 / 16) : ℝ) := mul_le_mul_of_nonneg_right hρA hXR
    have hstep1 : ρ * A * X ^ (-(337 / 16) : ℝ) ≤ ρ * A * Zf ^ (-(1 / 2) : ℝ) :=
      mul_le_mul_of_nonneg_left hZf_lb (by positivity)
    calc X ^ (4831 / 16 : ℝ) / (10 * A ^ 2)
        = (μ * A / 10) * X ^ (-(337 / 16) : ℝ) := by
          rw [hμA, div_div, show A ^ 2 * 10 = 10 * A ^ 2 by ring]
          exact hcomb.symm
      _ ≤ ρ * A * X ^ (-(337 / 16) : ℝ) := hstep2
      _ ≤ ρ * A * Zf ^ (-(1 / 2) : ℝ) := hstep1
  have hexp : 10 ≤ X ^ (-(161 / 16) : ℝ) := by
    have hY0 : 0 < X ^ (161 / 16 : ℝ) := Real.rpow_pos_of_pos hX0 _
    have h10 : 10 ≤ (X ^ (161 / 16 : ℝ))⁻¹ := by
      calc (10 : ℝ) = (10 * X ^ (161 / 16 : ℝ)) * (X ^ (161 / 16 : ℝ))⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hY0), mul_one]
        _ ≤ 1 * (X ^ (161 / 16 : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right hXnum (inv_nonneg.mpr hY0.le)
        _ = (X ^ (161 / 16 : ℝ))⁻¹ := one_mul _
    rwa [Real.rpow_neg hX0.le]
  have hkey1 : 10 * X ^ (312 : ℝ) ≤ X ^ (4831 / 16 : ℝ) := by
    have hX312 : X ^ (4831 / 16 : ℝ) = X ^ (312 : ℝ) * X ^ (-(161 / 16) : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    rw [hX312]
    calc 10 * X ^ (312 : ℝ) = X ^ (312 : ℝ) * 10 := by ring
      _ ≤ X ^ (312 : ℝ) * X ^ (-(161 / 16) : ℝ) :=
          mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hX0.le _)
  have hfin1 : X ^ (312 : ℝ) / A ^ 2 ≤ X ^ (4831 / 16 : ℝ) / (10 * A ^ 2) := by
    have hA2 : 0 < A ^ 2 := by positivity
    have h2 : 10 * X ^ (312 : ℝ) * A ^ 2 ≤ X ^ (4831 / 16 : ℝ) * A ^ 2 :=
      mul_le_mul_of_nonneg_right hkey1 hA2.le
    rw [div_le_div_iff₀ hA2 (by positivity : (0 : ℝ) < 10 * A ^ 2)]
    linarith
  -- ## Goal 2
  have heT : eT = X ^ (23 / 4 : ℝ) := by
    rw [heTdef]
    show fsXp (μ * A ^ 3) (23 / 4) = X ^ (23 / 4 : ℝ)
    rw [← htdef, ← hXc (23 / 4)]
  have hsq : Real.sqrt Zf * Zf ^ (-(1 / 2) : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hZf0]
    rw [show (1 : ℝ) / 2 + -(1 / 2) = 0 by norm_num, Real.rpow_zero]
  have hB0 : 0 ≤ (1 - eT) * X ^ (162 : ℝ)
      + eT * X ^ (156 : ℝ) := by
    have h1 : 0 ≤ 1 - eT := by
      have : eT ≤ 1 := by rw [heT]; exact Real.rpow_le_one hX0.le hX1 (by norm_num)
      linarith
    have h2 : 0 ≤ eT := by
      rw [heT]; exact Real.rpow_nonneg hX0.le _
    exact add_nonneg (mul_nonneg h1 (Real.rpow_nonneg hX0.le _))
      (mul_nonneg h2 (Real.rpow_nonneg hX0.le _))
  have hB : (1 - eT) * X ^ (162 : ℝ)
      + eT * X ^ (156 : ℝ) ≤ 2 * X ^ (647 / 4 : ℝ) := by
    have h6 : X ^ (162 : ℝ) ≤ X ^ (23 / 4 : ℝ) * X ^ (156 : ℝ) := by
      rw [← Real.rpow_add hX0]
      exact Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by norm_num)
    have hV : X ^ (23 / 4 : ℝ) * X ^ (156 : ℝ) = X ^ (647 / 4 : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    have h2 : eT * X ^ (156 : ℝ)
        = X ^ (23 / 4 : ℝ) * X ^ (156 : ℝ) := by rw [heT]
    have heTle : eT ≤ 1 := by rw [heT]; exact Real.rpow_le_one hX0.le hX1 (by norm_num)
    have h3 : (1 - eT) * X ^ (162 : ℝ)
        ≤ X ^ (23 / 4 : ℝ) * X ^ (156 : ℝ) := by
      have heT0 : 0 ≤ eT := by rw [heT]; exact Real.rpow_nonneg hX0.le _
      calc (1 - eT) * X ^ (162 : ℝ)
          ≤ 1 * X ^ (162 : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hX0.le _)
        _ = X ^ (162 : ℝ) := one_mul _
        _ ≤ X ^ (23 / 4 : ℝ) * X ^ (156 : ℝ) := h6
    calc (1 - eT) * X ^ (162 : ℝ)
          + eT * X ^ (156 : ℝ)
        ≤ X ^ (23 / 4 : ℝ) * X ^ (156 : ℝ) + X ^ (23 / 4 : ℝ) * X ^ (156 : ℝ) := by
          rw [h2]; linarith
      _ = 2 * X ^ (647 / 4 : ℝ) := by rw [hV]; ring
  have hLHS2 : 8 * ((1 - eT)
        * (2 * (Work.BoseBox.paramsAt μ A).s * Work.BoseFixR.ell v μ)⁻¹
      + eT
        * (2 * (Work.BoseBox.paramsAt μ A).d * (Work.BoseBox.paramsAt μ A).s
          * Work.BoseFixR.ell v μ)⁻¹) ^ 2 ≤ 8 * X ^ (647 / 2 : ℝ) / A ^ 2 := by
    rw [hc1, hc2]
    have hfac : (1 - eT) * (X ^ (162 : ℝ) / (2 * A))
          + eT * (X ^ (156 : ℝ) / (2 * A))
        = ((1 - eT) * X ^ (162 : ℝ)
            + eT * X ^ (156 : ℝ)) / (2 * A) := by
      ring
    rw [hfac]
    have h2 : 8 * (((1 - eT) * X ^ (162 : ℝ)
          + eT * X ^ (156 : ℝ)) / (2 * A)) ^ 2
        = 2 * ((1 - eT) * X ^ (162 : ℝ)
            + eT * X ^ (156 : ℝ)) ^ 2 / A ^ 2 := by
      ring
    rw [h2]
    have hBsq : ((1 - eT) * X ^ (162 : ℝ)
        + eT * X ^ (156 : ℝ)) ^ 2
        ≤ (2 * X ^ (647 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hB0 hB 2
    have h4 : (2 * X ^ (647 / 4 : ℝ)) ^ 2 = 4 * X ^ (647 / 2 : ℝ) := by
      rw [mul_pow, show (X ^ (647 / 4 : ℝ)) ^ 2 = X ^ (647 / 2 : ℝ) from by
        rw [← Real.rpow_mul_natCast hX0.le (647 / 4 : ℝ) 2]; norm_num]
      norm_num
    rw [h4] at hBsq
    have hA2 : 0 < A ^ 2 := by positivity
    calc 2 * ((1 - eT) * X ^ (162 : ℝ)
            + eT * X ^ (156 : ℝ)) ^ 2 / A ^ 2
        ≤ 2 * (4 * X ^ (647 / 2 : ℝ)) / A ^ 2 := by
          apply div_le_div_of_nonneg_right _ hA2.le
          linarith [hBsq]
      _ = 8 * X ^ (647 / 2 : ℝ) / A ^ 2 := by ring
  have hfinal2 : 8 * X ^ (647 / 2 : ℝ) / A ^ 2 ≤ 100 * ρ * A := by
    have h323 : X ^ (647 / 2 : ℝ) = X ^ (323 : ℝ) * X ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    have hXhalf : X ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hX0.le hX1 (by norm_num)
    have hkey : 8 * X ^ (647 / 2 : ℝ) ≤ 10 * X ^ (323 : ℝ) := by
      have hpx : 0 < X ^ (323 : ℝ) := Real.rpow_pos_of_pos hX0 _
      rw [h323]
      calc 8 * (X ^ (323 : ℝ) * X ^ (1 / 2 : ℝ))
          = (8 * X ^ (1 / 2 : ℝ)) * X ^ (323 : ℝ) := by ring
        _ ≤ (8 * 1) * X ^ (323 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hpx.le
            linarith
        _ ≤ 10 * X ^ (323 : ℝ) := by linarith
    have h10 : 10 * X ^ (323 : ℝ) / A ^ 2 = 10 * (μ * A) := by
      rw [mul_div_assoc, ← hμA]
    have hlow : 10 * X ^ (323 : ℝ) / A ^ 2 ≤ 100 * ρ * A := by
      rw [h10]
      have h1 : 10 * μ ≤ 100 * ρ := by linarith
      have := mul_le_mul_of_nonneg_right h1 hA.le
      linarith
    calc 8 * X ^ (647 / 2 : ℝ) / A ^ 2 ≤ 10 * X ^ (323 : ℝ) / A ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ A ^ 2)
          exact hkey
      _ ≤ 100 * ρ * A := hlow
  have hRHS2 : 100 * Real.sqrt Zf * (ρ * A * Zf ^ (-(1 / 2) : ℝ)) = 100 * ρ * A := by
    calc 100 * Real.sqrt Zf * (ρ * A * Zf ^ (-(1 / 2) : ℝ))
        = 100 * (ρ * A) * (Real.sqrt Zf * Zf ^ (-(1 / 2) : ℝ)) := by ring
      _ = 100 * (ρ * A) * 1 := by rw [hsq]
      _ = 100 * ρ * A := by ring
  refine ⟨?_, ?_⟩
  · rw [hLHS1]; exact le_trans hfin1 hRHS1
  · rw [hRHS2]; exact le_trans hLHS2 hfinal2

end Work.BoseFixR.All
