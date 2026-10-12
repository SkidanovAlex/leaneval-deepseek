import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseRowQ2.rowGchiMaskRow_honest
import Submission.Work.BoseRowQ2.rowMain_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.rowArith2_honest` — the second arithmetic row of FS l.3253–3257, proved

`RowsN.lean`'s `ArithAt2` is the `ε`-bookkeeping of FS l.3253–3257 for the *corrected*
`GchiAtN` row: `2ρŴ₁ω(0)(1+1/ε)(C₁/κ_lat)² ≤ (b/800)ℓ⁻²`.

At the honest data, `κ_lat = honCutRad v μ = ℓ·κ` with `κ = (K_ℓd²)^{-1}√(μa)`, so

    ℓκ = (K_ℓ(μa)^{-1/2})·(K_ℓd²)^{-1}(μa)^{1/2} = d^{-2},   i.e.  (1/κ_lat)² = d⁴,

while `ℓ⁻² = (μa)K_ℓ⁻²` (`K_ℓ² = t^{-3/323}`, `d⁴ = t^{24/323}`, `t = μa³`) and
`ε = fsEps v 58982400 μ = 58982400·t^{13/1292}`.  Dividing the row by `μa` and clearing
`K_ℓ²`, the whole row is therefore the purely absolute inequality

    `48πC₁²·t^{21/323}·(1 + 1/(58982400 t^{13/1292})) ≤ b/800 = 1/12800`,

using `ρ ≤ 3μ/2` (`AdmRho`) and `Ŵ₁ω(0) ≤ 16πa` (`honE_W1omega0_row`).  The left side is a sum
of two powers with *positive* exponents (`t^{84/1292}` and `t^{71/1292}/58982400`), so it tends
to `0` with `t`: the row holds for every fixed `C₁` below an explicit threshold, and the
diluteness threshold produced here is

    `εg' = min εg (min 1 (1/(25600·48π(1+C₁²)))³²)`.

All rpow algebra is isolated in the pure-real helper lemmas `ra2_*` below.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS Work.BoseRowsFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Pure-real arithmetic helpers -/

/-- `(x^c)^n = x^{c·n}` for `0 ≤ x`. -/
private lemma ra2_rpow_nat_mul {x : ℝ} (hx : 0 ≤ x) (c : ℝ) (n : ℕ) :
    (x ^ c) ^ n = x ^ (c * n) := by
  rw [← Real.rpow_natCast (x ^ c) n, Real.rpow_mul hx]

/-- `y^{-1/2}·y^{1/2} = 1` for `0 < y`. -/
private lemma ra2_rpow_half {y : ℝ} (hy : 0 < y) :
    y ^ (-(1 / 2 : ℝ)) * y ^ (1 / 2 : ℝ) = 1 := by
  rw [← Real.rpow_add hy, show -(1 / 2 : ℝ) + 1 / 2 = 0 by norm_num, Real.rpow_zero]

/-- The `ε`-identity: `ε_T^{-1}(dK_ℓ)² = (μa³)^{13/1292}` at the honest parameters. -/
private lemma ra2_eps_key {t : ℝ} (ht : 0 < t) :
    58982400 * (t ^ (23 / 1292 : ℝ))⁻¹ * (t ^ (6 / 323 : ℝ) * t ^ (-(3 / 646) : ℝ)) ^ 2
      = 58982400 * t ^ (13 / 1292 : ℝ) := by
  rw [mul_assoc, ← Real.rpow_neg ht.le, ← Real.rpow_add ht, ra2_rpow_nat_mul ht.le,
    ← Real.rpow_add ht]
  rw [show -(23 / 1292 : ℝ) + (6 / 323 + -(3 / 646)) * ↑(2 : ℕ) = 13 / 1292 by norm_num]

/-- `t^{21/323}/(58982400 t^{13/1292}) = t^{71/1292}/58982400`. -/
private lemma ra2_div_key {t : ℝ} (ht : 0 < t) :
    t ^ (21 / 323 : ℝ) / (58982400 * t ^ (13 / 1292 : ℝ)) = t ^ (71 / 1292 : ℝ) / 58982400 := by
  have hb : t ^ (13 / 1292 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  have hc : (58982400 : ℝ) ≠ 0 := by norm_num
  rw [div_eq_div_iff (mul_ne_zero hc hb) hc]
  have e : t ^ (71 / 1292 : ℝ) * (58982400 * t ^ (13 / 1292 : ℝ))
      = 58982400 * (t ^ (71 / 1292 : ℝ) * t ^ (13 / 1292 : ℝ)) := by ring
  rw [e, ← Real.rpow_add ht,
    show (71 / 1292 : ℝ) + 13 / 1292 = 21 / 323 by norm_num]
  ring

/-- `d⁴K_ℓ² = t^{21/323}`. -/
private lemma ra2_dK_key {t : ℝ} (ht : 0 < t) :
    (t ^ (6 / 323 : ℝ)) ^ 4 * (t ^ (-(3 / 646) : ℝ)) ^ 2 = t ^ (21 / 323 : ℝ) := by
  rw [ra2_rpow_nat_mul ht.le, ra2_rpow_nat_mul ht.le, ← Real.rpow_add ht]
  rw [show (6 / 323 : ℝ) * ↑(4 : ℕ) + -(3 / 646) * ↑(2 : ℕ) = 21 / 323 by norm_num]

/-- `ℓ^{-2}K_ℓ² = μa`: the exact cancellation of the box side. -/
private lemma ra2_ellK_key {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    (t ^ (-(3 / 646) : ℝ) * y ^ (-(1 / 2) : ℝ)) ^ (-(2 : ℝ))
        * (t ^ (-(3 / 646) : ℝ)) ^ 2 = y := by
  have h1 : (0 : ℝ) ≤ t ^ (-(3 / 646) : ℝ) := Real.rpow_nonneg ht.le _
  have h2 : (0 : ℝ) ≤ y ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hy.le _
  have ht' : 0 < t ^ (-(3 / 646) : ℝ) := Real.rpow_pos_of_pos ht _
  have hA : (t ^ (-(3 / 646) : ℝ)) ^ (-(2 : ℝ)) * (t ^ (-(3 / 646) : ℝ)) ^ 2 = 1 := by
    rw [← Real.rpow_natCast (t ^ (-(3 / 646) : ℝ)) 2, ← Real.rpow_add ht',
      show -(2 : ℝ) + ↑(2 : ℕ) = 0 by norm_num, Real.rpow_zero]
  have hB : (y ^ (-(1 / 2) : ℝ)) ^ (-(2 : ℝ)) = y := by
    rw [← Real.rpow_mul hy.le, show (-(1 / 2 : ℝ)) * (-(2 : ℝ)) = 1 by norm_num,
      Real.rpow_one]
  rw [Real.mul_rpow h1 h2, hB]
  have hstep : (t ^ (-(3 / 646) : ℝ)) ^ (-(2 : ℝ)) * y * (t ^ (-(3 / 646) : ℝ)) ^ 2
      = y * ((t ^ (-(3 / 646) : ℝ)) ^ (-(2 : ℝ)) * (t ^ (-(3 / 646) : ℝ)) ^ 2) := by ring
  rw [hstep, hA, mul_one]

/-- `ℓκ = d^{-2}`: the exact box-side/bump identity `honCutRad v μ = ((t^{6/323})²)⁻¹`. -/
private lemma ra2_cut_key {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    (t ^ (-(3 / 646) : ℝ) * y ^ (-(1 / 2) : ℝ))
        * ((t ^ (-(3 / 646) : ℝ) * (t ^ (6 / 323 : ℝ)) ^ (2 : ℕ))⁻¹ * y ^ (1 / 2 : ℝ))
      = ((t ^ (6 / 323 : ℝ)) ^ (2 : ℕ))⁻¹ := by
  set A : ℝ := t ^ (-(3 / 646) : ℝ) with hA
  set D : ℝ := (t ^ (6 / 323 : ℝ)) ^ (2 : ℕ) with hD
  set P : ℝ := y ^ (-(1 / 2) : ℝ) with hP
  set Q : ℝ := y ^ (1 / 2 : ℝ) with hQ
  have hPQ : P * Q = 1 := by rw [hP, hQ]; exact ra2_rpow_half hy
  have hAne : A ≠ 0 := by
    rw [hA]; exact ne_of_gt (Real.rpow_pos_of_pos ht _)
  rw [mul_inv A D]
  rw [show (A * P) * (A⁻¹ * D⁻¹ * Q) = D⁻¹ * ((A * A⁻¹) * (P * Q)) by ring]
  rw [mul_inv_cancel₀ hAne, one_mul, hPQ, mul_one]

/-- For `0 < t ≤ 1` and `b ≤ a`, `t^a ≤ t^b`. -/
private lemma ra2_le_exp {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {a b : ℝ} (hba : b ≤ a) (hb : 0 ≤ b) :
    t ^ a ≤ t ^ b := by
  have hb' : t ^ b * t ^ (a - b) = t ^ a := by
    rw [← Real.rpow_add ht, show b + (a - b) = a by ring]
  have hble : t ^ (a - b) ≤ 1 := by
    refine Real.rpow_le_one ht.le ht1 ?_
    linarith
  calc t ^ a = t ^ b * t ^ (a - b) := hb'.symm
    _ ≤ t ^ b * 1 := mul_le_mul_of_nonneg_left hble (Real.rpow_nonneg ht.le _)
    _ = t ^ b := by ring

/-- The core arithmetic: for `0 < t ≤ (1/M)³²` with `M = 25600·48π(1+C²)`,
`48πC²t^{21/323}(1 + 1/(58982400 t^{13/1292})) ≤ 1/12800`. -/
private lemma ra2_core {C t : ℝ} (ht : 0 < t)
    (htT : t ≤ (1 / (25600 * (48 * Real.pi * (1 + C ^ 2)))) ^ (32 : ℝ)) :
    48 * Real.pi * C ^ 2 * t ^ (21 / 323 : ℝ) * (1 + 1 / (58982400 * t ^ (13 / 1292 : ℝ)))
      ≤ 1 / 12800 := by
  set M : ℝ := 25600 * (48 * Real.pi * (1 + C ^ 2)) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    have hπ := Real.pi_gt_three
    nlinarith [sq_nonneg C]
  have hinv : 0 < 1 / M := by positivity
  have hinv1 : 1 / M ≤ 1 := by rw [div_le_one hMpos]; exact hM1
  have ht1 : t ≤ 1 := le_trans htT (Real.rpow_le_one hinv.le hinv1 (by norm_num))
  have hsmall : t ^ (1 / 32 : ℝ) ≤ 1 / M := by
    have hbase : (0 : ℝ) ≤ 1 / M := hinv.le
    calc t ^ (1 / 32 : ℝ) ≤ ((1 / M) ^ (32 : ℝ)) ^ (1 / 32 : ℝ) :=
          Real.rpow_le_rpow ht.le htT (by norm_num)
      _ = (1 / M) ^ ((32 : ℝ) * (1 / 32 : ℝ)) := (Real.rpow_mul hbase 32 (1 / 32)).symm
      _ = 1 / M := by rw [show (32 : ℝ) * (1 / 32) = 1 by norm_num, Real.rpow_one]
  have h1 : t ^ (21 / 323 : ℝ) ≤ t ^ (1 / 32 : ℝ) :=
    ra2_le_exp ht ht1 (by norm_num) (by norm_num)
  have h2 : t ^ (21 / 323 : ℝ) / (58982400 * t ^ (13 / 1292 : ℝ)) ≤ t ^ (1 / 32 : ℝ) := by
    rw [ra2_div_key ht]
    calc t ^ (71 / 1292 : ℝ) / 58982400 ≤ t ^ (71 / 1292 : ℝ) * 1 := by
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 58982400)]
          nlinarith [Real.rpow_nonneg ht.le (71 / 1292 : ℝ)]
      _ = t ^ (71 / 1292 : ℝ) := by ring
      _ ≤ t ^ (1 / 32 : ℝ) := ra2_le_exp ht ht1 (by norm_num) (by norm_num)
  have hsum : t ^ (21 / 323 : ℝ) * (1 + 1 / (58982400 * t ^ (13 / 1292 : ℝ)))
      ≤ 2 * t ^ (1 / 32 : ℝ) := by
    have he : t ^ (21 / 323 : ℝ) * (1 + 1 / (58982400 * t ^ (13 / 1292 : ℝ)))
        = t ^ (21 / 323 : ℝ) + t ^ (21 / 323 : ℝ) / (58982400 * t ^ (13 / 1292 : ℝ)) := by
      rw [mul_add, mul_one, mul_one_div]
    rw [he]
    linarith
  have hfin : 48 * Real.pi * C ^ 2 * (1 / M) ≤ 1 / 25600 := by
    rw [hMdef, mul_one_div, div_le_iff₀ (by positivity)]
    have hπ := Real.pi_pos
    nlinarith [sq_nonneg C]
  calc 48 * Real.pi * C ^ 2 * t ^ (21 / 323 : ℝ) * (1 + 1 / (58982400 * t ^ (13 / 1292 : ℝ)))
      = 48 * Real.pi * C ^ 2
          * (t ^ (21 / 323 : ℝ) * (1 + 1 / (58982400 * t ^ (13 / 1292 : ℝ)))) := by ring
    _ ≤ 48 * Real.pi * C ^ 2 * (2 * t ^ (1 / 32 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * (48 * Real.pi * C ^ 2 * t ^ (1 / 32 : ℝ)) := by ring
    _ ≤ 2 * (48 * Real.pi * C ^ 2 * (1 / M)) := by
        have := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ 48 * Real.pi * C ^ 2)
        linarith
    _ ≤ 2 * (1 / 25600) := by linarith
    _ = 1 / 12800 := by norm_num

/-! ## 2. The theorem -/

theorem rowArith2_honest {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (εg : ℝ) (hεg : 0 < εg) (hεg1 : εg ≤ 1)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧ ∀ Ng : ℝ → ℕ,
      Work.BoseRowQ2.RowArith2 (h := h) (fc := fc) (fu := fu) R εg' Ng C₁
        (Work.BoseRowQ2.RowGchiMaskRowAux.honCutRad v) (Work.BoseRowQ2.fsEps v 58982400) := by
  refine ⟨min εg (min 1 ((1 / (25600 * (48 * Real.pi * (1 + C₁ ^ 2)))) ^ (32 : ℝ))),
    lt_min hεg (lt_min one_pos (by positivity)), min_le_left _ _, ?_⟩
  intro Ng _hε'1 HM _hNg μ hμ hμa3 ρ hρ
  rw [ArithAt2]
  have hμa3g : μ * _root_.BoseGases.a v ^ 3 ≤ εg :=
    le_trans hμa3 (min_le_left _ _)
  have hμa3T : μ * _root_.BoseGases.a v ^ 3
      ≤ (1 / (25600 * (48 * Real.pi * (1 + C₁ ^ 2)))) ^ (32 : ℝ) :=
    le_trans hμa3 (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht : 0 < μ * _root_.BoseGases.a v ^ 3 := by positivity
  have hy : 0 < μ * _root_.BoseGases.a v := by positivity
  -- §1 the two basic bounds of the row
  have hρle : ρ ≤ 3 * μ / 2 := hρ.2.2
  obtain ⟨hW0, hWle⟩ := honE_W1omega0_row hR hav hv_nonneg hvrad hv_supp hrég HM μ hμ hμa3g
  have h2ρW : 2 * ρ * (honE v h fc fu HM μ).W1omega0
      ≤ 48 * Real.pi * (μ * _root_.BoseGases.a v) := by
    have h1 : ρ * (honE v h fc fu HM μ).W1omega0
        ≤ (3 * μ / 2) * (16 * Real.pi * _root_.BoseGases.a v) :=
      mul_le_mul hρle hWle hW0 (by positivity)
    nlinarith [h1, Real.pi_pos, hav, hμ]
  -- §2 the exact identities
  have hKpos : 0 < (honE v h fc fu HM μ).Kl := by
    rw [honE_Kl_eq v h fc fu HM μ]
    exact Real.rpow_pos_of_pos ht _
  have hPE : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      = (honE v h fc fu HM μ).eT := rfl
  have hPD : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = (honE v h fc fu HM μ).d := rfl
  have hPK : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      = (honE v h fc fu HM μ).Kl := rfl
  have hD : (honE v h fc fu HM μ).d = (μ * _root_.BoseGases.a v ^ 3) ^ (6 / 323 : ℝ) :=
    honE_d_eq v h fc fu HM μ
  have hK : (honE v h fc fu HM μ).Kl = (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ) :=
    honE_Kl_eq v h fc fu HM μ
  have hell : Work.BoseBoxFock.ellH v μ
      = (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ)
        * (μ * _root_.BoseGases.a v) ^ (-(1 / 2) : ℝ) := by
    rw [← honE_ell v h fc fu HM μ hμ hav, honE_ell_eq v h fc fu HM hμ hav]
  have hellE : (honE v h fc fu HM μ).ell
      = (μ * _root_.BoseGases.a v ^ 3) ^ (-(3 / 646) : ℝ)
        * (μ * _root_.BoseGases.a v) ^ (-(1 / 2) : ℝ) :=
    honE_ell_eq v h fc fu HM hμ hav
  have hεeq : fsEps v 58982400 μ
      = 58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ) := by
    rw [fsEps, hPE, hPD, hPK, honE_eT_eq', honE_d_eq, honE_Kl_eq]
    exact ra2_eps_key ht
  have hcut : (C₁ / RowGchiMaskRowAux.honCutRad v μ) ^ 2
      = C₁ ^ 2 * ((honE v h fc fu HM μ).d) ^ 4 := by
    have hκ : RowGchiMaskRowAux.honCutRad v μ = (((honE v h fc fu HM μ).d) ^ 2)⁻¹ := by
      rw [RowGchiMaskRowAux.honCutRad, RowGchiMaskRowAux.honKap, hPK, hPD,
        Real.rpow_neg_one, Real.sqrt_eq_rpow, hell, hD, hK]
      exact ra2_cut_key ht hy
    rw [hκ, div_inv_eq_mul]
    ring
  have hdK : ((honE v h fc fu HM μ).d) ^ 4 * ((honE v h fc fu HM μ).Kl) ^ 2
      = (μ * _root_.BoseGases.a v ^ 3) ^ (21 / 323 : ℝ) := by
    rw [hD, hK]
    exact ra2_dK_key ht
  have hellK : (honE v h fc fu HM μ).ell ^ (-(2 : ℝ)) * ((honE v h fc fu HM μ).Kl) ^ 2
      = μ * _root_.BoseGases.a v := by
    rw [hellE, hK]
    exact ra2_ellK_key ht hy
  have hdK2 : (C₁ ^ 2 * ((honE v h fc fu HM μ).d) ^ 4) * ((honE v h fc fu HM μ).Kl) ^ 2
      = C₁ ^ 2 * (μ * _root_.BoseGases.a v ^ 3) ^ (21 / 323 : ℝ) := by
    rw [← hdK]
    ring
  have hRHS : ((honE v h fc fu HM μ).b / 800) * (honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
        * ((honE v h fc fu HM μ).Kl) ^ 2 = (1 / 12800) * (μ * _root_.BoseGases.a v) := by
    rw [honE_b v h fc fu HM μ,
      show (1 / 16 / 800) * (honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
            * ((honE v h fc fu HM μ).Kl) ^ 2
          = (1 / 16 / 800) * ((honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
            * ((honE v h fc fu HM μ).Kl) ^ 2) from by ring,
      hellK]
    norm_num
  refine le_of_mul_le_mul_right ?_ (pow_pos hKpos 2)
  calc 2 * ρ * (honE v h fc fu HM μ).W1omega0 * (1 + 1 / (fsEps v 58982400 μ))
        * (C₁ / RowGchiMaskRowAux.honCutRad v μ) ^ 2 * ((honE v h fc fu HM μ).Kl) ^ 2
      = (2 * ρ * (honE v h fc fu HM μ).W1omega0)
          * ((1 + 1 / (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ)))
            * (C₁ ^ 2 * (μ * _root_.BoseGases.a v ^ 3) ^ (21 / 323 : ℝ))) := by
        rw [hcut, hεeq, mul_assoc, hdK2]
        ring
    _ ≤ (48 * Real.pi * (μ * _root_.BoseGases.a v))
          * ((1 + 1 / (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ)))
            * (C₁ ^ 2 * (μ * _root_.BoseGases.a v ^ 3) ^ (21 / 323 : ℝ))) :=
        mul_le_mul_of_nonneg_right h2ρW (by positivity)
    _ ≤ (1 / 12800) * (μ * _root_.BoseGases.a v) := by
        have hfre : 48 * Real.pi * (μ * _root_.BoseGases.a v)
              * ((1 + 1 / (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ)))
                * (C₁ ^ 2 * (μ * _root_.BoseGases.a v ^ 3) ^ (21 / 323 : ℝ)))
            = (μ * _root_.BoseGases.a v)
              * (48 * Real.pi * C₁ ^ 2 * (μ * _root_.BoseGases.a v ^ 3) ^ (21 / 323 : ℝ)
                * (1 + 1 / (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ)))) := by
          ring
        rw [hfre]
        calc (μ * _root_.BoseGases.a v)
              * (48 * Real.pi * C₁ ^ 2 * (μ * _root_.BoseGases.a v ^ 3) ^ (21 / 323 : ℝ)
                * (1 + 1 / (58982400 * (μ * _root_.BoseGases.a v ^ 3) ^ (13 / 1292 : ℝ))))
            ≤ (μ * _root_.BoseGases.a v) * (1 / 12800) :=
              mul_le_mul_of_nonneg_left
                (ra2_core (C := C₁) (t := μ * _root_.BoseGases.a v ^ 3) ht hμa3T)
                (by positivity)
          _ = (1 / 12800) * (μ * _root_.BoseGases.a v) := by ring
    _ = ((honE v h fc fu HM μ).b / 800) * (honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
          * ((honE v h fc fu HM μ).Kl) ^ 2 := hRHS.symm


end Work.BoseRowQ2
