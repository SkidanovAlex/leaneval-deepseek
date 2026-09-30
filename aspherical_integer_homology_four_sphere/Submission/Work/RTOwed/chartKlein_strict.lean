/-
# Strict positivity of the slacks of the cube chart

`chartKlein a (mkE4 x s)` is the Klein-model image of the upper-half-space point with cube
coordinates `x` and height `s` under the Möbius chart of the cube `a : Fin 48`.  This file proves
that for `x` *strictly inside* the unit cube of `a` and `s ∈ [11/10, ceilH a x)`, that point is in
the *interior* of the truncated 24-cell `Q̄`: every side slack `sideSlack S` and every truncation
slack `truncSlack w` is strictly positive.

## Method

Write `Q(x,σ) = chartMat a ·ᵥ v(x,σ)` with `v(x,σ) = (2x, |x|²+σ-1, |x|²+σ+1)`, so that
`chartKlein a (mkE4 x s) = kleinOfHyp (Q x s²)` (`chartKlein_mkE4`).  Each constraint of `Q̄` is a
*linear* functional of `Q`, and `Q` is *affine* in `σ`; hence the numerator of every slack,
`10·(the functional)`, is affine in `σ = s²` with constant slope.  Writing `σ` as a convex
combination of `σ₀ = 1` and `σ₂ = (ceilH a x)²` (with *positive* coefficients, because
`s ≥ 11/10 > 1` and `s < ceilH a x`), the positivity of a numerator follows from its positivity at
the two endpoints.

* at `σ₀ = 1` the numerators are positive: the quadratic lower bound `ckBnd` (a finite integer
  certificate over the 48 cubes and 48 constraints, `ckBnd_nonneg`/`ckBnd_pos`/`ckL0_ne`);
* at `σ₂ = (ceilH a x)²` the numerators are non-negative (`ckBnd2_nonneg`, again a finite
  certificate);
* the fourth coordinate `Q₄`, which is the denominator of every slack, is positive: at `σ₀ = 1` by
  a certificate (`ckBnd4_pos`) and at `σ₂` because `Q₄` is increasing in `σ` (`ckQ4_pos`).
-/
import Mathlib
import Submission.Work.RTOwed.cuspChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Matrix BigOperators
open Set Topology Function

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.RTOwed

/-! ## 1. The vector `v(x,σ)` and the affine map `Q` -/

/-- `v(x,σ) = (2x₀, 2x₁, 2x₂, |x|²+σ-1, |x|²+σ+1)`; it is proportional to `hypOfUHS` at the point
with horizontal coordinate `x` and height `s` when `σ = s²`. -/
def ckV (x : CuspE3) (σ : ℝ) : Fin 5 → ℝ :=
  ![2 * x 0, 2 * x 1, 2 * x 2,
    (x 0)^2 + (x 1)^2 + (x 2)^2 + σ - 1,
    (x 0)^2 + (x 1)^2 + (x 2)^2 + σ + 1]

@[simp] theorem ckV_apply_zero (x : CuspE3) (σ : ℝ) : ckV x σ 0 = 2 * x 0 := rfl
@[simp] theorem ckV_apply_one (x : CuspE3) (σ : ℝ) : ckV x σ 1 = 2 * x 1 := rfl
@[simp] theorem ckV_apply_two (x : CuspE3) (σ : ℝ) : ckV x σ 2 = 2 * x 2 := rfl
@[simp] theorem ckV_apply_three (x : CuspE3) (σ : ℝ) :
    ckV x σ 3 = (x 0)^2 + (x 1)^2 + (x 2)^2 + σ - 1 := rfl
@[simp] theorem ckV_apply_four (x : CuspE3) (σ : ℝ) :
    ckV x σ 4 = (x 0)^2 + (x 1)^2 + (x 2)^2 + σ + 1 := rfl

/-- The chart matrix of the cube `a` over `ℝ`. -/
def ckM (a : Fin 48) : Matrix (Fin 5) (Fin 5) ℝ :=
  (chartMat a).map (Int.castRingHom ℝ)

@[simp] theorem ckM_apply (a : Fin 48) (i j : Fin 5) : ckM a i j = ((chartMat a) i j : ℝ) := rfl

/-- The homogeneous coordinates of the chart of the point with cube coordinates `x` at height
`√σ`. -/
def ckQ (a : Fin 48) (x : CuspE3) (σ : ℝ) : Fin 5 → ℝ := ckM a *ᵥ ckV x σ

/-- The σ-derivative of `ckQ`. -/
def ckG (a : Fin 48) : Fin 5 → ℝ := fun j => ckM a j 3 + ckM a j 4

theorem ckQ_affine (a : Fin 48) (x : CuspE3) (σ : ℝ) :
    ckQ a x σ = ckQ a x 1 + (σ - 1) • ckG a := by
  funext j
  simp only [ckQ, ckM, ckG, Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_five, ckV_apply_zero, ckV_apply_one, ckV_apply_two, ckV_apply_three,
    ckV_apply_four]
  ring

/-- `ckQ` is affine in `σ`: a convex combination of the two values is the value at the convex
combination of the arguments. -/
theorem ckQ_convex (a : Fin 48) (x : CuspE3) (σ σ₁ σ₂ α β : ℝ) (h1 : α + β = 1)
    (h2 : σ = α * σ₁ + β * σ₂) :
    ckQ a x σ = α • ckQ a x σ₁ + β • ckQ a x σ₂ := by
  have hβ : β = 1 - α := by linarith
  funext j
  have h := congrFun (ckQ_affine a x σ) j
  have h₁ := congrFun (ckQ_affine a x σ₁) j
  have h₂ := congrFun (ckQ_affine a x σ₂) j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h h₁ h₂ ⊢
  rw [h, h₁, h₂, h2, hβ]
  ring

/-! ## 2. The chart is `kleinOfHyp ∘ ckQ` -/

theorem hypOfUHS_mkE4 (x : CuspE3) (s : ℝ) (hs : s ≠ 0) :
    Work.HypModel.hypOfUHS (mkE4 x s) = (2 * s)⁻¹ • ckV x (s^2) := by
  funext j
  fin_cases j <;>
  · simp only [ckV, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue]
    simp [mkE4, EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, Real.norm_eq_abs, sq_abs]
    field_simp

theorem proj4_smul (c : ℝ) (P : Work.HypModel.V5) :
    Work.HypModel.proj4 (c • P) = c • Work.HypModel.proj4 P := by
  ext i
  fin_cases i <;> simp [Work.HypModel.proj4]

theorem kleinOfHyp_smul (c : ℝ) (hc : c ≠ 0) (P : Work.HypModel.V5) :
    Work.HypModel.kleinOfHyp (c • P) = Work.HypModel.kleinOfHyp P := by
  simp only [Work.HypModel.kleinOfHyp, proj4_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
  have h : (c * P 4)⁻¹ * c = (P 4)⁻¹ := by
    rw [mul_inv_rev]; field_simp
  rw [h]

/-- **The chart in terms of `ckQ`**: `chartKlein a (mkE4 x s) = kleinOfHyp (ckQ a x s²)`. -/
theorem chartKlein_mkE4 (a : Fin 48) (x : CuspE3) (s : ℝ) (hs : s ≠ 0) :
    chartKlein a (mkE4 x s) = Work.HypModel.kleinOfHyp (ckQ a x (s^2)) := by
  rw [chartKlein, hypOfUHS_mkE4 x s hs, Matrix.mulVec_smul]
  rw [kleinOfHyp_smul _ (inv_ne_zero (mul_ne_zero two_ne_zero hs)) _]
  rfl

/-! ## 3. The slacks as quotients of linear functionals of `Q` -/

/-- The numerator of the side slack `S`: `Q₄ - ∑ n_{S,i} Q_i`. -/
def ckNS (S : Fin 24) (P : Fin 5 → ℝ) : ℝ :=
  P 4 - ∑ i : Fin 4, (Work.FoldInst.sideNormal S i : ℝ) * P (Fin.castSucc i)

/-- The numerator of the truncation slack `w`: `(4/5)Q₄ - (1/2)∑ p_{w,i} Q_i`. -/
def ckNT (w : Fin 24) (P : Fin 5 → ℝ) : ℝ :=
  (4/5 : ℝ) * P 4 - (1/2 : ℝ) * ∑ i : Fin 4, (Work.FoldInst.truncNormal2 w i : ℝ) * P (Fin.castSucc i)

@[simp] theorem castSucc_two : (Fin.castSucc (2 : Fin 4) : Fin 5) = 2 := rfl
@[simp] theorem castSucc_three : (Fin.castSucc (3 : Fin 4) : Fin 5) = 3 := rfl

theorem sideSlack_kleinOfHyp (S : Fin 24) (P : Fin 5 → ℝ) (h : P 4 ≠ 0) :
    Work.FoldInst.sideSlack S (Work.HypModel.kleinOfHyp P) = ckNS S P / P 4 := by
  simp only [Work.FoldInst.sideSlack, ckNS, Fin.sum_univ_four, Work.HypModel.kleinOfHyp_apply_zero,
    Work.HypModel.kleinOfHyp_apply_one, Work.HypModel.kleinOfHyp_apply_two,
    Work.HypModel.kleinOfHyp_apply_three, Fin.castSucc_zero, Fin.castSucc_one, castSucc_two,
    castSucc_three]
  field_simp

theorem truncSlack_kleinOfHyp (w : Fin 24) (P : Fin 5 → ℝ) (h : P 4 ≠ 0) :
    Work.FoldInst.truncSlack w (Work.HypModel.kleinOfHyp P) = ckNT w P / P 4 := by
  simp only [Work.FoldInst.truncSlack, ckNT, Fin.sum_univ_four, Work.HypModel.kleinOfHyp_apply_zero,
    Work.HypModel.kleinOfHyp_apply_one, Work.HypModel.kleinOfHyp_apply_two,
    Work.HypModel.kleinOfHyp_apply_three, Fin.castSucc_zero, Fin.castSucc_one, castSucc_two,
    castSucc_three]
  field_simp
  ring

/-- The combined constraint index: `k : Fin 48` is a side when `k < 24` and the truncation
`k - 24` otherwise. -/
def ckK (k : Fin 48) (P : Fin 5 → ℝ) : ℝ :=
  if h : (k : ℕ) < 24 then ckNS ⟨(k : ℕ), h⟩ P
  else ckNT ⟨(k : ℕ) - 24, by omega⟩ P

theorem ckNS_linear (S : Fin 24) (α β : ℝ) (P P' : Fin 5 → ℝ) :
    ckNS S (α • P + β • P') = α * ckNS S P + β * ckNS S P' := by
  simp only [ckNS, Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem ckNT_linear (w : Fin 24) (α β : ℝ) (P P' : Fin 5 → ℝ) :
    ckNT w (α • P + β • P') = α * ckNT w P + β * ckNT w P' := by
  simp only [ckNT, Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem ckK_linear (k : Fin 48) (α β : ℝ) (P P' : Fin 5 → ℝ) :
    ckK k (α • P + β • P') = α * ckK k P + β * ckK k P' := by
  by_cases h : (k : ℕ) < 24
  · simp only [ckK, dif_pos h]
    exact ckNS_linear _ _ _ _ _
  · simp only [ckK, dif_neg h]
    exact ckNT_linear _ _ _ _ _

/-- The index of a side constraint. -/
def ckOfSide (S : Fin 24) : Fin 48 := ⟨(S : ℕ), by omega⟩

/-- The index of a truncation constraint. -/
def ckOfTrunc (w : Fin 24) : Fin 48 := ⟨(w : ℕ) + 24, by omega⟩

@[simp] theorem ckK_ofSide (S : Fin 24) (P : Fin 5 → ℝ) : ckK (ckOfSide S) P = ckNS S P := by
  have h : ((ckOfSide S : Fin 48) : ℕ) < 24 := S.isLt
  rw [ckK, dif_pos h]
  congr 1

@[simp] theorem ckK_ofTrunc (w : Fin 24) (P : Fin 5 → ℝ) : ckK (ckOfTrunc w) P = ckNT w P := by
  have h : ¬ ((ckOfTrunc w : Fin 48) : ℕ) < 24 := by simp [ckOfTrunc]
  rw [ckK, dif_neg h]
  congr 1

/-! ## 4. The integer table of the functional `ckK` -/

/-- `10 · ckK k (Q)` as a linear combination of the entries of `v`: the coefficient of `v_j`. -/
def ckDc (a : Fin 48) (k : Fin 48) (j : Fin 5) : ℤ :=
  if h : (k : ℕ) < 24 then
    10 * ((chartMat a) 4 j - ∑ i : Fin 4,
      Work.FoldInst.sideNormal ⟨(k : ℕ), h⟩ i * (chartMat a) (Fin.castSucc i) j)
  else
    8 * (chartMat a) 4 j - 5 * ∑ i : Fin 4,
      Work.FoldInst.truncNormal2 ⟨(k : ℕ) - 24, by omega⟩ i * (chartMat a) (Fin.castSucc i) j

/-- `10 · ckK k (Q)` is `∑_j (ckDc a k j) · v_j`. -/
theorem sum_ckDc (a : Fin 48) (k : Fin 48) (x : CuspE3) (σ : ℝ) :
    ∑ j : Fin 5, (ckDc a k j : ℝ) * ckV x σ j = 10 * ckK k (ckQ a x σ) := by
  simp only [ckDc, ckK, ckNS, ckNT, ckQ, Matrix.mulVec, dotProduct, ckM_apply, Fin.sum_univ_five,
    Fin.sum_univ_four, ckV_apply_zero, ckV_apply_one, ckV_apply_two, ckV_apply_three,
    ckV_apply_four, Fin.castSucc_zero, Fin.castSucc_one, castSucc_two, castSucc_three]
  split_ifs <;> push_cast <;> ring

/-! ## 5. The endpoint `σ = 1`: quadratic certificate -/

/-- The inclusion `Fin 3 → Fin 5`. -/
def ck3to5 (j : Fin 3) : Fin 5 := ⟨(j : ℕ), by omega⟩

@[simp] theorem ck3to5_zero : ck3to5 0 = 0 := rfl
@[simp] theorem ck3to5_one : ck3to5 1 = 1 := rfl
@[simp] theorem ck3to5_two : ck3to5 2 = 2 := rfl

/-- The coefficient of `|t|²` in `10 · ckK k (Q(x,1))`, `t = x - cubeCorner a`. -/
def ckQ0 (a : Fin 48) (k : Fin 48) : ℤ := ckDc a k 3 + ckDc a k 4

/-- The coefficient of `t_j`. -/
def ckL0 (a : Fin 48) (k : Fin 48) (j : Fin 3) : ℤ :=
  2 * ckDc a k (ck3to5 j) + 2 * ckQ0 a k * Work.Cusp.cubeCorner a j

/-- The constant term. -/
def ckM0 (a : Fin 48) (k : Fin 48) : ℤ :=
  2 * (∑ j : Fin 3, ckDc a k (ck3to5 j) * Work.Cusp.cubeCorner a j)
    + ckQ0 a k * (∑ j : Fin 3, (Work.Cusp.cubeCorner a j)^2 + 1) + (ckDc a k 4 - ckDc a k 3)

/-- **The numerator at `σ = 1` as a quadratic function of `t = x - cubeCorner a`.** -/
theorem ten_ckK_one (a : Fin 48) (k : Fin 48) (x : CuspE3) :
    (10 : ℝ) * ckK k (ckQ a x 1)
      = (ckQ0 a k : ℝ) * (∑ j : Fin 3, (x j - (Work.Cusp.cubeCorner a j : ℝ))^2)
        + ∑ j : Fin 3, (ckL0 a k j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))
        + (ckM0 a k : ℝ) := by
  rw [← sum_ckDc a k x 1]
  simp only [ckQ0, ckL0, ckM0, Fin.sum_univ_three, Fin.sum_univ_five, ck3to5_zero, ck3to5_one,
    ck3to5_two, ckV_apply_zero, ckV_apply_one, ckV_apply_two, ckV_apply_three, ckV_apply_four]
  push_cast
  ring

/-- A lower bound for `Q u² + L u` with `u ∈ [0,1]` (the exact minimum up to rounding). -/
def ckIntMin (Q L : ℤ) : ℤ :=
  if 0 < Q then (if 0 ≤ L then 0 else if -L < 2 * Q then -((L*L + 4*Q - 1)/(4*Q)) else Q + L)
  else min (Q + L) 0

theorem intMin_le_mul (M : ℤ) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    ((min M 0 : ℤ) : ℝ) ≤ (M : ℝ) * u := by
  rcases le_total 0 M with h | h
  · rw [min_eq_right h]; push_cast
    have : (0:ℝ) ≤ (M:ℝ) * u := by positivity
    linarith
  · rw [min_eq_left h]
    have : (0:ℝ) ≤ (M:ℝ) * (u - 1) :=
      mul_nonneg_of_nonpos_of_nonpos (by exact_mod_cast h) (by linarith)
    linarith

theorem intMin_lt_mul (M : ℤ) (u : ℝ) (hM : M ≠ 0) (h0 : 0 < u) (h1 : u < 1) :
    ((min M 0 : ℤ) : ℝ) < (M : ℝ) * u := by
  rcases lt_trichotomy 0 M with h | h | h
  · rw [min_eq_right (le_of_lt h)]; push_cast
    have : (0:ℝ) < (M:ℝ) * u := by positivity
    linarith
  · exact absurd h.symm hM
  · rw [min_eq_left (le_of_lt h)]; push_cast
    have : (M:ℝ) * u > (M:ℝ) * 1 := mul_lt_mul_of_neg_left h1 (by exact_mod_cast h)
    linarith

theorem ckIntMin_le (Q L : ℤ) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    (ckIntMin Q L : ℝ) ≤ (Q : ℝ) * u^2 + (L : ℝ) * u := by
  rw [ckIntMin]
  split_ifs with hQ hL hc
  · push_cast
    have h1' : (0:ℝ) ≤ (Q:ℝ)*u^2 := by positivity
    have h2' : (0:ℝ) ≤ (L:ℝ)*u := by positivity
    linarith
  · push_cast
    have hQr : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
    have h4 : (0:ℝ) < 4*(Q:ℝ) := by linarith
    have hkey : L*L ≤ ((L*L + 4*Q - 1)/(4*Q)) * (4*Q) := by
      have h1' : (L*L + 4*Q - 1) % (4*Q) ≤ 4*Q - 1 := by
        have := Int.emod_lt_of_pos (L*L + 4*Q - 1) (show (0:ℤ) < 4*Q by omega)
        omega
      have h2' : (L*L + 4*Q - 1) = ((L*L + 4*Q - 1)/(4*Q)) * (4*Q) + (L*L + 4*Q - 1) % (4*Q) :=
        (Int.ediv_mul_add_emod _ _).symm
      omega
    have hkeyR : (L:ℝ)^2 ≤ ((((L*L + 4*Q - 1)/(4*Q) : ℤ)) : ℝ) * (4*(Q:ℝ)) := by
      have h' : (((L*L : ℤ)) : ℝ) ≤ ((((L*L + 4*Q - 1)/(4*Q)) * (4*Q) : ℤ) : ℝ) := by
        exact_mod_cast hkey
      push_cast at h' ⊢
      linarith
    have hdiv : (L:ℝ)^2 / (4*(Q:ℝ)) ≤ ((((L*L + 4*Q - 1)/(4*Q) : ℤ)) : ℝ) := by
      rw [div_le_iff₀ h4]
      linarith [hkeyR]
    have h3 : (0:ℝ) ≤ (Q:ℝ)*u^2 + (L:ℝ)*u + (L:ℝ)^2/(4*(Q:ℝ)) := by
      have hs := sq_nonneg (2*(Q:ℝ)*u + (L:ℝ))
      have he : (2*(Q:ℝ)*u + (L:ℝ))^2 = 4*(Q:ℝ)^2*u^2 + 4*(Q:ℝ)*(L:ℝ)*u + (L:ℝ)^2 := by ring
      have hX : (0:ℝ) ≤ 4*(Q:ℝ)^2*u^2 + 4*(Q:ℝ)*(L:ℝ)*u + (L:ℝ)^2 := by linarith [hs, he]
      have hdiv2 : (4*(Q:ℝ)^2*u^2 + 4*(Q:ℝ)*(L:ℝ)*u + (L:ℝ)^2)/(4*(Q:ℝ))
          = (Q:ℝ)*u^2 + (L:ℝ)*u + (L:ℝ)^2/(4*(Q:ℝ)) := by field_simp
      rw [← hdiv2]
      exact div_nonneg hX (le_of_lt h4)
    linarith
  · push_cast
    have hQr : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
    have hLr : (L:ℝ) ≤ -2*(Q:ℝ) := by
      have : ¬ (-(L:ℝ) < 2*(Q:ℝ)) := by
        intro hcon; exact hc (by exact_mod_cast hcon)
      linarith
    have h1' : u - 1 ≤ 0 := by linarith
    have h2' : (Q:ℝ)*u + (L:ℝ) + (Q:ℝ) ≤ 0 := by nlinarith
    have hprod := mul_nonneg_of_nonpos_of_nonpos h1' h2'
    have hexp : (u - 1) * ((Q:ℝ)*u + (L:ℝ) + (Q:ℝ))
        = (Q:ℝ)*u^2 + (L:ℝ)*u - ((Q:ℝ) + (L:ℝ)) := by ring
    rw [hexp] at hprod
    linarith
  · push_cast
    have hQr : (Q:ℝ) ≤ 0 := by
      have : ¬ (0 < (Q:ℝ)) := by intro hcon; exact hQ (by exact_mod_cast hcon)
      linarith
    have hmm := intMin_le_mul (Q + L) u h0 h1
    push_cast at hmm
    have hquad : ((Q:ℝ) + (L:ℝ)) * u ≤ (Q:ℝ)*u^2 + (L:ℝ)*u := by
      have : (0:ℝ) ≤ (Q:ℝ) * (u * (u - 1)) := by
        have : u * (u - 1) ≤ 0 := by nlinarith
        exact mul_nonneg_of_nonpos_of_nonpos hQr this
      nlinarith [this]
    linarith

@[simp] theorem ckIntMin_zero (L : ℤ) : ckIntMin 0 L = min L 0 := by
  simp [ckIntMin]

/-- The integral lower bound of `10 · ckK k (Q(x,1))` over the unit cube `t ∈ [0,1]³`. -/
def ckBnd (a : Fin 48) (k : Fin 48) : ℤ :=
  ckM0 a k + ∑ j : Fin 3, ckIntMin (ckQ0 a k) (ckL0 a k j)

/-- **The lower bound at `σ = 1`.** -/
theorem ckBnd_le_ten (a : Fin 48) (k : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) :
    (ckBnd a k : ℝ) ≤ 10 * ckK k (ckQ a x 1) := by
  have ht : ∀ j : Fin 3, 0 ≤ x j - (Work.Cusp.cubeCorner a j : ℝ)
      ∧ x j - (Work.Cusp.cubeCorner a j : ℝ) ≤ 1 := by
    intro j
    have h := hx j
    constructor <;> linarith [h.1, h.2]
  rw [ten_ckK_one a k x]
  have hsplit : (∑ j : Fin 3, (ckIntMin (ckQ0 a k) (ckL0 a k j) : ℝ))
      ≤ ∑ j : Fin 3, ((ckQ0 a k : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))^2
        + (ckL0 a k j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))) :=
    Finset.sum_le_sum fun j _ => ckIntMin_le (ckQ0 a k) (ckL0 a k j) _ (ht j).1 (ht j).2
  have hsplit2 : (ckQ0 a k : ℝ) * (∑ j : Fin 3, (x j - (Work.Cusp.cubeCorner a j : ℝ))^2)
      + ∑ j : Fin 3, (ckL0 a k j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))
      = ∑ j : Fin 3, ((ckQ0 a k : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))^2
        + (ckL0 a k j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  have hcast : (ckBnd a k : ℝ)
      = (ckM0 a k : ℝ) + ∑ j : Fin 3, (ckIntMin (ckQ0 a k) (ckL0 a k j) : ℝ) := by
    rw [ckBnd]
    push_cast
    ring
  linarith [hsplit, hsplit2, hcast]

/-! ### The finite certificates at `σ = 1` -/

/-- **Certificate**: the lower bound is non-negative. -/
theorem ckBnd_nonneg : ∀ (a : Fin 48) (k : Fin 48), 0 ≤ ckBnd a k := by decide +kernel

/-- **Certificate**: when the quadratic coefficient does not vanish, the lower bound is positive. -/
theorem ckBnd_pos : ∀ (a : Fin 48) (k : Fin 48), ckQ0 a k ≠ 0 → 0 < ckBnd a k := by decide +kernel

/-- **Certificate**: when the quadratic coefficient vanishes (the walls), some linear coefficient
does not. -/
theorem ckL0_ne : ∀ (a : Fin 48) (k : Fin 48), ckQ0 a k = 0 → ∃ j : Fin 3, ckL0 a k j ≠ 0 := by
  decide +kernel

/-- **Strict positivity of the numerator at `σ = 1`**, for `x` in the open cube. -/
theorem ckK_one_pos (a : Fin 48) (k : Fin 48) {x : CuspE3}
    (hx1 : ∀ j : Fin 3, (Work.Cusp.cubeCorner a j : ℝ) < x j)
    (hx2 : ∀ j : Fin 3, x j < (Work.Cusp.cubeCorner a j : ℝ) + 1) :
    0 < ckK k (ckQ a x 1) := by
  have hbox : x ∈ cubeBox a := fun j => ⟨le_of_lt (hx1 j), le_of_lt (hx2 j)⟩
  have ht : ∀ j : Fin 3, 0 < x j - (Work.Cusp.cubeCorner a j : ℝ)
      ∧ x j - (Work.Cusp.cubeCorner a j : ℝ) < 1 := fun j => ⟨by linarith [hx1 j], by linarith [hx2 j]⟩
  by_cases hQ : ckQ0 a k = 0
  · -- the walls: `10·N = ∑ L_j t_j + M0`, each `L_j t_j ≥ min (L_j) 0`, one strictly
    obtain ⟨j0, hj0⟩ := ckL0_ne a k hQ
    have hsum : (∑ j : Fin 3, ((min (ckL0 a k j) 0 : ℤ) : ℝ))
        < ∑ j : Fin 3, (ckL0 a k j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ)) := by
      refine Finset.sum_lt_sum (fun j _ => intMin_le_mul _ _
        (le_of_lt (ht j).1) (le_of_lt (ht j).2)) ⟨j0, Finset.mem_univ _, ?_⟩
      exact intMin_lt_mul _ _ hj0 (ht j0).1 (ht j0).2
    have hcast : (ckBnd a k : ℝ)
        = (ckM0 a k : ℝ) + ∑ j : Fin 3, ((min (ckL0 a k j) 0 : ℤ) : ℝ) := by
      simp only [ckBnd, hQ, ckIntMin_zero]
      push_cast
      ring
    have hnonneg : (0:ℝ) ≤ (ckM0 a k : ℝ) + ∑ j : Fin 3, ((min (ckL0 a k j) 0 : ℤ) : ℝ) := by
      rw [← hcast]
      exact_mod_cast ckBnd_nonneg a k
    have hten := ten_ckK_one a k x
    rw [hQ] at hten
    push_cast at hten
    simp only [zero_mul, zero_add] at hten
    linarith
  · have hpos := ckBnd_pos a k hQ
    have hle := ckBnd_le_ten a k hbox
    have : (0:ℝ) < (ckBnd a k : ℝ) := by exact_mod_cast hpos
    linarith

/-! ## 6. The endpoint `σ = (ceilH a x)²`: affine certificate -/

/-- The ceiling height squared, as a function of `x`. -/
def ckS2 (a : Fin 48) (x : CuspE3) : ℝ :=
  9/4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2))^2

/-- The constant term of `20 · ckK k (Q(x, σ₂))` as a function of `t = x - cubeCorner a`. -/
def ckK2 (a : Fin 48) (k : Fin 48) : ℤ :=
  4 * (∑ j : Fin 3, ckDc a k (ck3to5 j) * Work.Cusp.cubeCorner a j)
    + 2 * ckQ0 a k * (∑ j : Fin 3, (Work.Cusp.cubeCorner a j)^2) + 3 * ckQ0 a k
    + 2 * (ckDc a k 4 - ckDc a k 3)

/-- The coefficient of `t_j` in `20 · ckK k (Q(x, σ₂))`. -/
def ckE2 (a : Fin 48) (k : Fin 48) (j : Fin 3) : ℤ :=
  2 * (2 * ckDc a k (ck3to5 j) + 2 * ckQ0 a k * Work.Cusp.cubeCorner a j + ckQ0 a k)

/-- **The numerator at `σ = (ceilH a x)²` as an affine function of `t = x - cubeCorner a`.** -/
theorem twenty_ckK_two (a : Fin 48) (k : Fin 48) (x : CuspE3) :
    2 * (∑ j : Fin 5, (ckDc a k j : ℝ) * ckV x (ckS2 a x) j)
      = (ckK2 a k : ℝ)
        + ∑ j : Fin 3, (ckE2 a k j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ)) := by
  simp only [ckS2, ckK2, ckE2, ckQ0, Fin.sum_univ_three, Fin.sum_univ_five, ck3to5_zero,
    ck3to5_one, ck3to5_two, ckV_apply_zero, ckV_apply_one, ckV_apply_two, ckV_apply_three,
    ckV_apply_four]
  push_cast
  ring

/-- The integral lower bound of `20 · ckK k (Q(x, σ₂))` over the unit cube. -/
def ckBnd2 (a : Fin 48) (k : Fin 48) : ℤ :=
  ckK2 a k + ∑ j : Fin 3, min (ckE2 a k j) 0

/-- **Certificate**: the affine lower bound at the ceiling is non-negative. -/
theorem ckBnd2_nonneg : ∀ (a : Fin 48) (k : Fin 48), 0 ≤ ckBnd2 a k := by decide +kernel

/-- **Non-negativity of the numerator at the ceiling.** -/
theorem ckK_two_nonneg (a : Fin 48) (k : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) :
    0 ≤ ckK k (ckQ a x (ckS2 a x)) := by
  have ht : ∀ j : Fin 3, 0 ≤ x j - (Work.Cusp.cubeCorner a j : ℝ)
      ∧ x j - (Work.Cusp.cubeCorner a j : ℝ) ≤ 1 := by
    intro j
    have h := hx j
    constructor <;> linarith [h.1, h.2]
  have hsum := sum_ckDc a k x (ckS2 a x)
  have htw := twenty_ckK_two a k x
  have hcast : (ckBnd2 a k : ℝ)
      = (ckK2 a k : ℝ) + ∑ j : Fin 3, ((min (ckE2 a k j) 0 : ℤ) : ℝ) := by
    rw [ckBnd2]
    push_cast
    ring
  have h2 : (0:ℝ) ≤ (ckBnd2 a k : ℝ) := by exact_mod_cast ckBnd2_nonneg a k
  have hmin : (0:ℝ) ≤ (ckK2 a k : ℝ) + ∑ j : Fin 3, ((min (ckE2 a k j) 0 : ℤ) : ℝ) := by
    rw [← hcast]; exact h2
  have hsplit : (∑ j : Fin 3, ((min (ckE2 a k j) 0 : ℤ) : ℝ))
      ≤ ∑ j : Fin 3, (ckE2 a k j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ)) :=
    Finset.sum_le_sum fun j _ => intMin_le_mul _ _ (ht j).1 (ht j).2
  linarith [hsum, htw, hmin, hsplit]

/-! ## 7. Positivity of the fourth coordinate -/

/-- `10 · (row 4 of the chart matrix)`. -/
def ckD4 (a : Fin 48) (j : Fin 5) : ℤ := 10 * (chartMat a) 4 j

/-- The coefficient of `σ` in `Q₄ = (ckQ a x σ) 4`, scaled by `10`. -/
def ckQ4 (a : Fin 48) : ℤ := ckD4 a 3 + ckD4 a 4

/-- The coefficient of `t_j` in `10 · Q(x,1)₄`. -/
def ckL4 (a : Fin 48) (j : Fin 3) : ℤ :=
  2 * ckD4 a (ck3to5 j) + 2 * ckQ4 a * Work.Cusp.cubeCorner a j

/-- The constant term of `10 · Q(x,1)₄`. -/
def ckM4 (a : Fin 48) : ℤ :=
  2 * (∑ j : Fin 3, ckD4 a (ck3to5 j) * Work.Cusp.cubeCorner a j)
    + ckQ4 a * (∑ j : Fin 3, (Work.Cusp.cubeCorner a j)^2 + 1) + (ckD4 a 4 - ckD4 a 3)

/-- The Σ-derivative of `Q₄`. -/
theorem ckQ4_deriv (a : Fin 48) (x : CuspE3) (σ : ℝ) :
    (ckQ a x σ) 4 = (ckQ a x 1) 4 + (σ - 1) * (ckG a 4) := by
  have h := congrFun (ckQ_affine a x σ) 4
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h

theorem ckG_four (a : Fin 48) : ckG a 4 = ((chartMat a) 4 3 : ℝ) + ((chartMat a) 4 4 : ℝ) := by
  simp [ckG, ckM]

/-- **`10 · Q(x,1)₄` as a quadratic function of `t`.** -/
theorem ten_Q4 (a : Fin 48) (x : CuspE3) :
    (10 : ℝ) * (ckQ a x 1) 4
      = (ckQ4 a : ℝ) * (∑ j : Fin 3, (x j - (Work.Cusp.cubeCorner a j : ℝ))^2)
        + ∑ j : Fin 3, (ckL4 a j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))
        + (ckM4 a : ℝ) := by
  simp only [ckQ, ckQ4, ckD4, ckL4, ckM4, Matrix.mulVec, dotProduct, ckM_apply, Fin.sum_univ_three,
    Fin.sum_univ_five, ck3to5_zero, ck3to5_one, ck3to5_two, ckV_apply_zero, ckV_apply_one,
    ckV_apply_two, ckV_apply_three, ckV_apply_four]
  push_cast
  ring

/-- The integral lower bound of `10 · Q(x,1)₄` over the unit cube. -/
def ckBnd4 (a : Fin 48) : ℤ :=
  ckM4 a + ∑ j : Fin 3, ckIntMin (ckQ4 a) (ckL4 a j)

/-- **Certificate**: `Q₄` is positive at `σ = 1`. -/
theorem ckBnd4_pos : ∀ (a : Fin 48), 0 < ckBnd4 a := by decide +kernel

/-- **Certificate**: the coefficient of `σ` in `Q₄` is positive. -/
theorem ckQ4_pos : ∀ (a : Fin 48), 0 < ckQ4 a := by decide +kernel

/-- **`Q₄` is positive at `σ = 1`.** -/
theorem ckQ_one_pos (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) : 0 < (ckQ a x 1) 4 := by
  have ht : ∀ j : Fin 3, 0 ≤ x j - (Work.Cusp.cubeCorner a j : ℝ)
      ∧ x j - (Work.Cusp.cubeCorner a j : ℝ) ≤ 1 := by
    intro j
    have h := hx j
    constructor <;> linarith [h.1, h.2]
  have hsplit : (∑ j : Fin 3, (ckIntMin (ckQ4 a) (ckL4 a j) : ℝ))
      ≤ ∑ j : Fin 3, ((ckQ4 a : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))^2
        + (ckL4 a j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))) :=
    Finset.sum_le_sum fun j _ => ckIntMin_le (ckQ4 a) (ckL4 a j) _ (ht j).1 (ht j).2
  have hsplit2 : (ckQ4 a : ℝ) * (∑ j : Fin 3, (x j - (Work.Cusp.cubeCorner a j : ℝ))^2)
      + ∑ j : Fin 3, (ckL4 a j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))
      = ∑ j : Fin 3, ((ckQ4 a : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))^2
        + (ckL4 a j : ℝ) * (x j - (Work.Cusp.cubeCorner a j : ℝ))) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  have hcast : (ckBnd4 a : ℝ)
      = (ckM4 a : ℝ) + ∑ j : Fin 3, (ckIntMin (ckQ4 a) (ckL4 a j) : ℝ) := by
    rw [ckBnd4]
    push_cast
    ring
  have hle : (ckBnd4 a : ℝ) ≤ 10 * (ckQ a x 1) 4 := by
    rw [ten_Q4 a x]
    linarith [hsplit, hsplit2, hcast]
  have hpos : (0:ℝ) < (ckBnd4 a : ℝ) := by exact_mod_cast ckBnd4_pos a
  linarith

/-- **`Q₄` is positive at every `σ ≥ 1`.** -/
theorem ckQ_pos (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) {σ : ℝ} (hσ : 1 ≤ σ) :
    0 < (ckQ a x σ) 4 := by
  have h1 := ckQ_one_pos a hx
  have h2 := ckQ4_deriv a x σ
  have h3 := ckG_four a
  have h4 : (0:ℝ) < (ckQ4 a : ℝ) := by exact_mod_cast ckQ4_pos a
  have h4' : (0:ℝ) < ((chartMat a) 4 3 : ℝ) + ((chartMat a) 4 4 : ℝ) := by
    have : (ckQ4 a : ℝ) = 10 * (((chartMat a) 4 3 : ℝ) + ((chartMat a) 4 4 : ℝ)) := by
      simp only [ckQ4, ckD4]
      push_cast
      ring
    linarith
  rw [h2, h3]
  have : (0:ℝ) ≤ (σ - 1) * (((chartMat a) 4 3 : ℝ) + ((chartMat a) 4 4 : ℝ)) :=
    mul_nonneg (by linarith) (le_of_lt h4')
  linarith

/-! ## 8. The main theorem -/

theorem chartKlein_strict (a : Fin 48) {x : Work.RTOwed.CuspE3}
    (hx : ∀ i : Fin 3, (Work.Cusp.cubeCorner a i : ℝ) < x i ∧
      x i < (Work.Cusp.cubeCorner a i : ℝ) + 1) {s : ℝ} (hs1 : 11 / 10 ≤ s)
    (hs2 : s < Work.RTOwed.ceilH a x) :
    (∀ S : Fin 24, 0 < Work.FoldInst.sideSlack S
        (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 x s))) ∧
      (∀ w : Fin 24, 0 < Work.FoldInst.truncSlack w
        (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 x s))) := by
  have hspos : 0 < s := by linarith
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hbox : x ∈ cubeBox a := fun i => ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩
  have hceilpos : 0 < ceilH a x := by linarith
  have hrad : 0 < 9/4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2))^2 := by
    have h := Real.sqrt_pos.mp hceilpos
    simpa [ceilH] using h
  have hceil2 : (ceilH a x)^2 = ckS2 a x := by
    rw [ceilH, ckS2, Real.sq_sqrt (le_of_lt hrad)]
  have hσ1 : 1 < s^2 := by nlinarith [hs1]
  have hσσ2 : s^2 < ckS2 a x := by
    rw [← hceil2]
    nlinarith [hs2, hceilpos]
  have hs2ge1 : 1 ≤ ckS2 a x := le_of_lt (lt_trans hσ1 hσσ2)
  set σ := s^2 with hσdef
  set σ2 := ckS2 a x with hσ2def
  have hσ2ne : σ2 - 1 ≠ 0 := by linarith
  set α := (σ2 - σ) / (σ2 - 1) with hαdef
  set β := (σ - 1) / (σ2 - 1) with hβdef
  have hαβ : α + β = 1 := by
    rw [hαdef, hβdef]; field_simp; ring
  have hσeq : σ = α * 1 + β * σ2 := by
    rw [hαdef, hβdef]; field_simp; ring
  have hαpos : 0 < α := by
    rw [hαdef]; exact div_pos (by linarith) (by linarith)
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (by linarith) (by linarith)
  -- the convex combination of the homogeneous coordinates
  have hconv := ckQ_convex a x σ 1 σ2 α β hαβ hσeq
  -- positivity of `ckK k (ckQ a x σ)` for every constraint
  have hNpos : ∀ k : Fin 48, 0 < ckK k (ckQ a x σ) := by
    intro k
    have hlin := ckK_linear k α β (ckQ a x 1) (ckQ a x σ2)
    have h1 : 0 < ckK k (ckQ a x 1) :=
      ckK_one_pos a k (fun j => (hx j).1) (fun j => (hx j).2)
    have h2 : 0 ≤ ckK k (ckQ a x σ2) := ckK_two_nonneg a k hbox
    rw [hconv, hlin]
    nlinarith [hαpos, hβpos, h1, h2]
  -- positivity of the fourth coordinate
  have h4pos : 0 < (ckQ a x σ) 4 := by
    have h1 : 0 < (ckQ a x 1) 4 := ckQ_one_pos a hbox
    have h2 : 0 < (ckQ a x σ2) 4 := ckQ_pos a hbox hs2ge1
    have hcomp := congrFun hconv 4
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcomp
    rw [hcomp]
    nlinarith [hαpos, hβpos, h1, h2]
  have hchart : chartKlein a (mkE4 x s) = Work.HypModel.kleinOfHyp (ckQ a x σ) :=
    chartKlein_mkE4 a x s hsne
  have h4ne : (ckQ a x σ) 4 ≠ 0 := ne_of_gt h4pos
  constructor
  · intro S
    have h := sideSlack_kleinOfHyp S (ckQ a x σ) h4ne
    rw [hchart, h]
    have hk := hNpos (ckOfSide S)
    rw [ckK_ofSide] at hk
    exact div_pos hk h4pos
  · intro w
    have h := truncSlack_kleinOfHyp w (ckQ a x σ) h4ne
    rw [hchart, h]
    have hk := hNpos (ckOfTrunc w)
    rw [ckK_ofTrunc] at hk
    exact div_pos hk h4pos

end Work.RTOwed
