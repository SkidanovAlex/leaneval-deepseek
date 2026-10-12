import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseKinLoc.Assembly.TwoRegimeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Assembly.assembly_two_regime`

`AssemblySymbol β C` (`Submission/Work/BoseKinLoc/Residuals.lean`, BS `lm:Tu`) is the
pointwise momentum-space budget of the localised kinetic word `𝒯_u`:

```
εT (dℓ)⁻² raSym ℓ d p + b β⁻¹ ‖p‖²/(ℓ²‖p‖²+β)
  + (1-εT) tprSym ℓ (2s) C p + εT tprSym ℓ (2ds) C p  ≤  ‖p‖²      (∀ ℓ d s εT b, ∀p)
```

over the regime `KinRegime c₀ ℓ d s εT b` (with `tprSym` the two-regime kernel of BS
`lm:kinloc`, `Residuals.lean`).

This file proves `∃ β C, 0 < β ∧ β < 1 ∧ 0 < C ∧ AssemblySymbol β C`, with the explicit
constants `β = 1/2`, `C = 1`, `c₀ = 1/100`.

## Route

The budget is **homogeneous in the box momentum `q := ℓ‖p‖`**:

* `tprSym_scale`  : `ℓ² · tprSym ℓ σ C p = tprR σ C (ℓ‖p‖)` (`TwoRegimeDefs.lean`);
* `raTerm_scale`  : `ℓ² · ((dℓ)⁻² raSym ℓ d p) = (ℓ‖p‖)²/(1+d²(ℓ‖p‖)²)`;
* `gapTerm_scale` : `ℓ² · (‖p‖²/(ℓ²‖p‖²+β)) = (ℓ‖p‖)²/((ℓ‖p‖)²+β)`.

Multiplying the budget by `ℓ² > 0` and substituting `q = ℓ‖p‖` reduces it to the pure
real-arithmetic inequality `two_regime_core_aux`:

```
εT q²/(1+d²q²) + b (1/2)⁻¹ q²/(q²+1/2)
  + (1-εT) tprR (2s) 1 q + εT tprR (2ds) 1 q  ≤  q²
```

for all `q ≥ 0` and `0 < d,s,εT,b ≤ 1/100`.  That arithmetic is done by a three-region
analysis in `q`, according to which of the two branches of the two-regime kernel is active:

* **region A** (`q < (5/6)(2s)⁻¹`, both branches near): the near branches contribute
  `(1-εT)·8s³q² + εT·8d³s³q² ≤ 8s³q²`, and `εT + 4b + 8s³ ≤ 1`;
* **region B** (`(5/6)(2s)⁻¹ ≤ q < (5/6)(2ds)⁻¹`): the far branch of `tprR (2s)` supplies
  the slack `2qA - A² ≥ (7/3)A²` (`A = 1/(4s) ≥ 25`) against `2b + εT·(25/18)ds`;
* **region C** (`q ≥ (5/6)(2ds)⁻¹`, both branches far): the slack `(7/3)[(1-εT)A² + εT B²]`
  (`B = 1/(4ds)`) dominates `εT/d² + 2b`, using `7/(48s²) ≥ 100`.

## Note

The sibling module `Submission/Work/BoseKinLoc/Assembly/assembly_symbol.lean` refutes the
*old* (non-two-regime) rendering of the budget, in which the `Cs`-error symbol carried no
`ℓ²`-scaling.  The present statement is the corrected one, whose extra near-region branch
`Cσ³‖p‖²` of `tprSym` is exactly what makes the budget true.
-/

noncomputable section

namespace Work.BoseKinLoc.Assembly

open Work.BoseKinLoc
open Submission.BoseGases

/-! ## 1. The two branches of the two-regime kernel -/

/-- The near-region branch: below the switch `(5/6)σ⁻¹` the kernel is `Cσ³q²`. -/
lemma tprR_near {σ C q : ℝ} (h : ¬ ((5 / 6) * σ⁻¹ ≤ q)) : tprR σ C q = C * σ ^ 3 * q ^ 2 := by
  unfold tprR; rw [if_neg h]

/-- The far-region branch: above the switch `(5/6)σ⁻¹` the kernel is `[q − (2σ)⁻¹]²`
(the positive part being redundant because `(2σ)⁻¹ ≤ (5/6)σ⁻¹`). -/
lemma tprR_far {σ q : ℝ} (hσ : 0 < σ) (h : (5 / 6) * σ⁻¹ ≤ q) :
    tprR σ 1 q = (q - (2 * σ)⁻¹) ^ 2 := by
  have hσi : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have h2 : (2 * σ)⁻¹ = (2 : ℝ)⁻¹ * σ⁻¹ := by rw [mul_inv_rev]; ring
  have hle : (2 * σ)⁻¹ ≤ (5 / 6) * σ⁻¹ := by
    rw [h2]; exact mul_le_mul_of_nonneg_right (by norm_num) hσi
  unfold tprR; rw [if_pos h]; unfold fsKinCoeff; rw [max_eq_left]; linarith

/-! ## 2. Homogeneity of the budget in the box momentum `q = ℓ‖p‖` -/

/-- **Homogeneity of the two-regime kernel.**  For `ℓ > 0`,
`ℓ² · tprSym ℓ σ C p = tprR σ C (ℓ‖p‖)`: the switch `‖p‖ = (5/6)(σℓ)⁻¹` becomes
`ℓ‖p‖ = (5/6)σ⁻¹` and the far-region cut-off `(2σℓ)⁻¹` becomes `(2σ)⁻¹`. -/
lemma tprSym_scale (ℓ σ C : ℝ) (hℓ : 0 < ℓ) (p : ℝ³) :
    ℓ ^ 2 * tprSym ℓ σ C p = tprR σ C (ℓ * ‖p‖) := by
  have h1 : ℓ * (5 / 6 * (σ * ℓ)⁻¹) = 5 / 6 * σ⁻¹ := by
    rw [mul_inv_rev]; field_simp
  have hcond : (5 / 6 * (σ * ℓ)⁻¹ ≤ ‖p‖) ↔ (5 / 6 * σ⁻¹ ≤ ℓ * ‖p‖) := by
    rw [← h1]; exact (mul_le_mul_iff_of_pos_left hℓ).symm
  have h2 : ℓ * (2 * (σ * ℓ))⁻¹ = (2 * σ)⁻¹ := by
    rw [mul_inv_rev]; field_simp
  have hkin : ℓ ^ 2 * fsKinCoeff (2 * (σ * ℓ))⁻¹ ‖p‖ = fsKinCoeff (2 * σ)⁻¹ (ℓ * ‖p‖) := by
    unfold fsKinCoeff
    have hmax : ℓ * max (‖p‖ - (2 * (σ * ℓ))⁻¹) 0 = max (ℓ * ‖p‖ - (2 * σ)⁻¹) 0 := by
      rw [mul_max_of_nonneg _ _ (le_of_lt hℓ), mul_zero]
      congr 1
      rw [mul_sub, h2]
    have hsq : ℓ ^ 2 * max (‖p‖ - (2 * (σ * ℓ))⁻¹) 0 ^ 2
        = (ℓ * max (‖p‖ - (2 * (σ * ℓ))⁻¹) 0) ^ 2 := by ring
    rw [hsq, hmax]
  unfold tprSym tprR
  rw [mul_ite]
  by_cases h : 5 / 6 * (σ * ℓ)⁻¹ ≤ ‖p‖
  · rw [if_pos h, if_pos (hcond.mp h), hkin]
  · rw [if_neg h, if_neg (fun hc => h (hcond.mpr hc))]
    ring

/-- **Homogeneity of the Neumann-resolvent symbol** (BS `eq:Neumannineq`) in the box
momentum: `ℓ² (dℓ)⁻² raSym ℓ d p = (ℓ‖p‖)²/(1+d²(ℓ‖p‖)²)`. -/
lemma raTerm_scale (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) (p : ℝ³) :
    ℓ ^ 2 * ((d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)
      = (ℓ * ‖p‖) ^ 2 / (1 + d ^ 2 * (ℓ * ‖p‖) ^ 2) := by
  unfold raSym
  have h2 : (d * ℓ) ^ (-2 : ℤ) = 1 / (d * ℓ) ^ 2 := by
    rw [zpow_neg, zpow_ofNat]; ring
  rw [h2]; field_simp; ring

/-- **Homogeneity of the Neumann-gap symbol** (BS `eq:Quav`) in the box momentum:
`ℓ² ‖p‖²/(ℓ²‖p‖²+β) = (ℓ‖p‖)²/((ℓ‖p‖)²+β)`. -/
lemma gapTerm_scale (ℓ β : ℝ) (hℓ : 0 < ℓ) (p : ℝ³) :
    ℓ ^ 2 * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β)) = (ℓ * ‖p‖) ^ 2 / ((ℓ * ‖p‖) ^ 2 + β) := by
  field_simp

/-! ## 3. The core real-arithmetic inequality -/

set_option maxHeartbeats 1600000 in
/-- **The budget at `β = 1/2`, `C = 1`, `c₀ = 1/100`, in box momentum `q = ℓ‖p‖`.** -/
theorem two_regime_core_aux (q d s εT b : ℝ)
    (hq : 0 ≤ q) (hd : 0 < d) (hdc : d ≤ 1 / 100)
    (hs : 0 < s) (hsc : s ≤ 1 / 100) (hε : 0 < εT) (hεc : εT ≤ 1 / 100)
    (hb : 0 < b) (hbc : b ≤ 1 / 100) :
    εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) + b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2))
        + (1 - εT) * tprR (2 * s) 1 q + εT * tprR (2 * (d * s)) 1 q ≤ q ^ 2 := by
  have h2s : 0 < 2 * s := by linarith
  have h2ds : 0 < 2 * (d * s) := by positivity
  have hT1q : εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ εT * q ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + d ^ 2 * q ^ 2)]
    nlinarith [mul_nonneg (mul_nonneg hε.le (sq_nonneg q))
      (mul_nonneg (sq_nonneg d) (sq_nonneg q))]
  have hT2 : b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2)) ≤ 2 * b := by
    have h2 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    rw [h2]
    have h3 : q ^ 2 / (q ^ 2 + 1 / 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  have hT1d : εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ εT / d ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + d ^ 2 * q ^ 2)]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < d ^ 2)]
    nlinarith [hε.le, sq_nonneg q]
  have hT2q : b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2)) ≤ 4 * b * q ^ 2 := by
    have h2 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    rw [h2]
    have h3 : q ^ 2 / (q ^ 2 + 1 / 2) ≤ 2 * q ^ 2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < q ^ 2 + 1 / 2)]
      nlinarith
    nlinarith [h3, hb.le, sq_nonneg q]
  have hbig : (100 : ℝ) ≤ 7 / (48 * s ^ 2) := by
    have hs2 : s ^ 2 ≤ 1 / 10000 := by nlinarith [hs, hsc]
    have h1 : (100 : ℝ) ≤ 7 / (48 * (1 / 10000 : ℝ)) := by norm_num
    have h2 : 7 / (48 * (1 / 10000 : ℝ)) ≤ 7 / (48 * s ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith [hs2])
    linarith
  by_cases hB : (5 / 6) * (2 * s)⁻¹ ≤ q
  · by_cases hC : (5 / 6) * (2 * (d * s))⁻¹ ≤ q
    · -- ===== region C : both branches far =====
      rw [tprR_far h2s hB, tprR_far h2ds hC]
      set A := (2 * (2 * s))⁻¹ with hAdef
      set B := (2 * (2 * (d * s)))⁻¹ with hBdef
      have hApos : 0 < A := by rw [hAdef]; positivity
      have hBpos : 0 < B := by rw [hBdef]; positivity
      have hqA : (5 / 3) * A ≤ q := by
        have h1 : (5 / 6) * (2 * s)⁻¹ = (5 / 3) * A := by rw [hAdef]; field_simp; ring
        rw [← h1]; exact hB
      have hqB : (5 / 3) * B ≤ q := by
        have h1 : (5 / 6) * (2 * (d * s))⁻¹ = (5 / 3) * B := by rw [hBdef]; field_simp; ring
        rw [← h1]; exact hC
      have hAval : A ^ 2 = 1 / (16 * s ^ 2) := by rw [hAdef]; field_simp; ring
      have hBval : B ^ 2 = 1 / (16 * d ^ 2 * s ^ 2) := by rw [hBdef]; field_simp; ring
      have hT2b : 2 * b ≤ (7 / 3) * (1 - εT) * A ^ 2 := by
        rw [show (7 / 3) * (1 - εT) * A ^ 2 = (1 - εT) * (7 / (48 * s ^ 2)) by
          rw [hAval]; ring]
        have h2 : (2 : ℝ) * b ≤ 1 / 50 := by linarith
        have h1 : (99 / 100 : ℝ) ≤ 1 - εT := by linarith
        have h1' : (0:ℝ) ≤ 1 - εT := by linarith
        have := mul_le_mul h1 hbig (by norm_num : (0:ℝ) ≤ 100) h1'
        linarith
      have hs2' : s ^ 2 ≤ 7 / 48 := by nlinarith [hs, hsc]
      have hT1b : εT / d ^ 2 ≤ (7 / 3) * εT * B ^ 2 := by
        rw [hBval]
        rw [show (7 / 3) * εT * (1 / (16 * d ^ 2 * s ^ 2)) = (εT / d ^ 2) * (7 / (48 * s ^ 2)) by
          ring]
        have hone : (1 : ℝ) ≤ 7 / (48 * s ^ 2) := by linarith [hbig]
        have hunit : (0:ℝ) ≤ εT / d ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hone hunit]
      have hA7 : (7 / 3) * A ^ 2 ≤ 2 * q * A - A ^ 2 := by nlinarith [hqA, hApos]
      have hB7 : (7 / 3) * B ^ 2 ≤ 2 * q * B - B ^ 2 := by nlinarith [hqB, hBpos]
      nlinarith [hT1d, hT2, hT1b, hT2b, hA7, hB7]
    · -- ===== region B : tprR (2s) far, tprR (2ds) near =====
      rw [tprR_far h2s hB, tprR_near hC]
      set A := (2 * (2 * s))⁻¹ with hAdef
      have hApos : 0 < A := by rw [hAdef]; positivity
      have hqA : (5 / 3) * A ≤ q := by
        have h1 : (5 / 6) * (2 * s)⁻¹ = (5 / 3) * A := by rw [hAdef]; field_simp; ring
        rw [← h1]; exact hB
      have hAval : A ^ 2 = 1 / (16 * s ^ 2) := by rw [hAdef]; field_simp; ring
      have hqle : q ≤ 5 / (12 * d * s) := by
        have h := not_le.mp hC
        have h1 : (5 / 6) * (2 * (d * s))⁻¹ = 5 / (12 * d * s) := by field_simp; ring
        rw [h1] at h; linarith
      have hnear : 8 * d ^ 3 * s ^ 3 * q ^ 2 ≤ (25 / 18) * d * s := by
        have h1 : q ^ 2 ≤ (5 / (12 * d * s)) ^ 2 := by nlinarith [hqle, hq]
        have h2 : (5 / (12 * d * s)) ^ 2 = 25 / (144 * d ^ 2 * s ^ 2) := by field_simp; ring
        rw [h2] at h1
        have h3 : (8:ℝ) * d ^ 3 * s ^ 3 * (25 / (144 * d ^ 2 * s ^ 2)) = (25 / 18) * d * s := by
          field_simp; ring
        calc 8 * d ^ 3 * s ^ 3 * q ^ 2 ≤ 8 * d ^ 3 * s ^ 3 * (25 / (144 * d ^ 2 * s ^ 2)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (25 / 18) * d * s := h3
      have h23b : (1 : ℝ) * (2 * (d * s)) ^ 3 * q ^ 2 = 8 * d ^ 3 * s ^ 3 * q ^ 2 := by ring
      rw [h23b]
      have hA7 : (7 / 3) * A ^ 2 ≤ 2 * q * A - A ^ 2 := by nlinarith [hqA, hApos]
      have hRHS : 2 * b + εT * ((25 / 18) * d * s) ≤ (1 - εT) * ((7 / 3) * A ^ 2) := by
        rw [show (1 - εT) * ((7 / 3) * A ^ 2) = (1 - εT) * (7 / (48 * s ^ 2)) by
          rw [hAval]; ring]
        have h1 : (99 / 100 : ℝ) ≤ 1 - εT := by linarith
        have h1' : (0 : ℝ) ≤ 1 - εT := by linarith
        have h2 : (2 : ℝ) * b ≤ 1 / 50 := by linarith
        have hds : (25 / 18) * d * s ≤ (25 / 18) * (1 / 100) * (1 / 100) := by
          nlinarith [hdc, hsc, hd.le, hs.le]
        have h3 : εT * ((25 / 18) * d * s) ≤ 1 / 1000 := by
          have := mul_le_mul hεc hds (by positivity : (0:ℝ) ≤ (25/18)*d*s)
            (by norm_num : (0:ℝ) ≤ 1/100)
          nlinarith [this]
        have h4 : (99 / 100 : ℝ) * 100 ≤ (1 - εT) * (7 / (48 * s ^ 2)) :=
          mul_le_mul h1 hbig (by norm_num) h1'
        linarith
      have hnearE := mul_le_mul_of_nonneg_left hnear hε.le
      have hA7E := mul_le_mul_of_nonneg_left hA7 (by linarith : (0:ℝ) ≤ 1 - εT)
      nlinarith [hT1q, hT2, hnearE, hA7E, hRHS]
  · -- ===== region A : both branches near =====
    have hd1 : d ≤ 1 := by linarith
    have hA' : ¬ ((5 / 6) * (2 * (d * s))⁻¹ ≤ q) := by
      intro hcon
      have hdle : 2 * (d * s) ≤ 2 * s := by nlinarith [hd1, hs, hd.le]
      have hle : (2 * s)⁻¹ ≤ (2 * (d * s))⁻¹ :=
        (inv_le_inv₀ (by positivity : (0:ℝ) < 2 * s) (by positivity : (0:ℝ) < 2 * (d * s))).mpr hdle
      have hle2 : (5 / 6) * (2 * s)⁻¹ ≤ (5 / 6) * (2 * (d * s))⁻¹ := by linarith
      exact hB (le_trans hle2 hcon)
    rw [tprR_near hB, tprR_near hA']
    have h23a : (1 : ℝ) * (2 * s) ^ 3 * q ^ 2 = 8 * s ^ 3 * q ^ 2 := by ring
    have h23b : (1 : ℝ) * (2 * (d * s)) ^ 3 * q ^ 2 = 8 * d ^ 3 * s ^ 3 * q ^ 2 := by ring
    rw [h23a, h23b]
    have hd3 : d ^ 3 ≤ 1 := by nlinarith [hd.le, hd1]
    have hnear2 : 8 * d ^ 3 * s ^ 3 * q ^ 2 ≤ 8 * s ^ 3 * q ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hd3 (by positivity : (0:ℝ) ≤ s ^ 3 * q ^ 2)
      nlinarith [h]
    have hs3 : s ^ 3 ≤ 1 / 1000000 := by
      have h := pow_le_pow_left₀ hs.le hsc 3
      norm_num at h
      exact h
    have hfin : εT + 4 * b + 8 * s ^ 3 ≤ 1 := by linarith [hεc, hbc, hs3]
    have hkey : (1 - εT) * (8 * s ^ 3 * q ^ 2) + εT * (8 * d ^ 3 * s ^ 3 * q ^ 2)
        ≤ 8 * s ^ 3 * q ^ 2 := by
      have h1 : εT * (8 * d ^ 3 * s ^ 3 * q ^ 2) ≤ εT * (8 * s ^ 3 * q ^ 2) :=
        mul_le_mul_of_nonneg_left hnear2 hε.le
      nlinarith [h1]
    nlinarith [hT1q, hT2q, hkey, hfin, sq_nonneg q]

/-! ## 4. Assembly -/

/-- **The two-regime momentum budget** `AssemblySymbol (1/2) 1`: the pointwise budget of
BS `lm:Tu` holds with the two-regime kernel `tprSym`, `β = 1/2`, `C = 1`, `c₀ = 1/100`. -/
theorem assembly_two_regime :
    ∃ β C : ℝ, 0 < β ∧ β < 1 ∧ 0 < C ∧ Work.BoseKinLoc.AssemblySymbol β C := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold AssemblySymbol
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ℓ d s εT b hreg p
  unfold KinRegime at hreg
  obtain ⟨hℓ, hd, hdc, hd1, hs, hsc, hε, hεc, hb, hbc⟩ := hreg
  set q := ℓ * ‖p‖ with hqdef
  have hq : 0 ≤ q := by rw [hqdef]; positivity
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hcore := two_regime_core_aux q d s εT b hq hd hdc hs hsc hε hεc hb hbc
  have e1 : ℓ ^ 2 * (εT * (d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)
      = εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) := by
    have h := raTerm_scale ℓ d hℓ hd p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * (εT * (d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)
        = εT * (ℓ ^ 2 * ((d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)) by ring, h]
    ring
  have e2 : ℓ ^ 2 * (b * (1 / 2 : ℝ)⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + 1 / 2)))
      = b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2)) := by
    have h := gapTerm_scale ℓ (1 / 2) hℓ p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * (b * (1 / 2 : ℝ)⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + 1 / 2)))
        = b * (1 / 2 : ℝ)⁻¹ * (ℓ ^ 2 * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + 1 / 2))) by ring, h]
  have e3 : ℓ ^ 2 * ((1 - εT) * tprSym ℓ (2 * s) 1 p) = (1 - εT) * tprR (2 * s) 1 q := by
    have h := tprSym_scale ℓ (2 * s) 1 hℓ p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * ((1 - εT) * tprSym ℓ (2 * s) 1 p)
        = (1 - εT) * (ℓ ^ 2 * tprSym ℓ (2 * s) 1 p) by ring, h]
  have e4 : ℓ ^ 2 * (εT * tprSym ℓ (2 * (d * s)) 1 p) = εT * tprR (2 * (d * s)) 1 q := by
    have h := tprSym_scale ℓ (2 * (d * s)) 1 hℓ p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * (εT * tprSym ℓ (2 * (d * s)) 1 p)
        = εT * (ℓ ^ 2 * tprSym ℓ (2 * (d * s)) 1 p) by ring, h]
  have e5 : ℓ ^ 2 * ‖p‖ ^ 2 = q ^ 2 := by rw [hqdef]; ring
  apply (mul_le_mul_iff_of_pos_left hℓ2).mp
  rw [mul_add, mul_add, mul_add, e1, e2, e3, e4, e5]
  linarith [hcore]

end Work.BoseKinLoc.Assembly
