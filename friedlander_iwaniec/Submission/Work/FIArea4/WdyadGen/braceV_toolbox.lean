import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.Wdyad_units

namespace Work.FIArea4.WdyadGen

noncomputable section

/-!
# The brace `braceV` of Friedlander–Iwaniec (11.14): a toolbox

This file collects elementary comparison lemmas for the bracket

`braceV D R S ε = D^{-1/2} R S + (D√(RS) + R S^{3/4} + S R^{3/4})(RS)^ε`

and for the unit-class bracket `WTb` of (11.24).  They are the bookkeeping
inequalities used when reducing dyadic a̲ variance estimates to standard normalised
form: `WTb` is dominated by the brace (the redundant `D·min(R,S)` term is harmless),
the brace is stable under the dyadic dilation `S ↦ 2S`, under shrinking
`(D,S) ↦ (D/e, S/e)`, and it dominates each of `D`, `R` and the product
`R(X+1)` in the reduction regime `D < e`, `X e ≤ S`.
-/

/-- First summand of the brace: `D^{-1/2} R S`. -/
def braceV1 (D R S : ℕ) : ℝ :=
  (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)

/-- Second summand of the brace: `(D√(RS) + R S^{3/4} + S R^{3/4}) (RS)^ε`. -/
def braceV2 (D R S : ℕ) (ε : ℝ) : ℝ :=
  ((D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
      + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
      + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
    * (((R : ℝ) * (S : ℝ)) ^ ε)

lemma braceV_eq (D R S : ℕ) (ε : ℝ) :
    Work.FIArea4.braceV D R S ε = braceV1 D R S + braceV2 D R S ε := rfl

lemma braceV1_nonneg (D R S : ℕ) : 0 ≤ braceV1 D R S := by
  rw [braceV1]; positivity

lemma braceV2_nonneg (D R S : ℕ) (ε : ℝ) : 0 ≤ braceV2 D R S ε := by
  rw [braceV2]; positivity

lemma braceV_nonneg (D R S : ℕ) (ε : ℝ) : 0 ≤ Work.FIArea4.braceV D R S ε := by
  rw [braceV_eq]
  exact add_nonneg (braceV1_nonneg D R S) (braceV2_nonneg D R S ε)

lemma braceV1_le_braceV (D R S : ℕ) (ε : ℝ) :
    braceV1 D R S ≤ Work.FIArea4.braceV D R S ε := by
  rw [braceV_eq]; exact le_add_of_nonneg_right (braceV2_nonneg D R S ε)

lemma braceV2_le_braceV (D R S : ℕ) (ε : ℝ) :
    braceV2 D R S ε ≤ Work.FIArea4.braceV D R S ε := by
  rw [braceV_eq]; exact le_add_of_nonneg_left (braceV1_nonneg D R S)

lemma WTb_eq (D R S : ℕ) (ε : ℝ) :
    Work.FIArea4.WTb D R S ε =
      Work.FIArea4.braceV D R S ε
        + (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
  rw [Work.FIArea4.WTb, Work.FIArea4.braceV]; ring

/-- `x^{-1/2} = (√x)^{-1}`. -/
lemma rpow_neg_half_eq_inv_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- Lower bound for the integer quotient: if `1 ≤ D / e` then `D/(2e) ≤ ⌊D/e⌋`. -/
lemma nat_div_lower (D e : ℕ) (he : 1 ≤ e) (hq : 1 ≤ D / e) :
    (D : ℝ) / (2 * (e : ℝ)) ≤ ((D / e : ℕ) : ℝ) := by
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hq1 : (1 : ℝ) ≤ ((D / e : ℕ) : ℝ) := by exact_mod_cast hq
  have heq : (e : ℝ) ≤ ((D / e : ℕ) : ℝ) * (e : ℝ) :=
    le_mul_of_one_le_left (le_of_lt he0) hq1
  have hmod : ((D % e : ℕ) : ℝ) < (e : ℝ) := by
    exact_mod_cast (Nat.mod_lt D (by omega : 0 < e))
  have hD_eq : (D : ℝ) = ((D / e : ℕ) : ℝ) * (e : ℝ) + ((D % e : ℕ) : ℝ) := by
    have h := Nat.div_add_mod D e
    have h' : (D : ℝ) = ((e * (D / e) + D % e : ℕ) : ℝ) := by rw [h]
    push_cast at h'
    nlinarith [h']
  have hlt : (D : ℝ) < 2 * (((D / e : ℕ) : ℝ) * (e : ℝ)) := by
    rw [hD_eq]; linarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (e : ℝ))]
  linarith

/-- Scalar core of the `(D,S) ↦ (D/e, S/e)` stability of the brace: for positive `D`,
`d ≥ D/(2e)`, `e ≥ 1` and `s ≤ S/e`, the normalised first summand does not increase. -/
lemma sqrt_scale_le {D e d s S : ℝ} (hD : 0 < D) (he : 1 ≤ e) (hd : 0 < d)
    (hde : D / (2 * e) ≤ d) (hs : 0 ≤ s) (hsS : s ≤ S / e) (hS : 0 ≤ S) :
    d ^ (-(1 : ℝ) / 2) * s ≤ Real.sqrt 2 * D ^ (-(1 : ℝ) / 2) * S := by
  have he0 : 0 < e := lt_of_lt_of_le one_pos he
  have hd0 : 0 ≤ d := le_of_lt hd
  have hD0 : 0 ≤ D := le_of_lt hD
  have hL0 : 0 ≤ d ^ (-(1 : ℝ) / 2) * s :=
    mul_nonneg (Real.rpow_nonneg hd0 _) hs
  have hR0 : 0 ≤ Real.sqrt 2 * D ^ (-(1 : ℝ) / 2) * S :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.rpow_nonneg hD0 _)) hS
  have hdsq : d ^ (-(1 : ℝ) / 2) * d ^ (-(1 : ℝ) / 2) = d⁻¹ := by
    rw [← Real.rpow_add hd, show (-(1 : ℝ) / 2) + (-(1 : ℝ) / 2) = -1 by norm_num,
      Real.rpow_neg hd0, Real.rpow_one]
  have hDsq : D ^ (-(1 : ℝ) / 2) * D ^ (-(1 : ℝ) / 2) = D⁻¹ := by
    rw [← Real.rpow_add hD, show (-(1 : ℝ) / 2) + (-(1 : ℝ) / 2) = -1 by norm_num,
      Real.rpow_neg hD0, Real.rpow_one]
  have hs2 : s * s ≤ (S / e) * (S / e) := mul_self_le_mul_self hs hsS
  have hdinv : d⁻¹ ≤ 2 * e / D := by
    have hpos : 0 < D / (2 * e) := by positivity
    simpa [one_div, inv_div] using one_div_le_one_div_of_le hpos hde
  have hmain : d⁻¹ * (s * s) ≤ 2 * D⁻¹ * (S * S) := by
    have h1 : d⁻¹ * (s * s) ≤ (2 * e / D) * ((S / e) * (S / e)) :=
      mul_le_mul hdinv hs2 (mul_nonneg hs hs) (by positivity)
    have h2 : (2 * e / D) * ((S / e) * (S / e)) ≤ 2 * D⁻¹ * (S * S) := by
      have e1 : (2 * e / D) * ((S / e) * (S / e)) = 2 * (S * S) / (D * e) := by
        field_simp
      have e2 : 2 * D⁻¹ * (S * S) = 2 * (S * S) / D := by ring
      rw [e1, e2]
      apply div_le_div_of_nonneg_left (by positivity) hD
      exact le_mul_of_one_le_right hD0 he
    linarith [h1, h2]
  have hprod : (d ^ (-(1 : ℝ) / 2) * s) * (d ^ (-(1 : ℝ) / 2) * s)
      ≤ (Real.sqrt 2 * D ^ (-(1 : ℝ) / 2) * S) * (Real.sqrt 2 * D ^ (-(1 : ℝ) / 2) * S) := by
    have g2 : (d ^ (-(1 : ℝ) / 2) * s) * (d ^ (-(1 : ℝ) / 2) * s) = d⁻¹ * (s * s) := by
      rw [← hdsq]; ring
    have g3 : (Real.sqrt 2 * D ^ (-(1 : ℝ) / 2) * S) * (Real.sqrt 2 * D ^ (-(1 : ℝ) / 2) * S)
        = 2 * D⁻¹ * (S * S) := by
      have hs2' : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← sq]; exact Real.sq_sqrt (by norm_num)
      calc (Real.sqrt 2 * D ^ (-(1 : ℝ) / 2) * S) * (Real.sqrt 2 * D ^ (-(1 : ℝ) / 2) * S)
          = (Real.sqrt 2 * Real.sqrt 2) * (D ^ (-(1 : ℝ) / 2) * D ^ (-(1 : ℝ) / 2)) * (S * S) := by
            ring
        _ = 2 * D⁻¹ * (S * S) := by rw [hs2', hDsq]
    rw [g2, g3]; exact hmain
  exact (mul_self_le_mul_self_iff hL0 hR0).mpr hprod

/-- `WTb` is dominated by twice the brace: the extra term `D·min(R,S)(RS)^ε` is at most
`D√(RS)(RS)^ε`, already present in the brace. -/
lemma WTb_le_two_braceV (D R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    Work.FIArea4.WTb D R S ε ≤ 2 * Work.FIArea4.braceV D R S ε := by
  have hmin : (min R S : ℝ) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := by
    have h1 : (min R S : ℝ) ≤ (R : ℝ) := by exact_mod_cast min_le_left R S
    have h2 : (min R S : ℝ) ≤ (S : ℝ) := by exact_mod_cast min_le_right R S
    have h0 : (0 : ℝ) ≤ (min R S : ℝ) := by positivity
    have hr : (0 : ℝ) ≤ (R : ℝ) := by positivity
    apply Real.le_sqrt_of_sq_le
    have hsq : (min R S : ℝ) * (min R S : ℝ) ≤ (R : ℝ) * (S : ℝ) :=
      calc (min R S : ℝ) * (min R S : ℝ) ≤ (R : ℝ) * (min R S : ℝ) :=
              mul_le_mul_of_nonneg_right h1 h0
        _ ≤ (R : ℝ) * (S : ℝ) := mul_le_mul_of_nonneg_left h2 hr
    simpa [sq] using hsq
  have hp : (0 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.rpow_nonneg (by positivity) _
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hkey : (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)
      ≤ Work.FIArea4.braceV D R S ε := by
    have hstep1 : (D : ℝ) * (min R S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)
        ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hD0) hp
    have hstep2 : (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε)
        ≤ braceV2 D R S ε := by
      rw [braceV2]
      apply mul_le_mul_of_nonneg_right _ hp
      have h1 : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) := by positivity
      have h2 : (0 : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) := by positivity
      linarith
    exact le_trans hstep1 (le_trans hstep2 (braceV2_le_braceV D R S ε))
  rw [WTb_eq]
  linarith [hkey]

/-- The brace dominates `R`. -/
lemma R_le_braceV (D R S : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (R : ℝ) ≤ Work.FIArea4.braceV D R S ε := by
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hRS1 : (1 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by
    have := mul_le_mul hR1 hS1 (by norm_num : (0 : ℝ) ≤ 1) hR0
    simpa using this
  have hp1 : (1 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.one_le_rpow hRS1 hε
  have hS34 : (1 : ℝ) ≤ (S : ℝ) ^ ((3 : ℝ) / 4) := Real.one_le_rpow hS1 (by norm_num)
  have hA : (R : ℝ) ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) := le_mul_of_one_le_right hR0 hS34
  have hB : (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) :=
    le_mul_of_one_le_right (by positivity) hp1
  have hC : (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε)
      ≤ braceV2 D R S ε := by
    rw [braceV2]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    have h1 : (0 : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) := by positivity
    have h2 : (0 : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    linarith
  linarith [hA, hB, hC, braceV2_le_braceV D R S ε]

/-- The brace dominates `D`. -/
lemma D_le_braceV (D R S : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (D : ℝ) ≤ Work.FIArea4.braceV D R S ε := by
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hRS1 : (1 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by
    have := mul_le_mul hR1 hS1 (by norm_num : (0 : ℝ) ≤ 1) hR0
    simpa using this
  have hsq1 : (1 : ℝ) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := Real.one_le_sqrt.mpr hRS1
  have hp1 : (1 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.one_le_rpow hRS1 hε
  have hA : (D : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) := le_mul_of_one_le_right hD0 hsq1
  have hB : (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
      ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε) :=
    le_mul_of_one_le_right (by positivity) hp1
  have hC : (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε)
      ≤ braceV2 D R S ε := by
    rw [braceV2]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    have h1 : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    have h2 : (0 : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    linarith
  linarith [hA, hB, hC, braceV2_le_braceV D R S ε]

/-- Dyadic dilation `S ↦ 2S` costs at most `2^{ε+1}`. -/
lemma braceV_twoS_le (D R S : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    Work.FIArea4.braceV D R (2 * S) ε ≤ (2 : ℝ) ^ (ε + 1) * Work.FIArea4.braceV D R S ε := by
  have hcast : (((2 * S : ℕ) : ℝ)) = 2 * (S : ℝ) := by push_cast; ring
  have harg : (R : ℝ) * (((2 * S : ℕ) : ℝ)) = 2 * ((R : ℝ) * (S : ℝ)) := by rw [hcast]; ring
  have hsqrt : Real.sqrt ((R : ℝ) * (((2 * S : ℕ) : ℝ))) ≤ 2 * Real.sqrt ((R : ℝ) * (S : ℝ)) := by
    rw [harg, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    nlinarith [Real.sqrt_nonneg ((R : ℝ) * (S : ℝ))]
  have h34 : (((2 * S : ℕ) : ℝ)) ^ ((3 : ℝ) / 4) ≤ 2 * (S : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [hcast, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
    have h2 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (3 : ℝ) / 4 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (S : ℝ)) ((3 : ℝ) / 4)]
  have hp : ((R : ℝ) * (((2 * S : ℕ) : ℝ))) ^ ε ≤ (2 : ℝ) ^ ε * ((R : ℝ) * (S : ℝ)) ^ ε := by
    rw [harg, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
  have hAeq : braceV1 D R (2 * S) = 2 * braceV1 D R S := by
    rw [braceV1, braceV1, hcast]; ring
  have h2e : (2 : ℝ) ^ ε * 2 = (2 : ℝ) ^ (ε + 1) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hB2 : braceV2 D R (2 * S) ε ≤ (2 : ℝ) ^ (ε + 1) * braceV2 D R S ε := by
    unfold braceV2
    set b1 := (D : ℝ) * Real.sqrt ((R : ℝ) * (((2 * S : ℕ) : ℝ)))
        + (R : ℝ) * (((2 * S : ℕ) : ℝ)) ^ ((3 : ℝ) / 4)
        + (((2 * S : ℕ) : ℝ)) * (R : ℝ) ^ ((3 : ℝ) / 4) with hb1
    set p1 := (((R : ℝ) * (((2 * S : ℕ) : ℝ))) ^ ε) with hp1
    set b0 := (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
        + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
        + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) with hb0
    set p0 := (((R : ℝ) * (S : ℝ)) ^ ε) with hp0
    have hbr : b1 ≤ 2 * b0 := by
      rw [hb1, hb0]
      have h1 := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ (D : ℝ))
      have h2 := mul_le_mul_of_nonneg_left h34 (by positivity : (0 : ℝ) ≤ (R : ℝ))
      have h3 : (((2 * S : ℕ) : ℝ)) * (R : ℝ) ^ ((3 : ℝ) / 4)
          = 2 * ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)) := by rw [hcast]; ring
      nlinarith [h1, h2, h3]
    have hp' : p1 ≤ (2 : ℝ) ^ ε * p0 := by rw [hp1, hp0]; exact hp
    have hb0nn : (0 : ℝ) ≤ b0 := by rw [hb0]; positivity
    have hp1nn : (0 : ℝ) ≤ p1 := by rw [hp1]; positivity
    have hmul := mul_le_mul hbr hp' hp1nn (by positivity : (0 : ℝ) ≤ 2 * b0)
    calc b1 * p1 ≤ (2 * b0) * ((2 : ℝ) ^ ε * p0) := hmul
      _ = (2 : ℝ) ^ (ε + 1) * (b0 * p0) := by rw [← h2e]; ring
  calc Work.FIArea4.braceV D R (2 * S) ε
      = braceV1 D R (2 * S) + braceV2 D R (2 * S) ε := braceV_eq D R (2 * S) ε
    _ ≤ 2 * braceV1 D R S + (2 : ℝ) ^ (ε + 1) * braceV2 D R S ε :=
          add_le_add (le_of_eq hAeq) hB2
    _ ≤ (2 : ℝ) ^ (ε + 1) * braceV1 D R S + (2 : ℝ) ^ (ε + 1) * braceV2 D R S ε := by
          have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ (ε + 1) := by
            have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
              (show (1 : ℝ) ≤ ε + 1 by linarith)
            rwa [Real.rpow_one] at this
          have := mul_le_mul_of_nonneg_right h2le (braceV1_nonneg D R S)
          linarith
    _ = (2 : ℝ) ^ (ε + 1) * Work.FIArea4.braceV D R S ε := by
          rw [braceV_eq]; ring

/-- Shrinking `(D,S) ↦ (D/e, S/e)` costs at most `1 + √2`. -/
lemma braceV_div_le (D R S e : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (he : 1 ≤ e) :
    Work.FIArea4.braceV (D / e) R (S / e) ε
      ≤ (1 + Real.sqrt 2) * Work.FIArea4.braceV D R S ε := by
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hA' : ((D / e : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * ((S / e : ℕ) : ℝ)
      ≤ Real.sqrt 2 * braceV1 D R S := by
    by_cases hDe0 : D / e = 0
    · rw [hDe0]
      rw [braceV1]
      rw [show (((0 : ℕ) : ℝ)) ^ (-(1 : ℝ) / 2) = 0 by
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num : (-(1 : ℝ) / 2) ≠ 0)]]
      simp only [zero_mul]
      positivity
    · have hDe1 : 1 ≤ D / e := Nat.one_le_iff_ne_zero.mpr hDe0
      have hdpos : (0 : ℝ) < ((D / e : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < D / e)
      have hfloor : (D : ℝ) / (2 * (e : ℝ)) ≤ ((D / e : ℕ) : ℝ) := nat_div_lower D e he hDe1
      have hsS : ((S / e : ℕ) : ℝ) ≤ (S : ℝ) / (e : ℝ) := Nat.cast_div_le
      have hs0 : (0 : ℝ) ≤ ((S / e : ℕ) : ℝ) := by positivity
      have hS0 : (0 : ℝ) ≤ (S : ℝ) := by positivity
      have hsc := sqrt_scale_le hDpos he1 hdpos hfloor hs0 hsS hS0
      rw [braceV1]
      calc ((D / e : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * ((S / e : ℕ) : ℝ)
          = (((D / e : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) * ((S / e : ℕ) : ℝ)) * (R : ℝ) := by ring
        _ ≤ (Real.sqrt 2 * (D : ℝ) ^ (-(1 : ℝ) / 2) * (S : ℝ)) * (R : ℝ) :=
              mul_le_mul_of_nonneg_right hsc hR0
        _ = Real.sqrt 2 * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)) := by ring
  have hB' : braceV2 (D / e) R (S / e) ε ≤ braceV2 D R S ε := by
    unfold braceV2
    have hDe_le : ((D / e : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.div_le_self D e
    have hSe_le : ((S / e : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast Nat.div_le_self S e
    have hsqrt : Real.sqrt ((R : ℝ) * ((S / e : ℕ) : ℝ)) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hSe_le hR0)
    have h34 : ((S / e : ℕ) : ℝ) ^ ((3 : ℝ) / 4) ≤ (S : ℝ) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hSe_le (by norm_num)
    have hp : ((R : ℝ) * ((S / e : ℕ) : ℝ)) ^ ε ≤ ((R : ℝ) * (S : ℝ)) ^ ε :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hSe_le hR0) hε
    apply mul_le_mul _ hp (by positivity) (by positivity)
    have h1 := mul_le_mul hDe_le hsqrt (by positivity : (0 : ℝ) ≤ Real.sqrt ((R : ℝ) * ((S / e : ℕ) : ℝ)))
      (by positivity : (0 : ℝ) ≤ (D : ℝ))
    have h2 := mul_le_mul_of_nonneg_left h34 (by positivity : (0 : ℝ) ≤ (R : ℝ))
    have h3 := mul_le_mul_of_nonneg_left hSe_le (by positivity : (0 : ℝ) ≤ (R : ℝ) ^ ((3 : ℝ) / 4))
    nlinarith [h1, h2, h3]
  have h1 : braceV1 (D / e) R (S / e) ≤ Real.sqrt 2 * Work.FIArea4.braceV D R S ε := by
    rw [braceV1]
    exact le_trans hA' (mul_le_mul_of_nonneg_left (braceV1_le_braceV D R S ε) (Real.sqrt_nonneg 2))
  have h2 : braceV2 (D / e) R (S / e) ε ≤ Work.FIArea4.braceV D R S ε :=
    le_trans hB' (braceV2_le_braceV D R S ε)
  calc Work.FIArea4.braceV (D / e) R (S / e) ε
      = braceV1 (D / e) R (S / e) + braceV2 (D / e) R (S / e) ε := braceV_eq _ _ _ _
    _ ≤ Real.sqrt 2 * Work.FIArea4.braceV D R S ε + Work.FIArea4.braceV D R S ε :=
          add_le_add h1 h2
    _ = (1 + Real.sqrt 2) * Work.FIArea4.braceV D R S ε := by ring

/-- In the reduction regime `D < e`, `X e ≤ S`, the brace dominates `R (X+1)`. -/
lemma R_mul_le_braceV (D R S e X : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (hDe : D < e) (hXe : X * e ≤ S) :
    (R : ℝ) * ((X : ℝ) + 1) ≤ 2 * Work.FIArea4.braceV D R S ε := by
  rcases Nat.eq_zero_or_pos X with hX0 | hXpos
  · subst hX0
    have h := R_le_braceV D R S ε hε hR hS
    simp only [Nat.cast_zero, zero_add, mul_one]
    linarith [h, braceV_nonneg D R S ε]
  · have he0 : (0 : ℝ) < (e : ℝ) := by
      have : 0 < e := by omega
      exact_mod_cast this
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
    have hDeR : (D : ℝ) < (e : ℝ) := by exact_mod_cast hDe
    have hXle : (X : ℝ) ≤ (S : ℝ) / (e : ℝ) := by
      rw [le_div_iff₀ he0]
      have h : ((X * e : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast hXe
      push_cast at h
      linarith
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXpos
    have hXp1 : (X : ℝ) + 1 ≤ 2 * (X : ℝ) := by linarith
    have hXR : (R : ℝ) * (X : ℝ) ≤ (R : ℝ) * ((S : ℝ) / (e : ℝ)) :=
      mul_le_mul_of_nonneg_left hXle (by positivity : (0 : ℝ) ≤ (R : ℝ))
    have hsqrtD : Real.sqrt (D : ℝ) ≤ (e : ℝ) := by
      have h1 : Real.sqrt (D : ℝ) ≤ (D : ℝ) := by
        rw [Real.sqrt_le_iff]
        exact ⟨by positivity, by nlinarith [show (1 : ℝ) ≤ (D : ℝ) by exact_mod_cast hD]⟩
      linarith
    have hsqrtpos : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hRS : (R : ℝ) * ((S : ℝ) / (e : ℝ)) ≤ (R : ℝ) * ((S : ℝ) / Real.sqrt (D : ℝ)) := by
      have hinv : 1 / (e : ℝ) ≤ 1 / Real.sqrt (D : ℝ) := one_div_le_one_div_of_le hsqrtpos hsqrtD
      have := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ))
      calc (R : ℝ) * ((S : ℝ) / (e : ℝ)) = ((R : ℝ) * (S : ℝ)) * (1 / (e : ℝ)) := by ring
        _ ≤ ((R : ℝ) * (S : ℝ)) * (1 / Real.sqrt (D : ℝ)) := this
        _ = (R : ℝ) * ((S : ℝ) / Real.sqrt (D : ℝ)) := by ring
    have hb1 : (R : ℝ) * ((S : ℝ) / Real.sqrt (D : ℝ)) = braceV1 D R S := by
      rw [braceV1, rpow_neg_half_eq_inv_sqrt _ hD0]; ring
    have hfin : (R : ℝ) * ((X : ℝ) + 1) ≤ 2 * ((R : ℝ) * ((S : ℝ) / Real.sqrt (D : ℝ))) := by
      calc (R : ℝ) * ((X : ℝ) + 1) ≤ (R : ℝ) * (2 * (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hXp1 (by positivity)
        _ = 2 * ((R : ℝ) * (X : ℝ)) := by ring
        _ ≤ 2 * ((R : ℝ) * ((S : ℝ) / (e : ℝ))) := mul_le_mul_of_nonneg_left hXR (by norm_num)
        _ ≤ 2 * ((R : ℝ) * ((S : ℝ) / Real.sqrt (D : ℝ))) := mul_le_mul_of_nonneg_left hRS (by norm_num)
    rw [hb1] at hfin
    linarith [hfin, braceV1_le_braceV D R S ε, braceV_nonneg D R S ε]
theorem braceV_toolbox (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      (∀ D R S : ℕ, 1 ≤ R → 1 ≤ S →
        Work.FIArea4.WTb D R S ε ≤ K * Work.FIArea4.braceV D R S ε) ∧
      (∀ D R S : ℕ, 1 ≤ D → 1 ≤ R → 1 ≤ S →
        Work.FIArea4.braceV D R (2 * S) ε ≤ K * Work.FIArea4.braceV D R S ε) ∧
      (∀ D R S e : ℕ, 1 ≤ D → 1 ≤ R → 1 ≤ S → 1 ≤ e →
        Work.FIArea4.braceV (D / e) R (S / e) ε ≤ K * Work.FIArea4.braceV D R S ε) ∧
      (∀ D R S : ℕ, 1 ≤ D → 1 ≤ R → 1 ≤ S → (R : ℝ) ≤ K * Work.FIArea4.braceV D R S ε) ∧
      (∀ D R S : ℕ, 1 ≤ R → 1 ≤ S → (D : ℝ) ≤ K * Work.FIArea4.braceV D R S ε) ∧
      (∀ D R S e X : ℕ, 1 ≤ D → 1 ≤ R → 1 ≤ S → D < e → X * e ≤ S →
        (R : ℝ) * ((X : ℝ) + 1) ≤ K * Work.FIArea4.braceV D R S ε) := by
  have hε0 : (0 : ℝ) ≤ ε := hε.le
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (ε + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hKpos : (0 : ℝ) < (2 : ℝ) ^ (ε + 1) + 3 := by linarith
  refine ⟨(2 : ℝ) ^ (ε + 1) + 3, hKpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro D R S hR hS
    have h := WTb_le_two_braceV D R S ε hR hS
    have hK : (2 : ℝ) ≤ (2 : ℝ) ^ (ε + 1) + 3 := by linarith
    have hbv := braceV_nonneg D R S ε
    exact le_trans h (by simpa using mul_le_mul_of_nonneg_right hK hbv)
  · intro D R S hD hR hS
    have h := braceV_twoS_le D R S ε hε0
    have hK : (2 : ℝ) ^ (ε + 1) ≤ (2 : ℝ) ^ (ε + 1) + 3 := by linarith
    have hbv := braceV_nonneg D R S ε
    exact le_trans h (by simpa using mul_le_mul_of_nonneg_right hK hbv)
  · intro D R S e hD hR hS he
    have h := braceV_div_le D R S e ε hε0 hD hR hS he
    have hK : 1 + Real.sqrt 2 ≤ (2 : ℝ) ^ (ε + 1) + 3 := by
      have hs2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      linarith
    have hbv := braceV_nonneg D R S ε
    exact le_trans h (by simpa using mul_le_mul_of_nonneg_right hK hbv)
  · intro D R S hD hR hS
    have h := R_le_braceV D R S ε hε0 hR hS
    have hK : (1 : ℝ) ≤ (2 : ℝ) ^ (ε + 1) + 3 := by linarith
    have hbv := braceV_nonneg D R S ε
    exact le_trans h (by simpa using mul_le_mul_of_nonneg_right hK hbv)
  · intro D R S hR hS
    by_cases hD0 : D = 0
    · rw [hD0]
      simp only [Nat.cast_zero]
      exact mul_nonneg (le_of_lt hKpos) (braceV_nonneg 0 R S ε)
    · have hD : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr hD0
      have h := D_le_braceV D R S ε hε0 hD hR hS
      have hK : (1 : ℝ) ≤ (2 : ℝ) ^ (ε + 1) + 3 := by linarith
      have hbv := braceV_nonneg D R S ε
      exact le_trans h (by simpa using mul_le_mul_of_nonneg_right hK hbv)
  · intro D R S e X hD hR hS hDe hXe
    have h := R_mul_le_braceV D R S e X ε hε0 hD hR hS hDe hXe
    have hK : (2 : ℝ) ≤ (2 : ℝ) ^ (ε + 1) + 3 := by linarith
    have hbv := braceV_nonneg D R S ε
    exact le_trans h (by simpa using mul_le_mul_of_nonneg_right hK hbv)

end

end Work.FIArea4.WdyadGen
