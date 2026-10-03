import Mathlib
import Submission.Work.FIArea2.Sec9AggDefs
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Work.FIArea2.sum_weight_sqcong
import Submission.Work.FIArea2.Count.summable_int_rpow_majorant

namespace Work.FIArea2.Count

open scoped BigOperators

noncomputable section

/-! ## Auxiliary one-dimensional and pointwise estimates

The §9 frequency weight `sec9Uwt Pa h₁ h₂ = (1 + h₁²H⁻²)⁻¹(1 + h₂²H⁻²)⁻¹` decays like
`H⁴ (h₁h₂)⁻²`, so the `τ₄`-weighted series over `ℤ²` converges.  The three ingredients are:

* a comparison of the weight with `(1+h²)⁻¹` (`inv_one_add_div_sq_le`);
* summability of `|h|^{1/2}(1+h²)⁻¹` on `ℤ` (`summable_abs_sqrt_mul_one_add_sq_inv`);
* the divisor bound `τ(n) ≤ C n^{1/16}`, hence `τ(n)⁴ ≤ C⁴ n^{1/4}` (`tau4_le`).
-/

/-- For `x ≥ 0`, `x^{1/2}(1+x)^{3/2} ≤ 2^{3/2}(1+x²)`. -/
lemma sqrt_cube_le (x : ℝ) (hx : 0 ≤ x) :
    x^((1:ℝ)/2) * (1+x)^((3:ℝ)/2) ≤ 2^((3:ℝ)/2) * (1 + x^2) := by
  have hx1 : 0 ≤ 1 + x := by linarith
  have h23 : (0:ℝ) < 2^((3:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  rcases le_total x 1 with h | h
  · have ha : x^((1:ℝ)/2) ≤ 1 := by
      have hh := Real.rpow_le_rpow hx h (by norm_num : (0:ℝ) ≤ 1/2)
      rwa [Real.one_rpow] at hh
    have hb : (1+x)^((3:ℝ)/2) ≤ 2^((3:ℝ)/2) :=
      Real.rpow_le_rpow hx1 (by linarith) (by norm_num : (0:ℝ) ≤ 3/2)
    have hle1 : (1:ℝ) ≤ 1 + x^2 := by linarith [sq_nonneg x]
    calc x^((1:ℝ)/2) * (1+x)^((3:ℝ)/2) ≤ 1 * 2^((3:ℝ)/2) :=
          mul_le_mul ha hb (Real.rpow_nonneg hx1 ((3:ℝ)/2)) (by norm_num)
      _ = 2^((3:ℝ)/2) := one_mul _
      _ ≤ 2^((3:ℝ)/2) * (1 + x^2) := by
          have := mul_le_mul_of_nonneg_left hle1 h23.le
          simpa using this
  · have hxpos : (0:ℝ) < x := by linarith
    have h2x : (1+x) ≤ 2*x := by linarith
    have hb : (1+x)^((3:ℝ)/2) ≤ (2*x)^((3:ℝ)/2) :=
      Real.rpow_le_rpow hx1 h2x (by norm_num : (0:ℝ) ≤ 3/2)
    have hb2 : (2*x)^((3:ℝ)/2) = 2^((3:ℝ)/2) * x^((3:ℝ)/2) :=
      Real.mul_rpow (by norm_num) hx
    have hprod : x^((1:ℝ)/2) * x^((3:ℝ)/2) = x^2 := by
      rw [← Real.rpow_add hxpos]
      rw [show (1:ℝ)/2 + 3/2 = 2 by norm_num, Real.rpow_two]
    calc x^((1:ℝ)/2)*(1+x)^((3:ℝ)/2)
        ≤ x^((1:ℝ)/2)*(2*x)^((3:ℝ)/2) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx ((1:ℝ)/2))
      _ = x^((1:ℝ)/2) * (2^((3:ℝ)/2) * x^((3:ℝ)/2)) := by rw [hb2]
      _ = 2^((3:ℝ)/2) * (x^((1:ℝ)/2)*x^((3:ℝ)/2)) := by ring
      _ = 2^((3:ℝ)/2) * x^2 := by rw [hprod]
      _ ≤ 2^((3:ℝ)/2) * (1 + x^2) := by
          have : x^2 ≤ 1 + x^2 := by linarith
          exact mul_le_mul_of_nonneg_left this h23.le

/-- `|t|^{1/2}(1+t²)⁻¹` is summable on `ℤ`. -/
lemma summable_abs_sqrt_mul_one_add_sq_inv :
    Summable (fun t : ℤ => |(t:ℝ)|^((1:ℝ)/2) * (1 + (t:ℝ)^2)⁻¹) := by
  have hbase : Summable (fun t : ℤ => (1 + |(t:ℝ)|/1)^(-(3/2:ℝ))) :=
    Work.FIArea2.Count.summable_int_rpow_majorant 1 le_rfl
  have hbase' : Summable (fun t : ℤ => (1 + |(t:ℝ)|)^(-(3/2:ℝ))) := by
    simpa using hbase
  have hmaj : Summable (fun t : ℤ => (2:ℝ)^((3:ℝ)/2) * (1 + |(t:ℝ)|)^(-(3/2:ℝ))) :=
    hbase'.mul_left _
  refine Summable.of_nonneg_of_le
    (f := fun t : ℤ => (2:ℝ)^((3:ℝ)/2) * (1 + |(t:ℝ)|)^(-(3/2:ℝ))) ?_ ?_ hmaj
  · intro t; positivity
  · intro t
    have hx0 : (0:ℝ) ≤ |(t:ℝ)| := abs_nonneg _
    have h1x0 : (0:ℝ) < 1 + |(t:ℝ)| := by linarith
    have h1x2 : (0:ℝ) < 1 + |(t:ℝ)|^2 := by positivity
    have h3 : (0:ℝ) < (1+|(t:ℝ)|)^((3:ℝ)/2) := Real.rpow_pos_of_pos h1x0 _
    have hkey2 : |(t:ℝ)|^((1:ℝ)/2) / (1+|(t:ℝ)|^2)
        ≤ (2:ℝ)^((3:ℝ)/2) / (1+|(t:ℝ)|)^((3:ℝ)/2) := by
      rw [div_le_div_iff₀ h1x2 h3]
      exact sqrt_cube_le |(t:ℝ)| hx0
    have hsq : (t:ℝ)^2 = |(t:ℝ)|^2 := (sq_abs _).symm
    rw [hsq, Real.rpow_neg (le_of_lt h1x0)]
    exact hkey2

/-- The weight comparison `(1 + h²H⁻²)⁻¹ ≤ (1+H²)(1+h²)⁻¹`. -/
lemma inv_one_add_div_sq_le (H h : ℝ) (hH : 0 < H) :
    (1 + h^2/H^2)⁻¹ ≤ (1+H^2) * (1+h^2)⁻¹ := by
  have hLpos : (0:ℝ) < 1 + h^2/H^2 := by positivity
  have hpos : (0:ℝ) < 1 + h^2 := by positivity
  have hmain : 1 + h^2 ≤ (1+H^2) * (1 + h^2/H^2) := by
    have hrw : (1+H^2) * (1 + h^2/H^2) = 1 + h^2 + (H^2 + h^2/H^2) := by
      field_simp
      ring
    rw [hrw]
    have : 0 ≤ H^2 + h^2/H^2 := by positivity
    linarith
  rw [show (1+H^2) * (1+h^2)⁻¹ = (1+H^2)/(1+h^2) by rw [div_eq_mul_inv],
      show (1 + h^2/H^2)⁻¹ = 1/(1+h^2/H^2) by rw [one_div],
      div_le_div_iff₀ hLpos hpos]
  simpa using hmain

/-- Pointwise form of the weight comparison, for `sec9Uwt`. -/
lemma sec9Uwt_le (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    Work.FIArea2.sec9Uwt Pa h1 h2
      ≤ (1 + (Work.FIPlan.Hscale Pa.M Pa.N)^2)^2
        * ((1 + (h1:ℝ)^2)⁻¹ * (1 + (h2:ℝ)^2)⁻¹) := by
  have hMpos : 0 < Pa.M := by linarith [Pa.hM1]
  have hNpos : 0 < Pa.N := by linarith [Pa.hN1]
  have hHpos : 0 < Work.FIPlan.Hscale Pa.M Pa.N := by
    unfold Work.FIPlan.Hscale; positivity
  have e1 := inv_one_add_div_sq_le (Work.FIPlan.Hscale Pa.M Pa.N) (h1:ℝ) hHpos
  have e2 := inv_one_add_div_sq_le (Work.FIPlan.Hscale Pa.M Pa.N) (h2:ℝ) hHpos
  have hA2nn : (0:ℝ) ≤ (1 + (h2:ℝ)^2/(Work.FIPlan.Hscale Pa.M Pa.N)^2)⁻¹ :=
    inv_nonneg.mpr (by positivity)
  have hB1nn : (0:ℝ) ≤ (1+(Work.FIPlan.Hscale Pa.M Pa.N)^2) * (1+(h1:ℝ)^2)⁻¹ := by positivity
  rw [Work.FIArea2.sec9Uwt]
  refine (mul_le_mul e1 e2 hA2nn hB1nn).trans (le_of_eq ?_)
  ring

/-- The divisor bound in the `τ₄` form: `τ(m)⁴ ≤ Cd⁴(|u₁|^{1/4}|h₁|^{1/2}+|u₂|^{1/4}|h₂|^{1/2})`
for `m = |u₁h₁² − u₂h₂²|`. -/
lemma tau4_le (Cd : ℝ) (hCdpos : 0 < Cd)
    (hCd : ∀ n : ℕ, ((n.divisors.card : ℝ)) ≤ Cd * (n:ℝ)^((1:ℝ)/16))
    (u1 u2 h1 h2 : ℤ) :
    ((((u1 * h1^2 - u2*h2^2).natAbs.divisors.card : ℝ))^4)
      ≤ Cd^4 * ( |(u1:ℝ)|^((1:ℝ)/4) * |(h1:ℝ)|^((1:ℝ)/2)
               + |(u2:ℝ)|^((1:ℝ)/4) * |(h2:ℝ)|^((1:ℝ)/2) ) := by
  set m : ℕ := (u1 * h1^2 - u2*h2^2).natAbs with hm
  have hmcast : (m:ℝ) = |(u1:ℝ)*(h1:ℝ)^2 - (u2:ℝ)*(h2:ℝ)^2| := by
    rw [hm]; simp
  have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
  have hmle : (m:ℝ) ≤ |(u1:ℝ)| * (h1:ℝ)^2 + |(u2:ℝ)| * (h2:ℝ)^2 := by
    rw [hmcast]
    calc |(u1:ℝ)*(h1:ℝ)^2 - (u2:ℝ)*(h2:ℝ)^2|
        = |(u1:ℝ)*(h1:ℝ)^2 + (-((u2:ℝ)*(h2:ℝ)^2))| := by rw [sub_eq_add_neg]
      _ ≤ |(u1:ℝ)*(h1:ℝ)^2| + |((u2:ℝ)*(h2:ℝ)^2)| := by
          have hh := abs_add_le ((u1:ℝ)*(h1:ℝ)^2) (-((u2:ℝ)*(h2:ℝ)^2))
          rwa [abs_neg] at hh
      _ = |(u1:ℝ)| * (h1:ℝ)^2 + |(u2:ℝ)| * (h2:ℝ)^2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (h1:ℝ)),
              abs_of_nonneg (sq_nonneg (h2:ℝ))]
  have hA0 : 0 ≤ |(u1:ℝ)| * (h1:ℝ)^2 := by positivity
  have hB0 : 0 ≤ |(u2:ℝ)| * (h2:ℝ)^2 := by positivity
  have hs1 : ((h1:ℝ)^2)^((1:ℝ)/4) = |(h1:ℝ)|^((1:ℝ)/2) := by
    rw [show (1:ℝ)/4 = (1/2:ℝ)*(1/2) by norm_num, Real.rpow_mul (sq_nonneg (h1:ℝ))]
    rw [show ((h1:ℝ)^2)^((1:ℝ)/2) = |(h1:ℝ)| by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]]
  have hs2 : ((h2:ℝ)^2)^((1:ℝ)/4) = |(h2:ℝ)|^((1:ℝ)/2) := by
    rw [show (1:ℝ)/4 = (1/2:ℝ)*(1/2) by norm_num, Real.rpow_mul (sq_nonneg (h2:ℝ))]
    rw [show ((h2:ℝ)^2)^((1:ℝ)/2) = |(h2:ℝ)| by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]]
  have hstep1 : (m:ℝ)^((1:ℝ)/4)
      ≤ (|(u1:ℝ)| * (h1:ℝ)^2 + |(u2:ℝ)| * (h2:ℝ)^2)^((1:ℝ)/4) :=
    Real.rpow_le_rpow hmnn hmle (by norm_num)
  have hstep2 : (|(u1:ℝ)| * (h1:ℝ)^2 + |(u2:ℝ)| * (h2:ℝ)^2)^((1:ℝ)/4)
      ≤ (|(u1:ℝ)| * (h1:ℝ)^2)^((1:ℝ)/4) + (|(u2:ℝ)| * (h2:ℝ)^2)^((1:ℝ)/4) :=
    Real.rpow_add_le_add_rpow hA0 hB0 (by norm_num) (by norm_num)
  have hstep3 : (|(u1:ℝ)| * (h1:ℝ)^2)^((1:ℝ)/4)
      = |(u1:ℝ)|^((1:ℝ)/4) * |(h1:ℝ)|^((1:ℝ)/2) := by
    rw [Real.mul_rpow (abs_nonneg _) (sq_nonneg _), hs1]
  have hstep3b : (|(u2:ℝ)| * (h2:ℝ)^2)^((1:ℝ)/4)
      = |(u2:ℝ)|^((1:ℝ)/4) * |(h2:ℝ)|^((1:ℝ)/2) := by
    rw [Real.mul_rpow (abs_nonneg _) (sq_nonneg _), hs2]
  have hfin : (m:ℝ)^((1:ℝ)/4)
      ≤ |(u1:ℝ)|^((1:ℝ)/4) * |(h1:ℝ)|^((1:ℝ)/2)
        + |(u2:ℝ)|^((1:ℝ)/4) * |(h2:ℝ)|^((1:ℝ)/2) := by
    rw [← hstep3, ← hstep3b]
    exact hstep1.trans hstep2
  have htau : (((m.divisors.card : ℝ))^4) ≤ (Cd * (m:ℝ)^((1:ℝ)/16))^4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hCd m) 4
  have hpow : (Cd * (m:ℝ)^((1:ℝ)/16))^4 = Cd^4 * (m:ℝ)^((1:ℝ)/4) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmnn]
    congr 1
    norm_num
  calc (((m.divisors.card : ℝ))^4)
      ≤ (Cd * (m:ℝ)^((1:ℝ)/16))^4 := htau
    _ = Cd^4 * (m:ℝ)^((1:ℝ)/4) := hpow
    _ ≤ Cd^4 * ( |(u1:ℝ)|^((1:ℝ)/4) * |(h1:ℝ)|^((1:ℝ)/2)
                + |(u2:ℝ)|^((1:ℝ)/4) * |(h2:ℝ)|^((1:ℝ)/2) ) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)

set_option maxHeartbeats 1000000 in
theorem summable_Wt_tau4 (Pa : Work.FITop.Params) (u1 u2 : ℤ) :
    Summable (fun h : ℤ × ℤ => Work.FIArea2.sec9Uwt Pa h.1 h.2
      * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)) := by
  obtain ⟨Cd, hCdpos, hCd⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow ((1:ℝ)/16) (by norm_num)
  let K : ℝ := (1 + (Work.FIPlan.Hscale Pa.M Pa.N)^2)^2
  have hKpos : 0 < K := by
    have : (0:ℝ) < 1 + (Work.FIPlan.Hscale Pa.M Pa.N)^2 := by
      have hMpos : 0 < Pa.M := by linarith [Pa.hM1]
      have hNpos : 0 < Pa.N := by linarith [Pa.hN1]
      have : 0 < Work.FIPlan.Hscale Pa.M Pa.N := by unfold Work.FIPlan.Hscale; positivity
      positivity
    exact pow_pos this 2
  have hb : Summable (fun t : ℤ => (1 + (t:ℝ)^2)⁻¹) :=
    (Work.FIArea2.summable_Wt 1 le_rfl).congr (fun t => by simp [Work.FIArea2.Wt])
  have hw : Summable (fun t : ℤ => |(t:ℝ)|^((1:ℝ)/2) * (1 + (t:ℝ)^2)⁻¹) :=
    summable_abs_sqrt_mul_one_add_sq_inv
  have hbnn : ∀ t : ℤ, 0 ≤ (1 + (t:ℝ)^2)⁻¹ := fun t => by positivity
  have hwnn : ∀ t : ℤ, 0 ≤ |(t:ℝ)|^((1:ℝ)/2) * (1 + (t:ℝ)^2)⁻¹ := fun t => by positivity
  have hwb : Summable (fun p : ℤ × ℤ =>
      |(p.1:ℝ)|^((1:ℝ)/2) * (1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹) :=
    Summable.mul_of_nonneg hw hb hwnn hbnn
  have hbw : Summable (fun p : ℤ × ℤ =>
      (1 + (p.1:ℝ)^2)⁻¹ * (|(p.2:ℝ)|^((1:ℝ)/2) * (1 + (p.2:ℝ)^2)⁻¹)) :=
    Summable.mul_of_nonneg hb hw hbnn hwnn
  let G : ℤ × ℤ → ℝ := fun p => K * Cd^4 *
      ( |(u1:ℝ)|^((1:ℝ)/4) * (|(p.1:ℝ)|^((1:ℝ)/2) * (1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹)
      + |(u2:ℝ)|^((1:ℝ)/4) * ((1 + (p.1:ℝ)^2)⁻¹ * (|(p.2:ℝ)|^((1:ℝ)/2) * (1 + (p.2:ℝ)^2)⁻¹)) )
  have hG : Summable G :=
    ((hwb.mul_left (|(u1:ℝ)|^((1:ℝ)/4))).add (hbw.mul_left (|(u2:ℝ)|^((1:ℝ)/4)))).mul_left (K * Cd^4)
  refine Summable.of_nonneg_of_le (f := G) ?_ ?_ hG
  · intro p
    exact mul_nonneg (Work.FIArea2.sec9Uwt_nonneg Pa p.1 p.2) (by positivity)
  · intro p
    have hA : Work.FIArea2.sec9Uwt Pa p.1 p.2
        ≤ K * ((1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹) := sec9Uwt_le Pa p.1 p.2
    have hB := tau4_le Cd hCdpos hCd u1 u2 p.1 p.2
    have hAnn : 0 ≤ K * ((1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹) := by positivity
    have hBnn : 0 ≤ ((((u1 * p.1^2 - u2*p.2^2).natAbs.divisors.card : ℝ))^4) := by positivity
    calc Work.FIArea2.sec9Uwt Pa p.1 p.2
            * ((((u1 * p.1^2 - u2*p.2^2).natAbs.divisors.card : ℝ))^4)
        ≤ (K * ((1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹))
          * (Cd^4 * ( |(u1:ℝ)|^((1:ℝ)/4) * |(p.1:ℝ)|^((1:ℝ)/2)
                    + |(u2:ℝ)|^((1:ℝ)/4) * |(p.2:ℝ)|^((1:ℝ)/2) )) :=
          mul_le_mul hA hB hBnn hAnn
      _ = G p := by
          simp only [G]
          ring

end

end Work.FIArea2.Count
