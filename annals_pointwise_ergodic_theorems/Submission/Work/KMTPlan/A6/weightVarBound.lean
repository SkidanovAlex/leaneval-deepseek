import Mathlib
import Submission.Work.KMTPlan.A6.LowDefs
import Submission.Work.KMTPlan.A6.IntegIdent
import Submission.Work.KMTPlan.A6.WeightVarDefs
import Submission.Work.KMTPlan.A6.VarNormAntitoneBound

set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## 1. Elementary monomial bound -/

theorem abs_pow_le_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) : |u ^ n| ≤ 1 := by
  rw [abs_of_nonneg (pow_nonneg hu0 n)]
  exact pow_le_one₀ hu0 hu1

/-! ## 2. Nonnegativity of the coefficient sums -/

theorem Phi1uConst_nonneg (P : Polynomial ℤ) : 0 ≤ Phi1uConst P :=
  Finset.sum_nonneg fun j _ => abs_nonneg _

theorem Phi1uLip_nonneg (P : Polynomial ℤ) : 0 ≤ Phi1uLip P :=
  Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

theorem Phi2uConst_nonneg (P : Polynomial ℤ) : 0 ≤ Phi2uConst P :=
  Finset.sum_nonneg fun j _ => abs_nonneg _

theorem Phi2uLip_nonneg (P : Polynomial ℤ) : 0 ≤ Phi2uLip P :=
  Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

/-! ## 3. Lipschitz and sup bounds for the coefficient sums -/

theorem Phi1u_lipschitz (P : Polynomial ℤ) {u v : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 1) : |Phi1u P u - Phi1u P v| ≤ Phi1uLip P * |u - v| := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  unfold Phi1u Phi1uLip
  have key : (∑ j ∈ Finset.range P.natDegree, der1Coeff P j * u ^ (P.natDegree - 1 - j))
      - (∑ j ∈ Finset.range P.natDegree, der1Coeff P j * v ^ (P.natDegree - 1 - j))
      = ∑ j ∈ Finset.range P.natDegree,
          der1Coeff P j * (u ^ (P.natDegree - 1 - j) - v ^ (P.natDegree - 1 - j)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  calc |∑ j ∈ Finset.range P.natDegree,
          der1Coeff P j * (u ^ (P.natDegree - 1 - j) - v ^ (P.natDegree - 1 - j))|
      ≤ ∑ j ∈ Finset.range P.natDegree,
          |der1Coeff P j * (u ^ (P.natDegree - 1 - j) - v ^ (P.natDegree - 1 - j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range P.natDegree,
          |der1Coeff P j| * |u ^ (P.natDegree - 1 - j) - v ^ (P.natDegree - 1 - j)| := by
        simp_rw [abs_mul]
    _ ≤ ∑ j ∈ Finset.range P.natDegree,
          |der1Coeff P j| * (((P.natDegree - 1 - j : ℕ) : ℝ) * |u - v|) :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le_one _ hu0 hu1 hv0 hv1) (abs_nonneg _)
    _ = (∑ j ∈ Finset.range P.natDegree,
          |der1Coeff P j| * ((P.natDegree - 1 - j : ℕ) : ℝ)) * |u - v| := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

theorem Phi2u_lipschitz (P : Polynomial ℤ) {u v : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 1) : |Phi2u P u - Phi2u P v| ≤ Phi2uLip P * |u - v| := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  unfold Phi2u Phi2uLip
  have key : (∑ j ∈ Finset.range (P.natDegree - 1), der2Coeff P j * u ^ (P.natDegree - 2 - j))
      - (∑ j ∈ Finset.range (P.natDegree - 1), der2Coeff P j * v ^ (P.natDegree - 2 - j))
      = ∑ j ∈ Finset.range (P.natDegree - 1),
          der2Coeff P j * (u ^ (P.natDegree - 2 - j) - v ^ (P.natDegree - 2 - j)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  calc |∑ j ∈ Finset.range (P.natDegree - 1),
          der2Coeff P j * (u ^ (P.natDegree - 2 - j) - v ^ (P.natDegree - 2 - j))|
      ≤ ∑ j ∈ Finset.range (P.natDegree - 1),
          |der2Coeff P j * (u ^ (P.natDegree - 2 - j) - v ^ (P.natDegree - 2 - j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (P.natDegree - 1),
          |der2Coeff P j| * |u ^ (P.natDegree - 2 - j) - v ^ (P.natDegree - 2 - j)| := by
        simp_rw [abs_mul]
    _ ≤ ∑ j ∈ Finset.range (P.natDegree - 1),
          |der2Coeff P j| * (((P.natDegree - 2 - j : ℕ) : ℝ) * |u - v|) :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le_one _ hu0 hu1 hv0 hv1) (abs_nonneg _)
    _ = (∑ j ∈ Finset.range (P.natDegree - 1),
          |der2Coeff P j| * ((P.natDegree - 2 - j : ℕ) : ℝ)) * |u - v| := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

theorem Phi1u_abs_le (P : Polynomial ℤ) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    |Phi1u P u| ≤ Phi1uConst P := by
  obtain ⟨hu0, hu1⟩ := hu
  unfold Phi1u Phi1uConst
  calc |∑ j ∈ Finset.range P.natDegree, der1Coeff P j * u ^ (P.natDegree - 1 - j)|
      ≤ ∑ j ∈ Finset.range P.natDegree, |der1Coeff P j * u ^ (P.natDegree - 1 - j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range P.natDegree, |der1Coeff P j| * |u ^ (P.natDegree - 1 - j)| := by
        simp_rw [abs_mul]
    _ ≤ ∑ j ∈ Finset.range P.natDegree, |der1Coeff P j| * 1 :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_pow_le_one hu0 hu1 _) (abs_nonneg _)
    _ = ∑ j ∈ Finset.range P.natDegree, |der1Coeff P j| := by simp

theorem Phi2u_abs_le (P : Polynomial ℤ) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    |Phi2u P u| ≤ Phi2uConst P := by
  obtain ⟨hu0, hu1⟩ := hu
  unfold Phi2u Phi2uConst
  calc |∑ j ∈ Finset.range (P.natDegree - 1), der2Coeff P j * u ^ (P.natDegree - 2 - j)|
      ≤ ∑ j ∈ Finset.range (P.natDegree - 1), |der2Coeff P j * u ^ (P.natDegree - 2 - j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (P.natDegree - 1), |der2Coeff P j| * |u ^ (P.natDegree - 2 - j)| := by
        simp_rw [abs_mul]
    _ ≤ ∑ j ∈ Finset.range (P.natDegree - 1), |der2Coeff P j| * 1 :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_pow_le_one hu0 hu1 _) (abs_nonneg _)
    _ = ∑ j ∈ Finset.range (P.natDegree - 1), |der2Coeff P j| := by simp

theorem Phi1u_zero (P : Polynomial ℤ) (hdeg : 1 ≤ P.natDegree) :
    Phi1u P 0 = (P.natDegree : ℝ) * ((P.leadingCoeff : ℤ) : ℝ) := by
  have hmem : P.natDegree - 1 ∈ Finset.range P.natDegree :=
    Finset.mem_range.mpr (by omega)
  unfold Phi1u
  rw [Finset.sum_eq_single (P.natDegree - 1)]
  · rw [Nat.sub_self, pow_zero, mul_one, der1Coeff, Nat.sub_add_cancel hdeg,
      Polynomial.coeff_natDegree]
    push_cast
    ring
  · intro j hj hjne
    rw [Finset.mem_range] at hj
    have hpos : 0 < P.natDegree - 1 - j := by omega
    rw [zero_pow hpos.ne', mul_zero]
  · intro h
    exact absurd hmem h

/-! ## 4. The coefficient expansions of `P'` and `P''` -/

theorem PderivR_eq_sum_range' (P : Polynomial ℤ) (y : ℝ) :
    PderivR P y = ∑ j ∈ Finset.range P.natDegree, der1Coeff P j * y ^ j := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
  · rw [h0, Finset.range_zero, Finset.sum_empty, PderivR,
      Polynomial.derivative_of_natDegree_zero h0]
    simp
  · have hlt : ((P.map (Int.castRingHom ℝ)).derivative).natDegree < P.natDegree := by
      have hnat : (P.map (Int.castRingHom ℝ)).natDegree = P.natDegree :=
        Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ)
          (fun a b h => Int.cast_injective h) P
      rw [← hnat]
      refine lt_of_le_of_lt (Polynomial.natDegree_derivative_le _) ?_
      rw [hnat]
      omega
    rw [PderivR, ← Polynomial.derivative_map, Polynomial.eval_eq_sum_range' hlt y]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_derivative, Polynomial.coeff_map]
    simp only [der1Coeff, Int.coe_castRingHom]
    push_cast
    ring

theorem Pderiv2R_eq_sum_range' (P : Polynomial ℤ) (y : ℝ) :
    Pderiv2R P y = ∑ j ∈ Finset.range (P.natDegree - 1), der2Coeff P j * y ^ j := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
  · have hsum : Finset.range (P.natDegree - 1) = ∅ := by
      rw [Finset.range_eq_empty_iff]
      omega
    rw [hsum, Finset.sum_empty, Pderiv2R,
      Polynomial.derivative_of_natDegree_zero (by omega : P.natDegree = 0)]
    simp
  · by_cases h1 : P.natDegree ≤ 1
    · have hd0 : P.derivative.natDegree = 0 := by
        have := Polynomial.natDegree_derivative_le P
        omega
      have hsum : Finset.range (P.natDegree - 1) = ∅ := by
        rw [Finset.range_eq_empty_iff]
        omega
      rw [hsum, Finset.sum_empty, Pderiv2R,
        Polynomial.derivative_of_natDegree_zero hd0]
      simp
    · have h2 : 2 ≤ P.natDegree := by omega
      have hlt : ((P.map (Int.castRingHom ℝ)).derivative.derivative).natDegree
          < P.natDegree - 1 := by
        have hnat : (P.map (Int.castRingHom ℝ)).natDegree = P.natDegree :=
          Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ)
            (fun a b h => Int.cast_injective h) P
        have ha : ((P.map (Int.castRingHom ℝ)).derivative.derivative).natDegree
            ≤ (P.map (Int.castRingHom ℝ)).derivative.natDegree - 1 :=
          Polynomial.natDegree_derivative_le _
        have hb : (P.map (Int.castRingHom ℝ)).derivative.natDegree
            ≤ (P.map (Int.castRingHom ℝ)).natDegree - 1 :=
          Polynomial.natDegree_derivative_le _
        have hc : (P.map (Int.castRingHom ℝ)).derivative.natDegree - 1
            ≤ P.natDegree - 2 := by
          have hbb := Nat.sub_le_sub_right hb 1
          rw [hnat, Nat.sub_sub] at hbb
          exact hbb
        omega
      rw [Pderiv2R, ← Polynomial.derivative_map, ← Polynomial.derivative_map,
        Polynomial.eval_eq_sum_range' hlt y]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative, Polynomial.coeff_map]
      simp only [der2Coeff, Int.coe_castRingHom]
      push_cast
      ring

/-! ## 5. The identities relating the weights to `PderivR` and `Pderiv2R` -/

theorem Phi1u_inv (P : Polynomial ℤ) {y : ℝ} (hy : y ≠ 0) :
    Phi1u P y⁻¹ = PderivR P y / y ^ (P.natDegree - 1) := by
  rw [Phi1u, PderivR_eq_sum_range', Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hjle : j ≤ P.natDegree - 1 := by omega
  have key : y ^ j / y ^ (P.natDegree - 1) = (y⁻¹) ^ (P.natDegree - 1 - j) := by
    rw [inv_pow, pow_sub₀ y hy hjle, mul_inv_rev, inv_inv, div_eq_mul_inv]
  rw [mul_div_assoc, key]

theorem Phi2u_inv (P : Polynomial ℤ) {y : ℝ} (hy : y ≠ 0) :
    Phi2u P y⁻¹ = Pderiv2R P y / y ^ (P.natDegree - 2) := by
  rw [Phi2u, Pderiv2R_eq_sum_range', Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hjle : j ≤ P.natDegree - 2 := by omega
  have key : y ^ j / y ^ (P.natDegree - 2) = (y⁻¹) ^ (P.natDegree - 2 - j) := by
    rw [inv_pow, pow_sub₀ y hy hjle, mul_inv_rev, inv_inv, div_eq_mul_inv]
  rw [mul_div_assoc, key]

theorem Phi1u_mul (P : Polynomial ℤ) {y : ℝ} (hy : y ≠ 0) :
    PderivR P y = y ^ (P.natDegree - 1) * Phi1u P y⁻¹ := by
  rw [Phi1u_inv P hy, mul_div_cancel₀ _ (pow_ne_zero _ hy)]

theorem Phi2u_mul (P : Polynomial ℤ) {y : ℝ} (hy : y ≠ 0) :
    Pderiv2R P y = y ^ (P.natDegree - 2) * Phi2u P y⁻¹ := by
  rw [Phi2u_inv P hy, mul_div_cancel₀ _ (pow_ne_zero _ hy)]

theorem seq3_identity (P : Polynomial ℤ) (hdeg : 1 ≤ P.natDegree) {y : ℝ} (hy : 0 < y) :
    y ^ P.natDegree * Pderiv2R P y / (PderivR P y) ^ 2
      = Phi2u P y⁻¹ / (Phi1u P y⁻¹) ^ 2 := by
  have hyne : y ≠ 0 := ne_of_gt hy
  by_cases h2 : 2 ≤ P.natDegree
  · rw [Phi1u_mul P hyne, Phi2u_mul P hyne]
    have hkey : y ^ P.natDegree * y ^ (P.natDegree - 2) = (y ^ (P.natDegree - 1)) ^ 2 := by
      rw [← pow_add, ← pow_mul]
      congr 1
      omega
    rw [mul_pow, ← mul_assoc, hkey,
      mul_div_mul_left _ _ (pow_ne_zero 2 (pow_ne_zero _ hyne))]
  · have hd1 : P.natDegree = 1 := by omega
    have hd0 : P.derivative.natDegree = 0 := by
      have := Polynomial.natDegree_derivative_le P
      omega
    have hz : Pderiv2R P y = 0 := by
      rw [Pderiv2R, Polynomial.derivative_of_natDegree_zero hd0]
      simp
    have hrange : P.natDegree - 1 = 0 := by omega
    rw [hz, hd1]
    simp only [Phi2u]
    rw [hrange]
    simp

/-! ## 6. Lipschitz bounds for the reciprocal and the quotient -/

theorem Phi1u_inv_lipschitz (P : Polynomial ℤ) {u v c : ℝ} (hc : 0 < c)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hlu : c ≤ |Phi1u P u|) (hlv : c ≤ |Phi1u P v|) :
    |(Phi1u P u)⁻¹ - (Phi1u P v)⁻¹| ≤ Phi1uLip P / c ^ 2 * |u - v| := by
  have hKq : 0 ≤ Phi1uLip P := Phi1uLip_nonneg P
  have hlips := Phi1u_lipschitz P hu hv
  have hpu : 0 < |Phi1u P u| := lt_of_lt_of_le hc hlu
  have hpv : 0 < |Phi1u P v| := lt_of_lt_of_le hc hlv
  have ha : Phi1u P u ≠ 0 := by intro h; rw [h] at hpu; simp at hpu
  have hb : Phi1u P v ≠ 0 := by intro h; rw [h] at hpv; simp at hpv
  have hden' : c ^ 2 ≤ |Phi1u P u| * |Phi1u P v| := by
    have hcc : c * c ≤ |Phi1u P u| * |Phi1u P v| :=
      mul_le_mul hlu hlv (le_of_lt hc) (abs_nonneg _)
    nlinarith
  have hstep : |Phi1u P u - Phi1u P v| / (|Phi1u P u| * |Phi1u P v|)
      ≤ (Phi1uLip P * |u - v|) / c ^ 2 :=
    div_le_div₀ (mul_nonneg hKq (abs_nonneg _)) hlips (by positivity) hden'
  calc |(Phi1u P u)⁻¹ - (Phi1u P v)⁻¹|
      = |Phi1u P u - Phi1u P v| / (|Phi1u P u| * |Phi1u P v|) := by
        rw [inv_sub_inv ha hb, abs_div, abs_mul, abs_sub_comm (Phi1u P v) (Phi1u P u)]
    _ ≤ (Phi1uLip P * |u - v|) / c ^ 2 := hstep
    _ = Phi1uLip P / c ^ 2 * |u - v| := by ring

theorem Phi_quo_lipschitz (P : Polynomial ℤ) {u v c : ℝ} (hc : 0 < c)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hlu : c ≤ |Phi1u P u|) (hlv : c ≤ |Phi1u P v|) :
    |Phi2u P u / (Phi1u P u) ^ 2 - Phi2u P v / (Phi1u P v) ^ 2|
      ≤ (Phi2uLip P * (Phi1uConst P) ^ 2 + 2 * Phi2uConst P * Phi1uLip P * Phi1uConst P)
          / c ^ 4 * |u - v| := by
  have hKp : 0 ≤ Phi2uLip P := Phi2uLip_nonneg P
  have hAp : 0 ≤ Phi2uConst P := Phi2uConst_nonneg P
  have hKq : 0 ≤ Phi1uLip P := Phi1uLip_nonneg P
  have hAq : 0 ≤ Phi1uConst P := Phi1uConst_nonneg P
  have hq := Phi1u_lipschitz P hu hv
  have hp := Phi2u_lipschitz P hu hv
  have hAqu := Phi1u_abs_le P hu
  have hAqv := Phi1u_abs_le P hv
  have hpu : 0 < |Phi1u P u| := lt_of_lt_of_le hc hlu
  have hpv : 0 < |Phi1u P v| := lt_of_lt_of_le hc hlv
  have hqu : Phi1u P u ≠ 0 := by intro h; rw [h] at hpu; simp at hpu
  have hqv : Phi1u P v ≠ 0 := by intro h; rw [h] at hpv; simp at hpv
  have hd : (0:ℝ) < |Phi1u P u| ^ 2 * |Phi1u P v| ^ 2 := by positivity
  have hd' : c ^ 4 ≤ |Phi1u P u| ^ 2 * |Phi1u P v| ^ 2 := by
    have hcc : c * c ≤ |Phi1u P u| * |Phi1u P v| :=
      mul_le_mul hlu hlv (le_of_lt hc) (abs_nonneg _)
    have h4 := mul_le_mul hcc hcc (mul_nonneg (le_of_lt hc) (le_of_lt hc))
      (by positivity : (0:ℝ) ≤ |Phi1u P u| * |Phi1u P v|)
    nlinarith
  have hnum : |Phi2u P u * (Phi1u P v) ^ 2 - (Phi1u P u) ^ 2 * Phi2u P v|
      ≤ (Phi2uLip P * (Phi1uConst P) ^ 2 + 2 * Phi2uConst P * Phi1uLip P * Phi1uConst P)
          * |u - v| := by
    have hsplit : Phi2u P u * (Phi1u P v) ^ 2 - (Phi1u P u) ^ 2 * Phi2u P v
        = (Phi2u P u - Phi2u P v) * (Phi1u P v) ^ 2
          + Phi2u P v * ((Phi1u P v) ^ 2 - (Phi1u P u) ^ 2) := by ring
    have h1 : |(Phi2u P u - Phi2u P v) * (Phi1u P v) ^ 2|
        ≤ Phi2uLip P * |u - v| * (Phi1uConst P) ^ 2 := by
      rw [abs_mul, abs_pow]
      have h2 : |Phi1u P v| ^ 2 ≤ (Phi1uConst P) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hAqv 2
      have h3 : 0 ≤ Phi2uLip P * |u - v| := mul_nonneg hKp (abs_nonneg _)
      calc |Phi2u P u - Phi2u P v| * |Phi1u P v| ^ 2
          ≤ (Phi2uLip P * |u - v|) * (Phi1uConst P) ^ 2 :=
            mul_le_mul hp h2 (pow_nonneg (abs_nonneg _) 2) h3
        _ = Phi2uLip P * |u - v| * (Phi1uConst P) ^ 2 := by ring
    have h2 : |Phi2u P v * ((Phi1u P v) ^ 2 - (Phi1u P u) ^ 2)|
        ≤ Phi2uConst P * (2 * Phi1uConst P * Phi1uLip P * |u - v|) := by
      rw [abs_mul]
      have hd2 : |(Phi1u P v) ^ 2 - (Phi1u P u) ^ 2|
          ≤ 2 * Phi1uConst P * Phi1uLip P * |u - v| := by
        have hfac : (Phi1u P v) ^ 2 - (Phi1u P u) ^ 2
            = (Phi1u P v - Phi1u P u) * (Phi1u P v + Phi1u P u) := by ring
        rw [hfac, abs_mul, abs_sub_comm (Phi1u P v) (Phi1u P u)]
        have hsum : |Phi1u P v + Phi1u P u| ≤ 2 * Phi1uConst P := by
          calc |Phi1u P v + Phi1u P u| ≤ |Phi1u P v| + |Phi1u P u| := abs_add_le _ _
            _ ≤ Phi1uConst P + Phi1uConst P := add_le_add hAqv hAqu
            _ = 2 * Phi1uConst P := by ring
        calc |Phi1u P u - Phi1u P v| * |Phi1u P v + Phi1u P u|
            ≤ (Phi1uLip P * |u - v|) * (2 * Phi1uConst P) :=
              mul_le_mul hq hsum (abs_nonneg _) (mul_nonneg hKq (abs_nonneg _))
          _ = 2 * Phi1uConst P * Phi1uLip P * |u - v| := by ring
      exact mul_le_mul (Phi2u_abs_le P hv) hd2 (abs_nonneg _) hAp
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add h1 h2) |>.trans ?_
    nlinarith [abs_nonneg (u - v), hKp, hAp, hKq, hAq, sq_nonneg (Phi1uConst P)]
  calc |Phi2u P u / (Phi1u P u) ^ 2 - Phi2u P v / (Phi1u P v) ^ 2|
      = |Phi2u P u * (Phi1u P v) ^ 2 - (Phi1u P u) ^ 2 * Phi2u P v|
          / (|Phi1u P u| ^ 2 * |Phi1u P v| ^ 2) := by
        rw [div_sub_div (Phi2u P u) (Phi2u P v) (pow_ne_zero 2 hqu) (pow_ne_zero 2 hqv),
          abs_div, abs_mul, abs_pow, abs_pow]
    _ ≤ (Phi2uLip P * (Phi1uConst P) ^ 2 + 2 * Phi2uConst P * Phi1uLip P * Phi1uConst P)
          * |u - v| / c ^ 4 :=
        div_le_div₀ (mul_nonneg (add_nonneg (mul_nonneg hKp (sq_nonneg _)) (by positivity))
            (abs_nonneg _)) hnum (by positivity) hd'
    _ = (Phi2uLip P * (Phi1uConst P) ^ 2 + 2 * Phi2uConst P * Phi1uLip P * Phi1uConst P)
          / c ^ 4 * |u - v| := by ring


/-! ## 7. Elementary helpers used by the assembly -/

theorem abs_sub_abs_le' (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  have h1 : |a| ≤ |b| + |a - b| := by
    calc |a| = |b + (a - b)| := by ring_nf
      _ ≤ |b| + |a - b| := abs_add_le _ _
  linarith

theorem norm_ofReal_complex (z : ℝ) : ‖((z : ℂ))‖ = |z| := by simp

theorem inv_pow_abs_le_two_pow {t : ℝ} (ht1 : (1 : ℝ) / 2 ≤ t) (e : ℕ) :
    |(t ^ e)⁻¹| ≤ (2 : ℝ) ^ e := by
  have htpos : 0 < t := by linarith
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg htpos.le e))]
  have h1 : ((1 : ℝ) / 2) ^ e ≤ t ^ e := pow_le_pow_left₀ (by norm_num) ht1 e
  have h2 : 0 < ((1 : ℝ) / 2) ^ e := by positivity
  have h3 : (((1 : ℝ) / 2) ^ e)⁻¹ = (2 : ℝ) ^ e := by
    rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]
  rw [← h3]
  exact (inv_le_inv₀ (pow_pos htpos e) h2).mpr h1

/-! ## 8. The target -/


open MeasureTheory Polynomial Finset Filter Topology in
open scoped ENNReal NNReal BigOperators in
theorem weightVarBound (P : Polynomial ℤ) (hdeg : 1 ≤ P.natDegree) (r : NNReal)
    (hr : 1 ≤ r) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (t : ℝ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, C₀ ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ((Work.KMTPlan.A6.PderivR P ((a n : ℝ) * t)
              / ((a n : ℝ) ^ (P.natDegree - 1)) : ℝ) : ℂ)) ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => (((a n : ℝ) ^ (P.natDegree - 1)
              / Work.KMTPlan.A6.PderivR P ((a n : ℝ) * t) : ℝ) : ℂ)) ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => (((a n : ℝ) ^ P.natDegree
                * Work.KMTPlan.A6.Pderiv2R P ((a n : ℝ) * t)
              / (Work.KMTPlan.A6.PderivR P ((a n : ℝ) * t)) ^ 2 : ℝ) : ℂ))
          ≤ ENNReal.ofReal C := by
  have hPne : P ≠ 0 := by intro h; rw [h] at hdeg; simp at hdeg
  have hlcr : ((P.leadingCoeff : ℤ) : ℝ) ≠ 0 := fun h =>
    hPne (Polynomial.leadingCoeff_eq_zero.mp (Int.cast_eq_zero.mp h))
  set A1 : ℝ := Phi1uConst P with hA1
  set K1 : ℝ := Phi1uLip P with hK1
  set A2 : ℝ := Phi2uConst P with hA2
  set K2 : ℝ := Phi2uLip P with hK2
  have hA1nn : 0 ≤ A1 := by rw [hA1]; exact Phi1uConst_nonneg P
  have hK1nn : 0 ≤ K1 := by rw [hK1]; exact Phi1uLip_nonneg P
  have hA2nn : 0 ≤ A2 := by rw [hA2]; exact Phi2uConst_nonneg P
  have hK2nn : 0 ≤ K2 := by rw [hK2]; exact Phi2uLip_nonneg P
  set v0 : ℝ := (P.natDegree : ℝ) * |((P.leadingCoeff : ℤ) : ℝ)| with hv0
  have hv0pos : 0 < v0 := by
    rw [hv0]
    exact mul_pos (by exact_mod_cast hdeg) (abs_pos.mpr hlcr)
  set R : ℝ := max 1 (2 * K1 / v0) with hR
  have hR1 : 1 ≤ R := by rw [hR]; exact le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRle : 2 * K1 / v0 ≤ R := by rw [hR]; exact le_max_right _ _
  set ρ : ℝ := R⁻¹ with hρ
  have hρpos : 0 < ρ := by rw [hρ]; exact inv_pos.mpr hRpos
  have hρnn : 0 ≤ ρ := le_of_lt hρpos
  have hρ1 : ρ ≤ 1 := by rw [hρ]; exact inv_le_one_of_one_le₀ hR1
  have hK1ρ : K1 * ρ ≤ v0 / 2 := by
    rcases eq_or_lt_of_le hK1nn with h0 | hpos
    · rw [← h0, zero_mul]; linarith
    · have hstep : ρ ≤ v0 / (2 * K1) := by
        rw [hρ, inv_le_comm₀ hRpos (by positivity), inv_div]
        exact hRle
      calc K1 * ρ ≤ K1 * (v0 / (2 * K1)) := mul_le_mul_of_nonneg_left hstep hpos.le
        _ = v0 / 2 := by field_simp <;> ring
  set c : ℝ := v0 / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  set D : ℝ := (2 : ℝ) ^ P.natDegree with hD
  have hD1 : 1 ≤ D := by rw [hD]; exact one_le_pow₀ (by norm_num)
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hDle : (2 : ℝ) ^ (P.natDegree - 1) ≤ D := by
    rw [hD]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  set Cval : ℝ := D * (A1 + K1 * ρ) + (D / c + D * (K1 / c ^ 2) * ρ)
      + (D * (A2 / c ^ 2) + D * ((K2 * A1 ^ 2 + 2 * A2 * K1 * A1) / c ^ 4) * ρ) + 1 with hCval
  have hCvalpos : 0 < Cval := by rw [hCval]; positivity
  have hC1 : A1 + K1 * ρ ≤ Cval := by
    rw [hCval]
    have h1 : A1 + K1 * ρ ≤ D * (A1 + K1 * ρ) := by
      have hnn : 0 ≤ A1 + K1 * ρ := by positivity
      nlinarith [hD1]
    have h2 : 0 ≤ D / c + D * (K1 / c ^ 2) * ρ := by positivity
    have h3 : 0 ≤ D * (A2 / c ^ 2) + D * ((K2 * A1 ^ 2 + 2 * A2 * K1 * A1) / c ^ 4) * ρ := by
      positivity
    linarith
  have hC2 : D / c + D * (K1 / c ^ 2) * ρ ≤ Cval := by
    rw [hCval]
    have h1 : 0 ≤ D * (A1 + K1 * ρ) := by positivity
    have h3 : 0 ≤ D * (A2 / c ^ 2) + D * ((K2 * A1 ^ 2 + 2 * A2 * K1 * A1) / c ^ 4) * ρ := by
      positivity
    linarith
  have hC3 : D * (A2 / c ^ 2) + D * ((K2 * A1 ^ 2 + 2 * A2 * K1 * A1) / c ^ 4) * ρ ≤ Cval := by
    rw [hCval]
    have h1 : 0 ≤ D * (A1 + K1 * ρ) := by positivity
    have h2 : 0 ≤ D / c + D * (K1 / c ^ 2) * ρ := by positivity
    linarith
  refine ⟨2 * R, by positivity, Cval, hCvalpos, ?_⟩
  intro a Λ t hΛ hlac ha ht
  obtain ⟨ht1, ht2⟩ := ht
  have htpos : 0 < t := by linarith
  have h2R : (0 : ℝ) < 2 * R := by positivity
  have hane : ∀ n, (a n : ℝ) ≠ 0 := fun n =>
    ne_of_gt (lt_of_lt_of_le h2R (ha n))
  have hypos : ∀ n, 0 < (a n : ℝ) * t := fun n =>
    mul_pos (lt_of_lt_of_le h2R (ha n)) htpos
  have hylow : ∀ n, R ≤ (a n : ℝ) * t := fun n => by
    have h := ha n
    nlinarith [ht1]
  have hyne : ∀ n, ((a n : ℝ) * t) ≠ 0 := fun n => ne_of_gt (hypos n)
  have hynn : ∀ n, 0 ≤ ((a n : ℝ) * t)⁻¹ := fun n => le_of_lt (inv_pos.mpr (hypos n))
  have hyle : ∀ n, ((a n : ℝ) * t)⁻¹ ≤ ρ := fun n => by
    rw [hρ]
    exact (inv_le_inv₀ (hypos n) hRpos).mpr (hylow n)
  have hyle1 : ∀ n, ((a n : ℝ) * t)⁻¹ ≤ 1 := fun n => (hyle n).trans hρ1
  have ha_pos : ∀ n, 0 < a n := fun n => NNReal.coe_pos.mp (lt_of_lt_of_le h2R (ha n))
  have ha_succ : ∀ n, a n < a (n + 1) := fun n => by
    have h1 : (1 : NNReal) < a (n + 1) / a n := lt_trans hΛ (hlac n)
    calc a n = 1 * a n := (one_mul _).symm
      _ < (a (n + 1) / a n) * a n := mul_lt_mul_of_pos_right h1 (ha_pos n)
      _ = a (n + 1) := div_mul_cancel₀ _ (ne_of_gt (ha_pos n))
  have ha_mono : Monotone fun n => (a n : ℝ) := by
    refine monotone_nat_of_le_succ fun n => ?_
    exact_mod_cast (le_of_lt (ha_succ n))
  have hu_anti : Antitone fun n : ℕ => ((a n : ℝ) * t)⁻¹ := by
    intro m n hmn
    rw [inv_le_inv₀ (mul_pos (lt_of_lt_of_le h2R (ha n)) htpos)
      (mul_pos (lt_of_lt_of_le h2R (ha m)) htpos)]
    exact mul_le_mul_of_nonneg_right (ha_mono hmn) htpos.le
  -- the sup bound for `Phi1u P 0`
  have hPhi1zero_abs : |Phi1u P 0| = v0 := by
    rw [Phi1u_zero P hdeg, hv0, abs_mul, abs_of_nonneg (Nat.cast_nonneg P.natDegree)]
  -- the lower bound for `|Phi1u|` along the sequence
  have hPhi1low : ∀ n, c ≤ |Phi1u P (((a n : ℝ) * t)⁻¹)| := by
    intro n
    have h0 : |Phi1u P (((a n : ℝ) * t)⁻¹) - Phi1u P 0| ≤ K1 * (((a n : ℝ) * t)⁻¹) := by
      have hlip := Phi1u_lipschitz P (u := ((a n : ℝ) * t)⁻¹) (v := 0)
        ⟨hynn n, hyle1 n⟩ ⟨le_refl 0, by norm_num⟩
      rw [← hK1] at hlip
      rwa [sub_zero, abs_of_nonneg (hynn n)] at hlip
    have h0' : |Phi1u P 0 - Phi1u P (((a n : ℝ) * t)⁻¹)| ≤ K1 * (((a n : ℝ) * t)⁻¹) := by
      rwa [abs_sub_comm] at h0
    have hrt := abs_sub_abs_le' (Phi1u P 0) (Phi1u P 0 - Phi1u P (((a n : ℝ) * t)⁻¹))
    rw [show Phi1u P 0 - (Phi1u P 0 - Phi1u P (((a n : ℝ) * t)⁻¹))
        = Phi1u P (((a n : ℝ) * t)⁻¹) from by ring] at hrt
    have h1 : K1 * (((a n : ℝ) * t)⁻¹) ≤ K1 * ρ := mul_le_mul_of_nonneg_left (hyle n) hK1nn
    rw [hc]
    linarith [hrt, h0', h1, hK1ρ, hPhi1zero_abs]
  -- ### the first sequence
  have hkey1 : ∀ n : ℕ, PderivR P ((a n : ℝ) * t) / ((a n : ℝ) ^ (P.natDegree - 1))
      = t ^ (P.natDegree - 1) * Phi1u P (((a n : ℝ) * t)⁻¹) := by
    intro n
    have h := Phi1u_inv P (hyne n)
    rw [mul_pow] at h
    rw [h]
    have htne : t ^ (P.natDegree - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt htpos)
    have hane' : (a n : ℝ) ^ (P.natDegree - 1) ≠ 0 := pow_ne_zero _ (hane n)
    field_simp <;> ring
  have hTinv : |(t ^ (P.natDegree - 1))⁻¹| ≤ D :=
    (inv_pow_abs_le_two_pow ht1 (P.natDegree - 1)).trans hDle
  have hsup1 : ∀ n : ℕ,
      ‖((t ^ (P.natDegree - 1) * Phi1u P (((a n : ℝ) * t)⁻¹) : ℝ) : ℂ)‖ ≤ A1 := by
    intro n
    rw [norm_ofReal_complex, abs_mul]
    have h1 : |t ^ (P.natDegree - 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg htpos.le _)]
      exact pow_le_one₀ htpos.le ht2
    have h2 : |Phi1u P (((a n : ℝ) * t)⁻¹)| ≤ A1 := by
      rw [hA1]
      exact Phi1u_abs_le P ⟨hynn n, hyle1 n⟩
    calc |t ^ (P.natDegree - 1)| * |Phi1u P (((a n : ℝ) * t)⁻¹)| ≤ 1 * A1 :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = A1 := one_mul A1
  have hstep1 : ∀ n : ℕ,
      ‖((t ^ (P.natDegree - 1) * Phi1u P (((a (n + 1) : ℝ) * t)⁻¹) : ℝ) : ℂ)
        - ((t ^ (P.natDegree - 1) * Phi1u P (((a n : ℝ) * t)⁻¹) : ℝ) : ℂ)‖
      ≤ K1 * ((((a n : ℝ) * t)⁻¹) - (((a (n + 1) : ℝ) * t)⁻¹)) := by
    intro n
    rw [← Complex.ofReal_sub, norm_ofReal_complex]
    have hfac : t ^ (P.natDegree - 1) * Phi1u P (((a (n + 1) : ℝ) * t)⁻¹)
        - t ^ (P.natDegree - 1) * Phi1u P (((a n : ℝ) * t)⁻¹)
        = t ^ (P.natDegree - 1) * (Phi1u P (((a (n + 1) : ℝ) * t)⁻¹)
            - Phi1u P (((a n : ℝ) * t)⁻¹)) := by ring
    rw [hfac, abs_mul]
    have h1 : |t ^ (P.natDegree - 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg htpos.le _)]
      exact pow_le_one₀ htpos.le ht2
    have h2 : |Phi1u P (((a (n + 1) : ℝ) * t)⁻¹) - Phi1u P (((a n : ℝ) * t)⁻¹)|
        ≤ K1 * |(((a (n + 1) : ℝ) * t)⁻¹) - (((a n : ℝ) * t)⁻¹)| := by
      rw [hK1]
      exact Phi1u_lipschitz P ⟨hynn (n + 1), hyle1 (n + 1)⟩ ⟨hynn n, hyle1 n⟩
    have hmono1 : (((a (n + 1) : ℝ) * t)⁻¹) ≤ (((a n : ℝ) * t)⁻¹) := hu_anti (Nat.le_succ n)
    calc |t ^ (P.natDegree - 1)| * |Phi1u P (((a (n + 1) : ℝ) * t)⁻¹)
          - Phi1u P (((a n : ℝ) * t)⁻¹)|
        ≤ 1 * (K1 * |(((a (n + 1) : ℝ) * t)⁻¹) - (((a n : ℝ) * t)⁻¹)|) :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = K1 * ((((a n : ℝ) * t)⁻¹) - (((a (n + 1) : ℝ) * t)⁻¹)) := by
          rw [one_mul, abs_sub_comm (((a (n + 1) : ℝ) * t)⁻¹) (((a n : ℝ) * t)⁻¹),
            abs_of_nonneg (sub_nonneg.mpr hmono1)]
  have hconj1 : PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => ((PderivR P ((a n : ℝ) * t) / ((a n : ℝ) ^ (P.natDegree - 1)) : ℝ) : ℂ))
      ≤ ENNReal.ofReal Cval := by
    have hx : (fun n : ℕ =>
        ((PderivR P ((a n : ℝ) * t) / ((a n : ℝ) ^ (P.natDegree - 1)) : ℝ) : ℂ))
        = fun n : ℕ => ((t ^ (P.natDegree - 1) * Phi1u P (((a n : ℝ) * t)⁻¹) : ℝ) : ℂ) := by
      funext n
      rw [hkey1 n]
    rw [hx]
    refine (VarNormAntitoneBound (r := r) hr (u := fun n : ℕ => ((a n : ℝ) * t)⁻¹)
      (x := fun n : ℕ => ((t ^ (P.natDegree - 1) * Phi1u P (((a n : ℝ) * t)⁻¹) : ℝ) : ℂ))
      (B := A1) (K := K1) (ρ := ρ) hρnn hynn hyle hu_anti hA1nn hK1nn hsup1 hstep1).trans ?_
    exact ENNReal.ofReal_le_ofReal hC1
  -- ### the second sequence
  have hkey2 : ∀ n : ℕ, (a n : ℝ) ^ (P.natDegree - 1) / PderivR P ((a n : ℝ) * t)
      = (t ^ (P.natDegree - 1))⁻¹ * (Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹ := by
    intro n
    have h := Phi1u_inv P (hyne n)
    rw [mul_pow] at h
    rcases eq_or_ne (PderivR P ((a n : ℝ) * t)) 0 with hX | hX
    · have hz : Phi1u P (((a n : ℝ) * t)⁻¹) = 0 := by
        rw [h, hX]
        simp
      rw [hz, hX]
      simp
    · rw [h, inv_div]
      have htne : t ^ (P.natDegree - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt htpos)
      have hane' : (a n : ℝ) ^ (P.natDegree - 1) ≠ 0 := pow_ne_zero _ (hane n)
      field_simp <;> ring
  have hsup2 : ∀ n : ℕ,
      ‖(((t ^ (P.natDegree - 1))⁻¹ * (Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹ : ℝ) : ℂ)‖
        ≤ D / c := by
    intro n
    rw [norm_ofReal_complex, abs_mul]
    have h1 : |(t ^ (P.natDegree - 1))⁻¹| ≤ D := hTinv
    have h2 : |(Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹| ≤ 1 / c := by
      rw [abs_inv, one_div]
      exact (inv_le_inv₀ (lt_of_lt_of_le hcpos (hPhi1low n)) hcpos).mpr (hPhi1low n)
    calc |(t ^ (P.natDegree - 1))⁻¹| * |(Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹| ≤ D * (1 / c) :=
          mul_le_mul h1 h2 (abs_nonneg _) hDpos.le
      _ = D / c := by ring
  have hstep2 : ∀ n : ℕ,
      ‖(((t ^ (P.natDegree - 1))⁻¹ * (Phi1u P (((a (n + 1) : ℝ) * t)⁻¹))⁻¹ : ℝ) : ℂ)
        - (((t ^ (P.natDegree - 1))⁻¹ * (Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹ : ℝ) : ℂ)‖
      ≤ (D * (K1 / c ^ 2)) * ((((a n : ℝ) * t)⁻¹) - (((a (n + 1) : ℝ) * t)⁻¹)) := by
    intro n
    rw [← Complex.ofReal_sub, norm_ofReal_complex]
    have hfac : (t ^ (P.natDegree - 1))⁻¹ * (Phi1u P (((a (n + 1) : ℝ) * t)⁻¹))⁻¹
        - (t ^ (P.natDegree - 1))⁻¹ * (Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹
        = (t ^ (P.natDegree - 1))⁻¹ * ((Phi1u P (((a (n + 1) : ℝ) * t)⁻¹))⁻¹
            - (Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹) := by ring
    rw [hfac, abs_mul]
    have h2 : |(Phi1u P (((a (n + 1) : ℝ) * t)⁻¹))⁻¹ - (Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹|
        ≤ K1 / c ^ 2 * |(((a (n + 1) : ℝ) * t)⁻¹) - (((a n : ℝ) * t)⁻¹)| := by
      rw [hK1]
      exact Phi1u_inv_lipschitz P hcpos ⟨hynn (n + 1), hyle1 (n + 1)⟩ ⟨hynn n, hyle1 n⟩
        (hPhi1low (n + 1)) (hPhi1low n)
    have hmono1 : (((a (n + 1) : ℝ) * t)⁻¹) ≤ (((a n : ℝ) * t)⁻¹) := hu_anti (Nat.le_succ n)
    calc |(t ^ (P.natDegree - 1))⁻¹|
          * |(Phi1u P (((a (n + 1) : ℝ) * t)⁻¹))⁻¹ - (Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹|
        ≤ D * (K1 / c ^ 2 * |(((a (n + 1) : ℝ) * t)⁻¹) - (((a n : ℝ) * t)⁻¹)|) :=
          mul_le_mul hTinv h2 (abs_nonneg _) hDpos.le
      _ = (D * (K1 / c ^ 2)) * ((((a n : ℝ) * t)⁻¹) - (((a (n + 1) : ℝ) * t)⁻¹)) := by
          rw [abs_sub_comm (((a (n + 1) : ℝ) * t)⁻¹) (((a n : ℝ) * t)⁻¹),
            abs_of_nonneg (sub_nonneg.mpr hmono1)]
          ring
  have hconj2 : PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => (((a n : ℝ) ^ (P.natDegree - 1) / PderivR P ((a n : ℝ) * t) : ℝ) : ℂ))
      ≤ ENNReal.ofReal Cval := by
    have hx : (fun n : ℕ => (((a n : ℝ) ^ (P.natDegree - 1) / PderivR P ((a n : ℝ) * t) : ℝ) : ℂ))
        = fun n : ℕ => (((t ^ (P.natDegree - 1))⁻¹ * (Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹ : ℝ) : ℂ) := by
      funext n
      rw [hkey2 n]
    rw [hx]
    refine (VarNormAntitoneBound (r := r) hr (u := fun n : ℕ => ((a n : ℝ) * t)⁻¹)
      (x := fun n : ℕ => (((t ^ (P.natDegree - 1))⁻¹ * (Phi1u P (((a n : ℝ) * t)⁻¹))⁻¹ : ℝ) : ℂ))
      (B := D / c) (K := D * (K1 / c ^ 2)) (ρ := ρ) hρnn hynn hyle hu_anti
      (by positivity) (by positivity) hsup2 hstep2).trans ?_
    exact ENNReal.ofReal_le_ofReal hC2
  -- ### the third sequence
  have hTinvd : |(t ^ P.natDegree)⁻¹| ≤ D := by
    rw [hD]
    exact inv_pow_abs_le_two_pow ht1 P.natDegree
  have hkey3 : ∀ n : ℕ, (a n : ℝ) ^ P.natDegree * Pderiv2R P ((a n : ℝ) * t)
        / (PderivR P ((a n : ℝ) * t)) ^ 2
      = (t ^ P.natDegree)⁻¹ * (Phi2u P (((a n : ℝ) * t)⁻¹)
          / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2) := by
    intro n
    have h3 := seq3_identity P hdeg (hypos n)
    have h1 : (t ^ P.natDegree)⁻¹ * (((a n : ℝ) * t) ^ P.natDegree)
        = (a n : ℝ) ^ P.natDegree := by
      rw [← inv_pow, ← mul_pow, mul_comm ((a n : ℝ)) t,
        inv_mul_cancel_left₀ (ne_of_gt htpos)]
    have hassoc : ((t ^ P.natDegree)⁻¹ * ((a n : ℝ) * t) ^ P.natDegree)
          * Pderiv2R P ((a n : ℝ) * t) / (PderivR P ((a n : ℝ) * t)) ^ 2
        = (t ^ P.natDegree)⁻¹ * (((a n : ℝ) * t) ^ P.natDegree
            * Pderiv2R P ((a n : ℝ) * t) / (PderivR P ((a n : ℝ) * t)) ^ 2) := by
      simp only [div_eq_mul_inv]
      ring
    rw [← h1, hassoc, h3]
  have hsup3 : ∀ n : ℕ,
      ‖(((t ^ P.natDegree)⁻¹ * (Phi2u P (((a n : ℝ) * t)⁻¹)
        / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2) : ℝ) : ℂ)‖ ≤ D * (A2 / c ^ 2) := by
    intro n
    rw [norm_ofReal_complex, abs_mul]
    have h2 : |Phi2u P (((a n : ℝ) * t)⁻¹) / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2|
        ≤ A2 / c ^ 2 := by
      rw [abs_div, abs_pow, hA2]
      have hq : c ^ 2 ≤ |Phi1u P (((a n : ℝ) * t)⁻¹)| ^ 2 :=
        pow_le_pow_left₀ hcpos.le (hPhi1low n) 2
      exact div_le_div₀ hA2nn (Phi2u_abs_le P ⟨hynn n, hyle1 n⟩) (by positivity) hq
    exact mul_le_mul hTinvd h2 (abs_nonneg _) hDpos.le
  have hstep3 : ∀ n : ℕ,
      ‖(((t ^ P.natDegree)⁻¹ * (Phi2u P (((a (n + 1) : ℝ) * t)⁻¹)
          / (Phi1u P (((a (n + 1) : ℝ) * t)⁻¹)) ^ 2) : ℝ) : ℂ)
        - (((t ^ P.natDegree)⁻¹ * (Phi2u P (((a n : ℝ) * t)⁻¹)
          / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2) : ℝ) : ℂ)‖
      ≤ (D * ((K2 * A1 ^ 2 + 2 * A2 * K1 * A1) / c ^ 4))
          * ((((a n : ℝ) * t)⁻¹) - (((a (n + 1) : ℝ) * t)⁻¹)) := by
    intro n
    rw [← Complex.ofReal_sub, norm_ofReal_complex]
    have hfac : (t ^ P.natDegree)⁻¹ * (Phi2u P (((a (n + 1) : ℝ) * t)⁻¹)
          / (Phi1u P (((a (n + 1) : ℝ) * t)⁻¹)) ^ 2)
        - (t ^ P.natDegree)⁻¹ * (Phi2u P (((a n : ℝ) * t)⁻¹)
          / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2)
        = (t ^ P.natDegree)⁻¹ * ((Phi2u P (((a (n + 1) : ℝ) * t)⁻¹)
            / (Phi1u P (((a (n + 1) : ℝ) * t)⁻¹)) ^ 2)
          - (Phi2u P (((a n : ℝ) * t)⁻¹)
            / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2)) := by ring
    rw [hfac, abs_mul]
    have h2 : |Phi2u P (((a (n + 1) : ℝ) * t)⁻¹)
            / (Phi1u P (((a (n + 1) : ℝ) * t)⁻¹)) ^ 2
          - Phi2u P (((a n : ℝ) * t)⁻¹) / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2|
        ≤ (K2 * A1 ^ 2 + 2 * A2 * K1 * A1) / c ^ 4
          * |(((a (n + 1) : ℝ) * t)⁻¹) - (((a n : ℝ) * t)⁻¹)| := by
      rw [hK2, hA1, hA2, hK1]
      exact Phi_quo_lipschitz P hcpos ⟨hynn (n + 1), hyle1 (n + 1)⟩ ⟨hynn n, hyle1 n⟩
        (hPhi1low (n + 1)) (hPhi1low n)
    have hmono1 : (((a (n + 1) : ℝ) * t)⁻¹) ≤ (((a n : ℝ) * t)⁻¹) := hu_anti (Nat.le_succ n)
    calc |(t ^ P.natDegree)⁻¹| * |Phi2u P (((a (n + 1) : ℝ) * t)⁻¹)
            / (Phi1u P (((a (n + 1) : ℝ) * t)⁻¹)) ^ 2
          - Phi2u P (((a n : ℝ) * t)⁻¹) / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2|
        ≤ D * ((K2 * A1 ^ 2 + 2 * A2 * K1 * A1) / c ^ 4
            * |(((a (n + 1) : ℝ) * t)⁻¹) - (((a n : ℝ) * t)⁻¹)|) :=
          mul_le_mul hTinvd h2 (abs_nonneg _) hDpos.le
      _ = (D * ((K2 * A1 ^ 2 + 2 * A2 * K1 * A1) / c ^ 4))
            * ((((a n : ℝ) * t)⁻¹) - (((a (n + 1) : ℝ) * t)⁻¹)) := by
          rw [abs_sub_comm (((a (n + 1) : ℝ) * t)⁻¹) (((a n : ℝ) * t)⁻¹),
            abs_of_nonneg (sub_nonneg.mpr hmono1)]
          ring
  have hconj3 : PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => (((a n : ℝ) ^ P.natDegree * Pderiv2R P ((a n : ℝ) * t)
        / (PderivR P ((a n : ℝ) * t)) ^ 2 : ℝ) : ℂ)) ≤ ENNReal.ofReal Cval := by
    have hx : (fun n : ℕ => (((a n : ℝ) ^ P.natDegree * Pderiv2R P ((a n : ℝ) * t)
          / (PderivR P ((a n : ℝ) * t)) ^ 2 : ℝ) : ℂ))
        = fun n : ℕ => (((t ^ P.natDegree)⁻¹ * (Phi2u P (((a n : ℝ) * t)⁻¹)
            / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2) : ℝ) : ℂ) := by
      funext n
      rw [hkey3 n]
    rw [hx]
    refine (VarNormAntitoneBound (r := r) hr (u := fun n : ℕ => ((a n : ℝ) * t)⁻¹)
      (x := fun n : ℕ => (((t ^ P.natDegree)⁻¹ * (Phi2u P (((a n : ℝ) * t)⁻¹)
        / (Phi1u P (((a n : ℝ) * t)⁻¹)) ^ 2) : ℝ) : ℂ))
      (B := D * (A2 / c ^ 2)) (K := D * ((K2 * A1 ^ 2 + 2 * A2 * K1 * A1) / c ^ 4))
      (ρ := ρ) hρnn hynn hyle hu_anti (by positivity) (by positivity) hsup3 hstep3).trans ?_
    exact ENNReal.ofReal_le_ofReal hC3
  exact ⟨hconj1, hconj2, hconj3⟩


end

end Work.KMTPlan.A6
