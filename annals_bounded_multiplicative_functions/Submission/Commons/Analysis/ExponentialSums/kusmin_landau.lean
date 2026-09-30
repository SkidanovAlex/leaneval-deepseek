import Mathlib
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test
import Submission.Commons.Analysis.Trig.cot_diff_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Kusmin–Landau inequality (first derivative test)

`Commons.Analysis.ExponentialSums.kusmin_landau` : if `f` is `C¹` on `[A,B]` with
`deriv f` monotone there and `deriv f` at distance `≥ δ > 0` from every integer,
then

    ‖∑_{A < n ≤ B} exp(2πi f(n))‖ ≤ 1/δ.

## Proof outline

1. `band_of_monotone`: a continuous monotone `g` on `[a,b]` that avoids the
   `δ`-neighbourhoods of the integers on `(a,b)` stays inside a single band
   `[k+δ, k+1-δ]` (the image is connected, and the intermediate value theorem
   applied to `g` on subintervals detects any crossing of a forbidden
   neighbourhood).
2. The increments `α_j = f(j+1) - f(j)` (via the mean value theorem) lie in
   `[k+δ, k+1-δ]` and are monotone.
3. Writing `z_j = e(f(j))` and `β_j = α_j - k ∈ [δ,1-δ]` monotone, we have
   `z_{j+1} = z_j · e(β_j)`.  With `u_j = (1 - e(β_j))⁻¹ = 1/2 + (i/2)cot(πβ_j)`
   one has `z_j = (z_j - z_{j+1}) u_j`, and summation by parts gives

       ∑_{j<N} z_j = z_0 u_0 + z_{N-1}(1 - u_{N-2})
                     + ∑_{m<N-2} z_{m+1}(u_{m+1} - u_m).

   The norms are `‖u_j‖ = 1/(2 sin πβ_j) ≤ 1/(4δ)` and
   `‖u_{m+1} - u_m‖ = (1/2)(cot πβ_m - cot πβ_{m+1})`; the latter telescopes by
   monotonicity of `β`, and `cot(πδ) ≤ 1/(2δ)`.  The total is
   `1/(4δ) + 1/(4δ) + cot(πδ) ≤ 1/δ`.
4. The antitone case is reduced to the monotone one by replacing `f` with `-f`
   (complex conjugation of the sum).

All ingredients are proved from Mathlib plus the shared commons
(`Submission.Commons.Analysis.ExponentialSums.second_derivative_test`,
`Submission.Commons.Analysis.Trig.cot_diff_eq`).
-/

namespace Commons.Analysis.ExponentialSums

open Complex
open scoped Real BigOperators ComplexConjugate

noncomputable section

/-! ### Distance to the nearest integer is even -/

lemma intDist_neg (x : ℝ) :
    Submission.VanDerCorput.intDist (-x) = Submission.VanDerCorput.intDist x := by
  change min (Int.fract (-x)) (1 - Int.fract (-x)) = min (Int.fract x) (1 - Int.fract x)
  by_cases h : Int.fract x = 0
  · have hx : x = (⌊x⌋ : ℝ) := by
      have h2 : x - (⌊x⌋ : ℝ) = 0 := by
        rw [Submission.IntDistRegion.sub_floor_eq_fract]; exact h
      linarith
    rw [hx]
    have hz : -(⌊x⌋ : ℝ) = ((-⌊x⌋ : ℤ) : ℝ) := by push_cast; ring
    rw [hz, Int.fract_intCast]
    simp
  · rw [Int.fract_neg h,
      show (1 - (1 - Int.fract x)) = Int.fract x by ring,
      min_comm (Int.fract x) (1 - Int.fract x)]

/-! ### Elementary trigonometry -/

/-- `2δ ≤ sin (πβ)` for `β ∈ [δ, 1-δ]`, `0 < δ ≤ 1/2`. -/
lemma two_mul_le_sin_pi_of_mem {δ β : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2)
    (h2 : δ ≤ β) (h3 : β ≤ 1 - δ) : 2 * δ ≤ Real.sin (Real.pi * β) := by
  have hβ0 : 0 < β := lt_of_lt_of_le h0 h2
  by_cases hβ : β ≤ 1 / 2
  · have hx0 : 0 ≤ Real.pi * β := by positivity
    have hx1 : Real.pi * β ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hβ]
    have h := Real.mul_le_sin hx0 hx1
    have h2' : (2 / Real.pi) * (Real.pi * β) = 2 * β := by field_simp
    rw [h2'] at h
    linarith
  · have hβ' : 1 / 2 < β := lt_of_not_ge hβ
    have ht0 : 0 ≤ Real.pi * (1 - β) := by nlinarith [Real.pi_pos, hβ']
    have ht1 : Real.pi * (1 - β) ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hβ']
    have h := Real.mul_le_sin ht0 ht1
    have h2' : (2 / Real.pi) * (Real.pi * (1 - β)) = 2 * (1 - β) := by field_simp
    rw [h2'] at h
    have hsin : Real.sin (Real.pi * (1 - β)) = Real.sin (Real.pi * β) := by
      have harg : Real.pi * (1 - β) = Real.pi - Real.pi * β := by ring
      rw [harg, Real.sin_pi_sub]
    rw [hsin] at h
    linarith

/-- `cot (πδ) ≤ 1/(2δ)` for `0 < δ ≤ 1/2`. -/
lemma cot_pi_le_inv_two {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) :
    Real.cot (Real.pi * δ) ≤ 1 / (2 * δ) := by
  have hπδ0 : 0 < Real.pi * δ := by positivity
  have hπδ1 : Real.pi * δ < Real.pi := by nlinarith [Real.pi_pos, h1]
  have hsin : 0 < Real.sin (Real.pi * δ) := Real.sin_pos_of_pos_of_lt_pi hπδ0 hπδ1
  have hJ : 2 * δ ≤ Real.sin (Real.pi * δ) := by
    have hx1 : Real.pi * δ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, h1]
    have h := Real.mul_le_sin (le_of_lt hπδ0) hx1
    have h2' : (2 / Real.pi) * (Real.pi * δ) = 2 * δ := by field_simp
    rwa [h2'] at h
  have h2δ : 0 < 2 * δ := by linarith
  rw [Real.cot_eq_cos_div_sin]
  calc Real.cos (Real.pi * δ) / Real.sin (Real.pi * δ)
      ≤ 1 / Real.sin (Real.pi * δ) :=
        div_le_div_of_nonneg_right (Real.cos_le_one _) (le_of_lt hsin)
    _ ≤ 1 / (2 * δ) := div_le_div_of_nonneg_left (by norm_num) h2δ hJ

/-- `cot (π - x) = -cot x`. -/
lemma cot_pi_sub (x : ℝ) : Real.cot (Real.pi - x) = -Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub]
  ring

/-- `cot` is antitone on the rescaled interval `[δ,1-δ]`. -/
lemma cot_pi_antitone_of_le {δ x y : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2)
    (hx : δ ≤ x) (hx' : x ≤ 1 - δ) (hy : δ ≤ y) (hy' : y ≤ 1 - δ) (hxy : x ≤ y) :
    Real.cot (Real.pi * y) ≤ Real.cot (Real.pi * x) := by
  have hx0 : 0 < x := lt_of_lt_of_le h0 hx
  have hy0 : 0 < y := lt_of_lt_of_le h0 hy
  have hπx0 : 0 < Real.pi * x := by positivity
  have hπy0 : 0 < Real.pi * y := by positivity
  have hx1 : x < 1 := by linarith
  have hy1 : y < 1 := by linarith
  have hπx1 : Real.pi * x < Real.pi := by nlinarith [Real.pi_pos]
  have hπy1 : Real.pi * y < Real.pi := by nlinarith [Real.pi_pos]
  have hd := Commons.Analysis.Trig.cot_diff_eq hπx0 hπx1 hπy0 hπy1
  have hsin : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, hxy])
      (by nlinarith [Real.pi_pos, h1, hx, hy'])
  have hden : 0 < Real.sin (Real.pi * x) * Real.sin (Real.pi * y) :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi hπx0 hπx1) (Real.sin_pos_of_pos_of_lt_pi hπy0 hπy1)
  have hnn : 0 ≤ Real.cot (Real.pi * x) - Real.cot (Real.pi * y) := by
    rw [hd]; exact div_nonneg hsin (le_of_lt hden)
  linarith


/-! ### The function `u = (1 - E β)⁻¹` -/

/-- `‖1 - E t‖ = 2 sin (πt)` for `t ∈ [0,1]`. -/
lemma norm_one_sub_E {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖1 - Submission.SdtPoisson.E t‖ = 2 * Real.sin (Real.pi * t) := by
  have hE : Submission.SdtPoisson.E t = cexp (↑(2 * Real.pi * t) * I) := rfl
  rw [hE, Submission.UnitCircle.norm_one_sub_cexp_two_pi]
  rw [abs_of_nonneg]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos, h1])

/-- `1 - E β ≠ 0` for `β ∈ (0,1)`. -/
lemma one_sub_E_ne_zero {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    1 - Submission.SdtPoisson.E β ≠ 0 := by
  intro h
  have hn := norm_one_sub_E (le_of_lt h0) (le_of_lt h1)
  have hsin : 0 < Real.sin (Real.pi * β) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, h1])
  rw [h, norm_zero] at hn
  linarith

/-- `‖(1 - E t)⁻¹‖ = 1/(2 sin (πt))` for `t ∈ (0,1)`. -/
lemma norm_inv_one_sub_E {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ‖(1 - Submission.SdtPoisson.E t)⁻¹‖ = 1 / (2 * Real.sin (Real.pi * t)) := by
  rw [norm_inv, norm_one_sub_E (le_of_lt h0) (le_of_lt h1), inv_eq_one_div]

/-- `‖E t - E s‖ = 2 sin (π(t-s))` for `0 ≤ s ≤ t ≤ 1`. -/
lemma norm_E_sub_E {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ‖Submission.SdtPoisson.E t - Submission.SdtPoisson.E s‖
      = 2 * Real.sin (Real.pi * (t - s)) := by
  have hE : Submission.SdtPoisson.E t
      = Submission.SdtPoisson.E s * Submission.SdtPoisson.E (t - s) := by
    rw [← Submission.SdtPoisson.E_add]
    congr 1
    ring
  have hfac : Submission.SdtPoisson.E s * Submission.SdtPoisson.E (t - s)
        - Submission.SdtPoisson.E s
      = Submission.SdtPoisson.E s * (Submission.SdtPoisson.E (t - s) - 1) := by ring
  rw [hE, hfac, norm_mul, Submission.SdtPoisson.E_norm, one_mul, norm_sub_rev]
  exact norm_one_sub_E (by linarith) (by linarith)

/-- Difference identity for `(1 - E β)⁻¹`: the norm is half the difference of the
cotangents. -/
lemma norm_inv_one_sub_E_sub {s t : ℝ} (h0 : 0 < s) (hst : s ≤ t) (h1 : t < 1) :
    ‖(1 - Submission.SdtPoisson.E s)⁻¹ - (1 - Submission.SdtPoisson.E t)⁻¹‖
      = (1 / 2) * (Real.cot (Real.pi * s) - Real.cot (Real.pi * t)) := by
  have hs1 : s < 1 := by linarith
  have hsne : 1 - Submission.SdtPoisson.E s ≠ 0 := one_sub_E_ne_zero h0 hs1
  have htne : 1 - Submission.SdtPoisson.E t ≠ 0 :=
    one_sub_E_ne_zero (by linarith) h1
  have hkey : (1 - Submission.SdtPoisson.E s)⁻¹ - (1 - Submission.SdtPoisson.E t)⁻¹
      = (Submission.SdtPoisson.E s - Submission.SdtPoisson.E t)
        / ((1 - Submission.SdtPoisson.E s) * (1 - Submission.SdtPoisson.E t)) := by
    field_simp
    ring
  have hnum : ‖Submission.SdtPoisson.E s - Submission.SdtPoisson.E t‖
      = 2 * Real.sin (Real.pi * (t - s)) := by
    rw [norm_sub_rev]
    exact norm_E_sub_E (le_of_lt h0) hst (le_of_lt h1)
  have ht0 : 0 < Real.pi * t := by nlinarith [Real.pi_pos, h0, hst]
  have hs0 : 0 < Real.pi * s := by nlinarith [Real.pi_pos, h0]
  rw [hkey, norm_div, norm_mul, hnum, norm_one_sub_E (le_of_lt h0) (le_of_lt hs1),
    norm_one_sub_E (le_of_lt (by linarith)) (le_of_lt h1)]
  rw [Commons.Analysis.Trig.cot_diff_eq hs0 (by nlinarith [Real.pi_pos, hs1])
      ht0 (by nlinarith [Real.pi_pos, h1])]
  rw [show Real.pi * t - Real.pi * s = Real.pi * (t - s) by ring]
  have hsa : Real.sin (Real.pi * s) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hs0 (by nlinarith [Real.pi_pos, hs1]))
  have hta : Real.sin (Real.pi * t) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht0 (by nlinarith [Real.pi_pos, h1]))
  field_simp

/-- `‖(1 - E β)⁻¹‖ ≤ 1/(4δ)` for `β ∈ [δ,1-δ]`. -/
lemma norm_inv_one_sub_E_le {δ β : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2)
    (h2 : δ ≤ β) (h3 : β ≤ 1 - δ) :
    ‖(1 - Submission.SdtPoisson.E β)⁻¹‖ ≤ 1 / (4 * δ) := by
  have hβ0 : 0 < β := lt_of_lt_of_le h0 h2
  have hβ1 : β < 1 := by linarith
  have hsin := two_mul_le_sin_pi_of_mem h0 h1 h2 h3
  have h4 : 0 < 4 * δ := by linarith
  calc ‖(1 - Submission.SdtPoisson.E β)⁻¹‖
      = 1 / (2 * Real.sin (Real.pi * β)) := norm_inv_one_sub_E hβ0 hβ1
    _ ≤ 1 / (4 * δ) := one_div_le_one_div_of_le h4 (by linarith)

/-- `‖1 - (1 - E β)⁻¹‖ ≤ 1/(4δ)` for `β ∈ [δ,1-δ]`. -/
lemma norm_one_sub_inv_one_sub_E_le {δ β : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2)
    (h2 : δ ≤ β) (h3 : β ≤ 1 - δ) :
    ‖1 - (1 - Submission.SdtPoisson.E β)⁻¹‖ ≤ 1 / (4 * δ) := by
  have hβ0 : 0 < β := lt_of_lt_of_le h0 h2
  have hβ1 : β < 1 := by linarith
  have hne : 1 - Submission.SdtPoisson.E β ≠ 0 := one_sub_E_ne_zero hβ0 hβ1
  have hkey : 1 - (1 - Submission.SdtPoisson.E β)⁻¹
      = -(Submission.SdtPoisson.E β) / (1 - Submission.SdtPoisson.E β) := by
    field_simp
    ring
  have hsin := two_mul_le_sin_pi_of_mem h0 h1 h2 h3
  have h4 : 0 < 4 * δ := by linarith
  calc ‖1 - (1 - Submission.SdtPoisson.E β)⁻¹‖
      = ‖Submission.SdtPoisson.E β‖ / ‖1 - Submission.SdtPoisson.E β‖ := by
        rw [hkey, norm_div, norm_neg]
    _ = 1 / (2 * Real.sin (Real.pi * β)) := by
        rw [Submission.SdtPoisson.E_norm, norm_one_sub_E (le_of_lt hβ0) (le_of_lt hβ1)]
    _ ≤ 1 / (4 * δ) := one_div_le_one_div_of_le h4 (by linarith)


/-- `|cot (πβ)| ≤ cot (πδ)` for `β ∈ [δ,1-δ]`. -/
lemma abs_cot_pi_le {δ β : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) (h2 : δ ≤ β)
    (h3 : β ≤ 1 - δ) :
    |Real.cot (Real.pi * β)| ≤ Real.cot (Real.pi * δ) := by
  have h1' : δ ≤ 1 - δ := by linarith
  have hle : Real.cot (Real.pi * β) ≤ Real.cot (Real.pi * δ) :=
    cot_pi_antitone_of_le h0 h1 (le_refl δ) h1' h2 h3 h2
  have hge : -Real.cot (Real.pi * δ) ≤ Real.cot (Real.pi * β) := by
    have h2' : δ ≤ 1 - β := by linarith
    have h3' : 1 - β ≤ 1 - δ := by linarith
    have h := cot_pi_antitone_of_le h0 h1 (le_refl δ) h1' h2' h3' h2'
    have hsub : Real.cot (Real.pi * (1 - β)) = -Real.cot (Real.pi * β) := by
      rw [show Real.pi * (1 - β) = Real.pi - Real.pi * β by ring, cot_pi_sub]
    rw [hsub] at h
    linarith
  exact abs_le.mpr ⟨hge, hle⟩

/-! ### Summation by parts -/

lemma sum_range_diff_mul {R : Type*} [CommRing R] (z u : ℕ → R) (K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), (z j - z (j + 1)) * u j
      = z 0 * u 0 - z (K + 1) * u K
        + ∑ m ∈ Finset.range K, z (m + 1) * (u (m + 1) - u m) := by
  have hsplit : (∑ j ∈ Finset.range (K + 1), (z j - z (j + 1)) * u j)
      = (∑ j ∈ Finset.range (K + 1), z j * u j)
        - (∑ j ∈ Finset.range (K + 1), z (j + 1) * u j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hA : (∑ j ∈ Finset.range (K + 1), z j * u j)
      = z 0 * u 0 + ∑ m ∈ Finset.range K, z (m + 1) * u (m + 1) := by
    have h := Finset.sum_range_succ' (fun j : ℕ => z j * u j) K
    rw [h]
    ring
  have hB : (∑ j ∈ Finset.range (K + 1), z (j + 1) * u j)
      = (∑ m ∈ Finset.range K, z (m + 1) * u m) + z (K + 1) * u K := by
    have h := Finset.sum_range_succ (fun j : ℕ => z (j + 1) * u j) K
    rw [h]
  have hD : (∑ m ∈ Finset.range K, z (m + 1) * (u (m + 1) - u m))
      = (∑ m ∈ Finset.range K, z (m + 1) * u (m + 1))
        - (∑ m ∈ Finset.range K, z (m + 1) * u m) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hsplit, hA, hB, hD]
  ring

/-! ### The Kusmin–Landau core estimate -/

/-- Core estimate: if the successive ratios of a sequence of unit complex numbers
are `e(β j)` with the `β j` monotone and `δ`-separated from the integers, then the
partial sums are bounded by `1/δ`. -/
lemma kusmin_core {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {N : ℕ} (hN : 2 ≤ N) {z : ℕ → ℂ} {β : ℕ → ℝ}
    (hz : ∀ j, ‖z j‖ = 1)
    (hβlo : ∀ j ≤ N - 2, δ ≤ β j) (hβhi : ∀ j ≤ N - 2, β j ≤ 1 - δ)
    (hβmono : ∀ i j, i ≤ j → j ≤ N - 2 → β i ≤ β j)
    (hzrec : ∀ j ≤ N - 2, z (j + 1) = z j * Submission.SdtPoisson.E (β j)) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤ 1 / δ := by
  set u : ℕ → ℂ := fun j => (1 - Submission.SdtPoisson.E (β j))⁻¹ with hu
  have hu_bound : ∀ j ≤ N - 2, ‖u j‖ ≤ 1 / (4 * δ) := fun j hj =>
    norm_inv_one_sub_E_le hδ hδ2 (hβlo j hj) (hβhi j hj)
  have hu1_bound : ∀ j ≤ N - 2, ‖1 - u j‖ ≤ 1 / (4 * δ) := fun j hj =>
    norm_one_sub_inv_one_sub_E_le hδ hδ2 (hβlo j hj) (hβhi j hj)
  have hstep : ∀ j ≤ N - 2, z j = (z j - z (j + 1)) * u j := by
    intro j hj
    have h0 : 0 < β j := lt_of_lt_of_le hδ (hβlo j hj)
    have h1 : β j < 1 := by linarith [hβhi j hj, hδ]
    have hne : 1 - Submission.SdtPoisson.E (β j) ≠ 0 := one_sub_E_ne_zero h0 h1
    have hfac : z j - z j * Submission.SdtPoisson.E (β j)
        = z j * (1 - Submission.SdtPoisson.E (β j)) := by ring
    rw [hzrec j hj, hu, hfac, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have hN1 : N - 1 + 1 = N := by omega
  have hN2 : N - 2 + 1 = N - 1 := by omega
  have hdecomp : ∑ j ∈ Finset.range N, z j
      = z 0 * u 0 + z (N - 1) * (1 - u (N - 2))
        + ∑ m ∈ Finset.range (N - 2), z (m + 1) * (u (m + 1) - u m) := by
    have hA : ∑ j ∈ Finset.range N, z j = (∑ j ∈ Finset.range (N - 1), z j) + z (N - 1) := by
      have h := Finset.sum_range_succ (f := z) (n := N - 1)
      rwa [hN1] at h
    have hB : ∑ j ∈ Finset.range (N - 1), z j
        = ∑ j ∈ Finset.range (N - 1), (z j - z (j + 1)) * u j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ N - 2 := by have := Finset.mem_range.mp hj; omega
      exact hstep j hj'
    have hC := sum_range_diff_mul z u (N - 2)
    rw [hN2] at hC
    rw [hA, hB, hC]
    ring
  rw [hdecomp]
  have hb1 : ‖z 0 * u 0‖ ≤ 1 / (4 * δ) := by
    rw [norm_mul, hz 0, one_mul]
    exact hu_bound 0 (by omega)
  have hb2 : ‖z (N - 1) * (1 - u (N - 2))‖ ≤ 1 / (4 * δ) := by
    rw [norm_mul, hz (N - 1), one_mul]
    exact hu1_bound (N - 2) (by omega)
  have hb3 : ‖∑ m ∈ Finset.range (N - 2), z (m + 1) * (u (m + 1) - u m)‖
      ≤ Real.cot (Real.pi * δ) := by
    have hterm : ∀ m, m + 1 ≤ N - 2 → ‖u (m + 1) - u m‖
        = (1 / 2) * (Real.cot (Real.pi * β m) - Real.cot (Real.pi * β (m + 1))) := by
      intro m hm
      have h0 : 0 < β m := lt_of_lt_of_le hδ (hβlo m (by omega))
      have hst : β m ≤ β (m + 1) := hβmono m (m + 1) (by omega) hm
      have h1 : β (m + 1) < 1 := by linarith [hβhi (m + 1) hm, hδ]
      rw [norm_sub_rev]
      exact norm_inv_one_sub_E_sub h0 hst h1
    have htel : (∑ m ∈ Finset.range (N - 2),
          (Real.cot (Real.pi * β m) - Real.cot (Real.pi * β (m + 1))))
        = Real.cot (Real.pi * β 0) - Real.cot (Real.pi * β (N - 2)) := by
      have h := Finset.sum_range_sub (fun j : ℕ => Real.cot (Real.pi * β j)) (N - 2)
      rw [show Real.cot (Real.pi * β 0) - Real.cot (Real.pi * β (N - 2))
            = -(Real.cot (Real.pi * β (N - 2)) - Real.cot (Real.pi * β 0)) by ring, ← h,
        ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    have hcot0 := abs_cot_pi_le hδ hδ2 (hβlo 0 (by omega)) (hβhi 0 (by omega))
    have hcotN := abs_cot_pi_le hδ hδ2 (hβlo (N - 2) (by omega)) (hβhi (N - 2) (by omega))
    have h0' := abs_le.mp hcot0
    have hN' := abs_le.mp hcotN
    calc ‖∑ m ∈ Finset.range (N - 2), z (m + 1) * (u (m + 1) - u m)‖
        ≤ ∑ m ∈ Finset.range (N - 2), ‖z (m + 1) * (u (m + 1) - u m)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range (N - 2), ‖u (m + 1) - u m‖ := by
          apply Finset.sum_le_sum
          intro m hm
          rw [norm_mul, hz (m + 1), one_mul]
      _ = ∑ m ∈ Finset.range (N - 2),
            (1 / 2) * (Real.cot (Real.pi * β m) - Real.cot (Real.pi * β (m + 1))) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hm' : m + 1 ≤ N - 2 := by have := Finset.mem_range.mp hm; omega
          rw [hterm m hm']
      _ = (1 / 2) * (∑ m ∈ Finset.range (N - 2),
            (Real.cot (Real.pi * β m) - Real.cot (Real.pi * β (m + 1)))) := by
          rw [Finset.mul_sum]
      _ = (1 / 2) * (Real.cot (Real.pi * β 0) - Real.cot (Real.pi * β (N - 2))) := by
          rw [htel]
      _ ≤ Real.cot (Real.pi * δ) := by linarith [h0'.1, h0'.2, hN'.1, hN'.2]
  have hnum : 1 / (4 * δ) + 1 / (4 * δ) + 1 / (2 * δ) = 1 / δ := by
    field_simp
    ring
  have hc := cot_pi_le_inv_two hδ hδ2
  calc ‖z 0 * u 0 + z (N - 1) * (1 - u (N - 2))
        + ∑ m ∈ Finset.range (N - 2), z (m + 1) * (u (m + 1) - u m)‖
      ≤ ‖z 0 * u 0 + z (N - 1) * (1 - u (N - 2))‖
        + ‖∑ m ∈ Finset.range (N - 2), z (m + 1) * (u (m + 1) - u m)‖ := norm_add_le _ _
    _ ≤ 1 / δ := by
        linarith [norm_add_le (z 0 * u 0) (z (N - 1) * (1 - u (N - 2))), hb1, hb2, hb3, hc, hnum]


/-! ### The monotone-derivative band -/

/-- If `g` is continuous and monotone on `[a,b]` and stays at distance `≥ δ` from
the integers on `(a,b)`, then `g` stays inside a single band `[k+δ, k+1-δ]`. -/
lemma band_of_monotone {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) {g : ℝ → ℝ}
    (hgcont : ContinuousOn g (Set.Ioo a b))
    (hgmono : MonotoneOn g (Set.Icc a b))
    (hdist : ∀ x ∈ Set.Ioo a b, δ ≤ Submission.VanDerCorput.intDist (g x)) :
    ∃ k : ℤ, ∀ x ∈ Set.Ioo a b, (k : ℝ) + δ ≤ g x ∧ g x ≤ (k : ℝ) + 1 - δ := by
  set c : ℝ := (a + b) / 2 with hc
  have hcx : c ∈ Set.Ioo a b := by
    refine ⟨?_, ?_⟩ <;> dsimp [c] <;> linarith
  have hcIcc : c ∈ Set.Icc a b := ⟨le_of_lt hcx.1, le_of_lt hcx.2⟩
  have hbad : ∀ y ∈ Set.Ioo a b, ∀ j : ℤ, δ ≤ |g y - (j : ℝ)| := by
    intro y hy j
    by_contra hlt
    have h1 := (Submission.IntDistRegion.intDist_lt_iff_exists_int (le_of_lt hδ)).mpr
      ⟨j, lt_of_not_ge hlt⟩
    linarith [hdist y hy]
  have hIVT : ∀ x₀ x₁ c' : ℝ, a < x₀ → x₀ ≤ x₁ → x₁ < b → g x₀ ≤ c' → c' ≤ g x₁ →
      ∃ t ∈ Set.Ioo a b, g t = c' := by
    intro x₀ x₁ c' h0 h01 h1 hle hge
    have hcont : ContinuousOn g (Set.Icc x₀ x₁) :=
      hgcont.mono (fun y hy => ⟨lt_of_lt_of_le h0 hy.1, lt_of_le_of_lt hy.2 h1⟩)
    have himg := intermediate_value_Icc h01 hcont
    have hmem : c' ∈ g '' Set.Icc x₀ x₁ := himg ⟨hle, hge⟩
    rcases hmem with ⟨t, ht, hgt⟩
    exact ⟨t, ⟨lt_of_lt_of_le h0 ht.1, lt_of_le_of_lt ht.2 h1⟩, hgt⟩
  set m : ℤ := ⌊g c⌋ with hm
  have hgclo : (m : ℝ) + δ ≤ g c := by
    have h1 := hdist c hcx
    have h2 := Submission.IntDistRegion.intDist_le_abs_sub (g c) m
    have h3 : 0 ≤ g c - (m : ℝ) := by
      have := Int.floor_le (g c)
      rw [← hm] at this
      linarith
    rw [abs_of_nonneg h3] at h2
    linarith
  have hgchi : g c ≤ (m : ℝ) + 1 - δ := by
    have h1 := hdist c hcx
    have h2 := Submission.IntDistRegion.intDist_le_abs_sub (g c) (m + 1)
    have h3 : g c - (((m + 1 : ℤ) : ℝ)) ≤ 0 := by
      have := Int.lt_floor_add_one (g c)
      rw [← hm] at this
      push_cast
      linarith
    rw [abs_of_nonpos h3] at h2
    push_cast at h2
    linarith
  refine ⟨m, ?_⟩
  intro x hx
  have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hbadx : ∀ j : ℤ, δ ≤ |g x - (j : ℝ)| := hbad x hx
  have hbadc : ∀ j : ℤ, δ ≤ |g c - (j : ℝ)| := hbad c hcx
  rcases le_total c x with hcx' | hxc
  · -- `c ≤ x`: monotonicity gives the lower bound, IVT the upper bound
    refine ⟨by linarith [hgclo, hgmono hcIcc hxIcc hcx'], ?_⟩
    by_contra hcon
    push_neg at hcon
    by_cases h2 : g x ≤ (m : ℝ) + 1 - δ / 2
    · -- `g x` is within `δ` of `m+1`
      have hb := hbadx (m + 1)
      have hlt : |g x - (((m + 1 : ℤ) : ℝ))| < δ := by
        rw [abs_lt]
        constructor <;> push_cast <;> linarith
      linarith
    · push_neg at h2
      -- IVT produces a point in the forbidden neighbourhood of `m+1`
      obtain ⟨t, ht, hgt⟩ :=
        hIVT c x ((m : ℝ) + 1 - δ / 2) hcx.1 hcx' hx.2 (by linarith) (le_of_lt h2)
      have hb := hbad t ht (m + 1)
      have heq : g t - (((m + 1 : ℤ) : ℝ)) = -(δ / 2) := by
        rw [hgt]
        push_cast
        ring
      rw [heq, abs_neg, abs_of_pos (by linarith)] at hb
      linarith
  · -- `x ≤ c`: monotonicity gives the upper bound, IVT the lower bound
    refine ⟨?_, by linarith [hgchi, hgmono hxIcc hcIcc hxc]⟩
    by_contra hcon
    push_neg at hcon
    by_cases h2 : (m : ℝ) + δ / 2 ≤ g x
    · -- `g x` is within `δ` of `m`
      have hb := hbadx m
      have hlt : |g x - ((m : ℤ) : ℝ)| < δ := by
        rw [abs_lt]
        constructor <;> linarith
      linarith
    · push_neg at h2
      -- IVT produces a point in the forbidden neighbourhood of `m`
      obtain ⟨t, ht, hgt⟩ :=
        hIVT x c ((m : ℝ) + δ / 2) hx.1 hxc hcx.2 (le_of_lt h2) (by linarith)
      have hb := hbad t ht m
      have heq : g t - ((m : ℤ) : ℝ) = δ / 2 := by
        rw [hgt]
        ring
      rw [heq, abs_of_pos (by linarith)] at hb
      linarith

/-! ### The Kusmin–Landau inequality for a monotone derivative -/

private lemma kusmin_landau_mono {A B : ℤ} (hAB : A ≤ B) {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 1 f (Set.Icc (A : ℝ) (B : ℝ)))
    (hmono : MonotoneOn (deriv f) (Set.Icc (A : ℝ) (B : ℝ)))
    (hdist : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ),
      δ ≤ Submission.VanDerCorput.intDist (deriv f x)) :
    ‖∑ n ∈ Finset.Icc (A + 1) B, Submission.SdtPoisson.E (f (n : ℝ))‖ ≤ 1 / δ := by
  have hδ2 : δ ≤ 1 / 2 := le_trans
    (hdist (A : ℝ) ⟨le_rfl, by exact_mod_cast hAB⟩)
    (Submission.VanDerCorput.intDist_le_half (deriv f (A : ℝ)))
  by_cases hAB1 : A + 1 ≤ B
  · have hABlt : A < B := by omega
    have hRlt : (A : ℝ) < (B : ℝ) := by exact_mod_cast hABlt
    set N : ℕ := (B - A).toNat with hNdef
    have hNcast : (N : ℤ) = B - A := Int.toNat_of_nonneg (by omega)
    have hAN : A + (N : ℤ) = B := by omega
    have hAcast : (A : ℝ) + (N : ℝ) = (B : ℝ) := by exact_mod_cast hAN
    by_cases hN1 : N = 1
    · -- a single term
      have hAB1' : A + 1 = B := by omega
      have hsum : Finset.Icc (A + 1) B = {B} := by
        rw [hAB1']
        exact Finset.Icc_self B
      rw [hsum, Finset.sum_singleton, Submission.SdtPoisson.E_norm, le_div_iff₀ hδ]
      linarith
    · have hN2 : 2 ≤ N := by omega
      -- continuity of the derivative on the open interval
      have hdcont : ContinuousOn (deriv f) (Set.Ioo (A : ℝ) (B : ℝ)) := by
        have hdw : ContinuousOn (derivWithin f (Set.Icc (A : ℝ) (B : ℝ)))
            (Set.Icc (A : ℝ) (B : ℝ)) :=
          hf.continuousOn_derivWithin (uniqueDiffOn_Icc hRlt) le_rfl
        refine (hdw.mono Set.Ioo_subset_Icc_self).congr ?_
        intro x hx
        exact (derivWithin_of_mem_nhds (Filter.mem_of_superset
          (isOpen_Ioo.mem_nhds hx) Set.Ioo_subset_Icc_self)).symm
      obtain ⟨k, hk⟩ := band_of_monotone hRlt hδ hdcont hmono
        (fun x hx => hdist x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
      set x₀ : ℝ := (A : ℝ) + 1 with hx₀def
      set α : ℕ → ℝ := fun i => f (x₀ + (i : ℝ) + 1) - f (x₀ + (i : ℝ)) - (k : ℝ) with hαdef
      set β : ℕ → ℝ := fun j => α (min j (N - 2)) with hβdef
      set z : ℕ → ℂ := fun j => Submission.SdtPoisson.E (f (x₀ + (j : ℝ))) with hzdef
      -- mean value theorem data for the increments
      have hmvt : ∀ i ≤ N - 2,
          ∃ c ∈ Set.Ioo (x₀ + (i : ℝ)) (x₀ + (i : ℝ) + 1),
            deriv f c = f (x₀ + (i : ℝ) + 1) - f (x₀ + (i : ℝ)) := by
        intro i hi
        have hlt : x₀ + (i : ℝ) < x₀ + (i : ℝ) + 1 := by linarith
        have hile : (i : ℝ) ≤ (N : ℝ) - 2 := by
          have : i ≤ N - 2 := hi
          have h2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
            have : (2 : ℕ) ≤ N := by omega
            push_cast [Nat.cast_sub this]
            ring
          calc (i : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by exact_mod_cast hi
            _ = (N : ℝ) - 2 := h2
        have hcont : ContinuousOn f (Set.Icc (x₀ + (i : ℝ)) (x₀ + (i : ℝ) + 1)) :=
          hf.continuousOn.mono (fun y hy => by
            constructor
            · dsimp [x₀] at *; linarith [hy.1]
            · have : y ≤ (A : ℝ) + (N : ℝ) := by dsimp [x₀] at *; linarith [hy.2]
              linarith [hAcast])
        have hdiff : DifferentiableOn ℝ f (Set.Ioo (x₀ + (i : ℝ)) (x₀ + (i : ℝ) + 1)) :=
          (hf.differentiableOn (by norm_num)).mono (fun y hy => by
            constructor
            · dsimp [x₀] at *; linarith [hy.1]
            · have : y ≤ (A : ℝ) + (N : ℝ) := by dsimp [x₀] at *; linarith [hy.2]
              linarith [hAcast])
        obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hlt hcont hdiff
        refine ⟨c, hc, ?_⟩
        rw [hcd, show x₀ + (i : ℝ) + 1 - (x₀ + (i : ℝ)) = 1 by ring, div_one]
      have hαband : ∀ i ≤ N - 2, δ ≤ α i ∧ α i ≤ 1 - δ := by
        intro i hi
        obtain ⟨c, hc, hcd⟩ := hmvt i hi
        have hcb := hk c ⟨by linarith [hc.1], by
          have : c < x₀ + (i : ℝ) + 1 := hc.2
          have hcn : ((A : ℝ) + (N : ℝ)) = (B : ℝ) := hAcast
          have h1 : (i : ℝ) ≤ (N : ℝ) - 2 := by
            calc (i : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by exact_mod_cast hi
              _ = (N : ℝ) - 2 := by
                  rw [Nat.cast_sub (by omega : 2 ≤ N)]; push_cast; ring
          dsimp [x₀] at *
          linarith⟩
        have hαi : α i = deriv f c - (k : ℝ) := by
          simp only [hαdef]
          rw [hcd]
        rw [hαi]
        exact ⟨by linarith [hcb.1], by linarith [hcb.2]⟩
      have hαmono : ∀ i j, i ≤ j → j ≤ N - 2 → α i ≤ α j := by
        intro i j hij hj
        rcases lt_or_eq_of_le hij with hlt | heq
        · obtain ⟨c₁, hc₁, hd₁⟩ := hmvt i (by omega)
          obtain ⟨c₂, hc₂, hd₂⟩ := hmvt j hj
          have hc12 : c₁ ≤ c₂ := by
            have h1 : (i : ℝ) + 1 ≤ (j : ℝ) := by
              have : i + 1 ≤ j := by omega
              exact_mod_cast this
            linarith [hc₁.2, hc₂.1]
          have hmon := hmono
            (show c₁ ∈ Set.Icc (A : ℝ) (B : ℝ) from ⟨by linarith [hc₁.1, hx₀def], by
              have h1 : (i : ℝ) ≤ (N : ℝ) - 2 := by
                calc (i : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by exact_mod_cast (show i ≤ N - 2 by omega)
                  _ = (N : ℝ) - 2 := by rw [Nat.cast_sub (by omega : 2 ≤ N)]; push_cast; ring
              dsimp [x₀] at *
              linarith [hAcast, hc₁.2]⟩)
            (show c₂ ∈ Set.Icc (A : ℝ) (B : ℝ) from ⟨by linarith [hc₂.1, hx₀def], by
              have h1 : (j : ℝ) ≤ (N : ℝ) - 2 := by
                calc (j : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by exact_mod_cast hj
                  _ = (N : ℝ) - 2 := by rw [Nat.cast_sub (by omega : 2 ≤ N)]; push_cast; ring
              dsimp [x₀] at *
              linarith [hAcast, hc₂.2]⟩)
            hc12
          have hαi : α i = deriv f c₁ - (k : ℝ) := by simp only [hαdef]; rw [hd₁]
          have hαj : α j = deriv f c₂ - (k : ℝ) := by simp only [hαdef]; rw [hd₂]
          rw [hαi, hαj]
          linarith
        · subst heq
          exact le_rfl
      have hβlo : ∀ j ≤ N - 2, δ ≤ β j := by
        intro j hj
        have hj' : min j (N - 2) = j := min_eq_left hj
        simp only [hβdef, hj']
        exact (hαband j hj).1
      have hβhi : ∀ j ≤ N - 2, β j ≤ 1 - δ := by
        intro j hj
        have hj' : min j (N - 2) = j := min_eq_left hj
        simp only [hβdef, hj']
        exact (hαband j hj).2
      have hβmono : ∀ i j, i ≤ j → j ≤ N - 2 → β i ≤ β j := by
        intro i j hij hj
        have hi' : min i (N - 2) = i := min_eq_left (le_trans hij hj)
        have hj' : min j (N - 2) = j := min_eq_left hj
        simp only [hβdef, hi', hj']
        exact hαmono i j hij hj
      have hzrec : ∀ j ≤ N - 2, z (j + 1) = z j * Submission.SdtPoisson.E (β j) := by
        intro j hj
        have hβj : β j = α j := by
          simp only [hβdef, min_eq_left hj]
        have hzj : z j = Submission.SdtPoisson.E (f (x₀ + (j : ℝ))) := by simp only [hzdef]
        have hzj1 : z (j + 1) = Submission.SdtPoisson.E (f (x₀ + (j : ℝ) + 1)) := by
          simp only [hzdef]
          congr 1
          push_cast
          ring
        have hαj : α j = f (x₀ + (j : ℝ) + 1) - f (x₀ + (j : ℝ)) - (k : ℝ) := by
          simp only [hαdef]
        rw [hzj, hzj1, hβj, hαj, ← Submission.SdtPoisson.E_add]
        have harg : f (x₀ + (j : ℝ)) + (f (x₀ + (j : ℝ) + 1) - f (x₀ + (j : ℝ)) - (k : ℝ))
            = f (x₀ + (j : ℝ) + 1) + ((-k : ℤ) : ℝ) := by push_cast; ring
        rw [harg, Submission.SdtPoisson.E_add, Submission.SdtPoisson.E_of_int, mul_one]
      have hcore := kusmin_core hδ hδ2 hN2 (z := z) (β := β)
        (fun j => Submission.SdtPoisson.E_norm _) hβlo hβhi hβmono hzrec
      have hsum_eq : (∑ n ∈ Finset.Icc (A + 1) B, Submission.SdtPoisson.E (f (n : ℝ)))
          = ∑ j ∈ Finset.range N, z j := by
        have h1 : (∑ n ∈ Finset.Icc (A + 1) B, Submission.SdtPoisson.E (f (n : ℝ)))
            = ∑ n ∈ Finset.Icc (A + 1) B,
                Complex.exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * Complex.I) :=
          Finset.sum_congr rfl (fun n _ => rfl)
        rw [h1, ← hAN]
        rw [Submission.SecondDerivativeTest.Icc_sum_eq_range_sum (a := A) (N := N) f]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [hzdef]
        exact rfl
      rw [hsum_eq]
      exact hcore
  · have hempty : Finset.Icc (A + 1) B = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, norm_zero]
    exact div_nonneg zero_le_one (le_of_lt hδ)

/-- **Kusmin–Landau inequality (first derivative test, distance-to-integer form).**

If `A ≤ B` are integers, `f` is `C¹` on `[A,B]` with `deriv f` monotone there and
`deriv f` at distance at least `δ > 0` from every integer on `[A,B]`, then

    ‖∑_{A < n ≤ B} exp(2πi f(n))‖ ≤ 1/δ. -/
theorem kusmin_landau {A B : ℤ} (hAB : A ≤ B) {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 1 f (Set.Icc (A : ℝ) (B : ℝ)))
    (hmono : MonotoneOn (deriv f) (Set.Icc (A : ℝ) (B : ℝ)) ∨
             AntitoneOn (deriv f) (Set.Icc (A : ℝ) (B : ℝ)))
    (hdist : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ), δ ≤ Submission.VanDerCorput.intDist (deriv f x)) :
    ‖∑ n ∈ Finset.Icc (A + 1) B,
        Complex.exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ 1 / δ := by
  have hE : ∀ t : ℝ, Submission.SdtPoisson.E t
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := fun t => rfl
  have hflip : ∀ {A B : ℤ}, (∑ n ∈ Finset.Icc (A + 1) B, Submission.SdtPoisson.E (f (n : ℝ)))
      = ∑ n ∈ Finset.Icc (A + 1) B,
          Complex.exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * Complex.I) :=
    fun {_ _} => Finset.sum_congr rfl (fun n _ => hE (f (n : ℝ)))
  rcases hmono with hm | ha
  · rw [← hflip]
    exact kusmin_landau_mono hAB hδ hf hm hdist
  · have hf' : ContDiffOn ℝ 1 (fun x : ℝ => -f x) (Set.Icc (A : ℝ) (B : ℝ)) := hf.neg
    have hm' : MonotoneOn (deriv (fun x : ℝ => -f x)) (Set.Icc (A : ℝ) (B : ℝ)) := by
      have hd : deriv (fun x : ℝ => -f x) = fun x : ℝ => -deriv f x := by
        ext x
        exact deriv.neg
      rw [hd]
      exact ha.neg
    have hdist' : ∀ x ∈ Set.Icc (A : ℝ) (B : ℝ),
        δ ≤ Submission.VanDerCorput.intDist (deriv (fun x : ℝ => -f x) x) := by
      intro x hx
      have hd : deriv (fun x : ℝ => -f x) x = -deriv f x := deriv.neg
      rw [hd, intDist_neg]
      exact hdist x hx
    have hmain := kusmin_landau_mono hAB hδ hf' hm' hdist'
    have hconj : (∑ n ∈ Finset.Icc (A + 1) B, Submission.SdtPoisson.E (-(f (n : ℝ))))
        = conj (∑ n ∈ Finset.Icc (A + 1) B, Submission.SdtPoisson.E (f (n : ℝ))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      exact (Submission.SdtPoisson.sb_conj_E (f (n : ℝ))).symm
    have hnorm : ‖∑ n ∈ Finset.Icc (A + 1) B, Submission.SdtPoisson.E (f (n : ℝ))‖
        = ‖∑ n ∈ Finset.Icc (A + 1) B, Submission.SdtPoisson.E (-(f (n : ℝ)))‖ := by
      rw [hconj, Complex.norm_conj]
    rw [← hflip, hnorm]
    exact hmain

end

end Commons.Analysis.ExponentialSums
