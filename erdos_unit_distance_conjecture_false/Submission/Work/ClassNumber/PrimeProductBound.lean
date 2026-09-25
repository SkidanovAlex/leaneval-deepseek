import Mathlib
import Submission.Work.ClassNumber.PrimeNormCount

namespace Work.ClassNumber

open NumberField

/-- Telescoping product identity: for `1 ≤ m`,
`∏_{k=2}^{m} (1 - 1/k²) = (m+1)/(2m)`. -/
lemma prod_Icc_one_sub_inv_sq (m : ℕ) (hm : 1 ≤ m) :
    ∏ k ∈ Finset.Icc 2 m, (1 - (((k : ℝ))⁻¹) ^ 2) = ((m : ℝ) + 1) / (2 * m) := by
  have hrat :
      ∏ k ∈ Finset.Icc 2 m, (((k : ℝ))^2 - 1) / ((k : ℝ)^2) = ((m : ℝ) + 1) / (2 * m) := by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      have hm0 : (0:ℝ) < m := by exact_mod_cast hm
      have hne : (((m:ℝ)+1))^2 ≠ 0 := by positivity
      field_simp
      push_cast
      ring
  rw [← hrat]
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have hk0 : ((k:ℝ)) ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1
    positivity
  field_simp

/-- The telescoping bound `∏_{k=2}^{m} (1 - 1/k²)⁻¹ ≤ 2`. -/
lemma prod_Icc_inv_le_two (m : ℕ) :
    ∏ k ∈ Finset.Icc 2 m, (1 - (((k : ℝ))⁻¹) ^ 2)⁻¹ ≤ 2 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have hempty : Finset.Icc 2 m = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      omega
    rw [hempty, Finset.prod_empty]; norm_num
  · have hm1 : 1 ≤ m := by omega
    rw [Finset.prod_inv_distrib, prod_Icc_one_sub_inv_sq m hm1, inv_div]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (m:ℝ) + 1)]
    linarith

/-- **Euler-product type bound.** For a finite set `Q` of nonzero prime ideals whose norms lie in
`[2, m]` and are each attained at most `[K : ℚ]` times inside `Q`, the product of the local Euler
factors `(1 - N(℘)⁻²)⁻¹` over `Q` is at most `2^[K:ℚ]`: grouping by the value of the norm and
telescoping `∏_{k=2}^{m} (1 - 1/k²)⁻¹ = 2m/(m+1) ≤ 2` gives the claim. -/
theorem PrimeProductBound (K : Type*) [Field K] [NumberField K] (m : ℕ)
    (Q : Finset (Ideal (NumberField.RingOfIntegers K))) (hQ : ∀ ℘ ∈ Q, ℘.IsPrime) (hQ0 : ∀ ℘ ∈ Q, ℘ ≠ ⊥)
    (hN : ∀ ℘ ∈ Q, Ideal.absNorm ℘ ≤ m)
    (hcard : ∀ k ∈ Finset.Icc 2 m, (Q.filter (fun ℘ => Ideal.absNorm ℘ = k)).card ≤ Module.finrank ℚ K) :
    ∏ ℘ ∈ Q, (1 - (((Ideal.absNorm ℘ : ℝ)⁻¹)) ^ 2)⁻¹ ≤ (2 : ℝ) ^ Module.finrank ℚ K := by
  classical
  have h2 : ∀ ℘ ∈ Q, 2 ≤ Ideal.absNorm ℘ := by
    intro ℘ h℘
    have hne0 : Ideal.absNorm ℘ ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hQ0 ℘ h℘
    have hne1 : Ideal.absNorm ℘ ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact (hQ ℘ h℘).ne_top
    omega
  have hf1 : ∀ k : ℕ, 2 ≤ k → 1 ≤ (1 - (((k : ℝ))⁻¹) ^ 2)⁻¹ := by
    intro k hk
    have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hpos : 0 < 1 - (((k : ℝ))⁻¹) ^ 2 := by
      have hle : ((k:ℝ))⁻¹ ≤ 2⁻¹ := by
        rw [inv_le_inv₀ hk0 (by norm_num : (0:ℝ) < 2)]
        exact_mod_cast (by omega : 2 ≤ k)
      nlinarith [inv_nonneg.mpr hk0.le]
    rw [one_le_inv₀ hpos]
    nlinarith [sq_nonneg (((k : ℝ))⁻¹)]
  have hfpos : ∀ k : ℕ, 2 ≤ k → 0 < (1 - (((k : ℝ))⁻¹) ^ 2)⁻¹ :=
    fun k hk => lt_of_lt_of_le one_pos (hf1 k hk)
  rw [← Finset.prod_fiberwise_of_maps_to (t := Q.image Ideal.absNorm) (g := Ideal.absNorm)
      (f := fun ℘ => (1 - (((Ideal.absNorm ℘ : ℝ)⁻¹)) ^ 2)⁻¹)
      (fun i hi => Finset.mem_image_of_mem Ideal.absNorm hi)]
  have hinner : ∀ k ∈ Q.image Ideal.absNorm,
      ∏ ℘ ∈ Q.filter (fun ℘ => Ideal.absNorm ℘ = k),
          (1 - (((Ideal.absNorm ℘ : ℝ)⁻¹)) ^ 2)⁻¹
        = ((1 - (((k : ℝ))⁻¹) ^ 2)⁻¹) ^ (Q.filter (fun ℘ => Ideal.absNorm ℘ = k)).card := by
    intro k hk
    rw [Finset.prod_congr rfl (fun ℘ h℘ => ?_), Finset.prod_const]
    simp only [Finset.mem_filter] at h℘
    rw [h℘.2]
  rw [Finset.prod_congr rfl hinner]
  have hsub : Q.image Ideal.absNorm ⊆ Finset.Icc 2 m := by
    intro k hk
    obtain ⟨℘, h℘Q, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr ⟨h2 ℘ h℘Q, hN ℘ h℘Q⟩
  have hmn : ∀ k ∈ Q.image Ideal.absNorm, 2 ≤ k := fun k hk => (Finset.mem_Icc.mp (hsub hk)).1
  have hstep1 : ∏ k ∈ Q.image Ideal.absNorm,
        ((1 - (((k : ℝ))⁻¹) ^ 2)⁻¹) ^ (Q.filter (fun ℘ => Ideal.absNorm ℘ = k)).card
      ≤ ∏ k ∈ Q.image Ideal.absNorm, ((1 - (((k : ℝ))⁻¹) ^ 2)⁻¹) ^ Module.finrank ℚ K := by
    refine Finset.prod_le_prod₀ (fun k hk => pow_nonneg (hfpos k (hmn k hk)).le _) (fun k hk => ?_)
    obtain ⟨℘, h℘Q, rfl⟩ := Finset.mem_image.mp hk
    exact pow_le_pow_right₀ (hf1 _ (h2 ℘ h℘Q))
      (hcard _ (Finset.mem_Icc.mpr ⟨h2 ℘ h℘Q, hN ℘ h℘Q⟩))
  have hstep2 : ∏ k ∈ Q.image Ideal.absNorm, ((1 - (((k : ℝ))⁻¹) ^ 2)⁻¹) ^ Module.finrank ℚ K
      = (∏ k ∈ Q.image Ideal.absNorm, (1 - (((k : ℝ))⁻¹) ^ 2)⁻¹) ^ Module.finrank ℚ K :=
    Finset.prod_pow _ _ _
  have hstep3 : (∏ k ∈ Q.image Ideal.absNorm, (1 - (((k : ℝ))⁻¹) ^ 2)⁻¹) ^ Module.finrank ℚ K
      ≤ (∏ k ∈ Finset.Icc 2 m, (1 - (((k : ℝ))⁻¹) ^ 2)⁻¹) ^ Module.finrank ℚ K := by
    refine pow_le_pow_left₀ (Finset.prod_nonneg (fun k hk => (hfpos k (hmn k hk)).le)) ?_ _
    exact Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun k hk => (hfpos k (hmn k hk)).le)
      (fun k hk _ => hf1 k (Finset.mem_Icc.mp hk).1)
  have hstep4 : (∏ k ∈ Finset.Icc 2 m, (1 - (((k : ℝ))⁻¹) ^ 2)⁻¹) ^ Module.finrank ℚ K
      ≤ (2 : ℝ) ^ Module.finrank ℚ K :=
    pow_le_pow_left₀ (Finset.prod_nonneg (fun k hk => (hfpos k (Finset.mem_Icc.mp hk).1).le))
      (prod_Icc_inv_le_two m) _
  exact hstep1.trans (hstep2.trans_le (hstep3.trans hstep4))

end Work.ClassNumber
