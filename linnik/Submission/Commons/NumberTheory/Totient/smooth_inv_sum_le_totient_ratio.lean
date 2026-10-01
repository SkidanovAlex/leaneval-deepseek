import Mathlib

namespace Commons.NumberTheory.Totient

open scoped BigOperators

/-- The reciprocal sum over the `S`-smooth numbers up to `Y` is bounded by the Euler
product `∏_{p ∈ S} p/(p-1)`: the sum over all `S`-smooth `m ≤ Y` of `1/m` is a partial
sum of the expansion of `∏_{p ∈ S} (1 - 1/p)⁻¹`. -/
theorem smooth_inv_sum_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (Y : ℕ) :
    (∑ m ∈ (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ S), (1 : ℝ) / m)
      ≤ ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  set A : Finset ℕ := (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ S) with hA
  let e : ℕ → (↥S → ℕ) := fun m p => m.factorization p.1
  let w : (↥S → ℕ) → ℝ := fun x => ∏ p : ↥S, (1 / ((p.1 : ℕ) : ℝ)) ^ (x p)
  let box : Finset (↥S → ℕ) := Fintype.piFinset (fun _ : ↥S => Finset.range (Y + 1))
  -- Basic facts about the members of `A`.
  have hmemA : ∀ m ∈ A, 1 ≤ m ∧ m ≤ Y ∧ m ≠ 0 ∧ m.primeFactors ⊆ S := by
    intro m hm
    rw [hA] at hm
    obtain ⟨hmIcc, hmsub⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmY⟩ := Finset.mem_Icc.mp hmIcc
    exact ⟨hm1, hmY, by omega, hmsub⟩
  -- (1) Each summand equals the weight of the exponent vector.
  have hterm : ∀ m ∈ A, (1 : ℝ) / m = w (e m) := by
    intro m hm
    obtain ⟨hm1, hmY, hm0, hmsub⟩ := hmemA m hm
    have hprod : (∏ p ∈ S, p ^ m.factorization p) = m := by
      rw [← Finset.prod_subset hmsub (fun p hpS hpm => by
        have hp : p.Prime := hS p hpS
        have hnotdvd : ¬ p ∣ m :=
          fun hd => hpm (Nat.mem_primeFactors.mpr ⟨hp, hd, hm0⟩)
        rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd, pow_zero])]
      exact (Nat.prod_primeFactors_pow_factorization hm0).symm
    have hcast : (m : ℝ) = ∏ p ∈ S, (p : ℝ) ^ m.factorization p := by
      conv_lhs => rw [← hprod]
      rw [Nat.cast_prod]
      exact Finset.prod_congr rfl (fun p _ => Nat.cast_pow p (m.factorization p))
    have hw : w (e m) = ∏ p ∈ S, (1 / (p : ℝ)) ^ m.factorization p := by
      show (∏ p : ↥S, (1 / ((p.1 : ℕ) : ℝ)) ^ (m.factorization p.1))
          = ∏ p ∈ S, (1 / (p : ℝ)) ^ m.factorization p
      rw [Finset.prod_coe_sort S (fun p => (1 / (p : ℝ)) ^ m.factorization p)]
    rw [hw, one_div, hcast, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun p _ => by rw [one_div, ← inv_pow])
  -- (2) The exponent map is injective on `A`.
  have hinj : Set.InjOn e ↑A := by
    intro m hm m' hm' heq
    rw [Finset.mem_coe] at hm hm'
    obtain ⟨hm1, hmY, hm0, hmsub⟩ := hmemA m hm
    obtain ⟨hm1', hmY', hm0', hmsub'⟩ := hmemA m' hm'
    refine Nat.eq_of_factorization_eq hm0 hm0' (fun p => ?_)
    by_cases hpS : p ∈ S
    · exact congrFun heq ⟨p, hpS⟩
    · have hm0fac : m.factorization p = 0 := by
        by_contra hne
        rw [Nat.factorization_eq_zero_iff] at hne
        push Not at hne
        exact hpS (hmsub (Nat.mem_primeFactors.mpr ⟨hne.1, hne.2.1, hm0⟩))
      have hm0fac' : m'.factorization p = 0 := by
        by_contra hne
        rw [Nat.factorization_eq_zero_iff] at hne
        push Not at hne
        exact hpS (hmsub' (Nat.mem_primeFactors.mpr ⟨hne.1, hne.2.1, hm0'⟩))
      rw [hm0fac, hm0fac']
  -- (3) The exponent vector of a member of `A` lies in the box.
  have hbox : A.image e ⊆ box := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨hm1, hmY, hm0, hmsub⟩ := hmemA m hm
    change e m ∈ Fintype.piFinset (fun _ : ↥S => Finset.range (Y + 1))
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    show m.factorization p.1 < Y + 1
    have := Nat.factorization_lt p.1 hm0
    omega
  -- (4) The weight is nonnegative.
  have hwnonneg : ∀ x, 0 ≤ w x := by
    intro x
    apply Finset.prod_nonneg
    intro p _
    positivity
  -- (5) Single-factor geometric bound.
  have hgeom : ∀ p : ↥S,
      (∑ k ∈ Finset.range (Y + 1), (1 / ((p.1 : ℕ) : ℝ)) ^ k)
        ≤ (1 - 1 / ((p.1 : ℕ) : ℝ))⁻¹ := by
    intro p
    have hp2 : 2 ≤ p.1 := (hS p.1 p.2).two_le
    have hx0 : 0 ≤ 1 / ((p.1 : ℕ) : ℝ) := by positivity
    have hx1 : ‖(1 / ((p.1 : ℕ) : ℝ))‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hx0, div_lt_one (by positivity)]
      exact_mod_cast (by omega : 1 < p.1)
    calc ∑ k ∈ Finset.range (Y + 1), (1 / ((p.1 : ℕ) : ℝ)) ^ k
        ≤ ∑' k : ℕ, (1 / ((p.1 : ℕ) : ℝ)) ^ k :=
          Summable.sum_le_tsum _ (fun k _ => by positivity)
            (summable_geometric_of_norm_lt_one hx1)
      _ = (1 - 1 / ((p.1 : ℕ) : ℝ))⁻¹ := tsum_geometric_of_norm_lt_one hx1
  -- (6) Rewriting the single factor.
  have hfactor : ∀ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hp2 : 2 ≤ p := (hS p hp).two_le
    have h1 : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
      field_simp
    rw [h1, inv_div]
  -- (7) The box sum factorises.
  have hboxsum : ∑ x ∈ box, w x
      = ∏ p : ↥S, ∑ k ∈ Finset.range (Y + 1), (1 / ((p.1 : ℕ) : ℝ)) ^ k := by
    have h := Finset.prod_univ_sum (fun _ : ↥S => Finset.range (Y + 1))
      (fun (p : ↥S) (k : ℕ) => (1 / ((p.1 : ℕ) : ℝ)) ^ k)
    simpa only [box, w] using h.symm
  -- Assembly.
  calc (∑ m ∈ (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ S), (1 : ℝ) / m)
      = ∑ m ∈ A, (1 : ℝ) / m := by rw [hA]
    _ = ∑ m ∈ A, w (e m) := Finset.sum_congr rfl hterm
    _ = ∑ x ∈ A.image e, w x := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ box, w x :=
        Finset.sum_le_sum_of_subset_of_nonneg hbox (fun x _ _ => hwnonneg x)
    _ = ∏ p : ↥S, ∑ k ∈ Finset.range (Y + 1), (1 / ((p.1 : ℕ) : ℝ)) ^ k := hboxsum
    _ ≤ ∏ p : ↥S, (1 - 1 / ((p.1 : ℕ) : ℝ))⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro p _; positivity
        · intro p _; exact hgeom p
    _ = ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
        rw [Finset.prod_coe_sort S (fun p => (1 - 1 / (p : ℝ))⁻¹)]
        exact Finset.prod_congr rfl hfactor

/-- The totient ratio is the Euler product over the distinct prime factors. -/
theorem totient_div_eq_prod_primeFactors_div_pred (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) / (Nat.totient r : ℝ)
      = ∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  have hr0 : r ≠ 0 := by omega
  have hcast : (Nat.totient r : ℝ) * ∏ p ∈ r.primeFactors, (p : ℝ)
      = (r : ℝ) * ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) (Nat.totient_mul_prod_primeFactors r)
    simp only [Nat.cast_mul, Nat.cast_prod] at h
    rw [h]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hQne : (∏ p ∈ r.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  have hφne : (Nat.totient r : ℝ) ≠ 0 := by
    have : 0 < Nat.totient r := Nat.totient_pos.mpr (by omega)
    positivity
  rw [Finset.prod_div_distrib]
  rw [div_eq_div_iff hφne hQne]
  exact hcast.symm.trans
    (mul_comm (Nat.totient r : ℝ) (∏ p ∈ r.primeFactors, (p : ℝ)))

theorem smooth_inv_sum_le_totient_ratio (r Y : ℕ) (hr : 1 ≤ r) :
    (∑ m ∈ (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ r.primeFactors), (1 : ℝ) / m)
      ≤ (r : ℝ) / (Nat.totient r : ℝ) := by
  have hS : ∀ p ∈ r.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  calc (∑ m ∈ (Finset.Icc 1 Y).filter (fun m => m.primeFactors ⊆ r.primeFactors), (1 : ℝ) / m)
      ≤ ∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1) :=
        smooth_inv_sum_le_prod r.primeFactors hS Y
    _ = (r : ℝ) / (Nat.totient r : ℝ) :=
        (totient_div_eq_prod_primeFactors_div_pred r hr).symm

end Commons.NumberTheory.Totient
