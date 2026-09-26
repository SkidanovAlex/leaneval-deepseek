import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.E8ThetaAux
import Submission.Work.Modular.Th4_S_smul
import Submission.Work.Modular.Th2_S_smul

/-!
# The `S`-transformation law for the `E₈` theta series

We prove `Θ_{E₈}(-1/τ) = τ⁴ Θ_{E₈}(τ)`, the weight-`4` modularity of the theta series of the
even unimodular lattice `E₈` under `S : τ ↦ -1/τ`.

The proof combines

* the decomposition `Θ_{E₈} = (1/2)(Θ₃⁸ + Θ₄⁸ + Θ₂⁸)` of the `E₈` theta series into eighth powers
  of the three Jacobi theta functions (`thetaSeries_E8_decomp`), obtained by splitting
  `E₈ = D₈ ⊔ (D₈ + s)` and factoring the sums over `ℤ⁸`; and
* the `S`-transformation laws of `Θ₃`, `Θ₄`, `Θ₂`.

-/

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

lemma D8set_subset_range_vec :
    D8set ⊆ Set.range (vec : (Fin 8 → ℤ) → EuclideanSpace ℝ (Fin 8)) := by
  rintro x ⟨⟨m, hm⟩, rfl⟩
  exact ⟨m, rfl⟩

lemma C8set_subset_range_vec :
    C8set ⊆ Set.range (fun m : Fin 8 → ℤ => (vec m + svec : EuclideanSpace ℝ (Fin 8))) := by
  rintro x ⟨⟨m, hm⟩, rfl⟩
  exact ⟨m, rfl⟩

lemma summable_norm_thetaTerm_vec (τ : ℍ) :
    Summable (fun m : Fin 8 → ℤ => ‖thetaTerm τ (vec m)‖) := by
  refine Summable.of_norm_bounded
    (summable_norm_prod_pi (fun m : ℤ => phi3 τ m) (summable_norm_phi3 τ) 8) (fun m => ?_)
  rw [thetaTerm_vec]
  simpa only [norm_norm] using Finset.norm_prod_le Finset.univ (fun i => phi3 τ (m i))

lemma summable_norm_thetaTerm_vec_add_svec (τ : ℍ) :
    Summable (fun m : Fin 8 → ℤ => ‖thetaTerm τ (vec m + svec)‖) := by
  refine Summable.of_norm_bounded
    (summable_norm_prod_pi (fun m : ℤ => phi2 τ m) (summable_norm_phi2 τ) 8) (fun m => ?_)
  rw [thetaTerm_vec_add_svec]
  simpa only [norm_norm] using Finset.norm_prod_le Finset.univ (fun i => phi2 τ (m i))

lemma summable_if_even_thetaTerm_vec (τ : ℍ) :
    Summable (fun m : Fin 8 → ℤ => if Even (∑ i, m i) then thetaTerm τ (vec m) else 0) := by
  refine Summable.of_norm_bounded (summable_norm_thetaTerm_vec τ) (fun m => ?_)
  by_cases h : Even (∑ i, m i)
  · rw [if_pos h]
  · rw [if_neg h]; simp

lemma summable_if_even_thetaTerm_vec_add_svec (τ : ℍ) :
    Summable (fun m : Fin 8 → ℤ =>
      if Even (∑ i, m i) then thetaTerm τ (vec m + svec) else 0) := by
  refine Summable.of_norm_bounded (summable_norm_thetaTerm_vec_add_svec τ) (fun m => ?_)
  by_cases h : Even (∑ i, m i)
  · rw [if_pos h]
  · rw [if_neg h]; simp

lemma summable_indicator_D8 (τ : ℍ) : Summable (D8set.indicator (thetaTerm τ)) := by
  have hf : ∀ x ∉ Set.range (vec : (Fin 8 → ℤ) → EuclideanSpace ℝ (Fin 8)),
      D8set.indicator (thetaTerm τ) x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun hc => hx (D8set_subset_range_vec hc)) _
  refine (Function.Injective.summable_iff vec_injective hf).mp ?_
  refine (summable_congr (fun m => ?_)).mpr (summable_if_even_thetaTerm_vec τ)
  simp only [Function.comp_apply]
  by_cases h : Even (∑ i, m i)
  · rw [if_pos h, Set.indicator_of_mem (vec_mem_D8set.mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem (fun hc => h (vec_mem_D8set.mp hc))]

lemma summable_indicator_C8 (τ : ℍ) : Summable (C8set.indicator (thetaTerm τ)) := by
  have hf : ∀ x ∉ Set.range (fun m : Fin 8 → ℤ => (vec m + svec : EuclideanSpace ℝ (Fin 8))),
      C8set.indicator (thetaTerm τ) x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun hc => hx (C8set_subset_range_vec hc)) _
  refine (Function.Injective.summable_iff vec_add_svec_injective hf).mp ?_
  refine (summable_congr (fun m => ?_)).mpr (summable_if_even_thetaTerm_vec_add_svec τ)
  simp only [Function.comp_apply]
  by_cases h : Even (∑ i, m i)
  · rw [if_pos h, Set.indicator_of_mem (vec_add_svec_mem_C8set.mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem (fun hc => h (vec_add_svec_mem_C8set.mp hc))]

lemma tsum_indicator_D8 (τ : ℍ) :
    (∑' x : EuclideanSpace ℝ (Fin 8), D8set.indicator (thetaTerm τ) x)
      = ∑' m : Fin 8 → ℤ, (if Even (∑ i, m i) then thetaTerm τ (vec m) else 0) := by
  have hsupp : Function.support (D8set.indicator (thetaTerm τ)) ⊆
      Set.range (vec : (Fin 8 → ℤ) → EuclideanSpace ℝ (Fin 8)) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra h
    exact hx (Set.indicator_of_notMem (fun hc => h (D8set_subset_range_vec hc)) _)
  rw [← Function.Injective.tsum_eq vec_injective hsupp]
  apply tsum_congr
  intro m
  by_cases h : Even (∑ i, m i)
  · rw [if_pos h, Set.indicator_of_mem (vec_mem_D8set.mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem (fun hc => h (vec_mem_D8set.mp hc))]

lemma tsum_indicator_C8 (τ : ℍ) :
    (∑' x : EuclideanSpace ℝ (Fin 8), C8set.indicator (thetaTerm τ) x)
      = ∑' m : Fin 8 → ℤ,
          (if Even (∑ i, m i) then thetaTerm τ (vec m + svec) else 0) := by
  have hsupp : Function.support (C8set.indicator (thetaTerm τ)) ⊆
      Set.range (fun m : Fin 8 → ℤ => (vec m + svec : EuclideanSpace ℝ (Fin 8))) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra h
    exact hx (Set.indicator_of_notMem (fun hc => h (C8set_subset_range_vec hc)) _)
  rw [← Function.Injective.tsum_eq vec_add_svec_injective hsupp]
  apply tsum_congr
  intro m
  by_cases h : Even (∑ i, m i)
  · rw [if_pos h, Set.indicator_of_mem (vec_add_svec_mem_C8set.mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem (fun hc => h (vec_add_svec_mem_C8set.mp hc))]


lemma indicator_E8_eq (τ : ℍ) (x : EuclideanSpace ℝ (Fin 8)) :
    (E8 : Set (EuclideanSpace ℝ (Fin 8))).indicator (thetaTerm τ) x =
      D8set.indicator (thetaTerm τ) x + C8set.indicator (thetaTerm τ) x := by
  by_cases hx : x ∈ (E8 : Set (EuclideanSpace ℝ (Fin 8)))
  · rw [Set.indicator_of_mem hx]
    rcases E8_subset_union hx with h | h
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_notMem (fun hc => Set.disjoint_left.mp disjoint_D8set_C8set h hc),
        add_zero]
    · rw [Set.indicator_of_notMem (fun hc => Set.disjoint_left.mp disjoint_D8set_C8set hc h),
        Set.indicator_of_mem h, zero_add]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun hc => hx (D8set_subset_E8 hc)),
      Set.indicator_of_notMem (fun hc => hx (C8set_subset_E8 hc)), add_zero]

lemma parity_ite (k : ℤ) (Z : ℂ) :
    (if Even k then Z else 0) = (1/2) * (Z + sgn k * Z) := by
  by_cases h : Even k
  · rw [if_pos h, sgn_eq_pow, Even.neg_one_zpow h]; ring
  · rw [if_neg h, sgn_eq_pow, Odd.neg_one_zpow (Int.not_even_iff_odd.mp h)]; ring

set_option maxHeartbeats 2000000 in
lemma thetaSeries_E8_indicator (τ : ℍ) :
    thetaSeries E8 τ = ∑' x : EuclideanSpace ℝ (Fin 8),
      (E8 : Set (EuclideanSpace ℝ (Fin 8))).indicator (thetaTerm τ) x := by
  rw [thetaSeries]
  exact tsum_subtype (E8 : Set (EuclideanSpace ℝ (Fin 8))) (fun x => thetaTerm τ x)

theorem thetaSeries_E8_decomp (τ : ℍ) :
    thetaSeries E8 τ = (1/2) * (Th3 τ ^ 8 + Th4 τ ^ 8 + Th2 τ ^ 8) := by
  have hXnorm := summable_norm_thetaTerm_vec τ
  have hYnorm := summable_norm_thetaTerm_vec_add_svec τ
  have hX : Summable (fun m : Fin 8 → ℤ => thetaTerm τ (vec m)) := hXnorm.of_norm
  have hY : Summable (fun m : Fin 8 → ℤ => thetaTerm τ (vec m + svec)) := hYnorm.of_norm
  have hHX : Summable (fun m : Fin 8 → ℤ => sgn (∑ i, m i) * thetaTerm τ (vec m)) :=
    (hXnorm.congr (fun m => by rw [norm_mul, norm_sgn, one_mul])).of_norm
  have hHY : Summable (fun m : Fin 8 → ℤ => sgn (∑ i, m i) * thetaTerm τ (vec m + svec)) :=
    (hYnorm.congr (fun m => by rw [norm_mul, norm_sgn, one_mul])).of_norm
  have hXsum : (∑' m : Fin 8 → ℤ, thetaTerm τ (vec m)) = Th3 τ ^ 8 := by
    rw [show (∑' m : Fin 8 → ℤ, thetaTerm τ (vec m))
        = ∑' m : Fin 8 → ℤ, ∏ i, phi3 τ (m i) from tsum_congr (fun m => thetaTerm_vec τ m)]
    rw [tsum_prod_pi (fun m : ℤ => phi3 τ m) (summable_norm_phi3 τ) 8, tsum_phi3]
  have hYsum : (∑' m : Fin 8 → ℤ, thetaTerm τ (vec m + svec)) = Th2 τ ^ 8 := by
    rw [show (∑' m : Fin 8 → ℤ, thetaTerm τ (vec m + svec))
        = ∑' m : Fin 8 → ℤ, ∏ i, phi2 τ (m i)
        from tsum_congr (fun m => thetaTerm_vec_add_svec τ m)]
    rw [tsum_prod_pi (fun m : ℤ => phi2 τ m) (summable_norm_phi2 τ) 8, tsum_phi2]
  have hSXsum : (∑' m : Fin 8 → ℤ, sgn (∑ i, m i) * thetaTerm τ (vec m)) = Th4 τ ^ 8 := by
    rw [show (∑' m : Fin 8 → ℤ, sgn (∑ i, m i) * thetaTerm τ (vec m))
        = ∑' m : Fin 8 → ℤ, ∏ i, (sgn (m i) * phi3 τ (m i))
        from tsum_congr (fun m => by rw [thetaTerm_vec, Finset.prod_mul_distrib, prod_sgn])]
    rw [tsum_prod_pi (fun m : ℤ => sgn m * phi3 τ m) (summable_norm_sgn_phi3 τ) 8, tsum_sgn_phi3]
  have hZ : Summable (fun m : Fin 8 → ℤ =>
      thetaTerm τ (vec m) + thetaTerm τ (vec m + svec)) := hX.add hY
  have hSZ : Summable (fun m : Fin 8 → ℤ =>
      sgn (∑ i, m i) * (thetaTerm τ (vec m) + thetaTerm τ (vec m + svec))) :=
    (hHX.add hHY).congr (fun m => by ring)
  have hSYsum : (∑' m : Fin 8 → ℤ, sgn (∑ i, m i) * thetaTerm τ (vec m + svec)) = 0 := by
    rw [show (∑' m : Fin 8 → ℤ, sgn (∑ i, m i) * thetaTerm τ (vec m + svec))
        = ∑' m : Fin 8 → ℤ, ∏ i, (sgn (m i) * phi2 τ (m i))
        from tsum_congr (fun m => by
          rw [thetaTerm_vec_add_svec, Finset.prod_mul_distrib, prod_sgn])]
    rw [tsum_prod_pi (fun m : ℤ => sgn m * phi2 τ m) (summable_norm_sgn_phi2 τ) 8, tsum_sgn_phi2]
    exact zero_pow (by norm_num)
  calc thetaSeries E8 τ
      = (∑' x : EuclideanSpace ℝ (Fin 8), D8set.indicator (thetaTerm τ) x)
          + ∑' x : EuclideanSpace ℝ (Fin 8), C8set.indicator (thetaTerm τ) x := by
        rw [thetaSeries_E8_indicator τ, tsum_congr (fun x => indicator_E8_eq τ x)]
        exact Summable.tsum_add (summable_indicator_D8 τ) (summable_indicator_C8 τ)
    _ = (∑' m : Fin 8 → ℤ, (if Even (∑ i, m i) then thetaTerm τ (vec m) else 0))
          + ∑' m : Fin 8 → ℤ,
              (if Even (∑ i, m i) then thetaTerm τ (vec m + svec) else 0) := by
        rw [tsum_indicator_D8 τ, tsum_indicator_C8 τ]
    _ = ∑' m : Fin 8 → ℤ, ((if Even (∑ i, m i) then thetaTerm τ (vec m) else 0)
          + (if Even (∑ i, m i) then thetaTerm τ (vec m + svec) else 0)) :=
        (Summable.tsum_add (summable_if_even_thetaTerm_vec τ)
          (summable_if_even_thetaTerm_vec_add_svec τ)).symm
    _ = ∑' m : Fin 8 → ℤ, (if Even (∑ i, m i)
          then (thetaTerm τ (vec m) + thetaTerm τ (vec m + svec)) else 0) := by
        apply tsum_congr; intro m
        by_cases h : Even (∑ i, m i) <;> simp [h]
    _ = (1/2) * ((∑' m : Fin 8 → ℤ, (thetaTerm τ (vec m) + thetaTerm τ (vec m + svec)))
          + ∑' m : Fin 8 → ℤ, sgn (∑ i, m i)
              * (thetaTerm τ (vec m) + thetaTerm τ (vec m + svec))) := by
        rw [show (∑' m : Fin 8 → ℤ, (if Even (∑ i, m i)
              then (thetaTerm τ (vec m) + thetaTerm τ (vec m + svec)) else 0))
            = ∑' m : Fin 8 → ℤ, (1/2) * ((thetaTerm τ (vec m) + thetaTerm τ (vec m + svec))
                + sgn (∑ i, m i)
                  * (thetaTerm τ (vec m) + thetaTerm τ (vec m + svec)))
            from tsum_congr (fun m => parity_ite (∑ i, m i) _)]
        rw [tsum_mul_left, Summable.tsum_add hZ hSZ]
    _ = (1/2) * ((Th3 τ ^ 8 + Th2 τ ^ 8) + (Th4 τ ^ 8 + 0)) := by
        rw [Summable.tsum_add hX hY]
        rw [show (∑' m : Fin 8 → ℤ,
              sgn (∑ i, m i) * (thetaTerm τ (vec m) + thetaTerm τ (vec m + svec)))
            = ∑' m : Fin 8 → ℤ, (sgn (∑ i, m i) * thetaTerm τ (vec m)
                + sgn (∑ i, m i) * thetaTerm τ (vec m + svec))
            from tsum_congr (fun m => by ring)]
        rw [Summable.tsum_add hHX hHY, hXsum, hYsum, hSXsum, hSYsum]
    _ = (1/2) * (Th3 τ ^ 8 + Th4 τ ^ 8 + Th2 τ ^ 8) := by ring

/-- The transformation of `Θ₃` under `S` (Jacobi's identity, from Mathlib). -/
theorem Th3_S_smul (τ : ℍ) :
    Th3 (ModularGroup.S • τ) = (-Complex.I * (τ:ℂ))^(1/2:ℂ) * Th3 τ :=
  jacobiTheta_S_smul τ

/-- `Θ_{E₈}` transforms as a modular form of weight `4` under `τ ↦ -1/τ`, because `E₈` is an
even unimodular lattice of rank `8`. -/
theorem thetaSeries_E8_S_smul (τ : ℍ) :
    thetaSeries E8 (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * thetaSeries E8 τ := by
  have h4 := Th4_S_smul τ
  have h2 := Th2_S_smul τ
  have h3 : Th3 (ModularGroup.S • τ) = (-Complex.I * (τ:ℂ))^(1/2:ℂ) * Th3 τ :=
    Th3_S_smul τ
  have hpow : ((-Complex.I * (τ:ℂ))^(1/2:ℂ))^8 = (τ:ℂ)^4 := by
    rw [← Complex.cpow_nat_mul]
    have hexp : ((8:ℕ):ℂ) * (1/2:ℂ) = ((4:ℕ):ℂ) := by norm_num
    rw [hexp, Complex.cpow_natCast, mul_pow,
      show (-Complex.I : ℂ)^4 = 1 by norm_num [Complex.ext_iff, Complex.I_mul_I], one_mul]
  calc thetaSeries E8 (ModularGroup.S • τ)
      = (1/2) * (Th3 (ModularGroup.S • τ)^8 + Th4 (ModularGroup.S • τ)^8
          + Th2 (ModularGroup.S • τ)^8) := thetaSeries_E8_decomp (ModularGroup.S • τ)
    _ = (1/2) * (((-Complex.I * (τ:ℂ))^(1/2:ℂ) * Th3 τ)^8
          + ((-Complex.I * (τ:ℂ))^(1/2:ℂ) * Th2 τ)^8
          + ((-Complex.I * (τ:ℂ))^(1/2:ℂ) * Th4 τ)^8) := by rw [h3, h4, h2]
    _ = (1/2) * (((-Complex.I * (τ:ℂ))^(1/2:ℂ))^8 * Th3 τ^8
          + ((-Complex.I * (τ:ℂ))^(1/2:ℂ))^8 * Th2 τ^8
          + ((-Complex.I * (τ:ℂ))^(1/2:ℂ))^8 * Th4 τ^8) := by simp only [mul_pow]
    _ = (1/2) * ((τ:ℂ)^4 * Th3 τ^8 + (τ:ℂ)^4 * Th2 τ^8 + (τ:ℂ)^4 * Th4 τ^8) := by rw [hpow]
    _ = (τ:ℂ)^4 * ((1/2) * (Th3 τ^8 + Th4 τ^8 + Th2 τ^8)) := by ring
    _ = (τ:ℂ)^4 * thetaSeries E8 τ := by rw [thetaSeries_E8_decomp τ]

end Work.Modular
