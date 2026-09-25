import Mathlib

/-!
# Summability of `∏ i ∈ c.support, x i ^ (c i)` over finitely supported `c : σ →₀ ℕ`

If `x : σ → ℝ` is nonnegative, summable, with `x i < 1` for all `i`, then the family
`c ↦ ∏ i ∈ c.support, x i ^ (c i)` on `σ →₀ ℕ` is summable (its sum being the product
`∏ i, (1 - x i)⁻¹`).
-/

namespace NK.HeckeL.Series

open Finset

variable {σ : Type*}

/-- Factorization of the summand with respect to a single coordinate: splitting off the value
at `a`. -/
private lemma prod_support_erase (x : σ → ℝ) (a : σ) (c : σ →₀ ℕ) :
    (∏ i ∈ c.support, x i ^ (c i))
      = x a ^ (c a) * ∏ i ∈ (Finsupp.erase a c).support, x i ^ ((Finsupp.erase a c) i) := by
  classical
  by_cases ha : a ∈ c.support
  · have hsupp : c.support = insert a (c.support.erase a) := (Finset.insert_erase ha).symm
    rw [hsupp, Finset.prod_insert (Finset.notMem_erase a c.support), Finsupp.support_erase]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨hne, _⟩ := Finset.mem_erase.mp hi
    rw [Finsupp.erase_ne hne]
  · have hca : c a = 0 := by
      by_contra h
      exact ha (Finsupp.mem_support_iff.mpr h)
    rw [Finsupp.erase_of_notMem_support ha, hca, pow_zero, one_mul]

/-- The "box bound": any finite collection of multi-indices whose supports lie in a finite set
`T` has total weight at most `∏ i ∈ T, (1 - x i)⁻¹`. -/
private lemma sum_le_prod_inv {x : σ → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) :
    ∀ (T : Finset σ) (u : Finset (σ →₀ ℕ)),
      (∀ c ∈ u, c.support ⊆ T) →
      ∑ c ∈ u, (∏ i ∈ c.support, x i ^ (c i)) ≤ ∏ i ∈ T, (1 - x i)⁻¹ := by
  classical
  intro T
  induction T using Finset.induction with
  | empty =>
      intro u hu
      have hprod : ∀ c ∈ u, (∏ i ∈ c.support, x i ^ (c i)) = 1 := by
        intro c hc
        have hcs : c.support = ∅ := Finset.subset_empty.mp (hu c hc)
        rw [hcs, Finset.prod_empty]
      have hsub : u ⊆ {0} := by
        intro c hc
        rw [Finset.mem_singleton]
        exact Finsupp.support_eq_empty.mp (Finset.subset_empty.mp (hu c hc))
      have hcard : u.card ≤ 1 := by
        have := Finset.card_le_card hsub
        simpa using this
      rw [Finset.sum_congr rfl hprod, Finset.sum_const, Finset.prod_empty, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard
  | insert a T' ha ih =>
      intro u hu
      set N : Finset ℕ := u.image (fun c => c a) with hN
      have hsplit : ∑ n ∈ N, ∑ c ∈ u.filter (fun c => c a = n), (∏ i ∈ c.support, x i ^ (c i))
          = ∑ c ∈ u, (∏ i ∈ c.support, x i ^ (c i)) :=
        Finset.sum_fiberwise_of_maps_to (fun c hc => Finset.mem_image.mpr ⟨c, hc, rfl⟩) _
      rw [← hsplit, Finset.prod_insert ha]
      have hB : 0 ≤ ∏ i ∈ T', (1 - x i)⁻¹ :=
        Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (by linarith [hx1 i]))
      have hgeom : ∑ m ∈ N, (x a) ^ m ≤ (1 - x a)⁻¹ := by
        have h := (summable_geometric_of_lt_one (hx0 a) (hx1 a)).sum_le_tsum N
          (fun m _ => pow_nonneg (hx0 a) m)
        rwa [tsum_geometric_of_lt_one (hx0 a) (hx1 a)] at h
      have hbound : ∀ n ∈ N, ∑ c ∈ u.filter (fun c => c a = n), (∏ i ∈ c.support, x i ^ (c i))
          ≤ (x a) ^ n * (∏ i ∈ T', (1 - x i)⁻¹) := by
        intro n _
        set s : Finset (σ →₀ ℕ) := u.filter (fun c => c a = n) with hs
        set v : Finset (σ →₀ ℕ) := s.image (Finsupp.erase a) with hv
        have hinj : Set.InjOn (Finsupp.erase a) (s : Set (σ →₀ ℕ)) := by
          intro c1 hc1 c2 hc2 heq
          simp only [Finset.mem_coe, hs, Finset.mem_filter] at hc1 hc2
          rw [← Finsupp.single_add_erase a c1, ← Finsupp.single_add_erase a c2, hc1.2, hc2.2,
            heq]
        have hvsub : ∀ c' ∈ v, c'.support ⊆ T' := by
          intro c' hc'
          rw [hv, Finset.mem_image] at hc'
          obtain ⟨c, hc, hce⟩ := hc'
          rw [hs, Finset.mem_filter] at hc
          rw [← hce]
          intro i hi
          rw [Finsupp.support_erase, Finset.mem_erase] at hi
          obtain ⟨hne, hci⟩ := hi
          rcases Finset.mem_insert.mp (hu c hc.1 hci) with h | h
          · exact absurd h hne
          · exact h
        have hvbound : ∑ c' ∈ v, (∏ i ∈ c'.support, x i ^ (c' i))
            ≤ ∏ i ∈ T', (1 - x i)⁻¹ := ih v hvsub
        have hstep : ∑ c ∈ s, (∏ i ∈ c.support, x i ^ (c i))
            = (x a) ^ n * ∑ c' ∈ v, (∏ i ∈ c'.support, x i ^ (c' i)) := by
          rw [hv, Finset.sum_image hinj, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [hs, Finset.mem_filter] at hc
          rw [prod_support_erase x a c, hc.2]
        rw [hstep]
        exact mul_le_mul_of_nonneg_left hvbound (pow_nonneg (hx0 a) n)
      calc ∑ n ∈ N, (∑ c ∈ u.filter (fun c => c a = n), (∏ i ∈ c.support, x i ^ (c i)))
          ≤ ∑ n ∈ N, (x a) ^ n * (∏ i ∈ T', (1 - x i)⁻¹) := Finset.sum_le_sum hbound
        _ = (∑ n ∈ N, (x a) ^ n) * (∏ i ∈ T', (1 - x i)⁻¹) := by rw [Finset.sum_mul]
        _ ≤ (1 - x a)⁻¹ * (∏ i ∈ T', (1 - x i)⁻¹) := mul_le_mul_of_nonneg_right hgeom hB

theorem summable_finsupp_prod_pow {σ : Type*} {x : σ → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1) (hx : Summable x) :
    Summable (fun c : σ →₀ ℕ => ∏ i ∈ c.support, x i ^ (c i)) := by
  classical
  have hf : ∀ c : σ →₀ ℕ, 0 ≤ ∏ i ∈ c.support, x i ^ (c i) :=
    fun c => Finset.prod_nonneg (fun i _ => pow_nonneg (hx0 i) _)
  have hev : ∀ᶠ i in Filter.cofinite, x i < (1 / 2 : ℝ) :=
    hx.tendsto_cofinite_zero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hfin : {i : σ | (1 / 2 : ℝ) ≤ x i}.Finite :=
    (Filter.eventually_cofinite.mp hev).subset (fun i hi => not_lt.mpr hi)
  set L : Finset σ := hfin.toFinset with hL
  have hLmem : ∀ i, i ∈ L ↔ (1 / 2 : ℝ) ≤ x i := fun i => by
    rw [hL]; exact hfin.mem_toFinset
  have hLneg : ∀ i, i ∉ L → x i < 1 / 2 := fun i hi => not_le.mp (fun h => hi ((hLmem i).mpr h))
  refine summable_of_sum_le hf (c := (∏ i ∈ L, (1 - x i)⁻¹) * Real.exp (2 * ∑' i, x i)) ?_
  intro u
  set T : Finset σ := u.biUnion (fun c => c.support) with hT
  have huT : ∀ c ∈ u, c.support ⊆ T := fun c hc => by
    rw [hT]; exact Finset.subset_biUnion_of_mem (fun c => c.support) hc
  have hmain : ∑ c ∈ u, (∏ i ∈ c.support, x i ^ (c i)) ≤ ∏ i ∈ T, (1 - x i)⁻¹ :=
    sum_le_prod_inv hx0 hx1 T u huT
  have hTsplit : (∏ i ∈ T, (1 - x i)⁻¹)
      = (∏ i ∈ T.filter (fun i => i ∈ L), (1 - x i)⁻¹)
        * (∏ i ∈ T.filter (fun i => ¬ i ∈ L), (1 - x i)⁻¹) :=
    (Finset.prod_filter_mul_prod_filter_not T (fun i => i ∈ L) (fun i => (1 - x i)⁻¹)).symm
  have hprod1 : (∏ i ∈ T.filter (fun i => i ∈ L), (1 - x i)⁻¹) ≤ ∏ i ∈ L, (1 - x i)⁻¹ := by
    refine Finset.prod_le_prod_of_subset_of_one_le₀ (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i _ => inv_nonneg.mpr (by linarith [hx1 i])) (fun i _ _ => ?_)
    rw [one_le_inv₀ (by linarith [hx1 i] : (0 : ℝ) < 1 - x i)]
    linarith [hx0 i]
  have hprod2 : (∏ i ∈ T.filter (fun i => ¬ i ∈ L), (1 - x i)⁻¹) ≤ Real.exp (2 * ∑' i, x i) := by
    have hle : ∀ i ∈ T.filter (fun i => ¬ i ∈ L), (1 - x i)⁻¹ ≤ Real.exp (2 * x i) := by
      intro i hi
      have hxi : x i < 1 / 2 := hLneg i (Finset.mem_filter.mp hi).2
      have h2 : (1 - x i)⁻¹ ≤ 1 + 2 * x i := by
        rw [inv_le_iff_one_le_mul₀ (by linarith [hx1 i] : (0 : ℝ) < 1 - x i)]
        nlinarith [hx0 i, hxi]
      calc (1 - x i)⁻¹ ≤ 1 + 2 * x i := h2
        _ ≤ Real.exp (2 * x i) := by linarith [Real.add_one_le_exp (2 * x i)]
    calc (∏ i ∈ T.filter (fun i => ¬ i ∈ L), (1 - x i)⁻¹)
        ≤ ∏ i ∈ T.filter (fun i => ¬ i ∈ L), Real.exp (2 * x i) :=
          Finset.prod_le_prod₀ (fun i _ => inv_nonneg.mpr (by linarith [hx1 i])) hle
      _ = Real.exp (∑ i ∈ T.filter (fun i => ¬ i ∈ L), 2 * x i) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (2 * ∑' i, x i) := by
          apply Real.exp_le_exp.mpr
          have hs : ∑ i ∈ T.filter (fun i => ¬ i ∈ L), x i ≤ ∑' i, x i :=
            hx.sum_le_tsum _ (fun i _ => hx0 i)
          calc ∑ i ∈ T.filter (fun i => ¬ i ∈ L), 2 * x i
              = 2 * ∑ i ∈ T.filter (fun i => ¬ i ∈ L), x i := (Finset.mul_sum _ _ _).symm
            _ ≤ 2 * ∑' i, x i := by linarith
  refine le_trans hmain ?_
  rw [hTsplit]
  exact mul_le_mul hprod1 hprod2
    (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (by linarith [hx1 i])))
    (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (by linarith [hx1 i])))

end NK.HeckeL.Series
