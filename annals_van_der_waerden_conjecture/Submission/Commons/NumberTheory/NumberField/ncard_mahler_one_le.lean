import Mathlib
import Submission.Commons.NumberTheory.NumberField.ncard_max_normAtPlace_le

set_option maxHeartbeats 1000000

open NumberField
open scoped Classical

namespace Commons.NumberTheory.NumberField

noncomputable section

/-- The Mahler measure of an element of a number field: the product over the infinite places of
`(max 1 |a|_w) ^ w.mult`. -/
def mahlerK (K : Type*) [Field K] [NumberField K] (a : K) : ℝ :=
  ∏ w : NumberField.InfinitePlace K,
    (max 1 (NumberField.mixedEmbedding.normAtPlace w
      (NumberField.mixedEmbedding K a))) ^ w.mult

/-- The place norm of an integer is its absolute value. -/
lemma infinitePlace_intCast_apply {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) (k : ℤ) :
    w ((k : K)) = |(k : ℝ)| := by
  rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.apply, map_intCast]
  rw [show (((k : ℤ)) : ℂ) = (((k : ℝ)) : ℂ) by push_cast; ring]
  exact RCLike.norm_ofReal k

/-- Each factor of the Mahler measure is at most the Mahler measure. -/
lemma normAtPlace_le_mahlerK {K : Type*} [Field K] [NumberField K] (a : K)
    (w₀ : NumberField.InfinitePlace K) :
    NumberField.mixedEmbedding.normAtPlace w₀ (NumberField.mixedEmbedding K a) ≤ mahlerK K a := by
  rw [mahlerK]
  have hstep : (max 1 (NumberField.mixedEmbedding.normAtPlace w₀
        (NumberField.mixedEmbedding K a))) ^ w₀.mult ≤
      ∏ w : NumberField.InfinitePlace K,
        (max 1 (NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K a))) ^ w.mult := by
    have hsub : ({w₀} : Finset (NumberField.InfinitePlace K)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have h := Finset.prod_le_prod_of_subset_of_one_le
      (s := {w₀}) (t := Finset.univ)
      (f := fun w : NumberField.InfinitePlace K =>
        (max 1 (NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K a))) ^ w.mult)
      hsub (fun w _ => by positivity) (fun w _ _ => one_le_pow₀ (le_max_left _ _))
    simpa using h
  have h3 : max 1 (NumberField.mixedEmbedding.normAtPlace w₀
        (NumberField.mixedEmbedding K a)) ≤
      (max 1 (NumberField.mixedEmbedding.normAtPlace w₀
        (NumberField.mixedEmbedding K a))) ^ w₀.mult := by
    calc max 1 (NumberField.mixedEmbedding.normAtPlace w₀
          (NumberField.mixedEmbedding K a))
        = (max 1 (NumberField.mixedEmbedding.normAtPlace w₀
          (NumberField.mixedEmbedding K a))) ^ 1 := (pow_one _).symm
      _ ≤ (max 1 (NumberField.mixedEmbedding.normAtPlace w₀
          (NumberField.mixedEmbedding K a))) ^ w₀.mult :=
          pow_le_pow_right₀ (le_max_left _ _) (by have := w₀.mult_pos; omega)
  exact (le_trans (le_max_right _ _) (le_trans h3 hstep))

/-- The number of rational integers of Mahler measure at most `Y` is bounded by `5 * Y`. -/
lemma ncard_rat_mahler_le {K : Type*} [Field K] [NumberField K] (Y : ℝ) (hY : 1 ≤ Y) :
    (({α : NumberField.RingOfIntegers K |
        ((α : NumberField.RingOfIntegers K) : K) ∈ Set.range (algebraMap ℤ K) ∧
          mahlerK K (((α : NumberField.RingOfIntegers K) : K)) ≤ Y} : Set _).ncard : ℝ) ≤ 5 * Y := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
  set f : NumberField.RingOfIntegers K → ℤ := fun α =>
    if h : ((α : NumberField.RingOfIntegers K) : K) ∈ Set.range (algebraMap ℤ K)
      then Classical.choose (Set.mem_range.mp h) else 0 with hf_def
  set s : Set (NumberField.RingOfIntegers K) := {α : NumberField.RingOfIntegers K |
      ((α : NumberField.RingOfIntegers K) : K) ∈ Set.range (algebraMap ℤ K) ∧
        mahlerK K (((α : NumberField.RingOfIntegers K) : K)) ≤ Y} with hs_def
  have hf_mem : ∀ α ∈ s, f α ∈ (Finset.Icc (-(⌈Y⌉₊ : ℤ)) (⌈Y⌉₊ : ℤ) : Finset ℤ) := by
    intro α hα
    have hα' := hα
    simp only [hs_def] at hα'
    obtain ⟨hr, hM⟩ := hα'
    have hfα : f α = Classical.choose (Set.mem_range.mp hr) := by
      simp only [hf_def]
      rw [dif_pos hr]
    have hspec : (((Classical.choose (Set.mem_range.mp hr) : ℤ)) : K) =
        ((α : NumberField.RingOfIntegers K) : K) := by
      simpa using Classical.choose_spec (Set.mem_range.mp hr)
    have h1 : w₀ ((Classical.choose (Set.mem_range.mp hr) : ℤ) : K) =
        |((Classical.choose (Set.mem_range.mp hr) : ℤ) : ℝ)| :=
      infinitePlace_intCast_apply w₀ _
    have habs : |((Classical.choose (Set.mem_range.mp hr) : ℤ) : ℝ)| ≤ Y := by
      rw [← h1, hspec]
      calc w₀ (((α : NumberField.RingOfIntegers K) : K))
          = NumberField.mixedEmbedding.normAtPlace w₀
              (NumberField.mixedEmbedding K (((α : NumberField.RingOfIntegers K) : K))) :=
            (NumberField.mixedEmbedding.normAtPlace_apply w₀ _).symm
        _ ≤ mahlerK K (((α : NumberField.RingOfIntegers K) : K)) :=
            normAtPlace_le_mahlerK _ w₀
        _ ≤ Y := hM
    rw [hfα, Finset.mem_Icc]
    have h3 : |Classical.choose (Set.mem_range.mp hr)| ≤ (⌈Y⌉₊ : ℤ) := by
      have h4 : ((|Classical.choose (Set.mem_range.mp hr)| : ℤ) : ℝ) ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := by
        rw [Int.cast_abs]
        exact le_trans habs (Nat.le_ceil Y)
      exact_mod_cast h4
    exact abs_le.mp h3
  have hf_inj : Set.InjOn f s := by
    intro a ha b hb hab
    have ha' := ha
    have hb' := hb
    simp only [hs_def] at ha' hb'
    have hfa : ((f a : ℤ) : K) = ((a : NumberField.RingOfIntegers K) : K) := by
      have h1 : f a = Classical.choose (Set.mem_range.mp ha'.1) := by
        simp only [hf_def]
        rw [dif_pos ha'.1]
      rw [h1]
      simpa using Classical.choose_spec (Set.mem_range.mp ha'.1)
    have hfb : ((f b : ℤ) : K) = ((b : NumberField.RingOfIntegers K) : K) := by
      have h1 : f b = Classical.choose (Set.mem_range.mp hb'.1) := by
        simp only [hf_def]
        rw [dif_pos hb'.1]
      rw [h1]
      simpa using Classical.choose_spec (Set.mem_range.mp hb'.1)
    apply NumberField.RingOfIntegers.coe_injective (K := K)
    change ((a : NumberField.RingOfIntegers K) : K) =
      ((b : NumberField.RingOfIntegers K) : K)
    rw [← hfa, ← hfb, hab]
  have h1 : s.ncard ≤ (Finset.Icc (-(⌈Y⌉₊ : ℤ)) (⌈Y⌉₊ : ℤ) : Finset ℤ).card := by
    rw [← Set.ncard_coe_finset (Finset.Icc (-(⌈Y⌉₊ : ℤ)) (⌈Y⌉₊ : ℤ))]
    exact Set.ncard_le_ncard_of_injOn f (fun α hα => by
        simpa only [Finset.mem_coe] using hf_mem α hα) hf_inj (Finset.finite_toSet _)
  have hcard : (Finset.Icc (-(⌈Y⌉₊ : ℤ)) (⌈Y⌉₊ : ℤ) : Finset ℤ).card = 2 * ⌈Y⌉₊ + 1 := by
    rw [Int.card_Icc]
    omega
  have h4 : ((2 * ⌈Y⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * Y := by
    have hceil : ((⌈Y⌉₊ : ℝ)) < Y + 1 := Nat.ceil_lt_add_one (le_trans zero_le_one hY)
    push_cast
    linarith
  calc (s.ncard : ℝ) ≤ ((Finset.Icc (-(⌈Y⌉₊ : ℤ)) (⌈Y⌉₊ : ℤ) : Finset ℤ).card : ℝ) := by
        exact_mod_cast h1
    _ = ((2 * ⌈Y⌉₊ + 1 : ℕ) : ℝ) := by rw [hcard]
    _ ≤ 5 * Y := h4

/-- **The `λ = 1` per-element Mahler count.**  The number of algebraic integers of Mahler measure
at most `Y` in a number field `K` of degree `n ≥ 2` is at most `200000 ^ n * Y * (1 + log Y) ^ (n-1)`.

The non-rational elements are counted by `ncard_max_normAtPlace_le` with `λ = 1` (every non-zero
algebraic integer has house at least `1`), and the rational integers `k` have Mahler measure at
least `|k|`, so there are at most `2 * ⌈Y⌉₊ + 1 ≤ 5 * Y` of them. -/
lemma mahler_card_le {K : Type*} [Field K] [NumberField K] (hn : 2 ≤ Module.finrank ℚ K)
    (Y : ℝ) (hY : 1 ≤ Y) :
    (Nat.card {α : NumberField.RingOfIntegers K //
        mahlerK K ((α : NumberField.RingOfIntegers K) : K) ≤ Y} : ℝ) ≤
      (200000 : ℝ) ^ Module.finrank ℚ K * Y *
        (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) := by
  classical
  set n := Module.finrank ℚ K with hn_def
  have hn2 : 2 ≤ n := by rw [hn_def]; exact hn
  let S : Set (𝓞 K) := {α | mahlerK K ((α : 𝓞 K) : K) ≤ Y}
  let Nset : Set (𝓞 K) :=
    {α | ((α : 𝓞 K) : K) ∉ Set.range (algebraMap ℤ K) ∧ mahlerK K ((α : 𝓞 K) : K) ≤ Y}
  let Rset : Set (𝓞 K) :=
    {α | ((α : 𝓞 K) : K) ∈ Set.range (algebraMap ℤ K) ∧ mahlerK K ((α : 𝓞 K) : K) ≤ Y}
  have hconv : (Nat.card {α : NumberField.RingOfIntegers K //
        mahlerK K ((α : NumberField.RingOfIntegers K) : K) ≤ Y} : ℝ) = (S.ncard : ℝ) := by
    exact_mod_cast Nat.card_coe_set_eq S
  rw [hconv]
  have hunion : S = Nset ∪ Rset := by
    ext α
    simp only [S, Nset, Rset, Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hunion]
  have hN : (Nset.ncard : ℝ) ≤ (100000 : ℝ) ^ n * Y * (1 + Real.log Y) ^ (n - 1) := by
    have hh := ncard_max_normAtPlace_le (K := K) hn Y 1 hY le_rfl (fun α hα => by
      have h0 : ((α : NumberField.RingOfIntegers K) : K) ≠ 0 := by
        intro h
        exact hα ⟨0, by rw [map_zero]; exact h.symm⟩
      exact NumberField.one_le_house_of_isIntegral (α := ((α : NumberField.RingOfIntegers K) : K))
        α.2 h0)
    simp only [div_one] at hh
    rw [← hn_def] at hh
    have hc : (Nset.ncard : ℝ) = (Nat.card {α : NumberField.RingOfIntegers K //
        ((α : NumberField.RingOfIntegers K) : K) ∉ Set.range (algebraMap ℤ K) ∧
          (∏ w : NumberField.InfinitePlace K,
            (max 1 (NumberField.mixedEmbedding.normAtPlace w
              (NumberField.mixedEmbedding K ((α : NumberField.RingOfIntegers K) : K)))) ^
                NumberField.InfinitePlace.mult w) ≤ Y} : ℝ) := by
      exact_mod_cast (Nat.card_coe_set_eq Nset).symm
    exact le_trans (le_of_eq hc) hh
  have hR : (Rset.ncard : ℝ) ≤ 5 * Y := ncard_rat_mahler_le (K := K) Y hY
  have hsplit : ((Nset ∪ Rset).ncard : ℝ) ≤ (Nset.ncard : ℝ) + (Rset.ncard : ℝ) := by
    exact_mod_cast Set.ncard_union_le Nset Rset
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hP : (1 : ℝ) ≤ (1 + Real.log Y) ^ (n - 1) := one_le_pow₀ (by linarith)
  have h2n : (4 : ℝ) ≤ 2 ^ n := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn2
  have h100 : (100000 : ℝ) ^ 2 ≤ 100000 ^ n :=
    pow_le_pow_right₀ (by norm_num) hn2
  have hpoweq : (200000 : ℝ) ^ n = 2 ^ n * 100000 ^ n := by
    rw [← mul_pow]; norm_num
  have hmain : (100000 : ℝ) ^ n + 5 ≤ 200000 ^ n := by
    rw [hpoweq]
    nlinarith [h2n, h100, pow_nonneg (by norm_num : (0 : ℝ) ≤ 100000) n]
  have hfinal : (100000 : ℝ) ^ n * Y * (1 + Real.log Y) ^ (n - 1) + 5 * Y ≤
      (200000 : ℝ) ^ n * Y * (1 + Real.log Y) ^ (n - 1) := by
    have hYP : 0 ≤ Y * (1 + Real.log Y) ^ (n - 1) :=
      mul_nonneg (by linarith) (le_trans zero_le_one hP)
    have h5 : 5 * Y ≤ 5 * (Y * (1 + Real.log Y) ^ (n - 1)) := by
      nlinarith [hP, mul_nonneg (by linarith : (0 : ℝ) ≤ Y)
        (by linarith : (0 : ℝ) ≤ (1 + Real.log Y) ^ (n - 1))]
    nlinarith [hmain, hYP, h5, mul_le_mul_of_nonneg_right hmain hYP]
  calc ((Nset ∪ Rset).ncard : ℝ)
      ≤ (100000 : ℝ) ^ n * Y * (1 + Real.log Y) ^ (n - 1) + 5 * Y := by
        linarith [hsplit, hN, hR]
    _ ≤ (200000 : ℝ) ^ n * Y * (1 + Real.log Y) ^ (n - 1) := hfinal

theorem ncard_mahler_one_le : ∃ C : ℝ, 0 < C ∧
    ∀ (K : Type) [Field K] [NumberField K], 2 ≤ Module.finrank ℚ K →
    ∀ (Y : ℝ), 1 ≤ Y →
    (Nat.card {α : NumberField.RingOfIntegers K //
        (∏ w : NumberField.InfinitePlace K,
          (max 1 (NumberField.mixedEmbedding.normAtPlace w
            (NumberField.mixedEmbedding K ((α : NumberField.RingOfIntegers K) : K)))) ^
              NumberField.InfinitePlace.mult w) ≤ Y} : ℝ)
      ≤ C ^ Module.finrank ℚ K * Y * (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) := by
  refine ⟨200000, by norm_num, fun K _ _ hn Y hY => ?_⟩
  exact mahler_card_le hn Y hY

end

end Commons.NumberTheory.NumberField
