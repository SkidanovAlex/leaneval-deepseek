import Mathlib
import Submission.Commons.NumberTheory.Counting.ncard_prod_max_one_abs_le
import Submission.Commons.NumberTheory.NumberField.abs_norm_eq_norm_embedding_sq_of_finrank_two
import Submission.Commons.NumberTheory.NumberField.units_rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one
import Submission.Commons.NumberTheory.NumberField.basis_one_omega_of_finrank_two
import Submission.Commons.NumberTheory.NumberField.house_eq_norm_embedding_of_finrank_two

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.NumberField

open NumberField
open scoped _root_.NumberField

lemma norm_intCast_field {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] (m : ℤ) :
    Algebra.norm ℚ ((m : K)) = (m : ℚ) ^ Module.finrank ℚ K := by
  have h : ((m : K)) = algebraMap ℚ K ((m : ℚ)) := (map_intCast (algebraMap ℚ K) m).symm
  rw [h]
  exact Algebra.norm_algebraMap (R := ℚ) (S := K) (x := (m : ℚ))

lemma units_coe_notMem_range {K : Type*} [Field K] [NumberField K]
    (u : (NumberField.RingOfIntegers K)ˣ) (hu : ¬ IsOfFinOrder u) :
    ((u : NumberField.RingOfIntegers K) : K) ∉ Set.range (algebraMap ℤ K) := by
  intro hmem
  obtain ⟨m, hm⟩ := Set.mem_range.mp hmem
  have hm' : ((u : NumberField.RingOfIntegers K) : K) = (m : K) := hm.symm
  have h1 : |Algebra.norm ℚ ((u : NumberField.RingOfIntegers K) : K)| = 1 :=
    NumberField.Units.norm (K := K) u
  rw [hm', norm_intCast_field] at h1
  have hd0 : Module.finrank ℚ K ≠ 0 := (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have h2 : |(m : ℚ)| = 1 := by
    rw [abs_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg (m : ℚ)) hd0).mp h1
  have h3 : m = 1 ∨ m = -1 := by
    rcases (abs_eq (by norm_num : (0:ℚ) ≤ 1)).mp h2 with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hcoe : ((u : NumberField.RingOfIntegers K) : NumberField.RingOfIntegers K) =
      (m : NumberField.RingOfIntegers K) := by
    apply NumberField.RingOfIntegers.coe_injective (K := K)
    rw [map_intCast]
    exact hm'
  rcases h3 with rfl | rfl
  · have : u = 1 := by
      apply Units.ext
      simpa using hcoe
    exact hu (this ▸ isOfFinOrder_iff_pow_eq_one.mpr ⟨1, le_refl 1, one_pow 1⟩)
  · have : u = -1 := by
      apply Units.ext
      simpa using hcoe
    refine hu (this ▸ ?_)
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩

theorem ncard_norm_le {K : Type*} [Field K] [NumberField K] (hn : 2 ≤ Module.finrank ℚ K)
    (B lam : ℝ) (hB : 1 ≤ B) (hlam : 1 ≤ lam)
    (hsep : ∀ α : NumberField.RingOfIntegers K, ((α : K)) ∉ Set.range (algebraMap ℤ K) →
      lam ≤ NumberField.house ((α : K))) :
    (Nat.card {α : NumberField.RingOfIntegers K // ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
        |Algebra.norm ℚ ((α : K))| ≤ B} : ℝ) ≤
      (100000 : ℝ) ^ Module.finrank ℚ K * B *
        (1 + Real.log B) ^ (Module.finrank ℚ K - 1) / lam := by
  classical
  by_cases hrank : NumberField.Units.rank K = 0
  · -- imaginary quadratic case
    have h2 : Module.finrank ℚ K = 2 := by
      have h1 := units_rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one K
      have h3 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
      have hr2pos : 1 ≤ NumberField.InfinitePlace.nrComplexPlaces K := by
        by_contra h; push Not at h; omega
      have hsum : NumberField.InfinitePlace.nrRealPlaces K +
          NumberField.InfinitePlace.nrComplexPlaces K = 1 := by omega
      omega
    have h0 : NumberField.InfinitePlace.nrRealPlaces K = 0 := by
      have h1 := units_rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one K
      have h3 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
      have hr2pos : 1 ≤ NumberField.InfinitePlace.nrComplexPlaces K := by
        by_contra h; push Not at h; omega
      have hsum : NumberField.InfinitePlace.nrRealPlaces K +
          NumberField.InfinitePlace.nrComplexPlaces K = 1 := by omega
      omega
    obtain ⟨b, hb0⟩ := basis_one_omega_of_finrank_two h2
    let σ : K →+* ℂ := Classical.arbitrary (K →+* ℂ)
    let ω : 𝓞 K := b 1
    have hω_notint : ((ω : 𝓞 K) : K) ∉ Set.range (algebraMap ℤ K) := by
      intro hmem
      obtain ⟨m, hm⟩ := Set.mem_range.mp hmem
      have hcoe : (ω : 𝓞 K) = (m : 𝓞 K) := by
        apply NumberField.RingOfIntegers.coe_injective (K := K)
        rw [map_intCast]
        exact hm.symm
      have hli := Fintype.linearIndependent_iff.mp b.linearIndependent
      have hg : (∑ i : Fin 2, (![-m, 1] : Fin 2 → ℤ) i • b i) = 0 := by
        rw [Fin.sum_univ_two]
        simp [hb0, hcoe, ω]
      have h1 := hli ![-m, 1] hg 1
      norm_num at h1
    set p : ℝ := (σ ((ω : 𝓞 K) : K)).re with hp
    set q : ℝ := (σ ((ω : 𝓞 K) : K)).im with hq
    set m0 : ℤ := ⌊p + 1/2⌋ with hm0
    have hpm0_abs : |p - (m0 : ℝ)| ≤ 1/2 := by
      have hl : (m0 : ℝ) ≤ p + 1/2 := by rw [hm0]; exact Int.floor_le _
      have hh : p + 1/2 < (m0 : ℝ) + 1 := by rw [hm0]; exact Int.lt_floor_add_one _
      rw [abs_le]; constructor <;> linarith
    have hσpq : σ ((ω : 𝓞 K) : K) = (p : ℂ) + (q : ℂ) * Complex.I := by
      rw [← Complex.re_add_im (σ ((ω : 𝓞 K) : K)), hp, hq]
    let ω' : 𝓞 K := ω - (m0 : 𝓞 K)
    have hω'nt : ((ω' : 𝓞 K) : K) ∉ Set.range (algebraMap ℤ K) := by
      intro hmem
      obtain ⟨n, hn⟩ := Set.mem_range.mp hmem
      apply hω_notint
      refine ⟨n + m0, ?_⟩
      have hsub : ((ω' : 𝓞 K) : K) = ((ω : 𝓞 K) : K) - ((m0 : ℤ) : K) := by
        rw [show ω' = ω - (m0 : 𝓞 K) from rfl]
        push_cast
        congr 1
      have hsub' : ((ω : 𝓞 K) : K) = ((ω' : 𝓞 K) : K) + ((m0 : ℤ) : K) := by rw [hsub]; ring
      have hstep : (algebraMap ℤ K) (n + m0) = ((ω' : 𝓞 K) : K) + ((m0 : ℤ) : K) := by
        rw [map_add, ← hn]
        congr 1
      exact hstep.trans hsub'.symm
    have hlam_le_ω' : lam ≤ ‖σ ((ω' : 𝓞 K) : K)‖ := by
      have h := hsep ω' hω'nt
      rwa [house_eq_norm_embedding_of_finrank_two h2 h0 σ ((ω' : 𝓞 K) : K)] at h
    have hσω' : σ ((ω' : 𝓞 K) : K) =
        ((p - (m0 : ℝ) : ℝ) : ℂ) + (q : ℂ) * Complex.I := by
      have hsub : ((ω' : 𝓞 K) : K) = ((ω : 𝓞 K) : K) - ((m0 : ℤ) : K) := by
        rw [show ω' = ω - (m0 : 𝓞 K) from rfl]
        push_cast
        congr 1
      rw [hsub, map_sub, hσpq]
      simp only [map_intCast]
      push_cast
      ring
    have hnorm_sq : ‖σ ((ω' : 𝓞 K) : K)‖ ^ 2 = (p - (m0 : ℝ)) ^ 2 + q ^ 2 := by
      rw [hσω', Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have hnorm_eq : ‖σ ((ω' : 𝓞 K) : K)‖ = Real.sqrt ((p - (m0 : ℝ)) ^ 2 + q ^ 2) := by
      rw [← hnorm_sq, Real.sqrt_sq (norm_nonneg _)]
    have hqm : (1:ℝ)/2 ≤ |q| := by
      have ht : (0:ℝ) ≤ (p - (m0 : ℝ)) ^ 2 + q ^ 2 := by positivity
      have hge1 : (1:ℝ) ≤ Real.sqrt ((p - (m0 : ℝ)) ^ 2 + q ^ 2) := by
        rw [← hnorm_eq]
        exact le_trans hlam hlam_le_ω'
      have hsq1 : (1:ℝ) ≤ (p - (m0 : ℝ)) ^ 2 + q ^ 2 := by
        have := Real.sq_sqrt ht
        nlinarith [Real.sqrt_nonneg ((p - (m0 : ℝ)) ^ 2 + q ^ 2), hge1, this]
      have hpm : (p - (m0 : ℝ)) ^ 2 ≤ 1/4 := by
        nlinarith [hpm0_abs, abs_nonneg (p - (m0 : ℝ)), sq_abs (p - (m0 : ℝ))]
      have hq2 : (1:ℝ)/4 ≤ q^2 := by linarith
      nlinarith [sq_abs q, abs_nonneg q]
    have hlam_le_2q : lam ≤ 2 * |q| := by
      have hsqrt_le : Real.sqrt ((p - (m0 : ℝ)) ^ 2 + q ^ 2) ≤ |p - (m0 : ℝ)| + |q| := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        nlinarith [sq_abs (p - (m0:ℝ)), sq_abs q, abs_nonneg (p - (m0:ℝ)), abs_nonneg q]
      have h2' : lam ≤ |p - (m0 : ℝ)| + |q| := by
        rw [hnorm_eq] at hlam_le_ω'
        exact le_trans hlam_le_ω' hsqrt_le
      linarith
    have hsqrtB1 : (1:ℝ) ≤ Real.sqrt B := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hB
    -- bounds for the coordinates of any element of the set
    have hprod_le : ∀ α : {α : 𝓞 K // ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
        |Algebra.norm ℚ ((α : K))| ≤ B},
        |(b.repr α.1 0 : ℝ) + m0 * (b.repr α.1 1 : ℝ)| ≤ 2 * Real.sqrt B ∧
        |(b.repr α.1 1 : ℝ)| ≤ 2 * Real.sqrt B / lam := by
      intro α
      have hαnt : ((α.1 : K)) ∉ Set.range (algebraMap ℤ K) := α.2.1
      have hαB : |Algebra.norm ℚ ((α.1 : K))| ≤ B := α.2.2
      have hαB' : |((Algebra.norm ℚ ((α.1 : K))) : ℝ)| ≤ B := by
        rw [← Rat.cast_abs]; exact hαB
      have hrepr : ((α.1 : 𝓞 K) : K) = ((b.repr α.1 0 : ℤ) : K) +
          ((b.repr α.1 1 : ℤ) : K) * ((b 1 : 𝓞 K) : K) := by
        have h := b.sum_repr α.1
        rw [Fin.sum_univ_two, hb0] at h
        have hK : (((b.repr α.1 0 : ℤ) : 𝓞 K) + ((b.repr α.1 1 : ℤ) : 𝓞 K) * b 1) = α.1 := by
          conv_rhs => rw [← h]
          simp only [zsmul_eq_mul, mul_one]
        have h2 := congrArg (algebraMap (𝓞 K) K) hK
        rw [map_add, map_mul, map_intCast, map_intCast] at h2
        simpa using h2.symm
      have hσα : σ ((α.1 : 𝓞 K) : K) =
          (((b.repr α.1 0 : ℝ) + (b.repr α.1 1 : ℝ) * p : ℝ) : ℂ) +
          (((b.repr α.1 1 : ℝ) * q : ℝ) : ℂ) * Complex.I := by
        rw [hrepr, map_add, map_mul, hσpq]
        simp only [map_intCast]
        push_cast
        ring
      have him : (σ ((α.1 : 𝓞 K) : K)).im = (b.repr α.1 1 : ℝ) * q := by
        rw [hσα]; simp
      have hare : (σ ((α.1 : 𝓞 K) : K)).re =
          (b.repr α.1 0 : ℝ) + (b.repr α.1 1 : ℝ) * p := by
        rw [hσα]; simp
      have hnormB : ‖σ ((α.1 : 𝓞 K) : K)‖ ≤ Real.sqrt B := by
        have h := abs_norm_eq_norm_embedding_sq_of_finrank_two h2 h0 σ ((α.1 : 𝓞 K) : K)
        have hsq : ‖σ ((α.1 : 𝓞 K) : K)‖ ^ 2 ≤ B := by rw [← h]; exact hαB'
        calc ‖σ ((α.1 : 𝓞 K) : K)‖ = Real.sqrt (‖σ ((α.1 : 𝓞 K) : K)‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hsq
      have hbb_le : |(b.repr α.1 1 : ℝ)| ≤ 2 * Real.sqrt B / lam := by
        have hqpos : 0 < |q| := by linarith [hqm]
        have h1 : |(b.repr α.1 1 : ℝ)| * |q| ≤ Real.sqrt B := by
          have h := Complex.abs_im_le_norm (σ ((α.1 : 𝓞 K) : K))
          rw [him, abs_mul] at h
          exact le_trans h hnormB
        rw [le_div_iff₀ (by linarith : (0:ℝ) < lam)]
        calc |(b.repr α.1 1 : ℝ)| * lam ≤ |(b.repr α.1 1 : ℝ)| * (2 * |q|) :=
              mul_le_mul_of_nonneg_left hlam_le_2q (abs_nonneg _)
          _ = 2 * (|(b.repr α.1 1 : ℝ)| * |q|) := by ring
          _ ≤ 2 * Real.sqrt B := by linarith
      have ha_le : |(b.repr α.1 0 : ℝ) + m0 * (b.repr α.1 1 : ℝ)| ≤ 2 * Real.sqrt B := by
        have h1 : (b.repr α.1 0 : ℝ) + m0 * (b.repr α.1 1 : ℝ) =
            (σ ((α.1 : 𝓞 K) : K)).re - (b.repr α.1 1 : ℝ) * (p - (m0:ℝ)) := by
          rw [hare]; ring
        rw [h1]
        calc |(σ ((α.1 : 𝓞 K) : K)).re - (b.repr α.1 1 : ℝ) * (p - (m0:ℝ))|
            ≤ |(σ ((α.1 : 𝓞 K) : K)).re| + |(b.repr α.1 1 : ℝ) * (p - (m0:ℝ))| :=
              abs_sub _ _
          _ ≤ ‖σ ((α.1 : 𝓞 K) : K)‖ + |(b.repr α.1 1 : ℝ)| * |p - (m0:ℝ)| := by
              rw [abs_mul]
              exact add_le_add (Complex.abs_re_le_norm _) le_rfl
          _ ≤ Real.sqrt B + (2 * Real.sqrt B / lam) * (1/2) := by
              apply add_le_add hnormB
              exact mul_le_mul hbb_le hpm0_abs (abs_nonneg _) (by positivity)
          _ ≤ 2 * Real.sqrt B := by
              have hle : (2 * Real.sqrt B / lam) * (1/2) ≤ Real.sqrt B := by
                rw [show (2 * Real.sqrt B / lam) * (1/2) = Real.sqrt B / lam by ring,
                  div_le_iff₀ (by linarith : (0:ℝ) < lam)]
                nlinarith [Real.sqrt_nonneg B, hlam]
              linarith [Real.sqrt_nonneg B]
      exact ⟨ha_le, hbb_le⟩
    let M : ℝ := 4 * B / lam
    have hfin : ({x : Fin 2 → ℤ | (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M}).Finite := by
      apply Set.Finite.subset
        (Set.Finite.pi (fun _ : Fin 2 => Set.finite_Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)))
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp only [Set.mem_univ, Set.mem_pi, true_implies]
      intro i
      have h1 : max 1 |((x i : ℤ) : ℝ)| ≤ M := by
        have hsub : ({i} : Finset (Fin 2)) ⊆ Finset.univ := Finset.subset_univ _
        have := Finset.prod_le_prod_of_subset_of_one_le
          (f := fun j : Fin 2 => max 1 |((x j : ℤ) : ℝ)|) hsub
          (fun j _ => by positivity) (fun j _ _ => le_max_left _ _)
        exact le_trans (by simpa using this) hx
      have h2 : |((x i : ℤ) : ℝ)| ≤ M := le_trans (le_max_right _ _) h1
      have h3 : |((x i : ℤ) : ℝ)| ≤ (⌈M⌉₊ : ℝ) := le_trans h2 (Nat.le_ceil M)
      have h4 : |x i| ≤ (⌈M⌉₊ : ℤ) := by
        rw [← Int.cast_le (R := ℝ), Int.cast_abs, Int.cast_natCast]
        exact h3
      rw [Set.mem_Icc]
      exact abs_le.mp h4
    haveI : Finite {x : Fin 2 → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} := hfin.to_subtype
    by_cases hS : Nonempty {α : 𝓞 K // ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧ |Algebra.norm ℚ ((α : K))| ≤ B}
    · obtain ⟨α0, hα0⟩ := hS
      have hlam_sqrtB : lam ≤ Real.sqrt B := by
        have hnt : ((α0 : K)) ∉ Set.range (algebraMap ℤ K) := hα0.1
        have hB0 : |Algebra.norm ℚ ((α0 : K))| ≤ B := hα0.2
        have h := hsep α0 hnt
        rw [house_eq_norm_embedding_of_finrank_two h2 h0 σ ((α0 : 𝓞 K) : K)] at h
        have hh := abs_norm_eq_norm_embedding_sq_of_finrank_two h2 h0 σ ((α0 : 𝓞 K) : K)
        have hsq : ‖σ ((α0 : 𝓞 K) : K)‖ ^ 2 ≤ B := by
          have : |((Algebra.norm ℚ ((α0 : K))) : ℝ)| ≤ B := by rw [← Rat.cast_abs]; exact hB0
          rw [← hh]; exact this
        have hnormB : ‖σ ((α0 : 𝓞 K) : K)‖ ≤ Real.sqrt B := by
          calc ‖σ ((α0 : 𝓞 K) : K)‖ = Real.sqrt (‖σ ((α0 : 𝓞 K) : K)‖ ^ 2) :=
                (Real.sqrt_sq (norm_nonneg _)).symm
            _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hsq
        exact le_trans h hnormB
      have hM1 : 1 ≤ M := by
        dsimp [M]
        rw [le_div_iff₀ (by linarith : (0:ℝ) < lam)]
        nlinarith [hlam_sqrtB, Real.sq_sqrt (le_trans zero_le_one hB), Real.sqrt_nonneg B]
      set g : {α : 𝓞 K // ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
          |Algebra.norm ℚ ((α : K))| ≤ B} →
          {x : Fin 2 → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} :=
        fun α => ⟨![(b.repr α.1 0 : ℤ) + m0 * (b.repr α.1 1 : ℤ), (b.repr α.1 1 : ℤ)],
          by
            rw [Fin.prod_univ_two]
            have hb1 : max 1 |(((b.repr α.1 1 : ℤ)) : ℝ)| ≤ 2 * Real.sqrt B / lam := by
              rw [max_le_iff]
              refine ⟨?_, (hprod_le α).2⟩
              rw [le_div_iff₀ (by linarith : (0:ℝ) < lam)]
              nlinarith [hsqrtB1, hlam]
            have ha1 : max 1 |((((b.repr α.1 0 : ℤ)) + m0 * (b.repr α.1 1 : ℤ) : ℤ) : ℝ)| ≤
                2 * Real.sqrt B := by
              rw [max_le_iff]
              refine ⟨by linarith [hsqrtB1], ?_⟩
              push_cast
              exact (hprod_le α).1
            calc max 1 |((((b.repr α.1 0 : ℤ)) + m0 * (b.repr α.1 1 : ℤ) : ℤ) : ℝ)| *
                  max 1 |(((b.repr α.1 1 : ℤ)) : ℝ)|
                ≤ (2 * Real.sqrt B) * (2 * Real.sqrt B / lam) :=
                  mul_le_mul ha1 hb1 (by positivity) (by positivity)
              _ = 4 * B / lam := by
                  rw [mul_div_assoc']
                  congr 1
                  nlinarith [Real.sq_sqrt (le_trans zero_le_one hB)]
              _ = M := rfl⟩ with hgdef
      have hg_inj : Function.Injective g := by
        intro α β h
        have h0 : (b.repr α.1 0 : ℤ) + m0 * (b.repr α.1 1 : ℤ) =
            (b.repr β.1 0 : ℤ) + m0 * (b.repr β.1 1 : ℤ) := by
          have := congrFun (congrArg Subtype.val h) 0
          simpa [hgdef] using this
        have h1 : (b.repr α.1 1 : ℤ) = (b.repr β.1 1 : ℤ) := by
          have := congrFun (congrArg Subtype.val h) 1
          simpa [hgdef] using this
        have ha : b.repr α.1 0 = b.repr β.1 0 := by
          rw [h1] at h0; linarith
        apply Subtype.ext
        apply b.repr.injective
        apply Finsupp.ext
        intro i
        fin_cases i
        · simpa using ha
        · simpa using h1
      have hcard := Nat.card_le_card_of_injective g hg_inj
      have hcount := Commons.NumberTheory.Counting.ncard_prod_max_one_abs_le 2 M hM1
      rw [h2]
      norm_num only [Nat.reduceSub, pow_one]
      calc (Nat.card {α : 𝓞 K // ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
              |Algebra.norm ℚ ((α : K))| ≤ B} : ℝ)
          ≤ (Nat.card {x : Fin 2 → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} : ℝ) := by
            exact_mod_cast hcard
        _ ≤ (100 : ℝ) ^ 2 * M * (1 + Real.log M) ^ (2 - 1) := hcount
        _ = 100 ^ 2 * (4 * B) * (1 + Real.log (4 * B / lam)) / lam := by
            rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
            rw [show M = 4 * B / lam from rfl]
            ring_nf
        _ ≤ 10000000000 * B * (1 + Real.log B) / lam := by
            apply div_le_div_of_nonneg_right _ (by linarith : (0:ℝ) ≤ lam)
            have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB
            have hlog4 : Real.log (4 * B / lam) ≤ Real.log 4 + Real.log B := by
              rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by linarith : B ≠ 0)]
              apply Real.log_le_log (by positivity)
              rw [div_le_iff₀ (by linarith : (0:ℝ) < lam)]
              nlinarith [hlam]
            have hlog4le : Real.log 4 ≤ 3 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
              linarith
            nlinarith [hlog4, hlog4le, hlogB0, hB]
    · have hEmpty : IsEmpty {α : 𝓞 K // ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
          |Algebra.norm ℚ ((α : K))| ≤ B} := not_nonempty_iff.mp hS
      haveI := hEmpty
      have hz : (Nat.card {α : 𝓞 K // ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
          |Algebra.norm ℚ ((α : K))| ≤ B} : ℝ) = 0 := by
        rw [Nat.card_eq_zero.mpr (Or.inl hEmpty)]
        norm_num
      rw [hz, h2]
      have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
      have hbase : 0 ≤ 1 + Real.log B := by linarith
      have : (0:ℝ) ≤ (100000 : ℝ) ^ 2 * B * (1 + Real.log B) ^ (2 - 1) / lam := by
        apply div_nonneg _ (by linarith)
        exact mul_nonneg (mul_nonneg (by positivity) (le_trans zero_le_one hB)) (pow_nonneg hbase _)
      simpa using this
  · -- rank ≠ 0 : infinitely many units, hence the set is infinite
    have hpos : 0 < NumberField.Units.rank K := Nat.pos_of_ne_zero hrank
    let i : Fin (NumberField.Units.rank K) := ⟨0, hpos⟩
    let u : (NumberField.RingOfIntegers K)ˣ := NumberField.Units.fundSystem K i
    have hne : ((NumberField.Units.basisUnitLattice K i :
        NumberField.Units.unitLattice K) :
        NumberField.Units.dirichletUnitTheorem.logSpace K) ≠ 0 := by
      intro h
      exact Module.Basis.ne_zero (NumberField.Units.basisUnitLattice K) i
        (Subtype.coe_injective h)
    have hu_notmem : u ∉ NumberField.Units.torsion K := by
      intro hmem
      have hlog :=
        (NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff (K := K)).mpr hmem
      rw [NumberField.Units.logEmbedding_fundSystem K i] at hlog
      exact hne hlog
    have hnotfin : ¬ IsOfFinOrder u :=
      fun h => hu_notmem ((CommGroup.mem_torsion u).mpr h)
    have horder : orderOf u = 0 := orderOf_eq_zero_iff.mpr hnotfin
    have hSinf : (Set.Infinite {α : NumberField.RingOfIntegers K |
        ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
          |Algebra.norm ℚ ((α : K))| ≤ B}) := by
      refine Set.infinite_of_injective_forall_mem
        (f := fun n : ℕ => ((u ^ (n + 1) : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K)) ?_ ?_
      · intro n m h
        have h' : u ^ (n + 1) = u ^ (m + 1) := Units.val_injective h
        have := (pow_inj_iff_of_orderOf_eq_zero horder).mp h'
        omega
      · intro n
        refine ⟨?_, ?_⟩
        · exact units_coe_notMem_range (u ^ (n + 1)) (by
            intro hfin
            apply hnotfin
            obtain ⟨k, hk, hk1⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
            exact isOfFinOrder_iff_pow_eq_one.mpr ⟨(n+1)*k, Nat.mul_pos (by omega) hk, by
              rw [pow_mul, hk1]⟩)
        · have hnorm1 : ((|Algebra.norm ℚ
              ((u ^ (n + 1) : (NumberField.RingOfIntegers K)ˣ) : K)| : ℚ) : ℝ) = 1 := by
            rw [NumberField.Units.norm (K := K) (u ^ (n+1))]
            norm_num
          rw [NumberField.Units.coe_coe, hnorm1]
          exact hB
    haveI : Infinite {α : NumberField.RingOfIntegers K //
        ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
          |Algebra.norm ℚ ((α : K))| ≤ B} := hSinf.to_subtype
    rw [Nat.card_eq_zero_of_infinite]
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
    have hbase : 0 ≤ 1 + Real.log B := by linarith
    have : (0:ℝ) ≤ (100000 : ℝ) ^ Module.finrank ℚ K * B *
        (1 + Real.log B) ^ (Module.finrank ℚ K - 1) / lam := by
      apply div_nonneg _ (by linarith)
      exact mul_nonneg (mul_nonneg (by positivity) (le_trans zero_le_one hB))
        (pow_nonneg hbase _)
    simpa using this

end Commons.NumberTheory.NumberField
