import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Comp.young_conv_lp
import Submission.Work.Diff.STE.seriesFun_mul
import Submission.Work.Diff.STE.B3.parseval_cube
import Submission.Work.Diff.STE.fourierCoeff_mul_seriesFun
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.GN.tools
import Submission.Work.Diff.STE.GN.discrete_convex
import Submission.Work.Diff.STE.GN.ibpRpowComplexClean
import Submission.Work.Diff.STE.GN.gnLevStepGenClean
import Submission.Work.Diff.STE.GN.gnLevStepOneClean

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Gagliardo–Nirenberg on the unit torus

The proof is Nirenberg's discrete log-convexity argument, in the form set up in
`Submission.Work.Diff.STE.GN.tools`: with the levels
`gnLev m f k = (∑_{l : Fin k → ι} ∫_{cube} ‖∂^l f‖ ^ (2m/k)) ^ (k/(2m))`, integration by parts
(`ibp_rpow_complex`) plus Hölder give `(P k)^2 ≤ C k (P (k-1)) (P (k+1))` for `1 ≤ k ≤ m-1`, and
`Work.Diff.STE.GN.discrete_convex` converts this into `P j ≤ K U ^ (1 - j/m) (P m) ^ (j/m)`,
which is the claim since `(P m)^2 = ENormSq m f` and `P j ^ (2m/j)` is (an upper bound for) the
left-hand side. -/

/-- The Nirenberg recursion for the level sequence `gnSeq`. -/
lemma gnSeq_step (m : ℕ) (hm : 2 ≤ m) (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : Periodic1 f) (U : ℝ) (hU0 : 0 ≤ U) (hU : ∀ x : ι → ℝ, ‖f x‖ ≤ U)
    {k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m) :
    (gnSeq m U f k) ^ 2 ≤ gnC (ι := ι) m k * gnSeq m U f (k - 1) * gnSeq m U f (k + 1) := by
  rcases eq_or_lt_of_le hk with h1 | h2
  · subst h1
    have h := Work.Diff.STE.GN.gnLevStepOneClean (ι := ι) m hm f hf hper U hU0 hU
      (fun i => Work.Diff.STE.GN.ibpRpowComplexClean i (gnP m 1)
        (gnP_two_le (by omega) (by omega)) f hf hper)
    rw [gnSeq_of_pos m U f (le_refl 1), gnSeq_zero, gnSeq_of_pos m U f (by norm_num : 1 ≤ 2)]
    simpa using h
  · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    subst hk'
    have hk1 : 1 ≤ k' := by omega
    have hkm' : k' + 2 ≤ m := by omega
    have h := Work.Diff.STE.GN.gnLevStepGenClean (ι := ι) m hm f hf hper k' hk1 hkm'
      (fun g i hg hgp => Work.Diff.STE.GN.ibpRpowComplexClean i (gnP m (k' + 1))
        (gnP_two_le (by omega) (by omega)) g hg hgp)
    rw [show k' + 1 - 1 = k' from by omega, show k' + 1 + 1 = k' + 2 from by omega]
    rw [gnSeq_of_pos m U f (by omega : 1 ≤ k' + 1), gnSeq_of_pos m U f hk1,
      gnSeq_of_pos m U f (by omega : 1 ≤ k' + 2)]
    exact h

lemma ENormSq_nonneg' (m : ℕ) (f : (ι → ℝ) → ℂ) : 0 ≤ ENormSq m f :=
  Finset.sum_nonneg fun l _ =>
    integral_nonneg fun x => pow_nonneg (norm_nonneg _) 2

/-- **Gagliardo–Nirenberg interpolation on the unit torus** (sharp exponents).  For a smooth
`1`-periodic `f` with `‖f‖_∞ ≤ U`, every `j`-th order partial derivative (`1 ≤ j ≤ m`) satisfies
`∫_{cube} ‖∂^β f‖^{2m/j} ≤ C · U^{2m/j - 2} · ENormSq m f`.

PROOF ROUTE (all ingredients are elementary; complex interpolation is *not* needed):
1. *Hausdorff–Young for the torus*: for `p ≥ 2`, `(∫ ‖f‖^p)^{1/p} ≤ C (Σ_k ‖fourierCoeff f k‖^{p'})^{1/p'}`
   with `p' = p/(p-1)`.  For *even* `p = 2k` this follows by expanding `∫ ‖f‖^{2k} = ∫ f^k · conj(f^k)`,
   identifying `fourierCoeff (f^k) = iConv k (fun _ => fourierCoeff f)`
   (`Work.Diff.STE.seriesFun_mul`, `Work.Diff.STE.fourierCoeff_mul_seriesFun`,
   `Work.Diff.STE.integral_seriesFun_mul_conj` / `parseval_cube`) and applying Young's convolution
   inequality with all exponents `p'` (`Work.Diff.STE.Comp.young_conv_lp`, giving the constant `1`).
   For general `p`, interpolate between the even exponents `p₁ = 2⌊p/2⌋` and `p₂ = p₁ + 2` using
   Hölder's inequality for the integrals on the cube and Lyapunov's inequality for the `ℓ^p` norms
   (the interpolation exponents agree since `1/p' = 1 - 1/p`).
2. Apply Hausdorff–Young to `∂^β f`.  Writing `ĉ_k = fourierCoeff f k` (so `|ĉ_k| ≤ U` and
   `Σ_k ‖ĉ_k‖^2 ≤ U^2` because the volume of the cube is `1`), and `a := |β| p'/(2m) ∈ (0,1]`,
   `Σ_k ‖k^β ĉ_k‖^{p'} ≤ Σ_k ‖k‖^{|β| p'} ‖ĉ_k‖^{p'} = Σ_k (‖k‖^{2m}‖ĉ_k‖^2)^a ‖ĉ_k‖^{p'-2a}`
   `≤ (Σ_k ‖k‖^{2m}‖ĉ_k‖²)^a · (Σ_k ‖ĉ_k‖^{s})^{1-a}` with `s := (p'-2a)/(1-a) ≥ 2`
   (Hölder with exponents `1/a`, `1/(1-a)`), and `Σ_k ‖ĉ_k‖^s ≤ U^{s-2} Σ_k ‖ĉ_k‖² ≤ U^s`.
   Finally `Σ_k ‖k‖^{2m}‖ĉ_k‖² ≤ (2π)^{-2m} · Σ_k (Σ_i k_i²)^m ‖ĉ_k‖² = (2π)^{-2m} ENormSq m f`
   (multinomial identity: `Σ_{l : Fin m → ι} ∏_i k_{l i}² = (Σ_i k_i²)^m`). -/
theorem GN_torus {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : ℝ) (f : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) f → Work.Diff.STE.Periodic1 f → (∀ x : ι → ℝ, ‖f x‖ ≤ U) →
      ∀ (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) (β : Fin j → ι),
        ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j β f x‖ ^ ((2 * (m : ℝ)) / (j : ℝ))
          ≤ C * U ^ ((2 * (m : ℝ)) / (j : ℝ) - 2) * Work.Diff.STE.ENormSq m f := by
  classical
  rcases Nat.lt_or_ge m 2 with hm01 | hm2
  · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      refine ⟨0, le_refl 0, ?_⟩
      intro U f hf hper hU j hj hjm β
      exfalso
      omega
    · have hm1 : m = 1 := by omega
      subst hm1
      refine ⟨1, zero_le_one, ?_⟩
      intro U f hf hper hU j hj hjm β
      have hj1 : j = 1 := by omega
      subst hj1
      have hsingle : ∫ x in unitCube, ‖pdVec 1 β f x‖ ^ ((2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ))
          ≤ ENormSq 1 f := by
        have hcongr : (∫ x in unitCube, ‖pdVec 1 β f x‖ ^ ((2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ)))
            = ∫ x in unitCube, ‖pdVec 1 β f x‖ ^ (2 : ℕ) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [show (2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ) = 2 by norm_num]
          exact Real.rpow_natCast _ _
        rw [hcongr, ENormSq]
        have hnn : ∀ l : Fin 1 → ι, 0 ≤ ∫ x in unitCube, ‖pdVec 1 l f x‖ ^ (2 : ℕ) :=
          fun l => integral_nonneg fun x => by positivity
        exact Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ β)
      refine le_trans hsingle ?_
      rw [show (2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ) - 2 = 0 by norm_num, Real.rpow_zero]
      exact le_of_eq (by ring)
  · obtain ⟨K, hK0, hK⟩ :=
      Work.Diff.STE.GN.discrete_convex m (gnC (ι := ι) m) (gnC_nonneg (ι := ι) m)
    refine ⟨(max K 1) ^ (2 * (m : ℝ)), Real.rpow_nonneg (by linarith [le_max_right K 1]) _, ?_⟩
    intro U f hf hper hU j hj hjm β
    by_cases hUneg : U < 0
    · exfalso
      have h3 : ‖f 0‖ ≤ U := hU 0
      have h4 : (0 : ℝ) ≤ ‖f 0‖ := norm_nonneg _
      linarith
    have hU0 : 0 ≤ U := le_of_not_gt hUneg
    have hstep : ∀ k, 1 ≤ k → k + 1 ≤ m →
        (gnSeq m U f k) ^ 2 ≤ gnC (ι := ι) m k * gnSeq m U f (k - 1) * gnSeq m U f (k + 1) :=
      fun k hk hkm => gnSeq_step (ι := ι) m hm2 f hf hper U hU0 hU hk hkm
    have hmain := hK (gnSeq m U f) (gnSeq_nonneg m hU0 f) hstep j hjm
    rw [gnSeq_zero, gnSeq_of_pos m U f hj, gnSeq_of_pos m U f (by omega : 1 ≤ m)] at hmain
    have hL2 : (gnLev m f m) ^ (2 : ℝ) = ENormSq m f := by
      rw [← gnP_self m (by omega : 1 ≤ m)]
      rw [gnLev_rpow m f (by omega : 1 ≤ m) (le_refl m)]
      rw [gnP_self m (by omega : 1 ≤ m)]
      rw [ENormSq]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine integral_congr_ae ?_
      filter_upwards with x
      exact Real.rpow_natCast _ _
    set q : ℝ := (2 * (m : ℝ)) / (j : ℝ) with hq
    have hqeq : q = gnP m j := by rw [hq, gnP]
    have hq0 : 0 ≤ q := by
      rw [hq]
      have hj0 : (0 : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j)
      exact div_nonneg (by positivity) (le_of_lt hj0)
    have hqM : q ≤ 2 * (m : ℝ) := by
      rw [hq]
      have hj0 : (0 : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j)
      rw [div_le_iff₀ hj0]
      have hj1 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj
      nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
    have hsingle : ∫ x in unitCube, ‖pdVec j β f x‖ ^ q ≤ (gnLev m f j) ^ q := by
      rw [hqeq, gnLev_rpow m f hj hjm]
      have hnn : ∀ l : Fin j → ι, 0 ≤ ∫ x in unitCube, ‖pdVec j l f x‖ ^ (gnP m j) :=
        fun l => integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
      exact Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ β)
    have hstep2 : (gnLev m f j) ^ q ≤
        (K * U ^ (1 - (j : ℝ) / m) * (gnLev m f m) ^ ((j : ℝ) / m)) ^ q :=
      Real.rpow_le_rpow (gnLev_nonneg m f j) hmain hq0
    have hexp : (K * U ^ (1 - (j : ℝ) / m) * (gnLev m f m) ^ ((j : ℝ) / m)) ^ q
        = K ^ q * U ^ (q - 2) * ENormSq m f := by
      rw [show K * U ^ (1 - (j : ℝ) / m) * (gnLev m f m) ^ ((j : ℝ) / m)
            = (K * U ^ (1 - (j : ℝ) / m)) * (gnLev m f m) ^ ((j : ℝ) / m) from by ring]
      rw [Real.mul_rpow (mul_nonneg hK0 (Real.rpow_nonneg hU0 _))
            (Real.rpow_nonneg (gnLev_nonneg m f m) _),
          Real.mul_rpow hK0 (Real.rpow_nonneg hU0 _),
          ← Real.rpow_mul hU0, ← Real.rpow_mul (gnLev_nonneg m f m)]
      rw [show (1 - (j : ℝ) / m) * q = q - 2 from by
            rw [hqeq]; exact (gnP_endpoint m j hj hjm).1,
          show ((j : ℝ) / m) * q = 2 from by
            rw [hqeq]; exact (gnP_endpoint m j hj hjm).2,
          hL2]
    have hKbound : K ^ q ≤ (max K 1) ^ (2 * (m : ℝ)) := by
      refine le_trans (Real.rpow_le_rpow hK0 (le_max_left K 1) hq0) ?_
      exact Real.rpow_le_rpow_of_exponent_le (le_max_right K 1) hqM
    have hENN : 0 ≤ ENormSq m f := ENormSq_nonneg' m f
    have hUU : 0 ≤ U ^ (q - 2) := Real.rpow_nonneg hU0 _
    calc ∫ x in unitCube, ‖pdVec j β f x‖ ^ q
        ≤ (gnLev m f j) ^ q := hsingle
      _ ≤ (K * U ^ (1 - (j : ℝ) / m) * (gnLev m f m) ^ ((j : ℝ) / m)) ^ q := hstep2
      _ = K ^ q * U ^ (q - 2) * ENormSq m f := hexp
      _ ≤ (max K 1) ^ (2 * (m : ℝ)) * U ^ (q - 2) * ENormSq m f := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hKbound hUU
          · exact hENN

end Work.Diff.STE
