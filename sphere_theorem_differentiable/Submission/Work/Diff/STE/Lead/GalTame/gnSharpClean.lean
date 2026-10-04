import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GN.tools
import Submission.Work.Diff.STE.GN.discrete_convex
import Submission.Work.Diff.STE.GN.gnLevStepGenClean
import Submission.Work.Diff.STE.GN.gnLevStepOneClean
import Submission.Work.Diff.STE.Lead.GalTame.ibpComplexSharp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp Gagliardo–Nirenberg inequality on the torus (clean)

`gnSharp` is the sharp-exponent Gagliardo–Nirenberg inequality on the unit torus,

  `∫_{cube} ‖∂^β f‖^{2m/j} ≤ C · U^{2m/j-2} · ENormSq m f`  for `‖f‖_∞ ≤ U`, `1 ≤ j ≤ m`,

proved by Nirenberg's discrete log-convexity argument.  It is the clean counterpart of
`Work.Diff.STE.GN_torus`, whose proof cites the two still-`sorry`ed Nirenberg steps
`Work.Diff.STE.GN.gnLev_step_one`/`gnLev_step_gen` (hence `sorryAx`); here those two steps are
replaced by their proved copies `gnStepOneClean`/`gnStepGenClean`, and the integration-by-parts
input is the clean `ibpComplexSharp`.
-/

noncomputable section

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory BigOperators
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! TEMPORARY STUBS for the two Nirenberg steps, which are being proved in parallel as
`Work.Diff.STE.Lead.GalTame.gnStepOneClean` / `gnStepGenClean`; they will be replaced by imports
of those modules once they land. -/
/-- The integration-by-parts input at the exponent `gnP m 1 = 2m`. -/
private lemma ibp_one (m : ℕ) (hm : 2 ≤ m) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f) (i : ι) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1
      ≤ (Work.Diff.STE.gnP m 1 - 1) * ∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖f x‖ * ‖Work.Diff.STE.pd i f x‖ ^ (Work.Diff.STE.gnP m 1 - 2)
            * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i f) x‖ :=
  ibpComplexSharp i (Work.Diff.STE.gnP m 1)
    (Work.Diff.STE.gnP_two_le (m := m) (k := 1) le_rfl (by omega)) f hf hper

/-- The Nirenberg recursion for the level sequence `gnSeq`, with the clean steps. -/
private lemma gnSeq_step_clean (m : ℕ) (hm : 2 ≤ m) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f) (U : ℝ) (hU0 : 0 ≤ U)
    (hU : ∀ x : ι → ℝ, ‖f x‖ ≤ U) {k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m) :
    (Work.Diff.STE.gnSeq m U f k) ^ 2
      ≤ Work.Diff.STE.gnC (ι := ι) m k * Work.Diff.STE.gnSeq m U f (k - 1)
        * Work.Diff.STE.gnSeq m U f (k + 1) := by
  rcases eq_or_lt_of_le hk with h1 | h2
  · subst h1
    have h := Work.Diff.STE.GN.gnLevStepOneClean (ι := ι) m hm f hf hper U hU0 hU (fun i => ibp_one m hm f hf hper i)
    rw [Work.Diff.STE.gnSeq_of_pos m U f (le_refl 1), Work.Diff.STE.gnSeq_zero,
      Work.Diff.STE.gnSeq_of_pos m U f (by norm_num : 1 ≤ 2)]
    simpa using h
  · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    subst hk'
    have hk1 : 1 ≤ k' := by omega
    have hkm' : k' + 2 ≤ m := by omega
    have h := Work.Diff.STE.GN.gnLevStepGenClean (ι := ι) m hm f hf hper k' hk1 hkm'
      (fun g i hg hgp => ibpComplexSharp i (Work.Diff.STE.gnP m (k' + 1))
        (Work.Diff.STE.gnP_two_le (m := m) (k := k' + 1) (by omega) (by omega)) g hg hgp)
    rw [show k' + 1 - 1 = k' from by omega, show k' + 1 + 1 = k' + 2 from by omega]
    rw [Work.Diff.STE.gnSeq_of_pos m U f (by omega : 1 ≤ k' + 1),
      Work.Diff.STE.gnSeq_of_pos m U f hk1,
      Work.Diff.STE.gnSeq_of_pos m U f (by omega : 1 ≤ k' + 2)]
    exact h

/-- **The sharp Gagliardo–Nirenberg inequality on the unit torus.**  For a smooth `1`-periodic
`f : (ι → ℝ) → ℂ` with `‖f‖_∞ ≤ U`, every `j`-th order partial derivative (`1 ≤ j ≤ m`) satisfies
`∫_{cube} ‖∂^β f‖^{2m/j} ≤ C · U^{2m/j - 2} · ENormSq m f`. -/
theorem gnSharp (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : ℝ) (f : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) f → Work.Diff.STE.Periodic1 f → (∀ x : ι → ℝ, ‖f x‖ ≤ U) →
      ∀ (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) (β : Fin j → ι),
        ∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖Work.Diff.STE.pdVec j β f x‖ ^ ((2 * (m : ℝ)) / (j : ℝ))
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
      have hsingle : ∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec 1 β f x‖ ^ ((2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ))
          ≤ Work.Diff.STE.ENormSq 1 f := by
        have hcongr : (∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec 1 β f x‖ ^ ((2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ)))
            = ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec 1 β f x‖ ^ (2 : ℕ) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [show (2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ) = 2 by norm_num]
          exact Real.rpow_natCast _ _
        rw [hcongr, Work.Diff.STE.ENormSq]
        have hnn : ∀ l : Fin 1 → ι,
            0 ≤ ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec 1 l f x‖ ^ (2 : ℕ) :=
          fun l => integral_nonneg fun x => by positivity
        exact Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ β)
      refine le_trans hsingle ?_
      rw [show (2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ) - 2 = 0 by norm_num, Real.rpow_zero]
      exact le_of_eq (by ring)
  · obtain ⟨K, hK0, hK⟩ :=
      Work.Diff.STE.GN.discrete_convex m (Work.Diff.STE.gnC (ι := ι) m)
        (Work.Diff.STE.gnC_nonneg (ι := ι) m)
    refine ⟨(max K 1) ^ (2 * (m : ℝ)), Real.rpow_nonneg (by linarith [le_max_right K 1]) _, ?_⟩
    intro U f hf hper hU j hj hjm β
    by_cases hUneg : U < 0
    · exfalso
      have h3 : ‖f 0‖ ≤ U := hU 0
      have h4 : (0 : ℝ) ≤ ‖f 0‖ := norm_nonneg _
      linarith
    have hU0 : 0 ≤ U := le_of_not_gt hUneg
    have hstep : ∀ k, 1 ≤ k → k + 1 ≤ m →
        (Work.Diff.STE.gnSeq m U f k) ^ 2
          ≤ Work.Diff.STE.gnC (ι := ι) m k * Work.Diff.STE.gnSeq m U f (k - 1)
            * Work.Diff.STE.gnSeq m U f (k + 1) :=
      fun k hk hkm => gnSeq_step_clean (ι := ι) m hm2 f hf hper U hU0 hU hk hkm
    have hmain := hK (Work.Diff.STE.gnSeq m U f) (Work.Diff.STE.gnSeq_nonneg m hU0 f) hstep j hjm
    rw [Work.Diff.STE.gnSeq_zero, Work.Diff.STE.gnSeq_of_pos m U f hj,
      Work.Diff.STE.gnSeq_of_pos m U f (by omega : 1 ≤ m)] at hmain
    have hL2 : (Work.Diff.STE.gnLev m f m) ^ (2 : ℝ) = Work.Diff.STE.ENormSq m f := by
      rw [← Work.Diff.STE.gnP_self m (by omega : 1 ≤ m)]
      rw [Work.Diff.STE.gnLev_rpow m f (by omega : 1 ≤ m) (le_refl m)]
      rw [Work.Diff.STE.gnP_self m (by omega : 1 ≤ m)]
      rw [Work.Diff.STE.ENormSq]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine integral_congr_ae ?_
      filter_upwards with x
      exact Real.rpow_natCast _ _
    set q : ℝ := (2 * (m : ℝ)) / (j : ℝ) with hq
    have hqeq : q = Work.Diff.STE.gnP m j := by rw [hq, Work.Diff.STE.gnP]
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
    have hsingle : ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec j β f x‖ ^ q
        ≤ (Work.Diff.STE.gnLev m f j) ^ q := by
      rw [hqeq, Work.Diff.STE.gnLev_rpow m f hj hjm]
      have hnn : ∀ l : Fin j → ι,
          0 ≤ ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec j l f x‖ ^ (Work.Diff.STE.gnP m j) :=
        fun l => integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
      exact Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ β)
    have hstep2 : (Work.Diff.STE.gnLev m f j) ^ q ≤
        (K * U ^ (1 - (j : ℝ) / m) * (Work.Diff.STE.gnLev m f m) ^ ((j : ℝ) / m)) ^ q :=
      Real.rpow_le_rpow (Work.Diff.STE.gnLev_nonneg m f j) hmain hq0
    have hexp : (K * U ^ (1 - (j : ℝ) / m) * (Work.Diff.STE.gnLev m f m) ^ ((j : ℝ) / m)) ^ q
        = K ^ q * U ^ (q - 2) * Work.Diff.STE.ENormSq m f := by
      rw [show K * U ^ (1 - (j : ℝ) / m) * (Work.Diff.STE.gnLev m f m) ^ ((j : ℝ) / m)
            = (K * U ^ (1 - (j : ℝ) / m)) * (Work.Diff.STE.gnLev m f m) ^ ((j : ℝ) / m)
              from by ring]
      rw [Real.mul_rpow (mul_nonneg hK0 (Real.rpow_nonneg hU0 _))
            (Real.rpow_nonneg (Work.Diff.STE.gnLev_nonneg m f m) _),
          Real.mul_rpow hK0 (Real.rpow_nonneg hU0 _),
          ← Real.rpow_mul hU0, ← Real.rpow_mul (Work.Diff.STE.gnLev_nonneg m f m)]
      rw [show (1 - (j : ℝ) / m) * q = q - 2 from by
            rw [hqeq]; exact (Work.Diff.STE.gnP_endpoint m j hj hjm).1,
          show ((j : ℝ) / m) * q = 2 from by
            rw [hqeq]; exact (Work.Diff.STE.gnP_endpoint m j hj hjm).2,
          hL2]
    have hKbound : K ^ q ≤ (max K 1) ^ (2 * (m : ℝ)) := by
      refine le_trans (Real.rpow_le_rpow hK0 (le_max_left K 1) hq0) ?_
      exact Real.rpow_le_rpow_of_exponent_le (le_max_right K 1) hqM
    have hENN : 0 ≤ Work.Diff.STE.ENormSq m f :=
      Finset.sum_nonneg fun l _ => integral_nonneg fun x => by positivity
    have hUU : 0 ≤ U ^ (q - 2) := Real.rpow_nonneg hU0 _
    calc ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec j β f x‖ ^ q
        ≤ (Work.Diff.STE.gnLev m f j) ^ q := hsingle
      _ ≤ (K * U ^ (1 - (j : ℝ) / m) * (Work.Diff.STE.gnLev m f m) ^ ((j : ℝ) / m)) ^ q :=
          hstep2
      _ = K ^ q * U ^ (q - 2) * Work.Diff.STE.ENormSq m f := hexp
      _ ≤ (max K 1) ^ (2 * (m : ℝ)) * U ^ (q - 2) * Work.Diff.STE.ENormSq m f := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hKbound hUU
          · exact hENN

end Work.Diff.STE.Lead.GalTame
