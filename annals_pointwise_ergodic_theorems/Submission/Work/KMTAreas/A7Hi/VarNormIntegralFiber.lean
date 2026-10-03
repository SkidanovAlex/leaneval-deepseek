import Mathlib
import Submission.Work.KMTAreas.A7.varNorm_intervalIntegral_le
import Submission.Work.KMTAreas.A7.lacDilTriVar
import Submission.Work.KMTAreas.A7.variationalNorm_mul_le

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- The `r`-variational norm is submultiplicative for the pointwise product, with constant `1`. -/
theorem variationalNorm_mul_le_one (r : NNReal) (hr : 1 ≤ r) (u v : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => u n * v n) ≤
      PointwiseErgodicTheorems.variationalNorm r u *
        PointwiseErgodicTheorems.variationalNorm r v := by
  have hvar := Work.KMTAreas.A7.varPart_mul_le hr u v
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r (fun n => u n * v n),
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r u,
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r v]
  calc (⨆ n, ‖u n * v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r (fun n => u n * v n)
      ≤ ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
          + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
              + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v) :=
        add_le_add (Work.KMTAreas.A7.iSup_enorm_mul_le u v) hvar
    _ ≤ ((⨆ n, ‖u n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r u)
          * ((⨆ n, ‖v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r v) := by
        calc ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
              + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
                  + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v)
            ≤ ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
              + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
                  + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v)
              + (Submission.PointwiseErgodicTheorems.varPart r u
                  * Submission.PointwiseErgodicTheorems.varPart r v) := le_add_right le_rfl
          _ = ((⨆ n, ‖u n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r u)
                * ((⨆ n, ‖v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r v) := by ring

/-- Minkowski plus subadditivity plus the product rule for the variational norm, in the exact shape needed by the pointwise fibre bound for the model tuple (used in `Submission/Work/KMTAreas/A7/modelTuple_variationalPointwise_exact.lean`; the `t`-Minkowski step is `Work.KMTAreas.A7.varNorm_intervalIntegral_le`, subadditivity is `Work.KMTAreas.A7.variationalNorm_finset_sum_le` in `A7/lacDilTriVar.lean`, the product rule is `Work.KMTAreas.A7.variationalNorm_mul_le`, and homogeneity is `Submission.PointwiseErgodicTheorems.variationalNorm_smul`).  Integrability of `t ↦ B t m` on `(1/2,1]` is essential (Mathlib's Bochner integral is `0` for non-integrable integrands). -/
theorem VarNormIntegralFiber (r : NNReal) (hr : 2 < r) (q : ℕ) (hq : 1 ≤ q)
    (B : ℝ → ℕ → ℂ) (A₁ A₂ : ℝ → ℤ → ℕ → ℂ)
    (hZ : ∀ m : ℕ, MeasureTheory.Integrable (fun t : ℝ => B t m)
        (MeasureTheory.volume.restrict (Set.Ioc (1/2 : ℝ) 1)))
    (hdecomp : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, ∀ m : ℕ,
        B t m = ((q : ℂ))⁻¹ * ∑ n₀ ∈ Finset.range q,
          A₁ t (n₀ : ℤ) m * A₂ t (n₀ : ℤ) m) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => ∫ t in (1/2 : ℝ)..1, B t m) ≤
      ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q,
        PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => A₁ t (n₀ : ℤ) m) *
        PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => A₂ t (n₀ : ℤ) m) := by
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hcoef : ‖((q : ℂ))⁻¹‖ₑ = (q : ENNReal)⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_natCast, ENNReal.ofReal_inv_of_pos hq0,
      ENNReal.ofReal_natCast]
  -- The Minkowski step, moving the integral inside the variational norm.
  have hmain := Work.KMTAreas.A7.varNorm_intervalIntegral_le r hr1 B hZ
  refine hmain.trans ?_
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  -- The pointwise fibre bound, from the decomposition of `B`, homogeneity, subadditivity and
  -- the product rule.
  have hfun : (fun m : ℕ => B t m)
      = ((q : ℂ))⁻¹ • (fun m : ℕ => ∑ n₀ ∈ Finset.range q,
          A₁ t (n₀ : ℤ) m * A₂ t (n₀ : ℤ) m) := by
    funext m
    rw [Pi.smul_apply, smul_eq_mul]
    exact hdecomp t ht m
  have hsum := Work.KMTAreas.A7.variationalNorm_finset_sum_le hr1 (Finset.range q)
    (fun n₀ m => A₁ t (n₀ : ℤ) m * A₂ t (n₀ : ℤ) m)
  have hmul : ∀ n₀ ∈ Finset.range q, PointwiseErgodicTheorems.variationalNorm r
      (fun m : ℕ => A₁ t (n₀ : ℤ) m * A₂ t (n₀ : ℤ) m) ≤
      PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => A₁ t (n₀ : ℤ) m) *
      PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => A₂ t (n₀ : ℤ) m) :=
    fun n₀ _ => variationalNorm_mul_le_one r hr1 _ _
  calc PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => B t m)
      = ‖((q : ℂ))⁻¹‖ₑ * PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => ∑ n₀ ∈ Finset.range q,
            A₁ t (n₀ : ℤ) m * A₂ t (n₀ : ℤ) m) := by
        rw [hfun, Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := r) hr1]
    _ ≤ ‖((q : ℂ))⁻¹‖ₑ * ∑ n₀ ∈ Finset.range q,
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => A₁ t (n₀ : ℤ) m * A₂ t (n₀ : ℤ) m) :=
        mul_le_mul_right hsum _
    _ ≤ ‖((q : ℂ))⁻¹‖ₑ * ∑ n₀ ∈ Finset.range q,
          PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => A₁ t (n₀ : ℤ) m) *
          PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => A₂ t (n₀ : ℤ) m) :=
        mul_le_mul_right (Finset.sum_le_sum hmul) _
    _ = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q,
          PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => A₁ t (n₀ : ℤ) m) *
          PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => A₂ t (n₀ : ℤ) m) := by
        rw [hcoef]

end Work.KMTAreas.A7Hi
