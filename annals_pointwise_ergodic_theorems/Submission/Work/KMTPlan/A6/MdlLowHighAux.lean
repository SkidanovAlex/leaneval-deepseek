/-
# Auxiliary (UNVERIFIED) lemmas for the low-high case of the §6 integration-by-parts identity

These are the elementary bounds that the assembly of `Work.KMTPlan.A6.MdlDecayLowHigh` needs
(boundedness of the model inputs, `ℓ¹`-summability of the window kernels, bounds on the weights
`W₁`, `W₂`, and the normal-form rewriting of `Btwist`).  They have NOT yet been built (moved here
out of `MdlDecayLowHigh.lean` so that the target file stays buildable); the next session should
verify them one by one and then inline them into the target file.

The mathematical route is that of the sibling `MdlDecayHighLow` (identity (i)): the model tuple is
written in the normal form `mdlNF` of `Work.KMTPlan.A6.MdlDecayDefs` (`Btwist_Tle_eq_mdlNF`, from
the §6 functional calculus `Work.A7.ModelApproxCore_kernelComp`), the `t`-integral is exchanged
with the series (`Work.KMTPlan.A6.MdlNFIntegral`), and the resulting *coefficient* identity
`MdlKerIdentLowHigh` -- the `cw`-level identity `MdlCwIntegIdent` multiplied by the `t`-independent
arithmetic characters (`mdlIWKer_eq_cw`) -- is applied pointwise in the convolution index `z`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlCwIntegIdent
import Submission.Work.KMTPlan.A6.MdlNFIntegral
import Submission.Work.KMTPlan.A6.MdlKerVarphiNt
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNt
import Submission.Work.KMTPlan.A6.MdlKerLowHigh
import Submission.Work.A7.ModelApproxCore_Fpiece_convOp
import Submission.Work.A7.ModelApproxCore_kernelComp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7
open Work.Analysis.EndVar
open Work.Analysis.IonescuWainger

/-! ## Elementary bounds on the inputs -/

/-- `‖z‖ ≤ 1` from `Complex.normSq z ≤ 1`. -/
theorem mdl_normSq_le_one {z : ℂ} (h : Complex.normSq z ≤ 1) : ‖z‖ ≤ 1 := by
  have h2 : ‖z‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h
  nlinarith [norm_nonneg z]

/-- The kernel `exactKer` of the exact-height projection is in `ℓ¹(ℤ)`. -/
theorem mdl_summable_exactKer_norm (ρ : ℝ) (l : ℕ) (k : ℤ) :
    Summable (fun j : ℤ => ‖Work.KMTAreas.A7.exactKer ρ l k j‖) := by
  rcases eq_or_ne l 0 with hl | hl
  · subst hl
    rw [Work.A7.exactKer_zero]
    exact Work.KMTAreas.A5.summable_kmtKern_norm ρ 0 k
  · have hfun : (fun j : ℤ => ‖Work.KMTAreas.A7.exactKer ρ l k j‖)
        = fun j : ℤ => ‖Work.KMTAreas.A5.kmtKern ρ l k j
            - Work.KMTAreas.A5.kmtKern ρ (l - 1) k j‖ := by
      funext j
      rw [Work.A7.exactKer_of_ne ρ hl, Pi.sub_apply]
    rw [hfun]
    exact Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => norm_sub_le _ _)
      ((Work.KMTAreas.A5.summable_kmtKern_norm ρ l k).add
        (Work.KMTAreas.A5.summable_kmtKern_norm ρ (l - 1) k))

/-- The exact-height projection of a bounded sequence is bounded. -/
theorem mdl_mdlF_bounded (ρ : ℝ) (u l : ℕ) {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, Complex.normSq (f x) ≤ 1) : ∃ C : ℝ, ∀ y : ℤ, ‖mdlF ρ u l f y‖ ≤ C := by
  have hf1 : ∀ x : ℤ, ‖f x‖ ≤ 1 := fun x => mdl_normSq_le_one (hf x)
  refine ⟨(∑' j : ℤ, ‖Work.KMTAreas.A7.exactKer ρ l (-(u : ℤ)) j‖) * max 1 0, fun y => ?_⟩
  have hb : Work.KMTAreas.A5.BoundedZ f := ⟨1, hf1⟩
  rw [mdlF, Work.A7.piExact_eq_convOp ρ l (-(u : ℤ)) hb]
  exact Work.A7.ModelApproxCore_aux.norm_convOp_le (mdl_summable_exactKer_norm ρ l _) hf1 y

/-- The exact-height projection of a bounded sequence is bounded (the `g`-side twist). -/
theorem mdl_mdlG_bounded (ρ : ℝ) (P : Polynomial ℤ) (u l : ℕ) {g : ℤ → ℂ}
    (hg : ∀ x : ℤ, Complex.normSq (g x) ≤ 1) : ∃ C : ℝ, ∀ y : ℤ, ‖mdlG ρ P u l g y‖ ≤ C := by
  have hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1 := fun x => mdl_normSq_le_one (hg x)
  refine ⟨(∑' j : ℤ, ‖Work.KMTAreas.A7.exactKer ρ l (-((P.natDegree : ℤ) * (u : ℤ))) j‖) * max 1 0,
    fun y => ?_⟩
  have hb : Work.KMTAreas.A5.BoundedZ g := ⟨1, hg1⟩
  rw [mdlG, Work.A7.piExact_eq_convOp ρ l (-((P.natDegree : ℤ) * (u : ℤ))) hb]
  exact Work.A7.ModelApproxCore_aux.norm_convOp_le (mdl_summable_exactKer_norm ρ l _) hg1 y

/-- The arithmetic symbol `m_Ẑ` is an average of `q` complex numbers of modulus one. -/
private lemma mdl_mZ_norm_le_one (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range q,
      fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
    calc ‖∑ n ∈ Finset.range q,
          fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        ≤ ∑ n ∈ Finset.range q,
            ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe, mul_one]
      _ = (q : ℝ) := by simp
  calc ((q : ℝ))⁻¹ * ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
      ≤ ((q : ℝ))⁻¹ * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = 1 := by rw [inv_mul_cancel₀ (by exact_mod_cast hq.ne')]

/-- The arithmetic kernel of `Btwist` is bounded by the product of the cardinalities. -/
theorem mdl_arithKernel_norm_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖
      ≤ ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) := by
  unfold arithKernel
  calc ‖∑ α₁ ∈ iwArithFreqs ρ l₁, ∑ α₂ ∈ iwArithFreqs ρ l₂,
        mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
          * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ iwArithFreqs ρ l₁, ‖∑ α₂ ∈ iwArithFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ := norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ iwArithFreqs ρ l₁, ∑ α₂ ∈ iwArithFreqs ρ l₂,
          ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ iwArithFreqs ρ l₁, ∑ _α₂ ∈ iwArithFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact mdl_mZ_norm_le_one P (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ _) α₁ α₂
    _ = ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The kernel of `Btwist` is in `ℓ¹(ℤ²)` as soon as the two symbols have summable `cw`. -/
theorem mdl_summable_mdlBtwK_general (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h₁ : Summable fun j : ℤ => ‖cw m₁ j‖) (h₂ : Summable fun j : ℤ => ‖cw m₂ j‖) :
    Summable fun p : ℤ × ℤ => ‖mdlBtwK ρ P l₁ l₂ m₁ m₂ p.1 p.2‖ := by
  have hbound : ∀ p : ℤ × ℤ,
      ‖mdlBtwK ρ P l₁ l₂ m₁ m₂ p.1 p.2‖
        ≤ ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)
            * ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ := by
    intro p
    rw [mdlBtwK, twKer, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (mdl_arithKernel_norm_le ρ P l₁ l₂ p.1 p.2) le_rfl
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) le_rfl
      (norm_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (norm_nonneg _))
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound ?_
  exact ((Summable.mul_of_nonneg h₁ h₂ (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)).mul_left
    (((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ))).congr
    (fun p => by ring)

/-- The `cw`-coefficients of the window `mStarF u = etaCut kmtEta (-(2u))` are summable. -/
theorem mdl_summable_cw_mStarF (u : ℕ) : Summable fun j : ℤ => ‖cw (mStarF u) j‖ := by
  obtain ⟨C, _hCpos, hC⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [mStarF] using hC j

/-- The `cw`-coefficients of `mStargF d u = etaCut kmtEta (-(2du))` are summable. -/
theorem mdl_summable_cw_mStargF (d u : ℕ) : Summable fun j : ℤ => ‖cw (mStargF d u) j‖ := by
  obtain ⟨C, _hCpos, hC⟩ := cw_etaCut_decay (-((d : ℤ) * 2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [mStargF] using hC j

/-- The concrete instance of the previous lemma for the window `m_* = mStarF u ⊗ mStargF d u`. -/
theorem mdl_summable_mdlBtwK_mStarF (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) :
    Summable fun p : ℤ × ℤ => ‖mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      p.1 p.2‖ :=
  mdl_summable_mdlBtwK_general ρ P l₁ l₂ _ _
    (mdl_summable_cw_mStarF u) (mdl_summable_cw_mStargF P.natDegree u)

/-! ## Bounds on the two weights `W₁ = N^{d-1}/P'(Nt)`, `W₂ = N^dP''(Nt)/P'(Nt)²` -/

/-- `W₁` is bounded on `[1/2,1]` when `P'` does not vanish there. -/
theorem mdl_W1_bound (P : Polynomial ℤ) (N : ℕ)
    (hP : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, PderivR P ((N : ℝ) * t) ≠ 0) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ‖mdlW1 P N t‖ ≤ Cw := by
  have hcont : ContinuousOn (fun t : ℝ => mdlW1 P N t) (Set.Icc (1/2 : ℝ) 1) := by
    unfold mdlW1
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact continuousOn_const.div (continuous_PderivR_comp P (N : ℝ)).continuousOn
      (fun t ht => hP t ht)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1/2 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont
  exact ⟨max C 0, le_max_right _ _, fun t ht => le_trans (hC t ht) (le_max_left _ _)⟩

/-- `W₂` is bounded on `[1/2,1]` when `P'` does not vanish there. -/
theorem mdl_W2_bound (P : Polynomial ℤ) (N : ℕ)
    (hP : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, PderivR P ((N : ℝ) * t) ≠ 0) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ‖mdlW2 P N t‖ ≤ Cw := by
  have hcont : ContinuousOn (fun t : ℝ => mdlW2 P N t) (Set.Icc (1/2 : ℝ) 1) := by
    have h1 : ContinuousOn (fun t : ℝ => Pderiv2R P ((N : ℝ) * t)) (Set.Icc (1/2 : ℝ) 1) := by
      simpa only [Pderiv2R, PderivR] using
        (continuous_PderivR_comp P.derivative (N : ℝ)).continuousOn
    have h2 : ContinuousOn (fun t : ℝ => (PderivR P ((N : ℝ) * t)) ^ 2) (Set.Icc (1/2 : ℝ) 1) :=
      (continuous_PderivR_comp P (N : ℝ)).continuousOn.pow 2
    have h3 : ContinuousOn (fun t : ℝ => ((N : ℝ) ^ P.natDegree * Pderiv2R P ((N : ℝ) * t))
        / (PderivR P ((N : ℝ) * t)) ^ 2) (Set.Icc (1/2 : ℝ) 1) :=
      (continuousOn_const.mul h1).div h2 (fun t ht => pow_ne_zero 2 (hP t ht))
    unfold mdlW2
    exact Complex.continuous_ofReal.comp_continuousOn h3
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1/2 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont
  exact ⟨max C 0, le_max_right _ _, fun t ht => le_trans (hC t ht) (le_max_left _ _)⟩

/-! ## Measurability of the two weights (unconditional) -/

/-- `mdlW1 P N` is measurable in `t`, with no hypothesis on `P'`. -/
theorem measurable_mdlW1 (P : Polynomial ℤ) (N : ℕ) : Measurable (mdlW1 P N) := by
  unfold mdlW1
  exact Complex.continuous_ofReal.measurable.comp
    (measurable_const.div (continuous_PderivR_comp P (N : ℝ)).measurable)

/-- `mdlW2 P N` is measurable in `t`, with no hypothesis on `P'`. -/
theorem measurable_mdlW2 (P : Polynomial ℤ) (N : ℕ) : Measurable (mdlW2 P N) := by
  have h2 : Measurable (fun t : ℝ => Pderiv2R P ((N : ℝ) * t)) := by
    simpa only [Pderiv2R, PderivR] using
      (continuous_PderivR_comp P.derivative (N : ℝ)).measurable
  unfold mdlW2
  exact Complex.continuous_ofReal.measurable.comp
    ((measurable_const.mul h2).div
      ((continuous_PderivR_comp P (N : ℝ)).pow 2).measurable)

/-! ## `Btwist` applied to two `Tle`-images, in the normal form `mdlNF` -/

theorem Btwist_Tle_eq_mdlNF (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (Φ Ψ : ℝ → ℂ) (F G : ℤ → ℂ) {CF CG : ℝ}
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hK : Summable fun p : ℤ × ℤ => ‖mdlBtwK ρ P l₁ l₂ m₁ m₂ p.1 p.2‖)
    (hκ : Summable fun i : ℤ => ‖mdlIWKer ρ l₁ Φ i‖)
    (hκ' : Summable fun i : ℤ => ‖mdlIWKer ρ l₂ Ψ i‖) (x : ℤ) :
    Btwist ρ P l₁ l₂ m₁ m₂ (Tle ρ l₁ Φ F) (Tle ρ l₂ Ψ G) x
      = mdlNF (mdlBtwK ρ P l₁ l₂ m₁ m₂) (mdlIWKer ρ l₁ Φ) (mdlIWKer ρ l₂ Ψ) F G x := by
  rw [Btwist_eq_bilinOp, Tle_eq_convOp, Tle_eq_convOp,
    ← Work.A7.ModelApproxCore_kernelComp (K := mdlBtwK ρ P l₁ l₂ m₁ m₂)
      (κ := mdlIWKer ρ l₁ Φ) (κ' := mdlIWKer ρ l₂ Ψ) (u := F) (v := G)
      (Cu := CF) (Cv := CG) hK hκ hκ' hF hG x]
  exact bilinOp_kernComp_eq_mdlNF hK hκ hκ' hF hG x

end

end Work.KMTPlan.A6
