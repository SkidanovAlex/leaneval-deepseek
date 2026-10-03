/-
# Shared foundations for Case B of the small-scale model estimate of the low case of area A6

This module collects the pieces that the proof of `Work.KMTPlan.A6.lowModelVarCaseB` shares with
its delegated sub-lemmas (so that those sub-lemmas can be stated in the same vocabulary and
imported by the target file without an import cycle):

* `tmKer_eq_arithChar`: the arithmetic-character form of the exact-height kernel
  `tmKer ρ l ψ i = (∑_{α ∈ (ℚ/ℤ)_l} e(-iα)) · cw ψ i`;
* `summable_arithKerM`: the kernel of the exact-height twisted bilinear multiplier is in
  `ℓ¹(ℤ²)` for the narrow window `m_* = mStarF u ⊗ mStargF d u`;
* `BtwistEx_Tm_eq_mdlNF`: the normal form of `BtwistEx` on two `Tm`-images;
* the *anchored clamped* bump families of Case B (the four modified bumps of the
  integration-by-parts identity, frozen at `t`, zero at `n = 0` and off the small-scale set),
  in the two variants (f-side of the low-high case, g-side of the low-high case, and the
  `j`-twists);
* the `TmRandModL2` interface: the `ℓ²`-bound for the *randomised* packets of those families,
  which is the `hSS`-hypothesis of the Rademacher--Menshov reduction
  (`Work.KMTPlan.A6.VrFull_TmBtwist_le_rand_abs`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallAux
import Submission.Work.KMTPlan.A6.MdlDecayLowHigh
import Submission.Work.KMTPlan.A6.MdlDecayHighLow
import Submission.Work.KMTPlan.A6.varphitildeNtj_bounds

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## The arithmetic-character form of the exact-height kernel -/

/-- **The arithmetic-character form of `tmKer`.**  For an integrable symbol `ψ` the convolution
kernel of the exact-height multiplier `Tm ρ l ψ` factors as the arithmetic character sum over the
exact-height frequency set times the continuous Fourier coefficient:
`tmKer ρ l ψ i = (∑_{α ∈ (ℚ/ℤ)_l} e(-iα)) · cw ψ i`. -/
theorem tmKer_eq_arithChar (ρ : ℝ) (l : ℕ) {ψ : ℝ → ℂ} (hψ : MeasureTheory.Integrable ψ) (i : ℤ) :
    tmKer ρ l ψ i
      = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-i) α) * cw ψ i :=
  IwKernelArithChar (diffFreqs ρ l) hψ i

/-! ## Bounds and summability of the kernel of `BtwistEx` -/

/-- The arithmetic symbol `m_Ẑ` is an average of `q` complex numbers of modulus one. -/
theorem mdl_mZ_norm_le_one' (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q) (α₁ α₂ : Circ) :
    ‖mZ P q α₁ α₂‖ ≤ 1 := by
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

/-- **The arithmetic kernel of `BtwistEx` is bounded by the product of the cardinalities** of the
two exact-height frequency sets. -/
theorem mdl_arithKernelEx_norm_le (ρ : ℝ) (P : Polynomial ℤ) (q l₁ l₂ : ℕ) (hq : 0 < q)
    (j₁ j₂ : ℤ) :
    ‖arithKernelEx ρ P q l₁ l₂ j₁ j₂‖
      ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
  unfold arithKernelEx
  calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
        mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ := norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          ‖mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ diffFreqs ρ l₁, ∑ _α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact mdl_mZ_norm_le_one' P q hq α₁ α₂
    _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- **The kernel of `BtwistEx` is in `ℓ¹(ℤ²)`**, for any two symbols with summable `cw`. -/
theorem summable_arithKernelEx_general (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (m₁ m₂ : ℝ → ℂ) (h₁ : Summable fun j : ℤ => ‖cw m₁ j‖)
    (h₂ : Summable fun j : ℤ => ‖cw m₂ j‖) (q : ℕ) (hq : 0 < q) :
    Summable fun p : ℤ × ℤ =>
      ‖arithKernelEx ρ P q l₁ l₂ p.1 p.2 * cw m₁ p.1 * cw m₂ p.2‖ := by
  have hbound : ∀ p : ℤ × ℤ,
      ‖arithKernelEx ρ P q l₁ l₂ p.1 p.2 * cw m₁ p.1 * cw m₂ p.2‖
        ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)
            * ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ := by
    intro p
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (mdl_arithKernelEx_norm_le ρ P q l₁ l₂ hq p.1 p.2) le_rfl
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) le_rfl
      (norm_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (norm_nonneg _))
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound ?_
  exact ((Summable.mul_of_nonneg h₁ h₂ (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)).mul_left
    (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ))).congr
    (fun p => by ring)

/-- **The kernel of `BtwistEx` with the narrow window `m_* = mStarF u ⊗ mStargF d u`** at
`u = uScale ρ (lcL l₁ l₂ k₁ k₂)` is in `ℓ¹(ℤ²)`. -/
theorem summable_arithKerM (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ : ℕ) :
    Summable fun p : ℤ × ℤ => ‖arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ := by
  have h := summable_arithKernelEx_general ρ P l₁ l₂
    (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (mdl_summable_cw_mStarF _) (mdl_summable_cw_mStargF _ _)
    (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ (max l₁ l₂))
  simpa only [arithKerM] using h

/-- The same, at an arbitrary window scale `u` and window symbols. -/
theorem summable_arithKernelEx_window (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) :
    Summable fun p : ℤ × ℤ => ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
      * cw (mStarF u) p.1 * cw (mStargF P.natDegree u) p.2‖ :=
  summable_arithKernelEx_general ρ P l₁ l₂ _ _ (mdl_summable_cw_mStarF u)
    (mdl_summable_cw_mStargF P.natDegree u) (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ (max l₁ l₂))

/-- **`BtwistEx` on two `Tm`-images, in the normal form `mdlNF`.** -/
theorem BtwistEx_Tm_eq_mdlNF (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (Φ Ψ : ℝ → ℂ) (F G : ℤ → ℂ) {CF CG : ℝ}
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hK : Summable fun p : ℤ × ℤ => ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂))
      l₁ l₂ p.1 p.2 * cw m₁ p.1 * cw m₂ p.2‖)
    (hκ : Summable fun i : ℤ => ‖tmKer ρ l₁ Φ i‖)
    (hκ' : Summable fun i : ℤ => ‖tmKer ρ l₂ Ψ i‖) (x : ℤ) :
    BtwistEx ρ P l₁ l₂ m₁ m₂ (Tm ρ l₁ Φ F) (Tm ρ l₂ Ψ G) x
      = mdlNF (fun a b => arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b
          * cw m₁ a * cw m₂ b) (tmKer ρ l₁ Φ) (tmKer ρ l₂ Ψ) F G x := by
  have hK' := hK
  have hmain : BtwistEx ρ P l₁ l₂ m₁ m₂ (Tm ρ l₁ Φ F) (Tm ρ l₂ Ψ G) x
      = bilinOp (fun a b => arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b
            * cw m₁ a * cw m₂ b)
          (convOp (tmKer ρ l₁ Φ) F) (convOp (tmKer ρ l₂ Ψ) G) x := by
    rw [Tm_eq_convOp, Tm_eq_convOp]
    rfl
  rw [hmain, ← Work.A7.ModelApproxCore_kernelComp (K := fun a b =>
      arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b * cw m₁ a * cw m₂ b)
    (κ := tmKer ρ l₁ Φ) (κ' := tmKer ρ l₂ Ψ) (u := F) (v := G)
    (Cu := CF) (Cv := CG) hK' hκ hκ' hF hG x]
  exact bilinOp_kernComp_eq_mdlNF hK' hκ hκ' hF hG x

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-- The arithmetic character of the exact-height frequency set `(ℚ/ℤ)_l` at the integer `i`:
the sum `∑_{α ∈ (ℚ/ℤ)_l} e(-iα)`. -/
noncomputable def tmChar (ρ : ℝ) (l : ℕ) (i : ℤ) : ℂ :=
  ∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-i) α

theorem tmKer_eq_tmChar_mul_cw (ρ : ℝ) (l : ℕ) {ψ : ℝ → ℂ}
    (hψ : MeasureTheory.Integrable ψ) (i : ℤ) :
    tmKer ρ l ψ i = tmChar ρ l i * cw ψ i :=
  tmKer_eq_arithChar ρ l hψ i

/-! ## The kernel-level integration-by-parts identity (ii) for `tmKer` -/

/-- **The kernel-level integration-by-parts identity (ii) at `(k₁, k₂ ≥ 1)` for the exact-height
kernel `tmKer`.**  This is the companion of `Work.KMTPlan.A6.MdlKerIdentLowHigh` in the
exact-height vocabulary: the `cw`-level identity `MdlCwIntegIdent` multiplied by the (now
`t`-independent) arithmetic character `tmChar ρ l₁ (-z₁) · tmChar ρ l₂ (-z₂)`. -/
theorem tmKerIdentLowHighEx (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ N k₁ k₂ : ℕ) (hk₂ : 1 ≤ k₂)
    (hN : 1 ≤ N)
    (hP : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, Work.KMTPlan.A6.PderivR P ((N : ℝ) * t) ≠ 0)
    (z₁ z₂ : ℤ) :
    (∫ t in (1 / 2 : ℝ)..1,
        tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) z₁
          * tmKer ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) z₂)
      = (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
          * (Work.KMTPlan.A6.mdlW1 P N 1
                * (tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ 1) z₁
                    * tmKer ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) 1) z₂)
              - Work.KMTPlan.A6.mdlW1 P N (1 / 2)
                * (tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ (1 / 2)) z₁
                    * tmKer ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) (1 / 2)) z₂))
        - (Work.KMTPlan.A6.mdlScaleFe P k₁ k₂ : ℂ)
            * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.mdlW1 P N t
                * (tmKer ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ 1 t) z₁
                    * tmKer ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) t) z₂))
        + (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.mdlW2 P N t
                * (tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) z₁
                    * tmKer ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) t) z₂)) := by
  have hcw := MdlCwIntegIdent P N k₁ k₂ hN hk₂ hP
  set T : ℂ := tmChar ρ l₁ z₁ * tmChar ρ l₂ z₂ with hT
  have hmem1 : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hmem2 : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hIcc : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    exact ht
  have hL : (∫ t in (1 / 2 : ℝ)..1,
        tmKer ρ l₁ (varphiNt N k₁ t) z₁ * tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t) z₂)
      = T * (∫ t in (1 / 2 : ℝ)..1,
          cw (varphiNt N k₁ t) z₁ * cw (varphitildeNt P P.natDegree N k₂ t) z₂) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [tmKer_eq_tmChar_mul_cw ρ l₁ (integrable_varphiNt N k₁ t) z₁,
        tmKer_eq_tmChar_mul_cw ρ l₂
          (integrable_varphitildeNt_aux P P.natDegree N k₂ t) z₂, hT]
    ring
  have hM1 : (∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t
        * (tmKer ρ l₁ (varphiNtj N k₁ 1 t) z₁
          * tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) z₂))
      = T * (∫ t in (1 / 2 : ℝ)..1,
          cw (varphiNtj N k₁ 1 t) z₁ * cw (varphitildeNtj P N k₂ (-1) t) z₂
            * mdlW1 P N t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' := hIcc t ht
    rw [tmKer_eq_tmChar_mul_cw ρ l₁ ((mdlKerVarphiNtjOne ρ l₁ N k₁).1 t ht') z₁,
        tmKer_eq_tmChar_mul_cw ρ l₂ ((mdlKerVarphitildeNtjNeg ρ l₂ P N k₂ hk₂).1 t ht') z₂, hT]
    ring
  have hM2 : (∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t
        * (tmKer ρ l₁ (varphiNt N k₁ t) z₁
          * tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) z₂))
      = T * (∫ t in (1 / 2 : ℝ)..1,
          cw (varphiNt N k₁ t) z₁ * cw (varphitildeNtj P N k₂ (-1) t) z₂
            * mdlW2 P N t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' := hIcc t ht
    rw [tmKer_eq_tmChar_mul_cw ρ l₁ (integrable_varphiNt N k₁ t) z₁,
        tmKer_eq_tmChar_mul_cw ρ l₂ ((mdlKerVarphitildeNtjNeg ρ l₂ P N k₂ hk₂).1 t ht') z₂, hT]
    ring
  have hB1 : tmKer ρ l₁ (varphiNt N k₁ 1) z₁
        * tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) 1) z₂
      = T * (cw (varphiNt N k₁ 1) z₁ * cw (varphitildeNtj P N k₂ (-1) 1) z₂) := by
    rw [tmKer_eq_tmChar_mul_cw ρ l₁ (integrable_varphiNt N k₁ 1) z₁,
        tmKer_eq_tmChar_mul_cw ρ l₂
          ((mdlKerVarphitildeNtjNeg ρ l₂ P N k₂ hk₂).1 1 hmem1) z₂, hT]
    ring
  have hB2 : tmKer ρ l₁ (varphiNt N k₁ (1 / 2)) z₁
        * tmKer ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) z₂
      = T * (cw (varphiNt N k₁ (1 / 2)) z₁
          * cw (varphitildeNtj P N k₂ (-1) (1 / 2)) z₂) := by
    rw [tmKer_eq_tmChar_mul_cw ρ l₁ (integrable_varphiNt N k₁ (1 / 2)) z₁,
        tmKer_eq_tmChar_mul_cw ρ l₂
          ((mdlKerVarphitildeNtjNeg ρ l₂ P N k₂ hk₂).1 (1 / 2) hmem2) z₂, hT]
    ring
  rw [hL, hM1, hM2, hB1, hB2, hcw z₁ z₂]
  ring

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## The anchored clamped bump families of Case B

Case B is the regime `max l₁ l₂ < lcL l₁ l₂ k₁ k₂ = max k₁ k₂` with `k₁ = 0 ∨ k₂ = 0`.  The
integration-by-parts identity of §6 replaces the modulated bumps `φ_{N,t}`, `φ̃_{N,t}` of the
model tuple by the *modified* bumps `φ_{N,t,j} = (2^{-k}Nξ)^j φ_{N,t}`,
`φ̃_{N,t,j} = (2^{-dk}N^dξ)^j φ̃_{N,t}` at the frozen times `t = 1`, `t = 1/2` (boundary terms) and
under the `t`-integral (weights `mdlW1`, `mdlW2`).  The families below are those bumps as families
of `n`, anchored at `n = 0` and clamped by `lowSmallSet` (which is what makes them narrow
supported and what the Rademacher--Menshov reduction of
`Work.KMTPlan.A6.VrFull_TmBtwist_le_rand_abs` needs). -/

/-- **The anchored `f`-side modified bump family** of Case B: the bump `φ_{N,k₁,j}(t)` at
`N = ⌊a n⌋` on the small-scale set, zero at `n = 0` and off the set. -/
noncomputable def lowModSymbF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (j : ℤ) (t : ℝ) : ℕ → ℝ → ℂ :=
  fun n ξ =>
    if n = 0 then 0
    else if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
      then varphiNtj (Nat.floor (a n)) k₁ j t ξ else 0

/-- **The anchored `g`-side modified bump family** of Case B: the bump `φ̃_{N,k₂,j}(t)` at
`N = ⌊a n⌋` on the small-scale set, zero at `n = 0` and off the set. -/
noncomputable def lowModSymbG (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (j : ℤ) (t : ℝ) : ℕ → ℝ → ℂ :=
  fun n ξ =>
    if n = 0 then 0
    else if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
      then varphitildeNtj P (Nat.floor (a n)) k₂ j t ξ else 0

theorem lowModSymbF_zero (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j : ℤ)
    (t : ℝ) : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t 0 = 0 := by
  funext ξ; simp [lowModSymbF]

theorem lowModSymbG_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (j : ℤ) (t : ℝ) : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t 0 = 0 := by
  funext ξ; simp [lowModSymbG]

/-- **The `ℓ²`-bound for the randomised `f`-side packets of Case B.**  For every twist `j` that is
not the forbidden pair `(k₁, j) = (0, -1)` of the paper's integration-by-parts identity, the
`ℓ²`-norm of the `Tm`-image of the randomised cut-off of the anchored clamped modified bump
family is bounded by the `ℓ²`-norm of `f`, with a constant depending only on `ρ`, `C₀` and `Λ`
(and *not* on `K`, `l₁`, `l₂`, `k₁`, `k₂`, `a`, `t`, `ε`). -/
def LowModRandL2F (P : Polynomial ℤ) (C₀ : ℕ) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ B : ℕ, ∃ C : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (j : ℤ) (ε : ℕ → ℂ)
      (f : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k₁ = 0 ∧ j = -1) →
      B ≤ lcL l₁ l₂ k₁ k₂ →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁
          (Work.KMTAreas.A7.randSymb (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t) ε K) f)
        2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- **The `ℓ²`-bound for the randomised `g`-side packets of Case B** (the mirror of
`LowModRandL2F`). -/
def LowModRandL2G (P : Polynomial ℤ) (C₀ : ℕ) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ B : ℕ, ∃ C : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (j : ℤ) (ε : ℕ → ℂ)
      (g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k₂ = 0 ∧ j = -1) →
      B ≤ lcL l₁ l₂ k₁ k₂ →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂
          (Work.KMTAreas.A7.randSymb (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t) ε K) g)
        2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## The kernel-level integration-by-parts identity (i) for `tmKer`

The `cw`-level identity (i) is proved in `MdlKerIdentHighLow.lean` as a *private* lemma
`MdlCwIntegIdentI_aux`; the statement below takes it as a hypothesis, so that the exact-height
kernel form can be derived without re-running its (long) Fubini argument.  The public form of the
`cw`-level identity is delegated as `Work.KMTPlan.A6.MdlCwIntegIdentI`. -/

/-- **The kernel-level integration-by-parts identity (i) at `(k₁ ≥ 1, k₂ = 0)` for the
exact-height kernel `tmKer`**, from the `cw`-level identity (i). -/
theorem tmKerIdentHighLowEx (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ N k₁ : ℕ) (hk₁ : 1 ≤ k₁)
    (hN : 1 ≤ N)
    (hcw : ∀ i₁ i₂ : ℤ,
      (∫ t in (1 / 2 : ℝ)..1,
          cw (varphiNt N k₁ t) i₁ * cw (varphitildeNt P P.natDegree N 0 t) i₂)
        = (Work.KMTPlan.A6.mdlScaleF k₁ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (cw (Work.KMTPlan.A6.varphiNtj N k₁ (-1) 1) i₁
                * cw (varphitildeNt P P.natDegree N 0 1) i₂
              - cw (Work.KMTPlan.A6.varphiNtj N k₁ (-1) (1 / 2)) i₁
                * cw (varphitildeNt P P.natDegree N 0 (1 / 2)) i₂)
          - (Work.KMTPlan.A6.mdlScaleFG P k₁ 0 : ℂ)
              * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.mdlW3 P N t
                  * (cw (Work.KMTPlan.A6.varphiNtj N k₁ (-1) t) i₁
                      * cw (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t) i₂)))
    (z₁ z₂ : ℤ) :
    (∫ t in (1 / 2 : ℝ)..1,
        tmKer ρ l₁ (varphiNt N k₁ t) z₁
          * tmKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) z₂)
      = (Work.KMTPlan.A6.mdlScaleF k₁ : ℂ) * Work.KMTPlan.A6.mdlIota
          * (tmKer ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ (-1) 1) z₁
                * tmKer ρ l₂ (varphitildeNt P P.natDegree N 0 1) z₂
              - tmKer ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ (-1) (1 / 2)) z₁
                * tmKer ρ l₂ (varphitildeNt P P.natDegree N 0 (1 / 2)) z₂)
        - (Work.KMTPlan.A6.mdlScaleFG P k₁ 0 : ℂ)
            * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.mdlW3 P N t
                * (tmKer ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ (-1) t) z₁
                    * tmKer ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t) z₂)) := by
  set T : ℂ := tmChar ρ l₁ z₁ * tmChar ρ l₂ z₂ with hT
  have hIcc : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    exact ht
  have hL : (∫ t in (1 / 2 : ℝ)..1,
        tmKer ρ l₁ (varphiNt N k₁ t) z₁
          * tmKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) z₂)
      = T * (∫ t in (1 / 2 : ℝ)..1,
          cw (varphiNt N k₁ t) z₁ * cw (varphitildeNt P P.natDegree N 0 t) z₂) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [tmKer_eq_tmChar_mul_cw ρ l₁ (integrable_varphiNt N k₁ t) z₁,
        tmKer_eq_tmChar_mul_cw ρ l₂ (integrable_varphitildeNt_aux P P.natDegree N 0 t) z₂, hT]
    ring
  have hmem1 : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hmem2 : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hM : (∫ t in (1 / 2 : ℝ)..1, mdlW3 P N t
        * (tmKer ρ l₁ (varphiNtj N k₁ (-1) t) z₁
          * tmKer ρ l₂ (varphitildeNtj P N 0 1 t) z₂))
      = T * (∫ t in (1 / 2 : ℝ)..1, mdlW3 P N t
          * (cw (varphiNtj N k₁ (-1) t) z₁ * cw (varphitildeNtj P N 0 1 t) z₂)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' := hIcc t ht
    rw [tmKer_eq_tmChar_mul_cw ρ l₁ ((MdlKerVarphiNtj ρ l₁ N k₁ hk₁).1 t ht') z₁,
        tmKer_eq_tmChar_mul_cw ρ l₂ ((MdlKerVarphitildeNtj ρ l₂ P N).1 t ht') z₂, hT]
    ring
  have hB1 : tmKer ρ l₁ (varphiNtj N k₁ (-1) 1) z₁
        * tmKer ρ l₂ (varphitildeNt P P.natDegree N 0 1) z₂
      = T * (cw (varphiNtj N k₁ (-1) 1) z₁
          * cw (varphitildeNt P P.natDegree N 0 1) z₂) := by
    rw [tmKer_eq_tmChar_mul_cw ρ l₁ ((MdlKerVarphiNtj ρ l₁ N k₁ hk₁).1 1 hmem1) z₁,
        tmKer_eq_tmChar_mul_cw ρ l₂ (integrable_varphitildeNt_aux P P.natDegree N 0 1) z₂, hT]
    ring
  have hB2 : tmKer ρ l₁ (varphiNtj N k₁ (-1) (1 / 2)) z₁
        * tmKer ρ l₂ (varphitildeNt P P.natDegree N 0 (1 / 2)) z₂
      = T * (cw (varphiNtj N k₁ (-1) (1 / 2)) z₁
          * cw (varphitildeNt P P.natDegree N 0 (1 / 2)) z₂) := by
    rw [tmKer_eq_tmChar_mul_cw ρ l₁ ((MdlKerVarphiNtj ρ l₁ N k₁ hk₁).1 (1 / 2) hmem2) z₁,
        tmKer_eq_tmChar_mul_cw ρ l₂ (integrable_varphitildeNt_aux P P.natDegree N 0 (1 / 2)) z₂,
        hT]
    ring
  rw [hL, hM, hB1, hB2, hcw z₁ z₂]
  ring

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## The named kernel of `BtwistEx` for general window symbols -/

/-- The kernel of the exact-height twisted bilinear multiplier `BtwistEx` with the window
`m₁ ⊗ m₂`: `arithKerMX ρ P l₁ l₂ m₁ m₂ a b = arithKernelEx … a b · cw m₁ a · cw m₂ b`. -/
noncomputable def arithKerMX (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) :
    ℤ → ℤ → ℂ :=
  fun a b => arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b * cw m₁ a * cw m₂ b

theorem arithKerM_eq_arithKerMX (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ : ℕ) :
    arithKerM ρ P l₁ l₂ k₁ k₂
      = arithKerMX ρ P l₁ l₂ (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
          (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) := rfl

theorem summable_arithKerMX (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) :
    Summable fun p : ℤ × ℤ => ‖arithKerMX ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      p.1 p.2‖ := by
  have h : Summable fun p : ℤ × ℤ => ‖arithKerMX ρ P l₁ l₂ (mStarF u)
      (mStargF P.natDegree u) p.1 p.2‖ := summable_arithKernelEx_window ρ P l₁ l₂ u
  exact h

/-! ## The `ℓ²`-interfaces with the structural hypotheses of the available library

The `j = 0` case of `LowModRandL2F`/`LowModRandL2G` is the proved
`Work.KMTPlan.A6.tmRandSymb_l2` / `tmRandSymbG_l2`, which require `2 ≤ P.natDegree`,
`AreaA1` and `1 ≤ C₀` (through `randSymbG_sup_le`, the good-major-arcs constant of `AreaA1` and
`narrow_of_index`).  The two interfaces below carry those hypotheses as arguments, which is the
form in which the assembly of `Work.KMTPlan.A6.lowModelVarCaseB` consumes them (all three are
hypotheses of that target). -/

/-- The `f`-side randomised `ℓ²`-interface with the structural hypotheses. -/
def LowModRandL2F' (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ B : ℕ, ∃ C : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (j : ℤ) (ε : ℕ → ℂ)
      (f : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k₁ = 0 ∧ j = -1) →
      B ≤ lcL l₁ l₂ k₁ k₂ →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁
          (Work.KMTAreas.A7.randSymb (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t) ε K) f)
        2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- The `g`-side randomised `ℓ²`-interface with the structural hypotheses. -/
def LowModRandL2G' (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ B : ℕ, ∃ C : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (j : ℤ) (ε : ℕ → ℂ)
      (g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k₂ = 0 ∧ j = -1) →
      B ≤ lcL l₁ l₂ k₁ k₂ →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂
          (Work.KMTAreas.A7.randSymb (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t) ε K) g)
        2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- `LowModRandL2F'` implies `LowModRandL2F` (the latter quantifies over fewer hypotheses only
through the parameters; it is the same statement at `hd`, `hA1`, `hC₀` fixed). -/
theorem lowModRandL2F_of' {P : Polynomial ℤ} {C₀ : ℕ} (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hC₀ : 1 ≤ C₀) (h : LowModRandL2F' P hd hA1 C₀ hC₀) :
    LowModRandL2F P C₀ := h

/-- The `g`-side analogue. -/
theorem lowModRandL2G_of' {P : Polynomial ℤ} {C₀ : ℕ} (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hC₀ : 1 ≤ C₀) (h : LowModRandL2G' P hd hA1 C₀ hC₀) :
    LowModRandL2G P C₀ := h

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## The uniform majorants of the exact-height kernels of the four modified bumps -/

/-- Joint measurability of the modulated bump `varphiNt N k`. -/
theorem measurable_varphiNt_uncurryEx0 (N k : ℕ) :
    Measurable fun q : ℝ × ℝ => varphiNt N k q.1 q.2 := by
  have h1 : Measurable (fun q : ℝ × ℝ => varphiN N k q.2) :=
    (Work.KMTAreas.A7.contDiff_varphiN N k).continuous.measurable.comp measurable_snd
  have h2 : Measurable (fun q : ℝ × ℝ => ee ((N : ℝ) * q.1 * q.2)) := by
    have hc : Continuous (fun q : ℝ × ℝ => ee ((N : ℝ) * q.1 * q.2)) := by
      unfold ee; fun_prop
    exact hc.measurable
  rw [show (fun q : ℝ × ℝ => varphiNt N k q.1 q.2)
      = fun q : ℝ × ℝ => varphiN N k q.2 * ee ((N : ℝ) * q.1 * q.2) from rfl]
  exact h1.mul h2

/-- Joint measurability of the modulated bump `varphitildeNt P d N k`. -/
theorem measurable_varphitildeNt_uncurryEx0 (P : Polynomial ℤ) (N k : ℕ) :
    Measurable fun q : ℝ × ℝ => varphitildeNt P P.natDegree N k q.1 q.2 := by
  have h1 : Measurable (fun q : ℝ × ℝ => varphitildeN P.natDegree N k q.2) :=
    (Work.KMTAreas.A7.contDiff_varphitildeN P.natDegree N k).continuous.measurable.comp
      measurable_snd
  have h2 : Measurable (fun q : ℝ × ℝ => ee (PevalR P ((N : ℝ) * q.1) * q.2)) := by
    have hc : Continuous (fun q : ℝ × ℝ => ee (PevalR P ((N : ℝ) * q.1) * q.2)) := by
      have hp : Continuous fun q : ℝ × ℝ => PevalR P ((N : ℝ) * q.1) :=
        (continuous_PevalR_comp P (N : ℝ)).comp continuous_fst
      unfold ee
      exact Complex.continuous_exp.comp (by fun_prop)
    exact hc.measurable
  rw [show (fun q : ℝ × ℝ => varphitildeNt P P.natDegree N k q.1 q.2)
      = fun q : ℝ × ℝ => varphitildeN P.natDegree N k q.2
          * ee (PevalR P ((N : ℝ) * q.1) * q.2) from rfl]
  exact h1.mul h2

/-- Uncurried measurability of the modified `f`-side bump (`j ∈ {-1,0,1}`). -/
theorem measurable_varphiNtj_uncurryEx (N k : ℕ) (j : ℤ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) :
    Measurable fun p : ℝ × ℝ => varphiNtj N k j p.1 p.2 := by
  have h0 : Measurable fun p : ℝ × ℝ => varphiNt N k p.1 p.2 :=
    measurable_varphiNt_uncurryEx0 N k
  have hbase : Measurable fun p : ℝ × ℝ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ))
      : ℂ) := by fun_prop
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h | h
  · subst h
    rw [show (fun p : ℝ × ℝ => varphiNtj N k (-1) p.1 p.2)
        = fun p : ℝ × ℝ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ)⁻¹
            * varphiNt N k p.1 p.2 by
      (funext p; rw [varphiNtj, zpow_neg_one])]
    exact hbase.inv.mul h0
  · subst h
    simpa only [varphiNtj_zero] using h0
  · subst h
    rw [show (fun p : ℝ × ℝ => varphiNtj N k 1 p.1 p.2)
        = fun p : ℝ × ℝ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ)
            * varphiNt N k p.1 p.2 by
      (funext p; rw [varphiNtj, zpow_one])]
    exact hbase.mul h0

/-- Uncurried measurability of the modified `g`-side bump (`j ∈ {-1,0,1}`). -/
theorem measurable_varphitildeNtj_uncurryEx (P : Polynomial ℤ) (N k : ℕ) (j : ℤ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) :
    Measurable fun p : ℝ × ℝ => varphitildeNtj P N k j p.1 p.2 := by
  have h0 : Measurable fun p : ℝ × ℝ => varphitildeNt P P.natDegree N k p.1 p.2 :=
    measurable_varphitildeNt_uncurryEx0 P N k
  have hbase : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * p.2 : ℝ))
        : ℂ) := by fun_prop
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h | h
  · subst h
    rw [show (fun p : ℝ × ℝ => varphitildeNtj P N k (-1) p.1 p.2)
        = fun p : ℝ × ℝ =>
            ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * p.2
              : ℝ)) : ℂ)⁻¹ * varphitildeNt P P.natDegree N k p.1 p.2 by
      (funext p; rw [varphitildeNtj, zpow_neg_one])]
    exact hbase.inv.mul h0
  · subst h
    simpa only [varphitildeNtj_zero] using h0
  · subst h
    rw [show (fun p : ℝ × ℝ => varphitildeNtj P N k 1 p.1 p.2)
        = fun p : ℝ × ℝ =>
            ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * p.2
              : ℝ)) : ℂ) * varphitildeNt P P.natDegree N k p.1 p.2 by
      (funext p; rw [varphitildeNtj, zpow_one])]
    exact hbase.mul h0

/-- **The generic kernel package for `tmKer`.**  A measurable bump family `Φ`, `C²` with compact
support and with uniform-in-`t` `L¹`-bounds for the bump and its second derivative, has a summable
uniform majorant for the exact-height kernel `tmKer ρ l (Φ t)` together with the measurability in
`t` of that kernel; the proof is the `diffFreqs ρ l` instance of `iwKernel_decay_of_bump`
(the arithmetic-character factor is not needed: equivalently one may use `tmKer_eq_arithChar`
together with the decay of `cw`). -/
theorem tmKerPackageEx (ρ : ℝ) (l : ℕ) {Φ : ℝ → ℝ → ℂ}
    (hcd : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ContDiff ℝ 2 (Φ t))
    (hcs : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, HasCompactSupport (Φ t))
    {S : ℝ} (hSnn : 0 ≤ S)
    (hbd : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      (∫ y, ‖Φ t y‖) ≤ S ∧ (∫ y, ‖iteratedDeriv 2 (Φ t) y‖) ≤ S)
    (hmeas : Measurable fun p : ℝ × ℝ => Φ p.1 p.2) :
    ∃ a : ℤ → ℝ, Summable a ∧
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ, ‖tmKer ρ l (Φ t) i‖ ≤ a i) ∧
      (∀ i : ℤ, Measurable (fun t : ℝ => tmKer ρ l (Φ t) i)) := by
  classical
  have h1 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ j : ℤ,
      ‖tmKer ρ l (Φ t) j‖ ≤ (4 * (((diffFreqs ρ l).card : ℝ) * S) + 1)
        * ‖kmtKernWeight j‖ := by
    intro t ht j
    have h := iwKernel_decay_of_bump (diffFreqs ρ l) (hcd t ht) (hcs t ht) hSnn
      (hbd t ht).1 (hbd t ht).2 j
    simpa only [tmKer] using h
  refine ⟨fun i => (4 * (((diffFreqs ρ l).card : ℝ) * S) + 1) * ‖kmtKernWeight i‖,
    summable_kmtKernWeight.mul_left _, ?_, ?_⟩
  · intro t ht i
    exact h1 t ht i
  · intro i
    have h := measurable_fourierCoeff_iwSymbolSet (diffFreqs ρ l) i
      (φ := fun t ξ => Φ t ξ) hmeas
    simpa only [tmKer, Work.Analysis.IWMultiplier.iwKernel] using h

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## The concrete kernel packages of the six bump families of Case B -/

/-- **The kernel package of the modified `f`-side bump** `varphiNtj N k j t` for
`j ∈ {-1,0,1}` (excluding the singular pair `(k,j) = (0,-1)`): a summable uniform majorant for
`tmKer ρ l (varphiNtj N k j t)` together with its measurability in `t`. -/
theorem tmKerPackage_varphiNtj (ρ : ℝ) (l N k : ℕ) (j : ℤ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (hk : k ≠ 0 ∨ 0 ≤ j) :
    ∃ a : ℤ → ℝ, Summable a ∧
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ, ‖tmKer ρ l (varphiNtj N k j t) i‖ ≤ a i) ∧
      (∀ i : ℤ, Measurable (fun t : ℝ => tmKer ρ l (varphiNtj N k j t) i)) := by
  obtain ⟨S, hSnn, hbd⟩ := varphiNtj_bounds N k j hk
  exact tmKerPackageEx ρ l (Φ := fun t ξ => varphiNtj N k j t ξ)
    (fun t ht => (hbd t ht).1) (fun t ht => (hbd t ht).2.1) hSnn
    (fun t ht => ⟨(hbd t ht).2.2.1, (hbd t ht).2.2.2⟩)
    (measurable_varphiNtj_uncurryEx N k j hj)

/-- **The kernel package of the modified `g`-side bump** `varphitildeNtj P N k j t` for
`j ∈ {-1,0,1}` (excluding the singular pair `(k,j) = (0,-1)`). -/
theorem tmKerPackage_varphitildeNtj (ρ : ℝ) (l : ℕ) (P : Polynomial ℤ) (N k : ℕ) (j : ℤ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (hk : k ≠ 0 ∨ 0 ≤ j) :
    ∃ a : ℤ → ℝ, Summable a ∧
      (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
        ‖tmKer ρ l (varphitildeNtj P N k j t) i‖ ≤ a i) ∧
      (∀ i : ℤ, Measurable (fun t : ℝ => tmKer ρ l (varphitildeNtj P N k j t) i)) := by
  obtain ⟨S, hSnn, hbd⟩ := varphitildeNtj_bounds P N k j hk
  exact tmKerPackageEx ρ l (Φ := fun t ξ => varphitildeNtj P N k j t ξ)
    (fun t ht => (hbd t ht).1) (fun t ht => (hbd t ht).2.1) hSnn
    (fun t ht => ⟨(hbd t ht).2.2.1, (hbd t ht).2.2.2⟩)
    (measurable_varphitildeNtj_uncurryEx P N k j hj)

theorem jmem (j : ℤ) (hj : j = -1 ∨ j = 0 ∨ j = 1) : j ∈ ({-1, 0, 1} : Finset ℤ) := by
  rcases hj with rfl | rfl | rfl <;> simp

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## The bodies of the two randomised-`ℓ²` interfaces

Splitting the interfaces into an existential envelope (`∃ B, ∃ C, body`) and the body is what
lets a consumer that has already fixed the threshold `B` and the constants state the estimate in
the form it needs. -/

/-- The body of `LowModRandL2F` at fixed `ρ`, `B`, `C`. -/
def LowModRandL2FBody (P : Polynomial ℤ) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) (C : NNReal → NNReal) : Prop :=
  ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (j : ℤ) (ε : ℕ → ℂ)
    (f : ℤ → ℂ),
    1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
    (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
    j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k₁ = 0 ∧ j = -1) →
    B ≤ lcL l₁ l₂ k₁ k₂ →
    MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
    MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁
        (Work.KMTAreas.A7.randSymb (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t) ε K) f)
      2 MeasureTheory.Measure.count
      ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- The body of `LowModRandL2G` at fixed `ρ`, `B`, `C`. -/
def LowModRandL2GBody (P : Polynomial ℤ) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) (C : NNReal → NNReal) : Prop :=
  ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (j : ℤ) (ε : ℕ → ℂ)
    (g : ℤ → ℂ),
    1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
    (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
    j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k₂ = 0 ∧ j = -1) →
    B ≤ lcL l₁ l₂ k₁ k₂ →
    MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
    MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂
        (Work.KMTAreas.A7.randSymb (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t) ε K) g)
      2 MeasureTheory.Measure.count
      ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- `LowModRandL2F'` unfolded into the existential envelope of its body. -/
theorem lowModRandL2F'_iff_body (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    LowModRandL2F' P hd hA1 C₀ hC₀ ↔
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
        ∃ B : ℕ, ∃ C : NNReal → NNReal, LowModRandL2FBody P C₀ ρ B C := Iff.rfl

/-- `LowModRandL2G'` unfolded into the existential envelope of its body. -/
theorem lowModRandL2G'_iff_body (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    LowModRandL2G' P hd hA1 C₀ hC₀ ↔
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
        ∃ B : ℕ, ∃ C : NNReal → NNReal, LowModRandL2GBody P C₀ ρ B C := Iff.rfl

end

end Work.KMTPlan.A6
