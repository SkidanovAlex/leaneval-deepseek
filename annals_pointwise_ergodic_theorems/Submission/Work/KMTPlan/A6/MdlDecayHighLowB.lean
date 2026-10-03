/-
# The operator-level integration-by-parts identity (i) of §6 with arbitrary bounds `Cf`, `Cg`

This module proves `Work.KMTPlan.A6.MdlDecayHighLowB`, the *bounded* (`B` for "bounded inputs")
form of the operator-level integration-by-parts identity (i) of Krause--Mirek--Tao §6 at the pair
`(k₁, k₂) = (k₁, 0)`:

  `mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ 0 0 0
     = (mdlScaleF k₁) mdlIota (sliceW(j₁=-1,j₂=0, w=1, t=1) − sliceW(..., t=1/2))
       − mdlScaleFG P k₁ 0 · WInt(j₁=-1, j₂=1, w = mdlW3)`

where the only difference with `Work.KMTPlan.A6.MdlDecayHighLow` is that the inputs `f`, `g` are
assumed bounded in the *normalised square* sense with **arbitrary** constants `Cf`, `Cg`
(`Complex.normSq (f x) ≤ Cf`, `Complex.normSq (g x) ≤ Cg`) rather than `≤ 1`.

The proof is the same argument as `MdlDecayHighLow` — `mdlDecayHighLow_core` already takes the
*pointwise* bounds `‖F y‖ ≤ CF`, `‖G y‖ ≤ CG` as parameters, and the only place where the
normalisation `≤ 1` was used is the extraction of the bounds for the exact-height projections
`mdlF ρ u l₁ f`, `mdlG ρ P u l₂ g`.  Here the extraction is done for a general constant, via
`mdl_F_bounded_of_le` / `mdl_G_bounded_of_le`: from `Complex.normSq (f x) ≤ Cf` one gets
`‖f x‖ ≤ √(max Cf 0)`, and `Work.A7.ModelApproxCore_aux.norm_convOp_le` then bounds the
convolution by `(∑'_j ‖exactKer … j‖) · max (√(max Cf 0)) 0`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDecayHighLow

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger

/-! ## Extracting a bound from a bound on the normalised square -/

/-- `‖z‖ ≤ √(max C 0)` from `Complex.normSq z ≤ C`. -/
theorem mdl_norm_le_sqrt_max {z : ℂ} {C : ℝ} (h : Complex.normSq z ≤ C) :
    ‖z‖ ≤ Real.sqrt (max C 0) := by
  have h2 : ‖z‖ ^ 2 ≤ max C 0 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact le_trans h (le_max_left _ _)
  exact (Real.le_sqrt (norm_nonneg z) (le_max_right _ _)).mpr h2

/-- **The exact-height projection of a sequence with `Complex.normSq ≤ Cf` is bounded.**  This is
`Work.KMTPlan.A6.mdl_F_bounded` with the normalisation `Cf = 1` replaced by an arbitrary constant
`Cf` (no sign hypothesis on `Cf` is needed: the bound is in terms of `max Cf 0`). -/
theorem mdl_F_bounded_of_le (ρ : ℝ) (u l : ℕ) {f : ℤ → ℂ} {Cf : ℝ}
    (hf : ∀ x : ℤ, Complex.normSq (f x) ≤ Cf) :
    ∃ C : ℝ, ∀ y : ℤ, ‖mdlF ρ u l f y‖ ≤ C := by
  have hf1 : ∀ x : ℤ, ‖f x‖ ≤ Real.sqrt (max Cf 0) := fun x => mdl_norm_le_sqrt_max (hf x)
  refine ⟨(∑' j : ℤ, ‖exactKer ρ l (-(u : ℤ)) j‖) * max (Real.sqrt (max Cf 0)) 0, fun y => ?_⟩
  have hb : Work.KMTAreas.A5.BoundedZ f := Work.KMTAreas.A5.boundedZ_of_bound hf1
  rw [mdlF, Work.A7.piExact_eq_convOp ρ l (-(u : ℤ)) hb]
  exact Work.A7.ModelApproxCore_aux.norm_convOp_le
    (κ := exactKer ρ l (-(u : ℤ))) (u := f) (Cu := Real.sqrt (max Cf 0))
    (mdl_summable_exactKer_norm ρ l _) hf1 y

/-- **The twisted exact-height projection of a sequence with `Complex.normSq ≤ Cg` is bounded**
(the `g`-side analogue of `mdl_F_bounded_of_le`, i.e. of `Work.KMTPlan.A6.mdl_G_bounded`). -/
theorem mdl_G_bounded_of_le (ρ : ℝ) (P : Polynomial ℤ) (u l : ℕ) {g : ℤ → ℂ} {Cg : ℝ}
    (hg : ∀ x : ℤ, Complex.normSq (g x) ≤ Cg) :
    ∃ C : ℝ, ∀ y : ℤ, ‖mdlG ρ P u l g y‖ ≤ C := by
  have hg1 : ∀ x : ℤ, ‖g x‖ ≤ Real.sqrt (max Cg 0) := fun x => mdl_norm_le_sqrt_max (hg x)
  refine ⟨(∑' j : ℤ, ‖exactKer ρ l (-((P.natDegree : ℤ) * (u : ℤ))) j‖)
    * max (Real.sqrt (max Cg 0)) 0, fun y => ?_⟩
  have hb : Work.KMTAreas.A5.BoundedZ g := Work.KMTAreas.A5.boundedZ_of_bound hg1
  rw [mdlG, Work.A7.piExact_eq_convOp ρ l (-((P.natDegree : ℤ) * (u : ℤ))) hb]
  exact Work.A7.ModelApproxCore_aux.norm_convOp_le
    (κ := exactKer ρ l (-((P.natDegree : ℤ) * (u : ℤ)))) (u := g) (Cu := Real.sqrt (max Cg 0))
    (mdl_summable_exactKer_norm ρ l _) hg1 y

/-! ## The identity -/

theorem MdlDecayHighLowB (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ : ℕ) (hk₁ : 1 ≤ k₁) (Cf Cg : ℝ)
    (hf : ∀ x : ℤ, Complex.normSq (f x) ≤ Cf)
    (hg : ∀ x : ℤ, Complex.normSq (g x) ≤ Cg)
    (hN : ∀ n : ℕ, 1 ≤ Nat.floor (a n)) :
    Work.KMTPlan.A6.mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ 0 0 0
      = fun n x => (Work.KMTPlan.A6.mdlScaleF k₁ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (Work.KMTPlan.A6.mdlSliceW ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 0
                  (fun _ _ => (1 : ℂ)) 1 n x
              - Work.KMTPlan.A6.mdlSliceW ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 0
                  (fun _ _ => (1 : ℂ)) (1 / 2) n x)
        - (Work.KMTPlan.A6.mdlScaleFG P k₁ 0 : ℂ)
            * Work.KMTPlan.A6.mdlWInt ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1
                (fun n t => Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t) n x := by
  funext n x
  by_cases hcore : mdlCore ρ C₀ a l₁ l₂ k₁ 0 n
  · obtain ⟨CF, hCF⟩ := mdl_F_bounded_of_le ρ (uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₁ hf
    obtain ⟨CG, hCG⟩ := mdl_G_bounded_of_le ρ P (uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ hg
    obtain ⟨Cw, hCw0, hw⟩ := mdl_W3_bound P (Nat.floor (a n))
    have hwm : AEStronglyMeasurable (fun t : ℝ => mdlW3 P (Nat.floor (a n)) t)
        (volume : MeasureTheory.Measure ℝ) :=
      (mdl_W3_continuous P _).measurable.aestronglyMeasurable
    have hK : Summable fun p : ℤ × ℤ =>
        ‖mdlBtwK ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ 0))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ 0)))) p.1 p.2‖ :=
      mdl_summable_mdlBtwK ρ P l₁ l₂ _ _
        (summable_cw_mStarF (uScale ρ (max (max l₁ l₂) (max k₁ 0))))
        (summable_cw_mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ 0))))
    obtain ⟨a₁, ha₁, hb₁, hm₁⟩ := MdlKerVarphiNt ρ l₁ (Nat.floor (a n)) k₁
    obtain ⟨a₂, ha₂, hb₂, hm₂⟩ := MdlKerVarphitildeNt ρ l₂ P.natDegree (Nat.floor (a n)) 0 P
    obtain ⟨_, a₃, ha₃, hb₃, hm₃⟩ := MdlKerVarphiNtj ρ l₁ (Nat.floor (a n)) k₁ hk₁
    obtain ⟨_, a₄, ha₄, hb₄, hm₄⟩ := MdlKerVarphitildeNtj ρ l₂ P (Nat.floor (a n))
    rw [mdlPartJ_zero_zero, mdlPart_eq, if_pos hcore]
    simp only [mdlSliceW, mdlWInt, if_pos hcore, one_mul]
    exact mdlDecayHighLow_core ρ P l₁ l₂ (Nat.floor (a n)) k₁ hk₁ (hN n)
      (uScale ρ (max (max l₁ l₂) (max k₁ 0)))
      (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₁ f)
      (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ g)
      CF CG Cw hCF hCG hCw0 hw hwm hK a₁ a₂ a₃ a₄ ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hb₄
      (fun i => (hm₁ i).aestronglyMeasurable) (fun i => (hm₂ i).aestronglyMeasurable)
      (fun i => (hm₃ i).aestronglyMeasurable) (fun i => (hm₄ i).aestronglyMeasurable) x
  · rw [mdlPartJ_eq_zero_of_not_core ρ P C₀ a f g l₁ l₂ k₁ 0 0 0 n x hcore]
    simp [mdlSliceW, mdlWInt, hcore]

end

end Work.KMTPlan.A6
