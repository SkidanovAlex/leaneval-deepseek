import Mathlib
import Submission.Work.KMTPlan.A6.varphiNt_support_all
import Submission.Work.KMTPlan.A6.Tm_lowSymbG_bdd
import Submission.Work.KMTPlan.A6.sliceAEMeasurable
import Submission.Work.KMTPlan.A6.aemeasurable_prod_count_iff
import Submission.Work.KMTPlan.A6.ssuBtwistExBdd
import Submission.Work.KMTPlan.A6.memLp_periodize_randSymb_lowSymb
import Submission.Work.KMTPlan.A6.lowModelVarCaseBLinf
import Submission.Work.KMTPlan.A6.MdlDecayHighLowB
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract

/-! ## The `t`-slices of the small-scale model tuple -/

/-- **Pointwise Minkowski in `t`.**  The variational norm of the model tuple is at most the
interval integral of the variational norms of its slices. -/
theorem varNorm_lowModel_le (r : ℝ≥0) (hr : 1 ≤ r) (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ)
    (a : ℕ → ℝ≥0) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (x : ℤ) (hM : ∀ n : ℕ,
      Measurable fun t : ℝ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
    (hI : ∀ n : ℕ, IntervalIntegrable
      (fun t : ℝ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x) volume (1 / 2) 1) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      ≤ ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1,
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x) := by
  have hseq : (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      = (fun n : ℕ => ∫ t in (1 / 2 : ℝ)..1,
          lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x) := by
    funext n
    exact lowModel_eq_integral_slice ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
  rw [hseq]
  exact varNorm_integral_le r hr
    (fun t : ℝ => fun n : ℕ => fun y : ℤ =>
      lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n y) x hI hM

/-- **The `t`-integral step of the assembly.**  If the variational norms of the slices obey a
uniform-in-`t` bound `C` in `ℓ¹(ℤ)`, then so does the variational norm of the model tuple
itself.  This is the pointwise Minkowski inequality `varNorm_lowModel_le` followed by Tonelli. -/
theorem eLpNorm_varNorm_lowModel_le_of_uniform (r : ℝ≥0) (hr : 1 ≤ r) (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ)
    (a : ℕ → ℝ≥0) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (C : ENNReal)
    (hMis : AEMeasurable (Function.uncurry (fun x : ℤ => fun t : ℝ => variationalNorm r
      (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)))
      (MeasureTheory.Measure.count.prod (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))))
    (hI : ∀ (x : ℤ) (n : ℕ), IntervalIntegrable
      (fun t : ℝ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x) volume (1 / 2) 1)
    (hM : ∀ (x : ℤ) (n : ℕ), Measurable fun t : ℝ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
    (hC : ∀ t : ℝ, MeasureTheory.eLpNorm (fun x : ℤ =>
      variationalNorm r (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
      1 MeasureTheory.Measure.count ≤ C) :
    MeasureTheory.eLpNorm (fun x : ℤ =>
      variationalNorm r (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      1 MeasureTheory.Measure.count ≤ C := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  have step1 : (∫⁻ x : ℤ, ‖variationalNorm r
        (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)‖ₑ ∂MeasureTheory.Measure.count)
      ≤ ∫⁻ x : ℤ, (∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1,
          variationalNorm r (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
            ∂volume) ∂MeasureTheory.Measure.count := by
    refine lintegral_mono (fun x => ?_)
    rw [enorm_eq_self]
    exact varNorm_lowModel_le r hr ρ P C₀ a f g l₁ l₂ k₁ k₂ x (hM x) (hI x)
  refine step1.trans ?_
  have step2 : (∫⁻ x : ℤ, (∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1,
        variationalNorm r (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
          ∂volume) ∂MeasureTheory.Measure.count)
      = ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, (∫⁻ x : ℤ,
          variationalNorm r (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
            ∂MeasureTheory.Measure.count) ∂volume := by
    rw [MeasureTheory.lintegral_lintegral_swap]
    exact hMis
  rw [step2]
  have hcongr : (∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, (∫⁻ x : ℤ,
        variationalNorm r (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
          ∂MeasureTheory.Measure.count) ∂volume)
      = ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
          variationalNorm r (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
          1 MeasureTheory.Measure.count ∂volume := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show (∫⁻ x : ℤ, variationalNorm r
        (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
        ∂MeasureTheory.Measure.count) = MeasureTheory.eLpNorm (fun x : ℤ =>
          variationalNorm r (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
          1 MeasureTheory.Measure.count
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun x => enorm_eq_self _)
  rw [hcongr]
  refine (lintegral_mono (fun t => hC t)).trans ?_
  rw [lintegral_const]
  by_cases htop : C = ⊤
  · rw [htop]; simp
  · have hvol : (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)) Set.univ = ENNReal.ofReal (1 / 2) := by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_uIoc]
      norm_num
    rw [hvol]
    have h1 : ENNReal.ofReal (1 / 2) ≤ (1 : ENNReal) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    calc C * ENNReal.ofReal (1 / 2) ≤ C * 1 := mul_le_mul' le_rfl h1
      _ = C := mul_one C


/-! ## Infrastructure for the Rademacher--Menshov step

The paper's §7 proof of the small-scale model estimate applies the two-dimensional
Rademacher--Menshov inequality for bilinear forms to the family `n ↦ BtwistEx … (Tm …)(Tm …)`.
The bilinear form `BtwistEx` is defined by an iterated `tsum`; it is bilinear only on the
*submodule of bounded sequences* (`Work.KMTPlan.A6.BtwistEx_bilinear_of_bounded`), so the
Rademacher--Menshov inequality is run there.  This section provides the submodule, the
bilinearity on it, and the generic Rademacher--Menshov reduction. -/

/-! ## The absolute-constant Rademacher--Menshov reduction

`Work.Analysis.Variation.rademacher_menshov_bilinear_full` produces the Rademacher--Menshov
constant only *after* the bilinear form `B`, the measure and the ambient spaces.  In the assembly
below the constant must be uniform in `l₁, l₂, k₁, k₂` (the target's `C : ℝ≥0 → ℝ≥0` may only
depend on `Λ`), so we use the absolute-constant form
`Work.Analysis.Variation.rademacher_menshov_bilinear_abs` and derive the shape actually needed:
the `L¹` bound of the full truncated `V²`-norm of a bilinear family, in terms of a uniform bound
over all coefficient families of `ℓ^∞`-norm `≤ 1`. -/

/-! ## The window arithmetic and the support of the randomised bumps -/

/-- Beyond a `ρ`-dependent threshold, the window scale `uScale ρ L = ⌊2^{2ρL}⌋` dominates `L`. -/
theorem uScale_ge_self (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L → L ≤ Work.KMTAreas.A7.uScale ρ L := by
  refine ⟨Nat.ceil (4 / ρ ^ 2), fun L hL => ?_⟩
  have h16 : Nat.ceil (16 / (2 * ρ) ^ 2) ≤ L := by
    have h1 : (16 : ℝ) / (2 * ρ) ^ 2 = 4 / ρ ^ 2 := by
      field_simp
      ring
    rw [h1]; exact hL
  have h2 : (L : ℝ) ≤ (2 : ℝ) ^ ((2 * ρ) * (L : ℝ)) :=
    le_two_rpow_self_of_ceil (2 * ρ) (by positivity) L h16
  have h3 : (2 : ℝ) ^ ((2 * ρ) * (L : ℝ)) = (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by ring_nf
  rw [h3] at h2
  have hfl : (L : ℤ) ≤ ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := Int.le_floor.mpr h2
  have hnn : (0 : ℤ) ≤ ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    le_trans (by exact_mod_cast Nat.zero_le L) hfl
  have hcast : (Work.KMTAreas.A7.uScale ρ L : ℤ) = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := by
    have hval : Work.KMTAreas.A7.uScale ρ L
        = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat := by
      simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount,
        Nat.cast_one, one_mul]
    rw [hval]
    exact Int.toNat_of_nonneg hnn
  have hz : (L : ℤ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℤ) := by rw [hcast]; exact hfl
  exact_mod_cast hz

/-- **The support of the randomised `f`-side symbol.**  On the small-scale index set with
`lcL ≥ B(ρ, C₀)`, the randomised family `randSymb (lowSymbF …)` is supported in the tiny arc
`|ξ| ≤ 2^{-3u}`, `u = uScale ρ L`: a nonzero value of the randomised sum forces one of the bumps
`varphiNt (⌊a n⌋) k₁ t` to be nonzero, and the arithmetic input
`Work.KMTPlan.A6.varphiNt_support_lowSmall` gives `k₁ + 3u ≤ Log N`. -/
theorem lowSymbF_support (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8) :
    ∃ B : ℕ, ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ε : ℕ → ℂ) (K : ℕ),
      B ≤ lcL l₁ l₂ k₁ k₂ →
      ∀ ξ : ℝ, Work.KMTAreas.A7.randSymb (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))) := by
  obtain ⟨B, hB⟩ := varphiNt_support_lowSmall ρ hρ C₀ hC₀ hρC₀
  refine ⟨B, fun a l₁ l₂ k₁ k₂ t ε K hBL ξ hξ => ?_⟩
  obtain ⟨n, _hnK, hn⟩ := Work.KMTPlan.A6.exists_ne_zero_of_randSymb_ne_zero hξ
  simp only [lowSymbF] at hn
  by_cases hn0 : n = 0
  · rw [if_pos hn0] at hn; exact absurd rfl hn
  · rw [if_neg hn0] at hn
    by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · rw [if_pos hls] at hn
      have hsupp := varphiNt_support_all (Nat.floor (a n)) k₁ t ξ hn
      have harith := hB l₁ l₂ k₁ k₂ (Nat.floor (a n)) hls.1 hls.2 hBL
      have hk1 : k₁ ≤ max k₁ k₂ := le_max_left _ _
      have hlog : ((k₁ : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)
          ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))) := by
        have h1 : (k₁ + 3 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)
            ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) :=
          le_trans (Nat.add_le_add_right hk1 _) harith
        have h2 : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
            = Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
          Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
        have h3 : ((k₁ + 3 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℕ) : ℤ)
            ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ) := by
          exact_mod_cast h1
        push_cast at h3
        rwa [h2] at h3
      have hgoal : (k₁ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)
          ≤ ((-(3 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) : ℤ) : ℝ) := by
        have h4 : (((k₁ : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ) : ℤ)
            : ℝ) ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by
          exact_mod_cast hlog
        push_cast at h4 ⊢
        linarith
      have hrf := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num : (1 : ℝ) ≤ 2) hgoal
      rw [Real.rpow_intCast] at hrf
      exact hsupp.trans hrf
    · rw [if_neg hls] at hn; exact absurd rfl hn

/-- **The support of the randomised `g`-side symbol** (the `d`-rescaled analogue of
`lowSymbF_support`). -/
theorem lowSymbG_supportSharp (P : ℤ[X]) (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8) :
    ∃ B : ℕ, ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ε : ℕ → ℂ) (K : ℕ),
      B ≤ lcL l₁ l₂ k₁ k₂ →
      ∀ ξ : ℝ, Work.KMTAreas.A7.randSymb (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) *
          (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))) := by
  obtain ⟨B, hB⟩ := varphiNt_support_lowSmall ρ hρ C₀ hC₀ hρC₀
  refine ⟨B, fun a l₁ l₂ k₁ k₂ t ε K hBL ξ hξ => ?_⟩
  obtain ⟨n, _hnK, hn⟩ := Work.KMTPlan.A6.exists_ne_zero_of_randSymb_ne_zero hξ
  simp only [lowSymbG] at hn
  by_cases hn0 : n = 0
  · rw [if_pos hn0] at hn; exact absurd rfl hn
  · rw [if_neg hn0] at hn
    by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · rw [if_pos hls] at hn
      have hsupp := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree
        (Nat.floor (a n)) k₂ t ξ hn
      have harith := hB l₁ l₂ k₁ k₂ (Nat.floor (a n)) hls.1 hls.2 hBL
      have hk2 : k₂ ≤ max k₁ k₂ := le_max_right _ _
      have hlog : ((k₂ : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)
          ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))) := by
        have h1 : (k₂ + 3 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)
            ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) :=
          le_trans (Nat.add_le_add_right hk2 _) harith
        have h2 : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
            = Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
          Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
        have h3 : ((k₂ + 3 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℕ) : ℤ)
            ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ) := by
          exact_mod_cast h1
        push_cast at h3
        rwa [h2] at h3
      have h6 : (k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))
          ≤ -(3 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) := by
        linarith [hlog]
      have h7 : (P.natDegree : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))
          ≤ (P.natDegree : ℤ) * (-(3 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      have h8 : (P.natDegree : ℤ) * (-(3 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))
          = -(3 * (P.natDegree : ℤ) *
            (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) := by ring
      rw [h8] at h7
      have hgoal : (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN
            (Nat.floor (a n)) : ℝ))
          ≤ ((-(3 * (P.natDegree : ℤ) *
            (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) : ℤ) : ℝ) := by
        exact_mod_cast h7
      have hrf := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num : (1 : ℝ) ≤ 2) hgoal
      rw [Real.rpow_intCast] at hrf
      exact hsupp.trans hrf
    · rw [if_neg hls] at hn; exact absurd rfl hn

/-! ## The `ℓ²` bound of `Tm` through the sup norm of its symbol -/

theorem Tm_l2_le_sup_symbol (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hcont : Continuous (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize φ)))
    (h : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ) ξ‖ ≤ C)
    (f : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l φ f) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  have hMem : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.KMTAreas.A7.diffFreqs ρ l) (Work.Analysis.IonescuWainger.periodize φ)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    MeasureTheory.MemLp.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall h)
  exact Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound (Work.KMTAreas.A7.diffFreqs ρ l)
    (Work.Analysis.IonescuWainger.periodize φ) C hC h hMem f hf

theorem not_lowSmallSet_of_lt (ρ : ℝ) (C₀ : ℕ) (D : ℝ) (hD : 0 < D) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ n : ℕ)
    (hD' : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
      (n : ℝ) + 1 ≤ D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (hn : lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) < n) :
    ¬ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n := by
  intro hls
  have h1 := hD' hls
  have h2 : (n : ℝ) < D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) + 1 := by
    linarith [h1]
  have h3 : (n : ℝ) < (Nat.ceil (D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
      : ℝ) + 1 := lt_of_lt_of_le h2 (by
        have := Nat.le_ceil (D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
        push_cast
        linarith)
  have h5 : n < Nat.ceil (D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂))) + 1 := by
    exact_mod_cast h3
  simp only [lowTrunc] at hn
  omega

/-- The anchored slice is the formula-definition of `lowModelSlice` at index `0`. -/
theorem lowSliceA_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) (x : ℤ) :
    lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x = 0 := by
  simp only [lowSliceA, lowSymbF_zero, lowSymbG_zero, Tm_zero ρ l₁ f hf, Tm_zero ρ l₂ g hg]
  exact congrFun (BtwistEx_zero_zero ρ P l₁ l₂ _ _ (cw_mStarF_summable _)
    (cw_mStargF_summable _ _)) x

theorem lowSliceA_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ k : ℕ) (t : ℝ)
    (hnot : ¬ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) (x : ℤ) :
    lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x = 0 := by
  have h1 : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
    funext ξ
    by_cases hk : k = 0
    · simp [lowSymbF, hk]
    · simp [lowSymbF, hk, hnot]
  have h2 : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
    funext ξ
    by_cases hk : k = 0
    · simp [lowSymbG, hk]
    · simp [lowSymbG, hk, hnot]
  simp only [lowSliceA, h1, h2, Tm_zero ρ l₁ f hf, Tm_zero ρ l₂ g hg]
  exact congrFun (BtwistEx_zero_zero ρ P l₁ l₂ _ _ (cw_mStarF_summable _)
    (cw_mStargF_summable _ _)) x

/-- **The comparison of the model slice family with its anchored version.**  The `n = 0` term of
the slice family need not vanish; splitting it off costs `2‖slice 0‖` and leaves the anchored
family, which is the family to which the Rademacher--Menshov reduction applies. -/
theorem variationalNorm_lowModelSlice_le_Vr (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (r : NNReal) (hr : 2 ≤ r) (D : ℝ) (hD : 0 < D)
    (hDbound : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
      (n : ℝ) + 1 ≤ D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
      ≤ Work.Analysis.Variation.VrFull 2 (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1)
          (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x)
        + 2 * ENNReal.ofReal ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖ := by
  have hshift := Work.KMTPlan.A6.variationalNorm_le_of_shift r
    (le_trans (by norm_num : (1 : NNReal) ≤ 2) hr)
    (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
    (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x)
    (lowSliceA_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ t hf hg x)
    (fun n hn => by
      have h0 : n ≠ 0 := by omega
      by_cases h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
      · have h1 : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n
            = Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t := by
          funext ξ; simp [lowSymbF, h0, h]
        have h2 : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n
            = Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t := by
          funext ξ; simp [lowSymbG, h0, h]
        rw [lowSliceA, h1, h2]
        simp only [lowModelSlice, h, if_true]
      · have h1 : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n = 0 := by
          funext ξ; simp [lowSymbF, h0, h]
        have h2 : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n = 0 := by
          funext ξ; simp [lowSymbG, h0, h]
        rw [lowSliceA, h1, h2, lowModelSlice, if_neg h,
          Tm_zero ρ l₁ f hf, Tm_zero ρ l₂ g hg]
        exact (congrFun (BtwistEx_zero_zero ρ P l₁ l₂ _ _ (cw_mStarF_summable _)
          (cw_mStargF_summable _ _)) x).symm)
  refine hshift.trans (add_le_add ?_ le_rfl)
  exact Work.KMTPlan.A6.variationalNorm_le_VrFull hr (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂))
    (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x)
    (fun k hk => lowSliceA_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ k t
      (not_lowSmallSet_of_lt ρ C₀ D hD a l₁ l₂ k₁ k₂ k (hDbound k) hk) hf hg x)

/-- **The `t`-integral step.**  A uniform-in-`t` bound on the `ℓ¹(ℤ)` norm of the variational norm
of the slice family gives the bound for the model tuple itself (Minkowski in `t` + Tonelli, via
`Work.KMTAreas.A7.variationalNorm_intervalIntegral_eLpNorm_le`). -/
theorem eLpNorm_variationalNorm_lowModel_le (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (r : NNReal) (hr : 1 ≤ r) (C : ℝ≥0∞)
    (hX : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℤ =>
      lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ p.1 n p.2)
      (MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.Measure.count))
    (h : ∀ t ∈ Set.Icc ((1 : ℝ) / 2) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
      1 MeasureTheory.Measure.count ≤ C) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      1 MeasureTheory.Measure.count ≤ C := by
  have h1 : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∫ t in ((1 : ℝ) / 2)..1,
          lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x) := by
    funext x
    congr 1
    funext n
    exact lowModel_eq_integral_slice ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
  rw [h1]
  exact Work.KMTAreas.A7.variationalNorm_intervalIntegral_eLpNorm_le r hr 1 (by norm_num)
    (fun t n x => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x) C hX h

/-! ## The absorption of the Rademacher--Menshov loss into the gain -/

/-- **The Rademacher--Menshov loss is absorbed by the gain.**  Since the window scale is
`uScale ρ L = ⌊2^{2ρL}⌋`, the loss `(log₂ K + 2)²` is `≲ 2^{4ρL}`; for `ρ` small (namely
`4ρ ≤ c - c'`) this is dominated by the gain `2^{-cL}`, leaving the weaker gain `2^{-c'L}`. -/
theorem two_rpow_absorb (c c' ρ : ℝ) (hcc : 4 * ρ ≤ c - c') (L : ℕ) :
    (2 : ℝ) ^ (4 * ρ * (L : ℝ)) * (2 : ℝ) ^ (-(c * (L : ℝ)))
      ≤ (2 : ℝ) ^ (-(c' * (L : ℝ))) := by
  rw [Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num),
    Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num),
    Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num), ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h1 : (4 * ρ * (L : ℝ)) * Real.log 2 + (-(c * (L : ℝ))) * Real.log 2
      = (4 * ρ - c) * ((L : ℝ) * Real.log 2) := by ring
  have h2 : (-(c' * (L : ℝ))) * Real.log 2 = (-c') * ((L : ℝ) * Real.log 2) := by ring
  have h3 : (4 * ρ - c) * ((L : ℝ) * Real.log 2) ≤ (-c') * ((L : ℝ) * Real.log 2) :=
    mul_le_mul_of_nonneg_right (by linarith : 4 * ρ - c ≤ -c') (mul_nonneg hL hlog.le)
  linarith [h1, h2, h3]

theorem two_rpow_absorb_mul (M c c' ρ : ℝ) (hM : 0 ≤ M) (hcc : 4 * ρ ≤ c - c') (L : ℕ) :
    M * ((2 : ℝ) ^ (4 * ρ * (L : ℝ)) * (2 : ℝ) ^ (-(c * (L : ℝ))))
      ≤ M * (2 : ℝ) ^ (-(c' * (L : ℝ))) :=
  mul_le_mul_of_nonneg_left (two_rpow_absorb c c' ρ hcc L) hM

/-- **The window arithmetic.**  Beyond a `ρ`-dependent threshold, the window scale
`uScale ρ L = ⌊2^{2ρL}⌋` dominates both `L` and `2^{ρL}`.  These are the two arithmetic inputs that
let `ssuBtwistEx` be applied with `u := uScale ρ (lcL …)` in the small-scale assembly. -/
theorem uScale_window_arith (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L →
      (L : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) ∧
      (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
  obtain ⟨B₁, hB₁⟩ := uScale_ge_self ρ hρ
  refine ⟨max B₁ (Nat.ceil (1 / ρ) + 2), fun L hL => ?_⟩
  have hL₁ : B₁ ≤ L := le_trans (le_max_left _ _) hL
  have hceil : Nat.ceil (1 / ρ) + 1 ≤ L := by
    have := le_trans (le_max_right _ _) hL
    omega
  have hLpos : (1 : ℝ) ≤ ρ * (L : ℝ) := by
    have h1 : (1 : ℝ) / ρ ≤ (L : ℝ) := by
      have h2 : (((Nat.ceil (1 / ρ) + 1 : ℕ)) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hceil
      have h3 : (1 : ℝ) / ρ ≤ ((Nat.ceil (1 / ρ) : ℕ) : ℝ) := Nat.le_ceil _
      push_cast at h2
      linarith
    calc (1 : ℝ) = ρ * (1 / ρ) := by field_simp
      _ ≤ ρ * (L : ℝ) := mul_le_mul_of_nonneg_left h1 hρ.le
  refine ⟨by exact_mod_cast hB₁ L hL₁, ?_⟩
  set y : ℝ := (2 : ℝ) ^ (ρ * (L : ℝ)) with hy
  have hy2 : (2 : ℝ) ≤ y := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num : (1 : ℝ) ≤ 2) hLpos
    simpa [hy] using h
  have hsq : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) = y ^ (2 : ℝ) := by
    rw [hy, show (2 : ℝ) * ρ * (L : ℝ) = (ρ * (L : ℝ)) * 2 by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hfl : (Work.KMTAreas.A7.uScale ρ L : ℝ) = (⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ : ℝ) := by
    have hval : Work.KMTAreas.A7.uScale ρ L
        = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat := by
      simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Nat.cast_one, one_mul]
    have hnn : (0 : ℤ) ≤ ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := by
      refine Int.le_floor.mpr ?_
      push_cast
      positivity
    rw [hval]
    exact_mod_cast (Int.toNat_of_nonneg hnn)
  rw [hfl, hsq]
  have h1 : y ≤ y ^ (2 : ℝ) - 1 := by
    rw [Real.rpow_two]
    nlinarith [hy2]
  have h2 : y ^ (2 : ℝ) - 1 < (⌊y ^ (2 : ℝ)⌋ : ℝ) := by
    have := Int.lt_floor_add_one (y ^ (2 : ℝ))
    linarith
  linarith

/-- **The randomised single-scale bound, from `ssuBtwistEx` plus `tmRandSymb_l2`.**  In Case A
(`lcL … = max l₁ l₂`) the paper's `ssu` and the `ℓ²`-bound for the randomised cut-offs give the
bound `LowRandBound` needed by the per-`t` assembly; the support conditions of the two randomised
symbols and the two `ℓ²`-bounds are hypotheses (they are
`lowSymbF_support`/`lowSymbG_supportSharp`/`tmRandSymb_l2` in the caller). -/
theorem lowRandBound_of_ssu (P : ℤ[X]) (C₀ : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ (Λ : ℝ≥0) (c : ℝ) (hc : 0 < c) (Cssu : ℝ) (hCssu : 0 ≤ Cssu)
      (Ctm : ℝ≥0 → ℝ≥0) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (D : ℝ),
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      lcL l₁ l₂ k₁ k₂ = max l₁ l₂ →
      B ≤ lcL l₁ l₂ k₁ k₂ →
      (∀ (m₁ m₂ u : ℕ) (φ ψ : ℝ → ℂ) (f' g' : ℤ → ℂ),
        (max m₁ m₂ : ℝ) ≤ (u : ℝ) → (2 : ℝ) ^ (ρ * (max m₁ m₂ : ℝ)) ≤ (u : ℝ) →
        MeasureTheory.MemLp f' 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g' 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
          Work.Analysis.IonescuWainger.circleMeasure →
        MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize ψ) ⊤
          Work.Analysis.IonescuWainger.circleMeasure →
        (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) →
        (∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) →
        MeasureTheory.eLpNorm (fun x : ℤ => BtwistEx ρ P m₁ m₂
            (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
            (Work.KMTAreas.A7.Tm ρ m₁ φ f') (Work.KMTAreas.A7.Tm ρ m₂ ψ g') x)
          1 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(c * (max m₁ m₂ : ℝ))))
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ m₁ φ f') 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ m₂ ψ g') 2 MeasureTheory.Measure.count) →
      (∀ (ε : ℕ → ℂ) (K : ℕ) (ξ : ℝ),
        Work.KMTAreas.A7.randSymb (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))) →
      (∀ (ε : ℕ → ℂ) (K : ℕ) (ξ : ℝ),
        Work.KMTAreas.A7.randSymb (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ)
          * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))) →
      (∀ (ε : ℕ → ℂ), (∀ n, ‖ε n‖ ≤ 1) →
        MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.randSymb
            (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1)) f)
          2 MeasureTheory.Measure.count
          ≤ (Ctm Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) →
      (∀ (ε : ℕ → ℂ), (∀ n, ‖ε n‖ ≤ 1) →
        MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.randSymb
            (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1)) g)
          2 MeasureTheory.Measure.count
          ≤ (Ctm Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) →
      LowRandBound ρ P C₀ a f g l₁ l₂ k₁ k₂ t D
        (ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(c * (max l₁ l₂ : ℝ))))
          * (((Ctm Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
            * ((Ctm Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))) := by
  obtain ⟨B, hB⟩ := uScale_window_arith ρ hρ
  refine ⟨B, fun Λ c hc Cssu hCssu Ctm a f g l₁ l₂ k₁ k₂ t D hf hg hcaseA hBL
    hssu hsep₁ hsep₂ htm₁ htm₂ => ?_⟩
  intro ε ε' hε hε'
  have hwin := hB (lcL l₁ l₂ k₁ k₂) hBL
  have hm1 : max ((l₁ : ℝ)) ((l₂ : ℝ))
      ≤ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℝ) := by
    have h : ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)
        ≤ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℝ) := hwin.1
    rw [hcaseA, Nat.cast_max] at h
    rw [hcaseA]; exact h
  have hm2 : (2 : ℝ) ^ (ρ * max ((l₁ : ℝ)) ((l₂ : ℝ)))
      ≤ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℝ) := by
    have h : (2 : ℝ) ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
        ≤ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℝ) := hwin.2
    rw [hcaseA, Nat.cast_max] at h
    rw [hcaseA]; exact h
  have hmain := hssu l₁ l₂ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂))
    (Work.KMTAreas.A7.randSymb (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε
      (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1))
    (Work.KMTAreas.A7.randSymb (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε'
      (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1))
    f g hm1 hm2 hf hg
    ((Work.KMTPlan.A6.memLp_periodize_randSymb_lowSymb ρ P C₀ a l₁ l₂ k₁ k₂
      (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1) t ε).1)
    ((Work.KMTPlan.A6.memLp_periodize_randSymb_lowSymb ρ P C₀ a l₁ l₂ k₁ k₂
      (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1) t ε').2)
    (hsep₁ ε _) (hsep₂ ε' _)
  refine hmain.trans ?_
  have hF := htm₁ ε hε
  have hG := htm₂ ε' hε'
  calc ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(c * (max l₁ l₂ : ℝ))))
        * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.randSymb
            (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1)) f)
          2 MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.randSymb
            (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1)) g)
          2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(c * (max l₁ l₂ : ℝ))))
        * ((Ctm Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
        * ((Ctm Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hF bot_le) hG bot_le bot_le
      _ = _ := by ring

/-! ## The target

The proof of the target theorem is the paper's §7 route:

1. `lowModel` is the `t`-integral of its slices (`lowModel_eq_integral_slice`), so the
   pointwise Minkowski inequality in `t` (`varNorm_lowModel_le`) and Tonelli in `ℓ¹(ℤ)`
   reduce the target to a *uniform in* `t ∈ [1/2,1]` bound on the variational norm of the
   single-scale slice family `n ↦ lowModelSlice ... t n x`.
2. For fixed `t` the family is `n ↦ BtwistEx ρ P l₁ l₂ m_* m_*' (u n) (v n)` with
   `u n = Tm ρ l₁ (varphiNt (⌊a n⌋) k₁ t) f` (and the `g`-side analogue), so the family only
   lives on the lacunary scales `n ≤ K := lowIndexBound Λ (splitCut ρ L)`
   (`lowSmallSet_le_log`, `lacunaryScaleBound`); the two-dimensional Rademacher--Menshov
   inequality for bilinear forms (`rademacher_menshov_bilinear_full`, proved in
   `Work.Analysis.Variation`, instantiated at `q = 1`, loss `(log₂ K + 2)²`) bounds the
   variational norm over `n` by the supremum over the *randomised differences*
   `∑_{k<K} ε k (u (k+1) - u k)`, which by the linearity of `Tm` in its symbol
   (`Tm_add_of_memLp`) is `Tm ρ l₁ (randSymb … ) f`.
3. The single-scale bound for the randomised symbols is `Work.KMTPlan.A6.ssuBtwistEx` (the
   paper's Lemma `ssu` at the exact-height model operator, with the gain `2^{-c max(l₁,l₂)}`),
   and the `ℓ²`-norms of the two randomised packets are controlled by
   `Work.KMTPlan.A6.tmRandSymb_l2`; the non-degeneracy hypotheses of `ssuBtwistEx`
   (`|ξ| ≤ 2^{-3u}` for the two symbols, and `u ≥ 2^{ρ max l}`) follow on `lowSmallSet` from
   `inIndexSet` (`Log N ≥ 2^{L/C₀}`) together with the support lemma
   `Work.KMTAreas.A7.varphiNt_support_le` and `u = uScale ρ L ≫ 2^{ρ L}`.
4. The absorption of the Rademacher--Menshov loss `(log₂ K + 2)² ≤ 2^{O(ρL)}` into the gain
   `2^{-cL}` uses `ρ ≤ ρ₀` with `ρ₀` small (the quantifier order of the contract, `C₀` before
   `ρ`, is what makes this legal), and the case `max k₁ k₂ > max l₁ l₂` (which requires the
   extra decay `2^{-c max k}` from the integration-by-parts identity `MdlBumpIntegIdent`/`I`)
   is handled by the same reduction with the modified bumps of `A6/MdlDefs.lean`.
-/

/-! ## Measurability of the slice family

`eLpNorm_variationalNorm_lowModel_le_of_uniform` (and `lowModelVar_boundedL`) need the joint
a.e.-measurability of `(t,x) ↦ lowModelSlice … t n x` for the product of Lebesgue measure on `ℝ`
and counting measure on `ℤ`.  By `aemeasurable_prod_count_iff` this is the *slicewise*
a.e.-measurability of `t ↦ lowModelSlice … t n x`, which is supplied by
`Work.KMTPlan.A6.sliceAEMeasurable` (the `if lowSmallSet` guard does not depend on `t` or `x`). -/

/-- **Joint a.e.-measurability of the `t`-slices of `lowModel`.** -/
theorem lowModelSlice_aemeasurable (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℤ =>
      lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ p.1 n p.2)
      (MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.Measure.count) := by
  intro n
  refine (aemeasurable_prod_count_iff
    (fun t : ℝ => fun x : ℤ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)).mpr ?_
  intro x
  by_cases h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
  · have hred : (fun t : ℝ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
        = (fun t : ℝ => BtwistEx ρ P l₁ l₂
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
            (Work.KMTAreas.A7.mStargF P.natDegree
              (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tm ρ l₁
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f)
            (Work.KMTAreas.A7.Tm ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x) := by
      funext t
      simp only [lowModelSlice, h, if_true]
    rw [hred]
    exact sliceAEMeasurable ρ P l₁ l₂ k₁ k₂ _ _ (Nat.floor (a n)) f g x
  · have hred : (fun t : ℝ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
        = fun _ : ℝ => (0 : ℂ) := by
      funext t
      simp only [lowModelSlice, h, if_false]
    rw [hred]
    exact aemeasurable_const

/-! ## The `ℓ²` bound for `Tm` on narrow symbols (the two `ℓ²`-factors of the spike)

The spike of the small-scale assembly is `lowModelSlice … t 0`, i.e. the single-scale model
expression at `n = 0`; `slice_le_of_VrBoundA` bounds its contribution to the variational norm by
`2‖lowModelSlice … t 0 x‖`, and the `ℓ¹`-norm of that term is bounded by `SSUShape` applied at the
single scale `n = 0`, whose right-hand side still carries the two factors
`‖Tm ρ lᵢ (…bump…) f‖₂`.  Those are bounded by `2‖f‖₂` with the lemma below: the bump
`φ_{N,t}` is supported at scale `2^{k-⌊log₂N⌋} ≤ 2^{-3u}` (the *sharp* support condition
`varphiNt_support_lowSmall`), so its periodisation is supported in the arc `ℝ_{≤-3u}` on which the
exact-height frequencies `diffFreqs ρ l` are non-aliasing (`nonAliasing_diffFreqs`), and
`iwSymbolSet_narrow_bound` collapses the symbol sum to a single term of sup norm `≤ 2`. -/

/-- **The `ℓ²` bound for `Tm` on a narrow symbol.**  If `ψ` has a continuous `1`-periodisation
supported in the arc of scale `2^{-3u}` (`u = uScale ρ L`) and of sup norm `≤ C`, and the
exact-height frequencies `diffFreqs ρ l` are non-aliasing at that scale, then
`‖Tm ρ l ψ f‖₂ ≤ C‖f‖₂`. -/
theorem tm_narrow_l2_le (ρ : ℝ) (l L : ℕ) {ψ : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hNA : Work.Analysis.IonescuWainger.NonAliasing
      (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) (Work.KMTAreas.A7.diffFreqs ρ l))
    (hcontper : Continuous (Work.Analysis.IonescuWainger.periodize ψ))
    (hper : Work.Analysis.IonescuWainger.SupportedInArc
      (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)))
      (Work.Analysis.IonescuWainger.periodize ψ))
    (hsup : ∀ x : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.periodize ψ x‖ ≤ C)
    (f : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l ψ f) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  have hcont : Continuous (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize ψ) ξ) := by
    simp only [Work.Analysis.IonescuWainger.iwSymbolSet]
    exact continuous_finsetSum _ fun α _ =>
      hcontper.comp (continuous_id.sub continuous_const)
  refine Tm_l2_le_sup_symbol ρ l ψ C hC hcont ?_ f hf
  intro ξ
  exact iwSymbolSet_narrow_bound ρ l (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)))
    (Work.Analysis.IonescuWainger.periodize ψ) C hC hsup hper hNA ξ

/-- **The narrow-symbol data of the bump `φ_{N,t}`.**  On the sharp support condition
`k + 3u ≤ ⌊log₂N⌋` (`u = uScale ρ L`), the bump `φ_{N,t}` is supported in the arc `ℝ_{≤-3u}`, its
periodisation is continuous and supported in that arc, and its sup norm is `≤ 2`.  These are
exactly the hypotheses of `tm_narrow_l2_le`. -/
theorem varphiNt_narrow_data (ρ : ℝ) (L N k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hu : 1 ≤ Work.KMTAreas.A7.uScale ρ L)
    (hku : k + 3 * Work.KMTAreas.A7.uScale ρ L ≤ (Work.Analysis.EndVar.logN N).toNat) :
    (∀ ξ : ℝ, Work.KMTAreas.A7.varphiNt N k t ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)))) ∧
    Continuous (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t)) ∧
    Work.Analysis.IonescuWainger.SupportedInArc
      (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)))
      (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t)) ∧
    (∀ x : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t) x‖ ≤ 2) := by
  have hz : (0 : ℤ) ≤ Work.Analysis.EndVar.logN N := Work.Analysis.EndVar.logN_nonneg N
  have hcast : (((Work.Analysis.EndVar.logN N).toNat : ℕ) : ℤ) = Work.Analysis.EndVar.logN N :=
    Int.toNat_of_nonneg hz
  have hkr : (k : ℝ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    have hint : ((k : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))
        ≤ Work.Analysis.EndVar.logN N := by
      have hcast' : ((k + 3 * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℤ)
          ≤ (((Work.Analysis.EndVar.logN N).toNat : ℕ) : ℤ) := by exact_mod_cast hku
      push_cast at hcast'
      rw [hcast] at hcast'
      exact hcast'
    have hreal := (show (((k : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℤ) : ℤ) : ℝ)
        ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) from by exact_mod_cast hint)
    push_cast at hreal
    linarith
  -- the sharp support of the bump
  have hsupp : ∀ ξ : ℝ, Work.KMTAreas.A7.varphiNt N k t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
    intro ξ hξ
    have h1 := varphiNt_support_all N k t ξ hξ
    have h3 : (k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)
        ≤ ((-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)) : ℤ) : ℝ) := by
      push_cast
      linarith
    calc |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := h1
      _ ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
          rw [← Real.rpow_intCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
  -- membership in the arc
  have harc : ∀ x : ℝ, |x| ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) →
      x ∈ Work.Analysis.IonescuWainger.realArc (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
    intro x hx
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  obtain ⟨R, S, hS, hb⟩ := Work.KMTAreas.A7.varphiNt_bounds N k
  refine ⟨hsupp, ?_, ?_, ?_⟩
  · exact continuous_periodize_of_hasCompactSupport _
      (hb t ht).2.1.continuous (hb t ht).2.2.1
  · exact supportedInArc_periodize_of_support _ hu _ (fun ξ hξ => hsupp ξ hξ)
  · have h2 : (2 : ℝ) ^ ((-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) + 1) < 1 := by
      rw [← Real.rpow_intCast]
      have hz : ((-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)) + 1 : ℤ) : ℝ) ≤ (-2 : ℝ) := by
        have h3 : (3 : ℤ) ≤ 3 * (Work.KMTAreas.A7.uScale ρ L : ℤ) := by
          have : (1 : ℤ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℤ) := by exact_mod_cast hu
          linarith
        have hz' : (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)) + 1 : ℤ) ≤ (-2 : ℤ) := by linarith
        exact_mod_cast hz'
      calc (2 : ℝ) ^ (((-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) + 1 : ℤ) : ℝ)
          ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hz
        _ = 1 / 4 := by norm_num
        _ < 1 := by norm_num
    refine Work.Analysis.IWMultiplier.periodize_norm_le h2 (fun x hx => harc x (hsupp x hx))
      (fun x => ?_)
    rw [Work.KMTAreas.A7.varphiNt, norm_mul, norm_ee, mul_one]
    exact norm_varphiN_le_two N k x

/-- `‖φ̃_N(ξ)‖ ≤ 2`: the bump `φ̃_N` is a difference of two rescaled `η`'s (the `d`-fold
rescaled analogue of `norm_varphiN_le_two`, proved here because the module that holds the existing
version is not imported). -/
theorem norm_varphitildeN_le_two' (d N k : ℕ) (x : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeN d N k x‖ ≤ 2 := by
  rw [Work.KMTAreas.A7.varphitildeN]
  split_ifs with hk
  · exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · refine le_trans (norm_sub_le _ _) ?_
    have h1 := Work.KMTContract.norm_kmtEta_le
      ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * x)
    have h2 := Work.KMTContract.norm_kmtEta_le
      ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * x)
    linarith

/-- **The narrow-symbol data of the bump `φ̃_{N,t}`** (the `g`-side twin of
`varphiNt_narrow_data`).  On the sharp support condition `k₂ + 3u ≤ ⌊log₂N⌋`
(`u = uScale ρ L`), the bump `φ̃_{N,t}` is supported in the arc `ℝ_{≤-3du}` (`d = P.natDegree`),
its periodisation is continuous and supported in that arc, and its sup norm is `≤ 2`. -/
theorem varphitildeNt_narrow_data (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    (ρ : ℝ) (L N k₂ : ℕ) (t : ℝ)
    (hu : 1 ≤ Work.KMTAreas.A7.uScale ρ L)
    (hku : k₂ + 3 * Work.KMTAreas.A7.uScale ρ L ≤ (Work.Analysis.EndVar.logN N).toNat) :
    (∀ ξ : ℝ, Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ)))) ∧
    Continuous (Work.Analysis.IonescuWainger.periodize
      (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) ∧
    Work.Analysis.IonescuWainger.SupportedInArc
      (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ)))
      (Work.Analysis.IonescuWainger.periodize
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) ∧
    (∀ x : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.periodize
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) x‖ ≤ 2) := by
  have hz : (0 : ℤ) ≤ Work.Analysis.EndVar.logN N := Work.Analysis.EndVar.logN_nonneg N
  have hcast : (((Work.Analysis.EndVar.logN N).toNat : ℕ) : ℤ) = Work.Analysis.EndVar.logN N :=
    Int.toNat_of_nonneg hz
  have hkr : (k₂ : ℝ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ)
      ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    have hint : ((k₂ : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))
        ≤ Work.Analysis.EndVar.logN N := by
      have hcast' : ((k₂ + 3 * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℤ)
          ≤ (((Work.Analysis.EndVar.logN N).toNat : ℕ) : ℤ) := by exact_mod_cast hku
      push_cast at hcast'
      rw [hcast] at hcast'
      exact hcast'
    have hreal := (show (((k₂ : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℤ) : ℤ) : ℝ)
        ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) from by exact_mod_cast hint)
    push_cast at hreal
    linarith
  -- the sharp support of the bump
  have hsupp : ∀ ξ : ℝ, Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
    intro ξ hξ
    have h1 := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k₂ t ξ hξ
    have hd0 : (0 : ℝ) ≤ (P.natDegree : ℝ) := by positivity
    have hexp : (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
        ≤ ((-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ)) : ℤ) : ℝ) := by
      have h1' : (k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)
          ≤ -3 * (Work.KMTAreas.A7.uScale ρ L : ℝ) := by linarith
      have h2' := mul_le_mul_of_nonneg_left h1' hd0
      have h3' : (P.natDegree : ℝ) * (-3 * (Work.KMTAreas.A7.uScale ρ L : ℝ))
          = ((-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ)) : ℤ) : ℝ) := by
        push_cast; ring
      linarith [h2', h3']
    calc |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := h1
      _ ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
          rw [← Real.rpow_intCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  -- membership in the arc
  have harc : ∀ x : ℝ,
      |x| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) →
      x ∈ Work.Analysis.IonescuWainger.realArc
        (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) := by
    intro x hx
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  refine ⟨hsupp, ?_, ?_, ?_⟩
  · exact continuous_periodize_of_hasCompactSupport _
      (Work.KMTPlan.A6.contDiff_varphitildeNt_aux P P.natDegree N k₂ t).continuous
      (Work.KMTPlan.A6.hasCompactSupport_varphitildeNt_aux P P.natDegree N k₂ t)
  · exact supportedInArc_periodize_of_arc (fun x hx => harc x (hsupp x hx))
  · have h2 : (2 : ℝ) ^ ((-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) + 1) < 1 := by
      rw [← Real.rpow_intCast]
      have hzp : (((-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) + 1 : ℤ) : ℝ)
          ≤ (-2 : ℝ) := by
        have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
        have hu1 : (1 : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by exact_mod_cast hu
        push_cast
        nlinarith [hd1, hu1]
      calc (2 : ℝ) ^ (((-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ L : ℤ))) + 1 : ℤ) : ℝ)
          ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hzp
        _ = 1 / 4 := by norm_num
        _ < 1 := by norm_num
    refine Work.Analysis.IWMultiplier.periodize_norm_le h2 (fun x hx => harc x (hsupp x hx))
      (fun x => ?_)
    rw [Work.KMTAreas.A7.varphitildeNt, norm_mul, norm_ee, mul_one]
    exact norm_varphitildeN_le_two' P.natDegree N k₂ x

/-- `SupportedInArc` is monotone in the scale: a symbol supported in the smaller arc `ℝ_{≤k}` is
supported in any larger arc `ℝ_{≤k'}`.  (Used for the `g`-side bump, whose periodisation is
supported in `ℝ_{≤-3du} ⊆ ℝ_{≤-3u}`.) -/
theorem supportedInArc_mono {k k' : ℤ} (hkk : k ≤ k')
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (h : Work.Analysis.IonescuWainger.SupportedInArc k Φ) :
    Work.Analysis.IonescuWainger.SupportedInArc k' Φ := by
  intro ξ hξ
  obtain ⟨θ, hθ, hθξ⟩ := h ξ hξ
  have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k' := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hkk)
  exact ⟨θ, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, hθξ⟩

/-- **The spike bound.**  At the anchor `n = 0` the slice is the single-scale model expression
`BtwistEx_{m_*}(T^{l₁}_{φ_{N,t}}f, T^{l₂}_{φ̃_{N,t}}g)` (`N = ⌊a 0⌋`), so `SSUShape` applied at the
single scale `u = uScale ρ (lcL l₁ l₂ k₁ k₂)` bounds its `ℓ¹`-norm with the gain
`2^{-cS·max(l₁,l₂)}`; on the sharp support condition `max k₁ k₂ + 3u ≤ ⌊log₂N⌋` (proved for the
admissible scales by `varphiNt_support_lowSmall`) the two `ℓ²`-factors are bounded by `2‖f‖₂`,
`2‖g‖₂` with `tm_narrow_l2_le` and the two narrow-symbol data lemmas. -/
theorem lowSpike_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (ρ : ℝ) (hρ : 0 < ρ) (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8)
    {cS : ℝ} (hcS : 0 < cS) {Cssu : NNReal}
    (hSS : SSUBodyAtLinf P cS Cssu ρ) :
    ∃ B : ℕ, ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      B ≤ lcL l₁ l₂ k₁ k₂ → lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0 →
      ∀ (f g : ℤ → ℂ), MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
            ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
          1 MeasureTheory.Measure.count
          ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
              * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
              * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
  obtain ⟨Bna, hBna⟩ := nonAliasing_diffFreqs ρ hρ
  obtain ⟨Bsp, hBsp⟩ := varphiNt_support_lowSmall ρ hρ C₀ hC₀ hρC₀
  obtain ⟨Bw, hBw⟩ := uScale_window_arith ρ hρ
  refine ⟨max (max Bna Bsp) Bw, ?_⟩
  intro a l₁ l₂ k₁ k₂ t ht hBL hset f g hf hg
  set L : ℕ := lcL l₁ l₂ k₁ k₂ with hLdef
  set u : ℕ := Work.KMTAreas.A7.uScale ρ L with hudef
  have hnaL : Bna ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hBL
  have hspL : Bsp ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hBL
  have hwL : Bw ≤ L := le_trans (le_max_right _ _) hBL
  have hl₁L : l₁ ≤ L := le_trans (le_max_left l₁ l₂) (le_max_left _ _)
  have hl₂L : l₂ ≤ L := le_trans (le_max_right l₁ l₂) (le_max_left _ _)
  obtain ⟨huL, hu2⟩ := hBw L hwL
  -- `u ≥ 1`
  have hu1 : 1 ≤ u := by
    have h1 : (1 : ℤ) ≤ ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := by
      refine Int.le_floor.mpr ?_
      push_cast
      exact Real.one_le_rpow (by norm_num) (by positivity)
    have h2 : u = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat := by
      simp only [hudef, Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount,
        Nat.cast_one, one_mul]
    have h3 : ((⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat : ℕ) : ℤ)
        = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
      Int.toNat_of_nonneg (le_trans (by norm_num) h1)
    rw [h2]
    omega
  -- the two arithmetic clauses of `SSUShape`
  have hmax1 : (max l₁ l₂ : ℝ) ≤ (u : ℝ) := by
    have h1 : (L : ℝ) ≤ (u : ℝ) := huL
    have h2 : (max l₁ l₂ : ℝ) ≤ (L : ℝ) := by
      have : max l₁ l₂ ≤ L := le_max_left _ _   -- hmm: `lcL = max (max l₁l₂) (max k₁k₂)`
      exact_mod_cast this
    linarith
  have hmax2 : (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (u : ℝ) := by
    have h2 : (max l₁ l₂ : ℝ) ≤ (L : ℝ) := by
      have : max l₁ l₂ ≤ L := le_max_left _ _
      exact_mod_cast this
    have h3 : ρ * (max l₁ l₂ : ℝ) ≤ ρ * (L : ℝ) := mul_le_mul_of_nonneg_left h2 hρ.le
    exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) h3) hu2
  -- the non-aliasing
  have hNA₁ : Work.Analysis.IonescuWainger.NonAliasing (-(3 * (u : ℤ)))
      (Work.KMTAreas.A7.diffFreqs ρ l₁) := hBna L l₁ hnaL hl₁L
  have hNA₂ : Work.Analysis.IonescuWainger.NonAliasing (-(3 * (u : ℤ)))
      (Work.KMTAreas.A7.diffFreqs ρ l₂) := hBna L l₂ hnaL hl₂L
  -- the sharp support at the anchor
  have hku : max k₁ k₂ + 3 * u ≤ (Work.Analysis.EndVar.logN (Nat.floor (a 0))).toNat :=
    hBsp l₁ l₂ k₁ k₂ (Nat.floor (a 0)) hset.1 hset.2 hspL
  have hku₁ : k₁ + 3 * u ≤ (Work.Analysis.EndVar.logN (Nat.floor (a 0))).toNat :=
    le_trans (by omega : k₁ + 3 * u ≤ max k₁ k₂ + 3 * u) hku
  have hku₂ : k₂ + 3 * u ≤ (Work.Analysis.EndVar.logN (Nat.floor (a 0))).toNat :=
    le_trans (by omega : k₂ + 3 * u ≤ max k₁ k₂ + 3 * u) hku
  -- the narrow-symbol data
  have hdF := varphiNt_narrow_data ρ L (Nat.floor (a 0)) k₁ t ht hu1 hku₁
  have hdG := varphitildeNt_narrow_data P (by omega) ρ L (Nat.floor (a 0)) k₂ t hu1 hku₂
  -- the two `ℓ²` bounds
  have hF2 : MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁
      (Work.KMTAreas.A7.varphiNt (Nat.floor (a 0)) k₁ t) f) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal 2 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
    tm_narrow_l2_le ρ l₁ L (C := 2) (by norm_num) hNA₁ hdF.2.1 hdF.2.2.1 hdF.2.2.2 f hf
  have hG2 : MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂
      (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a 0)) k₂ t) g)
      2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal 2 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
    tm_narrow_l2_le ρ l₂ L (C := 2) (by norm_num) hNA₂ hdG.2.1
      (supportedInArc_mono (by
        have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
          have : 1 ≤ P.natDegree := by omega
          exact_mod_cast this
        have hu1Z : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu1
        push_cast
        nlinarith [hd1, hu1Z]) hdG.2.2.1)
      hdG.2.2.2 g hg
  -- the single-scale estimate
  have hssu0 := hSS l₁ l₂ u _ _ f g hmax1 hmax2 hf hg
    (Work.KMTAreas.A7.kmtA7_memLp_periodize_varphiNt (Nat.floor (a 0)) k₁ t)
    (Work.KMTAreas.A7.kmtA7_memLp_periodize_varphitildeNt P P.natDegree
      (Nat.floor (a 0)) k₂ t)
    hdF.1 hdG.1
  -- reduce the slice to the anchored expression at `n = 0`
  have hred : (fun x : ℤ => ENNReal.ofReal
        ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
      = (fun x : ℤ => ‖BtwistEx ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a 0)) k₁ t) f)
          (Work.KMTAreas.A7.Tm ρ l₂
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a 0)) k₂ t) g) x‖ₑ) := by
    funext x
    have hx : lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x
        = BtwistEx ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a 0)) k₁ t) f)
          (Work.KMTAreas.A7.Tm ρ l₂
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a 0)) k₂ t) g) x := by
      simp only [lowModelSlice, hset, if_true, hudef, hLdef]
    rw [hx]
    exact ofReal_norm _
  rw [hred, eLpNorm_enorm (hf := MeasureTheory.AEStronglyMeasurable.of_discrete)]
  exact hssu0.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl le_rfl) hF2) hG2)

/-- **The joint between `SSUShape`/`lowSpike_le` and `lowRandBound_of_ssu`.**  The single-scale
estimate is available in the `(C : ENNReal) * ofReal x` form (that is the form in which `SSUShape`
and `lowSpike_le` are stated), while `lowRandBound_of_ssu` consumes the `ofReal (C * x)` form.
The two agree for `x ≥ 0`. -/
theorem coe_mul_ofReal_eq (C : NNReal) {x : ℝ} (hx : 0 ≤ x) :
    (C : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal ((C : ℝ) * x) := by
  rw [show ENNReal.ofReal ((C : ℝ) * x) = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal x from
      ENNReal.ofReal_mul (NNReal.coe_nonneg C),
    ENNReal.ofReal_coe_nnreal]

/-- **The Rademacher--Menshov data of the Case-A assembly, at a fixed `ρ`.**  This is the
`∃ C_RM, ∃ Ct, ∃ B` package that the Case-A assembly consumes.  It is produced by
`VrFull_TmBtwist_le_rand_abs` (the *absolute* Rademacher--Menshov constant), with the
randomised single-scale bound supplied by `lowRandBound_of_ssu`, whose seven hypotheses are
discharged from `hSS` (via `coe_mul_ofReal_eq`), the two supports
`lowSymbF_support`/`lowSymbG_supportSharp`, and the two `ℓ²`-bounds `hsupF`/`hsupG`.  The `ℓ²` suppliers
are *parameters* so that this module does not depend on the `g`-side supplier `tmRandSymbG_l2`. -/
theorem rmStepData_of_suppliers (P : Polynomial ℤ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    {cS : ℝ} (hcS : 0 < cS) {Cssu : NNReal}
    (ρ : ℝ) (hρ : 0 < ρ) (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8)
    (hSS : SSUBodyAtLinf P cS Cssu ρ)
    (hsupF : TmRandL2AtF P C₀ ρ) (hsupG : TmRandL2AtG P C₀ ρ) :
    ∃ C_RM : ℝ, 0 < C_RM ∧ ∃ Ct : NNReal → NNReal, ∃ B : ℕ,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (D : ℝ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        lcL l₁ l₂ k₁ k₂ = max l₁ l₂ → B ≤ lcL l₁ l₂ k₁ k₂ →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2
            (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1)
            (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x))
          1 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C_RM
                * ((Nat.log2 (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ))
              * (ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
                  * (((Ct Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
                    * ((Ct Λ : ENNReal)
                      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))) := by
  obtain ⟨Cf, hCf⟩ := hsupF
  obtain ⟨Cg, hCg⟩ := hsupG
  obtain ⟨Bssu, hBssu⟩ := lowRandBound_of_ssu P C₀ ρ hρ
  obtain ⟨Bsf, hBsf⟩ := lowSymbF_support ρ hρ C₀ hC₀ hρC₀
  obtain ⟨Bsg, hBsg⟩ := lowSymbG_supportSharp P ρ hρ C₀ hC₀ hρC₀
  obtain ⟨C_RM, hC_RM, hRM⟩ := VrFull_TmBtwist_le_rand_abs ρ P
  let Ct : NNReal → NNReal := fun Λ => max (Cf Λ) (Cg Λ)
  refine ⟨C_RM, hC_RM, Ct, max Bssu (max Bsf Bsg), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t D f g hΛ hlac ha1 ht hcaseA hBL hf hg
  have hBssu' : Bssu ≤ lcL l₁ l₂ k₁ k₂ := le_trans (le_max_left _ _) hBL
  have hBsf' : Bsf ≤ lcL l₁ l₂ k₁ k₂ :=
    le_trans (le_trans (le_max_left Bsf Bsg) (le_max_right Bssu (max Bsf Bsg))) hBL
  have hBsg' : Bsg ≤ lcL l₁ l₂ k₁ k₂ :=
    le_trans (le_trans (le_max_right Bsf Bsg) (le_max_right Bssu (max Bsf Bsg))) hBL
  have hlowrb : LowRandBound ρ P C₀ a f g l₁ l₂ k₁ k₂ t D
      (ENNReal.ofReal ((Cssu : ℝ) * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
        * (((Ct Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
          * ((Ct Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))) := by
    refine hBssu Λ cS hcS (Cssu : ℝ) (by positivity) Ct a f g l₁ l₂ k₁ k₂ t D hf hg hcaseA
      hBssu' ?_ ?_ ?_ ?_ ?_
    · intro m₁ m₂ u φ ψ f' g' hm1 hm2 hf' hg' hperφ hperψ hφ hψ
      have h := hSS m₁ m₂ u φ ψ f' g' hm1 hm2 hf' hg' hperφ hperψ hφ hψ
      rwa [coe_mul_ofReal_eq Cssu (by positivity)] at h
    · intro ε K ξ hξ
      exact hBsf a l₁ l₂ k₁ k₂ t ε K hBsf' ξ hξ
    · intro ε K ξ hξ
      exact hBsg a l₁ l₂ k₁ k₂ t ε K hBsg' ξ hξ
    · intro ε hε
      refine (hCf a Λ l₁ l₂ k₁ k₂ (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1) t ε f
        hΛ hlac ha1 hε ht hf).trans ?_
      refine mul_le_mul' ?_ le_rfl
      exact_mod_cast (le_max_left (Cf Λ) (Cg Λ) : Cf Λ ≤ Ct Λ)
    · intro ε hε
      refine (hCg a Λ l₁ l₂ k₁ k₂ (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1) t ε g
        hΛ hlac ha1 hε ht hg).trans ?_
      refine mul_le_mul' ?_ le_rfl
      exact_mod_cast (le_max_right (Cf Λ) (Cg Λ) : Cg Λ ≤ Ct Λ)
  have hmain := hRM l₁ l₂
    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (cw_mStarF_summable _) (cw_mStargF_summable _ _)
    (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1)
    (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) f g
    (ENNReal.ofReal ((Cssu : ℝ) * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
      * (((Ct Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
        * ((Ct Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)))
    (lowSymbF_zero ρ C₀ a l₁ l₂ k₁ k₂ t) (lowSymbG_zero ρ P C₀ a l₁ l₂ k₁ k₂ t) hf hg
    (TmSide_lowSymbFA ρ C₀ a l₁ l₂ k₁ k₂ (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1) t)
    (TmSide_lowSymbGA P ρ C₀ a l₁ l₂ k₁ k₂ (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1) t)
    (Tm_lowSymbF_bddA P ρ l₁ C₀ a l₂ k₁ k₂ t f hf)
    (Tm_lowSymbG_bdd P ρ l₁ C₀ a l₂ k₁ k₂ t g hg)
    (fun ε ε' hε hε' => hlowrb ε ε' hε hε')
  simpa only [lowSliceA] using hmain



/-! ## The identification with the Area A7 small-scale model tuple

`Work.KMTAreas.A7.smallModelTuple` is *definitionally the same family* as `lowModel`: the kernel
`Work.KMTAreas.A7.smallBtwist` is `Work.KMTPlan.A6.BtwistEx` (`smallArithKernel = arithKernelEx`),
the scale `smallL l₁ l₂ k₁ k₂` is `lcL l₁ l₂ k₁ k₂`, and the window `mStarF (uScale ρ (smallL …))`
matches.  The only difference is the clamping predicate: `smallCond = lowSmallSet ∧ mainRegime`.
Hence on a quadruple for which `mainRegime` holds on every admissible scale, the two tuples
coincide, and the Area A7 results (`Work.KMTAreas.A7.SmallModelVar`,
`Work.KMTAreas.A7.SmallModApprox`) apply to `lowModel`. -/

/-- `smallBtwist` *is* `BtwistEx` definitionally (same arithmetic kernel, same window form). -/
theorem smallBtwist_eq_BtwistEx :
    Work.KMTAreas.A7.smallBtwist = BtwistEx := rfl

/-- The two scale functions agree definitionally. -/
theorem smallL_eq_lcL (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ = lcL l₁ l₂ k₁ k₂ := rfl

/-- **`lowModel` is `smallModelTuple` when the main regime holds on the admissible scales.** -/
theorem lowModel_eq_smallModelTuple (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ)
    (hmr : ∀ n, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
      Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n))) :
    lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂
      = Work.KMTAreas.A7.smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ := by
  funext n x
  rw [lowModel_apply, Work.KMTAreas.A7.smallModelTuple_apply]
  by_cases h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
  · have hc : Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ n :=
      ⟨h.1, h.2, hmr n h⟩
    rw [if_pos h, if_pos hc]
    rfl
  · have hc : ¬ Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ n :=
      fun hh => h ⟨hh.1, hh.2.1⟩
    rw [if_neg h, if_neg hc]

/-- **Merging an `ofReal` into a product.**  `ofReal a * (ofReal b * Z) = ofReal (a * b) * Z` for
`0 ≤ a`; this is the workhorse of the constant bookkeeping of the Case-A assembly. -/
theorem ofReal_mul_ofReal_mul {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (Z : ENNReal) :
    ENNReal.ofReal a * (ENNReal.ofReal b * Z) = ENNReal.ofReal (a * b) * Z := by
  rw [ENNReal.ofReal_mul ha, mul_assoc]

/-- **Case A of the small-scale model estimate of the low case of area A6.**  In the regime
`lcL l₁ l₂ k₁ k₂ = max l₁ l₂` the single-scale gain `2^{-cS·max(l₁,l₂)}` produced by `hSS`
(Lemma `ssu`) already has the strength required by the target, and the assembly is the paper's §7
route:

1. the spike at `n = 0` (`lowSpike_le`), giving the bound `C2`;
2. the Rademacher--Menshov reduction (`rmStepData_of_suppliers`, supplied here as the hypothesis
   `hRM`), giving the bound `C1` on the anchored family `lowSliceA`;
3. the per-`t` assembly (`slice_le_of_VrBoundA` with `variationalNorm_lowModelSlice_le_Vr` and the
   vanishing of the family beyond `lowTrunc`, i.e. the hypothesis `hDb`);
4. the `t`-integral (`eLpNorm_variationalNorm_lowModel_le` + `lowModelSlice_aemeasurable`);
5. the absorption of the Rademacher--Menshov loss `⟨log₂(lowTrunc (lowD Λ) ρ L + 1) + 2⟩²` into the
   gain, via `lowTruncLogBoundM` (`≤ lowMfun Λ · 2^{4ρL}`) and `two_rpow_absorb`
   (`2^{4ρL}·2^{-cS L} ≤ 2^{-(cS/2)L}`, which is where `8ρ ≤ cS` is used).  The resulting constant
   is `CA Λ = C_RM · lowMfun Λ · Cssu · (Ct Λ)² + 8·Cssu + 1`. -/
theorem lowModelVar_caseA (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) {cS : ℝ} (hcS : 0 < cS) {Cssu : NNReal}
    (ρ : ℝ) (hρ : 0 < ρ) (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8) (hρcS : 8 * ρ ≤ cS)
    (hSS : SSUBodyAtLinf P cS Cssu ρ)
    (C_RM : ℝ) (hC_RM : 0 < C_RM) (Ct : NNReal → NNReal) (Brm : ℕ)
    (hRM : ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (D : ℝ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        lcL l₁ l₂ k₁ k₂ = max l₁ l₂ → Brm ≤ lcL l₁ l₂ k₁ k₂ →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2
            (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1)
            (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x))
          1 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C_RM
                * ((Nat.log2 (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ))
              * (ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
                  * (((Ct Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
                    * ((Ct Λ : ENNReal)
                      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)))) :
    ∃ CA : NNReal → NNReal, ∃ Bc : ℕ,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
          (n : ℝ) + 1 ≤ lowD Λ * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂))) →
        lcL l₁ l₂ k₁ k₂ = max l₁ l₂ → Bc ≤ lcL l₁ l₂ k₁ k₂ →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (CA Λ : ENNReal) * ENNReal.ofReal (lcWeight (cS / 2) l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨Bsp, hSpike⟩ := lowSpike_le P hd C₀ hC₀ ρ hρ hρC₀ hcS hSS
  let CA : NNReal → NNReal := fun Λ =>
    ⟨C_RM * lowMfun Λ * (Cssu : ℝ) * ((Ct Λ : ℝ) ^ 2) + 2 * (4 * (Cssu : ℝ)) + 1, by
      have h1 : 0 ≤ lowMfun Λ := lowMfun_nonneg Λ
      have h2 : 0 ≤ (Cssu : ℝ) := by positivity
      have h4 : 0 ≤ C_RM := le_of_lt hC_RM
      have h5 : 0 ≤ ((Ct Λ : ℝ)) ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg h4 h1) h2) h5]⟩
  refine ⟨CA, max Brm Bsp, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ hlac ha1 hDb hcaseA hBL hf hg
  have hBrm : Brm ≤ lcL l₁ l₂ k₁ k₂ := le_trans (le_max_left _ _) hBL
  have hBsp : Bsp ≤ lcL l₁ l₂ k₁ k₂ := le_trans (le_max_right _ _) hBL
  have hDpos : 0 < lowD Λ := by
    rw [Work.KMTPlan.A6.lowD]
    have hlog : 0 < Real.log (Λ : ℝ) := Real.log_pos (by exact_mod_cast hΛ)
    positivity
  -- the per-`t` estimate
  have hper : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
        1 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C_RM
            * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ))
          * (ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * (((Ct Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
              * ((Ct Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)))
        + 2 * ((Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
            * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)) := by
    intro t ht
    have hspike' : MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
        ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖) 1 MeasureTheory.Measure.count
        ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
            * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
      by_cases h0 : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0
      · exact hSpike a l₁ l₂ k₁ k₂ t ht hBsp h0 f g hf hg
      · have hz : (fun x : ℤ => ENNReal.ofReal
            ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖) = (0 : ℤ → ENNReal) := by
          funext x
          rw [show lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x = 0 by
            simp only [lowModelSlice, h0, if_false]]
          simp
        rw [hz, MeasureTheory.eLpNorm_zero]
        exact bot_le
    have hvr : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2
        (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1)
        (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x))
        1 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C_RM
              * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ))
            * (ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
              * (((Ct Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
                * ((Ct Λ : ENNReal)
                  * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))) :=
      hRM a Λ l₁ l₂ k₁ k₂ t (lowD Λ) f g hΛ hlac ha1 ht hcaseA hBrm hf hg
    have hptt := Work.KMTPlan.A6.variationalNorm_lowModelSlice_le_Vr ρ P C₀ a f g l₁ l₂ k₁ k₂ t
      r (le_of_lt hr) (lowD Λ) hDpos hDb hf hg
    exact Work.KMTPlan.A6.slice_le_of_VrBoundA ρ P C₀ a f g l₁ l₂ k₁ k₂ t r
      (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1)
      (ENNReal.ofReal (C_RM
              * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ))
            * (ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
              * (((Ct Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
                * ((Ct Λ : ENNReal)
                  * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))))
      ((Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
            * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))
      (fun x => hptt x) hvr hspike'
  have hmain := Work.KMTPlan.A6.eLpNorm_variationalNorm_lowModel_le ρ P C₀ a f g l₁ l₂ k₁ k₂ r
    (le_of_lt (lt_of_le_of_lt (by norm_num : (1 : NNReal) ≤ 2) hr))
    (ENNReal.ofReal (C_RM
            * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ))
          * (ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * (((Ct Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
              * ((Ct Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)))
        + 2 * ((Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
            * (ENNReal.ofReal 2 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)))
    (Work.KMTPlan.A6.lowModelSlice_aemeasurable ρ P C₀ a f g l₁ l₂ k₁ k₂)
    (fun t ht => hper t ht)
  -- ## the absorption of the Rademacher--Menshov loss
  set X : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count with hXdef
  set Y : ENNReal := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hYdef
  set C1 : ENNReal := ENNReal.ofReal (C_RM
          * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ))
        * (ENNReal.ofReal (Cssu * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * (((Ct Λ : ENNReal) * X) * ((Ct Λ : ENNReal) * Y))) with hC1def
  set C2 : ENNReal := (Cssu : ENNReal)
        * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
        * (ENNReal.ofReal 2 * X) * (ENNReal.ofReal 2 * Y) with hC2def
  obtain ⟨g0, hg0def⟩ : ∃ g0 : ℝ, g0 = (2 : ℝ) ^ (-(cS * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))) :=
    ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = (2 : ℝ) ^ (-((cS / 2) * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))) :=
    ⟨_, rfl⟩
  have hcaseR : (max (l₁ : ℝ) (l₂ : ℝ)) = ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) := by
    rw [hcaseA, Nat.cast_max]
  have hL0 : (0 : ℝ) ≤ ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hg00 : 0 ≤ g0 := by rw [hg0def]; positivity
  have hCssu0 : 0 ≤ (Cssu : ℝ) := by positivity
  have hCR0 : 0 ≤ C_RM := le_of_lt hC_RM
  have hw0 : 0 ≤ w := by rw [hwdef]; positivity
  have hwgt : lcWeight (cS / 2) l₁ l₂ k₁ k₂ = w := by
    rw [Work.KMTPlan.A6.lcWeight_eq_rpow_lcLA (cS / 2) l₁ l₂ k₁ k₂, hwdef]
  -- the logarithmic truncation bound
  have hlogK : ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ 2
      ≤ lowMfun Λ * (2 : ℝ) ^ (4 * ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)) := by
    have hKl : ((lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1 : ℕ) : ℝ)
        = ((Nat.ceil (lowD Λ * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
            + 2 : ℕ) : ℝ) := by
      rw [Work.KMTPlan.A6.lowTrunc]
    have hle : ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2)
        ≤ Real.logb 2 ((Nat.ceil (lowD Λ
              * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂))) + 2 : ℕ) : ℝ) + 2 := by
      have h := Work.KMTPlan.A6.nat_log2_cast_le_logb
        (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1)
      rw [hKl] at h
      linarith
    exact (pow_le_pow_left₀ (by positivity) hle 2).trans
      (Work.KMTPlan.A6.lowTruncLogBoundM ρ hρ Λ hΛ (lcL l₁ l₂ k₁ k₂))
  have hg0w : g0 ≤ w := by
    rw [hg0def, hwdef]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith [hcS, hL0]
  have habs : (2 : ℝ) ^ (4 * ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)) * g0 ≤ w := by
    rw [hg0def, hwdef]
    exact Work.KMTPlan.A6.two_rpow_absorb cS (cS / 2) ρ (by linarith) (lcL l₁ l₂ k₁ k₂)
  have h1 : ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ 2 * g0
      ≤ lowMfun Λ * w := by
    calc ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ 2 * g0
        ≤ (lowMfun Λ * (2 : ℝ) ^ (4 * ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))) * g0 :=
          mul_le_mul_of_nonneg_right hlogK hg00
      _ = lowMfun Λ * ((2 : ℝ) ^ (4 * ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)) * g0) := by ring
      _ ≤ lowMfun Λ * w := mul_le_mul_of_nonneg_left habs (lowMfun_nonneg Λ)
  -- the two normalised term bounds
  have hC1norm : C1 = ENNReal.ofReal (C_RM
        * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ)
        * ((Cssu : ℝ) * g0) * ((Ct Λ : ℝ) * (Ct Λ : ℝ))) * (X * Y) := by
    rw [hC1def, hcaseR, ← hg0def, ← ENNReal.ofReal_coe_nnreal]
    rw [show (ENNReal.ofReal ((Ct Λ : ℝ)) * X) * (ENNReal.ofReal ((Ct Λ : ℝ)) * Y)
        = (ENNReal.ofReal ((Ct Λ : ℝ)) * ENNReal.ofReal ((Ct Λ : ℝ))) * (X * Y) from by ring]
    rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg (Ct Λ))]
    calc ENNReal.ofReal (C_RM * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ 2)
          * (ENNReal.ofReal ((Cssu : ℝ) * g0)
            * (ENNReal.ofReal ((Ct Λ : ℝ) * (Ct Λ : ℝ)) * (X * Y)))
        = ENNReal.ofReal (C_RM * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ)
            * ((Cssu : ℝ) * g0))
          * (ENNReal.ofReal ((Ct Λ : ℝ) * (Ct Λ : ℝ)) * (X * Y)) :=
          ofReal_mul_ofReal_mul (show (0 : ℝ) ≤ C_RM * ((Nat.log2
            (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ) from by positivity) _ _
      _ = ENNReal.ofReal (C_RM * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ)
            * ((Cssu : ℝ) * g0) * ((Ct Λ : ℝ) * (Ct Λ : ℝ))) * (X * Y) :=
          ofReal_mul_ofReal_mul (show (0 : ℝ) ≤ C_RM * ((Nat.log2
            (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ) * ((Cssu : ℝ) * g0)
            from by positivity) _ _
  have hC2norm : 2 * C2 = ENNReal.ofReal (2 * (Cssu : ℝ) * g0 * 2 * 2) * (X * Y) := by
    rw [hC2def, hcaseR, ← hg0def, ← ENNReal.ofReal_coe_nnreal,
      show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) from (ENNReal.ofReal_ofNat 2).symm]
    rw [show ENNReal.ofReal (2 : ℝ) * (ENNReal.ofReal (Cssu : ℝ) * ENNReal.ofReal g0
          * (ENNReal.ofReal 2 * X) * (ENNReal.ofReal 2 * Y))
        = ENNReal.ofReal (2 : ℝ) * (ENNReal.ofReal (Cssu : ℝ) * (ENNReal.ofReal g0
            * (ENNReal.ofReal 2 * (ENNReal.ofReal 2 * (X * Y))))) from by ring]
    calc ENNReal.ofReal (2 : ℝ) * (ENNReal.ofReal (Cssu : ℝ) * (ENNReal.ofReal g0
            * (ENNReal.ofReal 2 * (ENNReal.ofReal 2 * (X * Y)))))
        = ENNReal.ofReal (2 * (Cssu : ℝ)) * (ENNReal.ofReal g0
            * (ENNReal.ofReal 2 * (ENNReal.ofReal 2 * (X * Y)))) :=
          ofReal_mul_ofReal_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
      _ = ENNReal.ofReal (2 * (Cssu : ℝ) * g0)
            * (ENNReal.ofReal 2 * (ENNReal.ofReal 2 * (X * Y))) :=
          ofReal_mul_ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (Cssu : ℝ)) _ _
      _ = ENNReal.ofReal (2 * (Cssu : ℝ) * g0 * 2) * (ENNReal.ofReal 2 * (X * Y)) :=
          ofReal_mul_ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (Cssu : ℝ) * g0) _ _
      _ = ENNReal.ofReal (2 * (Cssu : ℝ) * g0 * 2 * 2) * (X * Y) :=
          ofReal_mul_ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (Cssu : ℝ) * g0 * 2) _ _
  -- the sum
  have hsum : C1 + 2 * C2 ≤ ENNReal.ofReal ((CA Λ : ℝ) * w) * (X * Y) := by
    rw [hC1norm, hC2norm, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hCAval : (CA Λ : ℝ)
        = C_RM * lowMfun Λ * (Cssu : ℝ) * (Ct Λ : ℝ) ^ 2 + 2 * (4 * (Cssu : ℝ)) + 1 := rfl
    have h2 : C_RM * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ)
          * ((Cssu : ℝ) * g0) * ((Ct Λ : ℝ) * (Ct Λ : ℝ))
        ≤ C_RM * lowMfun Λ * (Cssu : ℝ) * ((Ct Λ : ℝ) * (Ct Λ : ℝ)) * w := by
      have hsq : ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ)
          = ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ 2 := by
        rw [Real.rpow_two, pow_two]
      rw [hsq]
      have hb : 0 ≤ C_RM * (Cssu : ℝ) * ((Ct Λ : ℝ) * (Ct Λ : ℝ)) := by positivity
      calc C_RM * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ 2
            * ((Cssu : ℝ) * g0) * ((Ct Λ : ℝ) * (Ct Λ : ℝ))
          = C_RM * (Cssu : ℝ) * ((Ct Λ : ℝ) * (Ct Λ : ℝ)) * (((Nat.log2
              (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ 2 * g0) := by ring
        _ ≤ C_RM * (Cssu : ℝ) * ((Ct Λ : ℝ) * (Ct Λ : ℝ)) * (lowMfun Λ * w) :=
            mul_le_mul_of_nonneg_left h1 hb
        _ = C_RM * lowMfun Λ * (Cssu : ℝ) * ((Ct Λ : ℝ) * (Ct Λ : ℝ)) * w := by ring
    have h3 : 2 * (Cssu : ℝ) * g0 * 2 * 2 ≤ 2 * (4 * (Cssu : ℝ)) * w := by
      calc 2 * (Cssu : ℝ) * g0 * 2 * 2 = 2 * (4 * (Cssu : ℝ)) * g0 := by ring
        _ ≤ 2 * (4 * (Cssu : ℝ)) * w := mul_le_mul_of_nonneg_left hg0w (by positivity)
    calc C_RM * ((Nat.log2 (lowTrunc (lowD Λ) ρ (lcL l₁ l₂ k₁ k₂) + 1) : ℝ) + 2) ^ (2 : ℝ)
          * ((Cssu : ℝ) * g0) * ((Ct Λ : ℝ) * (Ct Λ : ℝ))
          + 2 * (Cssu : ℝ) * g0 * 2 * 2
        ≤ C_RM * lowMfun Λ * (Cssu : ℝ) * ((Ct Λ : ℝ) * (Ct Λ : ℝ)) * w
          + 2 * (4 * (Cssu : ℝ)) * w := add_le_add h2 h3
      _ ≤ (CA Λ : ℝ) * w := by
          rw [hCAval]
          nlinarith [hw0]
  refine hmain.trans hsum |>.trans ?_
  rw [hwgt, ← coe_mul_ofReal_eq (CA Λ) hw0]
  exact le_of_eq (by ring)

/-- **The assembly of `lowSmallModelVar` from the paper's route.**  Inputs: the single-scale estimate
`hSS` (the paper's Lemma `ssu`), the two randomised `ℓ²` suppliers `hTF`/`hTG`, and the Case-B
estimate `hB` (the `integ-ident` half of the argument).  The assembly splits, for each `Λ`, on the
`Λ`-dependent threshold `max Bsp0 (lowLogB ρ C₀ Λ)` of the sharp logarithmic truncation bound
`lowSmallSet_le_log_sharp`: below it the crude bound `lowModelVar_boundedLA` applies, above it the
hypothesis `hDb` of the Case-A/Case-B estimates is available (via `lowLogB_spec`), and the two cases
`lcL = max l₁ l₂` (Case A, `lowModelVar_caseA`) and `max l₁ l₂ < lcL` (Case B) exhaust the rest.
The three constants are combined into `C Λ = max (Cbdd Λ Λ) (max (CA Λ) (Cb Λ))`. -/
theorem lowSmallModelVar_of_shapes (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hSS : Work.KMTPlan.A6.SSUShapeLinf P) (hTF : Work.KMTPlan.A6.TmRandL2ShapeF P C₀)
    (hTG : Work.KMTPlan.A6.TmRandL2ShapeG P C₀) (hB : LowModelCaseBShape P r C₀) :
    LowModelVarShape P r C₀ := by
  classical
  obtain ⟨cS, hcS, ρ₀s, hρ₀s, hSSb⟩ := Work.KMTPlan.A6.exists_ssuBodyAtLinf_of_ssuShapeLinf hSS
  obtain ⟨ρF, hρF, hTF'⟩ := Work.KMTPlan.A6.tmRandL2AtF_of_shape hTF
  obtain ⟨ρG, hρG, hTG'⟩ := Work.KMTPlan.A6.tmRandL2AtG_of_shape hTG
  obtain ⟨cB, hcB, ρ₀B, hρ₀B, hBf⟩ := hB
  have hc : 0 < min (cS / 2) cB := lt_min (by linarith) hcB
  refine ⟨min (cS / 2) cB, hc,
    min (min (min ρ₀s (min ρF ρG)) (min ρ₀B (min (1 / (8 * (C₀ : ℝ))) 1))) (cS / 8), ?_, ?_⟩
  · refine lt_min (lt_min (lt_min hρ₀s (lt_min hρF hρG))
      (lt_min hρ₀B (lt_min (by positivity) one_pos))) (by linarith)
  intro ρ hρ hρle
  have hρ1 : ρ ≤ min ρ₀s (min ρF ρG) :=
    le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρ2 : ρ ≤ min ρ₀B (min (1 / (8 * (C₀ : ℝ))) 1) :=
    le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ3 : ρ ≤ cS / 8 := le_trans hρle (min_le_right _ _)
  have h1 : ρ ≤ ρ₀s := le_trans hρ1 (min_le_left _ _)
  have h2 : ρ ≤ ρF := le_trans hρ1 (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : ρ ≤ ρG := le_trans hρ1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have h4 : ρ ≤ ρ₀B := le_trans hρ2 (min_le_left _ _)
  have h5 : ρ ≤ 1 / (8 * (C₀ : ℝ)) :=
    le_trans hρ2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have h6 : ρ ≤ 1 := le_trans hρ2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have h7 : 8 * ρ ≤ cS := by linarith
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀ : 0 < C₀)
  have hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8 := by
    calc ρ * (C₀ : ℝ) ≤ (1 / (8 * (C₀ : ℝ))) * (C₀ : ℝ) :=
          mul_le_mul_of_nonneg_right h5 hC₀pos.le
      _ = 1 / 8 := by field_simp
  obtain ⟨Cssu, hCssu, hSSρ⟩ := hSSb ρ hρ h1
  obtain ⟨Cf, hCf⟩ := hTF' ρ hρ h2
  obtain ⟨Cg, hCg⟩ := hTG' ρ hρ h3
  obtain ⟨Cb, Bb, hCb⟩ := hBf ρ hρ h4
  obtain ⟨C_RM, hC_RM, Ct, Brm, hRM⟩ :=
    rmStepData_of_suppliers P C₀ hC₀ hcS ρ hρ hρC₀ hSSρ ⟨Cf, hCf⟩ ⟨Cg, hCg⟩
  obtain ⟨CA, Bc, hCA⟩ := lowModelVar_caseA P hd r hr C₀ hC₀ hcS ρ hρ hρC₀ h7 hSSρ
    C_RM hC_RM Ct Brm hRM
  obtain ⟨Bsp0, hBsp0def⟩ : ∃ Bsp0 : ℕ, Bsp0 = max Brm (max Bc Bb) := ⟨_, rfl⟩
  let Bspl : NNReal → ℕ := fun Λ => max Bsp0 (Work.KMTPlan.A6.lowLogB ρ C₀ Λ)
  let Cbdd : NNReal → NNReal → NNReal := fun Λ => Classical.choose
    (Work.KMTPlan.A6.lowModelVar_boundedLA P hd r hr ρ hρ h6 C₀ hC₀ (Bspl Λ) (min (cS / 2) cB))
  refine ⟨fun Λ => max (Cbdd Λ Λ) (max (CA Λ) (Cb Λ)), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ hlac ha1 hk hf hg hwin
  have hX : ∀ n : ℕ, AEMeasurable (fun p : ℝ × ℤ =>
      lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ p.1 n p.2)
      (MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.Measure.count) :=
    lowModelSlice_aemeasurable ρ P C₀ a f g l₁ l₂ k₁ k₂
  by_cases hLs : lcL l₁ l₂ k₁ k₂ ≤ Bspl Λ
  · -- the crude bound, on the finitely many `Λ`-dependently bounded quadruples
    have h := Classical.choose_spec
      (Work.KMTPlan.A6.lowModelVar_boundedLA P hd r hr ρ hρ h6 C₀ hC₀ (Bspl Λ)
        (min (cS / 2) cB))
    have hb := h a Λ l₁ l₂ k₁ k₂ f g hΛ hlac ha1 hLs hf hg hX
    refine hb.trans ?_
    refine mul_le_mul' (mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl) le_rfl
    exact_mod_cast (le_max_left (Cbdd Λ Λ) (max (CA Λ) (Cb Λ)) : Cbdd Λ Λ
      ≤ max (Cbdd Λ Λ) (max (CA Λ) (Cb Λ)))
  · push Not at hLs
    have hmax : max Bsp0 (Work.KMTPlan.A6.lowLogB ρ C₀ Λ) ≤ lcL l₁ l₂ k₁ k₂ := le_of_lt hLs
    have hB0 : Bsp0 ≤ lcL l₁ l₂ k₁ k₂ := le_trans (le_max_left _ _) hmax
    have hBl : Work.KMTPlan.A6.lowLogB ρ C₀ Λ ≤ lcL l₁ l₂ k₁ k₂ :=
      le_trans (le_max_right _ _) hmax
    have hBrm0 : Brm ≤ Bsp0 := hBsp0def ▸ le_max_left Brm (max Bc Bb)
    have hBc0 : Bc ≤ Bsp0 :=
      hBsp0def ▸ le_trans (le_max_left Bc Bb) (le_max_right Brm (max Bc Bb))
    have hBb0 : Bb ≤ Bsp0 :=
      hBsp0def ▸ le_trans (le_max_right Bc Bb) (le_max_right Brm (max Bc Bb))
    have hBrmL : Brm ≤ lcL l₁ l₂ k₁ k₂ := le_trans hBrm0 hB0
    have hBcL : Bc ≤ lcL l₁ l₂ k₁ k₂ := le_trans hBc0 hB0
    have hBbL : Bb ≤ lcL l₁ l₂ k₁ k₂ := le_trans hBb0 hB0
    have hDb : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
        (n : ℝ) + 1 ≤ lowD Λ
          * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) :=
      fun n hsm => Work.KMTPlan.A6.lowLogB_spec ρ hρ C₀ Λ hΛ a l₁ l₂ k₁ k₂ n hlac ha1 hBl hsm
    have hmaxle : max l₁ l₂ ≤ lcL l₁ l₂ k₁ k₂ :=
      show max l₁ l₂ ≤ max (max l₁ l₂) (max k₁ k₂) from le_max_left _ _
    by_cases hcaseA : lcL l₁ l₂ k₁ k₂ = max l₁ l₂
    · -- Case A
      have hA := hCA a Λ l₁ l₂ k₁ k₂ f g hΛ hlac ha1 hDb hcaseA hBcL hf hg
      refine hA.trans ?_
      have hCAle : (CA Λ : ENNReal)
          ≤ ((max (Cbdd Λ Λ) (max (CA Λ) (Cb Λ)) : NNReal) : ENNReal) := by
        refine ENNReal.coe_le_coe.mpr ?_
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      have hw : ENNReal.ofReal (lcWeight (cS / 2) l₁ l₂ k₁ k₂)
          ≤ ENNReal.ofReal (lcWeight (min (cS / 2) cB) l₁ l₂ k₁ k₂) :=
        ENNReal.ofReal_le_ofReal (lcWeight_le_of_le (min_le_left _ _) l₁ l₂ k₁ k₂)
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' hCAle hw) le_rfl) le_rfl
    · -- Case B
      have hcaseB : max l₁ l₂ < lcL l₁ l₂ k₁ k₂ :=
        lt_of_le_of_ne hmaxle (Ne.symm hcaseA)
      have hB := hCb a Λ l₁ l₂ k₁ k₂ f g hΛ hlac ha1 hk hBbL hcaseB hwin hf hg
      refine hB.trans ?_
      have hCBle : (Cb Λ : ENNReal)
          ≤ ((max (Cbdd Λ Λ) (max (CA Λ) (Cb Λ)) : NNReal) : ENNReal) := by
        refine ENNReal.coe_le_coe.mpr ?_
        exact le_trans (le_max_right (CA Λ) (Cb Λ))
          (le_max_right (Cbdd Λ Λ) (max (CA Λ) (Cb Λ)))
      have hw : ENNReal.ofReal (lcWeight cB l₁ l₂ k₁ k₂)
          ≤ ENNReal.ofReal (lcWeight (min (cS / 2) cB) l₁ l₂ k₁ k₂) :=
        ENNReal.ofReal_le_ofReal (lcWeight_le_of_le (min_le_right _ _) l₁ l₂ k₁ k₂)
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' hCBle hw) le_rfl) le_rfl

/-- **The paper's Lemma `ssu`, in its provable (bounded-bump) form `SSUShapeLinf`**: this is
`Work.KMTPlan.A6.ssuBtwistExBdd` (sorry-free, axiom-clean). -/
theorem ssuShapeLinf_of_bdd (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) :
    Work.KMTPlan.A6.SSUShapeLinf P :=
  Work.KMTPlan.A6.ssuBtwistExBdd P hd hA1 hI

/-- **The Case-B estimate as a `LowModelCaseBShape`** (the wrapper of the delegated module
`Work.KMTPlan.A6.lowModelVarCaseB`). -/
theorem lowModelCaseBShape_of (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hSS : Work.KMTPlan.A6.SSUShapeLinf P) :
    LowModelCaseBShape P r C₀ :=
  Work.KMTPlan.A6.lowModelVarCaseBLinf P hd r hr hA1 hI C₀ hC₀ hSS

/-- **The small-scale model-tuple variational estimate of the low case of area A6.**

This is the paper's §7 estimate for the model tuple `lowModel` with the *exponential gain*
`2^{-c·lcL}`: the assembly `lowSmallModelVar_of_shapes` with the paper's three inputs, namely

* the single-scale estimate `ssu` with the gain (`ssuModelGain`, i.e. `ssuShape_of_ssu`),
* the two randomised `ℓ²` suppliers `tmRandSymb_l2`/`tmRandSymbG_l2`,
* the Case-B (`integ-ident`) estimate `lowModelVarCaseB` (i.e. `lowModelCaseBShape_of`). -/
theorem lowSmallModelVar (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂
          ≤ 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTPlan.A6.lcWeight c l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  lowSmallModelVar_of_shapes P hd r hr C₀ hC₀
    (ssuShapeLinf_of_bdd P hd hA1 hI)
    (Work.KMTPlan.A6.tmRandSymb_l2 P hd hA1 C₀ hC₀)
    (Work.KMTPlan.A6.tmRandSymbG_l2 P hd hA1 C₀ hC₀)
    (lowModelCaseBShape_of P hd r hr hA1 hI C₀ hC₀ (ssuShapeLinf_of_bdd P hd hA1 hI))

end

end Work.KMTPlan.A6
