import Mathlib
import Submission.Work.KMTAreas.A7.FpieceEqTm
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded
import Submission.Work.KMTAreas.integrable_iwSymbolSet_periodize
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp

namespace Work.KMTAreas.A7

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-! ## Linearity of the Ionescu--Wainger kernel and convolution in a finite sum of symbols

The kernel `iwKernel (iwSymbolSet A Φ) j` is the `j`-th Fourier coefficient of the symbol
`iwSymbolSet A Φ = ∑_{α ∈ A} Φ (· - α)`, so it is linear in a *finite* sum of symbols, and for
bounded input the convolution `iwConv` is linear in the symbol as well.  These are the elementary
lemmas needed for the target; they are recalled here as `private` helpers so that the file is
self-contained. -/

private theorem fourierCoeff_finsetSum_lin {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (g : ι → Work.Analysis.IonescuWainger.Circle → ℂ)
    (hInt : ∀ n ∈ s, Integrable (g n) circleMeasure) (j : ℤ) :
    fourierCoeff (fun ξ => ∑ n ∈ s, c n * g n ξ) j = ∑ n ∈ s, c n * fourierCoeff (g n) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fourierCoeff]
  | insert a s ha ih =>
      have hInt' : ∀ n ∈ s, Integrable (g n) circleMeasure :=
        fun n hn => hInt n (Finset.mem_insert_of_mem hn)
      have hsum : Integrable (fun ξ => ∑ n ∈ s, c n * g n ξ) circleMeasure :=
        integrable_finsetSum s (fun n hn => (hInt' n hn).const_mul (c n))
      have hsplit : (fun ξ => ∑ n ∈ insert a s, c n * g n ξ)
          = (fun ξ => c a * g a ξ) + (fun ξ => ∑ n ∈ s, c n * g n ξ) := by
        funext ξ
        simp only [Finset.sum_insert ha, Pi.add_apply]
      have h1 : fourierCoeff ((fun ξ => c a * g a ξ) + (fun ξ => ∑ n ∈ s, c n * g n ξ)) j
          = fourierCoeff (fun ξ => c a * g a ξ) j
            + fourierCoeff (fun ξ => ∑ n ∈ s, c n * g n ξ) j :=
        congrFun (fourierCoeff.add ((hInt a (Finset.mem_insert_self a s)).const_mul (c a))
          hsum) j
      rw [hsplit, h1, ih hInt', fourierCoeff.const_mul, Finset.sum_insert ha]

private theorem iwSymbolSet_finsetSum_lin {ι : Type*}
    (A : Finset Work.Analysis.IonescuWainger.Circle) (s : Finset ι) (c : ι → ℂ)
    (Φ : ι → Work.Analysis.IonescuWainger.Circle → ℂ) :
    iwSymbolSet A (fun ξ => ∑ n ∈ s, c n * Φ n ξ)
      = fun ξ => ∑ n ∈ s, c n * iwSymbolSet A (Φ n) ξ := by
  funext ξ
  simp only [iwSymbolSet]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun n _ => (Finset.mul_sum _ _ _).symm)

private theorem iwKernel_iwSymbolSet_finsetSum_lin {ι : Type*}
    (A : Finset Work.Analysis.IonescuWainger.Circle) (s : Finset ι) (c : ι → ℂ)
    (Φ : ι → Work.Analysis.IonescuWainger.Circle → ℂ)
    (hInt : ∀ n ∈ s, Integrable (iwSymbolSet A (Φ n)) circleMeasure) (j : ℤ) :
    iwKernel (iwSymbolSet A (fun ξ => ∑ n ∈ s, c n * Φ n ξ)) j
      = ∑ n ∈ s, c n * iwKernel (iwSymbolSet A (Φ n)) j := by
  rw [iwKernel, iwSymbolSet_finsetSum_lin]
  exact fourierCoeff_finsetSum_lin s c (fun n => iwSymbolSet A (Φ n)) hInt j

private theorem periodize_finsetSum_lin {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (ψ : ι → ℝ → ℂ) (hψ : ∀ n ∈ s, ∀ x : ℝ, Summable fun j : ℤ => ψ n (x + j)) :
    periodize (fun ξ => ∑ n ∈ s, c n * ψ n ξ) = fun ξ => ∑ n ∈ s, c n * periodize (ψ n) ξ := by
  funext ξ
  simp only [periodize]
  rw [Summable.tsum_finsetSum (f := fun n : ι => fun k : ℤ => c n * ψ n
        ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k))]
  · exact Finset.sum_congr rfl (fun n _ => (tsum_mul_left).trans (by rw [mul_comm]))
  · exact fun n hn => (hψ n hn _).mul_left (c n)

/-- For bounded input, the Ionescu--Wainger convolution is linear in the symbol of a *finite* sum:
the finitely many kernel families are all absolutely summable, so `tsum` is additive.  (For
arbitrary `f` the corresponding statement is false, see the header of `A7/FpieceEqTm.lean`.) -/
theorem iwConv_finsetSum_of_bounded_lin {ι : Type*}
    (A : Finset Work.Analysis.IonescuWainger.Circle)
    (s : Finset ι) (c : ι → ℂ) (Φ : ι → Work.Analysis.IonescuWainger.Circle → ℂ)
    (f : ℤ → ℂ) {B : ℝ} (hB : ∀ m : ℤ, ‖f m‖ ≤ B)
    (hInt : ∀ n ∈ s, Integrable (iwSymbolSet A (Φ n)) circleMeasure)
    (hκ : ∀ n ∈ s, Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A (Φ n)) j‖) :
    (∑ n ∈ s, c n • iwConv A (Φ n) f)
      = iwConv A (fun ξ => ∑ n ∈ s, c n * Φ n ξ) f := by
  classical
  funext x
  have hL : (∑ n ∈ s, c n • iwConv A (Φ n) f) x
      = ∑ n ∈ s, c n * (∑' j : ℤ, iwKernel (iwSymbolSet A (Φ n)) j * f (x - j)) := by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, iwConv_apply]
    simp only [smul_eq_mul]
  have hR : iwConv A (fun ξ => ∑ n ∈ s, c n * Φ n ξ) f x
      = ∑ n ∈ s, c n * (∑' j : ℤ, iwKernel (iwSymbolSet A (Φ n)) j * f (x - j)) := by
    rw [iwConv_apply]
    simp only [smul_eq_mul]
    have h1 : (∑' j : ℤ, iwKernel (iwSymbolSet A (fun ξ => ∑ n ∈ s, c n * Φ n ξ)) j
          * f (x - j))
        = ∑' j : ℤ, ∑ n ∈ s, (c n * iwKernel (iwSymbolSet A (Φ n)) j) * f (x - j) := by
      refine tsum_congr (fun j => ?_)
      rw [iwKernel_iwSymbolSet_finsetSum_lin A s c Φ hInt j, Finset.sum_mul]
    have hSumm : ∀ n ∈ s, Summable (fun j : ℤ =>
        (c n * iwKernel (iwSymbolSet A (Φ n)) j) * f (x - j)) := by
      intro n hn
      refine Summable.of_norm_bounded
        ((hκ n hn).mul_right (‖c n‖ * max B 0)) (fun j => ?_)
      rw [norm_mul, norm_mul]
      calc ‖c n‖ * ‖iwKernel (iwSymbolSet A (Φ n)) j‖ * ‖f (x - j)‖
          ≤ ‖c n‖ * ‖iwKernel (iwSymbolSet A (Φ n)) j‖ * max B 0 :=
            mul_le_mul_of_nonneg_left ((hB (x - j)).trans (le_max_left B 0)) (by positivity)
        _ = ‖iwKernel (iwSymbolSet A (Φ n)) j‖ * (‖c n‖ * max B 0) := by ring
    rw [h1, Summable.tsum_finsetSum (f := fun n : ι => fun j : ℤ =>
      (c n * iwKernel (iwSymbolSet A (Φ n)) j) * f (x - j)) hSumm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← tsum_mul_left]
    exact tsum_congr (fun j => by ring)
  rw [hL, hR]

/-- The kernel of the Ionescu--Wainger symbol of a *narrow* Schwartz symbol is in `ℓ¹`: the
narrowness hypothesis forces the symbol to have compact support, so the quadratic-decay estimate
`iwKernel_decay_of_bump` applies. -/
theorem summable_iwKernel_narrow_schwartz (ρ : ℝ) (l : ℕ) {k : ℤ}
    (Φ : SchwartzMap ℝ ℂ) (hnarrow : ∀ ξ : ℝ, (Φ : ℝ → ℂ) ξ ≠ 0 → ξ ∈ realArc k) :
    Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (Φ : ℝ → ℂ))) j‖) := by
  have hcs : HasCompactSupport (Φ : ℝ → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact (K := realArc k) isCompact_Icc
      (fun x hx => hnarrow x hx)
  have hcd : ContDiff ℝ 2 (Φ : ℝ → ℂ) := Φ.smooth 2
  set S : ℝ := max (∫ y, ‖(Φ : ℝ → ℂ) y‖) (∫ y, ‖iteratedDeriv 2 (Φ : ℝ → ℂ) y‖) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact le_trans (integral_nonneg fun y => norm_nonneg _) (le_max_left _ _)
  have h1 : (∫ y, ‖(Φ : ℝ → ℂ) y‖) ≤ S := by rw [hSdef]; exact le_max_left _ _
  have h2 : (∫ y, ‖iteratedDeriv 2 (Φ : ℝ → ℂ) y‖) ≤ S := by rw [hSdef]; exact le_max_right _ _
  have hdec := iwKernel_decay_of_bump (iwArithFreqs ρ l) hcd hcs hSnn h1 h2
  refine Work.KMTContract.kernel_l1_of_decay
    (C := 4 * (((iwArithFreqs ρ l).card : ℝ) * S) + 1) (fun j => ?_)
  have hj := hdec j
  rw [norm_kmtKernWeight] at hj
  rwa [mul_one_div] at hj

/-- **Linearity of `Tle` in the symbol over a finite signed sum, for bounded input.**
For a family `Φ : ℕ → SchwartzMap ℝ ℂ` of symbols all supported in the narrow arc `ℝ_{≤k}`
(`2^k < 1/2`), a finite set `U` and signs `ω`, the finite signed sum of the Ionescu–Wainger
projections `Tle ρ l (Φ n)` equals the single projection with the signed-sum symbol — provided the
input `f` is bounded (the unconditional statement is false, see `A7/FpieceEqTm.lean`). -/
theorem Tle_finsetSum_of_bounded (ρ : ℝ) (l : ℕ) (k : ℤ) (hk : (2 : ℝ) ^ k < 1 / 2)
    (Φ : ℕ → SchwartzMap ℝ ℂ)
    (hnarrow : ∀ n ξ, (Φ n : ℝ → ℂ) ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k)
    (U : Finset ℕ) (ω : ℕ → Bool) {f : ℤ → ℂ} {B : ℝ} (hB : ∀ m : ℤ, ‖f m‖ ≤ B) :
    (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * Work.KMTAreas.A7.Tle ρ l (Φ n : ℝ → ℂ) f x)
      = Work.KMTAreas.A7.Tle ρ l (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ) f := by
  classical
  simp only [Tle]
  have hInt : ∀ n ∈ U, Integrable (iwSymbolSet (iwArithFreqs ρ l)
      (periodize ((Φ n : ℝ → ℂ)))) circleMeasure :=
    fun n _ => Work.KMTAreas.integrable_iwSymbolSet_periodize _ (Φ n)
  have hκ : ∀ n ∈ U, Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
      (periodize ((Φ n : ℝ → ℂ)))) j‖) :=
    fun n _ => summable_iwKernel_narrow_schwartz ρ l (Φ n) (fun ξ hξ => hnarrow n ξ hξ)
  have hψ : ∀ n ∈ U, ∀ x : ℝ, Summable fun j : ℤ => (Φ n : ℝ → ℂ) (x + j) :=
    fun n _ x => (Work.KMTAreas.schwartz_shift_summable (Φ n) x).of_norm
  have hL : (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        iwConv (iwArithFreqs ρ l) (periodize ((Φ n : ℝ → ℂ))) f x)
      = ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) •
          iwConv (iwArithFreqs ρ l) (periodize ((Φ n : ℝ → ℂ))) f := by
    funext x
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun n _ => by rw [Pi.smul_apply, smul_eq_mul])
  have hmain : (∑ n ∈ U, (if ω n then (1 : ℂ) else -1) •
        iwConv (iwArithFreqs ρ l) (periodize ((Φ n : ℝ → ℂ))) f)
      = iwConv (iwArithFreqs ρ l)
          (fun ξ : Work.Analysis.IonescuWainger.Circle => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            periodize ((Φ n : ℝ → ℂ)) ξ) f :=
    iwConv_finsetSum_of_bounded_lin (iwArithFreqs ρ l) U (fun n => if ω n then (1 : ℂ) else -1)
      (fun n => periodize ((Φ n : ℝ → ℂ))) f hB hInt hκ
  have hper : periodize (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        (Φ n : ℝ → ℂ) ξ)
      = fun ξ : Work.Analysis.IonescuWainger.Circle =>
          ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * periodize ((Φ n : ℝ → ℂ)) ξ :=
    periodize_finsetSum_lin U (fun n => if ω n then (1 : ℂ) else -1)
      (fun n => (Φ n : ℝ → ℂ)) hψ
  rw [hL, hmain, hper]

end

end Work.KMTAreas.A7
