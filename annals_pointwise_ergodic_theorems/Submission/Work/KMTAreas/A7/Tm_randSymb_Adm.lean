/-
# Admissibility of symbols for the exact-height IW multiplier family `Tm`

The target of `Submission/Work/KMTAreas/A7/Tm_randSymb_smallSymb` is the identity

  `∑_{k<K} ε k • (Tm ρ l (φ (k+1)) f - Tm ρ l (φ k) f) = Tm ρ l (randSymb φ ε K) f`

for `φ = smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t` (and the `g`-side analogue), for an *arbitrary bounded*
input `f`.  Since `Tm ρ l ψ = iwConv (diffFreqs ρ l) (periodize ψ)` is defined by an
*unconditional* `tsum`, the linearity of `Tm` in the symbol is not free: the summands
`j ↦ iwKernel (iwSymbolSet A (periodize ψ)) j • f (n - j)` must be absolutely summable, and this is
the only place where the boundedness of `f` and the decay of the kernel enter.

This module isolates the three analytic properties that make a symbol `ψ` usable in such a
linearity argument:

* `Adm A ψ`: the translates of `ψ` are summable at every point (so that `periodize` is additive),
  the IW symbol `iwSymbolSet A (periodize ψ)` is integrable on the circle (so that the Fourier
  coefficients are additive in the symbol), and the convolution kernel is in `ℓ¹` (so that
  bounded input makes the `tsum` summable).

The module then records that `Adm` is closed under addition and scalar multiplication, and the
three forms of linearity of `Tm` that the assembly uses.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FpieceEqTm
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- **Admissibility of a symbol `φ` at the frequency set `A`**: the translates of `φ` are summable
at every point, the IW symbol `iwSymbolSet A (periodize φ)` is integrable on the circle, and its
Fourier-coefficient (convolution) kernel is in `ℓ¹`.  These are exactly the hypotheses under which
`Tm` is additive in the symbol for bounded input (`Tm_add_of_bounded`). -/
def Adm (A : Finset Work.Analysis.IonescuWainger.Circle) (φ : ℝ → ℂ) : Prop :=
  (∀ x : ℝ, Summable fun j : ℤ => φ (x + (j : ℝ))) ∧
    Integrable (iwSymbolSet A (periodize φ)) circleMeasure ∧
    Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A (periodize φ)) j‖

/-- The exact-height multiplier of the zero symbol is the zero operator. -/
theorem Tm_zero' (ρ : ℝ) (l : ℕ) (f : ℤ → ℂ) : Tm ρ l (0 : ℝ → ℂ) f = 0 := by
  funext y
  simp only [Tm, iwConv_apply, Pi.zero_apply]
  simp [iwKernel, fourierCoeff, periodize]

/-- Pointwise scalar multiples of an admissible symbol are admissible. -/
theorem Adm.const_mul {A : Finset Work.Analysis.IonescuWainger.Circle} {φ : ℝ → ℂ}
    (h : Adm A φ) (c : ℂ) : Adm A (fun ξ => c * φ ξ) := by
  have hper : periodize (fun ξ => c * φ ξ) = fun ξ => c * periodize φ ξ := by
    funext ξ
    simp only [periodize]
    exact tsum_mul_left
  have hsym : iwSymbolSet A (fun ξ => c * periodize φ ξ)
      = fun ξ => c * iwSymbolSet A (periodize φ) ξ := iwSymbolSet_const_mul A c (periodize φ)
  refine ⟨fun x => (h.1 x).mul_left c, ?_, ?_⟩
  · rw [hper, hsym]
    exact h.2.1.const_mul c
  · have hker : ∀ j : ℤ,
        iwKernel (iwSymbolSet A (fun ξ => c * periodize φ ξ)) j
          = c * iwKernel (iwSymbolSet A (periodize φ)) j :=
      fun j => iwKernel_iwSymbolSet_const_mul A c j
    simp only [hper]
    simpa only [hker, norm_mul] using h.2.2.mul_left ‖c‖

/-- Sums of admissible symbols are admissible. -/
theorem Adm.add {A : Finset Work.Analysis.IonescuWainger.Circle} {φ ψ : ℝ → ℂ}
    (h : Adm A φ) (h' : Adm A ψ) : Adm A (φ + ψ) := by
  have hper : periodize (φ + ψ) = periodize φ + periodize ψ := periodize_add h.1 h'.1
  refine ⟨fun x => (h.1 x).add (h'.1 x), ?_, ?_⟩
  · rw [hper, iwSymbolSet_add]
    exact h.2.1.add h'.2.1
  · have hker : ∀ j : ℤ,
        iwKernel (iwSymbolSet A (periodize φ + periodize ψ)) j
          = iwKernel (iwSymbolSet A (periodize φ)) j + iwKernel (iwSymbolSet A (periodize ψ)) j :=
      fun j => iwKernel_iwSymbolSet_add h.2.1 h'.2.1 j
    simp only [hper]
    exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => by rw [hker j]; exact norm_add_le _ _) (h.2.2.add h'.2.2)

/-- Negatives of admissible symbols are admissible. -/
theorem Adm.neg {A : Finset Work.Analysis.IonescuWainger.Circle} {φ : ℝ → ℂ} (h : Adm A φ) :
    Adm A (-φ) := by
  have hneg : Adm A (fun ξ => (-1 : ℂ) * φ ξ) := h.const_mul (-1)
  have hfun : (fun ξ => (-1 : ℂ) * φ ξ) = -φ := by funext ξ; simp
  rwa [hfun] at hneg

/-- Differences of admissible symbols are admissible. -/
theorem Adm.sub {A : Finset Work.Analysis.IonescuWainger.Circle} {φ ψ : ℝ → ℂ}
    (h : Adm A φ) (h' : Adm A ψ) : Adm A (φ - ψ) := by
  have hfun : φ - ψ = φ + -ψ := by
    funext ξ; simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  rw [hfun]
  exact h.add h'.neg

/-- **Linear additivity of `Tm` in the symbol**, in the `Adm` form used by the assembly. -/
theorem Tm_add_of_adm {ρ : ℝ} {l : ℕ} {φ ψ : ℝ → ℂ} {f : ℤ → ℂ} {B : ℝ}
    (hB : ∀ m : ℤ, ‖f m‖ ≤ B) (h : Adm (diffFreqs ρ l) φ) (h' : Adm (diffFreqs ρ l) ψ) :
    Tm ρ l (φ + ψ) f = Tm ρ l φ f + Tm ρ l ψ f :=
  Tm_add_of_bounded l hB h.1 h'.1 h.2.1 h'.2.1 h.2.2 h'.2.2

/-- **Linear subtractivity of `Tm` in the symbol**, in the `Adm` form used by the assembly. -/
theorem Tm_sub_of_adm {ρ : ℝ} {l : ℕ} {φ ψ : ℝ → ℂ} {f : ℤ → ℂ} {B : ℝ}
    (hB : ∀ m : ℤ, ‖f m‖ ≤ B) (h : Adm (diffFreqs ρ l) φ) (h' : Adm (diffFreqs ρ l) ψ) :
    Tm ρ l (φ - ψ) f = Tm ρ l φ f - Tm ρ l ψ f := by
  have hneg : Adm (diffFreqs ρ l) (fun ξ => (-1 : ℂ) * ψ ξ) := h'.const_mul (-1)
  have hsum := Tm_add_of_adm (ρ := ρ) (l := l) (f := f) hB h hneg
  have hcm := Tm_const_mul (ρ := ρ) l (-1 : ℂ) (φ := ψ) (f := f)
  have hfun : φ + (fun ξ => (-1 : ℂ) * ψ ξ) = φ - ψ := by
    funext ξ; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hfun] at hsum
  rw [hsum, hcm]
  funext n
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

end

end Work.KMTAreas.A7
