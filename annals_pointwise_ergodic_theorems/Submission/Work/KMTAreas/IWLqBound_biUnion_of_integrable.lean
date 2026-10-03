import Mathlib
import Submission.Work.KMTAreas.iw_family

/-!
# The `ℓ^q` Ionescu–Wainger bound on a disjoint finite union of frequency sets

`Work.Analysis.IWMultiplier.IWLqBound A Φ q C` is the assertion that the Ionescu–Wainger
multiplier with symbol `iwSymbolSet A Φ = ∑_{α ∈ A} Φ (· - α)`, acting by convolution on
`ℓ^q(ℤ; H)`, is bounded with constant `C`, uniformly over all finite dimensional Hilbert spaces
`H`.  This file proves that the bound is *finitely additive in the frequency set*: for a finite
family `A i` of pairwise disjoint frequency sets indexed by a finset `s`, if each `A i` enjoys the
bound with the same constant `C` then the union `⋃_{i ∈ s} A i = s.biUnion A` enjoys it with
constant `C * s.card`.

## The argument

Three elementary steps, none of them using any harmonic analysis beyond linearity of the Bochner
integral:

* the symbol of a disjoint union is the sum of the symbols,
  `iwSymbolSet (s.biUnion A) Φ = ∑_{i ∈ s} iwSymbolSet (A i) Φ` (`iwSymbolSet_biUnion`), which is
  `Finset.sum_biUnion` and is exactly where the disjointness hypothesis is used;
* the Fourier coefficients (= the convolution kernel) of a finite sum of symbols are the finite
  sum of the kernels, `iwKernel (∑_{i ∈ s} m i) j = ∑_{i ∈ s} iwKernel (m i) j`
  (`iwKernel_finset_sum`), i.e. linearity of `∫ fourier (-j) ξ • (∑_{i} m i ξ)`.  This is the only
  place where the integrability hypothesis is needed: `Integrable.bdd_mul` shows that multiplying
  an integrable symbol by the unimodular `fourier (-j)` stays integrable, so
  `integral_finsetSum` applies;
* hence the multiplier with frequency set `s.biUnion A` is the *sum of the multipliers*
  `iwConv (s.biUnion A) Φ f = ∑_{i ∈ s} iwConv (A i) Φ f` for every finitely supported `f`
  (`iwConv_biUnion_of_finsupp`): both sides are finite sums over the support of `f`, so this is
  just the interchange of two finite sums.

The `ℓ^q` bound then follows from the triangle inequality `eLpNorm_sum_le` (here `1 ≤ q` is used)
and the arithmetic of the constant: `∑_{i ∈ s} (C ‖f‖) = C · s.card · ‖f‖`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger (iwSymbolSet circleMeasure)
open Work.Analysis.IWMultiplier (iwKernel iwConv iwConv_apply iwConv_apply_eq_sum IWLqBound)

local notation "𝕋" => Work.Analysis.IonescuWainger.Circle

/-- **The symbol of a disjoint finite union is the sum of the symbols.**  For pairwise disjoint
frequency sets `A i` (`i ∈ s`), `∑_{α ∈ ⋃_{i ∈ s} A i} Φ (ξ - α) = ∑_{i ∈ s} ∑_{α ∈ A i} Φ (ξ - α)`
pointwise. -/
lemma iwSymbolSet_biUnion {ι : Type*} (s : Finset ι) (A : ι → Finset 𝕋)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) (Φ : 𝕋 → ℂ) :
    iwSymbolSet (s.biUnion A) Φ = fun ξ => ∑ i ∈ s, iwSymbolSet (A i) Φ ξ := by
  funext ξ
  simp only [iwSymbolSet]
  exact Finset.sum_biUnion hdisj

/-- Multiplying an integrable function on the circle by the unimodular exponential `fourier (-j)`
preserves integrability (the circle has finite measure, so `fourier (-j)` is bounded). -/
lemma integrable_fourier_smul {m : 𝕋 → ℂ} (hm : Integrable m circleMeasure) (j : ℤ) :
    Integrable (fun ξ : 𝕋 => fourier (-j) ξ • m ξ) circleMeasure := by
  have h := hm.bdd_mul (f := fun ξ : 𝕋 => fourier (-j) ξ)
    ((fourier (-j)).continuous.aestronglyMeasurable) (c := 1) ?_
  · simpa only [smul_eq_mul] using h
  · filter_upwards with ξ
    rw [fourier_apply]
    exact le_of_eq (_root_.Circle.norm_coe _)

/-- **The convolution kernel of a finite sum of symbols is the finite sum of the kernels**:
`iwKernel (∑_{i ∈ s} m i) j = ∑_{i ∈ s} iwKernel (m i) j`, by linearity of the Bochner integral
(the integrability of the summands is required, and is the reason the main theorem carries the
hypothesis `hint`). -/
lemma iwKernel_finset_sum {ι : Type*} (s : Finset ι) (m : ι → 𝕋 → ℂ)
    (hint : ∀ i ∈ s, Integrable (m i) circleMeasure) (j : ℤ) :
    iwKernel (fun ξ => ∑ i ∈ s, m i ξ) j = ∑ i ∈ s, iwKernel (m i) j := by
  have hpt : (fun ξ : 𝕋 => fourier (-j) ξ • (∑ i ∈ s, m i ξ))
      = fun ξ : 𝕋 => ∑ i ∈ s, fourier (-j) ξ • m i ξ := by
    funext ξ
    rw [Finset.smul_sum]
  rw [iwKernel, fourierCoeff, hpt, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [iwKernel, fourierCoeff]
  · intro i hi
    exact integrable_fourier_smul (hint i hi) j

/-- **The multiplier of a disjoint finite union is the sum of the multipliers**, at the level of
sequences: for every finitely supported `f`, `iwConv (⋃_{i ∈ s} A i) Φ f = ∑_{i ∈ s} iwConv (A i) Φ f`
pointwise.  Both sides are finite sums over the support of `f`, so this is the interchange of two
finite sums after `iwKernel_finset_sum`. -/
lemma iwConv_biUnion_of_finsupp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (s : Finset ι) (A : ι → Finset 𝕋) (Φ : 𝕋 → ℂ) (f : ℤ → H)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j))
    (hint : ∀ i ∈ s, Integrable (iwSymbolSet (A i) Φ) circleMeasure)
    (hsupp : (Function.support f).Finite) (n : ℤ) :
    iwConv (s.biUnion A) Φ f n = ∑ i ∈ s, iwConv (A i) Φ f n := by
  classical
  have hv : ∀ m : ℤ, m ∉ hsupp.toFinset → f m = 0 := fun m hm => by
    by_contra hne
    exact hm (hsupp.mem_toFinset.mpr hne)
  rw [iwConv_apply_eq_sum (s.biUnion A) Φ f hsupp.toFinset hv n]
  have hker : ∀ m : ℤ, iwKernel (iwSymbolSet (s.biUnion A) Φ) (n - m)
      = ∑ i ∈ s, iwKernel (iwSymbolSet (A i) Φ) (n - m) := by
    intro m
    rw [iwSymbolSet_biUnion s A hdisj Φ]
    exact iwKernel_finset_sum s (fun i => iwSymbolSet (A i) Φ) hint (n - m)
  calc ∑ m ∈ hsupp.toFinset, iwKernel (iwSymbolSet (s.biUnion A) Φ) (n - m) • f m
      = ∑ m ∈ hsupp.toFinset,
          (∑ i ∈ s, iwKernel (iwSymbolSet (A i) Φ) (n - m)) • f m :=
        Finset.sum_congr rfl fun m _ => by rw [hker m]
    _ = ∑ m ∈ hsupp.toFinset,
          ∑ i ∈ s, iwKernel (iwSymbolSet (A i) Φ) (n - m) • f m :=
        Finset.sum_congr rfl fun m _ => by rw [Finset.sum_smul]
    _ = ∑ i ∈ s,
          ∑ m ∈ hsupp.toFinset, iwKernel (iwSymbolSet (A i) Φ) (n - m) • f m :=
        Finset.sum_comm
    _ = ∑ i ∈ s, iwConv (A i) Φ f n :=
        Finset.sum_congr rfl fun i _ =>
          (iwConv_apply_eq_sum (A i) Φ f hsupp.toFinset hv n).symm

/-- **The `ℓ^q` Ionescu–Wainger bound is additive over disjoint frequency sets.**  If each of the
pairwise disjoint frequency sets `A i` (`i ∈ s`) satisfies the `ℓ^q` bound with constant `C` and
the corresponding symbols are integrable, then the union `s.biUnion A` satisfies the bound with
constant `C * s.card`. -/
theorem IWLqBound_biUnion_of_integrable {ι : Type*} (s : Finset ι)
    (A : ι → Finset Work.Analysis.IonescuWainger.Circle)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j))
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hint : ∀ i ∈ s, MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (A i) Φ)
      Work.Analysis.IonescuWainger.circleMeasure)
    {q : ENNReal} (hq : 1 ≤ q) {C : NNReal}
    (h : ∀ i ∈ s, Work.Analysis.IWMultiplier.IWLqBound (A i) Φ q C) :
    Work.Analysis.IWMultiplier.IWLqBound (s.biUnion A) Φ q (C * s.card) := by
  classical
  intro H _ _ _ f hf
  have hsplit := iwConv_biUnion_of_finsupp s A Φ f hdisj hint hf
  have heq : eLpNorm (iwConv (s.biUnion A) Φ f) q Measure.count
      = eLpNorm (∑ i ∈ s, fun n : ℤ => iwConv (A i) Φ f n) q Measure.count := by
    rw [show iwConv (s.biUnion A) Φ f = fun n : ℤ => ∑ i ∈ s, iwConv (A i) Φ f n
      from funext hsplit]
    congr 1
    funext n
    exact (Finset.sum_apply (s := s) n (fun i n => iwConv (A i) Φ f n)).symm
  rw [heq]
  have hcoe : ((C * s.card : NNReal) : ℝ) = (C : ℝ) * (s.card : ℝ) := by
    push_cast
    ring
  calc eLpNorm (∑ i ∈ s, fun n : ℤ => iwConv (A i) Φ f n) q Measure.count
      ≤ ∑ i ∈ s, eLpNorm (fun n : ℤ => iwConv (A i) Φ f n) q Measure.count :=
        eLpNorm_sum_le hq
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (C : ℝ) * eLpNorm f q Measure.count :=
        Finset.sum_le_sum fun i hi => h i hi H f hf
    _ = ENNReal.ofReal ((C * s.card : NNReal) : ℝ) * eLpNorm f q Measure.count := by
        rw [Finset.sum_const, nsmul_eq_mul, hcoe,
          ENNReal.ofReal_mul (show (0:ℝ) ≤ (C : ℝ) by positivity), ENNReal.ofReal_natCast]
        ring

end Work.KMTAreas
