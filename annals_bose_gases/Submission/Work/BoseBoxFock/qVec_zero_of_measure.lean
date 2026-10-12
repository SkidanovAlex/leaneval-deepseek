import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.qVec_zero_of_measure`

If a finite real combination `Σ_i x_i · qVec ℓ (K i)` of the localised plane waves with the
condensate removed (`qVec ℓ k = e^{ikx}χ_Λ − χ̂(ℓk)·θ`, `Work.BoseB4.BoxData.qVec`) has zero
`L²`-norm, then its value on any positive-measure set `B` must vanish.  On `B` the combination
is the *constant* `−Σ_i x_i χ̂(ℓ·K i)`: there `χ_Λ = 0` (so every `e^{ikx}χ_Λ` vanishes) and
`θ = 1`.  Zero `L²`-norm makes the combination vanish almost everywhere, hence at some point of
`B`, and a nonzero constant cannot vanish on a positive-measure set.

The mathematical content of the lemma is therefore the implication
`∫ ‖Σ_i x_i qVec_i‖² = 0 → Σ_i x_i χ̂(ℓ K i) = 0`, with the `L²`-integrability of the
integrand supplied by `Work.BoseB4.BoxData.integrable_conj_qVec_qVec` (the Bochner integral is
total, so `∫ ‖F‖² = 0` alone would also hold for a non-integrable `F`).
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

/-- The real part of a conjugated product is bilinear over real scalars: this is the
`Fin 3`-indexed bookkeeping lemma that lets `Complex.normSq` of a real combination be pushed
inside a `Finset.sum`. -/
private lemma re_conj_mul_smul (a b : ℝ) (u v : ℂ) :
    (starRingEnd ℂ ((a : ℂ) * u) * ((b : ℂ) * v)).re = a * b * (starRingEnd ℂ u * v).re := by
  have h : starRingEnd ℂ ((a : ℂ) * u) * ((b : ℂ) * v)
      = ((a * b : ℝ) : ℂ) * (starRingEnd ℂ u * v) := by
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `Complex.normSq` of a finite real combination, expanded over pairs. -/
private lemma normSq_sum_ofReal_mul {ι : Type*} [Fintype ι] (x : ι → ℝ) (q : ι → ℂ) :
    Complex.normSq (∑ i, (x i : ℂ) * q i)
      = ∑ i, ∑ j, (x i * x j) * ((starRingEnd ℂ (q i) * q j).re) := by
  rw [← Complex.ofReal_re (Complex.normSq _), Complex.normSq_eq_conj_mul_self,
      map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact re_conj_mul_smul (x i) (x j) (q i) (q j)

theorem qVec_zero_of_measure (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (K : Lab N → ℝ³) (x : Lab N → ℝ)
    {B : Set ℝ³} (hB : MeasurableSet B) (hvol : 0 < (MeasureTheory.volume B).toReal)
    (hchi : ∀ y ∈ B, Work.BoseK15.corpusBox.chiLam ℓ y = 0)
    (htheta : ∀ y ∈ B, Work.BoseK15.corpusBox.thetaFun ℓ y = 1)
    (h : ∫ y, Complex.normSq (∑ i, (x i : ℂ) * Work.BoseK15.corpusBox.qVec ℓ (K i) y) = 0) :
    ∑ i, x i * Work.BoseK15.corpusBox.hatChi (ℓ • K i) = 0 := by
  classical
  set F : ℝ³ → ℂ := fun y => ∑ i, (x i : ℂ) * Work.BoseK15.corpusBox.qVec ℓ (K i) y with hFdef
  set S : ℝ := ∑ i, x i * Work.BoseK15.corpusBox.hatChi (ℓ • K i) with hSdef
  -- On `B` both `e^{ikx}χ_Λ` (`χ_Λ = 0`) and `θ` (`= 1`) are pinned, so `F ≡ −S` there.
  have hconst : ∀ y ∈ B, F y = -((S : ℝ) : ℂ) := by
    intro y hy
    have hq : ∀ i, Work.BoseK15.corpusBox.qVec ℓ (K i) y
        = -((Work.BoseK15.corpusBox.hatChi (ℓ • K i) : ℝ) : ℂ) := by
      intro i
      rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply, hchi y hy,
        htheta y hy]
      simp
    simp only [hFdef, hSdef, hq, mul_neg, Finset.sum_neg_distrib, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum]
  -- `‖F‖²` is an `L²`-function: each pair term is integrable
  -- (`Work.BoseB4.BoxData.integrable_conj_qVec_qVec`).
  have hpt : ∀ y, Complex.normSq (F y)
      = ∑ i, ∑ j, (x i * x j) * ((starRingEnd ℂ (Work.BoseK15.corpusBox.qVec ℓ (K i) y)
          * Work.BoseK15.corpusBox.qVec ℓ (K j) y).re) := by
    intro y
    rw [hFdef]
    exact normSq_sum_ofReal_mul x (fun i => Work.BoseK15.corpusBox.qVec ℓ (K i) y)
  have hint : Integrable (fun y => Complex.normSq (F y)) MeasureTheory.volume := by
    have hsum : Integrable (fun y => ∑ i, ∑ j, (x i * x j) *
        ((starRingEnd ℂ (Work.BoseK15.corpusBox.qVec ℓ (K i) y)
          * Work.BoseK15.corpusBox.qVec ℓ (K j) y).re)) MeasureTheory.volume := by
      refine MeasureTheory.integrable_finsetSum Finset.univ (f := fun i y => ∑ j, (x i * x j) *
        ((starRingEnd ℂ (Work.BoseK15.corpusBox.qVec ℓ (K i) y)
          * Work.BoseK15.corpusBox.qVec ℓ (K j) y).re)) ?_
      intro i _
      refine MeasureTheory.integrable_finsetSum Finset.univ (f := fun j y => (x i * x j) *
        ((starRingEnd ℂ (Work.BoseK15.corpusBox.qVec ℓ (K i) y)
          * Work.BoseK15.corpusBox.qVec ℓ (K j) y).re)) ?_
      intro j _
      exact (Work.BoseB4.BoxData.integrable_conj_qVec_qVec Work.BoseK15.corpusBox hℓ (K i)
        (K j)).const_mul (x i * x j)
    exact hsum.congr (Filter.Eventually.of_forall fun y => (hpt y).symm)
  -- zero integral (of a nonnegative integrable function) ⟹ zero a.e.
  have hzero : F =ᵐ[MeasureTheory.volume] (0 : ℝ³ → ℂ) := by
    have h1 : ∫ y, Complex.normSq (F y) = 0 := by
      rw [hFdef]
      exact h
    have h2 : (fun y => Complex.normSq (F y)) =ᵐ[MeasureTheory.volume] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg
        (fun y => Complex.normSq_nonneg (F y)) hint).mp h1
    filter_upwards [h2] with y hy
    have hy' : Complex.normSq (F y) = 0 := by simpa using hy
    exact Complex.normSq_eq_zero.mp hy'
  -- `B` has positive measure, so it meets the conull set where `F = 0`.
  have hvne : MeasureTheory.volume B ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp hvol).1.ne'
  obtain ⟨y₀, hyB, hy0⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hvne (ae_restrict_of_ae hzero)
  have h1 : F y₀ = -((S : ℝ) : ℂ) := hconst y₀ hyB
  have h2 : -((S : ℝ) : ℂ) = 0 := by rw [← h1]; exact hy0
  have hS : S = 0 := Complex.ofReal_eq_zero.mp (neg_eq_zero.mp h2)
  simpa [hSdef] using hS

end Work.BoseBoxFock
