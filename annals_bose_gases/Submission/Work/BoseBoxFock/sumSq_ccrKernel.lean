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
# `Work.BoseBoxFock.sumSq_ccrKernel` — the box kernel as a sum of squares

The Gram quadratic form of FS's localised plane waves `qVec ℓ k = Q(e^{ikx}χ_Λ)`
(`Work.BoseB4.BoxData.qVec`) is the squared `L²(Λ)`-norm of their superposition: for
real coefficients `x`,

`ℓ³ · Σ i Σ j, x i x j (χ̂²(ℓ(K i − K j)) − χ̂(ℓK i)χ̂(ℓK j))
   = ∫ y, ‖Σ i x i · qVec ℓ (K i) y‖²`.

The kernel on the left is FS `eq:Commutator_general` in the form of
`Work.BoseB7.ccrKernel` (`Work.BoseB4.BoxData.boxKernel`), so this is the statement that
the `ℓ³`-scaled box kernel is the Gram matrix of the honest `L²(ℂ)` vectors — the `L²`
half of the identification `HonestModes.hf` of the box↔Fock design
(`BOSE_BOXFOCK_LEAD.md` §3, "the θ/χ Gram is *derived* from the physical vectors").

The two ingredients:

* `Work.BoseB4.realIP_qVec_qVec` (FS `eq:Commutator_general`, proved): each Gram entry is
  `ℓ³` times the kernel, `realIP (qVec ℓ k) (qVec ℓ k') = ℓ³ · boxKernel ℓ k k'`;
* `sum_realIP_eq_integral_normSq` (proved below): the double sum of the pairwise real inner
  products `∫ Re(conj f_p · f_q)` is the integral of `‖Σ_p c_p f_p‖²` — the finite sums are
  pulled out of the integral and the pointwise identity
  `Complex.normSq (Σ_i c_i z_i) = Σ_i Σ_j c_i c_j Re(conj z_i · z_j)`
  (`Work.BoseB4.normSq_sum_ofReal_mul`) is applied.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

/-- **The Gram quadratic form of a finite family of `L²(ℂ)` vectors is the squared norm of
its superposition.**  For real coefficients `c` and a finite family `f` whose pairwise
integrands are integrable,

`Σ p Σ q, c p c q · realIP (f p) (f q) = ∫ x, Complex.normSq (Σ p, (c p : ℂ) · f p x)`.

This is the identity behind `Work.BoseB4.realIP_sum_sum_nonneg` (which keeps only the
nonnegativity of the left-hand side), upgraded to the exact value of the form. -/
lemma sum_realIP_eq_integral_normSq (B : Work.BoseB4.BoxData) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : ι → ℝ³ → ℂ) (c : ι → ℝ)
    (hint : ∀ p q : ι, Integrable fun x => ((starRingEnd ℂ) (f p x) * f q x).re) :
    (∑ p, ∑ q, c p * c q * B.realIP (f p) (f q))
      = ∫ x, Complex.normSq (∑ p, (c p : ℂ) * f p x) := by
  simp only [Work.BoseB4.BoxData.realIP_apply]
  -- Pull the two finite sums out of the integral.
  have hswap : (∑ p, ∑ q, c p * c q * ∫ x, ((starRingEnd ℂ) (f p x) * f q x).re)
      = ∫ x, ∑ p, ∑ q, c p * c q * ((starRingEnd ℂ) (f p x) * f q x).re := by
    have h1 : ∀ p, (∑ q, c p * c q * ∫ x, ((starRingEnd ℂ) (f p x) * f q x).re)
        = ∫ x, ∑ q, (c p * c q) * ((starRingEnd ℂ) (f p x) * f q x).re := by
      intro p
      have hq : ∀ q, c p * c q * ∫ x, ((starRingEnd ℂ) (f p x) * f q x).re
          = ∫ x, (c p * c q) * ((starRingEnd ℂ) (f p x) * f q x).re := by
        intro q
        rw [MeasureTheory.integral_const_mul]
      rw [Finset.sum_congr rfl (fun q _ => hq q)]
      exact Work.BoseB4.sum_integral_eq_integral_sum _
        (fun q => (hint p q).const_mul (c p * c q))
    have h2 := Work.BoseB4.sum_integral_eq_integral_sum
      (fun p x => ∑ q, (c p * c q) * ((starRingEnd ℂ) (f p x) * f q x).re)
      (fun p => MeasureTheory.integrable_finsetSum Finset.univ
        (fun q _ => (hint p q).const_mul (c p * c q)))
    rw [Finset.sum_congr rfl (fun p _ => h1 p), h2]
  rw [hswap]
  -- Identify the integrand with the nonnegative `normSq` of the combination.
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x =>
    (Work.BoseB4.normSq_sum_ofReal_mul (fun p => f p x) c).symm))

/-- **FS `eq:Commutator_general` as a sum of squares.**  For real coefficients `c` and
labels `k`, the `ℓ³`-scaled box kernel quadratic form of the localised plane waves
`qVec ℓ (k i)` is the `L²(Λ)`-norm squared of their superposition. -/
lemma sumSq_boxKernel_eq_integral (B : Work.BoseB4.BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℝ³) (c : ι → ℝ) :
    ℓ ^ 3 * (∑ i, ∑ j, c i * c j * B.boxKernel ℓ (k i) (k j))
      = ∫ y, Complex.normSq (∑ i, (c i : ℂ) * B.qVec ℓ (k i) y) := by
  have hIP := sum_realIP_eq_integral_normSq B (fun i => B.qVec ℓ (k i)) c
    (fun i j => B.integrable_conj_qVec_qVec hℓ (k i) (k j))
  have h2 : (∑ i, ∑ j, c i * c j * B.realIP (B.qVec ℓ (k i)) (B.qVec ℓ (k j)))
      = ℓ ^ 3 * (∑ i, ∑ j, c i * c j * B.boxKernel ℓ (k i) (k j)) := by
    have hroot : ∀ i j, B.realIP (B.qVec ℓ (k i)) (B.qVec ℓ (k j))
        = ℓ ^ 3 * B.boxKernel ℓ (k i) (k j) :=
      fun i j => Work.BoseB4.realIP_qVec_qVec B hℓ (k i) (k j)
    simp only [hroot]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  exact h2.symm.trans hIP

/-- **The box kernel of the corpus χ is the `L²` Gram form of the localised plane waves.**
`ℓ³` times the quadratic form of `Work.BoseB7.ccrKernel` at the labels `K` is the squared
`L²(Λ)`-norm of `Σ_i x_i Q(e^{i K_i x}χ_Λ)`. -/
theorem sumSq_ccrKernel (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (K : Lab N → ℝ³) (x : Lab N → ℝ) :
    ℓ ^ 3 * (∑ i, ∑ j, x i * x j *
        Work.BoseB7.ccrKernel ℓ Work.BoseK15.corpusBox.hatChiSq Work.BoseK15.corpusBox.hatChi (K i) (K j))
      = ∫ y, Complex.normSq (∑ i, (x i : ℂ) * Work.BoseK15.corpusBox.qVec ℓ (K i) y) := by
  have hk : ∀ i j : Lab N,
      Work.BoseB7.ccrKernel ℓ Work.BoseK15.corpusBox.hatChiSq
          Work.BoseK15.corpusBox.hatChi (K i) (K j)
        = Work.BoseK15.corpusBox.boxKernel ℓ (K i) (K j) :=
    fun i j => by
      simp only [Work.BoseB7.ccrKernel, Work.BoseB4.BoxData.boxKernel]
  simp only [hk]
  exact sumSq_boxKernel_eq_integral Work.BoseK15.corpusBox hℓ K x

end Work.BoseBoxFock
