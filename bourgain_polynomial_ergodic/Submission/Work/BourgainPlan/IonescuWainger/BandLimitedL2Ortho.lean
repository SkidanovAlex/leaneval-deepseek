import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.BourgainPlan.IonescuWainger.tsum_prod_mul_conj_eq_zero_of_freqSupport

/-!
# Tao's `ortho`(ii)/(iii) for band-limited `ℓ²` major-arc systems

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Lemma `ortho`(ii) denominator orthogonality and `ortho`(iii) numerator orthogonality).

This file is the capstone of this lane: it combines

* the band-limited orthogonality `tsum_prod_mul_conj_eq_zero_of_freqSupport` (the `ℓ²(ℤ) ≅ L²(𝕋)`
  form of the pairing identity, in which the frequency supports are genuine measurable subsets of
  the circle) with
* the *arithmetic* disjointness criteria of `FreqArc.lean`
  (`disjoint_setSumFin_arcSet_of_nonce`, `disjoint_setSumFin_arcSet_of_petal`, and the
  `(r,c)`-good forms),

to obtain Tao's `ortho`(ii)/(iii) for **genuine band-limited major-arc systems**: functions
`f j ∈ ℓ²(ℤ)` whose Fourier transforms are supported in the arcs `arcSet (α j) ε` around the arc
points `α j ∈ Σ_{A j}`.

This is exactly the hypothesis consumed by `superorthogonal_khintchine_hypersystem` (via
`sys-ortho`(ii)) in the proof of the Ionescu–Wainger multiplier theorem.
-/

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

/-- **Tao's `ortho`(ii) for band-limited `ℓ²` systems.**  Same conclusion as
`tsum_prod_mul_conj_eq_zero_of_nonce` / `_l1`, but for `ℓ²` functions satisfying the (a.e.)
band-limitation hypothesis `HasFreqSupport`. -/
theorem tsum_prod_mul_conj_eq_zero_of_nonce_l2 {n : ℕ} {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ} (hA : ∀ j, A j ⊆ S) (hnonce : HasNonce A)
    {f : Fin (n + 1) ⊕ Fin (n + 1) → ℤ → ℂ} (hf : ∀ j, Memℓp (f j) 2)
    {α β : Fin (n + 1) → Circle} (hα : ∀ i, α i ∈ sigmaA (A (Sum.inl i)))
    (hβ : ∀ i, β i ∈ sigmaA (A (Sum.inr i))) {ε : ℝ}
    (hF : ∀ i, HasFreqSupport (f (Sum.inl i)) (hf (Sum.inl i)) (arcSet (α i) ε))
    (hG : ∀ i, HasFreqSupport (f (Sum.inr i)) (hf (Sum.inr i)) (arcSet (β i) ε))
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)) :
    ∑' m : ℤ, (∏ i, f (Sum.inl i) m) * star (∏ i, f (Sum.inr i) m) = 0 :=
  tsum_prod_mul_conj_eq_zero_of_freqSupport (fun i => f (Sum.inl i)) (fun i => f (Sum.inr i))
    (fun i => hf (Sum.inl i)) (fun i => hf (Sum.inr i))
    (fun i => arcSet (α i) ε) (fun i => arcSet (β i) ε) hF hG
    (disjoint_setSumFin_arcSet_of_nonce h2 hS hA hnonce hα hβ hsmall)

/-- **Tao's `ortho`(iii) for band-limited `ℓ²` systems** (numerator orthogonality, sunflower
petals). -/
theorem tsum_prod_mul_conj_eq_zero_of_petal_l2 {n : ℕ} {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {P : Fin (n + 1) → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisj : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (P i) (P j))
    {f g : Fin (n + 1) → ℤ → ℂ} (hf : ∀ i, Memℓp (f i) 2) (hg : ∀ i, Memℓp (g i) 2)
    {α β : Fin (n + 1) → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i) {ε : ℝ}
    (hF : ∀ i, HasFreqSupport (f i) (hf i) (arcSet (α i) ε))
    (hG : ∀ i, HasFreqSupport (g i) (hg i) (arcSet (β i) ε))
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε < 1 / ((∏ i, QA (P i) : ℕ) : ℝ)) :
    ∑' m : ℤ, (∏ i, f i m) * star (∏ i, g i m) = 0 :=
  tsum_prod_mul_conj_eq_zero_of_freqSupport f g hf hg (fun i => arcSet (α i) ε)
    (fun i => arcSet (β i) ε) hF hG
    (disjoint_setSumFin_arcSet_of_petal h2 hS hP hdisj hα hβ hne hsmall)

/-- Tao's `ortho`(iii) in the `(r,c)`-**good** parameterisation, for band-limited `ℓ²` systems. -/
theorem tsum_prod_mul_conj_eq_zero_of_petal_l2_of_good {n : ℕ} {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {P : Fin (n + 1) → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisj : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (P i) (P j))
    {f g : Fin (n + 1) → ℤ → ℂ} (hf : ∀ i, Memℓp (f i) 2) (hg : ∀ i, Memℓp (g i) 2)
    {α β : Fin (n + 1) → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i) {ε c : ℝ} {k' qmax : ℕ}
    (hPcard : ∀ i, (P i).card ≤ k') (hmax : ∀ q ∈ S, q ≤ qmax)
    (hc : 0 < c) (hc1 : c < 1)
    (hgood : ε < c / (2 * (n + 1) * (qmax : ℝ) ^ (2 * (n + 1) * k')))
    (hF : ∀ i, HasFreqSupport (f i) (hf i) (arcSet (α i) ε))
    (hG : ∀ i, HasFreqSupport (g i) (hg i) (arcSet (β i) ε)) :
    ∑' m : ℤ, (∏ i, f i m) * star (∏ i, g i m) = 0 :=
  tsum_prod_mul_conj_eq_zero_of_freqSupport f g hf hg (fun i => arcSet (α i) ε)
    (fun i => arcSet (β i) ε) hF hG
    (disjoint_setSumFin_arcSet_of_petal_of_good h2 hS hP hdisj hα hβ hne hPcard hmax hc hc1 hgood)

end Work.BourgainPlan.IonescuWainger
