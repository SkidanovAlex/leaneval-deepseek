import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ShiftArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.BandLimitedL2Ortho
import Submission.Work.BourgainPlan.IonescuWainger.sigmaA_petal_sum_shift_perturbed_ne_zero
import Submission.Work.BourgainPlan.IonescuWainger.tsum_prod_mul_conj_eq_zero_of_freqSupport

/-!
# Tao's `ortho`(iii) with a core: the Pythagoras step of `ortho-apply`(i)

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Lemma `ortho`(iii) *with core* and Theorem `ortho-apply`(i).

`BandLimitedL2Ortho.tsum_prod_mul_conj_eq_zero_of_petal_l2` is Tao's `ortho`(iii) in the degenerate
case in which the sunflower's core `A₀` is empty, i.e. for the products `∏_i f_{α_i}`.  The proof of
Theorem `ortho-apply`(i) needs the general statement, for the products of the *shifted* major-arc
functions `f_{Σ_{A₀} + α_i} = Σ_{γ ∈ Σ_{A₀}} f_{γ + α_i}`: the sunflowers appearing there have core
`A₀` and petals `A_i \ A₀`.

The only extra input is arithmetic: the frequency support of `f_{Σ_{A₀} + α}` is the shifted arc
`Σ_{⊆A₀} + α + [-ε,ε]` (`ShiftArcDefs.hasFreqSupport_majorArc_shift`), and the Minkowski sums of
these shifted arcs are disjoint as soon as the `α_i` differ from the `β_i` in at least one coordinate
(`disjoint_setSumFin_shiftArcSet_of_petal`, from the arithmetic core
`sigmaA_petal_sum_shift_perturbed_ne_zero`).

## Main declarations

* `disjoint_setSumFin_shiftArcSet_of_petal` — the shifted-arc disjointness (frequency side);
* `tsum_prod_shift_mul_conj_eq_zero_of_disjoint` — the abstract pairing form;
* `tsum_prod_shift_mul_conj_eq_zero_of_petal_l2` — **Tao's `ortho`(iii) with core**, band-limited
  `ℓ²` form: the shifted major-arc products `∏_i f_{Σ_{A₀} + α_i}` are pairwise orthogonal in
  `ℓ²(ℤ)` whenever the tuples `(α_i)` and `(β_i)` differ in at least one coordinate.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **Disjointness of the Minkowski sums of shifted arcs** (Tao's `ortho`(iii) with core, frequency
side).  For pairwise disjoint petals `P i` and a core `A₀` disjoint from each `P i`, points
`α i, β i ∈ Σ_{P i}` differing in at least one coordinate, and
`2·(n+1)·ε·Q_{A₀}·∏_i Q_{P i} < 1`, the Minkowski sums of the shifted arcs
`Σ_{⊆A₀} + α i + [-ε,ε]` and `Σ_{⊆A₀} + β i + [-ε,ε]` are disjoint. -/
theorem disjoint_setSumFin_shiftArcSet_of_petal {n : ℕ} {S A₀ : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : Fin (n + 1) → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {α β : Fin (n + 1) → Circle} (hα : ∀ i, α i ∈ sigmaA (P i))
    (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i) {ε : ℝ}
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε * ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) < 1) :
    Disjoint (setSumFin (n + 1) (fun i => shiftArcSet (sigmaSubA A₀) (α i) ε))
      (setSumFin (n + 1) (fun i => shiftArcSet (sigmaSubA A₀) (β i) ε)) := by
  rw [Set.disjoint_left]
  intro ξ h1 h2'
  rw [mem_setSumFin_shiftArcSet] at h1 h2'
  obtain ⟨γ, hγ, θ, hθ, hsum1⟩ := h1
  obtain ⟨δ, hδ, θ', hθ', hsum2⟩ := h2'
  refine sigmaA_petal_sum_shift_perturbed_ne_zero h2 hS hA₀ hP hdisjP hdisjA hα hβ hne hγ hδ
    hθ hθ' (by simpa using hsmall) ?_
  rw [Finset.sum_sub_distrib, hsum1, hsum2, sub_self]

/-- **The pairing of two products of shifted major-arc functions vanishes when the Minkowski sums
of the shifted arcs are disjoint.**  Abstract form: only the band-limitation of the system `f` and
the disjointness of the two families of shifted arcs are assumed. -/
theorem tsum_prod_shift_mul_conj_eq_zero_of_disjoint {n : ℕ} {A₀ : Finset ℕ}
    {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
    {α β : Fin (n + 1) → Circle}
    (hdisj : Disjoint (setSumFin (n + 1) (fun i => shiftArcSet (sigmaSubA A₀) (α i) ε))
      (setSumFin (n + 1) (fun i => shiftArcSet (sigmaSubA A₀) (β i) ε))) :
    ∑' m : ℤ, (∏ i, (∑ γ ∈ sigmaAFinset A₀, f (γ + α i) m))
      * star (∏ i, (∑ γ ∈ sigmaAFinset A₀, f (γ + β i) m)) = 0 :=
  tsum_prod_mul_conj_eq_zero_of_freqSupport
    (fun i => fun m => ∑ γ ∈ sigmaAFinset A₀, f (γ + α i) m)
    (fun i => fun m => ∑ γ ∈ sigmaAFinset A₀, f (γ + β i) m)
    (fun i => Memℓp.finsetSum (sigmaAFinset A₀) (fun γ _ => hf (γ + α i)))
    (fun i => Memℓp.finsetSum (sigmaAFinset A₀) (fun γ _ => hf (γ + β i)))
    (fun i => shiftArcSet (sigmaSubA A₀) (α i) ε)
    (fun i => shiftArcSet (sigmaSubA A₀) (β i) ε)
    (fun i => hasFreqSupport_majorArc_shift hf hF (α i))
    (fun i => hasFreqSupport_majorArc_shift hf hF (β i)) hdisj

/-- **Tao's `ortho`(iii) with core, for band-limited `ℓ²` systems.**  If the petals `P i` are
pairwise disjoint and disjoint from the core `A₀`, if `α i, β i ∈ Σ_{P i}` differ in at least one
coordinate, and if `2·(n+1)·ε·Q_{A₀}·∏_i Q_{P i} < 1`, then the shifted major-arc products
`∏_i f_{Σ_{A₀} + α_i}` and `∏_i f_{Σ_{A₀} + β_i}` are orthogonal in `ℓ²(ℤ)`:

`Σ_m ∏_i f_{Σ_{A₀}+α_i}(m) · conj (∏_i f_{Σ_{A₀}+β_i}(m)) = 0`.

This is the Pythagoras step of the proof of Tao's Theorem `ortho-apply`(i). -/
theorem tsum_prod_shift_mul_conj_eq_zero_of_petal_l2 {n : ℕ} {S A₀ : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : Fin (n + 1) → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
    {α β : Fin (n + 1) → Circle} (hα : ∀ i, α i ∈ sigmaA (P i))
    (hβ : ∀ i, β i ∈ sigmaA (P i)) (hne : ∃ i, α i ≠ β i)
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε * ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) < 1) :
    ∑' m : ℤ, (∏ i, (∑ γ ∈ sigmaAFinset A₀, f (γ + α i) m))
      * star (∏ i, (∑ γ ∈ sigmaAFinset A₀, f (γ + β i) m)) = 0 :=
  tsum_prod_shift_mul_conj_eq_zero_of_disjoint hf hF
    (disjoint_setSumFin_shiftArcSet_of_petal h2 hS hA₀ hP hdisjP hdisjA hα hβ hne hsmall)

end Work.BourgainPlan.IonescuWainger
