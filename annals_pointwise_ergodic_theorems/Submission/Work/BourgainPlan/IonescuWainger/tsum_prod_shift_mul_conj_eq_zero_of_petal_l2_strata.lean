import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataArcArith
import Submission.Work.BourgainPlan.IonescuWainger.ShiftArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.tsum_prod_mul_conj_eq_zero_of_freqSupport

/-!
# Tao's `ortho`(iii) with core, for Tao's strata `Σ_A`

This file is the strata analogue of `ShiftPetalOrtho.lean`
(`tsum_prod_shift_mul_conj_eq_zero_of_petal_l2`): the major-arc system is the *strata*
`Σ_A = sigmaStrataFinset A` rather than the sets of points of exact denominator
`Σ_A = sigmaAFinset A`.  The two extra ingredients of the strata case are

* the frequency support of `Σ_{γ ∈ Σ_{A₀}} f_{γ + α}` inside the shifted arc
  `Σ_{A₀} + α + [-ε,ε]` — here the arc set is the *stratum* `Σ_{A₀}`, not the whole torsion
  subgroup `Σ_{⊆ A₀}`;
* the arithmetic disjointness of the Minkowski sums of the shifted arcs, which is
  `sigmaStrata_petal_sum_shift_perturbed_ne_zero` of `StrataArcArith.lean`.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## The frequency support of a shifted sum over a stratum -/

/-- **The frequency support of a shifted stratum sum.**  If every `f δ` is band-limited in the arc
`arcSet δ ε`, then the shifted sum `Σ_{γ ∈ Σ_{A₀}} f_{γ + α₀}` over Tao's *stratum* `Σ_{A₀}` has
frequency support in the shifted arc `Σ_{A₀} + α₀ + [-ε,ε]`. -/
theorem hasFreqSupport_shift_sigmaStrataFinset {A₀ : Finset ℕ} {f : Circle → ℤ → ℂ}
    (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε)) (α₀ : Circle) :
    HasFreqSupport (fun m => ∑ γ ∈ sigmaStrataFinset A₀, f (γ + α₀) m)
      (Memℓp.finsetSum (sigmaStrataFinset A₀) (fun γ _ => hf (γ + α₀)))
      (shiftArcSet ((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) α₀ ε) := by
  refine hasFreqSupport_mono ?_ (hasFreqSupport_finsetSum (sigmaStrataFinset A₀)
    (f := fun γ => f (γ + α₀)) (hf := fun γ => hf (γ + α₀))
    (E := fun γ => arcSet (γ + α₀) ε) (hE := fun γ => hF (γ + α₀)))
  rintro ξ hmem
  rw [Set.mem_iUnion] at hmem
  obtain ⟨γ, hmem⟩ := hmem
  rw [Set.mem_iUnion] at hmem
  obtain ⟨hγ, hmem⟩ := hmem
  rw [arcSet] at hmem
  obtain ⟨θ, hθ, hξ⟩ := hmem
  exact ⟨γ, hγ, θ, hθ, hξ⟩

/-! ## Disjointness of the Minkowski sums of shifted stratum arcs -/

/-- **Disjointness of the Minkowski sums of shifted stratum arcs** (Tao's `ortho`(iii) with core,
frequency side, strata form).  For pairwise disjoint petals `P i` and a core `A₀` disjoint from each
`P i`, points `α i, β i ∈ Σ_{P i}` of Tao's strata differing in at least one coordinate, and
`2·(n+1)·ε·Q_{A₀}·∏_i Q_{P i} < 1`, the Minkowski sums of the shifted arcs `Σ_{A₀} + α i + [-ε,ε]`
and `Σ_{A₀} + β i + [-ε,ε]` are disjoint. -/
theorem disjoint_setSumFin_shiftArcSet_of_petal_strata {n : ℕ} {S A₀ : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : Fin (n + 1) → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {α β : Fin (n + 1) → Circle}
    (hα : ∀ i, α i ∈ (sigmaStrataFinset (P i) : Set Circle))
    (hβ : ∀ i, β i ∈ (sigmaStrataFinset (P i) : Set Circle))
    (hne : ∃ i, α i ≠ β i) {ε : ℝ}
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε * ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) < 1) :
    Disjoint
      (setSumFin (n + 1)
        (fun i => shiftArcSet ((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) (α i) ε))
      (setSumFin (n + 1)
        (fun i => shiftArcSet ((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) (β i) ε)) := by
  rw [Set.disjoint_left]
  intro ξ h1 h2'
  rw [mem_setSumFin_shiftArcSet] at h1 h2'
  obtain ⟨γ, hγ, θ, hθ, hsum1⟩ := h1
  obtain ⟨δ, hδ, θ', hθ', hsum2⟩ := h2'
  refine sigmaStrata_petal_sum_shift_perturbed_ne_zero h2 hS hA₀ hP hdisjP hdisjA hα hβ hne
    hγ hδ hθ hθ' (by simpa using hsmall) ?_
  rw [Finset.sum_sub_distrib, hsum1, hsum2, sub_self]

/-! ## The abstract pairing form -/

/-- **The pairing of two products of shifted stratum sums vanishes when the Minkowski sums of the
shifted stratum arcs are disjoint.** -/
theorem tsum_prod_shift_mul_conj_eq_zero_of_disjoint_strata {n : ℕ} {A₀ : Finset ℕ}
    {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
    {α β : Fin (n + 1) → Circle}
    (hdisj : Disjoint
      (setSumFin (n + 1)
        (fun i => shiftArcSet ((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) (α i) ε))
      (setSumFin (n + 1)
        (fun i => shiftArcSet ((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) (β i) ε))) :
    ∑' m : ℤ, (∏ i, (∑ γ ∈ sigmaStrataFinset A₀, f (γ + α i) m))
      * star (∏ i, (∑ γ ∈ sigmaStrataFinset A₀, f (γ + β i) m)) = 0 :=
  tsum_prod_mul_conj_eq_zero_of_freqSupport
    (fun i => fun m => ∑ γ ∈ sigmaStrataFinset A₀, f (γ + α i) m)
    (fun i => fun m => ∑ γ ∈ sigmaStrataFinset A₀, f (γ + β i) m)
    (fun i => Memℓp.finsetSum (sigmaStrataFinset A₀) (fun γ _ => hf (γ + α i)))
    (fun i => Memℓp.finsetSum (sigmaStrataFinset A₀) (fun γ _ => hf (γ + β i)))
    (fun i => shiftArcSet ((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) (α i) ε)
    (fun i => shiftArcSet ((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) (β i) ε)
    (fun i => hasFreqSupport_shift_sigmaStrataFinset hf hF (α i))
    (fun i => hasFreqSupport_shift_sigmaStrataFinset hf hF (β i)) hdisj

/-! ## Tao's `ortho`(iii) with core, strata form -/

/-- Tao's `ortho`(iii) *with core*, band-limited `ℓ²` form, stated for Tao's strata
(`Σ_A = sigmaStrataFinset A`): for pairwise disjoint petals `P i ⊆ S` and a core `A₀ ⊆ S` disjoint
from each petal, stratum points `α i, β i ∈ Σ_{P i}` differing in at least one coordinate, and the
per-tuple smallness `2 (n+1) ε Q_{A₀} ∏_i Q_{P i} < 1`, the shifted major-arc tuple products are
orthogonal in `ℓ²(ℤ)`.

Route: port `Work.BourgainPlan.IonescuWainger.tsum_prod_shift_mul_conj_eq_zero_of_petal_l2`
(`ShiftPetalOrtho.lean`) verbatim, replacing `sigmaAFinset` by `sigmaStrataFinset` everywhere.  The
three ingredients are (a) the frequency support of the shifted sums
`fun m => ∑ γ ∈ sigmaStrataFinset A₀, f (γ + α₀) m` inside
`shiftArcSet ((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) α₀ ε`, from
`hasFreqSupport_finsetSum` and
`((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) ⊆ sigmaSubA A₀` (unfold both Finsets, as in
`ShiftArcDefs.sigmaAFinset_subset_sigmaSubA`); (b) the strata disjointness of the Minkowski sums
`setSumFin (n+1) (fun i => shiftArcSet ((sigmaStrataFinset A₀ : Finset Circle) : Set Circle) (α i) ε)`
and its `β` counterpart, from `mem_setSumFin_shiftArcSet` and
`Work.BourgainPlan.IonescuWainger.sigmaStrata_petal_sum_shift_perturbed_ne_zero`
(`StrataArcArith.lean`, proved, whose hypotheses are exactly these); (c) the abstract pairing
`tsum_prod_mul_conj_eq_zero_of_freqSupport`. -/
theorem tsum_prod_shift_mul_conj_eq_zero_of_petal_l2_strata {n : ℕ} {S A₀ : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : Fin (n + 1) → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {f : Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, Work.BourgainPlan.IonescuWainger.HasFreqSupport (f δ) (hf δ)
      (Work.BourgainPlan.IonescuWainger.arcSet δ ε))
    {α β : Fin (n + 1) → Work.BourgainPlan.IonescuWainger.Circle}
    (hα : ∀ i, α i ∈ (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset (P i) :
      Set Work.BourgainPlan.IonescuWainger.Circle))
    (hβ : ∀ i, β i ∈ (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset (P i) :
      Set Work.BourgainPlan.IonescuWainger.Circle))
    (hne : ∃ i, α i ≠ β i)
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε * ((Work.BourgainPlan.IonescuWainger.QA A₀ *
      (∏ i, Work.BourgainPlan.IonescuWainger.QA (P i)) : ℕ) : ℝ) < 1) :
    ∑' m : ℤ,
      (∏ i, (∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀, f (γ + α i) m))
        * star (∏ i, (∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀,
            f (γ + β i) m)) = 0 :=
  tsum_prod_shift_mul_conj_eq_zero_of_disjoint_strata hf hF
    (disjoint_setSumFin_shiftArcSet_of_petal_strata h2 hS hA₀ hP hdisjP hdisjA hα hβ hne hsmall)

end Work.BourgainPlan.IonescuWainger
