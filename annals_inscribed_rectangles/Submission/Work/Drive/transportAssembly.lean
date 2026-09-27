import Mathlib
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.fibreMeet_ncard_eq_sum_diamMeet
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.collapseT4defs

/-!
# The parity assembly of the radial-collapse transport (T6)

`TRANSPORT_COLLAPSE_STATUS.md` §7.8 item 4: with all the *parity ingredients* of T6 on disk
(`colCount_zero_eq_topBdryMeet` for `K(0)`, `even_ncard_pairMeetBdry` for `K(0) + K(1)` even,
`colMeet_one_ncard_eq_fibreMeet` for `K(1)`, `fibreMeet_ncard_eq_sum_diamMeet` for the fibre sum, and
T5 — `odd_ncard_arcMeet_iff_core` — for the parity of each summand), what remains is the bookkeeping
that turns them into the transport

> `Odd n_P ↔ Odd (coreSideCount Q c P₁) ∧ Odd (coreSideCount Q c P₂)`.

This file does that bookkeeping:

* `odd_finset_sum_of_const_parity` — a finite sum of naturals all of whose summands have the same
  parity is odd iff both the number of summands and the common parity are odd;
* `odd_sum_diamMeet_iff` — its instance for the fibre sum, using
  `(coreMeet Q c P₁).ncard = coreSideCount Q c P₁`;
* `odd_ncard_of_even_colCount` — **the assembly**: from the two endpoint identifications
  (`K 0 = N`, `K 1 = #fibreMeet`), the fibre decomposition
  (`fibreMeet_ncard_eq_sum_diamMeet`, with its finiteness and basepoint hypotheses) and the two parity
  facts (`Even (K 0 + K 1)`, and the uniform parity of the diameter meets), the transport follows.

The result is the exact conclusion the design's `hdense` consumes (Hugelmeyer's Lemma 2 in the form
`n_P ≡ ε_Q · ε_R`).
-/

set_option autoImplicit false

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The parity of a sum of summands of constant parity -/

/-- **A finite sum of naturals of constant parity.**  If every summand in `s` has the parity of `c`,
then the sum is odd exactly when both the number of summands and `c` are odd. -/
lemma odd_finset_sum_of_const_parity {α : Type*} (s : Finset α) (f : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ s, Odd (f x) ↔ Odd c) :
    Odd (∑ x ∈ s, f x) ↔ Odd s.card ∧ Odd c := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  by_cases hc : Odd c
  · have hset : {x ∈ s | Odd (f x)} = s := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, (h x hx).mpr hc⟩⟩
    rw [hset]
    exact ⟨fun h => ⟨h, hc⟩, fun h => h.1⟩
  · have hset : {x ∈ s | Odd (f x)} = ∅ := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_filter] at hx
        exact absurd ((h x hx.1).mp hx.2) hc
      · intro hx
        exact absurd hx (Finset.notMem_empty x)
    rw [hset, Finset.card_empty]
    refine ⟨fun h => absurd h ?_, fun h => absurd h.2 hc⟩
    simp [Nat.odd_iff]

/-! ## 2. The fibre sum -/

/-- **The parity of the fibre sum.**  If the diameter meet count has the same parity for every angle
`t` — which is exactly T5's conclusion, `Odd (diamMeet Q t W) ↔ Odd (coreSideCount Q c P₂)` — then the
sum of the diameter meet counts over the core meets is odd exactly when the two side values are odd. -/
theorem odd_sum_diamMeet_iff {Q : ℂ → CappingSpace} {c : ℝ}
    {P₁ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {c₂ : ℝ} {P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hfin : (coreMeet Q c P₁).Finite)
    (hpar : ∀ t : ℝ, Odd (diamMeet Q t W).ncard ↔ Odd (coreSideCount Q c₂ P₂)) :
    Odd (∑ q ∈ hfin.toFinset, (diamMeet Q q.1 W).ncard)
      ↔ Odd (coreSideCount Q c P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
  rw [odd_finset_sum_of_const_parity hfin.toFinset (fun q => (diamMeet Q q.1 W).ncard)
    (coreSideCount Q c₂ P₂) (fun q _ => hpar q.1)]
  have hcard : hfin.toFinset.card = coreSideCount Q c P₁ := by
    rw [← Set.ncard_eq_toFinset_card (coreMeet Q c P₁) hfin]
    rfl
  rw [hcard]

/-! ## 3. The assembly -/

/-- **The parity assembly of the transport.**  With

* `h0` — the identification of the `s = 0` collapsed count with the plane/sweep triple count
  (`colCount_zero_eq_topBdryMeet`),
* `h1` — the identification of the `s = 1` collapsed count with the fibre presentation
  (`colMeet_one_ncard_eq_fibreMeet`),
* `hfin`, `hfind`, `hbase` — the hypotheses of the fibre decomposition
  (`fibreMeet_ncard_eq_sum_diamMeet`: the core meet set and the diameter meets are finite, and the
  core loop at the basepoint misses the sweep),
* `heven` — the box-parity conclusion `Even (K 0 + K 1)` of T1/T3 (`even_ncard_pairMeetBdry`,
  transferred through the chart bridge),
* `hpar` — T5, uniformly in the angle,

the transport `Odd n_P ↔ Odd (coreSideCount Q c P₁) ∧ Odd (coreSideCount Q c P₂)` follows. -/
theorem odd_ncard_of_even_colCount {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ}
    {P₁ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {c₂ : ℝ} {P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    {N : ℕ}
    (h0 : colCount β Q (clampedSweep c (fun t => 1 - t) P₁) W 0 = N)
    (h1 : colCount β Q (clampedSweep c (fun t => 1 - t) P₁) W 1
      = (fibreMeet Q (clampedSweep c (fun t => 1 - t) P₁) W).ncard)
    (hfin : (coreMeet Q c P₁).Finite)
    (hfind : ∀ q ∈ coreMeet Q c P₁, (diamMeet Q q.1 W).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c (fun t => 1 - t) P₁ y)
    (heven : Even (colCount β Q (clampedSweep c (fun t => 1 - t) P₁) W 0
      + colCount β Q (clampedSweep c (fun t => 1 - t) P₁) W 1))
    (hpar : ∀ t : ℝ, Odd (diamMeet Q t W).ncard ↔ Odd (coreSideCount Q c₂ P₂)) :
    Odd N ↔ Odd (coreSideCount Q c P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
  have hfib := fibreMeet_ncard_eq_sum_diamMeet Q c P₁ W hfin hfind hbase
  have hK1 : Odd (colCount β Q (clampedSweep c (fun t => 1 - t) P₁) W 1)
      ↔ Odd (coreSideCount Q c P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
    rw [h1, hfib]
    exact odd_sum_diamMeet_iff W hfin hpar
  have hK0 : Odd (colCount β Q (clampedSweep c (fun t => 1 - t) P₁) W 0)
      ↔ Odd (colCount β Q (clampedSweep c (fun t => 1 - t) P₁) W 1) := by
    have h := (Nat.even_add).mp heven
    rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd]
    exact not_iff_not.mpr h
  rw [h0] at hK0
  exact hK0.trans hK1

end

end Work.Drive
