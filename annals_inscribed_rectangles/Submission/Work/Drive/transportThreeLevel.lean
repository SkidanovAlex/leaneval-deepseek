import Mathlib
import Submission.Work.Drive.transportAssembly
import Submission.Work.Drive.even_ncard_pairMeetBdry
import Submission.Work.Drive.colMeet_one_ncard_eq_fibreMeet

/-!
# The transport (T6) with the three truncation levels of the engine independent

`Submission/Work/Drive/transportAssembly.lean` reduces the transport (Hugelmeyer's Lemma 2 in chain
form) to its four ingredients: the two endpoint identifications (`h0`: `K 0 = n_P`; `h1`:
`K 1 = #fibreMeet`), the box-parity conclusion `Even (K 0 + K 1)` and the uniform parity of the
diameter meets, and assembles them (`Work.Drive.odd_ncard_of_even_colCount`).

This file *instantiates* those four ingredients at the collapse family, so that the transport is
available as a theorem about the design's own data — and it does so with the **three truncation levels
independent**, which is what the counting engine needs: the triple
`(clampedSweep c₀ (diskPlane Q), clampedSweep c₁ P₁, clampedSweep c₂ P₂)` of
`Work.Drive.odd_sum_topBdryMeet_clampedSweeps_of_planes` truncates the three blocks at *pairwise
distinct* levels (`END_LEVEL_OBSTRUCTION.md` §1), and the identification `K 0 = n_P` must be proved for
those three levels (`Work.Drive.colCount_zero_eq_topBdryMeet'` below, generalising the two-level
`Work.Drive.colCount_zero_eq_topBdryMeet` of `collapseTransport.lean`).

Main result: **`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul`** —

> `Odd (topBdryMeet CappingSpace (fun k => clampedSweep (![c₀,c₁,c₂] k) (1-·)
>      (![diskPlane Q, P₁, P₂] k)) 0).ncard ↔
>   Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂)`,

i.e. the `0`-th top count of the design's triple is the product of the two side values (each at its own
truncation level).  Its hypotheses are exactly the design's inputs: the charted pair data with the
genericity `hreg`/`hface` and the level-face avoidances `havY`/`havZ` (the pair Sard analyser), the
chart bridge, the two cut-fibre conditions, the chart's seam clause, the collar data, the basepoint
condition of `TRANSPORT_COLLAPSE_STATUS.md` §7.5 and T5.

All declarations are `sorry`-free and rest on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The chart bridge in the pointwise form, and T1/T3 for the collapse family -/

/-- **The chart bridge.**  If the four chains are related by a bijection on the values that occur in
the box — stated as the two pointwise `↔`-hypotheses, which is what a local chart of `CappingSpace`
gives — then the collapsed meet set `colMeet β Q V W s` *is* the charted pair meet set
`pairMeetSet E E' V' W' s`.  (A chart of `CappingSpace` is injective only on its source, and the box is
exactly what confines the values to that source.) -/
theorem colMeet_eq_pairMeetSet_of_iff (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) (s : ℝ)
    (hcol : ∀ u ∈ Submission.Drive.unitBox 1, ∀ y ∈ Submission.Drive.unitBox 2,
      (colPlane β Q s u = V y ↔ E s u = V' y))
    (hdis : ∀ u ∈ Submission.Drive.unitBox 1, ∀ z ∈ Submission.Drive.unitBox 2,
      (diskPlane Q u = W z ↔ E' u = W' z)) :
    colMeet β Q V W s = pairMeetSet E E' V' W' s := by
  ext p
  simp only [colMeet, pairMeetSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, hV, hW⟩
    exact ⟨h1, h2, h3, (hcol p.1 h1 p.2.1 h2).mp hV, (hdis p.1 h1 p.2.2 h3).mp hW⟩
  · rintro ⟨h1, h2, h3, hV, hW⟩
    exact ⟨h1, h2, h3, (hcol p.1 h1 p.2.1 h2).mpr hV, (hdis p.1 h1 p.2.2 h3).mpr hW⟩

/-- **T1/T3 for the collapse family: `K 0 + K 1` is even.**  The pair-meet box-parity engine
`even_ncard_pairMeetBdry` (a statement about chains with values in `ℝ⁴`, i.e. in the coordinates of a
chart) applies to the collapse family through the chart bridge `colMeet_eq_pairMeetSet_of_iff`:

> `Even (colCount β Q V W 0 + colCount β Q V W 1)`.

The hypotheses are exactly the engine's, transported: the smoothness and the two genericity statements
`hreg`/`hface` for the *charted* pair map, the four seam invariances, and the two level-face avoidances
`havY`/`havZ`; plus the bridge (`hcol`/`hdis`), needed at the two parameters `s = 0, 1`. -/
theorem even_colCount_add
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E')
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
    (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W')
    (hreg : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V' W' x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff E E' V' W') x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8, pairDiff E E' V' W' x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff E E' V' W') x v.1))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ u : EuclideanSpace ℝ (Fin 2), onSeam2 u → E' (seamInv2 u) = E' u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V' (seamInv y) = V' y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W' (seamInv z) = W' z)
    (havY : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V' W' x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V' W' x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)
    (hcol : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ y ∈ Submission.Drive.unitBox 2, (colPlane β Q s u = V y ↔ E s u = V' y))
    (hdis : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ z ∈ Submission.Drive.unitBox 2, (diskPlane Q u = W z ↔ E' u = W' z)) :
    Even (colCount β Q V W 0 + colCount β Q V W 1) := by
  have h := even_ncard_pairMeetBdry E E' V' W' hE hE' hV' hW' hreg hface
    hseamU hseamU' hseamV hseamW havY havZ
  rw [colCount, colCount,
    colMeet_eq_pairMeetSet_of_iff E E' V' W' β Q V W 0 (hcol 0 (Or.inl rfl)) (hdis 0 (Or.inl rfl)),
    colMeet_eq_pairMeetSet_of_iff E E' V' W' β Q V W 1 (hcol 1 (Or.inr rfl)) (hdis 1 (Or.inr rfl))]
  exact h

/-! ## 2. `K 0 = n_P` with three independent truncation levels -/

/-- **`K(0) = n_P` with three independent truncation levels.**  The version of
`Work.Drive.colCount_zero_eq_topBdryMeet` in which the two sweeps are truncated at *different* levels
`c₁`, `c₂`: the design truncates the three blocks of one triple at pairwise distinct levels
(`END_LEVEL_OBSTRUCTION.md` §1), and the collapse count must be compared with the triple count of the
sweeps at exactly those levels. -/
theorem colCount_zero_eq_topBdryMeet' (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (c₀ c₁ c₂ : ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ ψ P₁) (clampedSweep c₂ ψ P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₁ ψ P₁) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ ψ P₁) (clampedSweep c₂ ψ P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₂ ψ P₂) u).ncard = 1) :
    colCount β Q (clampedSweep c₁ ψ P₁) (clampedSweep c₂ ψ P₂) 0
      = (topBdryMeet CappingSpace
          (fun k => clampedSweep (![c₀, c₁, c₂] k) ψ (![diskPlane Q, P₁, P₂] k)) 0).ncard := by
  have h := Capping.ncard_topBdryMeet_zero_eq_ncard_cutBaseBox
    (fun k => ![diskPlane Q, P₁, P₂] k) (fun k => ![c₀, c₁, c₂] k) ψ hψ hfibV hfibW
  rw [colCount, colMeet_zero_eq_cutTriples, h]
  have hcb : cutBaseBox (![diskPlane Q, P₁, P₂] 0)
      (clampedSweep (![c₀, c₁, c₂] 1) ψ (![diskPlane Q, P₁, P₂] 1))
      (clampedSweep (![c₀, c₁, c₂] 2) ψ (![diskPlane Q, P₁, P₂] 2))
      = cutBaseBox (diskPlane Q) (clampedSweep c₁ ψ P₁) (clampedSweep c₂ ψ P₂) := by simp
  rw [hcb]
  exact ncard_cutTriples_eq_ncard_cutBaseBox _ _ _ hfibV hfibW

/-! ## 3. The transport, with the three levels of the engine -/

/-- **T6 — the radial-collapse transport (Hugelmeyer's Lemma 2 at the chain level), with the three
truncation levels independent.**  For a disk chart `Q` (with the seam clause), a collar radius `δ` with
`β = √·` above `δ²`, and the disk of radius `δ` missing the cut of `Q` by the sweep of `P₂`:

> `Odd (topBdryMeet (the three sweeps at the levels c₀, c₁, c₂) 0).ncard ↔
>   Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂)`,

i.e. the plane's triple count at the levels `(c₀, c₁, c₂)` is the product of the two side values
`ε₁ · ε₂`, each at its own truncation level.

The ingredients, all proved: T1/T3 (`even_colCount_add`), the `K(0)` identification at the three levels
(`colCount_zero_eq_topBdryMeet'`), T4 (`colMeet_one_ncard_eq_fibreMeet`), the fibre sum
(`fibreMeet_ncard_eq_sum_diamMeet`, with the basepoint condition of `TRANSPORT_COLLAPSE_STATUS.md`
§7.5) and T5 (`ht5`); the assembly is `Work.Drive.odd_ncard_of_even_colCount`. -/
theorem odd_topBdryMeet_zero_iff_coreSideCount_mul
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E')
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
    (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W')
    (hreg : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V' W' x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff E E' V' W') x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8, pairDiff E E' V' W' x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff E E' V' W') x v.1))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ u : EuclideanSpace ℝ (Fin 2), onSeam2 u → E' (seamInv2 u) = E' u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V' (seamInv y) = V' y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W' (seamInv z) = W' z)
    (havY : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V' W' x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V' W' x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)
    (hcol : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ y ∈ Submission.Drive.unitBox 2,
      (colPlane β Q s u = clampedSweep c₁ (fun t => 1 - t) P₁ y ↔ E s u = V' y))
    (hdis : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ z ∈ Submission.Drive.unitBox 2,
      (diskPlane Q u = clampedSweep c₂ (fun t => 1 - t) P₂ z ↔ E' u = W' z))
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₂ (fun t => 1 - t) P₂) u).ncard = 1)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hβδ : ∀ t : ℝ, δ ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δ →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hfin : (coreMeet Q c₁ P₁).Finite)
    (hfind : ∀ q ∈ coreMeet Q c₁ P₁, (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c₁ (fun t => 1 - t) P₁ y)
    (ht5 : ∀ t : ℝ, Odd (diamMeet Q t (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard ↔
      Odd (coreSideCount Q c₂ P₂)) :
    Odd (topBdryMeet CappingSpace
        (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
          (![diskPlane Q, P₁, P₂] k)) 0).ncard ↔
      Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
  -- the two parity lemmas on `ℕ`
  have hpar₁ : Odd (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂) 0) ↔
      Odd (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂) 1) := by
    have hev := even_colCount_add E E' V' W' β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
      (clampedSweep c₂ (fun t => 1 - t) P₂) hE hE' hV' hW' hreg hface
      hseamU hseamU' hseamV hseamW havY havZ hcol hdis
    have h' : Even (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 0)
        ↔ Even (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 1) := Nat.even_add.mp hev
    rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd]
    exact not_congr h'
  -- `K 1` is the fibre-meet count
  have hfib : Odd (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂) 1) ↔
      Odd (fibreMeet Q (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard := by
    rw [colCount, colMeet_one_ncard_eq_fibreMeet β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
      (clampedSweep c₂ (fun t => 1 - t) P₂) hδ hQseam hβδ hδcut]
  -- the fibre sum
  have hsum : Odd (fibreMeet Q (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard ↔
      Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
    rw [fibreMeet_ncard_eq_sum_diamMeet (Q := Q) (c := c₁) (P₁ := P₁)
      (W := clampedSweep c₂ (fun t => 1 - t) P₂) hfin hfind hbase]
    rw [Finset.odd_sum_iff_odd_card_odd]
    have hfilter : (hfin.toFinset.filter
        (fun q => Odd ((diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard)))
        = if Odd (coreSideCount Q c₂ P₂) then hfin.toFinset else ∅ := by
      by_cases hP : Odd (coreSideCount Q c₂ P₂)
      · rw [if_pos hP]
        exact Finset.filter_true_of_mem (fun q _ => (ht5 q.1).mpr hP)
      · rw [if_neg hP]
        exact Finset.filter_false_of_mem (fun q _ hodd => hP ((ht5 q.1).mp hodd))
    rw [hfilter]
    have hcard : hfin.toFinset.card = (coreMeet Q c₁ P₁).ncard :=
      (Set.ncard_eq_toFinset_card (coreMeet Q c₁ P₁) hfin).symm
    by_cases hP : Odd (coreSideCount Q c₂ P₂)
    · rw [if_pos hP, hcard]
      exact ⟨fun h => ⟨h, hP⟩, fun h => h.1⟩
    · rw [if_neg hP, Finset.card_empty]
      refine ⟨fun h => absurd h (by decide), fun h => absurd h.2 hP⟩
  -- `K 0` is the triple count of the sweeps
  have h0 : Odd (topBdryMeet CappingSpace
        (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
          (![diskPlane Q, P₁, P₂] k)) 0).ncard ↔
      Odd (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂) 0) := by
    rw [colCount_zero_eq_topBdryMeet' β Q c₀ c₁ c₂ (fun t => 1 - t) (by norm_num) P₁ P₂ hfibV hfibW]
  exact h0.trans (hpar₁.trans (hfib.trans hsum))

/-! ## 4. The block criterion for the parameter derivative of the pair map

The Sard route to `hreg`/`hface` of `even_ncard_pairMeetBdry` needs — besides the chart containment —
the **surjectivity of the parameter-derivative** of the charted pair map at its zeros
(`TRANSPORT_COLLAPSE_STATUS.md` §8.2 item 1).  The theorem below is the pair analogue of
`Work.Drive.TParity.surjective_fderiv_chartDiff3_of_block` (the triple criterion that powers
`hsurj_chartShiftFamily`): if the four charted chains' values admit **independent** first-order
movements — block `E` and block `E'` can be moved in any direction while blocks `V`, `W` stay frozen —
then the parameter-derivative of the pair map is onto `ℝ⁸`.  A chart-shift of the two *plane
presentations* `P₁`, `P₂` supplies exactly this hypothesis (its charted value is the shifted value, so
its parameter-derivative is the corresponding block projection). -/

/-- `pair44` is `Work.Drive.pairUp` (the two definitions have the same body). -/
lemma pair44_eq_pairUp (a b : EuclideanSpace ℝ (Fin 4)) : pair44 a b = pairUp a b := rfl

/-- **The block criterion for `hsurj` of the pair map (T1/T3).**  Let
`t ↦ (E t, E' t, V t, W t)` be a family of four charted chains and `x` a point of the nine-box.  If at
the parameter `p` the charted values of the four chains have first-order movements `DE`, `DE'`, `DV`,
`DW` (`HasFDerivAt`), and if the blocks of `E` and `E'` can be moved **independently** of `V` and `W`,
then the parameter-derivative of the charted pair map at `x` is surjective:

> `Surjective (fderiv ℝ (fun t => pairDiff (E t) (E' t) (V t) (W t) x) p)`.

This is the exact input the parametric-Sard engine (`exists_forall_good_on_compact` and its face
version) consumes. -/
theorem surjective_fderiv_pairDiff_of_block (m : ℕ)
    (E : EuclideanSpace ℝ (Fin m) → ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (p : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin 9))
    (DE DE' DV DW : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hE : HasFDerivAt (fun t => E t (ftS x) (ftU x)) DE p)
    (hE' : HasFDerivAt (fun t => E' t (ftU x)) DE' p)
    (hV : HasFDerivAt (fun t => V t (ftY x)) DV p)
    (hW : HasFDerivAt (fun t => W t (ftZ x)) DW p)
    (hblock : ∀ a b : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      DE u = a ∧ DE' u = b ∧ DV u = 0 ∧ DW u = 0) :
    Function.Surjective
      (fderiv ℝ (fun t => pairDiff (E t) (E' t) (V t) (W t) x) p) := by
  have hprod : HasFDerivAt
      (fun t => (E t (ftS x) (ftU x) - V t (ftY x), E' t (ftU x) - W t (ftZ x)))
      ((DE - DV).prod (DE' - DW)) p := (hE.sub hV).prodMk (hE'.sub hW)
  have hpup : HasFDerivAt
      (fun t => TParity.pUpCLM (E t (ftS x) (ftU x) - V t (ftY x), E' t (ftU x) - W t (ftZ x)))
      (TParity.pUpCLM.comp ((DE - DV).prod (DE' - DW))) p :=
    TParity.pUpCLM.hasFDerivAt.comp p hprod
  have hfin : HasFDerivAt (fun t => pairDiff (E t) (E' t) (V t) (W t) x)
      (TParity.pUpCLM.comp ((DE - DV).prod (DE' - DW))) p :=
    hpup.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      simp only [pairDiff, TParity.pUpCLM_apply, pair44_eq_pairUp])
  rw [hfin.fderiv]
  intro w
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := hblock (TParity.fst8 w) (TParity.snd8 w)
  refine ⟨u, ?_⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, sub_apply, sub_apply,
    hu1, hu2, hu3, hu4, sub_zero, sub_zero, TParity.pUpCLM_apply, TParity.pUp_fst8_snd8]

/-! ## 5. The chart-shift family of the pair map has `hsurj` (T1/T3, unconditionally)

The design perturbs the two *plane presentations* (whence the two swept chains), which in the
coordinates of a chart is the shift `p ↦ E + (block p)`.  The theorem below is the pair analogue of
`Work.Drive.hsurj_chartShiftFamily`: for the charted family

> `E t s u = E₀ s u + unpackFst t`,  `E' t u = E'₀ u + unpackSnd t`

(with `unpackFst`/`unpackSnd` the two blocks of `ℝ⁸`), the parameter-derivative of the pair map is
**onto `ℝ⁸` at every point of the nine-box** — so the parametric-Sard engine can always be fired, with
no hypothesis on the base configuration beyond the chart containment that identifies the charted shift
with the honest one. -/

/-- The first `ℝ⁴`-block of `ℝ⁸`, as a continuous linear map. -/
noncomputable def unpackFst : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 4 =>
      PiLp.proj 2 (fun _ : Fin 8 => ℝ) (Fin.castAdd 4 i)))

/-- The second `ℝ⁴`-block of `ℝ⁸`, as a continuous linear map. -/
noncomputable def unpackSnd : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm
    (ContinuousLinearMap.pi (fun i : Fin 4 =>
      PiLp.proj 2 (fun _ : Fin 8 => ℝ) (Fin.natAdd 4 i)))

@[simp] lemma unpackFst_apply (t : EuclideanSpace ℝ (Fin 8)) (i : Fin 4) :
    unpackFst t i = t (Fin.castAdd 4 i) := by
  simp [unpackFst]

@[simp] lemma unpackSnd_apply (t : EuclideanSpace ℝ (Fin 8)) (i : Fin 4) :
    unpackSnd t i = t (Fin.natAdd 4 i) := by
  simp [unpackSnd]

lemma unpackFst_pairUp (a b : EuclideanSpace ℝ (Fin 4)) : unpackFst (pairUp a b) = a := by
  ext i
  rw [unpackFst_apply, pairUp_apply_fst]

lemma unpackSnd_pairUp (a b : EuclideanSpace ℝ (Fin 4)) : unpackSnd (pairUp a b) = b := by
  ext i
  rw [unpackSnd_apply, pairUp_apply_snd]

/-- **`hsurj` for the chart-shift family of the pair map.**  For the charted chains obtained from any
four charted chains by shifting the first two by the two blocks of the parameter `t ∈ ℝ⁸`, the
parameter-derivative of the charted pair map is surjective at every point of the nine-box. -/
theorem surjective_fderiv_pairDiff_shift
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (q : EuclideanSpace ℝ (Fin 8)) (x : EuclideanSpace ℝ (Fin 9)) :
    Function.Surjective (fderiv ℝ (fun t : EuclideanSpace ℝ (Fin 8) =>
      pairDiff (fun s u => E₀ s u + unpackFst t) (fun u => E'₀ u + unpackSnd t) V₀ W₀ x) q) := by
  refine surjective_fderiv_pairDiff_of_block 8
    (fun t s u => E₀ s u + unpackFst t) (fun t u => E'₀ u + unpackSnd t)
    (fun _ y => V₀ y) (fun _ z => W₀ z) q x unpackFst unpackSnd 0 0
    (by simpa using (ContinuousLinearMap.hasFDerivAt unpackFst).const_add (E₀ (ftS x) (ftU x)))
    (by simpa using (ContinuousLinearMap.hasFDerivAt unpackSnd).const_add (E'₀ (ftU x)))
    (hasFDerivAt_const _ _) (hasFDerivAt_const _ _) ?_
  intro a b
  exact ⟨pairUp a b, unpackFst_pairUp a b, unpackSnd_pairUp a b, rfl, rfl⟩

/-- **`hsurj` for the *weighted* chart-shift family of the pair map.**  The shift of the previous
theorem vanishes only if the weight does; since T6's two endpoint identifications (`K 0 = n_P`,
`K 1 = #fibreMeet`) need the perturbation to vanish at `s ∈ {0,1}`, the design uses a weight
`s ↦ w s` with `w 0 = w 1 = 0` and `w s ≠ 0` for `s ∈ (0,1)`.  Then the parameter-derivative of the
pair map is still onto `ℝ⁸` at every `x` whose family coordinate has `w (ftS x) ≠ 0` — in particular
on every zero of the pair map with `ftS x ∉ {0,1}`, which is exactly the region the parametric-Sard
engine is applied to. -/
theorem surjective_fderiv_pairDiff_weightedShift
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (w : ℝ → ℝ) (q : EuclideanSpace ℝ (Fin 8)) (x : EuclideanSpace ℝ (Fin 9))
    (hw : w (ftS x) ≠ 0) :
    Function.Surjective (fderiv ℝ (fun t : EuclideanSpace ℝ (Fin 8) =>
      pairDiff (fun s u => E₀ s u + w (ftS x) • unpackFst t)
        (fun u => E'₀ u + w (ftS x) • unpackSnd t) V₀ W₀ x) q) := by
  refine surjective_fderiv_pairDiff_of_block 8
    (fun t s u => E₀ s u + w (ftS x) • unpackFst t)
    (fun t u => E'₀ u + w (ftS x) • unpackSnd t)
    (fun _ y => V₀ y) (fun _ z => W₀ z) q x
    (w (ftS x) • unpackFst) (w (ftS x) • unpackSnd) 0 0
    (by simpa using (ContinuousLinearMap.hasFDerivAt ((w (ftS x)) • unpackFst)).const_add (E₀ (ftS x) (ftU x)))
    (by simpa using (ContinuousLinearMap.hasFDerivAt ((w (ftS x)) • unpackSnd)).const_add (E'₀ (ftU x)))
    (hasFDerivAt_const _ _) (hasFDerivAt_const _ _) ?_
  intro a b
  refine ⟨pairUp ((w (ftS x))⁻¹ • a) ((w (ftS x))⁻¹ • b), ?_, ?_, rfl, rfl⟩
  · rw [ContinuousLinearMap.smul_apply, unpackFst_pairUp, smul_smul,
      mul_inv_cancel₀ hw, one_smul]
  · rw [ContinuousLinearMap.smul_apply, unpackSnd_pairUp, smul_smul,
      mul_inv_cancel₀ hw, one_smul]

end

end Work.Drive
