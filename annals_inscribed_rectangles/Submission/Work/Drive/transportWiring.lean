import Mathlib
import Submission.Work.Drive.transportThreeLevel
import Submission.Work.Drive.transportCollar
import Submission.Work.Drive.transportSep

/-!
# The transport: decoupling the box parity from the genericity, and wiring the collars

`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul` (T6) proves the multiplicativity of the
transport from the design's charted pair data, using the box-parity engine *internally*.  Two
decouplings make its hypothesis list much smaller and let the perturbed (Sard) chains be used:

1. **`odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even`** — the same conclusion with the box-parity
   conclusion `Even (K 0 + K 1)` as a *hypothesis*, in place of the eight genericity hypotheses of the
   engine (`hreg`, `hface`, the four seam invariances `hseamU`/`hseamU'`/`hseamV`/`hseamW` and the two
   level-face avoidances `havY`/`havZ`) together with the two chart bridges `hcol`/`hdis`;
2. **`exists_even_colCount_add2_of_design`** — the box parity `Even (K 0 + K 1)` for the *perturbed*
   pair map, with

   * the Sard data on the compact `K` (`Work.Drive.exists_pairDiff2_good_shift`),
   * the **base** configuration's regularity and face data on the two end collars — the lead's
     **(G2)** — transferred by `Work.Drive.collar_reg` / `collar_face`,
   * the level-face avoidances of the perturbed chains, restricted to the ball `‖t‖ < ε` of the
     Sard parameter (so that they can be produced by the separation argument of
     `Work.Drive.pairDiff2_faceY_ne_of_sep` / `pairDiff2_faceZ_ne_of_sep`),
   * the design's own data (the two seam invariances, the chart bridges at the endpoint parameters,
     `w 0 = w 1 = 0`).

   `exists_even_colCount_add2_of_design_sep` is the version in which the level-face avoidances are
   *produced* from the separation data rather than assumed.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. T6 with the box parity as the hypothesis -/

/-- **The transport (T6) with the box parity decoupled.**  Same conclusion as
`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul`, but the box-parity input
`Even (K 0 + K 1)` is a hypothesis instead of being produced from the charted pair data: the eight
genericity hypotheses of the box-parity engine and the two chart bridges disappear from the
statement. -/
theorem odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (heven : Even (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 0
        + colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 1))
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
  have hpar₁ : Odd (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂) 0) ↔
      Odd (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂) 1) := by
    have h' : Even (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 0)
        ↔ Even (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 1) := Nat.even_add.mp heven
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

/-! ## 2. Smoothness of the shifted chart blocks, in the `(s, u)` variables -/

/-- The first shifted chart block is smooth as a function of `(s, u)`. -/
lemma contDiff_uncurry_shiftFst
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (hE₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E₀))
    {w : ℝ → ℝ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (t : EuclideanSpace ℝ (Fin 8)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry fun s u => E₀ s u + w s • unpackFst t) := by
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => w q.1) :=
    hw.comp contDiff_fst
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => w q.1 • unpackFst t) :=
    h2.smul contDiff_const
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => E₀ q.1 q.2) := hE₀
  exact h1.add h3

/-- The second shifted chart block is smooth as a function of `(s, u)`. -/
lemma contDiff_uncurry_shiftSnd
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (hE'₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'₀))
    {w : ℝ → ℝ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (t : EuclideanSpace ℝ (Fin 8)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry fun s u => E'₀ s u + w s • unpackSnd t) := by
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => w q.1) :=
    hw.comp contDiff_fst
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => w q.1 • unpackSnd t) :=
    h2.smul contDiff_const
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => E'₀ q.1 q.2) := hE'₀
  exact h1.add h3

/-! ## 3. Wiring: the box parity of the perturbed pair map from the Sard and the collars -/

/-- **The box parity of the transport's perturbed pair map, with the two collars handled by the base
configuration.**  The Sard supplies the regularity and the face data of the perturbed pair map on the
compact `K`; outside `K` the weight vanishes (so the perturbation is inactive) and the *base*
configuration's data — the lead's **(G2)** — takes over.  The level-face avoidances are required only
for the Sard parameters `‖t‖ < ε`, which is the shape the separation argument supplies. -/
theorem exists_even_colCount_add2_of_design
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {δ : ℝ}
    (hE₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E₀))
    (hE'₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'₀))
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
    (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W')
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwne : ∀ x ∈ K, w (ftS x) ≠ 0)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ ftS x → ftS x ≤ 1 - δ → x ∈ K)
    (hwleft : ∀ s, s ≤ δ → w s = 0) (hwright : ∀ s, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V' W' x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff2 E₀ E'₀ V' W') x))
    (hfaceBase : ∀ x ∈ Submission.Drive.unitBoxBdry 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V' W' x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff2 E₀ E'₀ V' W') x v.1))
    (ε : ℝ) (hε : 0 < ε)
    (havY : ∀ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε → ∀ x ∈ Submission.Drive.unitBox 8,
      pairDiff2 (fun s u => E₀ s u + w s • unpackFst t)
        (fun s u => E'₀ s u + w s • unpackSnd t) V' W' x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε → ∀ x ∈ Submission.Drive.unitBox 8,
      pairDiff2 (fun s u => E₀ s u + w s • unpackFst t)
        (fun s u => E'₀ s u + w s • unpackSnd t) V' W' x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E₀ s (seamInv2 u) = E₀ s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E'₀ s (seamInv2 u) = E'₀ s u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V' (seamInv y) = V' y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W' (seamInv z) = W' z)
    (hcol : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ y ∈ Submission.Drive.unitBox 2, (colPlane β Q s u = V y ↔ E₀ s u = V' y))
    (hdis : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ z ∈ Submission.Drive.unitBox 2, (diskPlane Q u = W z ↔ E'₀ s u = W' z))
    (hw0 : w 0 = 0) (hw1 : w 1 = 0) :
    ∃ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε ∧
      Even (colCount β Q V W 0 + colCount β Q V W 1) := by
  obtain ⟨t, ht, hgood, hface⟩ :=
    exists_pairDiff2_good_shift E₀ E'₀ V' W' w K hK hE₀ hE'₀ hV' hW' hw hwne ε hε
  refine ⟨t, ht, ?_⟩
  have hshift := weightedShift_agrees_both E₀ E'₀ hwleft hwright t
  have hout : ∀ x ∈ Submission.Drive.unitBox 8, x ∉ K → ftS x < δ ∨ 1 - δ < ftS x := by
    intro x hx hxK
    by_contra hc
    push Not at hc
    exact hxK (hKcover x hx hc.1 hc.2)
  have key : ∀ s, (s = 0 ∨ s = 1) → w s = 0 := by
    intro s hs
    rcases hs with h | h
    · rw [h]; exact hw0
    · rw [h]; exact hw1
  refine even_colCount_add2 (fun s u => E₀ s u + w s • unpackFst t)
    (fun s u => E'₀ s u + w s • unpackSnd t) V' W' β Q V W
    (contDiff_uncurry_shiftFst E₀ hE₀ hw t) (contDiff_uncurry_shiftSnd E'₀ hE'₀ hw t)
    hV' hW' ?_ ?_ ?_ ?_ hseamV hseamW ?_ ?_ ?_ ?_
  · intro x hx hzero
    by_cases hxK : x ∈ K
    · exact hgood x hxK hzero
    · exact collar_reg E₀ E'₀ V' W' _ _ hshift.1 hshift.2 hregBase x hx (hout x hx hxK) hzero
  · intro x hbdry hzero
    by_cases hxK : x ∈ K
    · exact hface x hxK hzero hbdry
    · exact collar_face E₀ E'₀ V' W' _ _ hshift.1 hshift.2 hfaceBase x hbdry.1
        (hout x hbdry.1 hxK) hzero hbdry
  · intro s u hu
    simp only [hseamU s u hu]
  · intro s u hu
    simp only [hseamU' s u hu]
  · intro x hx hzero
    exact havY t ht x hx hzero
  · intro x hx hzero
    exact havZ t ht x hx hzero
  · intro s hs u _hu y _hy
    simp only [key s hs, zero_smul, add_zero]
    exact hcol s hs u _hu y _hy
  · intro s hs u _hu z _hz
    simp only [key s hs, zero_smul, add_zero]
    exact hdis s hs u _hu z _hz

/-! ## 4. The same, with the level-face avoidances *produced* from separation -/

/-- **The box parity of the perturbed pair map, with every hypothesis design-suppliable.**  The
level-face avoidances of the perturbed chains are *derived* from the separation data
(`Work.Drive.pairDiff2_faceY_ne_of_sep` / `pairDiff2_faceZ_ne_of_sep`), so that the only geometric
inputs left are the honest containments of the two chart blocks and of the two sweeps' faces, and the
four separation constants. -/
theorem exists_even_colCount_add2_of_design_sep
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {δ : ℝ}
    (hE₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E₀))
    (hE'₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'₀))
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
    (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W')
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwne : ∀ x ∈ K, w (ftS x) ≠ 0)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ ftS x → ftS x ≤ 1 - δ → x ∈ K)
    (hwleft : ∀ s, s ≤ δ → w s = 0) (hwright : ∀ s, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V' W' x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff2 E₀ E'₀ V' W') x))
    (hfaceBase : ∀ x ∈ Submission.Drive.unitBoxBdry 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V' W' x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff2 E₀ E'₀ V' W') x v.1))
    {AY BY BY' AZ BZ BZ' : Set (EuclideanSpace ℝ (Fin 4))} {dY dZ : ℝ}
    (hAY : ∀ s : ℝ, ∀ u ∈ Submission.Drive.unitBox 1, E₀ s u ∈ AY)
    (hAYtop : ∀ y ∈ Submission.Drive.unitBox 2, y 2 = 1 → V' y ∈ BY)
    (hAYbot : ∀ y ∈ Submission.Drive.unitBox 2, y 2 = 0 → V' y ∈ BY')
    (hsepY : ∀ a ∈ AY, ∀ b ∈ BY, dY ≤ dist a b)
    (hsepY' : ∀ a ∈ AY, ∀ b ∈ BY', dY ≤ dist a b)
    (hAZ : ∀ s : ℝ, ∀ u ∈ Submission.Drive.unitBox 1, E'₀ s u ∈ AZ)
    (hAZtop : ∀ z ∈ Submission.Drive.unitBox 2, z 2 = 1 → W' z ∈ BZ)
    (hAZbot : ∀ z ∈ Submission.Drive.unitBox 2, z 2 = 0 → W' z ∈ BZ')
    (hsepZ : ∀ a ∈ AZ, ∀ b ∈ BZ, dZ ≤ dist a b)
    (hsepZ' : ∀ a ∈ AZ, ∀ b ∈ BZ', dZ ≤ dist a b)
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E₀ s (seamInv2 u) = E₀ s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E'₀ s (seamInv2 u) = E'₀ s u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V' (seamInv y) = V' y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W' (seamInv z) = W' z)
    (hcol : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ y ∈ Submission.Drive.unitBox 2, (colPlane β Q s u = V y ↔ E₀ s u = V' y))
    (hdis : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ z ∈ Submission.Drive.unitBox 2, (diskPlane Q u = W z ↔ E'₀ s u = W' z))
    (hw0 : w 0 = 0) (hw1 : w 1 = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hbdY : ∀ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε →
      ∀ s : ℝ, ‖w s • unpackFst t‖ < dY)
    (hbdZ : ∀ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε →
      ∀ s : ℝ, ‖w s • unpackSnd t‖ < dZ) :
    ∃ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε ∧
      Even (colCount β Q V W 0 + colCount β Q V W 1) :=
  exists_even_colCount_add2_of_design E₀ E'₀ V' W' β Q V W w K hK hE₀ hE'₀ hV' hW' hw hwne
    hKcover hwleft hwright hregBase hfaceBase ε hε
    (fun t ht x hx hzero =>
      pairDiff2_faceY_ne_of_sep E₀ E'₀ V' W' w t hAY hAYtop hAYbot hsepY hsepY'
        (hbdY t ht) x hx hzero)
    (fun t ht x hx hzero =>
      pairDiff2_faceZ_ne_of_sep E₀ E'₀ V' W' w t hAZ hAZtop hAZbot hsepZ hsepZ'
        (hbdZ t ht) x hx hzero)
    hseamU hseamU' hseamV hseamW hcol hdis hw0 hw1

/-! ## 5. The transport, with the *perturbed* box parity and every hypothesis design-suppliable -/

/-- **The transport (T6) with the box parity produced by the perturbed pair map.**  This is the
endpoint of the transport's box-parity lane: the multiplicativity `n_P ≡ ε_Q · ε_R` of the design's
`0`-th top count, with the hypothesis list reduced to

* the **Sard data** (`K` compact, `w` smooth with `w ≠ 0` on `K` containing the interior slab,
  `w 0 = w 1 = 0`);
* the **base configuration's data on the two end collars** (the lead's **(G2)**);
* the **separation data** of the honest charted sets, together with the smallness bound on the
  perturbation (this is what makes the level faces of the *perturbed* pair map be avoided);
* the **design's chart data**: the two seam invariances, the chart bridges at the endpoint parameters,
  the cut-fibre data, the level/`diskCut` data of the collapse and the basepoint condition,
  and T5.

No genericity of the *honest* pair map is required. -/
theorem odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_sep
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {δ : ℝ}
    (hE₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E₀))
    (hE'₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'₀))
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
    (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W')
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwne : ∀ x ∈ K, w (ftS x) ≠ 0)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ ftS x → ftS x ≤ 1 - δ → x ∈ K)
    (hwleft : ∀ s, s ≤ δ → w s = 0) (hwright : ∀ s, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V' W' x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff2 E₀ E'₀ V' W') x))
    (hfaceBase : ∀ x ∈ Submission.Drive.unitBoxBdry 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V' W' x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff2 E₀ E'₀ V' W') x v.1))
    {AY BY BY' AZ BZ BZ' : Set (EuclideanSpace ℝ (Fin 4))} {dY dZ : ℝ}
    (hAY : ∀ s : ℝ, ∀ u ∈ Submission.Drive.unitBox 1, E₀ s u ∈ AY)
    (hAYtop : ∀ y ∈ Submission.Drive.unitBox 2, y 2 = 1 → V' y ∈ BY)
    (hAYbot : ∀ y ∈ Submission.Drive.unitBox 2, y 2 = 0 → V' y ∈ BY')
    (hsepY : ∀ a ∈ AY, ∀ b ∈ BY, dY ≤ dist a b)
    (hsepY' : ∀ a ∈ AY, ∀ b ∈ BY', dY ≤ dist a b)
    (hAZ : ∀ s : ℝ, ∀ u ∈ Submission.Drive.unitBox 1, E'₀ s u ∈ AZ)
    (hAZtop : ∀ z ∈ Submission.Drive.unitBox 2, z 2 = 1 → W' z ∈ BZ)
    (hAZbot : ∀ z ∈ Submission.Drive.unitBox 2, z 2 = 0 → W' z ∈ BZ')
    (hsepZ : ∀ a ∈ AZ, ∀ b ∈ BZ, dZ ≤ dist a b)
    (hsepZ' : ∀ a ∈ AZ, ∀ b ∈ BZ', dZ ≤ dist a b)
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E₀ s (seamInv2 u) = E₀ s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E'₀ s (seamInv2 u) = E'₀ s u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V' (seamInv y) = V' y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W' (seamInv z) = W' z)
    (hcol : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ y ∈ Submission.Drive.unitBox 2,
      (colPlane β Q s u = clampedSweep c₁ (fun t => 1 - t) P₁ y ↔ E₀ s u = V' y))
    (hdis : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ z ∈ Submission.Drive.unitBox 2,
      (diskPlane Q u = clampedSweep c₂ (fun t => 1 - t) P₂ z ↔ E'₀ s u = W' z))
    (hw0 : w 0 = 0) (hw1 : w 1 = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hbdY : ∀ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε →
      ∀ s : ℝ, ‖w s • unpackFst t‖ < dY)
    (hbdZ : ∀ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε →
      ∀ s : ℝ, ‖w s • unpackSnd t‖ < dZ)
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₂ (fun t => 1 - t) P₂) u).ncard = 1)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {δc : ℝ} (hδc : 0 ≤ δc) (hβδc : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
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
  obtain ⟨t, _ht, heven⟩ :=
    exists_even_colCount_add2_of_design_sep E₀ E'₀ V' W' β Q
      (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) w K hK
      hE₀ hE'₀ hV' hW' hw hwne hKcover hwleft hwright hregBase hfaceBase hAY hAYtop hAYbot
      hsepY hsepY' hAZ hAZtop hAZbot hsepZ hsepZ' hseamU hseamU' hseamV hseamW hcol hdis
      hw0 hw1 ε hε hbdY hbdZ
  exact odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even β Q P₁ P₂ c₀ c₁ c₂ heven
    hfibV hfibW hQseam hδc hβδc hδcut hfin hfind hbase ht5

end

end Work.Drive
