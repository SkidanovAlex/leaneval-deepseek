import Mathlib
import Submission.Work.Drive.transportThreeLevel
import Submission.Work.Drive.ppIntrinsicStrip

/-!
# The transport `T6` with **no cut-fibre conditions** and the **sharpened `ht5`** — the form the
# reference-triple lane instantiates

Two defects of the transport `T6` as it stands on disk are repaired *here*, without touching the proved
files (the lead's design notes `NOTES_LEAD_hblock_uniformity.md` §4.2 and `NOTES_LEAD_hfib.md` §0,
where both are verified):

1. **`ht5` must be `∀ q ∈ coreMeet Q c₁ P₁`, not `∀ t : ℝ`.**  The `∀ t` form is *false in general*: at
   an angle at which the diameter loop is tangent to the cut curve, `ncard` counts the double zero only
   once, so the parity of `Odd (diamMeet Q t W)` flips, while `Odd (coreSideCount Q c₂ P₂)` does not.
   Nothing excludes such angles.  The transport uses `ht5` only at the `t`-values of the core meets
   (`Finset.filter` over `hfin.toFinset`), so the pointwise form is exactly what is consumed and is
   provable (`Task` 5 of the lead's hblock note restates it this way).
2. **`hfibV`/`hfibW` are not needed.**  They occur only through
   `Work.Drive.colCount_zero_eq_topBdryMeet'`, whose round trip
   `cutTriples → cutBaseBox → cutTriples` needs the two single-fibre conditions.  The direct bijection
   `colMeet β Q V W 0 = cutTriples (diskPlane Q) V W` (`colMeet_zero_eq_cutTriples`) composed with
   `Work.Drive.ncard_topBdryMeet_zero_eq_ncard_cutTriples` (whose only hypothesis is `ψ 1 = 0`) gives
   the same count with no fibre condition — this is the lead's
   `colCount_zero_eq_topBdryMeet_nofib`, reproduced below.

The module contains three declarations:

* `Work.Drive.colCount_zero_eq_topBdryMeet_nofib` — the fibre-free `K(0)` identification;
* `Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even_nf` — T6 with the box parity as the
  hypothesis, the two fibre binders deleted and `ht5` sharpened;
* `Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf` — the design-facing
  form: also without the (unsatisfiable) collar binder `hwne` (see
  `Submission/Work/Drive/PPINTRINSIC_STRIP_STATUS.md`), so that **all** of its remaining hypotheses are
  design data or genericity conditions on the configuration.

Everything is sorry-free and axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The `K(0)` identification of the transport, with no cut-fibre hypothesis.**  The proof of
`Work.Drive.colCount_zero_eq_topBdryMeet'` goes through `cutBaseBox`, whose projection to the plane
parameter needs `(cutFibreBox · u).ncard = 1`; the direct bijection
`colMeet β Q V W 0 = cutTriples` composed with `ncard_topBdryMeet_zero_eq_ncard_cutTriples` needs only
`ψ 1 = 0` (the injectivity of `cutProj` on the top face). -/
theorem colCount_zero_eq_topBdryMeet_nofib (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (c₀ c₁ c₂ : ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    colCount β Q (clampedSweep c₁ ψ P₁) (clampedSweep c₂ ψ P₂) 0
      = (topBdryMeet CappingSpace
          (fun k => clampedSweep (![c₀, c₁, c₂] k) ψ (![diskPlane Q, P₁, P₂] k)) 0).ncard := by
  rw [colCount, colMeet_zero_eq_cutTriples,
    ncard_topBdryMeet_zero_eq_ncard_cutTriples (fun k => ![diskPlane Q, P₁, P₂] k)
      (fun k => ![c₀, c₁, c₂] k) ψ hψ]
  rfl

theorem odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even_nf
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (heven : Even (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 0
        + colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 1))
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hβδ : ∀ t : ℝ, δ ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δ →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hfin : (coreMeet Q c₁ P₁).Finite)
    (hfind : ∀ q ∈ coreMeet Q c₁ P₁, (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c₁ (fun t => 1 - t) P₁ y)
    (ht5 : ∀ q ∈ coreMeet Q c₁ P₁,
      Odd (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard ↔
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
        exact Finset.filter_true_of_mem (fun q hq => (ht5 q (hfin.mem_toFinset.mp hq)).mpr hP)
      · rw [if_neg hP]
        exact Finset.filter_false_of_mem (fun q hq hodd => hP ((ht5 q (hfin.mem_toFinset.mp hq)).mp hodd))
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
    rw [colCount_zero_eq_topBdryMeet_nofib β Q c₀ c₁ c₂ (fun t => 1 - t) (by norm_num) P₁ P₂]
  exact h0.trans (hpar₁.trans (hfib.trans hsum))

theorem odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {δ : ℝ}
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hw : ContDiff ℝ Ctop w)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ < ftS x → ftS x < 1 - δ → x ∈ K)
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (hw0 : w 0 = 0) (hw1 : w 1 = 0)
    (hE : ContMDiff 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) (𝓡 4) Ctop
      (Function.uncurry (colPlane β Q)))
    (hE' : ContMDiff 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) (𝓡 4) Ctop
      (Function.uncurry (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)))
    (hV : ContMDiff (𝓡 3) (𝓡 4) Ctop (clampedSweep c₁ (fun t => 1 - t) P₁))
    (hW : ContMDiff (𝓡 3) (𝓡 4) Ctop (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u →
      colPlane β Q s (seamInv2 u) = colPlane β Q s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u →
      diskPlane Q (seamInv2 u) = diskPlane Q u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y →
      clampedSweep c₁ (fun t => 1 - t) P₁ (seamInv y) = clampedSweep c₁ (fun t => 1 - t) P₁ y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z →
      clampedSweep c₂ (fun t => 1 - t) P₂ (seamInv z) = clampedSweep c₂ (fun t => 1 - t) P₂ z)
    (hregBase : ∀ x ∈ Work.Drive.ppMeet (colPlane β Q) (fun _ u => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) →
      Work.Drive.PPRegAt (colPlane β Q) (fun _ u => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x)
    (ε : ℝ) (hε : 0 < ε)
    (htube : ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε' ∧
      (∀ x ∈ Work.Drive.ppMeet (ppShift Ξ w (unpackFst t) (colPlane β Q))
        (ppShift Ξ w (unpackSnd t) (fun _ u => diskPlane Q u))
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
        x ∈ K → Work.Drive.PPRegAt (ppShift Ξ w (unpackFst t) (colPlane β Q))
          (ppShift Ξ w (unpackSnd t) (fun _ u => diskPlane Q u))
          (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x) ∧
      (∀ x ∈ Work.Drive.ppMeet (ppShift Ξ w (unpackFst t) (colPlane β Q))
        (ppShift Ξ w (unpackSnd t) (fun _ u => diskPlane Q u))
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
        ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 ∧ ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1))
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {δc : ℝ} (hδ : 0 ≤ δc) (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hfin : (coreMeet Q c₁ P₁).Finite)
    (hfind : ∀ p ∈ coreMeet Q c₁ P₁, (diamMeet Q p.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c₁ (fun t => 1 - t) P₁ y)
    (ht5 : ∀ q ∈ coreMeet Q c₁ P₁,
      Odd (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard ↔
        Odd (coreSideCount Q c₂ P₂)) :
    Odd (topBdryMeet CappingSpace
        (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
          (![diskPlane Q, P₁, P₂] k)) 0).ncard ↔
      Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
  set V : EuclideanSpace ℝ (Fin 3) → CappingSpace := clampedSweep c₁ (fun t => 1 - t) P₁ with hVdef
  set W : EuclideanSpace ℝ (Fin 3) → CappingSpace := clampedSweep c₂ (fun t => 1 - t) P₂ with hWdef
  set E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u with hE'def
  obtain ⟨t, ht, heven⟩ :=
    exists_even_ppMeetEnd_add_intrinsic_strip (M := CappingSpace)
      Ξ hΞ.1 hΞ.2.1 (colPlane β Q) E' V W w K hK hE hE' hV hW hw hKcover hwleft hwright
      hregBase ε hε htube hseamU hseamU' hseamV hseamW
  have h0 : (ppMeetEnd (ppShift Ξ w (unpackFst t) (colPlane β Q))
        (ppShift Ξ w (unpackSnd t) E') V W 0).ncard = colCount β Q V W 0 := by
    rw [ppMeetEnd_zero_eq β Q Ξ w hΞ hw0 t V W,
      ncard_ppMeetEnd_eq_colCount β Q V W (Set.left_mem_Icc.mpr zero_le_one)]
  have h1 : (ppMeetEnd (ppShift Ξ w (unpackFst t) (colPlane β Q))
        (ppShift Ξ w (unpackSnd t) E') V W 1).ncard = colCount β Q V W 1 := by
    rw [ppMeetEnd_one_eq β Q Ξ w hΞ hw1 t V W,
      ncard_ppMeetEnd_eq_colCount β Q V W (Set.right_mem_Icc.mpr zero_le_one)]
  have heven' : Even (colCount β Q V W 0 + colCount β Q V W 1) := by
    rw [← h0, ← h1]
    exact heven
  exact odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even_nf β Q P₁ P₂ c₀ c₁ c₂ heven'
    hQseam hδ hβδ hδcut hfin hfind hbase ht5

end

end Work.Drive
