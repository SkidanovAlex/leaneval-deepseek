import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Bdry
import Submission.Work.Drive.transportWiring
import Submission.Work.Drive.ppParity.Shift
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.collapseT5
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.transportThreeLevel
import Submission.Work.Drive.exists_even_ppMeetEnd_add_intrinsic
import Submission.Work.Drive.ncard_ppMeetEnd_eq_colCount
import Submission.Work.Drive.exists_eps_ppShift_avoidances

/-!
# S5 of the lead's residency plan: the intrinsic transport `T6` for the design's chains

The last step of `Submission/Work/Drive/NOTES_LEAD_residency.md` (see
`Submission/Work/Drive/PPPARITY_STATUS.md`).  `Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even`
(`transportWiring.lean`) proves the multiplicativity (`T6`)

> `Odd (topBdryMeet (the three clamped sweeps) 0).ncard ↔ Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂)`

from the box-parity conclusion `heven : Even (colCount β Q V W 0 + colCount β Q V W 1)` — it is
**chart-free**, so the whole chart-residency obligation `hresQ`/`hresV`/`hresW` of the older
statements disappears.  This file records the remaining glue: `heven` is produced from

* the intrinsic box parity `Work.Drive.exists_even_ppMeetEnd_add_intrinsic` (S4), whose two end
  counts are exactly `colCount β Q V W 0` and `colCount β Q V W 1` by the chart-free bridge
  `Work.Drive.ncard_ppMeetEnd_eq_colCount` (the perturbation is inactive at the ends: `w 0 = w 1 = 0`
  and `Ξ 0 = id`).

The statement below is the design-facing form of `T6`: it drops `hresQ`/`hresV`/`hresW`, the
separation data `AY BY BY' AZ BZ BZ'`, `dY dZ`, `ε`/`hbd` and the charted `hregBase`/`hfaceBase`, and
carries instead the perturbation `Ξ` (via `ChartPert`), the self-centred collar regularity
`hregBase` and the perturbed genericity package `htube` that S3 produces
(`exists_ppReg_shift` with its coordinate form; the avoidances come from
`Work.Drive.exists_eps_ppShift_avoidances`).

This file is the assembly *target* only: it is stated here because its hypotheses mention the
`CappingSpace` charted structure (whose instances cannot be installed in a *delegated* statement, cf.
`PPPARITY_STATUS.md` §4), so it must be proved in place, once S2/S3/S4 have landed.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## The two ends of the perturbed chains are the honest ones

At `s = 0` (and `s = 1`) the weight vanishes (`w 0 = w 1 = 0`) and `Ξ 0 = id`
(`ChartPert`'s first clause), so the perturbed chain *is* the honest one, and the two end sets of S4
are the engine's `K 0` and `K 1` (through the bridge `ncard_ppMeetEnd_eq_colCount`). -/

/-- The perturbed first chain at the family parameter `0` is the disk presentation. -/
lemma ppShift_zero_eq_diskPlane (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (w : ℝ → ℝ) (hΞ : ChartPert Q 4 Ξ) (hw0 : w 0 = 0)
    (τ : EuclideanSpace ℝ (Fin 8)) :
    ppShift Ξ w (unpackFst τ) (colPlane β Q) 0 = diskPlane Q := by
  funext u
  simp only [ppShift, hw0, zero_smul]
  rw [hΞ.1 (colPlane β Q 0 u), congrFun (colPlane_zero β Q) u]

/-- The perturbed second chain at the family parameter `0` is the disk presentation. -/
lemma ppShift_zero_eq_diskPlane' (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (w : ℝ → ℝ) (hΞ : ChartPert Q 4 Ξ) (hw0 : w 0 = 0)
    (τ : EuclideanSpace ℝ (Fin 8)) :
    ppShift Ξ w (unpackSnd τ) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u) 0
      = diskPlane Q := by
  funext u
  simp only [ppShift, hw0, zero_smul]
  exact hΞ.1 (diskPlane Q u)

/-- The perturbed first chain at the family parameter `1` is the honest one. -/
lemma ppShift_one_fst (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (w : ℝ → ℝ) (hΞ : ChartPert Q 4 Ξ) (hw1 : w 1 = 0)
    (τ : EuclideanSpace ℝ (Fin 8)) :
    ppShift Ξ w (unpackFst τ) (colPlane β Q) 1 = colPlane β Q 1 := by
  funext u
  exact ppShift_eq_of_eq_zero hΞ.1 hw1 u

/-- The perturbed second chain at the family parameter `1` is the honest one. -/
lemma ppShift_one_snd (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (w : ℝ → ℝ) (hΞ : ChartPert Q 4 Ξ) (hw1 : w 1 = 0)
    (τ : EuclideanSpace ℝ (Fin 8)) :
    ppShift Ξ w (unpackSnd τ) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u) 1
      = (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u) 1 := by
  funext u
  exact ppShift_eq_of_eq_zero hΞ.1 hw1 u

/-- **The end set of S4 at `s = 1` is the honest one** (as sets). -/
lemma ppMeetEnd_one_eq (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (w : ℝ → ℝ) (hΞ : ChartPert Q 4 Ξ) (hw1 : w 1 = 0)
    (τ : EuclideanSpace ℝ (Fin 8))
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    ppMeetEnd (ppShift Ξ w (unpackFst τ) (colPlane β Q))
        (ppShift Ξ w (unpackSnd τ) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u))
        V W 1
      = ppMeetEnd (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
          V W 1 := by
  refine Set.ext fun x => ?_
  by_cases hft : ftS x = 1
  · have h1 := congrFun (ppShift_one_fst β Q Ξ w hΞ hw1 τ) (ftU x)
    have h2 := congrFun (ppShift_one_snd Q Ξ w hΞ hw1 τ) (ftU x)
    simp only [mem_ppMeetEnd, mem_ppMeet]
    rw [hft]
    simp only [h1, h2]
  · simp only [mem_ppMeetEnd]
    constructor
    · rintro ⟨-, h⟩; exact absurd h hft
    · rintro ⟨-, h⟩; exact absurd h hft

/-- **The end set of S4 at `s = 0` is the honest one** (as sets): the perturbed chains agree with
`colPlane β Q` and `diskPlane Q` there, because `w 0 = 0` and `Ξ 0 = id`. -/
lemma ppMeetEnd_zero_eq (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (w : ℝ → ℝ) (hΞ : ChartPert Q 4 Ξ) (hw0 : w 0 = 0)
    (τ : EuclideanSpace ℝ (Fin 8))
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    ppMeetEnd (ppShift Ξ w (unpackFst τ) (colPlane β Q))
        (ppShift Ξ w (unpackSnd τ) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u))
        V W 0
      = ppMeetEnd (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
          V W 0 := by
  refine Set.ext fun x => ?_
  by_cases hft : ftS x = 0
  · have h1 := congrFun (ppShift_zero_eq_diskPlane β Q Ξ w hΞ hw0 τ) (ftU x)
    have h2 := congrFun (ppShift_zero_eq_diskPlane' Q Ξ w hΞ hw0 τ) (ftU x)
    have h3 := congrFun (colPlane_zero β Q) (ftU x)
    simp only [mem_ppMeetEnd, mem_ppMeet]
    rw [hft]
    simp only [h1, h2, h3]
  · simp only [mem_ppMeetEnd]
    constructor
    · rintro ⟨-, h⟩; exact absurd h hft
    · rintro ⟨-, h⟩; exact absurd h hft

/-- **S5 — the intrinsic transport `T6` for the design's chains.**  Everything except the engine's own
data (`hfibV`, `hfibW`, `hQseam`, `hδ`, `hβδ`, `hδcut`, `hfin`, `hfind`, `hbase`, `ht5`, unchanged from
`odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even`) is hypothesis naming the *intrinsic* pair data:
the smoothness of the four honest chains, the four seam invariances, the self-centred collar
regularity and the perturbed package `htube`. -/
theorem odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {δ : ℝ}
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hw : ContDiff ℝ Ctop w) (hwne : ∀ x ∈ K, w (ftS x) ≠ 0)
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
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₂ (fun t => 1 - t) P₂) u).ncard = 1)
    {δc : ℝ} (hδ : 0 ≤ δc) (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hfin : (coreMeet Q c₁ P₁).Finite)
    (hfind : ∀ p ∈ coreMeet Q c₁ P₁, (diamMeet Q p.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c₁ (fun t => 1 - t) P₁ y)
    (ht5 : ∀ t : ℝ, Odd (diamMeet Q t (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard ↔
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
    exists_even_ppMeetEnd_add_intrinsic (M := CappingSpace)
      Ξ hΞ.1 hΞ.2.1 (colPlane β Q) E' V W w K hK hE hE' hV hW hw hwne hKcover hwleft hwright
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
  exact odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even β Q P₁ P₂ c₀ c₁ c₂ heven' hfibV hfibW
    hQseam hδ hβδ hδcut hfin hfind hbase ht5


end

end Work.Drive
