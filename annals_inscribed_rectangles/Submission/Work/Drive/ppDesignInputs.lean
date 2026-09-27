import Mathlib
import Submission.Work.Drive.ppIntrinsicStrip
import Submission.Work.Drive.ppParity.RepairedS3
import Submission.Work.Drive.exists_eps_ppShift_avoidances
import Submission.Work.Drive.transportFaces

/-!
# The design inputs of the intrinsic transport `T6`: the honest avoidances and the Sard package

`Submission/Work/Drive/ppIntrinsicStrip.lean` contains the two *consistent* forms of the intrinsic box
parity (S4) and of the transport `T6` (S5) — the versions of
`Work.Drive.exists_even_ppMeetEnd_add_intrinsic` and
`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic` with the (unused, and
jointly inconsistent with the other collar data) hypothesis `hwne` deleted.

`sWork.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_strip` still takes two
*geometric* inputs of the design:

* `havY`/`havZ` — the level-face avoidances `ftY2 x ∉ {0,1}`, `ftZ2 x ∉ {0,1}` at the honest pair
  meets, and
* `htube` — the Sard-plus-avoidance package: for every `ε' > 0` a parameter `τ` of norm `< ε'` at which
  every *perturbed* pair meet is regular **and** the perturbed meets still avoid the level faces.

This file produces both, from the design's geometric data.

* `Work.Drive.ppMeet_face_avoidances` — the honest avoidances, from the two **plane-disjointness**
  clauses (`P ∩ Pᵢ = ∅`, i.e. the design's `u ∈ Zc γ`), the two **level comparisons**
  ("the floors lie below the levels") and the two endpoint conditions of the cutoff: at the top face of
  the sweep the sweep *is* the plane, at the bottom face it is the shadow at the level `c`.  The chain
  lemmas `colPlane_ne_sweep_top`/`_bot`, `diskPlane_ne_sweep_top`/`_bot` are the proved, **chart-free**
  versions of `Submission/Work/Drive/transportFaces.lean`, so no chart bridge appears.

* `Work.Drive.exists_ppTubeData` — the package `htube`:
  * the **regularity** is the repaired intrinsic pair Sard
    `Work.Drive.exists_ppReg_shift_strip` (`ppParity/RepairedS3.lean`), whose conclusion is regularity
    at *every* meet in the box, hence in particular at the meets of `K`;
  * the **avoidance** is `Work.Drive.exists_eps_ppShift_avoidances`: the honest avoidances
    (`havY`/`havZ`) are stable under the perturbation, uniformly in a ball of parameters;
  * taking the minimum of the two radii gives the package for every `ε' > 0`.

With these two, the only remaining hypotheses of `T6` for a concrete configuration are the *design
data* (levels, cut fibres, finiteness, the basepoint condition and the T5 comparison) together with the
collar-honesty hypothesis `hregBase`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The honest level-face avoidances of the design's intrinsic pair map.**  At a meet of the
collapsed chart's plane `colPlane β Q` with the two swept planes `P₁`, `P₂`, the level coordinates of
the two sweep parameters are never `0` or `1`.

* `ftY2 x = 1` means the first sweep is the plane `P₁` itself (`clampedSweep_face_one`), and the image
  of the collapsed plane lies in the image of the chart's disk (`colPlane_mem_range_diskPlane`), so
  `P ∩ P₁ = ∅` excludes it; `ftY2 x = 0` means the sweep is the shadow of `P₁` at the level `c₁`
  (`clampedSweep_face_zero`), whose level is strictly below the chart's levels.
* The same for `ftZ2 x` against the *uncollapsed* plane `diskPlane Q`. -/
theorem ppMeet_face_avoidances {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t)
    (Q : ℂ → CappingSpace) (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlev₁ : ∀ z : ℂ, ‖z‖ ≤ 1 → c₁ < levelOf (Q z))
    (hlev₂ : ∀ z : ℂ, ‖z‖ ≤ 1 → c₂ < levelOf (Q z))
    (hdisj₁ : Disjoint (Set.range (diskPlane Q)) (Set.range P₁))
    (hdisj₂ : Disjoint (Set.range (diskPlane Q)) (Set.range P₂)) :
    (∀ x ∈ ppMeet (colPlane β Q) (fun _ u => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1) ∧
    (∀ x ∈ ppMeet (colPlane β Q) (fun _ u => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1) := by
  constructor
  · intro x hx
    rw [mem_ppMeet] at hx
    obtain ⟨hbox, h1, -⟩ := hx
    have hboxU := ftU_mem_unitBox hbox
    have hboxY := ftY_mem_unitBox hbox
    refine ⟨?_, ?_⟩
    · intro h0
      exact colPlane_ne_sweep_bot hβpos hβ Q P₁ c₁ hc₁ hlev₁ (ftS x) (ftU x) (ftY x)
        hboxU hboxY (by rw [ftY_two]; exact h0) h1
    · intro h1'
      exact colPlane_ne_sweep_top hβpos hβ Q P₁ c₁ hdisj₁ (ftS x) (ftU x) (ftY x)
        hboxU hboxY (by rw [ftY_two]; exact h1') h1
  · intro x hx
    rw [mem_ppMeet] at hx
    obtain ⟨hbox, -, h2⟩ := hx
    have hboxU := ftU_mem_unitBox hbox
    have hboxZ := ftZ_mem_unitBox hbox
    refine ⟨?_, ?_⟩
    · intro h0
      exact diskPlane_ne_sweep_bot Q P₂ c₂ hc₂ hlev₂ (ftU x) (ftZ x)
        hboxU hboxZ (by rw [ftZ_two]; exact h0) h2
    · intro h1
      exact diskPlane_ne_sweep_top Q P₂ c₂ hdisj₂ (ftU x) (ftZ x)
        hboxU hboxZ (by rw [ftZ_two]; exact h1) h2

/-- **The Sard-and-avoidance package of the intrinsic transport `T6`.**  For every `ε' > 0` there is a
perturbation parameter `τ : ℝ⁸` of norm `< ε'` such that

* every meet of the perturbed pair family is `PPRegAt` (the repaired intrinsic pair Sard
  `Work.Drive.exists_ppReg_shift_strip`), and
* every meet of the perturbed pair family still avoids the two level faces
  (`Work.Drive.exists_eps_ppShift_avoidances`, applied to the honest avoidances `havY`/`havZ`).

This is exactly the hypothesis `htube` of
`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_strip` (whose first clause
is asked only on the meets lying in `K`; regularity at *every* meet is stronger). -/
theorem exists_ppTubeData
    (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {δ : ℝ}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (hΞ : ChartPert Q 4 Ξ)
    (hδ : 0 ≤ δ)
    (hwne : ∀ x ∈ K, δ < ftS x → ftS x < 1 - δ → w (ftS x) ≠ 0)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ ftS x → ftS x ≤ 1 - δ →
      x ∈ interior K)
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) →
      ppMeet E E' V W x → PPRegAt E E' V W x)
    (havY : ∀ x ∈ ppMeet E E' V W, ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ ppMeet E E' V W, ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1) :
    ∀ ε' : ℝ, 0 < ε' → ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ε' ∧
      (∀ x ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W,
        PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x) ∧
      (∀ x ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W,
        ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 ∧ ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1) := by
  intro ε' hε'
  -- the radius of the perturbation-stable avoidances
  have hEc : Continuous fun x : EuclideanSpace ℝ (Fin 9) => E (ftS x) (ftU x) :=
    hE.continuous.comp continuous_ftSU
  have hE'c : Continuous fun x : EuclideanSpace ℝ (Fin 9) => E' (ftS x) (ftU x) :=
    hE'.continuous.comp continuous_ftSU
  have hVc : Continuous fun x : EuclideanSpace ℝ (Fin 9) => V (ftY x) :=
    hV.continuous.comp continuous_ftY
  have hWc : Continuous fun x : EuclideanSpace ℝ (Fin 9) => W (ftZ x) :=
    hW.continuous.comp continuous_ftZ
  obtain ⟨εa, hεa, hav⟩ := exists_eps_ppShift_avoidances Ξ hΞ.1 hΞ.2.1.continuous E E' V W w
    hw.continuous hEc hE'c hVc hWc havY havZ
  -- the repaired Sard, at a radius below both bounds
  have hpos : 0 < min ε' εa / 2 := by positivity
  obtain ⟨τ, hτ, hreg⟩ := exists_ppReg_shift_strip Q E E' V W Ξ w hE hE' hV hW hw hΞ K hK δ hδ
    hwne hKcover hwleft hwright hregBase (min ε' εa / 2) hpos
  have hτ' : ‖τ‖ < ε' := lt_of_lt_of_le hτ (by
    have h1 : min ε' εa / 2 ≤ min ε' εa := by linarith [le_of_lt hpos]
    exact le_trans h1 (min_le_left _ _))
  have hτa : ‖τ‖ < εa := lt_of_lt_of_le hτ (by
    have h1 : min ε' εa / 2 ≤ min ε' εa := by linarith [le_of_lt hpos]
    exact le_trans h1 (min_le_right _ _))
  refine ⟨τ, hτ', ?_, hav τ hτa⟩
  intro x hx
  exact hreg x (mem_ppMeet.mp hx).1 hx

end

end Work.Drive
