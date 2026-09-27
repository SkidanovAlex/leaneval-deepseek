import Mathlib
import Submission.Work.Drive.pairMeetDefs
import Submission.Work.Drive.even_ncard_pairMeetBdry
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.collapseFaceAvoid

/-!
# The chart bridge of the radial-collapse pair count (T6 step (v))

`Submission/Work/Drive/TRANSPORT_COLLAPSE_STATUS.md` §7.7(v): the honest count of the radial collapse
is `CappingSpace`-valued (`Work.Drive.colMeet` / `colCount`), while the box-parity engine T1/T3
(`Work.Drive.even_ncard_pairMeetBdry`) counts the zeros of a *charted* difference map
`pairDiff E E' V W : ℝ⁹ → ℝ⁸`.  The two counts are the same set of parameter triples once a chart
`chr` of the capping space — injective on a set `A` containing all the values of the four chains — is
chosen: the equality `colPlane β Q s u = V y` becomes `chr (colPlane β Q s u) = chr (V y)`.

This file supplies

* `colMeet_eq_pairMeetSet` — the set equality (a rewrite plus one application of `Set.InjOn`);
* `ncard_colCount_eq_pairMeetSet` — its `ncard` form;
* `even_ncard_colCount_zero_add_one_of_pairMeetBdry` — the transfer of any even-parity statement about
  the charted pair counts to the honest collapse counts, i.e. the first bullet of the transport
  `Even (colCount β Q V W 0 + colCount β Q V W 1)`;
* `pairMeet_ftY2_ne` / `pairMeet_ftZ2_ne` — the *charted* form of the level-face avoidances `havY`/`havZ`
  of the engine, obtained from the honest avoidances of
  `Submission/Work/Drive/collapseFaceAvoid.lean` through the same injectivity.

Everything is stated with the chart `chr` and the set `A` abstract, so that the design may instantiate
them with any chart of `CappingSpace` (e.g. `chartAt ℝ⁴ p`, whose *target* is opaque — see
`CHART_SHIFT_HSURJ_STATUS.md` §10: nothing about the shape of the target is needed here, only
injectivity on the source `A`).
-/

set_option autoImplicit false

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The chart bridge -/

/-- **The chart bridge.**  A chart `chr` injective on a set `A` containing the values of all four chains
identifies the honest collapse meet set with the charted pair meet set of T1. -/
theorem colMeet_eq_pairMeetSet {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hinj : Set.InjOn chr A)
    (hE : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE' : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), V y ∈ A)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), W z ∈ A)
    (s : ℝ) :
    colMeet β Q V W s
      = pairMeetSet (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
          (fun y => chr (V y)) (fun z => chr (W z)) s := by
  ext p
  constructor
  · intro hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hp
    exact ⟨h1, h2, h3, by show chr (colPlane β Q s p.1) = chr (V p.2.1); rw [h4],
      by show chr (diskPlane Q p.1) = chr (W p.2.2); rw [h5]⟩
  · intro hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hp
    exact ⟨h1, h2, h3, hinj (hE _ _) (hV _) h4, hinj (hE' _) (hW _) h5⟩

/-- **The chart bridge, `ncard` form.** -/
theorem ncard_colCount_eq_pairMeetSet {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hinj : Set.InjOn chr A)
    (hE : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE' : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), V y ∈ A)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), W z ∈ A)
    (s : ℝ) :
    colCount β Q V W s
      = (pairMeetSet (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
          (fun y => chr (V y)) (fun z => chr (W z)) s).ncard := by
  rw [colCount, colMeet_eq_pairMeetSet hinj hE hE' hV hW s]

/-- **The parity transfer of the transport's first bullet.**  Any even-parity statement about the two
end counts of the charted pair (`Work.Drive.even_ncard_pairMeetBdry`, whose hypotheses are the design's
to supply) transfers to the honest collapse counts. -/
theorem even_ncard_colCount_zero_add_one_of_pairMeetBdry {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hinj : Set.InjOn chr A)
    (hE : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE' : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), V y ∈ A)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), W z ∈ A)
    (h : Even ((pairMeetSet (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
              (fun y => chr (V y)) (fun z => chr (W z)) 0).ncard
        + (pairMeetSet (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
              (fun y => chr (V y)) (fun z => chr (W z)) 1).ncard)) :
    Even (colCount β Q V W 0 + colCount β Q V W 1) := by
  rw [ncard_colCount_eq_pairMeetSet hinj hE hE' hV hW 0,
    ncard_colCount_eq_pairMeetSet hinj hE hE' hV hW 1]
  exact h

/-! ## 2. The charted level-face avoidances `havY`/`havZ` -/

/-- The level coordinate `x 5` of the box is the second coordinate of the first sweep parameter. -/
lemma ftY2_eq_ftY_two (x : EuclideanSpace ℝ (Fin 9)) : ftY2 x = ftY x 2 := by
  rw [Work.Drive.PMB.ftY2_eq_coord, Work.Drive.PMB.ftY_apply]
  exact congrArg (fun i : Fin 9 => x i) (by decide)

/-- The level coordinate `x 8` of the box is the second coordinate of the second sweep parameter. -/
lemma ftZ2_eq_ftZ_two (x : EuclideanSpace ℝ (Fin 9)) : ftZ2 x = ftZ x 2 := by
  rw [Work.Drive.PMB.ftZ2_eq_coord, Work.Drive.PMB.ftZ_apply]
  exact congrArg (fun i : Fin 9 => x i) (by decide)

/-- **`havY` from the honest top-face avoidance.**  At a charted pair meet whose first sweep parameter
is on the top face (`ftY2 x = 1`), the honest equation `colPlane β Q s u = P₁ y'` holds, which the
avoidance `Work.Drive.colPlane_ne_clampedSweep_top` excludes. -/
theorem pairMeet_ftY2_ne_top {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ} {ψ : ℝ → ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hψ1 : ψ 1 = 0) (hβpos : ∀ t : ℝ, 0 < β t) (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t)
    (hcap : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ < 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcirc : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ = 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hinj : Set.InjOn chr A)
    (hE : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE' : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₁ y ∈ A)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₂ z ∈ A)
    {x : EuclideanSpace ℝ (Fin 9)}
    (hwy : ‖sqDisk (foldBox (mk2 (ftY x 0) (ftY x 1)))‖ < 1)
    (hzero : pairDiff (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
      (fun y => chr (clampedSweep c ψ P₁ y)) (fun z => chr (clampedSweep c ψ P₂ z)) x = 0) :
    ftY2 x ≠ 1 := by
  intro h1
  rw [ftY2_eq_ftY_two] at h1
  obtain ⟨hV', _hW'⟩ := (pairDiff_eq_zero_iff _ _ _ _ x).mp hzero
  have hhon : colPlane β Q (ftS x) (ftU x) = clampedSweep c ψ P₁ (ftY x) :=
    hinj (hE _ _) (hV _) hV'
  exact (colPlane_ne_clampedSweep_top hβpos hβ hψ1 hcap hcirc (ftS x) (ftU x) (ftY x) h1
    hwy) hhon

/-- **`havY` from the honest floor avoidance.**  At a charted pair meet whose first sweep parameter is
on the floor (`ftY2 x = 0`), the honest equation `colPlane β Q s u = shadow c (P₁ y')` holds, which the
level bound excludes. -/
theorem pairMeet_ftY2_ne_floor {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ} {ψ : ℝ → ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hc : 0 < c) (hψ0 : ψ 0 = 1) (hβpos : ∀ t : ℝ, 0 < β t) (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (hinj : Set.InjOn chr A)
    (hE : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE' : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₁ y ∈ A)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₂ z ∈ A)
    {x : EuclideanSpace ℝ (Fin 9)}
    (hzero : pairDiff (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
      (fun y => chr (clampedSweep c ψ P₁ y)) (fun z => chr (clampedSweep c ψ P₂ z)) x = 0) :
    ftY2 x ≠ 0 := by
  intro h1
  rw [ftY2_eq_ftY_two] at h1
  obtain ⟨hV', _hW'⟩ := (pairDiff_eq_zero_iff _ _ _ _ x).mp hzero
  have hhon : colPlane β Q (ftS x) (ftU x) = clampedSweep c ψ P₁ (ftY x) :=
    hinj (hE _ _) (hV _) hV'
  exact (colPlane_ne_clampedSweep_floor hβpos hβ hc hψ0 hlev (ftS x) (ftU x) (ftY x) h1) hhon

/-- **`havY`.**  At every zero of the charted difference map of the collapse pair whose first sweep
parameter is off the seam of its square, the level coordinate `ftY2` is neither `0` nor `1`. -/
theorem pairMeet_ftY2_ne {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ} {ψ : ℝ → ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hc : 0 < c) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hβpos : ∀ t : ℝ, 0 < β t) (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t)
    (hcap : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ < 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcirc : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ = 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (hinj : Set.InjOn chr A)
    (hE : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE' : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₁ y ∈ A)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₂ z ∈ A)
    {x : EuclideanSpace ℝ (Fin 9)}
    (hwy : ‖sqDisk (foldBox (mk2 (ftY x 0) (ftY x 1)))‖ < 1)
    (hzero : pairDiff (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
      (fun y => chr (clampedSweep c ψ P₁ y)) (fun z => chr (clampedSweep c ψ P₂ z)) x = 0) :
    ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 :=
  ⟨pairMeet_ftY2_ne_floor hc hψ0 hβpos hβ hlev hinj hE hE' hV hW hzero,
   pairMeet_ftY2_ne_top hψ1 hβpos hβ hcap hcirc hinj hE hE' hV hW hwy hzero⟩

/-- **`havZ`.**  The second block's version of `pairMeet_ftY2_ne`: at every zero of the charted
difference map whose second sweep parameter is off the seam of its square, the level coordinate `ftZ2`
is neither `0` nor `1`. -/
theorem pairMeet_ftZ2_ne {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ} {ψ : ℝ → ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hc : 0 < c) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hcap : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ ≤ 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₂ y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (hinj : Set.InjOn chr A)
    (hE : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE' : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₁ y ∈ A)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₂ z ∈ A)
    {x : EuclideanSpace ℝ (Fin 9)}
    (hwz : ‖sqDisk (foldBox (mk2 (ftZ x 0) (ftZ x 1)))‖ < 1)
    (hzero : pairDiff (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
      (fun y => chr (clampedSweep c ψ P₁ y)) (fun z => chr (clampedSweep c ψ P₂ z)) x = 0) :
    ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1 := by
  obtain ⟨_hV', hW'⟩ := (pairDiff_eq_zero_iff _ _ _ _ x).mp hzero
  have hhon : diskPlane Q (ftU x) = clampedSweep c ψ P₂ (ftZ x) := hinj (hE' _) (hW _) hW'
  constructor
  · rw [ftZ2_eq_ftZ_two]
    intro h1
    exact (diskPlane_ne_clampedSweep_floor hc hψ0 hlev (ftU x) (ftZ x) h1) hhon
  · rw [ftZ2_eq_ftZ_two]
    intro h1
    exact (diskPlane_ne_clampedSweep_top hψ1 hcap (ftU x) (ftZ x) h1 hwz) hhon

/-- **`havY` from the honest disjointness data and the engine's one-face clause.**  The "off the seam"
hypothesis of `pairMeet_ftY2_ne` is *not* an extra design input: if the level coordinate `ftY2 x` is on
a face of the box then `x` is a boundary point of the box, so the engine's face clause gives that all
the *other* coordinates are strictly interior — in particular `x 3, x 4 ∈ (0,1)`, which is exactly
`‖sqDisk (foldBox (mk2 (x 3) (x 4)))‖ < 1`
(`Work.Drive.norm_sqDisk_foldBox_lt_one_of_mem_Ioo`). -/
theorem pairMeet_ftY2_ne_of_hface {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ} {ψ : ℝ → ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hc : 0 < c) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t)
    (hcap : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ < 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcirc : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ = 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (hinj : Set.InjOn chr A)
    (hE : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE' : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₁ y ∈ A)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₂ z ∈ A)
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8,
      pairDiff (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
        (fun y => chr (clampedSweep c ψ P₁ y)) (fun z => chr (clampedSweep c ψ P₂ z)) x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1))
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Submission.Drive.unitBox 8)
    (hzero : pairDiff (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
      (fun y => chr (clampedSweep c ψ P₁ y)) (fun z => chr (clampedSweep c ψ P₂ z)) x = 0) :
    ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 := by
  have hfive : x 5 = ftY2 x := (Work.Drive.PMB.ftY2_eq_coord x).symm
  refine ⟨pairMeet_ftY2_ne_floor hc hψ0 hβpos hβ hlev hinj hE hE' hV hW hzero, ?_⟩
  intro h1
  -- `x` is a boundary point of the box, so the face clause applies
  have hxbd : x ∈ Submission.Drive.unitBoxBdry 8 :=
    ⟨hx, 5, Or.inr (by rw [hfive]; exact h1)⟩
  obtain ⟨i, hi, hint⟩ := hface x hxbd hzero
  have hfive_one : x 5 = 1 := by rw [hfive]; exact h1
  have hi3 : i ≠ 3 := by
    rintro rfl
    have h5 := hint 5 (by decide)
    rcases hi with h | h <;> linarith [h5.1, h5.2, hfive_one]
  have hi4 : i ≠ 4 := by
    rintro rfl
    have h5 := hint 5 (by decide)
    rcases hi with h | h <;> linarith [h5.1, h5.2, hfive_one]
  have hwy : ‖sqDisk (foldBox (mk2 (ftY x 0) (ftY x 1)))‖ < 1 :=
    norm_sqDisk_foldBox_lt_one_of_mem_Ioo
      (by rw [Work.Drive.PMB.ftY_zero]; exact hint 3 (Ne.symm hi3))
      (by rw [Work.Drive.PMB.ftY_one]; exact hint 4 (Ne.symm hi4))
  exact pairMeet_ftY2_ne_top hψ1 hβpos hβ hcap hcirc hinj hE hE' hV hW hwy hzero h1

/-- **`havZ` from the honest disjointness data and the engine's one-face clause** — the second block's
version of `pairMeet_ftY2_ne_of_hface`. -/
theorem pairMeet_ftZ2_ne_of_hface {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ} {ψ : ℝ → ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hc : 0 < c) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hcap : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ ≤ 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₂ y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (hinj : Set.InjOn chr A)
    (hE : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE' : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hV : ∀ y : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₁ y ∈ A)
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₂ z ∈ A)
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8,
      pairDiff (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
        (fun y => chr (clampedSweep c ψ P₁ y)) (fun z => chr (clampedSweep c ψ P₂ z)) x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1))
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Submission.Drive.unitBox 8)
    (hzero : pairDiff (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
      (fun y => chr (clampedSweep c ψ P₁ y)) (fun z => chr (clampedSweep c ψ P₂ z)) x = 0) :
    ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1 := by
  have height : x 8 = ftZ2 x := (Work.Drive.PMB.ftZ2_eq_coord x).symm
  obtain ⟨_hV', hW'⟩ := (pairDiff_eq_zero_iff _ _ _ _ x).mp hzero
  have hhon : diskPlane Q (ftU x) = clampedSweep c ψ P₂ (ftZ x) := hinj (hE' _) (hW _) hW'
  constructor
  · rw [ftZ2_eq_ftZ_two]
    intro h0
    exact (diskPlane_ne_clampedSweep_floor hc hψ0 hlev (ftU x) (ftZ x) h0) hhon
  · rw [ftZ2_eq_ftZ_two]
    intro h1
    have hxbd : x ∈ Submission.Drive.unitBoxBdry 8 :=
      ⟨hx, 8, Or.inr (by rw [height]; exact h1)⟩
    obtain ⟨i, hi, hint⟩ := hface x hxbd hzero
    have height_one : x 8 = 1 := by rw [height]; exact h1
    have hi6 : i ≠ 6 := by
      rintro rfl
      have h8 := hint 8 (by decide)
      rcases hi with h | h <;> linarith [h8.1, h8.2, height_one]
    have hi7 : i ≠ 7 := by
      rintro rfl
      have h8 := hint 8 (by decide)
      rcases hi with h | h <;> linarith [h8.1, h8.2, height_one]
    have hwz : ‖sqDisk (foldBox (mk2 (ftZ x 0) (ftZ x 1)))‖ < 1 :=
      norm_sqDisk_foldBox_lt_one_of_mem_Ioo
        (by rw [Work.Drive.PMB.ftZ_zero]; exact hint 6 (Ne.symm hi6))
        (by rw [Work.Drive.PMB.ftZ_one]; exact hint 7 (Ne.symm hi7))
    exact (diskPlane_ne_clampedSweep_top hψ1 hcap (ftU x) (ftZ x) h1 hwz) hhon

/-! ## 3. The T6 endpoint: `Even (K 0 + K 1)` from the design's data

The capstone below assembles the two reduced hypotheses of `even_ncard_pairMeetBdry` — the two
level-face avoidances (§2) and the four seam invariances (`colPlane_seamInv2`, `diskPlane_seamInv2`,
`clampedSweep_seamInv`) — so that the box-parity conclusion `Even (K 0 + K 1)` of the radial collapse
is available from the design's honest data alone: the chart's data, the sweep's data, the plane
disjointness, the level bound, the injectivity/residency of the chart, the smoothness of the four
charted chains and the two genericity fields `hreg`/`hface` (which the pair Sard analyser,
`Submission/Work/Drive/pairMeetSard.lean`, produces from a rich family). -/

/-- **The charted pair difference map of the collapse family.** -/
def chartedPairDiff (β : ℝ → ℝ) (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (chr : CappingSpace → EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
  pairDiff (fun s u => chr (colPlane β Q s u)) (fun u => chr (diskPlane Q u))
    (fun y => chr (clampedSweep c ψ P₁ y)) (fun z => chr (clampedSweep c ψ P₂ z))

/-- **The first bullet of the transport.**  `Even (K 0 + K 1)` for the radial collapse, from the
design's data. -/
theorem even_ncard_colCount_zero_add_one
    {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ} {ψ : ℝ → ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {chr : CappingSpace → EuclideanSpace ℝ (Fin 4)} {A : Set CappingSpace}
    (hβpos : ∀ t : ℝ, 0 < β t) (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (hβ1 : β 1 = 1)
    (hc : 0 < c) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hPseam₁ : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₁ y = P₁ (seamInv2 y))
    (hPseam₂ : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₂ y = P₂ (seamInv2 y))
    (hinj : Set.InjOn chr A)
    (hEA : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ A)
    (hE'A : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ A)
    (hVA : ∀ y : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₁ y ∈ A)
    (hWA : ∀ z : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₂ z ∈ A)
    (hsmE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun s u => chr (colPlane β Q s u))))
    (hsmE' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => chr (diskPlane Q u)))
    (hsmV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => chr (clampedSweep c ψ P₁ y)))
    (hsmW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => chr (clampedSweep c ψ P₂ z)))
    (hcap₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ < 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcirc₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ = 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcap₂ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ ≤ 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₂ y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (hreg : ∀ x ∈ Submission.Drive.unitBox 8, chartedPairDiff β Q c ψ P₁ P₂ chr x = 0 →
      Function.Surjective (fderiv ℝ (chartedPairDiff β Q c ψ P₁ P₂ chr) x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8, chartedPairDiff β Q c ψ P₁ P₂ chr x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (chartedPairDiff β Q c ψ P₁ P₂ chr) x v.1)) :
    Even (colCount β Q (clampedSweep c ψ P₁) (clampedSweep c ψ P₂) 0
      + colCount β Q (clampedSweep c ψ P₁) (clampedSweep c ψ P₂) 1) := by
  -- the four charted chains of the pair
  set E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4) :=
    fun s u => chr (colPlane β Q s u) with hE
  set E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4) :=
    fun u => chr (diskPlane Q u) with hE'
  set VecV : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4) :=
    fun y => chr (clampedSweep c ψ P₁ y) with hV
  set VecW : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4) :=
    fun z => chr (clampedSweep c ψ P₂ z) with hW
  have hreg' : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' VecV VecW x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff E E' VecV VecW) x) := hreg
  have hface' : ∀ x ∈ Submission.Drive.unitBoxBdry 8, pairDiff E E' VecV VecW x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff E E' VecV VecW) x v.1) := hface
  have hweak : ∀ x ∈ Submission.Drive.unitBoxBdry 8, pairDiff E E' VecV VecW x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) :=
    fun x hx h0 => by
      obtain ⟨i, hi, hint, -⟩ := hface' x hx h0
      exact ⟨i, hi, hint⟩
  have havY : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' VecV VecW x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 :=
    fun x hx h0 => pairMeet_ftY2_ne_of_hface hc hψ0 hψ1 hβpos hβ hcap₁ hcirc₁ hlev hinj hEA hE'A hVA
      hWA hweak hx h0
  have havZ : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' VecV VecW x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1 :=
    fun x hx h0 => pairMeet_ftZ2_ne_of_hface hc hψ0 hψ1 hcap₂ hlev hinj hEA hE'A hVA hWA hweak hx h0
  have hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u →
      E s (seamInv2 u) = E s u :=
    fun s u hu => by rw [hE]; exact congrArg chr (colPlane_seamInv2 hβ1 s hQseam hu)
  have hseamU' : ∀ u : EuclideanSpace ℝ (Fin 2), onSeam2 u → E' (seamInv2 u) = E' u :=
    fun u hu => by rw [hE']; exact congrArg chr (diskPlane_seamInv2 hQseam hu)
  have hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y →
      VecV (seamInv y) = VecV y :=
    fun y hy => by
      rw [hV]
      exact congrArg chr (clampedSweep_seamInv c ψ P₁ hPseam₁ y hy).symm
  have hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z →
      VecW (seamInv z) = VecW z :=
    fun z hz => by
      rw [hW]
      exact congrArg chr (clampedSweep_seamInv c ψ P₂ hPseam₂ z hz).symm
  have heven := even_ncard_pairMeetBdry E E' VecV VecW hsmE hsmE' hsmV hsmW hreg' hface'
    hseamU hseamU' hseamV hseamW havY havZ
  exact even_ncard_colCount_zero_add_one_of_pairMeetBdry hinj hEA hE'A hVA hWA heven

end

end Work.Drive
