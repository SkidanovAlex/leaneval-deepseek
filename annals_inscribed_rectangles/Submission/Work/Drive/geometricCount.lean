import Mathlib
import Submission.Work.Drive.coreMeetSeamDefect
import Submission.Work.Drive.meetBoxEngine

/-!
# The *geometric* (pairing) count of the loop against the sweep, and its relation to the box count

`Work.Drive.coreSideCount Q c P = #(coreMeet Q c P)` counts *parameter pairs*
`(s, x) ∈ [0,1] × unitBox 2` at which the core loop meets the clamped sweep.  Both parameter domains
are quotients presented by closed boxes, so a meet at either *seam* is counted **twice**
(`Submission/Work/Drive/coreMeetSeamDefect.lean`), and the parity of the box count is therefore **not**
locally constant in the angle (it is flipped at the isolated angles where a meet crosses a seam; see
`Submission/Work/Drive/HN4_SEAM_DEFECT.md`).

The parameterisation-free object is the set of *points of `CappingSpace`* lying on both images,

> `coreMeetPt Q c P := coreLoop Q '' [0,1] ∩ clampedSweep c (fun t => 1 - t) P '' unitBox 2`,

whose cardinality is the route's mod-2 pairing `⟨[core loop], [sweep]⟩` (its parity is the side value
`b`).  This file records the two basic relations with the box count:

* `Work.Drive.coreMeetPt_subset` — the geometric meet set is the image of the box meet set;
* **`Work.Drive.coreSideCountPt_le`** — the geometric count is at most the box count (the box counts
  the seam meets twice);
* `Work.Drive.coreMeetPt_ncard_eq_iff` — equality of the two counts holds exactly when the
  parameterisation is injective on the box meet set, i.e. (in the design's geometry) exactly when no
  meet sits on a seam.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The geometric meet set of the loop with the sweep**: the points of `CappingSpace` that lie both
on the core loop (its parameter in `[0,1]`) and on the clamped sweep (its parameter in `unitBox 2`).
This is parameterisation-free (it is the image of `coreMeet` under the two parameterisations). -/
def coreMeetPt (Q : ℂ → CappingSpace) (c : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    Set CappingSpace :=
  coreLoop Q '' {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1} ∩
    clampedSweep c (fun t => 1 - t) P '' Submission.Drive.unitBox 2

/-- **The geometric (mod-2 pairing) count**: the number of *points* of `CappingSpace` on both the core
loop and the clamped sweep.  This is the parameterisation-free replacement for
`Work.Drive.coreSideCount`. -/
def coreSideCountPt (Q : ℂ → CappingSpace) (c : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    ℕ :=
  (coreMeetPt Q c P).ncard

/-- The geometric meet set is the image of the box meet set under the parameterisations. -/
theorem coreMeetPt_subset (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    coreMeetPt Q c P = (fun p : ℝ × Work.Drive.Amb 2 =>
      coreLoop Q p.1) '' coreMeet Q c P := by
  ext y
  constructor
  · rintro ⟨⟨t, ht, hty⟩, ⟨x, hx, hxy⟩⟩
    have hmem : (t, x) ∈ coreMeet Q c P := by
      rw [coreMeet, Set.mem_ofPred_eq]
      refine ⟨ht, hx, ?_⟩
      show coreLoop Q t = clampedSweep c (fun s => 1 - s) P x
      rw [hty]
      exact hxy.symm
    exact ⟨(t, x), hmem, hty⟩
  · rintro ⟨p, hp, hpy⟩
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨⟨p.1, h1, hpy⟩, ⟨p.2, h2, ?_⟩⟩
    show clampedSweep c (fun s => 1 - s) P p.2 = y
    rw [← h3]
    exact hpy

/-- **The geometric count is at most the box count** (at a configuration with finitely many parameter
meets, i.e. away from tangencies).  The box count counts every geometric meet at least once, and the
seam meets twice. -/
theorem coreSideCountPt_le (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hfin : (coreMeet Q c P).Finite) :
    coreSideCountPt Q c P ≤ coreSideCount Q c P := by
  rw [coreSideCountPt, coreSideCount, coreMeetPt_subset]
  exact Set.ncard_image_le hfin

/-- **Equality of the two counts is exactly injectivity of the parameterisation on the box meet set**
(at a configuration with finitely many parameter meets, i.e. away from tangencies). -/
theorem coreMeetPt_ncard_eq_iff (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hfin : (coreMeet Q c P).Finite) :
    coreSideCountPt Q c P = coreSideCount Q c P ↔
      Set.InjOn (fun p : ℝ × Work.Drive.Amb 2 => coreLoop Q p.1) (coreMeet Q c P) := by
  rw [coreSideCountPt, coreSideCount, coreMeetPt_subset]
  exact Set.ncard_image_iff hfin

end

end Work.Drive
