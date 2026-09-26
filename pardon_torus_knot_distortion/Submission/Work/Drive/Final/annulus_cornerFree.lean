import Mathlib
import Submission.Work.Drive.Final.anyEvent_isolated
import Submission.Work.Drive.Mono.trace_localModel_of_not_event

/-!
# The annulus of an event carries no corner point of the box

`Work.Drive.Final.dent_annulus_margin` (whose conclusion `Work.Drive.Final.dent_annulus_regular`
turns into the regularity of the *deformed* wall, hence into L4b) needs, as its `hslack` hypothesis,
that no point of the carrier in the annulus `r/2 ≤ ‖· - centre‖ ≤ r` lies simultaneously on the box
sphere and on a slab face.  This module supplies it: the corner points of the carrier (points of the
carrier on the box sphere **and** on a slab face) are among the images of the events of any type, so
`Work.Drive.Final.anyEvent_isolated` makes the ones different from the centre sit at positive distance
from it. -/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

noncomputable section

/-- **The annulus of an event carries no corner point.**  There is `δ > 0` such that no point
`par ψ q'` of the carrier at distance `0 < ‖par ψ q' - par ψ pp‖ ≤ δ` from the centre of the event
`pp` lies both on the box sphere (`boxNorm c σ · = s`) and on a slab face
(`|slabFn c u v ·| = h`).

Indeed such a point is an image of an event of the third type (`IsCornerEvent`), and every event
whose image lies within the isolation radius of `par ψ pp` has image `par ψ pp` itself. -/
theorem exists_annulus_cornerFree {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ} (hs : 0 < s)
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {pp : ℝ × ℝ} (hp : IsAnyEvent ψ s c σ u v h ℓ pp) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q' : ℝ × ℝ,
      0 < ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ →
      ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ ≤ δ →
      ¬ (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s ∧
        |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h) := by
  obtain ⟨r₁, hr₁, hiso⟩ := anyEvent_isolated (ψ := ψ) (K := K) (s := s) (u := u) (c := c)
    (σ := σ) (v := v) (h := h) (R := R) (ℓ := ℓ) (exc := exc) (lam0 := lam0) (lam1 := lam1)
    (p := p) (q := q) hDP hp
  refine ⟨r₁, hr₁, fun q' hd hdr hcorner => ?_⟩
  have hev : IsAnyEvent ψ s c σ u v h ℓ q' :=
    Or.inr (Or.inr ⟨Work.Drive.Mono.mem_closure_PBox_of_boxNorm_eq hs hcorner.1, hcorner.1,
      hcorner.2⟩)
  have heq := hiso q' hev (le_trans hdr le_rfl)
  rw [heq, sub_self, norm_zero] at hd
  exact lt_irrefl 0 hd

end

end Work.Drive.Final
