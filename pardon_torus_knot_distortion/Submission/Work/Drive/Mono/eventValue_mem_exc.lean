import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.GoodSweepData

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion

/-- The face functional `slabFnPar` and the pull-back of `inner ℝ v ·` differ by the constant
`⟪v,c⟫ + u`, hence have the same derivative. -/
theorem fderiv_slabFnPar_eq_inner_aux {ψ : Submission.Diffeo} {c : R3} {u : ℝ} {v : R3}
    (p : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p =
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
  have h : Work.Drive.Final.slabFnPar ψ c u v
      = fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u) := by
    funext q
    rw [Work.Drive.Final.slabFnPar_apply, Work.Drive.Final.slabFn_apply]
  rw [h, fderiv_sub_const]

/-- **The value of an event of the tilted sweep of any of the three types lies in the exceptional
set `exc`.**  Per event type:

* `IsEvent` — clause (iii) of `Work.Drive.Final.TiltedGenericity` (a critical point of the sweep
  height inside the box and the closed slab is non-degenerate and its value lies in `exc`);
* `IsFaceEvent` — the contrapositive of clause (ii) of the same genericity: no level outside `exc`
  has a tangency of the sweep height with the slab functional (the two face functionals differ by a
  constant, `fderiv_slabFnPar_eq_inner_aux`);
* `IsCornerEvent` — clause (d) of `Work.Drive.Mono.JunctionGenC`, a field of `DataPackage` (hence of
  `GoodDataPackage3`): a point of the surface on the box sphere inside the closed slab has its
  `ℓ`-value in `exc`. -/
theorem eventValue_mem_exc
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {pp : ℝ × ℝ} (hev : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp) :
    ℓ (Work.BoxShrink.Pinch.par ψ pp) ∈ (exc : Set ℝ) := by
  obtain ⟨hD, -, -⟩ := hDP
  obtain ⟨hTilt, hJunc, -, -, -, -, -⟩ := hD
  have hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc := hTilt.1
  obtain ⟨hg1, hg2, hg3, -⟩ := hgen
  rcases hev with h1 | h2 | h3
  · -- an interior event: clause (iii) of the genericity
    exact (hg3 pp h1.1 h1.2.1 h1.2.2).2
  · -- a face event: the contrapositive of clause (ii) of the genericity
    by_contra hne
    obtain ⟨t, ht⟩ := h2.2.2
    rw [fderiv_slabFnPar_eq_inner_aux] at ht
    exact hg2 (ℓ (Work.BoxShrink.Pinch.par ψ pp)) hne pp h2.1 (by simpa using h2.2.1) rfl t ht
  · -- a corner event: clause (d) of `JunctionGenC`
    obtain ⟨-, hbn, hslab⟩ := h3
    exact hJunc.2.2.2 (Work.BoxShrink.Pinch.par ψ pp) ⟨pp, rfl⟩ hbn (by simpa using hslab)

end Work.Drive.Mono
