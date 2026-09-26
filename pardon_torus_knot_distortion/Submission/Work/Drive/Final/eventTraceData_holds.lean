import Mathlib
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Final.dentOutTraceTame
import Submission.Work.Drive.Final.dentOutTraceTame_of_trace
import Submission.Work.Drive.Final.exists_dentCaptureDepth
import Submission.Work.Drive.Final.sphereCover_pinch_margin
import Submission.Work.Drive.Final.dent_pullback_disjoint
import Submission.Work.Drive.Mono.eventValue_mem_window

/-!
# The residual `Work.Drive.Final.EventTraceData`, proved from the dent producer and L4b

Project lead, `Mono/NOTES_LEAD_LD_interface.md` item 4(b).  `EventTraceData ψ K s c σ u v h R ℓ`
asks, at every event `pp` and every neighbourhood `U` of its image, for a dent datum `D` over `U`
together with a cover `Ss` of the frontier of the level `ℓ D.centre` by embedded spheres whose
*pulled-back* traces on the surface are pairwise disjoint and tame.

The three inputs are

* `Work.Drive.Final.exists_dentCaptureDepth` — the datum `D`, with the depth bounded by the pinch
  margin `η`, and with all the clauses (`hslack`, isolation, windows, annulus regularity) that L4b
  consumes;
* the cover `Ss` from the last clause of `GoodSweepData3` (inside `hDP`), at the level
  `ℓ (par ψ pp) ∈ Icc lam0 lam1` (`Work.Drive.Mono.eventValue_mem_window`);
* `Work.Drive.Final.dentOutTraceTame` (L4b) together with the proved
  `Work.Drive.Final.dentOutTraceTame_of_trace`, which turns the whole-trace tameness into
  `Work.Drive.Final.DentOutTraceTame D Ss`, and
  `Work.Drive.Final.sphereCover_pinch_margin` + `Work.Drive.Final.dent_pullback_disjoint` for the
  pulled-back disjointness.

No other hypothesis is needed: in particular `hslice`, `himg`, `hcl`, `hS`, `d`, `hsmall` are all
irrelevant here (the box-sphere slicing is a clause of `DataPackage`, inside `hDP`).
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

noncomputable section

/-- **The `(L)`-residual at every event, proved.** -/
theorem eventTraceData_holds {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ} (hs : 0 < s)
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q) :
    EventTraceData ψ K s c σ u v h R ℓ := by
  intro pp hp U hU
  -- the cover of the level's frontier, from the bundle
  obtain ⟨-, -, -, -, -, -, -, -, -, hcov⟩ := hDP.2.1
  have hlevmem : ℓ (Work.BoxShrink.Pinch.par ψ pp) ∈ Set.Icc lam0 lam1 :=
    Work.Drive.Mono.eventValue_mem_window hDP hp
  obtain ⟨n, Ss, hsph, hdisj, hfront⟩ := hcov _ hlevmem
  -- the pinch margin of the cover
  obtain ⟨η, hηpos, hη⟩ := sphereCover_pinch_margin (ψ := ψ) hsph hdisj
  -- the dent datum, of depth below the pinch margin
  obtain ⟨D, hDp, hDr, hDa, hDaη, hDχ, hDχ1, hDiso, hDw0, hDw1, hDw2, hDw3, hDslack, hDann⟩ :=
    exists_dentCaptureDepth (ψ := ψ) (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v)
      (h := h) (R := R) (ℓ := ℓ) (exc := exc) (lam0 := lam0) (lam1 := lam1) (p := p) (q := q)
      hs hηpos hDP pp hp U hU
  have hcentre : D.centre = Work.BoxShrink.Pinch.par ψ pp := by rw [D.centre_eq, hDp]
  have hshr : |D.a'| * D.κ < D.r := by rw [abs_of_pos D.a'_pos]; exact hDa
  have hfront' : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) =
      ⋃ i, Ss i := by rw [hcentre]; exact hfront
  have hpd : ∀ i j : Fin n, i ≠ j →
      Disjoint ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
        ((D.deform ⁻¹' Ss j) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) :=
    dent_pullback_disjoint (ψ := ψ) (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v)
      (h := h) (R := R) (ℓ := ℓ) (U := U) D hη hDaη
  have hT := dentOutTraceTame (ψ := ψ) (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v)
    (h := h) (R := R) (ℓ := ℓ) (U := U) hDP D hDχ hDχ1 hDa hDiso hDw0 hDw1 hDw2 hDw3 hDslack hDann
  exact ⟨D, hDp, hDr, hshr, n, Ss, hsph, hfront', hpd,
    dentOutTraceTame_of_trace (ψ := ψ) (K := K) (s := s) (u := u) (c := c) (σ := σ) (v := v)
      (h := h) (R := R) (ℓ := ℓ) (U := U) D hsph hshr hfront' hpd hT⟩

end

end Work.Drive.Final
