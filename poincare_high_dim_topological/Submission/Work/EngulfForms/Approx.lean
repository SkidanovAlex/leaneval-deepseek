import Submission.Work.EngulfForms.Prelude

/-!
# A5: the frozen PL-approximation forms

Two forms of A5 (`Submission/Work/PL/Approx`) are consumed by area A9:

* `Work.Engulf.PlApproxFrozenAtForm S n` — frozen PL approximation **at a prescribed level** `r`
  of the subdivision `S`, the frozen set `L` being a union of faces of the *fine* complex
  `S.sdIter r K hK` (the `plApproxAt` field of `Tools`, added by the E4 repair,
  `Submission/Work/NOTES_LEAD_poincare_E4fix.md` §1.2);
* `Work.Engulf.PlApproxFrozenForm S n` — the same, with the level `r` *produced* by the mesh
  argument, and with the frozen set `L` a union of faces of the *coarse* complex `K`
  (the `plApprox` field of `Tools`); see `Submission/Work/EngulfForms/Approx/PlApproxFrozenForm.lean`.

`plApproxFrozenAtForm` below is the direct transcription of A5's
`Work.PL.Approx.Frozen.pl_approx_frozen_faces`: take `T` to be the faces of the fine complex
inside `L`; the hypothesis `IsSubSp (S.sdIter r K hK) L` supplies both that these cover `L` and
that the linearity hypothesis of the form is exactly the one on `T`.
-/

open Set Metric PL
open Work.Engulf

namespace Work.EngulfForms

/-- **A5, at a prescribed level**: `Work.Engulf.PlApproxFrozenAtForm`, from
`Work.PL.Approx.Frozen.pl_approx_frozen_faces`. -/
theorem plApproxFrozenAtForm {N n : ℕ} (S : SubdivTools N) : PlApproxFrozenAtForm S n := by
  classical
  intro K hK r L hL f hf α β hα hαβ hβ ε hε hlin hosc
  have hfin : (S.sdIter r K hK).faces.Finite := S.fin r K hK
  set T : Finset (Finset (E N)) := hfin.toFinset.filter (fun s => PL.simp s ⊆ L) with hT
  obtain ⟨g, hg1, hg2, hg3, hg4, hg5⟩ :=
    Work.PL.Approx.Frozen.pl_approx_frozen_faces K (S.sdIter r K hK) hfin f hf (S.subdiv r K hK)
      α β hα hαβ hβ ε hε T
      (fun t ht => (hfin.mem_toFinset.1 (Finset.mem_filter.1 ht).1))
      (fun t ht hz => by
        obtain ⟨A, hA⟩ := hlin t (hfin.mem_toFinset.1 (Finset.mem_filter.1 ht).1)
          (Finset.mem_filter.1 ht).2 hz
        exact ⟨A, fun z hz => hA hz⟩)
      hosc
  refine ⟨g, hg1, hg2, ?_, hg3, fun s hs hx => ?_⟩
  · intro x hx
    obtain ⟨t, ht, hxt, htL⟩ := hL.2 x hx
    exact hg4 t (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ht, htL⟩) x hxt
  · obtain ⟨A, hA⟩ := hg5 s hs hx
    exact ⟨A, fun y hy => hA y hy⟩

end Work.EngulfForms
