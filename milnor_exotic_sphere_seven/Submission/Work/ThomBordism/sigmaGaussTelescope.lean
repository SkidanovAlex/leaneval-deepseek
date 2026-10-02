import Mathlib
import Submission.Work.ThomBordism.sigmaTelescope_frameSign

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: `Gauss.sigma` is the **explicit frame-sign** cocycle, and the telescoping for the Gauss frame

`Work.ThomBordism.Gauss.sigma` was originally

  `Classical.choose (exists_signCocycle E ND)`,

and then `(Classical.choose (framePairSign_cocycle E ND)) • framePairSign`; both forms contain a
`Classical.choose`, whose *specification* (a sign cocycle with the determinant `frameChange`) is
invariant under `σ ↦ ρ · σ` for **any** locally constant `ρ : V.pt → {± 1}`.  Since
`Work.ThomBordism.Gauss.gframe`, `…padGaussFunM` (the Gauss map) and hence the *coorientation* of
every level set of the source construction are built from `σ`, the orientation of the Gauss frame was
not determined by any recorded fact (`Work.ThomBordism.sigmaUpToLocalSign`,
`Submission/Work/ThomBordism/NOTE_SIGMA_TELESCOPE.md` §1).

The definition has now been *pinned* to the **explicit** witness
`Work.ThomBordism.FrameSigns.frameSign V` — the sign of the chart tangent frame against the *given*
fundamental class `V.c` — so that

* `Work.ThomBordism.Gauss.sigma = Work.ThomBordism.sigmaFS` and
  `Work.ThomBordism.Gauss.gframe = Work.ThomBordism.gframeFS` **definitionally**, and
* the telescoping `Work.ThomBordism.sigmaTelescope_frameSign` (proved for the explicit cocycle)
  applies to the *actual* Gauss frame: `Work.ThomBordism.sigmaTelescope_gauss` below.

Mathematically this is the statement the last mile needs: **the σ-corrected normal frame `gframe` is
exactly the frame whose closing-up with the `V.c`-oriented tangent frame is the standard orientation
of the ambient space** — i.e. `gframe` represents the *canonical* (intrinsic) coorientation of the
normal bundle of `V`, the one determined by `or(V) = c` and the ambient orientation alone, and
therefore *independent of the gluing datum* `ND`.  See
`Submission/Work/ThomBordism/NOTE_SIGMA_TELESCOPE.md` and `NOTE_BRANCH_COFREEDOM.md`.

## Main results

* `Work.ThomBordism.Gauss.sigma_eq_mul_of_mem` (in `gaussDefs.lean`) — the defining formula;
* `Work.ThomBordism.Gauss.sigma_eq_sigmaFS`, `…gframe_eq_gframeFS` — the definitional identifications;
* `Work.ThomBordism.sigmaTelescope_gauss` — the telescoping for `Gauss.gframe`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The explicit sign cocycle *is* `Gauss.sigma`**, definitionally. -/
theorem Gauss.sigma_eq_sigmaFS (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Gauss.sigma E ND = sigmaFS E ND := rfl

/-- **The explicit corrected frame *is* `Gauss.gframe`**, definitionally. -/
theorem Gauss.gframe_eq_gframeFS (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Gauss.gframe E ND = gframeFS E ND := rfl

/-- **The telescoping for the actual Gauss frame.**  The normal frame `Gauss.gframe` used by the
Gauss map is exactly the frame whose closing-up with the `V.c`-oriented tangent frame
`flipTan E i x (FrameSigns.frameSign V i.1 x)` is the standard orientation of the ambient space:

  `pairSign (flipTan … (frameSign …)) (Gauss.gframe …) = 1`.

Equivalently: `Gauss.gframe` represents the *canonical coorientation* of the normal bundle of `V` —
the one determined by the orientation `V.c` of `V` and the standard orientation of the ambient space —
with no orientation choice left.  This is the *frame half* of the orientation coordination of the last
mile, now a statement about the objects the construction actually uses. -/
theorem sigmaTelescope_gauss (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (hk : 1 ≤ k)
    (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    pairSign (flipTan E i x (FrameSigns.frameSign V i.1 x)) (Gauss.gframe E ND i x) = 1 := by
  rw [Gauss.gframe_eq_gframeFS E ND]
  exact sigmaTelescope_frameSign E ND hk i x hx

end

end Work.ThomBordism
