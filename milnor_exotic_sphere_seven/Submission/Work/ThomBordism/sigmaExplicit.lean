import Mathlib
import Submission.Work.ThomBordism.gaussDefs
import Submission.Work.ThomBordism.orthFrameOrientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the **explicit** sign cocycle of the normal frames, and the `σ`-telescoping

`Work.ThomBordism.Gauss.sigma` is defined as `Classical.choose (exists_signCocycle E ND)`, whose
*proof* exhibits the explicit witness `δ i.1 x * framePairSign E ND i x` (with `δ` the tangent frame
sign of `Work.ThomBordism.framePairSign_cocycle`, i.e. `FrameSigns.frameSign`, the sign of the chart
tangent frame against the **given** fundamental class `V.c`).  Because `Classical.choose` does not
reduce, nothing about the *value* of `Gauss.sigma` follows from its specification — only that it is
some solution of the orientation cocycle, i.e. it is determined only up to multiplication by an
arbitrary locally constant sign `ρ : V.pt → {±1}`.  Since `Gauss.gframe`, `Gauss.padGaussFunM` (the
Gauss map) and hence the coorientation of every level set in the source construction are built from
`sigma`, that ambiguity propagates to the *orientation* of the Gauss frame.

This file records the explicit sign function `sigmaEL`, the corresponding gauge and corrected frame,
and the small lemmas about them.  The telescoping identity that the orientation coordination of the
last mile needs is stated and proved separately as `Work.ThomBordism.sigmaTelescope`
(`Submission/Work/ThomBordism/sigmaTelescope.lean`):

  `pairSign (the c-oriented tangent frame) (gframeEL) = +1`,

i.e. **the corrected normal frame is exactly the frame whose closing-up orientation of the piece is the
piece's given class `c`**.  See `Submission/Work/ThomBordism/NOTE_SIGMA_TELESCOPE.md` for the proof,
the recommended (conservative) redefinition of `Gauss.sigma` and the consequences.

## Main definitions

* `Work.ThomBordism.sigmaEL` — the explicit sign cocycle `δ i.1 x * framePairSign E ND i x`;
* `Work.ThomBordism.gaugeEL`, `…gframeEL` — the corresponding gauge and corrected normal frame;
* `Work.ThomBordism.flipTan` — the tangent frame with its first vector scaled by a sign (so that
  `flipTan (δ i x) (tanFrame E i x)` is a frame of `T_x V` oriented by `V.c`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology BigOperators

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The tangent frame with its first vector scaled by `s`.**  For `s = ±1` this is a frame of
`T_x V`; for `s = δ i x` (the tangent frame sign of `FrameSigns.frameSign`, i.e. the sign of the chart
frame against `V.c`) it is a frame of `T_x V` **oriented by `V.c`**. -/
def flipTan (E : EmbeddingData V (8 + k)) (i : CoverIdx V k) (x : V.pt) (s : ℝ) :
    Fin 8 → Work.Tubular.Euc (8 + k) :=
  fun a => if (a : ℕ) = 0 then s • tanFrame E i x a else tanFrame E i x a

/-- **The explicit sign cocycle**: the witness used in the proof of `Gauss.exists_signCocycle`. -/
def sigmaEL (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) : ℝ := by
  classical
  exact if _ : x ∈ ND.D.baseSet i then
    (Classical.choose (framePairSign_cocycle E ND)) i.1 x * framePairSign E ND i x
  else 1

theorem sigmaEL_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    sigmaEL E ND i x = (Classical.choose (framePairSign_cocycle E ND)) i.1 x
      * framePairSign E ND i x := by
  rw [sigmaEL, dif_pos hx]

/-- **The explicit gauge matrix** `diag (σEL, 1, …, 1)`. -/
def gaugeEL (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) : Matrix (Fin k) (Fin k) ℝ :=
  Gauss.Hmat (sigmaEL E ND i x)

/-- **The explicit corrected normal frame** — the analogue of `Gauss.gframe` with `σ` replaced by
`σEL`. -/
def gframeEL (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) : Fin k → Work.Tubular.Euc (8 + k) :=
  Gauss.frameAct (gaugeEL E ND i x) (Work.Tubular.orthFrame E ND i x)

theorem gframeEL_rel (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) :
    ∀ b, gframeEL E ND i x b
      = ∑ b', gaugeEL E ND i x b' b • Work.Tubular.orthFrame E ND i x b' := fun b => rfl

theorem gaugeEL_det (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (hk : 1 ≤ k)
    (i : CoverIdx V k) (x : V.pt) : (gaugeEL E ND i x).det = sigmaEL E ND i x :=
  Gauss.Hmat_det hk _

end

end Work.ThomBordism
