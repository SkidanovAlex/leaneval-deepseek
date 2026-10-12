import ChallengeDeps
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseGateFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.Hon` — the honest vocabulary, locally

The honest family of `Work.BoseGateFS.KinkInputHonest` is built from the
**vocabulary module** `Submission.Work.BoseBoxFock.Defs` only
(`HonestBoxFam v h fc fu HM μ : HonestBox v μ`); the four abbreviations
`honF`, `honT`, `honE`, `honKmom` are just the projections
`.F`, `.T`, `.E` of that structure together with `kmomLab`.

This module repeats those four abbreviations **inside this area's namespace**, so
that statements of this area can be phrased in exactly the node's vocabulary
while importing only modules that are *upstream* of
`Submission.Work.BoseGateFS.GateHonest`.  The point is purely practical: the
upstream file `Submission/Work/BoseGateFS/GateHonest.lean` is stale-broken
(see `README.md` §2bis; two words of `CloseCond` should be `CloseCondFS`), and
anything that imports it cannot be built by `lake build` until the lead repairs
it.  Statements written with the abbreviations below elaborate to **the same
terms** as the node's, so nothing is lost: `Work.BoseRowsFS.honE` and
`Work.BoseGateFS.honE` are definitionally equal (both unfold to
`(HonestBoxFam v h fc fu HM μ).E`).

Both the body and the name of each abbreviation are chosen to match
`Work.BoseGateFS.KinkInputHonest` character for character, so that a statement
transcribed from the node compiles here verbatim.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowsFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

/-- The honest family's Fock data (same body as `Work.BoseGateFS.honF`). -/
noncomputable abbrev honF (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) : FockData (Lab (HM μ).N) :=
  (HonestBoxFam v h fc fu HM μ).F

/-- The honest family's θ-mode data (same body as `Work.BoseGateFS.honT`). -/
noncomputable abbrev honT (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) : TildeData (honF v h fc fu HM μ) :=
  (HonestBoxFam v h fc fu HM μ).T

/-- The honest family's environment (same body as `Work.BoseGateFS.honE`). -/
noncomputable abbrev honE (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) : Q3Env (Lab (HM μ).N) :=
  (HonestBoxFam v h fc fu HM μ).E

/-- The honest cube's momentum map (same body as `Work.BoseGateFS.honKmom`). -/
noncomputable abbrev honKmom (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) : Lab (HM μ).N → EuclideanSpace ℝ (Fin 3) :=
  kmomLab (ellH v μ) (HM μ).N

/-- The `kmom` of the honest Fock data is the honest momentum map. -/
lemma honF_kmom (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (honF v h fc fu HM μ).kmom = honKmom v HM μ := rfl

/-! ## The honest data, unfolded (clean copies of the node's lemmas)

Each of the following is the *same statement* as the node's lemma of the same
name in `Work.BoseGateFS.KinkFSHonest` / `HonestInhab` / `GateThresholdsExist`;
where the node's version takes a `HonSetup` package (which lives downstream of
the breakage) the positivity data are taken directly. -/

/-- The honest environment's `aScat` is `a v`. -/
lemma honE_aScat (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (honE v h fc fu HM μ).aScat = _root_.BoseGases.a v := rfl

/-- The honest environment's `ℓ` is `ellH v μ`. -/
lemma honE_ell (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    (honE v h fc fu HM μ).ell = ellH v μ := by
  rw [ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
  rfl

/-- The honest `Ŵ₁` (with its UV cut) at a mode. -/
lemma honE_W1_apply (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (k : Lab (HM μ).N) :
    (honE v h fc fu HM μ).W1 k
      = uvCut fu (uvRad (ellH v μ) (HM μ).N) ((honF v h fc fu HM μ).kmom k)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ))
            ((honF v h fc fu HM μ).kmom k) := by
  rw [ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
  rfl

/-- The honest environment's gap coefficient is FS's `b = 1/16`. -/
lemma honE_b (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (honE v h fc fu HM μ).b = 1 / 16 := by
  have h1 : (honE v h fc fu HM μ).b = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b := by
    simp only [honE, Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon,
      Work.BoseFixR.KzEnvFs]
  rw [h1, Work.BoseFixB1.paramsAt_b_eq, Work.BoseBox.bValue]

/-- The honest `ε_T`: `ε_T = (μa³)^{23/1292}`. -/
lemma honE_eT_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (honE v h fc fu HM μ).eT = (μ * (_root_.BoseGases.a v) ^ 3) ^ (23 / 1292 : ℝ) := by
  rw [show (honE v h fc fu HM μ).eT
      = (Work.BoseFixR.KzEnvFs v h μ (honF v h fc fu HM μ) fc).eT from rfl]
  rw [Work.BoseFixR.KzEnvFs_eT_val, Work.BoseBox.fsXp]
  norm_num

/-- The τ̃-pin at the honest family. -/
lemma honE_tau (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ∀ k : Lab (HM μ).N,
      (honE v h fc fu HM μ).tau k
        = Work.BoseBoxFock.tauSm (honE v h fc fu HM μ).eT (honE v h fc fu HM μ).s
            (honE v h fc fu HM μ).d (honE v h fc fu HM μ).ell
            ((honF v h fc fu HM μ).kmom k) := by
  intro k
  simp only [honE, honF, Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon,
    Work.BoseFixR.KzEnvFs]

end Work.BoseRowsFS
