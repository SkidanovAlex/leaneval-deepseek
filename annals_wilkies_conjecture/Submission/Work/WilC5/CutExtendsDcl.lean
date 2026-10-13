/-
  WilC5 — **the cut of an element determines the extension of an embedding to its definable
  closure** (the model-theoretic step of vdDMM Lemmas 4.2–4.4).

  Let `K, L ⊨ TR`, let `F ≤ K` be an `LRc`-substructure which is `Dcl`-closed (hence a model of
  `TR`), let `σ : F → L` be an `LRc`-embedding, and let `x ∈ K`, `y ∈ L` define the same *cut*
  through `σ`: `(f : K) < x ↔ σ f < y` and `x < (f : K) ↔ y < σ f` for every `f ∈ F`.

  o-minimality of the models of `TR` (`hOM`) says that the type of `x` over the model `F` is
  determined by this cut; in the form proved in the workspace it is
  `Work.WilC5.cut_determines_type_F` (`dmm42_cut_extend.lean`), which gives, for every `LRc`-formula
  `φ(v, w̄)` with parameters `w̄ ∈ F`,

      `K ⊨ φ(x, w̄)  ↔  L ⊨ φ(y, σ w̄)`.

  `Work.WilC5.dmm42_cut_extend` uses this to extend `σ` to the *substructure generated* by
  `F ∪ {x}` (terms in `x` over `F`).  The present lemma extends it all the way to the *definable
  closure* `Dcl (F ∪ {x})`, which is what the §4 domains are (`S4Dom` is `Dcl`-closed): the
  elements of `Dcl (F ∪ {x})` are the unique solutions of formulas `φ(v, x, w̄)` (`w̄ ∈ F`), and
  the type comparison above shows both that the corresponding set
  `{v ∈ L | φ(v, y, σ w̄)}` is a singleton and that the assignment is well defined, injective and
  preserves the `LRc`-structure.

  This is the "`σ₀` extends to an `L_an`-embedding `σ : F → L` with `σ(x) = y`" step of vdDMM
  Lemmas 4.2 and 4.3, and the induction step of their Claim 4; what it does *not* contain is the
  log-closure of the new domain and the log-preservation of the extension, which are the
  value-theoretic content of Lemmas 4.2–4.4 (`S4StepNoNew.lean`, `S4StepExp.lean`,
  `S4StepNew.lean`).
-/
import Mathlib
import Submission.Work.WilC5.dmm42_cut_extend
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC5.dcl_iUnion_chain
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.DclExtension
import Submission.Work.WilC2.Dcl

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC5

/-- **The cut determines the extension to the definable closure.**

In the canonical setting of area C2 — `K, L` are ordered fields in the `rexp` language, with the
ring/order/`rexp`/constants instances fixed and both models of `TR` — let `F ≤ K` be an
`LRc`-substructure which is `Dcl`-closed (so `F ⊨ TR`), `σ : F → L` an `LRc`-embedding, and let
`x ∈ K`, `y ∈ L` have the same cut through `σ`.  Then `σ` extends to an `LRc`-embedding `σ'` of a
domain `S ≤ K` whose carrier is exactly the definable closure `Work.WilC2.Dcl (F ∪ {x})` (which is
again `Dcl`-closed), sending `x` to `y`. -/
theorem CutExtendsDcl {K L : Type}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (F : WilkiesDesign.CG.LRc.Substructure K) (hF : (F : Type) ⊨ WilkiesDesign.CG.TR)
    (hFdcl : Work.WilC2.Dcl (F : Set K) ⊆ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding F L) {x : K} {y : L}
    (hcut : (∀ f : F, ((f : K) < x ↔ (σ f : L) < y)) ∧
      (∀ f : F, (x < (f : K) ↔ y < (σ f : L)))) :
    ∃ (S : WilkiesDesign.CG.LRc.Substructure K)
      (hS : (S : Set K) = Work.WilC2.Dcl ((F : Set K) ∪ {x}))
      (hSdcl : Work.WilC2.Dcl (S : Set K) ⊆ (S : Set K))
      (hle : F ≤ S) (hxS : x ∈ (S : Set K)),
      ∃ σ' : WilkiesDesign.CG.LRc.Embedding S L,
        (∀ f : F, σ' ⟨(f : K), hle f.2⟩ = σ f) ∧ σ' ⟨x, hxS⟩ = y :=
  DclExtension hMCr hOM F hF hFdcl σ hcut

end Work.WilC5
