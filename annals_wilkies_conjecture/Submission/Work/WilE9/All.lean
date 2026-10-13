/-
  WilE9 — one import for the whole delivered interface (and a co-import check: every module below
  must be importable together in a single environment).

  Delivered content (all `sorry`-free apart from the unavoidable import of the frozen hole file
  `Submission/Work/Wilkies/E/Spec.lean`), by layer:

  * vocabulary, the target set and the `Gen` algebra — `Submission.Work.WilE9.Defs`;
  * the geometric input of the assembly, as an exact `Prop` — `Submission.Work.WilE9.EffSmooth`;
  * the `eaD` calculus (E.V vocabulary) — `Submission.Work.WilE9.EaD.*`;
  * the `psi`-calculus and its algebraic factors — `Submission.Work.WilE9.Psi.*`;
  * Cramer/adjugate linear algebra — `Submission.Work.WilE9.Mat.*`;
  * iterated derivatives: `glDeriv`, the `C^k` characterisation, `mvPolyDeriv` —
    `Submission.Work.WilE9.Deriv.*`;
  * the BNZ §3 implicit-function package — `Submission.Work.WilE9.Ift.*` and
    `Submission.Work.WilE9.Deg.iftP_totalDegree_le`;
  * the definable-analysis layer over `Gen` — `Submission.Work.WilE9.Gen.*`.
-/
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.EffSmooth
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt
import Submission.Work.WilE9.EaD.eaD_totalDegree_le
import Submission.Work.WilE9.EaD.eaEval_contDiff
import Submission.Work.WilE9.Psi.psi_sq_add_psig_sq
import Submission.Work.WilE9.Psi.psi_psig_algebra
import Submission.Work.WilE9.Psi.hasDerivAt_psi
import Submission.Work.WilE9.Psi.hasDerivAt_psig
import Submission.Work.WilE9.Psi.psi_psiInv
import Submission.Work.WilE9.Psi.psiInv_psi
import Submission.Work.WilE9.Psi.contDiff_psi
import Submission.Work.WilE9.Psi.psig_pos
import Submission.Work.WilE9.Psi.deriv_psiInv
import Submission.Work.WilE9.Psi.fderiv_psiV
import Submission.Work.WilE9.Psi.fderiv_psiInv_comp
import Submission.Work.WilE9.Psi.psi_iteratedDeriv_poly
import Submission.Work.WilE9.Psi.psiInv_iteratedDeriv_poly
import Submission.Work.WilE9.Mat.adjugate_mulVec_of_mulVec_eq
import Submission.Work.WilE9.Mat.mulVec_eq_inv_smul_adjugate
import Submission.Work.WilE9.Deriv.glDeriv_ofFn
import Submission.Work.WilE9.Deriv.mvPolyDeriv
import Submission.Work.WilE9.Deriv.contDiffAt_iff_partials
import Submission.Work.WilE9.Ift.Basic
import Submission.Work.WilE9.Ift.fderiv_eaEval_append
import Submission.Work.WilE9.Ift.jc_eval_eq
import Submission.Work.WilE9.Ift.deriv_eaEval_solution
import Submission.Work.WilE9.Ift.ift_identity
import Submission.Work.WilE9.Ift.ift_exists
import Submission.Work.WilE9.Ift.oneShot_star
import Submission.Work.WilE9.Deg.iftP_totalDegree_le
import Submission.Work.WilE9.Gen.gen_SA
import Submission.Work.WilE9.Gen.gen_closure
import Submission.Work.WilE9.Gen.gen_interior
import Submission.Work.WilE9.Gen.gen_contSet
import Submission.Work.WilE9.Gen.gen_diffSet

set_option autoImplicit false
noncomputable section

namespace Work.WilE9

/-- The relative version of `SOMin.SharpDeriv` for the filtration `Gen`, i.e. the statement that
the assembly must produce (see `STATUS.md` §1 and `Work.WilE9.EffSmooth.E9Reduction`). -/
def SharpDerivGen : Prop :=
  ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
    ∀ (D : ℕ) (f : (Fin n → ℝ) → ℝ),
      WilkiesDesign.E.Gen F D (n + 1) (WilkiesDesign.graphOf f) →
      ∀ (k : ℕ) (v : Fin k → Fin n),
        WilkiesDesign.E.Gen a (MvPolynomial.eval ![D, k] b) (n + 1) (sdSet f k v)

/-- `SharpDerivGen` is `genSOMin.SharpDeriv` (definitionally: `genSOMin.Ω = Gen`).

The `change` is not cosmetic: unfolding the *definition* `WilkiesDesign.E.genSOMin` materialises
its `comps` field, which is the frozen hole `E8_comps` (a `sorry`).  Proving the equivalence by a
bare `Iff.rfl` would therefore put `sorryAx` into the proof term of this lemma and, through it,
into every theorem stated over `genSOMin.SharpDeriv`.  Unfolding with `change` first keeps the
definitional equality in the *type checker* instead of the proof term. -/
theorem sharpDerivGen_iff : WilkiesDesign.E.genSOMin.SharpDeriv ↔ SharpDerivGen := by
  change (∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin n → ℝ) → ℝ),
        WilkiesDesign.E.Gen F D (n + 1) (WilkiesDesign.graphOf f) →
        ∀ (k : ℕ) (v : Fin k → Fin n),
          WilkiesDesign.E.Gen a (MvPolynomial.eval ![D, k] b) (n + 1) (sdSet f k v)) ↔
    SharpDerivGen
  exact Iff.rfl

end Work.WilE9
