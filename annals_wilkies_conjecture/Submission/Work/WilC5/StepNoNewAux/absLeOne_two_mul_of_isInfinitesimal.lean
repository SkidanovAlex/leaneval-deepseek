import Mathlib
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC5.S4ExpF.Bridge

namespace Work.WilC5.StepNoNewAux

/-!
## Why the theorem below is **false as stated** (and what the correct statement is)

`Work.WilC5.absLeOne`, `mulE`, `addE`, `oneE` are the *symbols of the `LEc`-structure* on `M`,
whereas `Work.WilC5.IsInfinitesimal` (in the hypothesis) is stated with the **typeclass**
`Field`/`LinearOrder`/`IsStrictOrderedRing` data of `M`.  Nothing in the hypotheses relates the
`LEc`-structure to that field data: `Ring.CompatibleRing M` relates the field operations only to
*its own* `Language.ring.Structure M`, which need not be the ring part of the `LEc`-structure
(the latter is `lrcRingReduct (reductStruct M)`, a different instance).  The two can therefore be
conjugated independently, and the statement fails.

**Machine-checked counterexample** (module `Submission._CntrAbsLeOne`, all proofs sorry-free):
take `M = ℝ`, let `Tstr` be the `LEc`-structure obtained by conjugating the canonical one by the
translation `σ x = x + 5`, i.e. `funMap_T f x̄ = σ (funMap_canonical f (σ⁻¹ ∘ x̄))`; take the
standard `Field`/`LinearOrder`/`IsStrictOrderedRing`/`Ring.CompatibleRing` instances and
`ε = 0`.  Then
* `Tstr_model : @Theory.Model LRc ℝ (reductStruct ℝ Tstr) TR` (the `rexp`-reduct is
  `LRc`-isomorphic to the standard `ℝ_rexp` via `σ`, so `hM` holds);
* `zero_isInfinitesimal : IsInfinitesimal (0 : ℝ)`;
* `not_concl : ¬ absLeOne (mulE (addE oneE oneE) 0)`, since `oneE_T = 6`,
  `addE_T oneE_T oneE_T = σ 2 = 7`, `mulE_T (…) 0 = σ (2 · σ⁻¹ 0) = σ (-10) = -5`, and
  `isSquare_T (addE_T oneE_T (-5))` is `0 ≤ σ⁻¹ (σ (-9)) = -9`, i.e. false.
Hence `target_statement_false : ¬ (∀ M [_] _ _ _ _ (hM : M ⊨ TR) (ε), IsInfinitesimal ε → …)`,
and applying the target declaration to this instance gives `contradiction_with_target : False`.

**Correct statement.**  One must add the coherence of the `LEc`-structure with the field/order
data, exactly as in `Submission/Work/WilC5/S4ExpF/Bridge.lean` and `StepExp.lean` (whose `hδ1`
is the result below): assume `hTE : M ⊨ TE` together with `hadd : addE x y = x + y`,
`hmul : mulE x y = x * y`, `hone : oneE = 1`, `hleneg : leE x y ↔ x ≤ y` — or, equivalently,
state the lemma with the canonical instances derived from `hM` (`Work.WilC5.trField M hM`,
`Work.WilC5.trLinearOrder M hM`, `FirstOrder.Field.compatibleRingOfModelField M`).  In the
canonical setting all four coherence hypotheses are provable (cf. `Work.WilC5.StepNoNew`'s
`haddK`).  The version with those hypotheses is `absLeOne_two_mul_of_isInfinitesimal_aux` below.
-/

/-- **The intended statement, with the missing coherence hypotheses made explicit** (see the
module docstring for why they cannot be dropped, and `StepExp.lean`/`S4ExpF.Bridge.lean` for the
same computation). -/
theorem absLeOne_two_mul_of_isInfinitesimal_aux {M : Type} [WilkiesDesign.CG.LEc.Structure M]
    [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE)
    (hadd : ∀ x y : M, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : M, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : M) = 1)
    (hleneg : ∀ x y : M, Work.WilC5.leE x y ↔ x ≤ y)
    {ε : M} (hε : Work.WilC5.IsInfinitesimal ε) :
    Work.WilC5.absLeOne
      (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ε) := by
  have h2 : Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ε = 2 * ε := by
    rw [hadd, hone, hmul]
    norm_num
  have hhalf : |ε| ≤ (2 : M)⁻¹ := by
    have h := hε 1
    have h2M : (((1 : ℕ) : M) + 1) = 2 := by norm_num
    rwa [h2M] at h
  rw [h2, Work.WilC5.S4ExpF.absLeOne_iff_abs hM hadd hone hleneg (2 * ε), abs_mul]
  have h2abs : |(2 : M)| = 2 := abs_of_pos (by norm_num)
  rw [h2abs]
  calc (2 : M) * |ε| ≤ (2 : M) * (2 : M)⁻¹ :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = 1 := by
        have h2pos : (0 : M) < 2 := by norm_num
        rw [mul_inv_cancel₀ (ne_of_gt h2pos)]

/- NOTE: the statement that stood here is *false as stated* (a machine-checked
   counterexample is recorded in the module header of this file / in
   `Submission._CntrAbsLeOne`), so it has been withdrawn rather than left as a `sorry`.
   Nothing in the directory uses it: the importing modules (`StepSeqLogPres*`) reference
   only their own imports from this cluster. -/

end Work.WilC5.StepNoNewAux
