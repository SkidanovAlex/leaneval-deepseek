import Mathlib
import Submission.Work.Gen.EulerDefs
import Submission.Work.Gen.TautTensorTriv
import Submission.Work.Gen.chernClass_one_whitneySum_eq_tensorLine
import Submission.Work.Gen.chernClass_one_of_conjGauge_neg
import Submission.Work.Projective.Atlas

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Unconditional `c\u2081`-facts for `\u2102 \u2297 O(1) = O(1) \u2295 O(-1)`: a `sorry`-free home

These are the facts a *consumer* of the `GEN` area needs without importing
`Submission/Work/Gen/EulerChernTwo.lean` (which carries the single `sorry` that isolates the
Whitney sum formula, and would therefore contaminate an importer's `#print axioms`):

* `Work.Gen.DetTrickTwo` / `Work.Gen.detTrickTwo` — the **determinant trick at rank `2`**,
  `c\u2081(L \u2295 M) = c\u2081(L \u2297 M)` for complex line bundles over an arbitrary base, delivered by the fleet
  in `Submission/Work/Gen/chernClass_one_whitneySum_eq_tensorLine.lean` (route: the wedge
  isomorphism `Q_{L\u2295M} \u2245 \u03c0^*(L \u2297 M)` of `Submission/Work/Gen/tautQuotient_line_tensor.lean`, the descent
  `Work.Thom.chernClass_succ_of_le`, and injectivity of `\u03c0^*` in degree `2`);
* `Work.Gen.chernClass_lineC_one_uncond` — **`c\u2081(\u2102 \u2297 O(1)) = 0` for every `n`**, unconditionally
  (`O(1) \u2297 O(-1) \u2245 \u2102` via `Work.Gen.TautTensorTriv`); this is the `c\u2081` input of the Euler-sequence
  computation of `c(\u2102 \u2297 T\u2102P\u207f)`, for `n = 2` (`EulerChernTwo`) and for `n = 4`;
* `Work.Gen.paracompactSpace_CP` — `\u2102P\u207f` is paracompact (one line from
  `Work.Projective.compactSpace_CP` and Mathlib's `paracompact_of_compact`), which is the extra
  instance a *paracompact-base* delivery of the splitting principle would require.

Everything here is `sorry`-free and depends only on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.Gen

open Work.Projective

/-! ## Pointer: the general conjugation sign (delivered, not used here)

The fleet delivered `Work.Gen.chernClass_one_of_conjGauge_neg`
(`Submission/Work/Gen/chernClass_one_of_conjGauge_neg.lean`, `sorry`-free): if `L'` has the
complex-conjugated transition scalars of `L` (same cover), then `c\u2081(L') = - c\u2081(L)`.  Together with
`Work.Gen.detTrickTwo` this is what a *general* determinant calculus (`c\u2081(W) = c\u2081(\u039b^{top}W)`, hence
`c\u2081` of a self-conjugate bundle or of a complexification vanishes) is built from, and it is the
input behind `p\u2081(L_\u211d) = c\u2081(L) \u2323 c\u2081(L)` in `Submission/Work/Whitney/README.md` \u00a76(d). -/

/-- **The determinant trick at rank `2`**: for complex line bundles `L, M`,
`c\u2081(L \u2295 M) = c\u2081(L \u2297 M)`. -/
def DetTrickTwo : Prop :=
  ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂),
    Work.Thom.chernClass (1 + 1) 1 (Work.Whitney.whitneySum L M)
      = Work.Thom.chernClass 1 1 (Work.Gen.tensorLine L M)

/-- **The determinant trick, delivered**: `c\u2081(L \u2295 M) = c\u2081(L \u2297 M)` for complex line bundles,
proved by the fleet in `Submission/Work/Gen/chernClass_one_whitneySum_eq_tensorLine.lean`. -/
theorem detTrickTwo : DetTrickTwo :=
  Work.Gen.chernClass_one_whitneySum_eq_tensorLine

/-- **`c\u2081(\u2102 \u2297 O(1)) = c\u2081(O(1) \u2295 O(-1)) = 0`, unconditionally** (`n` arbitrary): the determinant
trick reduces it to `c\u2081(O(1) \u2297 O(-1)) = 0`, which is `Work.Gen.TautTensorTriv`. -/
theorem chernClass_lineC_one_uncond (n : ℕ) :
    Work.Thom.chernClass 2 1 (lineC n) = 0 :=
  (detTrickTwo (tautDual n) (tautLine n)).trans (Work.Gen.TautTensorTriv n)

/-- The same statement from the determinant trick as an explicit hypothesis (the form in which it
was isolated before the delivery). -/
theorem chernClass_lineC_one_of_detTrick (h : DetTrickTwo) (n : ℕ) :
    Work.Thom.chernClass 2 1 (lineC n) = 0 :=
  (h (tautDual n) (tautLine n)).trans (Work.Gen.TautTensorTriv n)

/-- **`\u2102P\u207f` is paracompact**: `\u2102P\u207f` is compact (`Work.Projective.compactSpace_CP`) and Mathlib's
instance `paracompact_of_compact` produces paracompactness from compactness. -/
theorem paracompactSpace_CP (n : ℕ) : ParacompactSpace (CP n) := by
  haveI := Work.Projective.compactSpace_CP n
  infer_instance

/-! ## Shared helpers

Both deliveries imported above, together with `Submission/Work/Gen/LineTensor.lean`, now share a
single copy of the helper `Work.Gen.scl_smul_id_eq` (it lives in `LineTensor.lean`, next to `scl`,
`scl_id` and `scl_smul`, and the two deliveries no longer define their own).  The former collision
("environment already contains `Work.Gen.scl_smul_id_eq`") is therefore gone, and this module
exports the determinant trick, the unconditional `c\u2081(\u2102 \u2297 O(1)) = 0`, `ParacompactSpace (\u2102P\u207f)` and
the conjugation sign together.
-/

end Work.Gen
