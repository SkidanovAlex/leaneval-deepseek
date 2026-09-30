import Mathlib
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Serre.CWModel.Maps
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.cellStepDefs
import Submission.Work.Serre.SPC.OneCellX
import Submission.Work.StemsB.Fibrations

set_option synthInstance.maxHeartbeats 400000


/-!
# The `b = 1` case: the invariant of the induction

`Work.Serre.SPC.GoodN b₀ p r γ₀ g` says that the comparison map
`Work.StemsB.relPairMap (pullbackFst g p) γ₀` of the pullback of `p : E → B` along `g : Γ → B`
is an isomorphism on integral homology in degrees `< r` and surjective in degree `r`.  It is the
invariant carried through the construction of the `1`-cell model of `B`
(`Work.Serre.SPC.b1Comparison`), and it is the *exact* shape of the two comparison conjuncts of
that statement with `r = 1 + f`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC

noncomputable section

/-- **The invariant of the `b = 1` induction.** -/
def GoodN {B : Type} [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (r : ℕ) {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B)) : Prop :=
  (∀ i : ℕ, i < r → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) r).hom


/-! ## The propagation lemma (to be proved elsewhere, `Work.Serre.SPC.goodN_attachCells`)

The comparison map is transported across a cell attachment `Γ' = attachCells (D-2) Γ ι fr`
(`D ≥ 2`) with `g' = attachG (D-2) Γ ι fr g G hG` by the five lemma applied to the morphism of the
short exact sequences of the *triples* `F ⊆ X₀ ⊆ X₁` and `{γ₀} ⊆ Γ ⊆ Γ'`, where
`X₁ = Pullback g' p`, `X₀ = Pullback g p` (identified with `(pullbackFst g' p) ⁻¹' range attachIncl`
through the canonical homeomorphism of the pullbacks) and `γ₀' = attachIncl (D-2) Γ ι fr γ₀`:

* the third column `H_*(X₁, X₀) → H_*(Γ', Γ)` is `Work.Serre.cellStepAttachMap D Γ ι fr X₁ (pullbackFst g' p)`
  (up to that homeomorphism), and its isomorphy in degrees `≤ r` is the hypothesis `hstep`;
* the first column `H_*(X₀, F) → H_*(Γ, γ₀)` is `GoodN b₀ p r γ₀ g`;
* the second column is the conclusion;
* the two long exact sequences are `Work.Cohomology.relChains_triple_shortExact`.

NOTE on the five lemma.  In the triple short exact sequence `relChains(X₀,F) → relChains(X₁,F) →
relChains(X₁,X₀)` the map we want to conclude about is the **middle** (`τ₂`) one, whereas Mathlib's
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃` / `epi_homologyMap_τ₃` conclude about the
**third**.  The needed forms — "`τ₁` and `τ₃` isomorphisms in a range (with `τ₁` epi at the top)
imply `τ₂` is an isomorphism below the range and epi at its top" — have to be derived from those
(by duality, by a diagram chase on the long exact sequences, or by applying the `τ₃` versions in the
opposite direction to the same short exact sequences), and are the only genuine work of the proof
besides the pullback identification `X₀ ≅ (pullbackFst g' p) ⁻¹' range attachIncl`.
-/
end

end Work.Serre.SPC
