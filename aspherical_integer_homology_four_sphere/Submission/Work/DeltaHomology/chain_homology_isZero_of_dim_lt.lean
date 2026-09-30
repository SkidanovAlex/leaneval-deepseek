import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.Chain
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology Work.DeltaHomology

/-- The `Δ`-chain complex of a finite `Δ`-complex is concentrated in degrees `≤ K.dim`:
above the dimension the chain group `K.chainX k = ∐ (fun _ : Fin (K.card k) => ℤ)` is the
coproduct over the empty index type (`K.card_eq_zero k h : K.card k = 0`), hence the zero
object of `ModuleCat ℤ`.  Concretely we show `𝟙 = 0` on the coproduct, which by
`IsZero.iff_id_eq_zero` is exactly `IsZero`; the two morphisms are compared on each
coproduct inclusion `Sigma.ι`, of which there are none. -/
theorem chainX_isZero_of_dim_lt (K : DeltaCx) {k : ℕ} (h : K.dim < k) :
    IsZero (K.chainX k) := by
  change IsZero (∐ (fun _ : Fin (K.card k) => Work.Homology.ZMod))
  rw [DeltaCx.card_eq_zero' K h]
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro i
  exact i.elim0

/-- The homology of the `Δ`-chain complex of a finite `Δ`-complex vanishes above its
dimension: for `k > K.dim` the chain groups `K.chainX k` and `K.chainX (k+1)` are zero
(`DeltaCx.card_eq_zero`), so `H_k^Δ(K) = K.chain.homology k` is zero. -/
theorem chain_homology_isZero_of_dim_lt (K : DeltaCx) {k : ℕ} (h : K.dim < k) :
    IsZero (K.chain.homology k) := by
  exact ShortComplex.isZero_homology_of_isZero_X₂ (S := K.chain.sc k) (by
    rw [show (K.chain.sc k).X₂ = K.chainX k from rfl]
    exact chainX_isZero_of_dim_lt K h)

end Work.DeltaHomology
