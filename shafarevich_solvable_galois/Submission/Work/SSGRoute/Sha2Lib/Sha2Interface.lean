import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open scoped NumberField

/-- **The local datum at a finite place, relative to a base level `K`.**

`P` is a finite place of `Ω` over `k` (i.e. `SSGRoute.IsFinPlace k P`) and `K ⊆ Ω` a level.  The
datum is a function `f` on the decomposition group `D_P = decomp k P ⊓ K.fixingSubgroup` of `P` over
`K`, satisfying

* `hadd` — it is additive on `D_P`;
* `hcont` — it vanishes on an open subgroup of `D_P` (local constancy for the discrete target);
* `hne` — it is non-trivial;
* `hinv` — it is invariant under conjugation by the *full* decomposition group `decomp k P` of `P`
  over `k` (the compatibility needed to transport the datum to the other places above the same prime
  of `k`);
* `hinertia` — it vanishes on the inertia group of `P`: the local extension it describes is
  unramified.

The canonical such datum is the (unramified) Frobenius character `D_P ⧸ I_P ≅ Ẑ ↠ ZMod p`; see
`Work.SSGRoute.Sha2Lib.exists_unramLocalDatum`. -/
structure UnramLocalDatum (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (P : ValuationSubring Ω) where
  /-- the local character -/
  f : (Ω ≃ₐ[k] Ω) → ZMod p
  /-- additivity on the decomposition group of `P` over `K` -/
  hadd : ∀ g ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup,
    ∀ h ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup, f (g * h) = f g + f h
  /-- local constancy: the character vanishes on an open subgroup -/
  hcont : ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
    ∀ x ∈ U, x ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup → f x = 0
  /-- non-triviality -/
  hne : ∃ δ ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup, f δ ≠ 0
  /-- invariance under conjugation by the decomposition group of `P` over `k` -/
  hinv : ∀ (σ : Ω ≃ₐ[k] Ω), σ ∈ SSGRoute.decomp k P →
    ∀ δ ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup, f (σ * δ * σ⁻¹) = f δ
  /-- the character vanishes on the inertia group of `P` (unramifiedness) -/
  hinertia : ∀ δ ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup,
    SSGRoute.IsInertia k P δ → f δ = 0

end Work.SSGRoute.Sha2Lib
