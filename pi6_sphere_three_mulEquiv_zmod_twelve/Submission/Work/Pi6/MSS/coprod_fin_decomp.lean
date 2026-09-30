import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Elements of a coproduct of `R`-modules are finite sums of coproduct inclusions

For a family `M : ι → ModuleCat R` of `R`-modules, every element of the coproduct `∐ i, M i`
is a finite sum `∑ j : Fin k, Sigma.ι M (σ j) (v j)` of images of the coproduct inclusions along
a finite family of indices `σ : Fin k → ι`.

The proof transports the statement along `ModuleCat.coprodIsoDirectSum` to the direct sum
`⨁ i, M i` (which is `DFinsupp`), where `DirectSum.sum_support_of` exhibits every element as the
finite sum of its components over its (finite) support; the support is reindexed by `Fin (card)`.
-/

open CategoryTheory Limits DirectSum

namespace Work.Pi6.MSS

theorem coprod_fin_decomp {R : Type} [Ring R] {ι : Type} (M : ι → ModuleCat R)
    (y : (∐ (fun i => M i) : ModuleCat R)) :
    ∃ (k : ℕ) (σ : Fin k → ι) (v : ∀ j : Fin k, M (σ j)),
      y = ∑ j : Fin k, (CategoryTheory.Limits.Sigma.ι M (σ j)) (v j) := by
  classical
  let φ := ModuleCat.coprodIsoDirectSum M
  set x : (⨁ i, M i) := φ.hom y with hx
  -- `x` is the image of `y` in the direct sum
  have h1 : (ConcreteCategory.hom φ.inv) x = y := by
    rw [hx]
    exact Iso.hom_inv_id_apply φ y
  -- every element of the direct sum is the sum of its components over its support
  have hxs : x = ∑ i ∈ x.support, DirectSum.of (fun i => (M i : Type)) i (x i) :=
    (DirectSum.sum_support_of (β := fun i => (M i : Type)) x).symm
  -- push this through the inverse iso, using that the inclusions of the coproduct are the `lof`s
  have step1 : (ConcreteCategory.hom φ.inv) x
      = ∑ i ∈ x.support, (ConcreteCategory.hom (Sigma.ι M i)) (x i) := by
    conv_lhs => rw [hxs]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => ModuleCat.lof_coprodIsoDirectSum_inv_apply M i (x i)
  -- reindex the finite support by `Fin (card)`
  set σ : Fin x.support.card → ι := fun j => ((Finset.equivFin x.support).symm j : x.support) with hσ
  refine ⟨x.support.card, σ, fun j => x (σ j), ?_⟩
  rw [← h1, step1]
  have hA : (∑ i ∈ x.support, (ConcreteCategory.hom (Sigma.ι M i)) (x i))
      = ∑ i : ↥(x.support), (ConcreteCategory.hom (Sigma.ι M ↑i)) (x ↑i) := by
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
  rw [hA, ← Equiv.sum_comp (Finset.equivFin x.support).symm
        (fun i : ↥(x.support) => (ConcreteCategory.hom (Sigma.ι M ↑i)) (x ↑i))]

end Work.Pi6.MSS
