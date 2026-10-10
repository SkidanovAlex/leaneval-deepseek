import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pairing on a restricted product

Mathlib's `RestrictedProduct` (`Πʳ i, [X i, U i]` for a family of subgroups `U i ≤ X i` and the
cofinite filter) is where the local Tate pairings of the Poitou–Tate theory naturally live: the
local factors pair perfectly in both variables, and the *unramified* subgroups `U i`, `U' i` annihilate
each other, so the sum `Σ_i ⟨x_i, y_i⟩` of the local pairings is a **finite** sum for
`x ∈ Πʳ [X i, U i]`, `y ∈ Πʳ [Y i, U' i]`.

This file provides exactly that interface:

* `Work.SSGRoute.PT.exists_finset_unramified` — the finite set of places outside which both `x` and
  `y` take values in `U`, `U'`;
* `Work.SSGRoute.PT.restrictedPairing` — the pairing `Πʳ [X i, U i] → Πʳ [Y i, U' i] → 𝔽_p`, given by
  that finite sum, with the computation rule `restrictedPairing_eq_sum` for *any* admissible finite
  set of places (the extra terms vanish by the hypothesis `hβ0` that `U i` and `U' i` annihilate
  each other).

The bilinearity of `restrictedPairing` (needed to speak of its annihilators) and the duality
statement `(C^⊥)^⊥ = C` for a *closed* subgroup `C` of the restricted product are the content of the
sibling node `Work.SSGRoute.PT.restrictedProduct_relaxation`, which also contains the relaxation step
of `Submission/Work/SSGRoute/DESIGN_PT.md` §3.
-/

open scoped RestrictedProduct
open Filter

namespace Work.SSGRoute.PT

variable {p : ℕ} [Fact p.Prime] {ι : Type*} {X Y : ι → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module (ZMod p) (X i)]
  [∀ i, AddCommGroup (Y i)] [∀ i, Module (ZMod p) (Y i)]

/-- **A finite set of places outside which `x` and `y` are unramified.**  Both factors of the
restricted product satisfy their defining cofinite condition, so the union of the two exceptional
sets is finite. -/
theorem exists_finset_unramified (U : ∀ i, Submodule (ZMod p) (X i))
    (U' : ∀ i, Submodule (ZMod p) (Y i))
    (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, U' i]) :
    ∃ S : Finset ι, ∀ i ∉ S, (x i : X i) ∈ U i ∧ (y i : Y i) ∈ U' i := by
  classical
  have hxf : ({i | (x i : X i) ∉ U i}).Finite := Filter.eventually_cofinite.mp x.2
  have hyf : ({i | (y i : Y i) ∉ U' i}).Finite := Filter.eventually_cofinite.mp y.2
  refine ⟨hxf.toFinset ∪ hyf.toFinset, fun i hi => ⟨?_, ?_⟩⟩
  · by_contra h
    exact hi (Finset.mem_union_left _ ((hxf.mem_toFinset).mpr h))
  · by_contra h
    exact hi (Finset.mem_union_right _ ((hyf.mem_toFinset).mpr h))

noncomputable def restrictedPairing (U : ∀ i, Submodule (ZMod p) (X i))
    (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, U' i]) : ZMod p :=
  ∑ i ∈ Classical.choose (exists_finset_unramified U U' x y), β i (x i) (y i)

/-- **The computation rule for `restrictedPairing`**: the sum of the local pairings does not
depend on the finite set of places over which it is taken, as long as the two arguments are
unramified outside it (the extra terms vanish by the hypothesis `hβ0` that the "unramified"
subgroups annihilate each other). -/
theorem sum_eq_sum_of_unramified (U : ∀ i, Submodule (ZMod p) (X i))
    (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (hβ0 : ∀ i, ∀ x ∈ U i, ∀ y ∈ U' i, β i x y = 0)
    (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, U' i])
    {S S' : Finset ι}
    (hS : ∀ i ∉ S, (x i : X i) ∈ U i ∧ (y i : Y i) ∈ U' i)
    (hS' : ∀ i ∉ S', (x i : X i) ∈ U i ∧ (y i : Y i) ∈ U' i) :
    (∑ i ∈ S, β i (x i) (y i)) = ∑ i ∈ S', β i (x i) (y i) := by
  classical
  have h1 : (∑ i ∈ S, β i (x i) (y i)) = ∑ i ∈ S ∪ S', β i (x i) (y i) := by
    refine Finset.sum_subset Finset.subset_union_left fun i hi hnot => ?_
    exact hβ0 i (x i) (hS i hnot).1 (y i) (hS i hnot).2
  have h2 : (∑ i ∈ S', β i (x i) (y i)) = ∑ i ∈ S ∪ S', β i (x i) (y i) := by
    refine Finset.sum_subset Finset.subset_union_right fun i hi hnot => ?_
    exact hβ0 i (x i) (hS' i hnot).1 (y i) (hS' i hnot).2
  rw [h1, h2]

/-- **The computation rule for `restrictedPairing`**, in the form used by its consumers. -/
theorem restrictedPairing_eq_sum (U : ∀ i, Submodule (ZMod p) (X i))
    (U' : ∀ i, Submodule (ZMod p) (Y i))
    (β : ∀ i, X i →ₗ[ZMod p] Y i →ₗ[ZMod p] ZMod p)
    (hβ0 : ∀ i, ∀ x ∈ U i, ∀ y ∈ U' i, β i x y = 0)
    (x : Πʳ i, [X i, U i]) (y : Πʳ i, [Y i, U' i])
    (S : Finset ι) (hS : ∀ i ∉ S, (x i : X i) ∈ U i ∧ (y i : Y i) ∈ U' i) :
    restrictedPairing U U' β x y = ∑ i ∈ S, β i (x i) (y i) :=
  sum_eq_sum_of_unramified U U' β hβ0 x y
    (Classical.choose_spec (exists_finset_unramified U U' x y)) hS

end Work.SSGRoute.PT
