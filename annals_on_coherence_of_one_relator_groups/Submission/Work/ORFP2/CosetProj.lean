/-
# The `k[H]`-component of `k[G]`, and the coset decomposition of `k[G]` over `k[H]`

For a subgroup `H ≤ G` of a group `G` and a commutative ring `k`, this file provides the
elementary vocabulary attached to the decomposition of `k[G]` into its `k[H]`-components
along the left cosets of `H`:

* `projH k H x` : the `H`-component of `x ∈ k[G]`, an element of `k[H]`;
* `comp k H q x` : the component of `x` on the left coset `q ∈ G ⧸ H`, an element of `k[H]`;
* `cosetSupport k H x` : the finite set of cosets meeting the support of `x`;
* `augMapA`, `augMapB` : the maps `k[H]^S → k[H]`, `e_s ↦ s - 1`, and its `k[G]`-analogue.

Here `G ⧸ H` denotes the set of *left* cosets `gH`, i.e. the quotient of `G` by
`QuotientGroup.leftRel H`.
-/
import Mathlib
import Submission.Work.ORFP2.Basic

set_option autoImplicit false

open MonoidAlgebra

namespace Work.ORFP2

variable (k : Type*) [CommRing k] {G : Type*} [Group G]

/-- The projection of `x : k[G]` onto its `H`-component: the element of `k[H]` whose
coefficient at `h : H` is the coefficient of `h` in `x`.  It is the identity on `k[H]`
(seen as a subalgebra of `k[G]`) and annihilates every element whose support misses `H`. -/
noncomputable def projH (H : Subgroup G) (x : MonoidAlgebra k G) : MonoidAlgebra k H :=
  MonoidAlgebra.ofCoeff (Finsupp.subtypeDomain (fun g => g ∈ H) x.coeff)

@[simp]
lemma projH_coeff (H : Subgroup G) (x : MonoidAlgebra k G) (g : G) (hg : g ∈ H) :
    (projH k H x).coeff ⟨g, hg⟩ = x.coeff g := by
  rw [projH, MonoidAlgebra.coeff_ofCoeff, Finsupp.subtypeDomain_apply]

@[simp]
lemma projH_zero (H : Subgroup G) : projH k H (0 : MonoidAlgebra k G) = 0 := by
  rw [projH, MonoidAlgebra.coeff_zero, Finsupp.subtypeDomain_zero, MonoidAlgebra.ofCoeff_zero]

lemma projH_add (H : Subgroup G) (x y : MonoidAlgebra k G) :
    projH k H (x + y) = projH k H x + projH k H y := by
  rw [projH, projH, projH, MonoidAlgebra.coeff_add, Finsupp.subtypeDomain_add,
    MonoidAlgebra.ofCoeff_add]

lemma projH_eq_zero_iff (H : Subgroup G) (x : MonoidAlgebra k G) :
    projH k H x = 0 ↔ ∀ g ∈ H, x.coeff g = 0 := by
  constructor
  · intro h g hg
    have := congrArg (fun y : MonoidAlgebra k H => y.coeff ⟨g, hg⟩) h
    simpa using this
  · intro h
    ext ⟨g, hg⟩
    rw [projH_coeff k H x g hg]
    simp [h g hg]

/-- The component of `x : k[G]` on the left coset `q : G ⧸ H`, as an element of `k[H]`. -/
noncomputable def comp (H : Subgroup G) (q : G ⧸ H) (x : MonoidAlgebra k G) : MonoidAlgebra k H :=
  projH k H (MonoidAlgebra.single (Quotient.out q)⁻¹ (1 : k) * x)

@[simp]
lemma comp_coeff (H : Subgroup G) (q : G ⧸ H) (x : MonoidAlgebra k G) (h : H) :
    (comp k H q x).coeff h = x.coeff (Quotient.out q * h) := by
  rw [comp]
  change (projH k H (MonoidAlgebra.single (Quotient.out q)⁻¹ (1 : k) * x)).coeff
      ⟨(h : G), h.2⟩ = x.coeff (Quotient.out q * (h : G))
  rw [projH_coeff, MonoidAlgebra.coeff_single_mul_apply]
  simp


/-- `projH` as an additive homomorphism. -/
noncomputable def projH_addHom (H : Subgroup G) :
    MonoidAlgebra k G →+ MonoidAlgebra k H where
  toFun := projH k H
  map_zero' := projH_zero k H
  map_add' := projH_add k H

@[simp]
lemma projH_addHom_apply (H : Subgroup G) (x : MonoidAlgebra k G) :
    projH_addHom k H x = projH k H x := rfl

/-- The finite set of left cosets of `H` that meet the support of `x : k[G]`. -/
noncomputable def cosetSupport (H : Subgroup G) (x : MonoidAlgebra k G) : Finset (G ⧸ H) := by
  classical
  exact x.coeff.support.image (fun g => QuotientGroup.mk g)

lemma mem_cosetSupport {H : Subgroup G} {x : MonoidAlgebra k G} {q : G ⧸ H} :
    q ∈ cosetSupport k H x ↔ ∃ g ∈ x.coeff.support, QuotientGroup.mk g = q := by
  classical
  simp [cosetSupport]

/-- The `k[H]`-linear map `k[H]^S → k[H]` sending the `s`-th basis vector to `s - 1`. -/
noncomputable def augMapA (H : Type*) [Group H] (S : Finset H) :
    (S →₀ MonoidAlgebra k H) →ₗ[MonoidAlgebra k H] MonoidAlgebra k H :=
  Finsupp.linearCombination (MonoidAlgebra k H)
    (fun s : S => MonoidAlgebra.single (s : H) (1 : k) - 1)

/-- The `k[G]`-linear map `k[G]^S → k[G]` sending the `s`-th basis vector to `s - 1`. -/
noncomputable def augMapB (G : Type*) [Group G] (H : Subgroup G) (S : Finset H) :
    (S →₀ MonoidAlgebra k G) →ₗ[MonoidAlgebra k G] MonoidAlgebra k G :=
  Finsupp.linearCombination (MonoidAlgebra k G)
    (fun s : S => MonoidAlgebra.single ((s : H) : G) (1 : k) - 1)

lemma augMapA_apply (H : Type*) [Group H] (S : Finset H) (c : S →₀ MonoidAlgebra k H) :
    augMapA k H S c
      = c.sum fun s x => x * (MonoidAlgebra.single (s : H) (1 : k) - 1) := by
  rw [augMapA, Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr fun s _ => rfl

lemma augMapB_apply (G : Type*) [Group G] (H : Subgroup G) (S : Finset H)
    (c : S →₀ MonoidAlgebra k G) :
    augMapB k G H S c
      = c.sum fun s x => x * (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) := by
  rw [augMapB, Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr fun s _ => rfl

end Work.ORFP2
