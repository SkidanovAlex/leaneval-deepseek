/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Injectivity of `K[G] → S = D(G)`

Node N14, part (2): the map `LinData.toS : K[G] →ₐ[K] S = D(G)` (a `K`-subalgebra of the ring
of affiliated operators `U(G)`) is injective, i.e. `K[G] ⊆ S`.

The proof is Linnell independence (I1) at the trivial subgroup `⊥`.  The composite
`LinData.toU = (coe : S → U) ∘ LinData.toS` sends a finitely supported family `x : K[G]` to

`∑_{g ∈ supp x} algebraMap K U (x g) * gen g`,

i.e. to a `D(⊥) = K`-linear combination of the group elements `gen g` with pairwise distinct
group parts `g` (they lie in pairwise distinct right cosets of `⊥`).  By (I1) such a
combination vanishes only if every coefficient vanishes.  (Injectivity is *not* formal: over a
general `K`-algebra the images of a group under an injective monoid homomorphism need not be
`K`-linearly independent.)  Injectivity of `toS` then follows because the inclusion `S ↪ U` is
injective.
-/

import Mathlib
import Submission.Work.ORAssembly.RingHalfDefs
import Submission.Work.ORLinnell.Main

universe u

namespace Work.ORAssembly.Ring

open Work.ORLinnell

/-- The `K`-algebra map `K[G] → U` attached to a Linnell datum is injective (Linnell
independence (I1) at the trivial subgroup). -/
theorem toU_injective {K : Type u} [Field K] {G : Type u} [Group G] {U : Type u} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) :
    Function.Injective (Work.ORAssembly.LinData.toU L) := by
  -- It suffices to show that an element of `K[G]` with vanishing image vanishes.
  have key : ∀ x : MonoidAlgebra K G, Work.ORAssembly.LinData.toU L x = 0 → x = 0 := by
    intro x hx
    classical
    -- `toU` evaluated on `x = ∑_{g ∈ supp x} single g (x g)` is the sum
    -- `∑_{g ∈ supp x} algebraMap K U (x g) * gen g`.
    have h1 : Work.ORAssembly.LinData.toU L x =
        ∑ i : ↑x.coeff.support, algebraMap K U (x.coeff ↑i) * (L.gen (↑i : G) : U) := by
      rw [Work.ORAssembly.LinData.toU, MonoidAlgebra.lift_apply', Finsupp.sum]
      rw [← Finset.sum_coe_sort x.coeff.support
        (fun a => algebraMap K U (x.coeff a) * (Work.ORAssembly.LinData.genU L) a)]
      rfl
    have hsum : ∑ i : ↑x.coeff.support,
        algebraMap K U (x.coeff ↑i) * (L.gen (↑i : G) : U) = 0 := by
      rw [← h1]; exact hx
    -- The group parts are the elements of `supp x`, all of whose right `⊥`-cosets are distinct.
    have hind := Work.ORLinnell.FiniteIndex.independence_fintype L (H := ⊥)
      (g := fun i : ↑x.coeff.support => (↑i : G))
      (hinj := fun i j hij => Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hij)))
      (a := fun i : ↑x.coeff.support => algebraMap K U (x.coeff ↑i))
      (ha := fun i => L.algebraMap_mem ⊥ _)
      (hsum := hsum)
    -- Hence every coefficient of `x` vanishes.
    apply MonoidAlgebra.ext
    ext g
    by_cases hg : g ∈ x.coeff.support
    · have h3 : algebraMap K U (x.coeff g) = 0 := hind ⟨g, hg⟩
      by_contra hne
      have h4 : (x.coeff g) • (1 : U) = 0 := by
        rwa [Algebra.algebraMap_eq_smul_one] at h3
      have h5 : (1 : U) = 0 := by
        have h6 := congrArg (fun u : U => (x.coeff g)⁻¹ • u) h4
        simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] using h6
      exact one_ne_zero h5
    · exact Finsupp.notMem_support_iff.mp hg
  intro x y hxy
  have h2 : x - y = 0 := key _ (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp h2

/-- **Linnell independence (I1) at the trivial subgroup**, in the form needed by the assembly:
the `K`-algebra map `K[G] → S = D(G)` is injective. -/
theorem toS_injective {K : Type u} [Field K] {G : Type u} [Group G] {U : Type u} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) : Function.Injective (Work.ORAssembly.LinData.toS L) := by
  intro x y hxy
  apply toU_injective L
  have h : ((Work.ORAssembly.LinData.toS L x : ↥(Work.ORAssembly.LinData.SAlg L)) : U) =
      ((Work.ORAssembly.LinData.toS L y : ↥(Work.ORAssembly.LinData.SAlg L)) : U) :=
    congrArg Subtype.val hxy
  simpa using h

end Work.ORAssembly.Ring
