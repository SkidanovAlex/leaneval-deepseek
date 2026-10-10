import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Algebra.Group.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finitely many open-kernel homomorphisms into a group of prime order

Let `G` be a topological group and suppose that for every prime `l` there are only finitely many
open-kernel homomorphisms `G →* Multiplicative (ZMod l)`.  Then for every finite *abelian* group `S`
whose cardinality `l = Nat.card S` is prime, there are only finitely many open-kernel
homomorphisms `G →* S`.

The point is that a group of prime order is cyclic, so `S` is isomorphic to
`Multiplicative (ZMod (Nat.card S))` (`isCyclic_of_prime_card` and `zmodCyclicMulEquiv`), and this
`MulEquiv` identifies the two sets of homomorphisms with their (unchanged) kernels.
-/

namespace Work.SSGRoute

theorem primeCard_homs_finite {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ∀ l : ℕ, l.Prime → Finite {χ : G →* Multiplicative (ZMod l) // IsOpen (χ.ker : Set G)})
    (S : Type*) [CommGroup S] [Finite S] (hl : (Nat.card S).Prime) :
    Finite {χ : G →* S // IsOpen (χ.ker : Set G)} := by
  -- a group of prime order is cyclic, hence isomorphic to `Multiplicative (ZMod (Nat.card S))`
  let e : S ≃* Multiplicative (ZMod (Nat.card S)) :=
    (zmodCyclicMulEquiv (G := S)
      (isCyclic_of_prime_card (p := Nat.card S) (hp := Fact.mk hl) rfl)).symm
  -- the hypothesis at the prime `Nat.card S`
  have hfin : Finite {ψ : G →* Multiplicative (ZMod (Nat.card S)) // IsOpen (ψ.ker : Set G)} :=
    h (Nat.card S) hl
  -- post-composition with `e` is injective and preserves the kernel
  refine @Finite.of_injective _ _
    (by simpa using hfin)
    (fun χ : {χ : G →* S // IsOpen (χ.ker : Set G)} =>
      (⟨e.toMonoidHom.comp χ.1, ?_⟩ :
        {ψ : G →* Multiplicative (ZMod (Nat.card S)) // IsOpen (ψ.ker : Set G)}))
    ?_
  · -- `ker (e ∘ χ) = ker χ` because `e` is injective
    have hk : (e.toMonoidHom.comp χ.1).ker = χ.1.ker :=
      MonoidHom.ker_comp_of_injective χ.1 e.toMonoidHom e.injective
    rw [hk]
    exact χ.2
  · intro x y hxy
    have h1 : e.toMonoidHom.comp x.1 = e.toMonoidHom.comp y.1 := Subtype.ext_iff.mp hxy
    have h2 : x.1 = y.1 := by
      ext g
      exact e.injective (by
        have hg := congrFun (congrArg
          (fun f : G →* Multiplicative (ZMod (Nat.card S)) =>
            (f : G → Multiplicative (ZMod (Nat.card S)))) h1) g
        simpa using hg)
    exact Subtype.ext h2

end Work.SSGRoute
