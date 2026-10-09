import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

/-- **A character of `Gal(L/K)` with kernel the fixing subgroup of a degree-`p` Galois
subextension.**  Let `K ⊆ L` be a finite Galois extension of number fields and `E` an intermediate
field with `E/K` Galois of degree `p` (a prime).  Then the restriction map
`Gal(L/K) → Gal(E/K)` is surjective, and since `Gal(E/K)` has order `p` it admits an isomorphism
with `Multiplicative (ZMod p)`; composing gives a character of `Gal(L/K)` whose kernel is exactly
the fixing subgroup `Gal(L/E) = E.fixingSubgroup`. -/
theorem exists_char_ker_fixingSubgroup {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : IntermediateField K L) [FiniteDimensional K E] [IsGalois K E]
    (p : ℕ) [Fact p.Prime] (hrank : Module.finrank K E = p) :
    ∃ χ : Gal(L/K) →* Multiplicative (ZMod p), χ.ker = E.fixingSubgroup := by
  classical
  -- The restriction map `Gal(L/K) →* Gal(E/K)` (well defined since `E/K` is normal).
  let φ : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  -- Its kernel is exactly the fixing subgroup of `E` (i.e. `Gal(L/E)`).
  have hker : φ.ker = E.fixingSubgroup := by
    ext σ
    simp only [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    rw [show φ σ = AlgEquiv.restrictNormal σ E from rfl, AlgEquiv.restrictNormal_eq_one_iff]
  -- `Gal(E/K)` has order `p`, hence is cyclic of order `p`, so it is isomorphic to `ZMod p`.
  have hcard : Nat.card Gal(E/K) = p := by
    rw [IsGalois.card_aut_eq_finrank K E, hrank]
  have hcyc : IsCyclic Gal(E/K) := isCyclic_of_prime_card hcard
  let e : Gal(E/K) ≃* Multiplicative (ZMod p) := hcard ▸ (zmodCyclicMulEquiv hcyc).symm
  refine ⟨e.toMonoidHom.comp φ, ?_⟩
  -- Composing with the injective `e` does not change the kernel.
  ext σ
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  change e (φ σ) = 1 ↔ σ ∈ E.fixingSubgroup
  rw [MulEquiv.map_eq_one_iff, ← hker]
  exact MonoidHom.mem_ker.symm

end Work.SSGcrux
