import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataTwo.SWFourTwo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Schmidt--Wingberg section four, `p = 2`: the three-term assembly of the `z`-data

This module isolates the *bookkeeping* half of Schmidt--Wingberg's section four in the exceptional
case `p = 2` (`arXiv:math/9809211`, pp. 16--17): once the three halves `z₁, z₂, z_N` of the final
class `z = z_i + z_j + z_N` have been produced (each being the Kummer cochain of an element of
`Kˣ`, agreeing with the data `y` on the places of `cs(S)`, vanishing on the involutions, and
ramified only over its own new "escape" prime, with the one-sided vanishing of the *sum* at the
companions of the three escape primes), the node's four arithmetic conjuncts follow, with
`b = b₁ · b₂ · b₃`.

The two inputs which the construction supplies and which this module consumes are:

* **confinement** — `z` is unramified outside `cs(S) ∪ {G_K-conjugates of Pset}` (the paper's
  condition (1), summed over the three halves);
* **one-sided vanishing** — for every escape prime `P ∈ Pset` and every `k`-conjugate place `B`
  of `P` which is not `G_K`-conjugate to it, the class `z` vanishes on the local group
  `decomp k B ⊓ G_K` (the paper's condition (b): `z_{σP} = 0` for `σ ∈ G(K|k) ∖ {1}`).

The two derived conjuncts are:

* clause (3) — `z` is unramified at every place outside `cs(S)` that is not split in `Λ`
  (`unramified_outside_of_confinement`), because an escape prime is split in `Λ` and complete
  splitting in a normal extension is invariant under `G_k`-conjugation;
* clause (4) — if `z` is ramified at such a split place `B`, then `B` is a `G_K`-conjugate of one
  of the escape primes, and the one-sided vanishing transfers to the companions of `B`
  (`companion_vanishing_of_confinement`).

This is the `p = 2` analogue of `Work.SSGRoute.ZSplit.sw_conjuncts_five_six` (the odd-`p` two-term
assembly); the difference is that three escape primes (not two) are involved, which is the reason
for the shoe-box principle in the exceptional case.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-! ## Clause (3): unramifiedness away from `cs(S)` at the places not split in `Λ` -/

/-- **Clause (3) of the `z`-data from the confinement of the ramification.**
If `z` is unramified outside `cs(S)` and the `G_K`-conjugates of the escape primes `Pset`, and
every escape prime is split in the normal level `Λ`, then `z` is unramified at every place outside
`cs(S)` that is not split in `Λ`. -/
theorem unramified_outside_of_confinement
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    (S Pset : Finset (ValuationSubring Ω))
    (hPsplit : ∀ P ∈ Pset, SSGRoute.IsSplitIn k Λ P)
    (z : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hz_conf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      (∀ P ∈ Pset, ∀ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup → τ • P ≠ B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0 := by
  intro B hB hnotS hnsplit σ hσK hσI
  refine hz_conf B hB hnotS ?_ σ hσK hσI
  intro P hP τ hτK hτPB
  exact hnsplit (hτPB ▸
    (SSGRoute.isSplitIn_conj Λ (IsGalois.fixingSubgroup_normal_of_isGalois Λ) P τ).mpr
      (hPsplit P hP))

/-! ## Clause (4): the one-sided vanishing transfers to the companions of a ramified place -/

/-- **Clause (4) of the `z`-data from the confinement and the one-sided vanishing.**
Suppose `z` is unramified outside `cs(S)` and the `G_K`-conjugates of `Pset`, and that for every
escape prime `P ∈ Pset` the class `z` vanishes on the local groups of the `k`-conjugates of `P`
that are not `G_K`-conjugates of it.  Then at every place `B` outside `cs(S)` that is split in `Λ`
and at which `z` is ramified, `z` vanishes on the local groups of the companions of `B`.

The point is that such a `B` must be a `G_K`-conjugate of some escape prime (otherwise `z` would be
unramified there), which makes `B`'s companions companions of that escape prime. -/
theorem companion_vanishing_of_confinement
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    (S Pset : Finset (ValuationSubring Ω))
    (z : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hz_conf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      (∀ P ∈ Pset, ∀ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup → τ • P ≠ B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0)
    (hz_conj : ∀ P ∈ Pset, ∀ B : ValuationSubring Ω, SSGRoute.IsConjPlace k P B →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • P = B) →
      ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z u = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0 := by
  intro B hB hnotS _ hram Q hBQ hnotconj τ hτ
  -- `B` is a `G_K`-conjugate of one of the escape primes
  have hBc : ∃ P ∈ Pset, ∃ ρ ∈ K.fixingSubgroup, ρ • P = B := by
    by_contra h
    push Not at h
    obtain ⟨σI, hσII, hσIK, hσIne⟩ := hram
    exact hσIne (hz_conf B hB hnotS (fun P hP τ' hτ'K => h P hP τ' hτ'K) σI hσIK hσII)
  obtain ⟨P, hP, ρ, hρK, hρPB⟩ := hBc
  -- `Q` is a `k`-conjugate of `P`, but not a `G_K`-conjugate of it
  obtain ⟨τ₁, hτ₁⟩ := hBQ
  have hPQ : SSGRoute.IsConjPlace k P Q := ⟨τ₁ * ρ, by rw [mul_smul, hρPB, hτ₁]⟩
  have hρinv : ρ⁻¹ • B = P := by rw [← hρPB, inv_smul_smul]
  have hnotKQ : ¬ ∃ ν ∈ K.fixingSubgroup, ν • P = Q := by
    rintro ⟨ν, hνK, hνQ⟩
    refine hnotconj ⟨ν * ρ⁻¹,
      K.fixingSubgroup.mul_mem hνK (K.fixingSubgroup.inv_mem hρK), ?_⟩
    rw [mul_smul, hρinv, hνQ]
  exact hz_conj P hP Q hPQ hnotKQ τ hτ

/-! ## The arithmetic core of the node from the three halves

We now assemble the node's arithmetic core (`Work.SSGRoute.shafarevich_z_data_two_kummerCore`) from
the three halves.  The class is `b = b₀ b₁ b₂`; its Kummer cochain is the sum
`z_{b₀} + z_{b₁} + z_{b₂}` (`Work.SSGRoute.ZDataTwo.threeTerm_eq_of_mul`), hence agrees with `y`
at `cs(S)` (clause (1): `3 · y = y` in `𝔽₂`), vanishes on the involutions (clause (2)), and
inherits the two place-theoretic conjuncts from the two lemmas above. -/

/-- In `𝔽₂`, three copies of an element sum to that element: `x + x + x = x`. -/
private lemma zmodTwo_three_add (x : ZMod 2) : x + x + x = x := by
  rw [zmodTwo_add_self x, zero_add]

/-- **The arithmetic core of the `p = 2` node from the three halves of section four.**

Let `b : Fin 3 → (↥K)ˣ` be the three halves.  Assume

* each `z_{b i}` agrees with the data `y` on the decomposition groups of the places of `cs(S)`;
* each `z_{b i}` vanishes on the involutions of `G_K`;
* the sum `z = z_{b 0} + z_{b 1} + z_{b 2}` is unramified outside `cs(S)` and the `G_K`-conjugates
  of the escape primes `Pset`;
* the sum vanishes on the local groups of the `k`-conjugates of the escape primes that are not
  `G_K`-conjugate to them.

Then `b := b 0 * b 1 * b 2` satisfies the four conjuncts of
`Work.SSGRoute.shafarevich_z_data_two_kummerCore`. -/
theorem kummerCore_of_three_halves
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω))
    (Pset : Finset (ValuationSubring Ω))
    (hPfin : ∀ P ∈ Pset, SSGRoute.IsFinPlace k P)
    (hPsplit : ∀ P ∈ Pset, SSGRoute.IsSplitIn k Λ P)
    (hPnotS : ∀ P ∈ Pset, ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A P)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (b : Fin 3 → (↥K)ˣ)
    (hagree : ∀ i : Fin 3, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        nodeKummerCochar K ζ hζK hζ (b i) σ = y σ)
    (hinv : ∀ i : Fin 3, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      nodeKummerCochar K ζ hζK hζ (b i) c = 0)
    (hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      (∀ P ∈ Pset, ∀ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup → τ • P ≠ B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        nodeKummerCochar K ζ hζK hζ (b 0 * b 1 * b 2) σ = 0)
    (hconj : ∀ P ∈ Pset, ∀ B : ValuationSubring Ω, SSGRoute.IsConjPlace k P B →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • P = B) →
      ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        nodeKummerCochar K ζ hζK hζ (b 0 * b 1 * b 2) u = 0) :
    ∃ b' : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          nodeKummerCochar K ζ hζK hζ b' σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → nodeKummerCochar K ζ hζK hζ b' c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          nodeKummerCochar K ζ hζK hζ b' σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          nodeKummerCochar K ζ hζK hζ b' σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
            nodeKummerCochar K ζ hζK hζ b' τ = 0) := by
  classical
  have hzsum := threeTerm_eq_of_mul k Ω K ζ hζ hζK (b 0) (b 1) (b 2)
  refine ⟨b 0 * b 1 * b 2, ?_, ?_, ?_, ?_⟩
  · -- clause (1): the sum agrees with `y` on the places of `cs(S)`
    intro B hB hconjB σ hσK hσd
    rw [congrFun hzsum σ]
    simp only [Pi.add_apply]
    rw [hagree 0 B hB hconjB σ (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩),
      hagree 1 B hB hconjB σ (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩),
      hagree 2 B hB hconjB σ (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩)]
    exact zmodTwo_three_add (y σ)
  · -- clause (2): the sum vanishes on the involutions
    intro c hcK hc2
    rw [congrFun hzsum c]
    simp only [Pi.add_apply]
    rw [hinv 0 c hcK hc2, hinv 1 c hcK hc2, hinv 2 c hcK hc2, add_zero, add_zero]
  · -- clause (3): unramifiedness outside `cs(S)` at the places not split in `Λ`
    exact unramified_outside_of_confinement K Λ S Pset hPsplit _ hconf
  · -- clause (4): the one-sided vanishing
    exact companion_vanishing_of_confinement K Λ S Pset _ hconf hconj

end Work.SSGRoute.ZDataTwo
