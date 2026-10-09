import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataTwo.ThreeHalves
import Submission.Work.SSGRoute.ZDataTwo.SWFourTwo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# NodeS37, step 1: the three-halves conclusion from one good class

`Work.SSGRoute.ZDataTwo.mu2ThreeHalves` asks for *three* Kummer classes `b 0, b 1, b 2 ∈ (↥K)ˣ`
with prescribed local behaviour.  Following `ZDataTwo/ACTION_mu2_three_halves_plan.md` §1, the whole
content is the existence of **one** class `B` whose Kummer cochain has the four local properties,
together with the global Kummer class `b` of the datum `y` (which exists by Kummer duality:
`Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst`, applied to the additive,
locally constant `y`).

Indeed, taking

  `b 0 := b`,  `b 1 := b`,  `b 2 := b⁻² B`   (`B` here is the good class),

the cochain of the product is `χ_b + χ_b + χ_{b⁻² B} = χ_B` (characteristic `2`), so

* each `b i` agrees with `y` on the `cs(S)`-blocks iff `χ_B` does (for `i = 0, 1` because
  `χ_b = y`, for `i = 2` because `χ_{b⁻²B} = χ_B`);
* each `b i` kills the involutions (`i = 0,1` by `hyinf`, `i = 2` because `χ_B` does);
* the two place-theoretic conjuncts are those of `χ_B`.

This file contains that reduction, and the two elementary lemmas about the node's cochain which it
needs (`nodeKummerCochar_mul`, `nodeKummerCochar_sq`).
-/

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute
open Work.SSGRoute.ZDataTwo

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-! ## Two elementary identities for the node's Kummer cochain -/

/-- **The node's Kummer cochain is multiplicative in the element.** -/
theorem nodeKummerCochar_mul (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ 2) (a b : (↥K)ˣ) :
    nodeKummerCochar K ζ hζK hζ (a * b) =
      nodeKummerCochar K ζ hζK hζ a + nodeKummerCochar K ζ hζK hζ b :=
  kummerCochar_mul K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) a b

/-- **A square factor is invisible at `p = 2`.** -/
theorem nodeKummerCochar_sq (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ 2) (c : (↥K)ˣ) :
    nodeKummerCochar K ζ hζK hζ (c ^ 2) = 0 :=
  kummerCochar_sq K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) c

/-! ## The three-halves conclusion -/

/-- **The three-halves conclusion** — the body of `Work.SSGRoute.ZDataTwo.mu2ThreeHalves`. -/
def ThreeHalvesConcl (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ 2)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2) : Prop :=
  ∃ (Pset : Finset (ValuationSubring Ω)) (b : Fin 3 → (↥K)ˣ),
    (∀ P ∈ Pset, SSGRoute.IsFinPlace k P) ∧
    (∀ P ∈ Pset, SSGRoute.IsSplitIn k Λ P) ∧
    (∀ P ∈ Pset, ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A P) ∧
    (∀ i : Fin 3, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b i) σ = y σ) ∧
    (∀ i : Fin 3, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b i) c = 0) ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      (∀ P ∈ Pset, ∀ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup → τ • P ≠ B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b 0 * b 1 * b 2) σ = 0) ∧
    (∀ P ∈ Pset, ∀ B : ValuationSubring Ω, SSGRoute.IsConjPlace k P B →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • P = B) →
      ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b 0 * b 1 * b 2) u = 0)

/-- **The reduction of `mu2ThreeHalves` to one good class.**  Given the global Kummer class `b` of
`y` (`hb`), a finite place set `Pset` of `Λ`-split places outside the `cs(S)`-classes, and a class
`B` whose Kummer cochain realises `y` on the `cs(S)`-blocks, kills the involutions, kills the
inertia outside `cs(S)` and the `G_K`-classes of `Pset`, and vanishes on the companions of the
elements of `Pset`, the three-halves conclusion holds, with the halves `(b, b, b⁻²B)`. -/
theorem threeHalvesConcl_of_goodClass
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ 2)
    (S : Finset (ValuationSubring Ω))
    (Pset : Finset (ValuationSubring Ω))
    (hPfin : ∀ P ∈ Pset, SSGRoute.IsFinPlace k P)
    (hPsplit : ∀ P ∈ Pset, SSGRoute.IsSplitIn k Λ P)
    (hPnotS : ∀ P ∈ Pset, ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A P)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2) (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (b B : (↥K)ˣ)
    (hb : ∀ σ ∈ K.fixingSubgroup, nodeKummerCochar K ζ hζK hζ b σ = y σ)
    (h1 : ∀ B' : ValuationSubring Ω, SSGRoute.IsFinPlace k B' →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B') →
      ∀ σ ∈ SSGRoute.decomp k B' ⊓ K.fixingSubgroup,
        nodeKummerCochar K ζ hζK hζ B σ = y σ)
    (h2 : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → nodeKummerCochar K ζ hζK hζ B c = 0)
    (h3 : ∀ B' : ValuationSubring Ω, SSGRoute.IsFinPlace k B' →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B') →
      (∀ P ∈ Pset, ∀ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup → τ • P ≠ B') →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B' σ →
        nodeKummerCochar K ζ hζK hζ B σ = 0)
    (h4 : ∀ P ∈ Pset, ∀ B' : ValuationSubring Ω, SSGRoute.IsConjPlace k P B' →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • P = B') →
      ∀ u ∈ SSGRoute.decomp k B' ⊓ K.fixingSubgroup,
        nodeKummerCochar K ζ hζK hζ B u = 0) :
    ThreeHalvesConcl k Ω K Λ ζ hζK hζ S y := by
  classical
  -- `χ_{b⁻²B} = χ_B`
  have hmul : nodeKummerCochar K ζ hζK hζ ((b ^ 2)⁻¹ * B) =
      nodeKummerCochar K ζ hζK hζ B := by
    rw [nodeKummerCochar_mul, show (b ^ 2)⁻¹ = (b⁻¹) ^ 2 by group,
      nodeKummerCochar_sq, zero_add]
  -- the three halves
  let bf : Fin 3 → (↥K)ˣ :=
    Fin.cases b (Fin.cases b (fun _ : Fin 1 => (b ^ 2)⁻¹ * B))
  have hbf0 : bf 0 = b := rfl
  have hbf1 : bf 1 = b := rfl
  have hbf2 : bf 2 = (b ^ 2)⁻¹ * B := rfl
  have hprod : bf 0 * bf 1 * bf 2 = B := by
    rw [hbf0, hbf1, hbf2]
    group
  have hrepr : ∀ i : Fin 3, nodeKummerCochar K ζ hζK hζ (bf i) =
      nodeKummerCochar K ζ hζK hζ B ∨ bf i = b := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi with h | h | h
    · rw [h, hbf0]; exact Or.inr rfl
    · rw [h, hbf1]; exact Or.inr rfl
    · rw [h, hbf2]; exact Or.inl hmul
  refine ⟨Pset, bf, hPfin, hPsplit, hPnotS, ?_, ?_, ?_, ?_⟩
  · -- each half agrees with `y` on the `cs(S)`-blocks
    intro i B' hB' hconj σ hσ
    rcases hrepr i with h | h
    · rw [h]; exact h1 B' hB' hconj σ hσ
    · rw [h]; exact hb σ (Subgroup.mem_inf.mp hσ).2
  · -- each half kills the involutions
    intro i c hc hc2
    rcases hrepr i with h | h
    · rw [h]; exact h2 c hc hc2
    · rw [h, hb c hc]; exact hyinf c hc hc2
  · -- the product agrees with `χ_B` on the inertia outside the `Pset`-classes
    intro B' hB' hnotS hnotP σ hσK hσI
    rw [hprod]
    exact h3 B' hB' hnotS hnotP σ hσK hσI
  · -- and vanishes on the companions
    intro P hP B' hconj hnotconj u hu
    rw [hprod]
    exact h4 P hP B' hconj hnotconj u hu

end Work.SSGRoute.NodeS37
