import Submission.VermaNonzero

/-!
# The ⋆-action model of `Submission.StarQuotient` **is** the Verma module

Let `A = FA (Fin 8) = ℂ⟨f₁,…,f₈⟩` be the free associative algebra, `J ⊆ A` the `ℂ`-span of the
products `wordElt u * s * wordElt v` over the "f-side" Serre elements `s ∈ Gen` (so that
`A ⧸ J = U(𝔫⁻)`), and `V = A ⧸ J` with the `e₈`-action of `Submission.StarQuotient`
(`Submission.VermaNonzero.act`).  This file proves that the induced map

  `M(λ) = U(e₈) ⧸ J(λ)  ⟶  V`,   `u ↦ ρ(u)(1 + J)`

is an **isomorphism** for every weight `λ`.  Hence the ⋆-action model is a concrete realization of
the Verma module and the `f`-side Serre relations are the *only* relations imposed on a highest
weight vector.
-/

set_option backward.isDefEq.respectTransparency false
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

noncomputable section
open scoped BigOperators

namespace Submission.VermaModel

open Submission.StarQuotient Submission.StarModule Submission.E8Weights Submission.VermaNonzero

abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

abbrev U : Type := UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)

/-- The algebra map `ℂ⟨f₁,…,f₈⟩ → U(e₈)` sending the free generator `fᵢ` to `Fᵢ`. -/
noncomputable def iotaA : FA (Fin 8) →ₐ[ℂ] U :=
  (MonoidAlgebra.lift ℂ U (FreeMonoid (Fin 8)))
    (FreeMonoid.lift (fun i => Submission.E8Weights.f i))

lemma iotaA_wordElt (i : Fin 8) : iotaA (wordElt [i]) = Submission.E8Weights.f i := by
  simp [iotaA, wordElt]

lemma iotaA_serreGen (p q : Fin 8) :
    iotaA (serreGen p q) = UniversalEnvelopingAlgebra.ι ℂ ⁅SerreF p, SerreF q⁆ := by
  rw [serreGen, map_sub, map_mul, map_mul]
  simp only [iotaA_wordElt, LieHom.map_lie, LieRing.of_associative_ring_bracket,
    Submission.E8Weights.f]

lemma iotaA_serreGen2 (p q : Fin 8) :
    iotaA (serreGen2 p q) = UniversalEnvelopingAlgebra.ι ℂ ⁅SerreF p, ⁅SerreF p, SerreF q⁆⁆ := by
  rw [serreGen2, map_sub, map_mul, map_mul]
  simp only [iotaA_wordElt, iotaA_serreGen, LieHom.map_lie, LieRing.of_associative_ring_bracket,
    Submission.E8Weights.f]

lemma iotaA_serreGen_eq_zero (p q : Fin 8) (h : E8 p q = 0) : iotaA (serreGen p q) = 0 := by
  rw [iotaA_serreGen]
  have hz : ⁅SerreF p, SerreF q⁆ = 0 := by
    have h1 := serreLie_adF p q
    rw [show CartanMatrix.E₈ p q = 0 from h] at h1
    simpa using h1
  rw [hz, map_zero]

lemma iotaA_serreGen2_eq_zero (p q : Fin 8) (h : E8 p q = -1) : iotaA (serreGen2 p q) = 0 := by
  rw [iotaA_serreGen2]
  have hz : ⁅SerreF p, ⁅SerreF p, SerreF q⁆⁆ = 0 := by
    have h1 := serreLie_adF p q
    rw [show CartanMatrix.E₈ p q = -1 from h] at h1
    simpa using h1
  rw [hz, map_zero]

lemma iotaA_gen (s : FA (Fin 8)) (hs : s ∈ Gen E8) : iotaA s = 0 := by
  rcases hs with ⟨p, q, hpq, _, rfl⟩ | ⟨p, q, _, hpq, rfl⟩
  · exact iotaA_serreGen_eq_zero p q hpq
  · exact iotaA_serreGen2_eq_zero p q hpq

lemma iotaA_mem_J (x : FA (Fin 8)) (hx : x ∈ J E8) : iotaA x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨s, hs, u, v, rfl⟩
      rw [map_mul, map_mul, iotaA_gen s hs, mul_zero, zero_mul]
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- The class of `1` in `V = A ⧸ J`, the highest weight vector of the ⋆-model. -/
def v0 : V E8 := Submodule.Quotient.mk (1 : FA (Fin 8))

lemma iotaA_wordElt_list (w : List (Fin 8)) :
    iotaA (wordElt w) = (w.map Submission.E8Weights.f).prod := by
  induction w with
  | nil => rw [wordElt_nil, List.map_nil, List.prod_nil, map_one]
  | cons i w ih => rw [wordElt_cons_eq, List.map_cons, List.prod_cons, map_mul, iotaA_wordElt, ih]

/-- The `A`-action on `V` through `ρ ∘ ι'` is the given left multiplication:
`rho lam (iotaA x) v0 = mk x`. -/
lemma rho_v0_eq_mk (lam : Fin 8 → ℂ) (x : FA (Fin 8)) :
    rho lam (iotaA x) v0 = Submodule.Quotient.mk (p := J E8) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, Submodule.Quotient.mk_zero]; rfl
  | add p q hp hq =>
      rw [map_add, map_add, LinearMap.add_apply, hp, hq, Submodule.Quotient.mk_add]
  | single w c =>
      have hsw : (MonoidAlgebra.single w c : FA (Fin 8)) = c • wordElt (FreeMonoid.toList w) := by
        rw [wordElt]; simp [MonoidAlgebra.smul_single]
      rw [hsw, map_smul, map_smul, LinearMap.smul_apply, iotaA_wordElt_list,
        show v0 = Submodule.Quotient.mk (p := J E8) (1 : FA (Fin 8)) from rfl, rho_fword,
        ← Submodule.Quotient.mk_smul, ← hsw]

end Submission.VermaModel
