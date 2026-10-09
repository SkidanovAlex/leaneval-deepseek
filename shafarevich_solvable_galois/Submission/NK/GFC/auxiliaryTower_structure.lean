import Mathlib
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.GFC

theorem auxiliaryTower_structure {K E : Type} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (L₀ M : IntermediateField K E) [IsGalois K ↥L₀] [IsGalois K ↥M]
    (hdisj : L₀ ⊓ M = ⊥) (hsup : L₀ ⊔ M = ⊤)
    (hcard : Nat.card (↥L₀ ≃ₐ[K] ↥L₀) = Nat.card (↥M ≃ₐ[K] ↥M))
    (hcyc : IsCyclic (↥M ≃ₐ[K] ↥M)) :
    Nat.card Gal(E/K) = Nat.card (↥L₀ ≃ₐ[K] ↥L₀) * Nat.card (↥L₀ ≃ₐ[K] ↥L₀) ∧
    Module.finrank K E = Nat.card (↥L₀ ≃ₐ[K] ↥L₀) * Nat.card (↥L₀ ≃ₐ[K] ↥L₀) ∧
    Module.finrank K ↥L₀ = Nat.card (↥L₀ ≃ₐ[K] ↥L₀) ∧
    Module.finrank ↥L₀ E = Nat.card (↥L₀ ≃ₐ[K] ↥L₀) ∧
    (∀ g : Gal(E/K), g ^ Nat.card (↥L₀ ≃ₐ[K] ↥L₀) = 1) ∧
    (∀ a b : Gal(E/↥L₀), a * b = b * a) := by
  classical
  set n : ℕ := Nat.card (↥L₀ ≃ₐ[K] ↥L₀) with hn
  have hcardL : Nat.card (↥L₀ ≃ₐ[K] ↥L₀) = n := hn.symm
  have hfrL : Module.finrank K ↥L₀ = n := by
    rw [hn, ← IsGalois.card_aut_eq_finrank K ↥L₀]
  have hnpos : 0 < n := by
    rw [← hfrL]; exact Module.finrank_pos
  have hfrM : Module.finrank K ↥M = n := by
    rw [← IsGalois.card_aut_eq_finrank K ↥M, ← hcard, hn]
  have hcardM : Nat.card (↥M ≃ₐ[K] ↥M) = n := by
    rw [IsGalois.card_aut_eq_finrank K ↥M, hfrM]
  -- linear disjointness and the degree of the compositum
  have hLD : L₀.LinearDisjoint ↥M := IntermediateField.LinearDisjoint.of_inf_eq_bot hdisj
  have hsupfin : Module.finrank K ↥(L₀ ⊔ M) = Module.finrank K ↥L₀ * Module.finrank K ↥M :=
    IntermediateField.LinearDisjoint.finrank_sup hLD
  have hfrE : Module.finrank K E = n * n := by
    have h1 : Module.finrank K ↥(L₀ ⊔ M) = Module.finrank K E := by
      rw [hsup]
      exact (IntermediateField.topEquiv (F := K) (E := E)).toLinearEquiv.finrank_eq
    rw [← h1, hsupfin, hfrL, hfrM]
  have hcardG : Nat.card Gal(E/K) = n * n := by
    rw [IsGalois.card_aut_eq_finrank K E, hfrE]
  -- `[E : L₀] = n`
  have hfrEL : Module.finrank ↥L₀ E = n := by
    have htower : Module.finrank K ↥L₀ * Module.finrank ↥L₀ E = Module.finrank K E :=
      Module.finrank_mul_finrank K ↥L₀ E
    rw [hfrL, hfrE] at htower
    exact Nat.eq_of_mul_eq_mul_left hnpos htower
  -- the exponent
  have hinfFix : L₀.fixingSubgroup ⊓ M.fixingSubgroup = ⊥ := by
    rw [← IntermediateField.fixingSubgroup_sup, hsup, IntermediateField.fixingSubgroup_top]
  have hexp : ∀ g : Gal(E/K), g ^ n = 1 := by
    intro g
    have hmemL : g ^ n ∈ L₀.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker L₀, MonoidHom.mem_ker, map_pow]
      have h := pow_card_eq_one' (x := AlgEquiv.restrictNormalHom ↥L₀ g)
      rwa [hcardL] at h
    have hmemM : g ^ n ∈ M.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker M, MonoidHom.mem_ker, map_pow]
      have h := pow_card_eq_one' (x := AlgEquiv.restrictNormalHom ↥M g)
      rwa [hcardM] at h
    have hmem : g ^ n ∈ L₀.fixingSubgroup ⊓ M.fixingSubgroup := ⟨hmemL, hmemM⟩
    rw [hinfFix, Subgroup.mem_bot] at hmem
    exact hmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsGalois.card_aut_eq_finrank K E, hfrE]
  · exact hfrE
  · exact hfrL
  · exact hfrEL
  · exact hexp
  · intro a b
    haveI : IsCyclic (↥M ≃ₐ[K] ↥M) := hcyc
    haveI : IsMulCommutative (↥M ≃ₐ[K] ↥M) := IsCyclic.isMulCommutative
    have hinj : Function.Injective (IntermediateField.restrictRestrictAlgEquivMapHom K ↥M ↥L₀ E) :=
      IntermediateField.restrictRestrictAlgEquivMapHom_injective M L₀ (by rw [sup_comm]; exact hsup)
    apply hinj
    rw [map_mul, map_mul]
    exact mul_comm' _ _

end NK.GFC
