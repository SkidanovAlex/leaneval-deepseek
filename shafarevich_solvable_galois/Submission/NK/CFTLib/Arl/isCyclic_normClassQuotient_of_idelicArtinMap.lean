import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFTdeep.hasseNorm_index_eq_universe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cyclicity of the norm class quotient from the idèlic Artin map

Let `L / K` be a finite cyclic Galois extension of number fields and let
`art : 𝕀 K →* Gal(L/K)` be a monoid homomorphism which kills the principal idèles and the norms
from `L`, and which is surjective.  Then the norm class quotient `C_K ⧸ N_{L/K} C_L` is cyclic.

Indeed `art` descends to a surjection `C_K ⧸ N_{L/K} C_L ↠ Gal(L/K)`, and by the (unconditional)
index formula `[C_K : N_{L/K} C_L] = [L : K] = #Gal(L/K)` this surjection is an isomorphism.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.CFTLib.Arl

open NK.GlobalCFT

theorem isCyclic_normClassQuotient_of_idelicArtinMap {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (art : NK.GlobalCFT.Idele K →* Gal(L/K))
    (hprincipal : ∀ a : Kˣ, art (NK.GlobalCFT.Idele.principalIdele K a) = 1)
    (hnorm : ∀ y : NK.GlobalCFT.Idele L, art (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hsurj : Function.Surjective art) :
    IsCyclic (NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K L) := by
  -- `art` kills the principal idèles, hence descends to the idèle class group `C_K`.
  have h1 : Idele.principalSubgroup K ≤ art.ker := by
    rintro x ⟨a, rfl⟩
    exact MonoidHom.mem_ker.mpr (hprincipal a)
  let art1 : IdeleClassGroup K →* Gal(L/K) :=
    QuotientGroup.lift (Idele.principalSubgroup K) art h1
  have hart1 : ∀ x : Idele K, art1 (IdeleClassGroup.mk K x) = art x := by
    intro x
    rw [IdeleClassGroup.mk_apply]
    exact QuotientGroup.lift_mk' (Idele.principalSubgroup K) h1 x
  have hart1_surj : Function.Surjective art1 := by
    intro g
    obtain ⟨x, hx⟩ := hsurj g
    exact ⟨IdeleClassGroup.mk K x, by rw [hart1, hx]⟩
  -- `art` kills the norms as well, so `art1` descends to `C_K ⧸ N_{L/K} C_L`.
  have h2 : Idele.normClassSubgroup K L ≤ art1.ker := by
    intro z hz
    change z ∈ (Idele.normImage K L).map (IdeleClassGroup.mk K) at hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    rw [MonoidHom.mem_ker, hart1]
    rw [Idele.normImage_eq_map, MonoidHom.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact hnorm y
  let Q := IdeleClassGroup K ⧸ Idele.normClassSubgroup K L
  let art2 : Q →* Gal(L/K) :=
    QuotientGroup.lift (Idele.normClassSubgroup K L) art1 h2
  have hart2 : ∀ z : IdeleClassGroup K,
      art2 (QuotientGroup.mk' (Idele.normClassSubgroup K L) z) = art1 z := by
    intro z
    exact QuotientGroup.lift_mk' (Idele.normClassSubgroup K L) h2 z
  have hart2_surj : Function.Surjective art2 := by
    intro g
    obtain ⟨x, hx⟩ := hart1_surj g
    exact ⟨QuotientGroup.mk' (Idele.normClassSubgroup K L) x, by rw [hart2, hx]⟩
  -- Cardinality: `#(C_K ⧸ N_{L/K} C_L) = [L : K] = #Gal(L/K)`.
  have hcardQ : Nat.card Q = Module.finrank K L := by
    change Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) = Module.finrank K L
    rw [← Subgroup.index_eq_card (Idele.normClassSubgroup K L),
      NK.GlobalCFTdeep.hasseNorm_index_eq_universe (K := K) (L := L)]
  have hcardG : Nat.card Gal(L/K) = Module.finrank K L :=
    IsGalois.card_aut_eq_finrank K L
  have hcardqk : Nat.card (Q ⧸ art2.ker) = Nat.card Gal(L/K) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange art2).toEquiv]
    rw [MonoidHom.range_eq_top.mpr hart2_surj, Subgroup.card_top]
  -- Hence `art2` has trivial kernel, so it is an isomorphism onto the cyclic group `Gal(L/K)`.
  have hker_index : art2.ker.index = Nat.card Q := by
    rw [Subgroup.index_eq_card, hcardqk, hcardG, ← hcardQ]
  have hcardker : Nat.card (art2.ker) = 1 := by
    have h := art2.ker.card_mul_index
    rw [hker_index] at h
    have hQpos : 0 < Nat.card Q := hcardQ.symm ▸ Module.finrank_pos
    refine Nat.mul_right_cancel hQpos ?_
    rw [h, one_mul]
  have hkerbot : art2.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ hcardker
  have hinj : Function.Injective art2 := (MonoidHom.ker_eq_bot_iff art2).mp hkerbot
  have hcycG : IsCyclic (Gal(L/K)) := inferInstance
  have e : Q ≃* Gal(L/K) := MulEquiv.ofBijective art2 ⟨hinj, hart2_surj⟩
  exact e.isCyclic.mpr hcycG

end NK.CFTLib.Arl
