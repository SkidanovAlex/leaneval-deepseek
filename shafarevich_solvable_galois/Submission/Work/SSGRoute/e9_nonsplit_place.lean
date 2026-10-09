import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.Sha2Lib.chebotarev_element_stabilizer
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped NumberField

/-- A nontrivial finite Galois extension of number fields has a place at which it does not split
completely: there is a place `v` of `K` and a place `W` of `E` above it whose decomposition group
(the stabiliser of `W` in `Gal(E/K)`) is nontrivial.  Route: if every place split completely, then
`∀ σ : E ≃ₐ[K] E, σ = 1` by Čebotarev's element form (`chebotarev_element_stabilizer`); but by
`IsGalois.card_aut_eq_finrank`, `Nat.card Gal(E/K) = [E : K] ≠ 1`, so `Gal(E/K) ≠ ⊥`, and a place
of `K` below a place of `E` exists (`NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder`). -/
theorem e9_nonsplit_place (K : Type) [Field K] [NumberField K]
    (E : Type) [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (hE : Module.finrank K E ≠ 1) :
    ∃ (v : NK.GlobalCFT.Place K) (W : NK.GlobalCFT.Place E),
      NK.GlobalCFT.Place.LiesOver W v ∧ MulAction.stabilizer (E ≃ₐ[K] E) W ≠ ⊥ := by
  -- `[E : K] ≠ 1`, so the Galois group is nontrivial.
  have hcard : Nat.card (E ≃ₐ[K] E) = Module.finrank K E := IsGalois.card_aut_eq_finrank K E
  have hnt : Nontrivial (E ≃ₐ[K] E) := by
    by_contra h
    have hsub : Subsingleton (E ≃ₐ[K] E) := not_nontrivial_iff_subsingleton.mp h
    have h1 : Nat.card (E ≃ₐ[K] E) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    exact hE (by rw [← hcard]; exact h1)
  obtain ⟨σ, hσ⟩ : ∃ σ : E ≃ₐ[K] E, σ ≠ 1 := exists_ne 1
  -- Čebotarev's element form: `σ` fixes some place of `E`.
  obtain ⟨W, hW⟩ := Work.SSGRoute.Sha2Lib.chebotarev_element_stabilizer K E σ
  -- Every place of `E` lies over a place of `K`.
  obtain ⟨v, hv⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := E) W
  exact ⟨v, W, hv, fun hbot => hσ (Subgroup.mem_bot.mp (hbot ▸ hW))⟩

end Work.SSGRoute
