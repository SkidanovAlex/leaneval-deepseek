import Mathlib.Algebra.Torsor.Defs
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic
import Submission.NK.NUV2.RouteE.levelSymbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# L7 in the cyclic case

For a finite Galois extension `E/F` with **cyclic** Galois group, the level symbol
`NK.NUV2.RouteE.levelSymbol hcomm u hu : Fˣ →* Gal(E/F)` (an arbitrary generator `u` of the cyclic
group `H²(Gal(E/F), Eˣ)`) has kernel exactly the norm group `N_{E/F} Eˣ`.

This is step 1 of L7 (`NK.NUV2.Final.levelSymbol_ker`): the general case reduces to it by passing
to the subfield fixed by a subgroup `K ≥ Im θ` with `Gal(·/F) ≅ G ⧸ K` cyclic
(`NK.NUV2.Final.exists_cyclic_quotient_of_ne_top`), where the level symbols are compatible
(proved L5, `NK.NUV2.RouteE.levelSymbol_restrict`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory

namespace NK.NUV2.Final

/-- **A faithful character of a cyclic group**: the invariant of a generator, viewed as a
`ℚ/ℤ`-valued character, has additive order the cardinality of the group. -/
theorem addOrderOf_invariantOf_of_generator {G : Type} [CommGroup G] [Finite G] (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hgord : addOrderOf (Additive.ofMul g) = Nat.card (Additive G)) :
    addOrderOf (NK.NUV2.RouteC.invariantOf (Additive.ofMul g) hgord) = Nat.card G := by
  have hn0 : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
  rw [NK.NUV2.RouteC.addOrderOf_addMonoidHom_eq_of_generator g hg,
    NK.NUV2.RouteC.invariantOf_generator (Additive.ofMul g) hgord]
  have hcard : Nat.card (Additive G) = Nat.card G := Nat.card_congr (Additive.ofMul)
  rw [hcard, ← NK.NUV2.RouteC.zmodToQmodZ_one (Nat.card G),
    NK.NUV2.RouteC.addOrderOf_zmodToQmodZ hn0, ZMod.addOrderOf_one]

/-- **L7, cyclic case**: the level symbol of a cyclic finite Galois extension has kernel the norm
group. -/
theorem levelSymbol_ker_cyclic {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [Fintype (E ≃ₐ[F] E)]
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)]
    (hcomm : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ) (hcyc : IsCyclic (E ≃ₐ[F] E))
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)) :
    MonoidHom.ker (NK.NUV2.RouteE.levelSymbol (F := F) (E := E) hcomm u hu)
      = NK.LocalReciprocity.normGroup F E := by
  classical
  letI : CommGroup (E ≃ₐ[F] E) := { (inferInstance : Group (E ≃ₐ[F] E)) with mul_comm := hcomm }
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  have hgord : addOrderOf (Additive.ofMul g) = Nat.card (Additive (E ≃ₐ[F] E)) := by
    rw [addOrderOf_ofMul_eq_orderOf]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  let χ : Additive (E ≃ₐ[F] E) →+ NK.NUV2.RouteC.qmodZ :=
    NK.NUV2.RouteC.invariantOf (Additive.ofMul g) hgord
  have hχ : addOrderOf χ = Nat.card (E ≃ₐ[F] E) :=
    addOrderOf_invariantOf_of_generator g hg hgord
  refine le_antisymm ?_ ?_
  · intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : χ (Additive.ofMul (NK.NUV2.RouteE.levelSymbol (F := F) (E := E) hcomm u hu a))
        = 0 := by
      rw [ha]
      exact map_zero χ
    rw [NK.NUV2.RouteE.levelSymbol_apply] at h1
    have h1' : (NK.NUV2.RouteC.invariantOf u hu) ((groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2)
        (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ)) = 0 := h1
    have h2 : (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2)
        (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ) = 0 :=
      NK.NUV2.RouteC.invariantOf_injective u hu (by rw [h1', map_zero])
    exact (NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic hcyc χ hχ a).mp h2
  · intro a ha
    rw [MonoidHom.mem_ker]
    apply NK.NUV2.RouteE.doubleDual_injective hcomm
    intro χ'
    rw [NK.NUV2.RouteE.levelSymbol_apply]
    show NK.NUV2.RouteE.charValue u hu a χ' = χ' (Additive.ofMul 1)
    rw [show NK.NUV2.RouteE.charValue u hu a χ'
        = NK.NUV2.RouteC.invariantOf u hu ((groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
            (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2)
            (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ')) from rfl]
    rw [show (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2)
        (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ') = 0 from
      NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup χ' a ha,
      map_zero]
    simp

end NK.NUV2.Final
