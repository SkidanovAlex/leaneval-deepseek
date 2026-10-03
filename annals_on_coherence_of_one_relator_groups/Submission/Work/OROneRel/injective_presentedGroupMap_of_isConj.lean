import Mathlib
import Submission.Work.OROneRel.Interface

/-!
# Conjugate relators: injectivity of the canonical Magnus map

If `s` is conjugate to `r` in the free group `F(α)`, then the two relators generate the *same*
normal closure `N{s} = N{r} =: N ⊴ F(α)`, hence present the same group
`⟨α | s⟩ = F(α)/N = ⟨α | r⟩` (with the *identity* on the generators, see
`Work.OROneRel.presentedGroup_conj_iso`).

Consequently the canonical maps `F(T) →* ⟨α | ·⟩` differ only in their codomain presentation: both
are the composite of the *same* homomorphism `L : F(T) →* F(α)` (sending a generator of `T` to the
corresponding generator of `F(α)`) with the quotient map `F(α) →* F(α)/N`, which is the same map for
both presentations.  Since a group homomorphism is injective iff its kernel is trivial, injectivity
of `presentedGroupMap s T` transfers to `presentedGroupMap r T`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- Conjugate elements of a group generate the same normal closure. -/
theorem normalClosure_singleton_eq_of_isConj {r s : FreeGroup α} (h : IsConj s r) :
    Subgroup.normalClosure ({s} : Set (FreeGroup α)) =
      Subgroup.normalClosure ({r} : Set (FreeGroup α)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have h1 : r ∈ Subgroup.normalClosure ({s} : Set (FreeGroup α)) := by
    have hmem : c * s * c⁻¹ ∈ Subgroup.normalClosure ({s} : Set (FreeGroup α)) :=
      (Subgroup.normalClosure_normal (s := ({s} : Set (FreeGroup α)))).conj_mem s
        (Subgroup.subset_normalClosure (by simp)) c
    rwa [hc] at hmem
  have h2 : s ∈ Subgroup.normalClosure ({r} : Set (FreeGroup α)) := by
    have hmem : c⁻¹ * r * (c⁻¹)⁻¹ ∈ Subgroup.normalClosure ({r} : Set (FreeGroup α)) :=
      (Subgroup.normalClosure_normal (s := ({r} : Set (FreeGroup α)))).conj_mem r
        (Subgroup.subset_normalClosure (by simp)) c⁻¹
    have heq : c⁻¹ * r * (c⁻¹)⁻¹ = s := by rw [← hc]; group
    rwa [heq] at hmem
  exact le_antisymm
    (Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr h2))
    (Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr h1))

/-- The kernel of `presentedGroupMap u T` is the preimage under `L : F(T) →* F(α)` of the normal
closure of `{u}`.  Here `L` is the homomorphism sending each generator of `T` to the corresponding
generator of `F(α)`; it is the same homomorphism for every relator `u`. -/
theorem ker_presentedGroupMap {T : Set α} (u : FreeGroup α) :
    (presentedGroupMap u T).ker =
      (Subgroup.normalClosure ({u} : Set (FreeGroup α))).comap
        (FreeGroup.lift fun t : T => FreeGroup.of (t : α)) := by
  ext x
  simp only [MonoidHom.mem_ker, presentedGroupMap, MonoidHom.comp_apply,
    PresentedGroup.mk_eq_one_iff, Subgroup.mem_comap]

theorem injective_presentedGroupMap_of_isConj {α : Type u} {r s : FreeGroup α} (h : IsConj s r)
    {T : Set α} (hinj : Function.Injective (Work.OROneRel.presentedGroupMap s T)) :
    Function.Injective (Work.OROneRel.presentedGroupMap r T) := by
  rw [← MonoidHom.ker_eq_bot_iff] at hinj ⊢
  rw [ker_presentedGroupMap (T := T) r, ← normalClosure_singleton_eq_of_isConj h,
    ← ker_presentedGroupMap (T := T) s]
  exact hinj

end Work.OROneRel
