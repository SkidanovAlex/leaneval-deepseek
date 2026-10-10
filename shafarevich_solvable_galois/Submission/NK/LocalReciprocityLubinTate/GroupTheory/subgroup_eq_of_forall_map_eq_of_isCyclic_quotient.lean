import Mathlib.GroupTheory.FiniteAbelian.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.GroupTheory

/-- Given a finite abelian group `G`, a subgroup `A` and an element `g ∉ A`, there is a
subgroup `H` containing `A` such that `G ⧸ H` is cyclic and `g ∉ H`. -/
lemma exists_isCyclic_quotient_not_mem {G : Type*} [CommGroup G] [Finite G]
    (A : Subgroup G) {g : G} (hg : g ∉ A) :
    ∃ H : Subgroup G, A ≤ H ∧ IsCyclic (G ⧸ H) ∧ g ∉ H := by
  classical
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite (G ⧸ A)
  have hb : e (QuotientGroup.mk' A g) ≠ 1 := by
    intro h1
    have h2 : e (QuotientGroup.mk' A g) = e 1 := by rw [h1, map_one]
    have h3 : (QuotientGroup.mk' A g) = 1 := e.injective h2
    exact hg ((QuotientGroup.eq_one_iff (N := A) g).mp h3)
  obtain ⟨i, hi⟩ : ∃ i, e (QuotientGroup.mk' A g) i ≠ 1 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    exact hb (funext hcon)
  let proj : ((i : ι) → Multiplicative (ZMod (n i))) →* Multiplicative (ZMod (n i)) :=
    Pi.evalMonoidHom _ i
  let ψ : G ⧸ A →* Multiplicative (ZMod (n i)) := proj.comp e.toMonoidHom
  let φ : G →* Multiplicative (ZMod (n i)) := ψ.comp (QuotientGroup.mk' A)
  have hφ : ∀ x : G, φ x = e (QuotientGroup.mk' A x) i := fun _ => rfl
  refine ⟨φ.ker, ?_, ?_, ?_⟩
  · intro a ha
    rw [MonoidHom.mem_ker, hφ a]
    rw [show (QuotientGroup.mk' A) a = 1 from (QuotientGroup.eq_one_iff (N := A) a).mpr ha]
    simp
  · exact ((QuotientGroup.quotientKerEquivRange φ).isCyclic).mpr (Subgroup.isCyclic φ.range)
  · intro hmem
    rw [MonoidHom.mem_ker] at hmem
    rw [hφ g] at hmem
    exact hi hmem

/-- A subgroup of a finite abelian group is determined by its images in all cyclic
quotients. -/
theorem subgroup_eq_of_forall_map_eq_of_isCyclic_quotient {G : Type*} [CommGroup G] [Finite G]
    (A B : Subgroup G)
    (h : ∀ H : Subgroup G, IsCyclic (G ⧸ H) →
      Subgroup.map (QuotientGroup.mk' H) A = Subgroup.map (QuotientGroup.mk' H) B) :
    A = B := by
  refine le_antisymm ?_ ?_
  · intro g hgA
    by_contra hgB
    obtain ⟨H, hBH, hHcyc, hgH⟩ := exists_isCyclic_quotient_not_mem B hgB
    have hmap := h H hHcyc
    have hbot : Subgroup.map (QuotientGroup.mk' H) B = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk' H]
      exact hBH
    have hmem : QuotientGroup.mk' H g ∈ Subgroup.map (QuotientGroup.mk' H) A := ⟨g, hgA, rfl⟩
    rw [hmap, hbot] at hmem
    exact hgH ((QuotientGroup.eq_one_iff (N := H) g).mp (Subgroup.mem_bot.mp hmem))
  · intro g hgB
    by_contra hgA
    obtain ⟨H, hAH, hHcyc, hgH⟩ := exists_isCyclic_quotient_not_mem A hgA
    have hmap := h H hHcyc
    have hbot : Subgroup.map (QuotientGroup.mk' H) A = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk' H]
      exact hAH
    have hmem : QuotientGroup.mk' H g ∈ Subgroup.map (QuotientGroup.mk' H) B := ⟨g, hgB, rfl⟩
    rw [← hmap, hbot] at hmem
    exact hgH ((QuotientGroup.eq_one_iff (N := H) g).mp (Subgroup.mem_bot.mp hmem))

end NK.LocalReciprocityLubinTate.GroupTheory
