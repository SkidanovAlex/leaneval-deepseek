import Mathlib
import Submission.Commons.PeriodicTiling.isContinuousTiling_of_isTiling_lift
import Submission.Commons.PeriodicTiling.periodicTilingSet_lattice_period

open scoped Pointwise

namespace Commons.PeriodicTiling

/-- Given an additive commutative group `G`, we say that `F ⊆ G` forms an aperiodic
tiling equation if there exists `A ⊆ G` such that `F` tiles `G` with tiling set `A`,
but every such `A` is not periodic.  This is the definition used by the periodic tiling
conjecture; it is stated here in the commons so that the lemma below does not depend on
the problem-specific `ChallengeDeps` module. -/
structure IsAperiodicTilingEquation {G : Type*} [AddCommGroup G] (F : Set G) where
  solvable : ∃ A, IsTiling F A
  aperiodic : ∀ A, IsTiling F A → ¬ IsPeriodicTilingSet A

private lemma isTiling_map_addEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) {F A : Set G} (h : IsTiling F A) :
    IsTiling (e '' F) (e '' A) := by
  classical
  let φA : A ≃ e '' A := e.toEquiv.image A
  let φF : F ≃ e '' F := e.toEquiv.image F
  let φ : A × F ≃ (e '' A) × (e '' F) := φA.prodCongr φF
  have hcomm : (fun x : (e '' A) × (e '' F) => (x.1 : H) + (x.2 : H)) ∘ φ =
      e ∘ (fun x : A × F => (x.1 : G) + (x.2 : G)) := by
    funext x
    rcases x with ⟨a, f⟩
    simp [φ, φA, φF, Equiv.prodCongr_apply, Equiv.image]
  have hbi : Function.Bijective (fun x : A × F => (x.1 : G) + (x.2 : G)) := by
    simpa [IsTiling, AddSubgroup.IsComplement] using h
  have hcomp : Function.Bijective ((fun x : (e '' A) × (e '' F) => (x.1 : H) + (x.2 : H)) ∘ φ) := by
    simpa [hcomm] using e.bijective.comp hbi
  have hfinal : Function.Bijective (fun x : (e '' A) × (e '' F) => (x.1 : H) + (x.2 : H)) := by
    have hcomp' := hcomp.comp φ.symm.bijective
    convert hcomp' using 1
    funext y
    simp [φ]
  simpa [IsTiling, AddSubgroup.IsComplement] using hfinal

private lemma isPeriodicTilingSet_map_addEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) {A : Set G} (h : IsPeriodicTilingSet A) :
    IsPeriodicTilingSet (e '' A) := by
  classical
  rcases h with ⟨L, hLfin, s, rfl⟩
  let L' : AddSubgroup H := L.map e.toAddMonoidHom
  have hL'fin : L'.FiniteIndex := by
    have hrel : L.relIndex ⊤ ≠ 0 := by
      rw [AddSubgroup.relIndex_top_right]
      exact hLfin.index_ne_zero
    have hc := AddSubgroup.relIndex_comap_ne_zero (G := H) (G' := G)
      (f := e.symm.toAddMonoidHom) (J := L) (K := ⊤) hrel
    have hL'eq : L' = L.comap e.symm.toAddMonoidHom := by
      ext x
      simp [L', AddSubgroup.mem_map, AddSubgroup.mem_comap]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        refine ⟨e.symm x, hx, ?_⟩
        simp
    exact ⟨by simpa [hL'eq, AddSubgroup.relIndex_top_right] using hc⟩
  refine ⟨L', hL'fin, s.image e, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_add] at hx
    rcases hx with ⟨a, ha, b, hb, hx⟩
    rw [Set.mem_add]
    refine ⟨e a, ?_, e b, ?_, ?_⟩
    · rw [Finset.mem_coe]
      exact Finset.mem_image.mpr ⟨a, by simpa [Finset.mem_coe] using ha, rfl⟩
    · exact AddSubgroup.mem_map.mpr ⟨b, by simpa using hb, rfl⟩
    · simpa [← map_add] using congrArg e hx
  · intro hy
    rw [Set.mem_add] at hy
    rcases hy with ⟨a, ha, b, hb, hy⟩
    rw [Finset.mem_coe, Finset.mem_image] at ha
    rcases ha with ⟨a0, ha0, rfl⟩
    rcases AddSubgroup.mem_map.mp hb with ⟨b0, hb0, rfl⟩
    rw [Set.mem_image]
    refine ⟨a0 + b0, ?_, by simpa [map_add] using hy⟩
    rw [Set.mem_add]
    exact ⟨a0, by simpa [Finset.mem_coe] using ha0, b0, by simpa using hb0, rfl⟩

theorem IsAperiodicTilingEquation_map_addEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    {F : Set G} (hF : IsAperiodicTilingEquation F) :
    IsAperiodicTilingEquation (e '' F) := by
  classical
  refine ⟨?_, ?_⟩
  · rcases hF.solvable with ⟨A, hA⟩
    exact ⟨e '' A, isTiling_map_addEquiv e hA⟩
  · intro B hB hBper
    let A : Set G := e.symm '' B
    have hA_tile : IsTiling F A := by
      have htmp := isTiling_map_addEquiv (e := e.symm) (F := e '' F) (A := B) hB
      have hpre : e.symm '' (e '' F) = F := by
        ext x
        simp [e.symm_apply_apply]
      simpa [A, hpre] using htmp
    have hA_per : IsPeriodicTilingSet A := isPeriodicTilingSet_map_addEquiv (e := e.symm) hBper
    exact hF.aperiodic A hA_tile hA_per

end Commons.PeriodicTiling
