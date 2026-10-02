import Mathlib
import Submission.Work.LerayHirsch.LhTwoCoverDefs
import Submission.Work.Thom.localThom_union

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom Work.Cohomology
open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- The point of the punctured total space of `Z` corresponding to a point of that of `Z|_U`, read
through the two comparable definitions. -/
theorem punctComap_eq_comapZeroMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (U : Set B) (a : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U))))) :
    punctComap Z (subtypeMap U) a = (comapZeroMap Z U a).1 := rfl

/-- **The piece map is the canonical homeomorphism**: `pieceMap Z U` is a homeomorphism onto the
piece `π⁻¹U` of `P(E)`. -/
theorem isHomeomorph_pieceMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (U : Set B) :
    ∃ e : ProjSpace (bundleComap Z (subtypeMap U)) ≃ₜ ↥(projMap Z ⁻¹' U),
      ⇑e = ⇑(pieceMap Z U) := by
  let A : Set ↥(zeroComplement (realification Z)) := {x | x.1.proj ∈ U}
  let h : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))) ≃ₜ ↥A := punctHomeo Z U
  have hsmul : ∀ (c : ℂˣ) (x : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U))))),
      h (smulPunct (bundleComap Z (subtypeMap U)) c x) = ⟨smulPunct Z c (h x).1, (h x).2⟩ :=
    fun _ _ => rfl
  have hcoe : ∀ a : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))),
      (h a).1 = (comapZeroMap Z U a).1 := fun a => rfl
  let T : Set (ProjSpace Z) := projMap Z ⁻¹' U
  have hT : (mkProj Z) '' A = T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx⟩ := surjective_mkProj Z y
      refine ⟨x, ?_, hx⟩
      have h3 : (projMap Z) (mkProj Z x) ∈ U := by rw [hx]; exact hy
      exact h3
  let Φ : ↥A → ↥T := fun a => ⟨mkProj Z a.1, by rw [← hT]; exact Set.mem_image_of_mem (mkProj Z) a.2⟩
  have hΦq : Topology.IsQuotientMap Φ :=
    isQuotientMap_restrict_of_saturated (continuous_mkProj Z) (isOpenMap_mkProj Z) hT (by rfl)
  have hkey : ∀ a : ↥(zeroComplement (realification (bundleComap Z (subtypeMap U)))),
      pieceMap Z U (mkProj (bundleComap Z (subtypeMap U)) a) = Φ (h a) := by
    intro a
    apply Subtype.ext
    show projMapComap Z (subtypeMap U) (mkProj (bundleComap Z (subtypeMap U)) a) = mkProj Z (h a).1
    rw [projMapComap_mkProj_apply, punctComap_eq_comapZeroMap]
    exact (congrArg (mkProj Z) (hcoe a)).symm
  have hcomp : Topology.IsQuotientMap
      ((pieceMap Z U) ∘ (mkProj (bundleComap Z (subtypeMap U)))) := by
    rw [show ((pieceMap Z U) ∘ (mkProj (bundleComap Z (subtypeMap U))))
        = (Φ ∘ (h : _ → ↥A)) from funext hkey]
    exact hΦq.comp h.isQuotientMap
  have hinj : Function.Injective (pieceMap Z U) := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := surjective_mkProj (bundleComap Z (subtypeMap U)) p
    obtain ⟨b, rfl⟩ := surjective_mkProj (bundleComap Z (subtypeMap U)) q
    rw [hkey a, hkey b] at hpq
    have h1 : mkProj Z (h a).1 = mkProj Z (h b).1 := Subtype.ext_iff.mp hpq
    obtain ⟨c, hc⟩ := (mkProj_eq_iff Z).mp h1
    refine (mkProj_eq_iff _).mpr ⟨c, ?_⟩
    apply h.injective
    rw [hsmul c b]
    exact Subtype.ext hc
  have hsurj : Function.Surjective (pieceMap Z U) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := surjective_mkProj Z y
    have hxA : x ∈ A := by
      show (projMap Z) (mkProj Z x) ∈ U
      rw [hx]; exact hy
    refine ⟨mkProj (bundleComap Z (subtypeMap U)) (h.symm ⟨x, hxA⟩), ?_⟩
    rw [hkey (h.symm ⟨x, hxA⟩)]
    apply Subtype.ext
    show mkProj Z (h (h.symm ⟨x, hxA⟩)).1 = y
    rw [Homeomorph.apply_symm_apply]
    exact hx
  have hq : Topology.IsQuotientMap (pieceMap Z U) :=
    Topology.IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' hcomp
  exact ⟨(Equiv.ofBijective (pieceMap Z U) ⟨hinj, hsurj⟩).toHomeomorph
    (fun _ => hq.isCoinducing.isOpen_preimage), rfl⟩

/-- **The piece map induces an isomorphism on cohomology.** -/
theorem isIso_CohMap_pieceMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (U : Set B) (k : ℕ) :
    CategoryTheory.IsIso (CohMap (pieceMap Z U) ℤ k) := by
  obtain ⟨e, he⟩ := isHomeomorph_pieceMap Z U
  have hc : (e : C(ProjSpace (bundleComap Z (subtypeMap U)), ↥(projMap Z ⁻¹' U)))
      = pieceMap Z U := ContinuousMap.ext (fun x => congrFun he x)
  have hbij : Function.Bijective (CohMap (pieceMap Z U) ℤ k).hom := by
    rw [← hc]
    exact bijective_CohMap_homeomorph e k
  rw [isIso_iff_mono_and_epi, ModuleCat.mono_iff_injective, ModuleCat.epi_iff_surjective]
  exact hbij

end
end Work.LerayHirsch
