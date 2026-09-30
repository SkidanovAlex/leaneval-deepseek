import Mathlib
import Submission.Work.Thom.thomClass_of_cover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open Work.TangentClasses
open Work.Cohomology

namespace Work.Thom

open Bundle CategoryTheory CategoryTheory.Limits

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

theorem thomClass_of_cover_gen {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (τ : Work.Thom.OpenThom Z n)
    (hUloc : Work.Thom.LocalThom Z n U) (hVloc : Work.Thom.LocalThom Z n V)
    (hUVloc : Work.Thom.LocalThom Z n (U ∩ V))
    (hUτ : hUloc.τ = (Work.Thom.PieceRes Z U n) τ)
    (hVτ : hVloc.τ = (Work.Thom.PieceRes Z V n) τ)
    (hUVτ : hUVloc.τ = (Work.Thom.PieceRes Z (U ∩ V) n) τ)
    (hlow : Subsingleton (Work.Thom.PieceCoh Z (U ∩ V) (n - 1))) :
    ∀ k : ℕ, Function.Bijective (Work.Thom.thomMap Z n τ k) := by
  have hcov' : Z.proj ⁻¹' U ∪ Z.proj ⁻¹' V = Set.univ := preimage_union_univ Z hcov
  have hmain := five_lemma_LES'
    (M₁ := fun k => pdCoh (TopCat.of B) (∅ : Set B) k)
    (P₁ := fun k => pdCohBiprod (TopCat.of B) (∅ : Set B) U V k)
    (Q₁ := fun k => pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) k)
    (M₂ := fun k => Work.Thom.OpenThom Z (k + n))
    (P₂ := fun k => pdCohBiprod (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (k + n))
    (Q₂ := fun k => pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) (k + n))
    (F₁ := fun k => honestF (TopCat.of B) (∅ : Set B) U V k)
    (G₁ := fun k => honestG (TopCat.of B) (∅ : Set B) U V k)
    (δ₁ := fun k => honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov k)
    (F₂ := fun k => honestF (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (k + n))
    (G₂ := fun k => honestG (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (k + n))
    (δ₂ := fun k => honestDelta (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
        (hV.preimage Z.continuous_proj) hcov' (k + n)
        ≫ eqToHom (congrArg (fun m => pdCoh (TopCat.of Z.TotalSpace) (zeroComplement Z) m)
            (by omega : k + n + 1 = (k + 1) + n)))
    (e₂₁ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₂ (TopCat.of B) (∅ : Set B) U V hU hV hcov k))
    (e₃₁ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₃ (TopCat.of B) (∅ : Set B) U V hU hV hcov k))
    (e₁₁ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₁ (TopCat.of B) (∅ : Set B) U V hU hV hcov k))
    (e₂₂ := fun k => ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₂ (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
          (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj) (hV.preimage Z.continuous_proj) hcov' (k + n)))
    (e₃₂ := fun k => by
      rw [ker_comp_iso]
      exact ShortComplex.Exact.moduleCat_range_eq_ker
        (honest_exact₃ (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
          (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj) (hV.preimage Z.continuous_proj) hcov' (k + n)))
    (e₁₂ := fun k => by
      have hr : LinearMap.range (ModuleCat.Hom.hom (honestDelta (TopCat.of Z.TotalSpace)
            (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
            (hV.preimage Z.continuous_proj) hcov' (k + n)))
          = LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z)
              (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((k + n) + 1))) :=
        ShortComplex.Exact.moduleCat_range_eq_ker
          (honest_exact₁ (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
            (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj) (hV.preimage Z.continuous_proj) hcov' (k + n))
      rw [ModuleCat.hom_comp, LinearMap.range_comp, hr]
      exact map_ker_eq_ker
        (congrArg (fun m => pdCoh (TopCat.of Z.TotalSpace) (zeroComplement Z) m)
          (by omega : (k + n) + 1 = (k + 1) + n))
        (congrArg (fun m => pdCohBiprod (TopCat.of Z.TotalSpace) (zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) m) (by omega : (k + n) + 1 = (k + 1) + n))
        (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((k + n) + 1))
        (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((k + 1) + n))
        (eqToHom_honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V)
          (by omega : (k + n) + 1 = (k + 1) + n)))
    (TM := fun k => (pdCohIso B k).hom ≫ ModuleCat.ofHom (thomMap Z n τ k))
    (TP := fun k => biprod.map
        ((pdCohIso ↥U k).hom ≫ ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k))
        ((pdCohIso ↥V k).hom ≫ ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)))
    (TQ := fun k => (pdCohIso ↥(U ∩ V) k).hom
        ≫ ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k))
    (f₁ := by
      haveI : Mono (hmvF (TopCat.of B) (∅ : Set B) U V) :=
        (hmv_shortExact (TopCat.of B) (∅ : Set B) U V).mono_f
      haveI : Mono (HomologicalComplex.homologyMap
          (hmvF (TopCat.of B) (∅ : Set B) U V) 0) := mono_homologyMap_f_zero _
      have heq : honestF (TopCat.of B) (∅ : Set B) U V 0
          = (cmpXIso (TopCat.of B) (∅ : Set B) U V hU hV hcov 0).hom
            ≫ HomologicalComplex.homologyMap (hmvF (TopCat.of B) (∅ : Set B) U V) 0
            ≫ (hmvMidIso (TopCat.of B) (∅ : Set B) U V 0).hom := by
        have hs := honestSq₁ (TopCat.of B) (∅ : Set B) U V 0
        have h := congrArg (fun m => m ≫ (hmvMidIso (TopCat.of B) (∅ : Set B) U V 0).hom) hs
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
        rw [← cmpXIso_hom] at h
        exact h.symm
      have hmono : Mono (honestF (TopCat.of B) (∅ : Set B) U V 0) := by
        rw [heq]
        infer_instance
      rw [LinearMap.ker_eq_bot]
      exact (ModuleCat.mono_iff_injective _).mp hmono)
    (f₂ := by
      have hker_n : LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace)
          (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)) = ⊥ := by
        have hr : LinearMap.range (ModuleCat.Hom.hom (honestDelta (TopCat.of Z.TotalSpace)
              (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
              (hV.preimage Z.continuous_proj) hcov' (n - 1)))
            = LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace)
                (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((n - 1) + 1))) :=
          ShortComplex.Exact.moduleCat_range_eq_ker
            (honest_exact₁ (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U)
              (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj) (hV.preimage Z.continuous_proj) hcov' (n - 1))
        haveI : Subsingleton (pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) (n - 1)) := hlow
        have hbot : (LinearMap.range (ModuleCat.Hom.hom (honestDelta (TopCat.of Z.TotalSpace)
            (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
            (hV.preimage Z.continuous_proj) hcov' (n - 1)))) = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro y hy
          obtain ⟨x, rfl⟩ := hy
          rw [show x = 0 from Subsingleton.elim x 0, map_zero]
        have hk : LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace)
            (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) ((n - 1) + 1))) = ⊥ := by
          rw [← hr, hbot]
        rwa [show (n - 1) + 1 = n from Nat.sub_add_cancel hn] at hk
      have hker0 : LinearMap.ker (ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace)
          (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (0 + n))) = ⊥ := by
        refine eq_bot_of_map_eq_bot
          (congrArg (fun m => pdCoh (TopCat.of Z.TotalSpace) (zeroComplement Z) m) (Nat.zero_add n)) _ ?_
        rw [map_ker_eq_ker
          (congrArg (fun m => pdCoh (TopCat.of Z.TotalSpace) (zeroComplement Z) m) (Nat.zero_add n))
          (congrArg (fun m => pdCohBiprod (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) m) (Nat.zero_add n))
          (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (0 + n))
          (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)
          (eqToHom_honestF (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V)
            (Nat.zero_add n)),
          hker_n]
      intro u hu
      have hu0 : u = 0 := by
        have hz := (Submodule.eq_bot_iff (LinearMap.ker (ModuleCat.Hom.hom (honestF
          (TopCat.of Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (0 + n))))).mp hker0
        exact hz u (by
          show ModuleCat.Hom.hom (honestF (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (0 + n)) u = 0
          exact hu)
      exact ⟨0, by rw [map_zero, hu0]⟩)
    (hF := ladder_F_square Z n hU hV hcov τ)
    (hG := ladder_G_square Z n hU hV hcov τ)
    (hδ := ladder_delta_square Z n hU hV hcov τ)
    (hP := by
      intro k
      have hbU : Function.Bijective (localThomMap Z n U (PieceRes Z U n τ) k) := by
        rw [← hUτ]; exact hUloc.isThom k
      have hbV : Function.Bijective (localThomMap Z n V (PieceRes Z V n τ) k) := by
        rw [← hVτ]; exact hVloc.isThom k
      haveI : IsIso (ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)) := by
        rw [isIso_iff_mono_and_epi]
        exact ⟨(ModuleCat.mono_iff_injective _).mpr hbU.1,
          (ModuleCat.epi_iff_surjective _).mpr hbU.2⟩
      haveI : IsIso (ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)) := by
        rw [isIso_iff_mono_and_epi]
        exact ⟨(ModuleCat.mono_iff_injective _).mpr hbV.1,
          (ModuleCat.epi_iff_surjective _).mpr hbV.2⟩
      haveI hiU : IsIso ((pdCohIso ↥U k).hom
          ≫ ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)) :=
        ((pdCohIso ↥U k).trans
          (asIso (ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)))).isIso_hom
      haveI hiV : IsIso ((pdCohIso ↥V k).hom
          ≫ ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)) :=
        ((pdCohIso ↥V k).trans
          (asIso (ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)))).isIso_hom
      exact (biprod.mapIso
        (asIso ((pdCohIso ↥U k).hom ≫ ModuleCat.ofHom (localThomMap Z n U (PieceRes Z U n τ) k)))
        (asIso ((pdCohIso ↥V k).hom ≫ ModuleCat.ofHom (localThomMap Z n V (PieceRes Z V n τ) k)))).isIso_hom)
    (hQ := by
      intro k
      have hbUV : Function.Bijective (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k) := by
        rw [← hUVτ]; exact hUVloc.isThom k
      haveI : IsIso (ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k)) := by
        rw [isIso_iff_mono_and_epi]
        exact ⟨(ModuleCat.mono_iff_injective _).mpr hbUV.1,
          (ModuleCat.epi_iff_surjective _).mpr hbUV.2⟩
      haveI : IsIso ((pdCohIso ↥(U ∩ V) k).hom
          ≫ ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k)) :=
        ((pdCohIso ↥(U ∩ V) k).trans
          (asIso (ModuleCat.ofHom (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k)))).isIso_hom
      exact ‹_›)
  intro k
  haveI hk := hmain k
  haveI hthom : IsIso (ModuleCat.ofHom (thomMap Z n τ k)) :=
    IsIso.of_isIso_comp_left (pdCohIso B k).hom (ModuleCat.ofHom (thomMap Z n τ k))
  rw [isIso_iff_mono_and_epi] at hthom
  exact ⟨(ModuleCat.mono_iff_injective _).mp hthom.1,
    (ModuleCat.epi_iff_surjective _).mp hthom.2⟩

end

end Work.Thom
