import Mathlib
import Submission.Work.Thom.thomClass_of_cover_gen
import Submission.Work.Thom.Glue2

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **Every locally compatible family of local Thom data is the restriction of a global Thom
class.**  If `Z` is a rank-`n` real bundle (`n ≥ 1`), `U, V ⊆ B` an open cover, and `LocalThom`
data over `U`, over `V` and over the overlap `U ∩ V` are compatible under restriction to the
overlap, and the overlap's `(n-1)`-st relative cohomology vanishes, then `Z` carries a Thom class.

The proof glues the two piece-classes into a global class `τ` with the middle exactness of the
honest relative Mayer–Vietoris sequence (`Work.Thom.exists_glue`) and concludes that `τ` is a Thom
class with the five-lemma rung of `Work.Thom.thomClass_of_cover_gen`. -/
theorem nonempty_thomClass_of_compatible_local {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (hn : 1 ≤ n) {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hUloc : Work.Thom.LocalThom Z n U)
    (hVloc : Work.Thom.LocalThom Z n V) (hUVloc : Work.Thom.LocalThom Z n (U ∩ V))
    (hUVU : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' (U ∩ V)) (Set.preimage_mono Set.inter_subset_left) n).hom
        hUloc.τ = hUVloc.τ)
    (hUVV : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' V) (Z.proj ⁻¹' (U ∩ V)) (Set.preimage_mono Set.inter_subset_right) n).hom
        hVloc.τ = hUVloc.τ)
    (hlow : Subsingleton (Work.Thom.PieceCoh Z (U ∩ V) (n - 1))) :
    Nonempty (Work.Thom.ThomClass Z n) := by
  have hUVU' : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' U) (Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) Set.inter_subset_left n).hom
      hUloc.τ = hUVloc.τ := hUVU
  have hUVV' : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' V) (Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) Set.inter_subset_right n).hom
      hVloc.τ = hUVloc.τ := hUVV
  have hfst_inl : ∀ c : PieceCoh Z U n,
      (ModuleCat.Hom.hom (biprod.fst : PieceCoh Z U n ⊞ PieceCoh Z V n ⟶ PieceCoh Z U n))
        ((ModuleCat.Hom.hom (biprod.inl : PieceCoh Z U n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n)) c)
        = c := by
    intro c
    have h := congrArg ModuleCat.Hom.hom
      (biprod.inl_fst (X := PieceCoh Z U n) (Y := PieceCoh Z V n))
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h c
  have hfst_inr : ∀ c : PieceCoh Z V n,
      (ModuleCat.Hom.hom (biprod.fst : PieceCoh Z U n ⊞ PieceCoh Z V n ⟶ PieceCoh Z U n))
        ((ModuleCat.Hom.hom (biprod.inr : PieceCoh Z V n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n)) c)
        = 0 := by
    intro c
    have h := congrArg ModuleCat.Hom.hom
      (biprod.inr_fst (X := PieceCoh Z U n) (Y := PieceCoh Z V n))
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h c
  have hsnd_inl : ∀ c : PieceCoh Z U n,
      (ModuleCat.Hom.hom (biprod.snd : PieceCoh Z U n ⊞ PieceCoh Z V n ⟶ PieceCoh Z V n))
        ((ModuleCat.Hom.hom (biprod.inl : PieceCoh Z U n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n)) c)
        = 0 := by
    intro c
    have h := congrArg ModuleCat.Hom.hom
      (biprod.inl_snd (X := PieceCoh Z U n) (Y := PieceCoh Z V n))
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h c
  have hsnd_inr : ∀ c : PieceCoh Z V n,
      (ModuleCat.Hom.hom (biprod.snd : PieceCoh Z U n ⊞ PieceCoh Z V n ⟶ PieceCoh Z V n))
        ((ModuleCat.Hom.hom (biprod.inr : PieceCoh Z V n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n)) c)
        = c := by
    intro c
    have h := congrArg ModuleCat.Hom.hom
      (biprod.inr_snd (X := PieceCoh Z U n) (Y := PieceCoh Z V n))
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h c
  -- the two piece classes are compatible on the overlap
  have hw : (ModuleCat.Hom.hom (Work.Cohomology.honestG (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n))
      ((ModuleCat.Hom.hom (biprod.inl : PieceCoh Z U n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n)) hUloc.τ
        + (ModuleCat.Hom.hom (biprod.inr : PieceCoh Z V n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n))
            hVloc.τ)
      = 0 := by
    have hi1 : (ModuleCat.Hom.hom (Work.Cohomology.honestG (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n))
        ((ModuleCat.Hom.hom (biprod.inl : PieceCoh Z U n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n))
          hUloc.τ)
        = hUVloc.τ := by
      have hcomp := congrArg ModuleCat.Hom.hom
        (Work.Cohomology.honestG_inl' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)
      rw [ModuleCat.hom_comp] at hcomp
      exact (LinearMap.congr_fun hcomp hUloc.τ).trans hUVU'
    have hi2 : (ModuleCat.Hom.hom (Work.Cohomology.honestG (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n))
        ((ModuleCat.Hom.hom (biprod.inr : PieceCoh Z V n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n))
          hVloc.τ)
        = - hUVloc.τ := by
      have hcomp := congrArg ModuleCat.Hom.hom
        (Work.Cohomology.honestG_inr' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_neg] at hcomp
      have h2 := LinearMap.congr_fun hcomp hVloc.τ
      rw [LinearMap.neg_apply] at h2
      exact h2.trans (congrArg Neg.neg hUVV')
    rw [map_add, hi1, hi2, add_neg_cancel]
  obtain ⟨τ, hτ⟩ := Work.Thom.exists_glue Z n hU hV hcov _ hw
  have hUτ : hUloc.τ = (PieceRes Z U n) τ := by
    have hcomp := congrArg ModuleCat.Hom.hom
      (Work.Cohomology.honestF_fst' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)
    rw [ModuleCat.hom_comp] at hcomp
    have h2 := LinearMap.congr_fun hcomp τ
    rw [LinearMap.comp_apply, hτ] at h2
    have hL : (ModuleCat.Hom.hom (biprod.fst : PieceCoh Z U n ⊞ PieceCoh Z V n ⟶ PieceCoh Z U n))
        ((ModuleCat.Hom.hom (biprod.inl : PieceCoh Z U n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n))
            hUloc.τ
          + (ModuleCat.Hom.hom (biprod.inr : PieceCoh Z V n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n))
            hVloc.τ)
        = hUloc.τ := by
      rw [map_add, hfst_inl, hfst_inr, add_zero]
    rw [hL] at h2
    exact h2
  have hVτ : hVloc.τ = (PieceRes Z V n) τ := by
    have hcomp := congrArg ModuleCat.Hom.hom
      (Work.Cohomology.honestF_snd' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)
    rw [ModuleCat.hom_comp] at hcomp
    have h2 := LinearMap.congr_fun hcomp τ
    rw [LinearMap.comp_apply, hτ] at h2
    have hL : (ModuleCat.Hom.hom (biprod.snd : PieceCoh Z U n ⊞ PieceCoh Z V n ⟶ PieceCoh Z V n))
        ((ModuleCat.Hom.hom (biprod.inl : PieceCoh Z U n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n))
            hUloc.τ
          + (ModuleCat.Hom.hom (biprod.inr : PieceCoh Z V n ⟶ PieceCoh Z U n ⊞ PieceCoh Z V n))
            hVloc.τ)
        = hVloc.τ := by
      rw [map_add, hsnd_inl, hsnd_inr, zero_add]
    rw [hL] at h2
    exact h2
  have hUVτ : hUVloc.τ = (PieceRes Z (U ∩ V) n) τ := by
    have h1 := Work.Thom.PieceRes_eq_pdCohMap Z n (Set.inter_subset_left : U ∩ V ⊆ U) τ
    rw [h1, ← hUτ]
    exact hUVU.symm
  exact ⟨⟨τ, Work.Thom.thomClass_of_cover_gen Z n hn hU hV hcov τ hUloc hVloc hUVloc
    hUτ hVτ hUVτ hlow⟩⟩

end

end Work.Thom
