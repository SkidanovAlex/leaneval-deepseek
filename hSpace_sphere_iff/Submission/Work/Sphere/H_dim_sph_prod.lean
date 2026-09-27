/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The dimension of the middle cohomology of `Sⁿ × Sⁿ`

The rational cohomology of `Sⁿ × Sⁿ` in degree `n ≥ 2` is two-dimensional, spanned by the
pullbacks of a generator of `H^n(S^n; ℚ)` along the two projections.  Equivalently, the two
pullback maps

`H^n(Sⁿ; ℚ) ⟶ H^n(Sⁿ × Sⁿ; ℚ)`,

induced by the first and the second projection, have images whose sum is everything.

This is the "diagonal" case of the Künneth computation for a product of spheres, and it is the
dimension input in the even-dimensional part of Adams' theorem: an H-space multiplication `μ` on
`Sⁿ` gives `μ^*(x) = x ⊗ 1 + 1 ⊗ x`, so that `x` must lie in the sum of the two images.

The argument is the Mayer–Vietoris analysis of the cover of `S^{a+1} × S^{a+1}` pulled back from
the two caps of the first factor (`Work.Sphere.ProdSetup`): the two pieces are homotopy equivalent
to `S^{a+1}`, and their intersection to `S^a × S^{a+1}`.  In degree `a` the connecting map
`H^a(S^a × S^{a+1}; ℚ) → H^{a+1}(small)` is injective (`H^a` of the pieces vanishes), so the
kernel of the restriction `mvAlphaH` is the line spanned by the image of a generator; in degree
`a+1` the class `pr₂^*z` restricts nontrivially to the first piece (a *slice* `y ↦ (c,y)` with
`c` in the cap gives a left inverse of the restriction) and to the intersection of the two pieces
(a slice into the intersection), so `mvBetaH` is nonzero with nonzero kernel, hence has a
one-dimensional kernel; a dimension count then identifies
`H^{a+1}(S^{a+1} × S^{a+1}; ℚ) ≅ ker (mvBetaH) × ker (mvAlphaH) ≅ ℚ × ℚ`.
-/
import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Sphere.Suspension
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.H_prod_sph
import Submission.Work.Cohomology.mvAlphaH_ker_eq_range
import Submission.Work.Cohomology.mvBetaH_ker_eq_range
import Submission.Work.Cohomology.mvConnecting_ker_eq_range
import Submission.Work.Cohomology.mvConnecting_surjective
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.H1_prod_sph_circle
import Submission.Work.Sphere.PH_low_mid
import Submission.Work.Sphere.H_iso_capPlus_prod
import Submission.Work.Sphere.contractibleSpace_sph_compl
import Submission.Work.Cohomology.H_map_homotopic
import Submission.Work.Cohomology.exists_chain_eval_ne_zero
import Submission.Work.Cohomology.Pairing
import Submission.Work.Cohomology.mvConnecting_injective
import Submission.Work.Cohomology.H_cup_cross_ne_zero
import Submission.Work.Cohomology.H_cup_comm
import Submission.Work.Cohomology.H_cupOf_mk
import Submission.Work.Cohomology.H_cupOf_add_left
import Submission.Work.Cohomology.H_cupOf_add_right
import Submission.Work.Cohomology.H_cupOf_smul_left
import Submission.Work.Cohomology.H_cupOf_smul_right
import Submission.Work.Cohomology.H_map_cupOf
import Submission.Work.Cohomology.H_map_comp
import Submission.Work.Cohomology.SingIn

open CategoryTheory Simplicial Opposite
open scoped CategoryTheory.MonoidalCategory

namespace Work.Sphere

open Submission.Cohomology Submission.Sphere

noncomputable section

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-! ## Slice maps of a product

For a point `c ∈ W ⊆ X` the slice `y ↦ (c, y)` gives a map `Sing Y ⟶ fstSub X Y W` which is a
section of the second projection.  These are the maps used to show that the restriction of the
class `pr₂^*z` to the pieces of a Mayer–Vietoris cover of `X × Y` is nonzero, and hence that the
Mayer–Vietoris map `mvBetaH` is nonzero. -/

namespace HdimProd


noncomputable section
variable {X Y : TopCat.{0}}

def sndMor (X Y : TopCat.{0}) : TopProd X Y ⟶ Y :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

def sliceMor (X Y : TopCat.{0}) (c : ↥X) : Y ⟶ TopProd X Y :=
  TopCat.ofHom ⟨fun y => (c, y), continuous_const.prodMk continuous_id⟩

lemma sliceMor_snd (X Y : TopCat.{0}) (c : ↥X) : sliceMor X Y c ≫ sndMor X Y = 𝟙 Y := by
  apply TopCat.hom_ext
  ext y
  rfl

lemma subcomplex_iota_mem {S : SSet.{0}} (A : S.Subcomplex) {n : SimplexCategoryᵒᵖ}
    (y : A.toSSet.obj n) : A.ι.app n y ∈ A.obj n := y.2

lemma slice_val {X Y : TopCat.{0}} (c : ↥X) (n : SimplexCategoryᵒᵖ)
    (τ : (TopCat.toSSet.obj Y).obj n) (t : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    TopCat.toSSetObjEquivT (TopProd X Y) n ((TopCat.toSSet.map (sliceMor X Y c)).app n τ) t
      = (c, (TopCat.toSSetObjEquivT Y n τ) t) := rfl

/-- The slice into a subcomplex of the form `fstSub X Y W`. -/
theorem exists_slice_fstSub (W : Set ↥X) (c : ↥X) (hc : c ∈ W) :
    ∃ ψ : TopCat.toSSet.obj Y ⟶ (fstSub X Y W).toSSet,
      ψ ≫ ((fstSub X Y W).ι ≫ TopCat.toSSet.map (sndMor X Y)) = 𝟙 (TopCat.toSSet.obj Y) := by
  have h₁ : SSet.Subcomplex.range (TopCat.toSSet.map (sliceMor X Y c)) ≤ fstSub X Y W := by
    intro n σ hσ
    rw [CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hσ
    obtain ⟨τ, rfl⟩ := hσ
    rw [mem_singIn_iff]
    intro t
    show (TopCat.toSSetObjEquivT (TopProd X Y) n
      ((TopCat.toSSet.map (sliceMor X Y c)).app n τ) t).1 ∈ W
    rw [slice_val]
    exact hc
  refine ⟨SSet.Subcomplex.lift (TopCat.toSSet.map (sliceMor X Y c)) h₁, ?_⟩
  rw [← Category.assoc, SSet.Subcomplex.lift_ι]
  have h2 : TopCat.toSSet.map (sliceMor X Y c ≫ sndMor X Y) = 𝟙 (TopCat.toSSet.obj Y) := by
    rw [sliceMor_snd]
    exact CategoryTheory.Functor.map_id _ _
  rw [← h2, CategoryTheory.Functor.map_comp]

/-- The slice into the intersection `fstSub X Y W₁ ⊓ fstSub X Y W₂`. -/
theorem exists_slice_inf (W₁ W₂ : Set ↥X) (c : ↥X) (hc : c ∈ W₁ ∩ W₂) :
    ∃ ψ : TopCat.toSSet.obj Y ⟶ (fstSub X Y W₁ ⊓ fstSub X Y W₂).toSSet,
      ψ ≫ ((fstSub X Y W₁ ⊓ fstSub X Y W₂).ι ≫ TopCat.toSSet.map (sndMor X Y))
        = 𝟙 (TopCat.toSSet.obj Y) := by
  have h₁ : SSet.Subcomplex.range (TopCat.toSSet.map (sliceMor X Y c)) ≤
      fstSub X Y W₁ ⊓ fstSub X Y W₂ := by
    intro n σ hσ
    rw [CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hσ
    obtain ⟨τ, rfl⟩ := hσ
    refine ⟨?_, ?_⟩ <;> rw [mem_singIn_iff] <;> intro t
    · show (TopCat.toSSetObjEquivT (TopProd X Y) n
        ((TopCat.toSSet.map (sliceMor X Y c)).app n τ) t).1 ∈ W₁
      rw [slice_val]
      exact hc.1
    · show (TopCat.toSSetObjEquivT (TopProd X Y) n
        ((TopCat.toSSet.map (sliceMor X Y c)).app n τ) t).1 ∈ W₂
      rw [slice_val]
      exact hc.2
  refine ⟨SSet.Subcomplex.lift (TopCat.toSSet.map (sliceMor X Y c)) h₁, ?_⟩
  rw [← Category.assoc, SSet.Subcomplex.lift_ι]
  have h2 : TopCat.toSSet.map (sliceMor X Y c ≫ sndMor X Y) = 𝟙 (TopCat.toSSet.obj Y) := by
    rw [sliceMor_snd]
    exact CategoryTheory.Functor.map_id _ _
  rw [← h2, CategoryTheory.Functor.map_comp]


/-- The slice into the first piece of the two-piece cover. -/
theorem exists_slice_fstAsub (W₁ W₂ : Set ↥X) (c : ↥X) (hc : c ∈ W₁) :
    ∃ ψ : TopCat.toSSet.obj Y ⟶ (fstAsub X Y W₁ W₂).toSSet,
      ψ ≫ ((fstAsub X Y W₁ W₂).ι ≫ (fstSmall X Y W₁ W₂).ι
        ≫ TopCat.toSSet.map (sndMor X Y)) = 𝟙 (TopCat.toSSet.obj Y) := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_slice_fstSub (X := X) (Y := Y) W₁ c hc
  set g : TopCat.toSSet.obj Y ⟶ (fstSmall X Y W₁ W₂).toSSet :=
    ψ₀ ≫ SSet.Subcomplex.homOfLE (le_sup_left : fstSub X Y W₁ ≤ fstSmall X Y W₁ W₂) with hg
  have h₂ : SSet.Subcomplex.range g ≤ fstAsub X Y W₁ W₂ := by
    intro n σ hσ
    rw [CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hσ
    obtain ⟨τ, rfl⟩ := hσ
    rw [SSet.Subcomplex.preimage_obj]
    show ((fstSmall X Y W₁ W₂).ι).app n (g.app n τ) ∈ (fstSub X Y W₁).obj n
    have hgg : g.app n τ = (SSet.Subcomplex.homOfLE
        (le_sup_left : fstSub X Y W₁ ≤ fstSmall X Y W₁ W₂)).app n (ψ₀.app n τ) := rfl
    rw [hgg]
    have hcomp : (SSet.Subcomplex.homOfLE
        (le_sup_left : fstSub X Y W₁ ≤ fstSmall X Y W₁ W₂)) ≫
        (fstSmall X Y W₁ W₂).ι = (fstSub X Y W₁).ι :=
      SSet.Subcomplex.homOfLE_ι _
    have happ := congrArg (fun (φ : (fstSub X Y W₁).toSSet ⟶
        TopCat.toSSet.obj (TopProd X Y)) => φ.app n (ψ₀.app n τ)) hcomp
    exact happ ▸ subcomplex_iota_mem (fstSub X Y W₁) (ψ₀.app n τ)
  refine ⟨SSet.Subcomplex.lift g h₂, ?_⟩
  rw [← Category.assoc, SSet.Subcomplex.lift_ι]
  rw [hg]
  have hcomp2 : (ψ₀ ≫ SSet.Subcomplex.homOfLE (le_sup_left : fstSub X Y W₁ ≤ fstSmall X Y W₁ W₂)) ≫
      (fstSmall X Y W₁ W₂).ι = ψ₀ ≫ (fstSub X Y W₁).ι := by
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
  rw [← Category.assoc, hcomp2, Category.assoc, hψ₀]

/-- The slice into the intersection of the two pieces, as a subcomplex of the small complex. -/
theorem exists_slice_inter_pre (W₁ W₂ : Set ↥X) (c : ↥X) (hc : c ∈ W₁ ∩ W₂) :
    ∃ ψ : TopCat.toSSet.obj Y ⟶
        ((fstSub X Y W₁ ⊓ fstSub X Y W₂).preimage (fstSmall X Y W₁ W₂).ι).toSSet,
      ψ ≫ (((fstSub X Y W₁ ⊓ fstSub X Y W₂).preimage (fstSmall X Y W₁ W₂).ι).ι
        ≫ (fstSmall X Y W₁ W₂).ι ≫ TopCat.toSSet.map (sndMor X Y))
        = 𝟙 (TopCat.toSSet.obj Y) := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_slice_inf (X := X) (Y := Y) W₁ W₂ c hc
  have hle : fstSub X Y W₁ ⊓ fstSub X Y W₂ ≤ fstSmall X Y W₁ W₂ :=
    le_trans inf_le_left le_sup_left
  have hgl : (ψ₀ ≫ SSet.Subcomplex.homOfLE hle) ≫ (fstSmall X Y W₁ W₂).ι
      = ψ₀ ≫ (fstSub X Y W₁ ⊓ fstSub X Y W₂).ι := by
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
  have hg : (ψ₀ ≫ SSet.Subcomplex.homOfLE hle) ≫ (fstSmall X Y W₁ W₂).ι
      ≫ TopCat.toSSet.map (sndMor X Y) = 𝟙 (TopCat.toSSet.obj Y) := by
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι_assoc]
    exact hψ₀
  have h₂ : SSet.Subcomplex.range (ψ₀ ≫ SSet.Subcomplex.homOfLE hle) ≤
      (fstSub X Y W₁ ⊓ fstSub X Y W₂).preimage (fstSmall X Y W₁ W₂).ι := by
    intro n σ hσ
    rw [CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hσ
    obtain ⟨τ, rfl⟩ := hσ
    rw [SSet.Subcomplex.preimage_obj]
    show ((fstSmall X Y W₁ W₂).ι).app n ((ψ₀ ≫ SSet.Subcomplex.homOfLE hle).app n τ)
      ∈ (fstSub X Y W₁ ⊓ fstSub X Y W₂).obj n
    have hgg : ((fstSmall X Y W₁ W₂).ι).app n
        ((ψ₀ ≫ SSet.Subcomplex.homOfLE hle).app n τ)
        = (fstSub X Y W₁ ⊓ fstSub X Y W₂).ι.app n (ψ₀.app n τ) :=
      congrArg (fun (φ : TopCat.toSSet.obj Y ⟶ TopCat.toSSet.obj (TopProd X Y)) =>
        φ.app n τ) hgl
    rw [hgg]
    exact subcomplex_iota_mem _ _
  refine ⟨SSet.Subcomplex.lift (ψ₀ ≫ SSet.Subcomplex.homOfLE hle) h₂, ?_⟩
  have hlift : SSet.Subcomplex.lift (ψ₀ ≫ SSet.Subcomplex.homOfLE hle) h₂
      ≫ ((fstSub X Y W₁ ⊓ fstSub X Y W₂).preimage
          (fstSmall X Y W₁ W₂).ι).ι = ψ₀ ≫ SSet.Subcomplex.homOfLE hle :=
    SSet.Subcomplex.lift_ι _ h₂
  show (SSet.Subcomplex.lift (ψ₀ ≫ SSet.Subcomplex.homOfLE hle) h₂
      ≫ ((fstSub X Y W₁ ⊓ fstSub X Y W₂).preimage
          (fstSmall X Y W₁ W₂).ι).ι)
      ≫ (fstSmall X Y W₁ W₂).ι ≫ TopCat.toSSet.map (sndMor X Y) = 𝟙 (TopCat.toSSet.obj Y)
  rw [hlift]
  exact hg

end
/-- If the projection `π : S ⟶ T` has a section `σ` (`σ ≫ π = 𝟙 T`), then the pullback
`H.map ℚ π n` is injective.  In particular a class whose pullback along `π` vanishes is zero. -/
lemma H_map_eq_zero_of_section {S T : SSet.{0}} (π : S ⟶ T) (σ : T ⟶ S)
    (h : σ ≫ π = 𝟙 T) (n : ℕ) (v : H T ℚ n) (hv : H.map ℚ π n v = 0) : v = 0 := by
  have hcomp := Work.Cohomology.H_map_comp σ π n v
  rw [hv, map_zero] at hcomp
  rw [h, H.map_id] at hcomp
  have h1 : (1 : H T ℚ n →ₗ[ℚ] H T ℚ n) v = v := Module.End.one_apply v
  rw [h1] at hcomp
  exact hcomp

end HdimProd

/-! ## The two-cap cover of `S^{a+1} × S^{a+1}` pulled back from the first factor -/

/-- The "small" subcomplex of the cover of `S^{a+1} × S^{a+1}`. -/
abbrev covSsub (a : ℕ) : (TopCat.toSSet.obj (TopProd (Sph (a+1)) (Sph (a+1)))).Subcomplex :=
  fstSmall (Sph (a+1)) (Sph (a+1)) (capPlus a) (capMinus a)

/-- The small complex, as a simplicial set. -/
abbrev covS (a : ℕ) : SSet.{0} := (covSsub a : SSet.{0})

/-- The first piece of the cover. -/
abbrev covA (a : ℕ) : (covS a).Subcomplex :=
  fstAsub (Sph (a+1)) (Sph (a+1)) (capPlus a) (capMinus a)

/-- The second piece of the cover. -/
abbrev covB (a : ℕ) : (covS a).Subcomplex :=
  fstBsub (Sph (a+1)) (Sph (a+1)) (capPlus a) (capMinus a)

/-- The intersection of the two pieces. -/
abbrev covI (a : ℕ) : (covS a).Subcomplex := covA a ⊓ covB a

lemma covA_sup_covB (a : ℕ) : covA a ⊔ covB a = ⊤ := fstAsub_sup_fstBsub _ _ _ _

lemma covA_inf_covB (a : ℕ) : covA a ⊓ covB a =
    fstCsub (Sph (a+1)) (Sph (a+1)) (capPlus a) (capMinus a) := fstAsub_inf_fstBsub _ _ _ _

/-! ## A point of the doubly punctured sphere -/

/-- The first standard basis vector of `ℝ^{a+2}`, as a point of `S^{a+1}` lying in neither pole. -/
def hdPt (a : ℕ) : ↥(Sph (a+1)) :=
  ⟨EuclideanSpace.single (0 : Fin (a+2)) 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]; norm_num⟩

lemma hdPt_mem_capPlus (a : ℕ) : hdPt a ∈ capPlus a := by
  intro h
  have h2 : (EuclideanSpace.single (0 : Fin (a+2)) (1:ℝ)).ofLp
      = (pole (a+1)).ofLp := congrArg WithLp.ofLp h
  have h3 := congrFun h2 (0 : Fin (a+2))
  rw [PiLp.single_apply] at h3
  simp [pole] at h3

lemma hdPt_mem_capMinus (a : ℕ) : hdPt a ∈ capMinus a := by
  intro h
  have h2 : (EuclideanSpace.single (0 : Fin (a+2)) (1:ℝ)).ofLp
      = (-pole (a+1)).ofLp := congrArg WithLp.ofLp h
  have h3 := congrFun h2 (0 : Fin (a+2))
  rw [PiLp.single_apply] at h3
  simp [pole] at h3

lemma hdPt_mem (a : ℕ) : hdPt a ∈ capPlus a ∩ capMinus a :=
  ⟨hdPt_mem_capPlus a, hdPt_mem_capMinus a⟩

/-! ## The cohomology of the pieces -/

/-- The first piece has the cohomology of `S^{a+1}`. -/
theorem covA_iso_sph (a : ℕ) (m : ℕ) :
    Nonempty (H (covA a) ℚ m ≃ₗ[ℚ] H (singSph (a+1)) ℚ m) := by
  haveI : ContractibleSpace ↥(capPlus a) := capPlus_contractible a
  obtain ⟨e1⟩ := H_fstAsub_iso (Sph (a+1)) (Sph (a+1)) (capPlus a) (capMinus a) m
  obtain ⟨e2⟩ := H_fstSub_contractible_iso (X := Sph (a+1)) (Y := Sph (a+1))
    (capPlus a) m
  exact ⟨e1.trans e2⟩

/-- The second piece has the cohomology of `S^{a+1}`. -/
theorem covB_iso_sph (a : ℕ) (m : ℕ) :
    Nonempty (H (covB a) ℚ m ≃ₗ[ℚ] H (singSph (a+1)) ℚ m) := by
  haveI : ContractibleSpace ↥(capMinus a) := capMinus_contractible a
  obtain ⟨e1⟩ := H_fstBsub_iso (Sph (a+1)) (Sph (a+1)) (capPlus a) (capMinus a) m
  obtain ⟨e2⟩ := H_fstSub_contractible_iso (X := Sph (a+1)) (Y := Sph (a+1))
    (capMinus a) m
  exact ⟨e1.trans e2⟩

/-- The intersection has the cohomology of `S^a × S^{a+1}`. -/
theorem covI_iso_prod (a : ℕ) (m : ℕ) :
    Nonempty (H (covI a) ℚ m ≃ₗ[ℚ]
      H (TopCat.toSSet.obj (TopProd (Sph a) (Sph (a+1)))) ℚ m) := by
  obtain ⟨e0⟩ := Submission.Sphere.H_iso_of_iso
    (SSet.Subcomplex.eqToIso (covA_inf_covB a)) m
  obtain ⟨e1⟩ := H_fstCsub_homeo (Sph (a+1)) (Sph (a+1)) (capPlus a) (capMinus a) m
  rw [capPlus_inter_capMinus_eq_DPset a] at e1
  obtain ⟨e2⟩ := H_DPset_prod_iso a (Sph (a+1)) m
  exact ⟨e0.trans (e1.trans e2)⟩

/-! ## The main computation -/

/-- **The middle degree of the cohomology of `S^{a+1} × S^{a+1}`.**  For `a ≥ 1` the group
`H^{a+1}(S^{a+1} × S^{a+1}; ℚ)` is two-dimensional. -/
theorem H_prod_iso_rat (a : ℕ) (ha : 1 ≤ a) :
    Nonempty (H (TopCat.toSSet.obj (TopProd (Sph (a+1)) (Sph (a+1)))) ℚ (a+1)
      ≃ₗ[ℚ] (ℚ × ℚ)) := by
  classical
  have hAB : covA a ⊔ covB a = ⊤ := covA_sup_covB a
  -- ### the two pieces have the cohomology of `S^{a+1}`
  obtain ⟨eA⟩ := covA_iso_sph a (a+1)
  obtain ⟨eB⟩ := covB_iso_sph a (a+1)
  obtain ⟨eA'⟩ := sphere_top (a+1) (by omega)
  obtain ⟨eB'⟩ := sphere_top (a+1) (by omega)
  let e2 : (H (covA a) ℚ (a+1) × H (covB a) ℚ (a+1)) ≃ₗ[ℚ] (ℚ × ℚ) :=
    (eA.trans eA').prodCongr (eB.trans eB')
  haveI hfin2 : FiniteDimensional ℚ (H (covA a) ℚ (a+1) × H (covB a) ℚ (a+1)) :=
    e2.symm.finiteDimensional
  have hsrc : Module.finrank ℚ (H (covA a) ℚ (a+1) × H (covB a) ℚ (a+1)) = 2 := by
    rw [LinearEquiv.finrank_eq e2, Module.finrank_prod]
    simp
  -- ### the two pieces vanish in degree `a`
  have hA_mid : Subsingleton (H (covA a) ℚ a) := by
    obtain ⟨f1⟩ := covA_iso_sph a a
    exact subsingleton_of_linearEquiv f1 (sphere_subsingleton (a+1) a (by omega) (by omega))
  have hB_mid : Subsingleton (H (covB a) ℚ a) := by
    obtain ⟨f1⟩ := covB_iso_sph a a
    exact subsingleton_of_linearEquiv f1 (sphere_subsingleton (a+1) a (by omega) (by omega))
  -- ### the intersection in degree `a` is `ℚ`
  have hI_low : Nonempty (H (covI a) ℚ a ≃ₗ[ℚ] ℚ) := by
    obtain ⟨f1⟩ := covI_iso_prod a a
    obtain ⟨f2⟩ := PH_low_mid a ha
    exact ⟨f1.trans f2⟩
  -- ### the connecting map in degree `a` is injective
  have hdcInj : Function.Injective (mvConnecting (covS a) (covA a) (covB a) hAB a) :=
    Work.Cohomology.mvConnecting_injective (covS a) (covA a) (covB a) hAB a ha hA_mid hB_mid
  -- ### the kernel of `mvAlphaH` is the line spanned by `g`
  obtain ⟨eI⟩ := hI_low
  set g : H (covS a) ℚ (a+1) := mvConnecting (covS a) (covA a) (covB a) hAB a (eI.symm 1)
    with hgdef
  have hg_mem : g ∈ (mvConnecting (covS a) (covA a) (covB a) hAB a).range := ⟨_, rfl⟩
  have hg_ne : g ≠ 0 := by
    intro h
    have h1 : (mvConnecting (covS a) (covA a) (covB a) hAB a) (eI.symm 1)
        = (mvConnecting (covS a) (covA a) (covB a) hAB a) 0 := by
      rw [show (mvConnecting (covS a) (covA a) (covB a) hAB a) (eI.symm 1) = g from rfl,
        h, map_zero]
    have h2 : eI.symm (1 : ℚ) = 0 := hdcInj h1
    have h3 : (1 : ℚ) = 0 := by
      conv_lhs => rw [← LinearEquiv.apply_symm_apply eI (1 : ℚ)]
      rw [h2, map_zero]
    exact one_ne_zero h3
  have hkerα : (mvAlphaH (covS a) (covA a) (covB a) (a+1)).ker = ℚ ∙ g := by
    rw [Work.Cohomology.mvAlphaH_ker_eq_range (covS a) (covA a) (covB a) hAB a]
    refine le_antisymm ?_ ?_
    · rintro v ⟨w, rfl⟩
      have hw : w = (eI w) • eI.symm 1 := by
        conv_lhs => rw [← LinearEquiv.symm_apply_apply eI w]
        rw [show eI w = (eI w) • (1 : ℚ) by simp, map_smul]
        simp
      show (mvConnecting (covS a) (covA a) (covB a) hAB a) w ∈ ℚ ∙ g
      rw [hw, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hg_mem
  have hg_ker : g ∈ (mvAlphaH (covS a) (covA a) (covB a) (a+1)).ker := by
    rw [Work.Cohomology.mvAlphaH_ker_eq_range (covS a) (covA a) (covB a) hAB a]
    exact hg_mem
  have hg_zero : mvAlphaH (covS a) (covA a) (covB a) (a+1) g = 0 :=
    LinearMap.mem_ker.mp hg_ker
  -- ### the class `z` on `S^{a+1}` and its pullbacks
  obtain ⟨eY⟩ := sphere_top (a+1) (by omega)
  set z : H (singSph (a+1)) ℚ (a+1) := eY.symm 1 with hzdef
  have hz : z ≠ 0 := by
    intro h
    have h2 : (1 : ℚ) = 0 := by
      have h3 : eY z = 0 := by rw [h, map_zero]
      rwa [show eY z = 1 from by rw [hzdef]; exact LinearEquiv.apply_symm_apply eY 1] at h3
    exact one_ne_zero h2
  set κS : H (covS a) ℚ (a+1) :=
    H.map ℚ ((covSsub a).ι
      ≫ TopCat.toSSet.map (HdimProd.sndMor (Sph (a+1)) (Sph (a+1)))) (a+1) z with hκSdef
  set κA : H (covA a) ℚ (a+1) :=
    H.map ℚ ((covA a).ι ≫ (covSsub a).ι
      ≫ TopCat.toSSet.map (HdimProd.sndMor (Sph (a+1)) (Sph (a+1)))) (a+1) z with hκAdef
  set κI : H (covI a) ℚ (a+1) :=
    H.map ℚ ((covI a).ι ≫ (covSsub a).ι
      ≫ TopCat.toSSet.map (HdimProd.sndMor (Sph (a+1)) (Sph (a+1)))) (a+1) z with hκIdef
  have hκA_map : H.map ℚ (covA a).ι (a+1) κS = κA := by
    have hcomp := Work.Cohomology.H_map_comp (covA a).ι
      ((covSsub a).ι ≫ TopCat.toSSet.map (HdimProd.sndMor (Sph (a+1)) (Sph (a+1)))) (a+1) z
    rw [hκSdef, ← hcomp, hκAdef]
  have hκI_rel : H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : covI a ≤ covA a)) (a+1) κA
      = κI := by
    have hcomp := Work.Cohomology.H_map_comp
      (SSet.Subcomplex.homOfLE (inf_le_left : covI a ≤ covA a))
      ((covA a).ι ≫ (covSsub a).ι
        ≫ TopCat.toSSet.map (HdimProd.sndMor (Sph (a+1)) (Sph (a+1)))) (a+1) z
    rw [hκAdef, ← hcomp, hκIdef, SSet.Subcomplex.homOfLE_ι_assoc]
  -- ### `κA` and `κI` are nonzero, since the projections have slices
  obtain ⟨ψA, hψA⟩ := HdimProd.exists_slice_fstAsub (X := Sph (a+1)) (Y := Sph (a+1))
    (capPlus a) (capMinus a) (hdPt a) (hdPt_mem_capPlus a)
  have hκA_ne : κA ≠ 0 := by
    intro h0
    refine hz (HdimProd.H_map_eq_zero_of_section
      ((covA a).ι ≫ (covSsub a).ι
        ≫ TopCat.toSSet.map (HdimProd.sndMor (Sph (a+1)) (Sph (a+1)))) ψA hψA (a+1) z ?_)
    rw [← hκAdef]
    exact h0
  obtain ⟨ψI, hψI⟩ := HdimProd.exists_slice_inter_pre (X := Sph (a+1)) (Y := Sph (a+1))
    (capPlus a) (capMinus a) (hdPt a) (hdPt_mem a)
  have hκI_ne : κI ≠ 0 := by
    intro h0
    refine hz (HdimProd.H_map_eq_zero_of_section
      ((covI a).ι ≫ (covSsub a).ι
        ≫ TopCat.toSSet.map (HdimProd.sndMor (Sph (a+1)) (Sph (a+1)))) ψI hψI (a+1) z ?_)
    rw [← hκIdef]
    exact h0
  -- ### `mvAlphaH κS ≠ 0` and `mvBetaH ≠ 0`
  have hακ : mvAlphaH (covS a) (covA a) (covB a) (a+1) κS ≠ 0 := by
    intro h0
    have h1 : H.map ℚ (covA a).ι (a+1) κS = 0 := by
      have h2 := congrArg Prod.fst h0
      simpa [mvAlphaH_apply] using h2
    rw [hκA_map] at h1
    exact hκA_ne h1
  have hβ_ne : mvBetaH (covS a) (covA a) (covB a) (a+1) ≠ 0 := by
    intro h0
    have hb : mvBetaH (covS a) (covA a) (covB a) (a+1) (κA, 0) = 0 := by
      rw [h0]
      rfl
    have hb' : mvBetaH (covS a) (covA a) (covB a) (a+1) (κA, 0)
        = H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : covI a ≤ covA a)) (a+1) κA := by
      rw [mvBetaH_apply]
      simp
    rw [hb', hκI_rel] at hb
    exact hκI_ne hb
  -- ### the kernel of `mvBetaH` is the line spanned by `α κS`
  have hkerβ_ne : (mvBetaH (covS a) (covA a) (covB a) (a+1)).ker ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨mvAlphaH (covS a) (covA a) (covB a) (a+1) κS, ?_, hακ⟩
    rw [Work.Cohomology.mvBetaH_ker_eq_range (covS a) (covA a) (covB a) hAB (a+1)]
    exact ⟨κS, rfl⟩
  have hk1 : 0 < Module.finrank ℚ ↥(mvBetaH (covS a) (covA a) (covB a) (a+1)).ker := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hkerβ_ne ((Submodule.finrank_eq_zero).mp h0)
  have hk2 : 0 < Module.finrank ℚ ↥(mvBetaH (covS a) (covA a) (covB a) (a+1)).range := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hβ_ne ((LinearMap.range_eq_bot).mp ((Submodule.finrank_eq_zero).mp h0))
  have hsum := LinearMap.finrank_range_add_finrank_ker
    (mvBetaH (covS a) (covA a) (covB a) (a+1))
  have hkerβ_fin : Module.finrank ℚ ↥(mvBetaH (covS a) (covA a) (covB a) (a+1)).ker = 1 := by
    omega
  have hkerβ_eq : (mvBetaH (covS a) (covA a) (covB a) (a+1)).ker
      = ℚ ∙ mvAlphaH (covS a) (covA a) (covB a) (a+1) κS := by
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      rw [Work.Cohomology.mvBetaH_ker_eq_range (covS a) (covA a) (covB a) hAB (a+1)]
      exact ⟨κS, rfl⟩
    · rw [hkerβ_fin, finrank_span_singleton hακ]
  -- ### the explicit isomorphism `ℚ × ℚ ≅ H^{a+1}(small)`
  let Φ : (ℚ × ℚ) →ₗ[ℚ] H (covS a) ℚ (a+1) :=
    { toFun := fun cd => cd.1 • κS + cd.2 • g
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      map_smul' := fun r x => by
        simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add, smul_smul,
          smul_eq_mul] }
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have h2 : Φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h3 : mvAlphaH (covS a) (covA a) (covB a) (a+1) (Φ (x - y)) = 0 := by
      rw [h2, map_zero]
    have h4 : (x - y).1 • (mvAlphaH (covS a) (covA a) (covB a) (a+1) κS) = 0 := by
      have h5 := h3
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul, hg_zero, map_zero,
        smul_zero, add_zero] at h5
      exact h5
    have hc : (x - y).1 = 0 := by
      rcases smul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h hακ
    have h5 : (x - y).2 • g = 0 := by
      have h6 := h2
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h6
      rw [hc, zero_smul, zero_add] at h6
      exact h6
    have hd : (x - y).2 = 0 := by
      rcases smul_eq_zero.mp h5 with h | h
      · exact h
      · exact absurd h hg_ne
    have h7 : x - y = 0 := Prod.ext hc hd
    exact sub_eq_zero.mp h7
  have hΦsurj : Function.Surjective Φ := by
    intro v
    have hv : mvAlphaH (covS a) (covA a) (covB a) (a+1) v
        ∈ (mvBetaH (covS a) (covA a) (covB a) (a+1)).ker := by
      rw [Work.Cohomology.mvBetaH_ker_eq_range (covS a) (covA a) (covB a) hAB (a+1)]
      exact ⟨v, rfl⟩
    rw [hkerβ_eq, Submodule.mem_span_singleton] at hv
    obtain ⟨c, hc⟩ := hv
    have hmem : v - c • κS ∈ (mvAlphaH (covS a) (covA a) (covB a) (a+1)).ker := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hc, sub_self]
    rw [hkerα, Submodule.mem_span_singleton] at hmem
    obtain ⟨d, hd⟩ := hmem
    refine ⟨(c, d), ?_⟩
    show c • κS + d • g = v
    rw [hd]
    abel
  let Φiso : (ℚ × ℚ) ≃ₗ[ℚ] H (covS a) ℚ (a+1) :=
    LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  -- ### transfer to the product of spheres
  obtain ⟨eS⟩ := H_fstSmall_iso (Sph (a+1)) (Sph (a+1)) (capPlus a) (capMinus a)
    (isOpen_capPlus a) (isOpen_capMinus a)
    (fun x => Set.eq_univ_iff_forall.mp (capPlus_union_capMinus a) x) (a+1)
  exact ⟨eS.trans Φiso.symm⟩

/-! ## The two ranges span the middle cohomology -/

/-- For `a ≥ 1` the pullbacks of a nonzero class of `H^{a+1}(S^{a+1}; ℚ)` along the two
projections of `S^{a+1} × S^{a+1}` are linearly independent: the products `x ⌣ x` vanish for
degree reasons, the cross product `p₁ ⌣ p₂` is nonzero, and the two middle terms of the
expansion of `(c p₁ + d p₂)²` cancel up to sign. -/
theorem H_cup_pair_indep (a : ℕ) (ha : 1 ≤ a)
    (x : H (singSph (a+1)) ℚ (a+1)) (hx : x ≠ 0) :
    ∀ c d : ℚ,
      c • H.map ℚ (SemiCartesianMonoidalCategory.fst (singSph (a+1)) (singSph (a+1))) (a+1) x
        + d • H.map ℚ (SemiCartesianMonoidalCategory.snd (singSph (a+1)) (singSph (a+1)))
            (a+1) x = 0 → c = 0 ∧ d = 0 := by
  intro c d hcd
  set p₁ := H.map ℚ (SemiCartesianMonoidalCategory.fst (singSph (a+1)) (singSph (a+1)))
    (a+1) x with hp1
  set p₂ := H.map ℚ (SemiCartesianMonoidalCategory.snd (singSph (a+1)) (singSph (a+1)))
    (a+1) x with hp2
  have hsquare : H.cup (a+1) (a+1) p₁ p₁ = 0 := by
    haveI : Subsingleton (H (singSph (a+1)) ℚ ((a+1)+(a+1))) :=
      sphere_subsingleton (a+1) ((a+1)+(a+1)) (by omega) (by omega)
    have hx2 : H.cup (a+1) (a+1) x x = 0 := Subsingleton.elim _ _
    have h1 : H.cup (a+1) (a+1) p₁ p₁
        = H.map ℚ (SemiCartesianMonoidalCategory.fst (singSph (a+1)) (singSph (a+1)))
            ((a+1)+(a+1)) (H.cup (a+1) (a+1) x x) := by
      rw [hp1]
      exact (Work.Cohomology.H_map_cupOf
        (SemiCartesianMonoidalCategory.fst (singSph (a+1)) (singSph (a+1)))
        (rfl : (a+1)+(a+1) = (a+1)+(a+1)) x x).symm
    rw [h1, hx2, map_zero]
  have hsquare2 : H.cup (a+1) (a+1) p₂ p₂ = 0 := by
    haveI : Subsingleton (H (singSph (a+1)) ℚ ((a+1)+(a+1))) :=
      sphere_subsingleton (a+1) ((a+1)+(a+1)) (by omega) (by omega)
    have hx2 : H.cup (a+1) (a+1) x x = 0 := Subsingleton.elim _ _
    have h1 : H.cup (a+1) (a+1) p₂ p₂
        = H.map ℚ (SemiCartesianMonoidalCategory.snd (singSph (a+1)) (singSph (a+1)))
            ((a+1)+(a+1)) (H.cup (a+1) (a+1) x x) := by
      rw [hp2]
      exact (Work.Cohomology.H_map_cupOf
        (SemiCartesianMonoidalCategory.snd (singSph (a+1)) (singSph (a+1)))
        (rfl : (a+1)+(a+1) = (a+1)+(a+1)) x x).symm
    rw [h1, hx2, map_zero]
  have hcross : H.cup (a+1) (a+1) p₁ p₂ ≠ 0 := by
    rw [hp1, hp2]
    exact Work.Cohomology.H_cup_cross_ne_zero x x hx hx
  have hcross' : H.cup (a+1) (a+1) p₂ p₁ ≠ 0 := by
    intro h
    rw [Work.Cohomology.H_cup_comm (a+1) p₁ p₂] at h
    have h2 : H.cup (a+1) (a+1) p₁ p₂ = 0 := by
      have h3 := congrArg (fun w => ((-1 : ℤ) ^ ((a+1)*(a+1))) • w) h
      rw [smul_zero] at h3
      rwa [Submission.Cohomology.negOnePow_smul_smul] at h3
    exact hcross h2
  have hzero_left : ∀ y, H.cup (a+1) (a+1)
      (0 : H (singSph (a+1) ⊗ singSph (a+1)) ℚ (a+1)) y = 0 := by
    intro y
    have h := Work.Cohomology.H_cupOf_smul_left (R := ℚ)
      (rfl : (a+1)+(a+1) = (a+1)+(a+1)) (0 : ℚ)
      (0 : H (singSph (a+1) ⊗ singSph (a+1)) ℚ (a+1)) y
    simpa [Submission.Cohomology.H.cup] using h
  have hp1ne : p₁ ≠ 0 := fun h => hcross (by rw [h]; exact hzero_left p₂)
  have hcup_add : ∀ u v w : H (singSph (a+1) ⊗ singSph (a+1)) ℚ (a+1),
      H.cup (a+1) (a+1) (u + v) w
        = H.cup (a+1) (a+1) u w + H.cup (a+1) (a+1) v w := by
    intro u v w
    have h := Work.Cohomology.H_cupOf_add_left (R := ℚ)
      (rfl : (a+1)+(a+1) = (a+1)+(a+1)) u v w
    simpa [Submission.Cohomology.H.cup] using h
  have hcup_smul : ∀ (r : ℚ) (u w : H (singSph (a+1) ⊗ singSph (a+1)) ℚ (a+1)),
      H.cup (a+1) (a+1) (r • u) w = r • H.cup (a+1) (a+1) u w := by
    intro r u w
    have h := Work.Cohomology.H_cupOf_smul_left (R := ℚ)
      (rfl : (a+1)+(a+1) = (a+1)+(a+1)) r u w
    simpa [Submission.Cohomology.H.cup] using h
  have h1 : c • H.cup (a+1) (a+1) p₁ p₁ + d • H.cup (a+1) (a+1) p₂ p₁ = 0 := by
    have h := congrArg (fun w => H.cup (a+1) (a+1) w p₁) hcd
    rw [hzero_left] at h
    rw [hcup_add, hcup_smul, hcup_smul] at h
    exact h
  have hd : d = 0 := by
    rw [hsquare, smul_zero, zero_add] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hcross'
  have hc : c = 0 := by
    rw [hd, zero_smul, add_zero] at hcd
    rcases smul_eq_zero.mp hcd with h | h
    · exact h
    · exact absurd h hp1ne
  exact ⟨hc, hd⟩

/-- **The two projection pullbacks span the middle cohomology of `S^{a+1} × S^{a+1}`.**  This is
the tensor-product form of `H_dim_sph_prod`. -/
theorem H_dim_prod_top (a : ℕ) (ha : 1 ≤ a) :
    LinearMap.range (H.map ℚ (SemiCartesianMonoidalCategory.fst (singSph (a+1))
        (singSph (a+1))) (a+1))
      ⊔ LinearMap.range (H.map ℚ (SemiCartesianMonoidalCategory.snd (singSph (a+1))
        (singSph (a+1))) (a+1)) = ⊤ := by
  classical
  obtain ⟨eP⟩ := H_prod_iso_rat a ha
  haveI hfinP : FiniteDimensional ℚ
      (H (TopCat.toSSet.obj (TopProd (Sph (a+1)) (Sph (a+1)))) ℚ (a+1)) :=
    eP.symm.finiteDimensional
  obtain ⟨eT⟩ := H_tensor_homeo (Sph (a+1)) (Sph (a+1)) (a+1)
  haveI hfinS : FiniteDimensional ℚ
      (H (MonoidalCategoryStruct.tensorObj (TopCat.toSSet.obj (Sph (a+1)))
        (TopCat.toSSet.obj (Sph (a+1)))) ℚ (a+1)) := eT.symm.finiteDimensional
  have hfin_prod : Module.finrank ℚ
      (H (TopCat.toSSet.obj (TopProd (Sph (a+1)) (Sph (a+1)))) ℚ (a+1)) = 2 := by
    rw [LinearEquiv.finrank_eq eP, Module.finrank_prod]
    simp
  have hfin_tensor : Module.finrank ℚ
      (H (MonoidalCategoryStruct.tensorObj (TopCat.toSSet.obj (Sph (a+1)))
        (TopCat.toSSet.obj (Sph (a+1)))) ℚ (a+1)) = 2 := by
    rw [LinearEquiv.finrank_eq eT, hfin_prod]
  obtain ⟨eY⟩ := sphere_top (a+1) (by omega)
  set x : H (singSph (a+1)) ℚ (a+1) := eY.symm 1 with hxdef
  have hx : x ≠ 0 := by
    intro h
    have h2 : (1 : ℚ) = 0 := by
      have h3 : eY x = 0 := by rw [h, map_zero]
      rwa [show eY x = 1 from by rw [hxdef]; exact LinearEquiv.apply_symm_apply eY 1] at h3
    exact one_ne_zero h2
  set p₁ : H (singSph (a+1) ⊗ singSph (a+1)) ℚ (a+1) :=
    H.map ℚ (SemiCartesianMonoidalCategory.fst (singSph (a+1)) (singSph (a+1)))
      (a+1) x with hp1def
  set p₂ : H (singSph (a+1) ⊗ singSph (a+1)) ℚ (a+1) :=
    H.map ℚ (SemiCartesianMonoidalCategory.snd (singSph (a+1)) (singSph (a+1)))
      (a+1) x with hp2def
  -- the group `H^{a+1}(S^{a+1})` is spanned by `x`
  have hspanX : ℚ ∙ x = (⊤ : Submodule ℚ (H (singSph (a+1)) ℚ (a+1))) := by
    apply le_antisymm le_top
    intro y _
    rw [Submodule.mem_span_singleton]
    refine ⟨eY y, ?_⟩
    rw [hxdef, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hrange1 : LinearMap.range (H.map ℚ
      (SemiCartesianMonoidalCategory.fst (singSph (a+1)) (singSph (a+1))) (a+1))
      = ℚ ∙ p₁ := by
    rw [LinearMap.range_eq_map, ← hspanX, Submodule.map_span, Set.image_singleton, hp1def]
  have hrange2 : LinearMap.range (H.map ℚ
      (SemiCartesianMonoidalCategory.snd (singSph (a+1)) (singSph (a+1))) (a+1))
      = ℚ ∙ p₂ := by
    rw [LinearMap.range_eq_map, ← hspanX, Submodule.map_span, Set.image_singleton, hp2def]
  have hind := H_cup_pair_indep a ha x hx
  have hli : LinearIndependent ℚ ![p₁, p₂] := by
    rw [LinearIndependent.pair_iff]
    exact hind
  have hcard : Module.finrank ℚ (Submodule.span ℚ (Set.range ![p₁, p₂])) = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  have htop : Submodule.span ℚ (Set.range ![p₁, p₂]) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hcard, hfin_tensor]
  have hrange_eq : Set.range ![p₁, p₂] = ({p₁, p₂} : Set _) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hw
      rcases hw with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
  have hspan_eq : Submodule.span ℚ ({p₁, p₂} : Set _) = ℚ ∙ p₁ ⊔ ℚ ∙ p₂ := by
    rw [show ({p₁, p₂} : Set _) = {p₁} ∪ {p₂} from rfl, Submodule.span_union]
  have htop' : ℚ ∙ p₁ ⊔ ℚ ∙ p₂ = ⊤ := by
    rw [← hspan_eq, ← hrange_eq]
    exact htop
  rw [hrange1, hrange2, htop']

/-- **The dimension input for the even case of Adams' theorem.**  For `n ≥ 2` the ranges of the
maps induced by the two projections `Sⁿ × Sⁿ → Sⁿ` on `H^n(-; ℚ)` span `H^n(Sⁿ × Sⁿ; ℚ)`. -/
theorem H_dim_sph_prod (n : ℕ) (hn : 2 ≤ n) :
    LinearMap.range (Submission.Cohomology.H.map ℚ
        (CategoryTheory.SemiCartesianMonoidalCategory.fst (Submission.Sphere.singSph n)
          (Submission.Sphere.singSph n)) n)
      ⊔ LinearMap.range (Submission.Cohomology.H.map ℚ
        (CategoryTheory.SemiCartesianMonoidalCategory.snd (Submission.Sphere.singSph n)
          (Submission.Sphere.singSph n)) n) = ⊤ := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  have ha : 1 ≤ a := by omega
  exact H_dim_prod_top a ha

end

end Work.Sphere
