import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.klain_333_dim_one
import Submission.Commons.Geometry.Convex.Hadwiger.continuous_convexBody_smul

open Set
open Filter
open scoped Pointwise Topology

namespace Commons.Geometry.Convex.Hadwiger

section BodyTransport

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Image of a convex body under a linear isometry equivalence. -/
noncomputable def ConvexBody.imageLIE (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody V) : ConvexBody W :=
  ⟨e '' (K : Set V), Convex.linear_image K.convex (e.toLinearEquiv.toLinearMap),
    K.isCompact.image e.continuous, K.nonempty.image e⟩

/-- The body-image map is a metric isometry. -/
theorem imageLIE_dist (e : V ≃ₗᵢ[ℝ] W) (K L : ConvexBody V) :
    dist (ConvexBody.imageLIE e K) (ConvexBody.imageLIE e L) = dist K L := by
  unfold ConvexBody.imageLIE
  rw [← ConvexBody.hausdorffDist_coe, ← ConvexBody.hausdorffDist_coe]
  exact Metric.hausdorffDist_image (h := e.isometry)

theorem imageLIE_isometry (e : V ≃ₗᵢ[ℝ] W) :
    Isometry (fun K : ConvexBody V => ConvexBody.imageLIE e K) := by
  rw [isometry_iff_dist_eq]
  intro K L
  exact imageLIE_dist e K L

@[simp] theorem imageLIE_apply (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody V) :
    (ConvexBody.imageLIE e K : Set W) = e '' (K : Set V) :=
  rfl

/-- Transporting back along the inverse cancels. -/
theorem imageLIE_symm_imageLIE (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody V) :
    ConvexBody.imageLIE e.symm (ConvexBody.imageLIE e K) = K := by
  apply ConvexBody.ext
  simp only [imageLIE_apply, Set.image_image]
  have hfun : (fun x : V => e.symm (e x)) = id := by
    funext x
    exact e.symm_apply_apply x
  rw [hfun]
  simp

/-- Transporting forward along the inverse cancels. -/
theorem imageLIE_imageLIE_symm (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody W) :
    ConvexBody.imageLIE e (ConvexBody.imageLIE e.symm K) = K := by
  apply ConvexBody.ext
  simp only [imageLIE_apply, Set.image_image]
  have hfun : (fun x : W => e (e.symm x)) = id := by
    funext x
    exact e.apply_symm_apply x
  rw [hfun]
  simp

/-- A linear isometry maps a translation of a set to the translation of the image. -/
theorem lie_image_translate (e : V ≃ₗᵢ[ℝ] W) (A : Set V) (t : V) :
    e '' ((fun x : V => x + t) '' A) = (fun y : W => y + e t) '' (e '' A) := by
  ext w
  constructor
  · rintro ⟨v, ⟨x, hxA, rfl⟩, rfl⟩
    refine ⟨e x, Set.mem_image_of_mem e hxA, ?_⟩
    exact (e.map_add x t).symm
  · rintro ⟨y, ⟨x, hxA, rfl⟩, rfl⟩
    refine ⟨x + t, ?_, ?_⟩
    · exact Set.mem_image_of_mem (fun z : V => z + t) hxA
    · exact e.map_add x t

/-- Interior commutes with the image under a linear isometry (a homeomorphism). -/
theorem lie_image_interior (e : V ≃ₗᵢ[ℝ] W) (A : Set V) :
    interior (e '' A : Set W) = e '' interior A := by
  rw [← LinearIsometryEquiv.coe_toHomeomorph]
  exact ((LinearIsometryEquiv.toHomeomorph e).image_interior A).symm

end BodyTransport

-- ============================================================
--  One-dimensional Euclidean space: coordinate model
-- ============================================================

namespace Fin1

abbrev V := EuclideanSpace ℝ (Fin 1)

/-- `x ↦ (x, x, ...)`: the vector of `V` whose coordinate is `x`. -/
noncomputable def coordInv (x : ℝ) : V := WithLp.toLp 2 (fun _ : Fin 1 => x)

/-- coordinate projection: first (and only) coordinate. -/
noncomputable def coordₗ : V ≃ₗ[ℝ] ℝ where
  toFun v := v 0
  invFun := coordInv
  left_inv v := by
    apply PiLp.ext
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  right_inv x := by
    rfl
  map_add' x y := by
    simp
  map_smul' c x := by
    simp

/-- The coordinate map as a linear isometry `V ≃ₗᵢ ℝ`. -/
noncomputable def coordLie : V ≃ₗᵢ[ℝ] ℝ :=
  LinearEquiv.isometryOfInner coordₗ (by
    intro x y
    simp [PiLp.inner_apply]
    rfl)

@[simp] theorem coordLie_apply (v : V) : coordLie v = v 0 := rfl

@[simp] theorem coordLie_symm_apply (x : ℝ) : coordLie.symm x = coordInv x := rfl

/-- The unit cube of `V` equals the image of `[0,1]` under the coordinate embedding. -/
theorem cube_eq_coordInv_Icc :
    (EuclideanSpace.equiv (Fin 1) ℝ).symm ''
        (Set.pi Set.univ (fun _ : Fin 1 => Set.Icc (0 : ℝ) 1)) =
      coordInv '' (Set.Icc (0 : ℝ) 1) := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [PiLp.coe_symm_continuousLinearEquiv]
    refine ⟨f 0, ?_, ?_⟩
    · exact hf 0 (Set.mem_univ 0)
    · apply PiLp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(fun _ : Fin 1 => t), ?_, ?_⟩
    · intro i hi
      exact ht
    · rw [PiLp.coe_symm_continuousLinearEquiv]
      rfl

end Fin1

/-- The image of the unit interval `[0,1]` under the coordinate isometry is the
unit cube of `EuclideanSpace ℝ (Fin 1)`. -/
theorem coordLie_symm_image_Icc :
    Fin1.coordLie.symm '' (Set.Icc (0 : ℝ) 1) =
      (EuclideanSpace.equiv (Fin 1) ℝ).symm ''
        (Set.pi Set.univ (fun _ : Fin 1 => Set.Icc (0 : ℝ) 1)) := by
  rw [Fin1.cube_eq_coordInv_Icc]
  have hfun : Fin1.coordLie.symm = Fin1.coordInv := by
    funext x
    exact Fin1.coordLie_symm_apply x
  rw [hfun]

/-- Klain's box-vanishing theorem in dimension one, phrased on
`EuclideanSpace ℝ (Fin 1)`.  Transporting the valuation to `ℝ` along the
coordinate isometry reduces it to `klain_333_dim_one`. -/
theorem klain333_fin1 :
    let V := EuclideanSpace ℝ (Fin 1)
    ∀ (φ : ConvexBody V → ℝ),
      Continuous φ →
      (∀ A B C D : ConvexBody V,
          (A : Set V) = (C : Set V) ∪ (D : Set V) →
          (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D) →
      (∀ A B : ConvexBody V, ∀ t : V,
          (B : Set V) = (fun x : V => x + t) '' (A : Set V) → φ A = φ B) →
      (∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0) →
      (∀ A B : ConvexBody V, (B : Set V) = -(A : Set V) → φ A = φ B) →
      (∀ Q : ConvexBody V,
          (Q : Set V) = (EuclideanSpace.equiv (Fin 1) ℝ).symm '' (Set.pi Set.univ (fun _ : Fin 1 => Set.Icc (0 : ℝ) 1)) → φ Q = 0) →
      ∀ K : ConvexBody V, φ K = 0 := by
  dsimp
  classical
  let V : Type := EuclideanSpace ℝ (Fin 1)
  intro φ hcont hadd htrans hsimple _heven hcube K
  let e : V ≃ₗᵢ[ℝ] ℝ := Fin1.coordLie
  let Ψ : ConvexBody ℝ → ℝ := fun B => φ (ConvexBody.imageLIE e.symm B)
  have hΨcont : Continuous Ψ := by
    dsimp [Ψ]
    exact hcont.comp (imageLIE_isometry e.symm).continuous
  have hΨadd : ∀ A B C D : ConvexBody ℝ,
      (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
      (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → Ψ A + Ψ B = Ψ C + Ψ D := by
    intro A B C D hU hI
    dsimp [Ψ]
    have hU' : (ConvexBody.imageLIE e.symm A : Set V) =
        (ConvexBody.imageLIE e.symm C : Set V) ∪
          (ConvexBody.imageLIE e.symm D : Set V) := by
      rw [imageLIE_apply, imageLIE_apply, imageLIE_apply, hU, Set.image_union]
    have hI' : (ConvexBody.imageLIE e.symm B : Set V) =
        (ConvexBody.imageLIE e.symm C : Set V) ∩
          (ConvexBody.imageLIE e.symm D : Set V) := by
      rw [imageLIE_apply, imageLIE_apply, imageLIE_apply, hI,
        Set.image_inter (e.symm.injective)]
    exact hadd (ConvexBody.imageLIE e.symm A) (ConvexBody.imageLIE e.symm B)
      (ConvexBody.imageLIE e.symm C) (ConvexBody.imageLIE e.symm D) hU' hI'
  have hΨsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → Ψ K = 0 := by
    intro U hUint
    dsimp [Ψ]
    apply hsimple
    rw [imageLIE_apply]
    rw [lie_image_interior (e := e.symm) (A := (U : Set ℝ))]
    rw [hUint]
    simp
  have hΨtrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
      (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → Ψ A = Ψ B := by
    intro A B t hB
    dsimp [Ψ]
    apply htrans (ConvexBody.imageLIE e.symm A) (ConvexBody.imageLIE e.symm B) (e.symm t)
    rw [imageLIE_apply, imageLIE_apply, hB]
    exact lie_image_translate (e := e.symm) (A := (A : Set ℝ)) (t := t)
  have hΨunit : ∀ U : ConvexBody ℝ, (U : Set ℝ) = Set.Icc (0 : ℝ) 1 → Ψ U = 0 := by
    intro U hU
    dsimp [Ψ]
    apply hcube
    rw [imageLIE_apply, hU]
    change Fin1.coordLie.symm '' (Set.Icc (0 : ℝ) 1) =
      (EuclideanSpace.equiv (Fin 1) ℝ).symm ''
        (Set.pi Set.univ (fun _ : Fin 1 => Set.Icc (0 : ℝ) 1))
    exact coordLie_symm_image_Icc
  have hbase : ∀ B : ConvexBody ℝ, Ψ B = 0 :=
    klain_333_dim_one Ψ hΨcont hΨadd hΨsimple hΨtrans hΨunit
  calc
    φ K = Ψ (ConvexBody.imageLIE e K) := by
      dsimp [Ψ]
      rw [imageLIE_symm_imageLIE e K]
    _ = 0 := hbase (ConvexBody.imageLIE e K)

end Commons.Geometry.Convex.Hadwiger
