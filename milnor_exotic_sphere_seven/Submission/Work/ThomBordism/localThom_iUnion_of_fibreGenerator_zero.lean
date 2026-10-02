import Mathlib
import Submission.Work.ThomBordism.fibreGenerator_zero_rank
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.Thom.step_natural
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The union step of the fibre-generator condition in rank `0`

For a real bundle `Z → B` with a `0`-dimensional (hence subsingleton) model fibre `F`, the
complement `E∖0` of the zero section is empty, so `H^*(E,E∖0;ℤ) = H^*(E;ℤ)` and the local Thom map
of a class `τ ∈ H^0(X|_W, X|_W∖0)` is simply the cup product with the *absolute* class `relToAbs τ`.

For a bundle of rank `0` the mathematical content of the union step of
`Work.ThomBordism.localThom_iUnion_of_fibreGenerator` collapses to a statement about *units of the
ring* `H^0`: a degree-zero class is a unit of `H^*(−;ℤ)` iff all its point evaluations are `±1`, and
the evaluations over the union `⋃₀ C` of a chain of open sets are determined by the evaluations over
the members of `C`.

The file proves this in the form needed by the intended application: if the local Thom map is
bijective over every member of a chain `C`, then it is bijective over the union.  The proof uses

* `Work.Thom.localThomMap_apply` and `Work.Thom.mixedCup_relToAbs` to write the local Thom map as
  the cup product with the absolute class `c = relToAbs τ` followed (in degree `k`) by the pullback
  along the projection of the piece;
* `Work.Thom.ptEv_ext`/`ptEv_cup`/`ptEv_one` to identify units of `H^0` with classes evaluating to
  `±1` at every point;
* the fact that for a rank-`0` bundle the projection `↥(π ⁻¹' U) → ↥U` is a homeomorphism (its
  inverse is the restriction of the zero section), hence induces a bijection on cohomology.
-/

open CategoryTheory

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

/-! ## The pieces of the total space -/

/-- The complement of the zero section, inside the piece of the total space over `W`. -/
abbrev pieceZeroZ (Z : RealBundle B F ι) (W : Set B) : Set ↥(Z.proj ⁻¹' W) :=
  (Subtype.val : ↥(Z.proj ⁻¹' W) → Z.TotalSpace) ⁻¹' Work.Thom.zeroComplement Z

/-- The inclusion of the pieces of the total space over `W ⊆ U`. -/
def pieceInclZ (Z : RealBundle B F ι) (W U : Set B) (hWU : W ⊆ U) :
    C(↥(Z.proj ⁻¹' W), ↥(Z.proj ⁻¹' U)) :=
  ⟨fun y => ⟨(y : Z.TotalSpace), hWU y.2⟩,
    Continuous.subtype_mk (f := fun y : ↥(Z.proj ⁻¹' W) => (y : Z.TotalSpace))
      continuous_subtype_val (fun y => hWU y.2)⟩

@[simp] theorem pieceInclZ_apply (Z : RealBundle B F ι) (W U : Set B) (hWU : W ⊆ U)
    (p : ↥(Z.proj ⁻¹' W)) : pieceInclZ Z W U hWU p = ⟨(p : Z.TotalSpace), hWU p.2⟩ := rfl

/-- The inclusion of the pieces carries the complement of the zero section into itself. -/
theorem pieceInclZ_mem (Z : RealBundle B F ι) (W U : Set B) (hWU : W ⊆ U) :
    ∀ p ∈ pieceZeroZ Z W, pieceInclZ Z W U hWU p ∈ pieceZeroZ Z U := fun _ hp => hp

/-- For a bundle with a subsingleton fibre the complement of the zero section is empty. -/
theorem pieceZeroZ_eq_empty [Subsingleton F] (Z : RealBundle B F ι) (W : Set B) :
    pieceZeroZ Z W = ∅ := by
  simp only [pieceZeroZ, zeroComplement_eq_empty Z, Set.preimage_empty]

/-! ## Naturality of the forgetful map under restriction to a piece -/

/-- **Naturality of `relToAbs` under the restriction to a piece.**  For `W ⊆ U` and a relative
class over the piece `U`, the forgetful image of its restriction to the piece `W` is the pullback
(along the inclusion of the pieces) of its forgetful image over `U`. -/
theorem pdCohMap_relToAbs_apply (Z : RealBundle B F ι) {W U : Set B} (hWU : W ⊆ U) (k : ℕ)
    (τ : Work.Thom.PieceCoh Z U k) :
    (Work.Thom.relToAbs ℤ (pieceZeroZ Z W) k).hom
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) k).hom τ)
      = (Work.Thom.CohMap (pieceInclZ Z W U hWU) ℤ k).hom
          ((Work.Thom.relToAbs ℤ (pieceZeroZ Z U) k).hom τ) := by
  have h : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) k)
      = Work.Thom.relCohMap (pieceInclZ Z W U hWU) (pieceZeroZ Z W) (pieceZeroZ Z U)
          (pieceInclZ_mem Z W U hWU) ℤ k := rfl
  rw [h]
  exact Work.Thom.relCohMap_relToAbs_apply (pieceInclZ Z W U hWU) (pieceZeroZ Z W)
    (pieceZeroZ Z U) (pieceInclZ_mem Z W U hWU) ℤ k τ

/-- **The pointwise form of the naturality** of the forgetful map under restriction to a piece. -/
theorem ptEv_relToAbs_pdCohMap (Z : RealBundle B F ι) {W U : Set B} (hWU : W ⊆ U)
    (τ : Work.Thom.PieceCoh Z U 0) (p : ↥(Z.proj ⁻¹' W)) :
    Work.Thom.ptEv p
        ((Work.Thom.relToAbs ℤ (pieceZeroZ Z W) 0).hom
          ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) 0).hom τ))
      = Work.Thom.ptEv (pieceInclZ Z W U hWU p)
          ((Work.Thom.relToAbs ℤ (pieceZeroZ Z U) 0).hom τ) := by
  rw [pdCohMap_relToAbs_apply Z hWU 0 τ]
  exact Work.Thom.ptEv_pullback (pieceInclZ Z W U hWU) p _

/-! ## Surjectivity in degree `0` forces the coefficients to be `±1` -/

/-- **The coefficients of a surjective degree-zero local Thom map are `±1` everywhere.**

If `τ ∈ H^0(X|_W, X|_W∖0)` has surjective local Thom map in degree `0`, then the absolute class
`relToAbs τ` evaluates to `±1` at every point of the piece: the unit class `1` is
`π^*(x) ⌣ relToAbs τ` for some `x` (surjectivity, together with the fact that for a subsingleton
fibre the forgetting map is an isomorphism), and evaluating at a point gives
`ptEv (π p) x · ptEv p (relToAbs τ) = 1`. -/
theorem ptEv_relToAbs_eq_pm_one_of_surjective [Subsingleton F]
    (Z : RealBundle B F ι) {W : Set B} (τ : Work.Thom.PieceCoh Z W 0)
    (hsurj : Function.Surjective (Work.Thom.localThomMap Z 0 W τ 0)) :
    ∀ p : ↥(Z.proj ⁻¹' W),
      Work.Thom.ptEv p ((Work.Thom.relToAbs ℤ (pieceZeroZ Z W) 0).hom τ) = 1
      ∨ Work.Thom.ptEv p ((Work.Thom.relToAbs ℤ (pieceZeroZ Z W) 0).hom τ) = -1 := by
  intro p
  obtain ⟨t, ht⟩ :=
    (bijective_relToAbs_of_eq_empty (pieceZeroZ_eq_empty Z W) 0).2
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))))
  obtain ⟨x, hx⟩ := hsurj t
  have key : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) 0 0
      ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ 0).hom x)
      ((Work.Thom.relToAbs ℤ (pieceZeroZ Z W) 0).hom τ)
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) := by
    rw [← ht, ← hx]
    rw [← Work.Thom.mixedCup_relToAbs (pieceZeroZ Z W) 0 0
      ((Work.Thom.CohMap (Work.Thom.pieceProj Z W) ℤ 0).hom x) τ]
    rw [Work.Thom.localThomMap_apply]
  have h1 : Work.Thom.ptEv p
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))) = 1 :=
    Work.Thom.ptEv_one p
  rw [← key] at h1
  rw [Work.Thom.ptEv_cup] at h1
  rw [Work.Thom.ptEv_pullback] at h1
  exact Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact h1)

/-! ## Degree-zero classes with `±1` evaluations are units -/

/-- A degree-zero class evaluating to `±1` at every point is an involution of the cohomology
ring. -/
theorem cup_self_eq_oneH_of_ptEv_z {X : Type} [TopologicalSpace X] (c : Work.Thom.Coh ℤ 0 X)
    (h : ∀ p : X, Work.Thom.ptEv p c = 1 ∨ Work.Thom.ptEv p c = -1) :
    Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 0 c c
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X)) := by
  refine Work.Thom.ptEv_ext (fun p => ?_)
  rcases h p with h1 | h1
  · rw [Work.Thom.ptEv_cup, h1, mul_one, Work.Thom.ptEv_one]
  · rw [Work.Thom.ptEv_cup, h1, Work.Thom.ptEv_one]
    norm_num

/-- **Cupping with an involution of `H⁰` is bijective in every degree.** -/
theorem bijective_cup_of_involution_z {X : Type} [TopologicalSpace X] (c : Work.Thom.Coh ℤ 0 X)
    (hc : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 0 c c
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) (k : ℕ) :
    Function.Bijective (fun x : Work.Thom.Coh ℤ k X =>
      Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) k 0 x c) := by
  have hinv : ∀ y : Work.Thom.Coh ℤ k X,
      Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) k 0
        (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) k 0 y c) c = y := by
    intro y
    have h1 := Work.Cohomology.cupH'_assoc ℤ (TopCat.toSSet.obj (TopCat.of X)) k 0 0 y c c
    rw [hc] at h1
    rw [Work.Cohomology.cupH'_one_right] at h1
    exact h1
  refine ⟨fun x y hxy => ?_,
    fun y => ⟨Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) k 0 y c, hinv y⟩⟩
  have h2 := congrArg (fun w => Work.Cohomology.cupH' ℤ
    (TopCat.toSSet.obj (TopCat.of X)) k 0 w c) hxy
  rwa [hinv x, hinv y] at h2

/-! ## The projection of a rank-`0` piece is a homeomorphism -/

/-- The pullback along a homeomorphism is bijective. -/
theorem bijective_CohMap_homeomorph_z {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ) : Function.Bijective (Work.Thom.CohMap (e : C(X, Y)) ℤ k).hom := by
  have h1 : Work.Thom.CohMap (e.symm : C(Y, X)) ℤ k ≫ Work.Thom.CohMap (e : C(X, Y)) ℤ k
      = 𝟙 (Work.Thom.Coh ℤ k X) := by
    rw [← Work.Thom.CohMap_comp (e : C(X, Y)) (e.symm : C(Y, X))]
    have hc : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
      ext x; exact e.symm_apply_apply x
    rw [hc, Work.Thom.CohMap_id]
  have h2 : Work.Thom.CohMap (e : C(X, Y)) ℤ k ≫ Work.Thom.CohMap (e.symm : C(Y, X)) ℤ k
      = 𝟙 (Work.Thom.Coh ℤ k Y) := by
    rw [← Work.Thom.CohMap_comp (e.symm : C(Y, X)) (e : C(X, Y))]
    have hc : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
      ext x; exact e.apply_symm_apply x
    rw [hc, Work.Thom.CohMap_id]
  have hl1 : (Work.Thom.CohMap (e.symm : C(Y, X)) ℤ k).hom.comp
      (Work.Thom.CohMap (e : C(X, Y)) ℤ k).hom = LinearMap.id := by
    have := congrArg ModuleCat.Hom.hom h2
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  have hl2 : (Work.Thom.CohMap (e : C(X, Y)) ℤ k).hom.comp
      (Work.Thom.CohMap (e.symm : C(Y, X)) ℤ k).hom = LinearMap.id := by
    have := congrArg ModuleCat.Hom.hom h1
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  constructor
  · intro a b hab
    have ha := LinearMap.congr_fun hl1 a
    have hb := LinearMap.congr_fun hl1 b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [hab] at ha
    exact ha.symm.trans hb
  · intro b
    exact ⟨(Work.Thom.CohMap (e.symm : C(Y, X)) ℤ k).hom b, LinearMap.congr_fun hl2 b⟩

/-- The restriction of the zero section to a piece of the base. -/
def pieceZeroSectionZ (Z : RealBundle B F ι) (U : Set B) : C(↥U, ↥(Z.proj ⁻¹' U)) :=
  ⟨fun b => ⟨Work.Thom.zeroSection Z b.1, by simpa using b.2⟩,
    Continuous.subtype_mk ((Work.Thom.zeroSection Z).continuous.comp continuous_subtype_val)
      (fun b => by simpa using b.2)⟩

theorem pieceZeroSectionZ_apply (Z : RealBundle B F ι) (U : Set B) (b : ↥U) :
    ((pieceZeroSectionZ Z U b : ↥(Z.proj ⁻¹' U)) : Z.TotalSpace)
      = Work.Thom.zeroSection Z b.1 := rfl

/-- **For a subsingleton fibre the projection of a piece is a homeomorphism** (with inverse the
restriction of the zero section). -/
def pieceHomeoZ (Z : RealBundle B F ι) [Subsingleton F] (U : Set B) :
    ↥(Z.proj ⁻¹' U) ≃ₜ ↥U where
  toFun := fun p => Work.Thom.pieceProj Z U p
  invFun := fun b => pieceZeroSectionZ Z U b
  left_inv := fun p => by
    apply Subtype.ext
    apply Bundle.TotalSpace.ext
    · rfl
    · exact heq_of_eq (Subsingleton.elim
        (show F from (Work.Thom.zeroSection Z (Z.proj p.1)).2) (show F from p.1.2))
  right_inv := fun b => by
    apply Subtype.ext
    rfl
  continuous_toFun := (Work.Thom.pieceProj Z U).continuous
  continuous_invFun := (pieceZeroSectionZ Z U).continuous

/-- **The projection of a rank-`0` piece is an isomorphism on cohomology.** -/
theorem bijective_CohMap_pieceProj_zero (Z : RealBundle B F ι) [Subsingleton F] (U : Set B)
    (k : ℕ) : Function.Bijective ((Work.Thom.CohMap (Work.Thom.pieceProj Z U) ℤ k).hom) := by
  have hb := bijective_CohMap_homeomorph_z (pieceHomeoZ Z U) k
  have he : ((pieceHomeoZ Z U : ↥(Z.proj ⁻¹' U) ≃ₜ ↥U) : C(↥(Z.proj ⁻¹' U), ↥U))
      = Work.Thom.pieceProj Z U := by
    ext p; rfl
  rwa [he] at hb

/-! ## The main theorem -/

theorem localThom_iUnion_of_fibreGenerator_zero {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (σ : Work.Thom.OpenThom Z 0)
    (h0 : Module.finrank ℝ F = 0)
    (C : Set (Set B)) (hC : ∀ W ∈ C, IsOpen W)
    (hchain : ∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' ∨ W' ⊆ W)
    (h : ∀ W (hW : W ∈ C), ∀ k, Function.Bijective (Work.Thom.localThomMap Z 0 W
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (⋃₀ C)) (Z.proj ⁻¹' W) (Set.preimage_mono (Set.subset_sUnion_of_mem hW)) 0).hom ((Work.Thom.PieceRes Z (⋃₀ C) 0).hom σ)) k)) :
    ∀ k, Function.Bijective (Work.Thom.localThomMap Z 0 (⋃₀ C)
        ((Work.Thom.PieceRes Z (⋃₀ C) 0).hom σ) k) := by
  haveI hF : Subsingleton F := subsingleton_of_finrank_zero h0
  let τ : Work.Thom.PieceCoh Z (⋃₀ C) 0 := (Work.Thom.PieceRes Z (⋃₀ C) 0).hom σ
  let c : Work.Thom.Coh ℤ 0 ↥(Z.proj ⁻¹' (⋃₀ C)) :=
    (Work.Thom.relToAbs ℤ (pieceZeroZ Z (⋃₀ C)) 0).hom τ
  -- the evaluations of `c` are `±1` at every point of the piece over the union
  have hpt : ∀ p : ↥(Z.proj ⁻¹' (⋃₀ C)),
      Work.Thom.ptEv p c = 1 ∨ Work.Thom.ptEv p c = -1 := by
    intro p
    obtain ⟨W, hW, hpW⟩ := Set.mem_sUnion.mp p.2
    have hWU : W ⊆ ⋃₀ C := Set.subset_sUnion_of_mem hW
    let pW : ↥(Z.proj ⁻¹' W) := ⟨p.1, hpW⟩
    have h2' := ptEv_relToAbs_eq_pm_one_of_surjective Z
      ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃₀ C)) (Z.proj ⁻¹' W) (Set.preimage_mono hWU) 0).hom τ)
      (h W hW 0).2 pW
    rw [ptEv_relToAbs_pdCohMap Z hWU τ pW] at h2'
    have h2 : Work.Thom.ptEv (pieceInclZ Z W (⋃₀ C) hWU pW) c = 1
        ∨ Work.Thom.ptEv (pieceInclZ Z W (⋃₀ C) hWU pW) c = -1 := h2'
    rwa [show pieceInclZ Z W (⋃₀ C) hWU pW = p from Subtype.ext rfl] at h2
  have hc : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' (⋃₀ C)))) 0 0 c c
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' (⋃₀ C)))) :=
    cup_self_eq_oneH_of_ptEv_z c hpt
  intro k
  have hcup := bijective_cup_of_involution_z c hc k
  have hπ := bijective_CohMap_pieceProj_zero Z (⋃₀ C) k
  have hrel : ∀ x : Work.Thom.Coh ℤ k ↥(⋃₀ C),
      (Work.Thom.relToAbs ℤ (pieceZeroZ Z (⋃₀ C)) k).hom
          (Work.Thom.localThomMap Z 0 (⋃₀ C) τ k x)
        = Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' (⋃₀ C)))) k 0
            ((Work.Thom.CohMap (Work.Thom.pieceProj Z (⋃₀ C)) ℤ k).hom x) c := by
    intro x
    rw [Work.Thom.localThomMap_apply]
    exact Work.Thom.mixedCup_relToAbs (pieceZeroZ Z (⋃₀ C)) k 0
      ((Work.Thom.CohMap (Work.Thom.pieceProj Z (⋃₀ C)) ℤ k).hom x) τ
  have hrelb : Function.Bijective
      ((Work.Thom.relToAbs ℤ (pieceZeroZ Z (⋃₀ C)) k).hom) :=
    bijective_relToAbs_of_eq_empty (pieceZeroZ_eq_empty Z (⋃₀ C)) k
  constructor
  · intro x y hxy
    have h1 : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' (⋃₀ C)))) k 0
          ((Work.Thom.CohMap (Work.Thom.pieceProj Z (⋃₀ C)) ℤ k).hom x) c
        = Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' (⋃₀ C)))) k 0
          ((Work.Thom.CohMap (Work.Thom.pieceProj Z (⋃₀ C)) ℤ k).hom y) c := by
      rw [← hrel x, ← hrel y, hxy]
    exact hπ.1 (hcup.1 h1)
  · intro z
    obtain ⟨w, hw⟩ := hcup.2 ((Work.Thom.relToAbs ℤ (pieceZeroZ Z (⋃₀ C)) k).hom z)
    have hw' : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' (⋃₀ C))))
          k 0 w c = (Work.Thom.relToAbs ℤ (pieceZeroZ Z (⋃₀ C)) k).hom z := hw
    obtain ⟨x, hx⟩ := hπ.2 w
    refine ⟨x, ?_⟩
    apply hrelb.1
    rw [hrel x, hx, hw']

end

end Work.ThomBordism
