import Mathlib
import Submission.Work.PTGeometric.HOFEuclid
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.PTGeometric.eucFam_germ_ball
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationPos
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationNeg
import Submission.Work.ThomBordism.FrameSigns.relKronH_natural
import Submission.Work.ThomBordism.FrameSigns.Defs
import Submission.Work.Tubular.relKronH_exists_eval_one
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.Cohomology.euclideanLocalHomologyTop
import Submission.Work.Cohomology.euclideanLocalHomologyZero
import Submission.Work.Cohomology.euclidean_relChains_top_homology_free
import Submission.Work.Thom.relCohMap_comp
import Submission.Work.Thom.Orientation.Reflection
import Submission.Work.ThomBordism.PosAtlas.cohLinearAction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.ThomBordism.PosAtlas



noncomputable section

/-- The model space `ℝ⁹`. -/
abbrev X9 : Type := EuclideanSpace ℝ (Fin 9)

/-! ## The local homology of `ℝ⁹` at a point is free in every degree

This is the freeness input of the relative-Kronecker-pairing duality `Work.Tubular.exists_relKronH_eval_iso`:
in the top degree `9` the group is free by `Work.Cohomology.euclidean_relChains_top_homology_free`, and
in every other degree it vanishes by `Work.Cohomology.euclideanLocalHomologyZero`. -/

theorem localH9_free :
    ∀ j : ℕ, Module.Free ℤ
      ↥((Work.Cohomology.relChains (TopCat.of X9) {v : X9 | v ≠ 0}).homology j) := by
  intro j
  rcases eq_or_ne j 9 with rfl | hj
  · exact Work.Cohomology.euclidean_relChains_top_homology_free (N := 9) (by norm_num)
      {0} isCompact_singleton
  · have hz : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.relChains (TopCat.of X9) {v : X9 | v ≠ 0}).homology j) :=
      Work.Cohomology.euclideanLocalHomologyZero 9 j (by norm_num) hj
    have h0 : (𝟙 ((Work.Cohomology.relChains (TopCat.of X9) {v : X9 | v ≠ 0}).homology j)) = 0 :=
      (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mp hz
    haveI : Subsingleton
        ↥((Work.Cohomology.relChains (TopCat.of X9) {v : X9 | v ≠ 0}).homology j) :=
      ⟨fun x y => by
        have hx : x = 0 := by
          have h := congrArg (fun (φ : (Work.Cohomology.relChains (TopCat.of X9)
              {v : X9 | v ≠ 0}).homology j ⟶
              (Work.Cohomology.relChains (TopCat.of X9) {v : X9 | v ≠ 0}).homology j) =>
            (ConcreteCategory.hom φ) x) h0
          simpa using h
        have hy : y = 0 := by
          have h := congrArg (fun (φ : (Work.Cohomology.relChains (TopCat.of X9)
              {v : X9 | v ≠ 0}).homology j ⟶
              (Work.Cohomology.relChains (TopCat.of X9) {v : X9 | v ≠ 0}).homology j) =>
            (ConcreteCategory.hom φ) y) h0
          simpa using h
        rw [hx, hy]⟩
    exact Module.Free.of_subsingleton ℤ _

/-! ## The relative chain map only depends on the value of the pair map

`Work.Cohomology.relChainsMapOf` takes the induced map `g` on the subspaces and a proof of the
compatibility; the proof is irrelevant, and equal maps induce the same chain map. -/

theorem relChainsMapOf_congr_map {X Y : TopCat} {A : Set X} {B : Set Y} {f : X ⟶ Y}
    {g g' : TopCat.of A ⟶ TopCat.of B}
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f = g' ≫ Work.Cohomology.subtypeIncl Y B)
    (hg : g = g') :
    Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf X Y A B f g' w' := by
  subst hg
  unfold Work.Cohomology.relChainsMapOf
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).mp
  rw [Work.Cohomology.cokernel_π_map]

/-- The translational behaviour of `eucFam` in the "singleton" spelling used below: the
translation by `c` carries the generator at `v` to the generator at `w = v + c`. -/
theorem eucFam_translation_singleton (c v w : X9) (hw : w = v + c)
    (hf : ∀ x : X9, x ∉ ({v} : Set X9) → Work.PTGeometric.HOF.eucSub c x ∉ ({w} : Set X9)) :
    Work.PTGeometric.HOF.RelHmapOf 9 (Work.PTGeometric.HOF.eucSub c) ({v} : Set X9) ({w} : Set X9)
        hf (Work.PTGeometric.HOF.eucFam 9 (by norm_num) v)
      = Work.PTGeometric.HOF.eucFam 9 (by norm_num) w :=
  Work.PTGeometric.eucFam_translation' (by norm_num) c v w hw hf


/-- The orientation character of a linear map of `ℝ⁹`: `1` if the determinant is positive and `-1`
otherwise (`-1` also in the degenerate case `det = 0`, which never occurs below). -/
def orSign (A : X9 →L[ℝ] X9) : ℤ := if 0 < LinearMap.det A.toLinearMap then (1 : ℤ) else -1

/-! ## The origin case

The core of the proof: pairing with a primitive cohomology class
(`Work.Tubular.relKronH_exists_eval_one`) turns the orientation character of the action on the local
*cohomology* into the action on the local *homology* generator.  The cohomological input is the
hypothesis `hcoh`. -/

theorem eucFam_linear_action_zero_of_coh
    (A : X9 →L[ℝ] X9) (hA : Function.Bijective A)
    (hpunct : ∀ x ∈ ({v : X9 | v ≠ 0} : Set X9),
      (A : C(X9, X9)) x ∈ ({v : X9 | v ≠ 0} : Set X9))
    (hcoh : ∀ ξ : Work.Thom.RelCoh ℤ 9 X9 ({v : X9 | v ≠ 0}),
      (Work.Thom.relCohMap (A : C(X9, X9)) ({v : X9 | v ≠ 0}) ({v : X9 | v ≠ 0}) hpunct ℤ 9).hom ξ
        = orSign A • ξ)
    (hmem : ∀ x : X9, x ∉ ({0} : Set X9) →
      (TopCat.ofHom (A : C(X9, X9))) x ∉ ({0} : Set X9)) :
    Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
        ({0} : Set X9) ({0} : Set X9) hmem
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num) 0)
      = orSign A • Work.PTGeometric.HOF.eucFam 9 (by norm_num) 0 := by
  classical
  have h9 : (1 : ℕ) ≤ 9 := by norm_num
  obtain ⟨eM⟩ := Work.Cohomology.euclideanLocalHomologyTop 9 (by norm_num)
  let e : Work.Orient.LocH (TopCat.of X9) 9 (0 : X9) ≃ₗ[ℤ] ℤ := eM.toLinearEquiv
  obtain ⟨β, hβ⟩ :=
    Work.Tubular.relKronH_exists_eval_one (n := 9) (A := {v : X9 | v ≠ 0}) localH9_free e
  have hgen : Submodule.span ℤ ({Work.PTGeometric.HOF.eucFam 9 h9 0} :
      Set (Work.Orient.LocH (TopCat.of X9) 9 (0 : X9))) = ⊤ :=
    Work.PTGeometric.HOF.eucFam_gen 9 (by norm_num) 0
  -- the generator pairs nontrivially with `β`
  have hbne : (Work.Tubular.relKronH (TopCat.of X9) {v : X9 | v ≠ 0} 9) β
      (Work.PTGeometric.HOF.eucFam 9 h9 0) ≠ 0 := by
    rcases Work.PTGeometric.HOF.iso_gen_pm_one hgen e with hc | hc
    · have h1 : Work.PTGeometric.HOF.eucFam 9 h9 0 = e.symm 1 := by
        rw [← hc]
        exact (e.symm_apply_apply _).symm
      rw [h1, hβ]; norm_num
    · have h1 : Work.PTGeometric.HOF.eucFam 9 h9 0 = e.symm (-1 : ℤ) := by
        rw [← hc]
        exact (e.symm_apply_apply _).symm
      rw [h1, show e.symm (-1 : ℤ) = - e.symm 1 from map_neg _ 1, map_neg, hβ]
      norm_num
  -- the naturality of the pairing, in the `RelHmapOf` normal form
  have hnat := Work.ThomBordism.FrameSigns.relKronH_natural (X := TopCat.of X9) (Y := TopCat.of X9)
      (A := ({v : X9 | v ≠ 0})) (B := ({v : X9 | v ≠ 0}))
      (f := (A : C(X9, X9))) hpunct 9 (b := β)
      (z := Work.PTGeometric.HOF.eucFam 9 h9 0)
  have hnat' : (Work.Tubular.relKronH (TopCat.of X9) {v : X9 | v ≠ 0} 9)
      (((Work.Thom.relCohMap (A : C(X9, X9)) ({v : X9 | v ≠ 0}) ({v : X9 | v ≠ 0}) hpunct
        ℤ 9).hom) β)
      (Work.PTGeometric.HOF.eucFam 9 h9 0)
      = (Work.Tubular.relKronH (TopCat.of X9) {v : X9 | v ≠ 0} 9) β
        (Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
          ({0} : Set X9) ({0} : Set X9) hmem
          (Work.PTGeometric.HOF.eucFam 9 h9 0)) := hnat
  -- the action on cohomology
  have hL : (Work.Tubular.relKronH (TopCat.of X9) {v : X9 | v ≠ 0} 9)
      (((Work.Thom.relCohMap (A : C(X9, X9)) ({v : X9 | v ≠ 0}) ({v : X9 | v ≠ 0}) hpunct
        ℤ 9).hom) β)
      (Work.PTGeometric.HOF.eucFam 9 h9 0)
      = orSign A * (Work.Tubular.relKronH (TopCat.of X9) {v : X9 | v ≠ 0} 9) β
          (Work.PTGeometric.HOF.eucFam 9 h9 0) := by
    rw [hcoh β, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  -- the coefficient of the action on the generator
  have hmem' : Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
      ({0} : Set X9) ({0} : Set X9) hmem (Work.PTGeometric.HOF.eucFam 9 h9 0)
      ∈ Submodule.span ℤ ({Work.PTGeometric.HOF.eucFam 9 h9 0} :
        Set (Work.Orient.LocH (TopCat.of X9) 9 (0 : X9))) := by
    rw [hgen]; exact Submodule.mem_top
  obtain ⟨k, hk0⟩ := (Submodule.mem_span_singleton.mp hmem')
  have hk : k • (Work.PTGeometric.HOF.eucFam 9 h9 0)
      = Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
          ({0} : Set X9) ({0} : Set X9) hmem (Work.PTGeometric.HOF.eucFam 9 h9 0) := by
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ
      (↥(Work.Orient.LocH (TopCat.of X9) 9 (0 : X9)))) k (Work.PTGeometric.HOF.eucFam 9 h9 0)]
    exact hk0
  have hkσ : k = orSign A := by
    have h1 : orSign A * (Work.Tubular.relKronH (TopCat.of X9) {v : X9 | v ≠ 0} 9) β
          (Work.PTGeometric.HOF.eucFam 9 h9 0)
        = k * (Work.Tubular.relKronH (TopCat.of X9) {v : X9 | v ≠ 0} 9) β
          (Work.PTGeometric.HOF.eucFam 9 h9 0) := by
      rw [← hL, hnat', ← hk, map_zsmul, Int.zsmul_eq_mul]
    exact (mul_right_cancel₀ hbne h1).symm
  rw [← hk, hkσ]


/-! ## Moving the base point

The origin case above is transported to an arbitrary base point `a` by observing that the map
`A` factors as `A = T(A a) ∘ A ∘ T(-a)` (as a map of the pair `({a}, {A a})` through the pairs
`({a},{0})`, `({0},{0})`, `({0},{A a})`), together with the translation invariance of `eucFam`. -/

theorem eucFam_linear_action_of_zero
    (A : X9 →L[ℝ] X9) (hA : Function.Bijective A)
    (hzero : ∀ (B : X9 →L[ℝ] X9) (hB : Function.Bijective B)
      (hmem : ∀ x : X9, x ∉ ({0} : Set X9) →
        (TopCat.ofHom (B : C(X9, X9))) x ∉ ({0} : Set X9)),
      Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (B : C(X9, X9)))
          ({0} : Set X9) ({0} : Set X9) hmem
          (Work.PTGeometric.HOF.eucFam 9 (by norm_num) 0)
        = orSign B • Work.PTGeometric.HOF.eucFam 9 (by norm_num) 0)
    (a : X9)
    (hmemA : ∀ x : X9, x ∉ ({a} : Set X9) →
      (TopCat.ofHom (A : C(X9, X9))) x ∉ ({A a} : Set X9)) :
    Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
        ({a} : Set X9) ({A a} : Set X9) hmemA
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num) a)
      = orSign A • Work.PTGeometric.HOF.eucFam 9 (by norm_num) (A a) := by
  have h9 : (1 : ℕ) ≤ 9 := by norm_num
  -- the pair conditions
  have hmem0 : ∀ x : X9, x ∉ ({0} : Set X9) →
      (TopCat.ofHom (A : C(X9, X9))) x ∉ ({0} : Set X9) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    exact hx (hA.1 (by simpa using h))
  have hsub1 : ∀ x : X9, x ∉ ({a} : Set X9) →
      (Work.PTGeometric.HOF.eucSub (-a)) x ∉ ({0} : Set X9) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    refine hx ?_
    have h'' : x + (-a) + a = 0 + a := congrArg (fun y : X9 => y + a) h
    rwa [add_assoc, neg_add_cancel, add_zero, zero_add] at h''
  have hsub3 : ∀ x : X9, x ∉ ({0} : Set X9) →
      (Work.PTGeometric.HOF.eucSub (A a)) x ∉ ({A a} : Set X9) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    exact hx (add_right_cancel (by rw [zero_add]; exact h))
  -- the factorisation of the map `A`
  have hcmp : (Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9))) ≫
      Work.PTGeometric.HOF.eucSub (A a) = TopCat.ofHom (A : C(X9, X9)) := by
    apply TopCat.ext
    intro x
    show A (x + (-a)) + A a = A x
    rw [map_add, map_neg]
    abel
  have hpair : ∀ x : X9, x ∉ ({a} : Set X9) →
      ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9))) ≫
        Work.PTGeometric.HOF.eucSub (A a)) x ∉ ({A a} : Set X9) := by
    intro x hx
    have hx' : ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9))) ≫
        Work.PTGeometric.HOF.eucSub (A a)) x = (TopCat.ofHom (A : C(X9, X9))) x := by
      rw [hcmp]
    rw [hx']
    exact hmemA x hx
  -- functoriality of the induced map
  have hgf1 : ∀ x : X9, x ∉ ({a} : Set X9) →
      (Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9))) x ∉ ({0} : Set X9) :=
    fun x hx => hmem0 (Work.PTGeometric.HOF.eucSub (-a) x) (hsub1 x hx)
  have hgf2 : ∀ x : X9, x ∉ ({a} : Set X9) → ((Work.PTGeometric.HOF.eucSub (-a) ≫
      TopCat.ofHom (A : C(X9, X9))) ≫ Work.PTGeometric.HOF.eucSub (A a)) x ∉ ({A a} : Set X9) :=
    hpair
  have hcomp1 : (Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
        ({0} : Set X9) ({0} : Set X9) hmem0).comp
      (Work.PTGeometric.HOF.RelHmapOf 9 (Work.PTGeometric.HOF.eucSub (-a))
        ({a} : Set X9) ({0} : Set X9) hsub1)
      = Work.PTGeometric.HOF.RelHmapOf 9
          (Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9)))
          ({a} : Set X9) ({0} : Set X9) hgf1 :=
    Work.PTGeometric.HOF.RelHmapOf_comp (n := 9)
      (f := Work.PTGeometric.HOF.eucSub (-a)) (g := TopCat.ofHom (A : C(X9, X9)))
      (K := ({a} : Set X9)) (K' := ({0} : Set X9)) (K'' := ({0} : Set X9))
      hsub1 hmem0 hgf1
  have hcomp2 : (Work.PTGeometric.HOF.RelHmapOf 9
        (Work.PTGeometric.HOF.eucSub (A a)) ({0} : Set X9) ({A a} : Set X9) hsub3).comp
      (Work.PTGeometric.HOF.RelHmapOf 9
        (Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9)))
        ({a} : Set X9) ({0} : Set X9) hgf1)
      = Work.PTGeometric.HOF.RelHmapOf 9
          ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9))) ≫
            Work.PTGeometric.HOF.eucSub (A a))
          ({a} : Set X9) ({A a} : Set X9) hgf2 :=
    Work.PTGeometric.HOF.RelHmapOf_comp (n := 9)
      (f := Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9)))
      (g := Work.PTGeometric.HOF.eucSub (A a))
      (K := ({a} : Set X9)) (K' := ({0} : Set X9)) (K'' := ({A a} : Set X9))
      hgf1 hsub3 hgf2
  have hcongr : Work.PTGeometric.HOF.RelHmapOf 9
      ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9))) ≫
        Work.PTGeometric.HOF.eucSub (A a)) ({a} : Set X9) ({A a} : Set X9) hpair
      = Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
          ({a} : Set X9) ({A a} : Set X9) hmemA :=
    Work.PTGeometric.HOF.RelHmapOf_congr hcmp hpair hmemA
  -- the two translations
  have hta : (Work.PTGeometric.HOF.RelHmapOf 9 (Work.PTGeometric.HOF.eucSub (-a))
      ({a} : Set X9) ({0} : Set X9) hsub1) (Work.PTGeometric.HOF.eucFam 9 h9 a)
      = Work.PTGeometric.HOF.eucFam 9 h9 0 :=
    eucFam_translation_singleton (-a) a 0 (add_neg_cancel a).symm hsub1
  have htb : (Work.PTGeometric.HOF.RelHmapOf 9 (Work.PTGeometric.HOF.eucSub (A a))
      ({0} : Set X9) ({A a} : Set X9) hsub3) (Work.PTGeometric.HOF.eucFam 9 h9 0)
      = Work.PTGeometric.HOF.eucFam 9 h9 (A a) :=
    eucFam_translation_singleton (A a) 0 (A a) (zero_add (A a)).symm hsub3
  have h0 := hzero A hA hmem0
  calc Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
        ({a} : Set X9) ({A a} : Set X9) hmemA (Work.PTGeometric.HOF.eucFam 9 h9 a)
      = Work.PTGeometric.HOF.RelHmapOf 9
          ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(X9, X9))) ≫
            Work.PTGeometric.HOF.eucSub (A a))
          ({a} : Set X9) ({A a} : Set X9) hpair (Work.PTGeometric.HOF.eucFam 9 h9 a) :=
        LinearMap.congr_fun hcongr.symm _
    _ = (Work.PTGeometric.HOF.RelHmapOf 9 (Work.PTGeometric.HOF.eucSub (A a))
          ({0} : Set X9) ({A a} : Set X9) hsub3)
          ((Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
            ({0} : Set X9) ({0} : Set X9) hmem0)
            ((Work.PTGeometric.HOF.RelHmapOf 9 (Work.PTGeometric.HOF.eucSub (-a))
              ({a} : Set X9) ({0} : Set X9) hsub1) (Work.PTGeometric.HOF.eucFam 9 h9 a))) := by
        rw [← hcomp2, ← hcomp1]; rfl
    _ = (Work.PTGeometric.HOF.RelHmapOf 9 (Work.PTGeometric.HOF.eucSub (A a))
          ({0} : Set X9) ({A a} : Set X9) hsub3)
          ((Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
            ({0} : Set X9) ({0} : Set X9) hmem0) (Work.PTGeometric.HOF.eucFam 9 h9 0)) := by
        rw [hta]
    _ = (Work.PTGeometric.HOF.RelHmapOf 9 (Work.PTGeometric.HOF.eucSub (A a))
          ({0} : Set X9) ({A a} : Set X9) hsub3)
          (orSign A • Work.PTGeometric.HOF.eucFam 9 h9 0) := by
        rw [h0]
    _ = orSign A • (Work.PTGeometric.HOF.RelHmapOf 9 (Work.PTGeometric.HOF.eucSub (A a))
          ({0} : Set X9) ({A a} : Set X9) hsub3) (Work.PTGeometric.HOF.eucFam 9 h9 0) := by
        rw [map_zsmul]
    _ = orSign A • Work.PTGeometric.HOF.eucFam 9 h9 (A a) := by
        rw [htb]


theorem eucFam_linear_action
    (A : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9))
    (hA : Function.Bijective A) (a : EuclideanSpace ℝ (Fin 9)) :
    Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom ⟨fun z => A z, A.continuous⟩)
        ({a} : Set (EuclideanSpace ℝ (Fin 9))) ({A a} : Set (EuclideanSpace ℝ (Fin 9)))
        (fun z hz => by
          simp only [Set.mem_singleton_iff] at hz ⊢
          exact fun h => hz (hA.1 h))
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num) a)
      = (if 0 < LinearMap.det A.toLinearMap then (1 : ℤ) else -1)
        • Work.PTGeometric.HOF.eucFam 9 (by norm_num) (A a) := by
  have hmem0 : ∀ x : X9, x ∉ ({0} : Set X9) →
      (TopCat.ofHom (A : C(X9, X9))) x ∉ ({0} : Set X9) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    exact hx (hA.1 (by simpa using h))
  -- the origin case, from the action on the local cohomology
  have hzero : ∀ (B : X9 →L[ℝ] X9) (hB : Function.Bijective B)
      (hmem : ∀ x : X9, x ∉ ({0} : Set X9) →
        (TopCat.ofHom (B : C(X9, X9))) x ∉ ({0} : Set X9)),
      Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (B : C(X9, X9)))
          ({0} : Set X9) ({0} : Set X9) hmem
          (Work.PTGeometric.HOF.eucFam 9 (by norm_num) 0)
        = orSign B • Work.PTGeometric.HOF.eucFam 9 (by norm_num) 0 := by
    intro B hB hmem
    refine eucFam_linear_action_zero_of_coh B hB ?_ ?_ hmem
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      intro h
      exact hx (hB.1 (by simpa using h))
    · intro ξ
      exact Work.ThomBordism.PosAtlas.cohLinearAction (by norm_num) B hB ξ
  -- the pair condition at the base point `a`
  have hmemA : ∀ x : X9, x ∉ ({a} : Set X9) →
      (TopCat.ofHom (A : C(X9, X9))) x ∉ ({A a} : Set X9) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    exact hx (hA.1 (by simpa using h))
  have hmap : TopCat.ofHom ⟨fun z => A z, A.continuous⟩ = TopCat.ofHom (A : C(X9, X9)) := by
    apply TopCat.ext; intro z; rfl
  have hmain := eucFam_linear_action_of_zero A hA hzero a hmemA
  rw [show Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom ⟨fun z => A z, A.continuous⟩)
        ({a} : Set X9) ({A a} : Set X9)
        (fun z hz => by
          simp only [Set.mem_singleton_iff] at hz ⊢
          exact fun h => hz (hA.1 h))
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num) a)
      = Work.PTGeometric.HOF.RelHmapOf 9 (TopCat.ofHom (A : C(X9, X9)))
        ({a} : Set X9) ({A a} : Set X9) hmemA
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num) a) from
      LinearMap.congr_fun (Work.PTGeometric.HOF.RelHmapOf_congr (n := 9) hmap _ _)
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num) a)]
  exact hmain

end

end Work.ThomBordism.PosAtlas
