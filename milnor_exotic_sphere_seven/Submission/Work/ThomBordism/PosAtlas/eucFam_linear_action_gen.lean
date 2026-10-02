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

/-!
# The action of a linear bijection of `ℝⁿ` on the Euclidean model family of local generators

This is the general-`n` (`n ≥ 1`) version of `Work.ThomBordism.PosAtlas.eucFam_linear_action`,
which deals with the case `n = 9`.  For a linear bijection `A` of `ℝⁿ` the induced map on local
homology carries the model generator `eucFam n hn a` at `a` to the orientation character
(`1` if `det A > 0`, `-1` otherwise) times the model generator at `A a`.

The proof is the one of the `n = 9` case, with all occurrences of `9` replaced by `n`:

1. **Cohomological input**: `Work.ThomBordism.PosAtlas.cohLinearAction` (already general `n`), the
   action of `A` on `Hⁿ(ℝⁿ, ℝⁿ∖0;ℤ)` is the sign of the determinant.
2. **The origin case**: a duality argument with the relative Kronecker pairing
   (`Work.Tubular.relKronH_exists_eval_one`, `Work.ThomBordism.FrameSigns.relKronH_natural`)
   converts the cohomological character into the homological one, using that the local homology of
   `ℝⁿ` at `0` is free in every degree (`localHn_free_gen`).
3. **The base point**: the factorisation `A = T(A a) ∘ A ∘ T(-a)` together with translation
   invariance of `eucFam` (`Work.PTGeometric.eucFam_translation'`) moves the statement to any `a`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.ThomBordism.PosAtlas

noncomputable section

/-- The model space `ℝⁿ`. -/
abbrev EucN (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-! ## The local homology of `ℝⁿ` at the origin is free in every degree

This is the freeness input of the relative-Kronecker-pairing duality
`Work.Tubular.exists_relKronH_eval_iso`: in the top degree `n` the group is free by
`Work.Cohomology.euclidean_relChains_top_homology_free`, and in every other degree it vanishes by
`Work.Cohomology.euclideanLocalHomologyZero`. -/

theorem localHn_free_gen (n : ℕ) (hn : 1 ≤ n) :
    ∀ j : ℕ, Module.Free ℤ
      ↥((Work.Cohomology.relChains (TopCat.of (EucN n)) {v : EucN n | v ≠ 0}).homology j) := by
  intro j
  rcases eq_or_ne j n with hjn | hj
  · rw [hjn]
    exact Work.Cohomology.euclidean_relChains_top_homology_free hn
      ({0} : Set (EucN n)) isCompact_singleton
  · have hz : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.relChains (TopCat.of (EucN n)) {v : EucN n | v ≠ 0}).homology j) :=
      Work.Cohomology.euclideanLocalHomologyZero n j hn hj
    have h0 : (𝟙 ((Work.Cohomology.relChains (TopCat.of (EucN n))
        {v : EucN n | v ≠ 0}).homology j)) = 0 :=
      (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mp hz
    haveI : Subsingleton
        ↥((Work.Cohomology.relChains (TopCat.of (EucN n)) {v : EucN n | v ≠ 0}).homology j) :=
      ⟨fun x y => by
        have hx : x = 0 := by
          have h := congrArg (fun (φ : (Work.Cohomology.relChains (TopCat.of (EucN n))
              {v : EucN n | v ≠ 0}).homology j ⟶
              (Work.Cohomology.relChains (TopCat.of (EucN n)) {v : EucN n | v ≠ 0}).homology j) =>
            (ConcreteCategory.hom φ) x) h0
          simpa using h
        have hy : y = 0 := by
          have h := congrArg (fun (φ : (Work.Cohomology.relChains (TopCat.of (EucN n))
              {v : EucN n | v ≠ 0}).homology j ⟶
              (Work.Cohomology.relChains (TopCat.of (EucN n)) {v : EucN n | v ≠ 0}).homology j) =>
            (ConcreteCategory.hom φ) y) h0
          simpa using h
        rw [hx, hy]⟩
    exact Module.Free.of_subsingleton ℤ _

/-! ## Translation invariance in the "singleton" spelling -/

/-- The translational behaviour of `eucFam` in the "singleton" spelling used below: the
translation by `c` carries the generator at `v` to the generator at `w = v + c`. -/
theorem eucFam_translation_singleton_gen (n : ℕ) (hn : 1 ≤ n) (c v w : EucN n) (hw : w = v + c)
    (hf : ∀ x : EucN n, x ∉ ({v} : Set (EucN n)) →
      Work.PTGeometric.HOF.eucSub c x ∉ ({w} : Set (EucN n))) :
    Work.PTGeometric.HOF.RelHmapOf n (Work.PTGeometric.HOF.eucSub c) ({v} : Set (EucN n))
        ({w} : Set (EucN n)) hf (Work.PTGeometric.HOF.eucFam n hn v)
      = Work.PTGeometric.HOF.eucFam n hn w :=
  Work.PTGeometric.eucFam_translation' hn c v w hw hf

/-- The orientation character of a linear map of `ℝⁿ`: `1` if the determinant is positive and `-1`
otherwise (`-1` also in the degenerate case `det = 0`, which never occurs below). -/
def orSignGen (n : ℕ) (A : EucN n →L[ℝ] EucN n) : ℤ :=
  if 0 < LinearMap.det A.toLinearMap then (1 : ℤ) else -1

/-! ## The origin case

The core of the proof: pairing with a primitive cohomology class
(`Work.Tubular.relKronH_exists_eval_one`) turns the orientation character of the action on the local
*cohomology* into the action on the local *homology* generator.  The cohomological input is the
hypothesis `hcoh`. -/

theorem eucFam_linear_action_zero_of_coh_gen
    (n : ℕ) (hn : 1 ≤ n)
    (A : EucN n →L[ℝ] EucN n) (hA : Function.Bijective A)
    (hpunct : ∀ x ∈ ({v : EucN n | v ≠ 0} : Set (EucN n)),
      (A : C(EucN n, EucN n)) x ∈ ({v : EucN n | v ≠ 0} : Set (EucN n)))
    (hcoh : ∀ ξ : Work.Thom.RelCoh ℤ n (EucN n) ({v : EucN n | v ≠ 0}),
      (Work.Thom.relCohMap (A : C(EucN n, EucN n)) ({v : EucN n | v ≠ 0})
        ({v : EucN n | v ≠ 0}) hpunct ℤ n).hom ξ
        = orSignGen n A • ξ)
    (hmem : ∀ x : EucN n, x ∉ ({0} : Set (EucN n)) →
      (TopCat.ofHom (A : C(EucN n, EucN n))) x ∉ ({0} : Set (EucN n))) :
    Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
        ({0} : Set (EucN n)) ({0} : Set (EucN n)) hmem
        (Work.PTGeometric.HOF.eucFam n hn 0)
      = orSignGen n A • Work.PTGeometric.HOF.eucFam n hn 0 := by
  classical
  obtain ⟨eM⟩ := Work.Cohomology.euclideanLocalHomologyTop n hn
  let e : Work.Orient.LocH (TopCat.of (EucN n)) n (0 : EucN n) ≃ₗ[ℤ] ℤ := eM.toLinearEquiv
  obtain ⟨β, hβ⟩ :=
    Work.Tubular.relKronH_exists_eval_one (n := n) (A := {v : EucN n | v ≠ 0})
      (localHn_free_gen n hn) e
  have hgen : Submodule.span ℤ ({Work.PTGeometric.HOF.eucFam n hn 0} :
      Set (Work.Orient.LocH (TopCat.of (EucN n)) n (0 : EucN n))) = ⊤ :=
    Work.PTGeometric.HOF.eucFam_gen n hn 0
  -- the generator pairs nontrivially with `β`
  have hbne : (Work.Tubular.relKronH (TopCat.of (EucN n)) {v : EucN n | v ≠ 0} n) β
      (Work.PTGeometric.HOF.eucFam n hn 0) ≠ 0 := by
    rcases Work.PTGeometric.HOF.iso_gen_pm_one hgen e with hc | hc
    · have h1 : Work.PTGeometric.HOF.eucFam n hn 0 = e.symm 1 := by
        rw [← hc]
        exact (e.symm_apply_apply _).symm
      rw [h1, hβ]; norm_num
    · have h1 : Work.PTGeometric.HOF.eucFam n hn 0 = e.symm (-1 : ℤ) := by
        rw [← hc]
        exact (e.symm_apply_apply _).symm
      rw [h1, show e.symm (-1 : ℤ) = - e.symm 1 from map_neg _ 1, map_neg, hβ]
      norm_num
  -- the naturality of the pairing, in the `RelHmapOf` normal form
  have hnat := Work.ThomBordism.FrameSigns.relKronH_natural (X := TopCat.of (EucN n))
      (Y := TopCat.of (EucN n))
      (A := ({v : EucN n | v ≠ 0})) (B := ({v : EucN n | v ≠ 0}))
      (f := (A : C(EucN n, EucN n))) hpunct n (b := β)
      (z := Work.PTGeometric.HOF.eucFam n hn 0)
  have hnat' : (Work.Tubular.relKronH (TopCat.of (EucN n)) {v : EucN n | v ≠ 0} n)
      (((Work.Thom.relCohMap (A : C(EucN n, EucN n)) ({v : EucN n | v ≠ 0})
        ({v : EucN n | v ≠ 0}) hpunct ℤ n).hom) β)
      (Work.PTGeometric.HOF.eucFam n hn 0)
      = (Work.Tubular.relKronH (TopCat.of (EucN n)) {v : EucN n | v ≠ 0} n) β
        (Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
          ({0} : Set (EucN n)) ({0} : Set (EucN n)) hmem
          (Work.PTGeometric.HOF.eucFam n hn 0)) := hnat
  -- the action on cohomology
  have hL : (Work.Tubular.relKronH (TopCat.of (EucN n)) {v : EucN n | v ≠ 0} n)
      (((Work.Thom.relCohMap (A : C(EucN n, EucN n)) ({v : EucN n | v ≠ 0})
        ({v : EucN n | v ≠ 0}) hpunct ℤ n).hom) β)
      (Work.PTGeometric.HOF.eucFam n hn 0)
      = orSignGen n A * (Work.Tubular.relKronH (TopCat.of (EucN n)) {v : EucN n | v ≠ 0} n) β
          (Work.PTGeometric.HOF.eucFam n hn 0) := by
    rw [hcoh β, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  -- the coefficient of the action on the generator
  have hmem' : Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
      ({0} : Set (EucN n)) ({0} : Set (EucN n)) hmem (Work.PTGeometric.HOF.eucFam n hn 0)
      ∈ Submodule.span ℤ ({Work.PTGeometric.HOF.eucFam n hn 0} :
        Set (Work.Orient.LocH (TopCat.of (EucN n)) n (0 : EucN n))) := by
    rw [hgen]; exact Submodule.mem_top
  obtain ⟨k, hk0⟩ := (Submodule.mem_span_singleton.mp hmem')
  have hk : k • (Work.PTGeometric.HOF.eucFam n hn 0)
      = Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
          ({0} : Set (EucN n)) ({0} : Set (EucN n)) hmem (Work.PTGeometric.HOF.eucFam n hn 0) := by
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ
      (↥(Work.Orient.LocH (TopCat.of (EucN n)) n (0 : EucN n)))) k
        (Work.PTGeometric.HOF.eucFam n hn 0)]
    exact hk0
  have hkσ : k = orSignGen n A := by
    have h1 : orSignGen n A * (Work.Tubular.relKronH (TopCat.of (EucN n))
          {v : EucN n | v ≠ 0} n) β (Work.PTGeometric.HOF.eucFam n hn 0)
        = k * (Work.Tubular.relKronH (TopCat.of (EucN n)) {v : EucN n | v ≠ 0} n) β
          (Work.PTGeometric.HOF.eucFam n hn 0) := by
      rw [← hL, hnat', ← hk, map_zsmul, Int.zsmul_eq_mul]
    exact (mul_right_cancel₀ hbne h1).symm
  rw [← hk, hkσ]

/-! ## Moving the base point

The origin case above is transported to an arbitrary base point `a` by observing that the map
`A` factors as `A = T(A a) ∘ A ∘ T(-a)` (as a map of the pair `({a}, {A a})` through the pairs
`({a},{0})`, `({0},{0})`, `({0},{A a})`), together with the translation invariance of `eucFam`. -/

theorem eucFam_linear_action_of_zero_gen
    (n : ℕ) (hn : 1 ≤ n)
    (A : EucN n →L[ℝ] EucN n) (hA : Function.Bijective A)
    (hzero : ∀ (B : EucN n →L[ℝ] EucN n) (hB : Function.Bijective B)
      (hmem : ∀ x : EucN n, x ∉ ({0} : Set (EucN n)) →
        (TopCat.ofHom (B : C(EucN n, EucN n))) x ∉ ({0} : Set (EucN n))),
      Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (B : C(EucN n, EucN n)))
          ({0} : Set (EucN n)) ({0} : Set (EucN n)) hmem
          (Work.PTGeometric.HOF.eucFam n hn 0)
        = orSignGen n B • Work.PTGeometric.HOF.eucFam n hn 0)
    (a : EucN n)
    (hmemA : ∀ x : EucN n, x ∉ ({a} : Set (EucN n)) →
      (TopCat.ofHom (A : C(EucN n, EucN n))) x ∉ ({A a} : Set (EucN n))) :
    Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
        ({a} : Set (EucN n)) ({A a} : Set (EucN n)) hmemA
        (Work.PTGeometric.HOF.eucFam n hn a)
      = orSignGen n A • Work.PTGeometric.HOF.eucFam n hn (A a) := by
  -- the pair conditions
  have hmem0 : ∀ x : EucN n, x ∉ ({0} : Set (EucN n)) →
      (TopCat.ofHom (A : C(EucN n, EucN n))) x ∉ ({0} : Set (EucN n)) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    exact hx (hA.1 (by simpa using h))
  have hsub1 : ∀ x : EucN n, x ∉ ({a} : Set (EucN n)) →
      (Work.PTGeometric.HOF.eucSub (-a)) x ∉ ({0} : Set (EucN n)) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    refine hx ?_
    have h'' : x + (-a) + a = 0 + a := congrArg (fun y : EucN n => y + a) h
    rwa [add_assoc, neg_add_cancel, add_zero, zero_add] at h''
  have hsub3 : ∀ x : EucN n, x ∉ ({0} : Set (EucN n)) →
      (Work.PTGeometric.HOF.eucSub (A a)) x ∉ ({A a} : Set (EucN n)) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    exact hx (add_right_cancel (by rw [zero_add]; exact h))
  -- the factorisation of the map `A`
  have hcmp : (Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n))) ≫
      Work.PTGeometric.HOF.eucSub (A a) = TopCat.ofHom (A : C(EucN n, EucN n)) := by
    apply TopCat.ext
    intro x
    show A (x + (-a)) + A a = A x
    rw [map_add, map_neg]
    abel
  have hpair : ∀ x : EucN n, x ∉ ({a} : Set (EucN n)) →
      ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n))) ≫
        Work.PTGeometric.HOF.eucSub (A a)) x ∉ ({A a} : Set (EucN n)) := by
    intro x hx
    have hx' : ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n))) ≫
        Work.PTGeometric.HOF.eucSub (A a)) x = (TopCat.ofHom (A : C(EucN n, EucN n))) x := by
      rw [hcmp]
    rw [hx']
    exact hmemA x hx
  -- functoriality of the induced map
  have hgf1 : ∀ x : EucN n, x ∉ ({a} : Set (EucN n)) →
      (Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n))) x
        ∉ ({0} : Set (EucN n)) :=
    fun x hx => hmem0 (Work.PTGeometric.HOF.eucSub (-a) x) (hsub1 x hx)
  have hgf2 : ∀ x : EucN n, x ∉ ({a} : Set (EucN n)) → ((Work.PTGeometric.HOF.eucSub (-a) ≫
      TopCat.ofHom (A : C(EucN n, EucN n))) ≫ Work.PTGeometric.HOF.eucSub (A a)) x
        ∉ ({A a} : Set (EucN n)) :=
    hpair
  have hcomp1 : (Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
        ({0} : Set (EucN n)) ({0} : Set (EucN n)) hmem0).comp
      (Work.PTGeometric.HOF.RelHmapOf n (Work.PTGeometric.HOF.eucSub (-a))
        ({a} : Set (EucN n)) ({0} : Set (EucN n)) hsub1)
      = Work.PTGeometric.HOF.RelHmapOf n
          (Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n)))
          ({a} : Set (EucN n)) ({0} : Set (EucN n)) hgf1 :=
    Work.PTGeometric.HOF.RelHmapOf_comp (n := n)
      (f := Work.PTGeometric.HOF.eucSub (-a)) (g := TopCat.ofHom (A : C(EucN n, EucN n)))
      (K := ({a} : Set (EucN n))) (K' := ({0} : Set (EucN n))) (K'' := ({0} : Set (EucN n)))
      hsub1 hmem0 hgf1
  have hcomp2 : (Work.PTGeometric.HOF.RelHmapOf n
        (Work.PTGeometric.HOF.eucSub (A a)) ({0} : Set (EucN n)) ({A a} : Set (EucN n))
        hsub3).comp
      (Work.PTGeometric.HOF.RelHmapOf n
        (Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n)))
        ({a} : Set (EucN n)) ({0} : Set (EucN n)) hgf1)
      = Work.PTGeometric.HOF.RelHmapOf n
          ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n))) ≫
            Work.PTGeometric.HOF.eucSub (A a))
          ({a} : Set (EucN n)) ({A a} : Set (EucN n)) hgf2 :=
    Work.PTGeometric.HOF.RelHmapOf_comp (n := n)
      (f := Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n)))
      (g := Work.PTGeometric.HOF.eucSub (A a))
      (K := ({a} : Set (EucN n))) (K' := ({0} : Set (EucN n))) (K'' := ({A a} : Set (EucN n)))
      hgf1 hsub3 hgf2
  have hcongr : Work.PTGeometric.HOF.RelHmapOf n
      ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n))) ≫
        Work.PTGeometric.HOF.eucSub (A a)) ({a} : Set (EucN n)) ({A a} : Set (EucN n)) hpair
      = Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
          ({a} : Set (EucN n)) ({A a} : Set (EucN n)) hmemA :=
    Work.PTGeometric.HOF.RelHmapOf_congr hcmp hpair hmemA
  -- the two translations
  have hta : (Work.PTGeometric.HOF.RelHmapOf n (Work.PTGeometric.HOF.eucSub (-a))
      ({a} : Set (EucN n)) ({0} : Set (EucN n)) hsub1) (Work.PTGeometric.HOF.eucFam n hn a)
      = Work.PTGeometric.HOF.eucFam n hn 0 :=
    eucFam_translation_singleton_gen n hn (-a) a 0 (add_neg_cancel a).symm hsub1
  have htb : (Work.PTGeometric.HOF.RelHmapOf n (Work.PTGeometric.HOF.eucSub (A a))
      ({0} : Set (EucN n)) ({A a} : Set (EucN n)) hsub3) (Work.PTGeometric.HOF.eucFam n hn 0)
      = Work.PTGeometric.HOF.eucFam n hn (A a) :=
    eucFam_translation_singleton_gen n hn (A a) 0 (A a) (zero_add (A a)).symm hsub3
  have h0 := hzero A hA hmem0
  calc Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
        ({a} : Set (EucN n)) ({A a} : Set (EucN n)) hmemA (Work.PTGeometric.HOF.eucFam n hn a)
      = Work.PTGeometric.HOF.RelHmapOf n
          ((Work.PTGeometric.HOF.eucSub (-a) ≫ TopCat.ofHom (A : C(EucN n, EucN n))) ≫
            Work.PTGeometric.HOF.eucSub (A a))
          ({a} : Set (EucN n)) ({A a} : Set (EucN n)) hpair (Work.PTGeometric.HOF.eucFam n hn a) :=
        LinearMap.congr_fun hcongr.symm _
    _ = (Work.PTGeometric.HOF.RelHmapOf n (Work.PTGeometric.HOF.eucSub (A a))
          ({0} : Set (EucN n)) ({A a} : Set (EucN n)) hsub3)
          ((Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
            ({0} : Set (EucN n)) ({0} : Set (EucN n)) hmem0)
            ((Work.PTGeometric.HOF.RelHmapOf n (Work.PTGeometric.HOF.eucSub (-a))
              ({a} : Set (EucN n)) ({0} : Set (EucN n)) hsub1)
              (Work.PTGeometric.HOF.eucFam n hn a))) := by
        rw [← hcomp2, ← hcomp1]; rfl
    _ = (Work.PTGeometric.HOF.RelHmapOf n (Work.PTGeometric.HOF.eucSub (A a))
          ({0} : Set (EucN n)) ({A a} : Set (EucN n)) hsub3)
          ((Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
            ({0} : Set (EucN n)) ({0} : Set (EucN n)) hmem0) (Work.PTGeometric.HOF.eucFam n hn 0)) := by
        rw [hta]
    _ = (Work.PTGeometric.HOF.RelHmapOf n (Work.PTGeometric.HOF.eucSub (A a))
          ({0} : Set (EucN n)) ({A a} : Set (EucN n)) hsub3)
          (orSignGen n A • Work.PTGeometric.HOF.eucFam n hn 0) := by
        rw [h0]
    _ = orSignGen n A • (Work.PTGeometric.HOF.RelHmapOf n (Work.PTGeometric.HOF.eucSub (A a))
          ({0} : Set (EucN n)) ({A a} : Set (EucN n)) hsub3) (Work.PTGeometric.HOF.eucFam n hn 0) := by
        rw [map_zsmul]
    _ = orSignGen n A • Work.PTGeometric.HOF.eucFam n hn (A a) := by
        rw [htb]


theorem eucFam_linear_action_gen (n : ℕ) (hn : 1 ≤ n)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Function.Bijective A) (a : EuclideanSpace ℝ (Fin n)) :
    Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom ⟨fun z => A z, A.continuous⟩)
        ({a} : Set (EuclideanSpace ℝ (Fin n))) ({A a} : Set (EuclideanSpace ℝ (Fin n)))
        (fun z hz => by
          simp only [Set.mem_singleton_iff] at hz ⊢
          exact fun h => hz (hA.1 h))
        (Work.PTGeometric.HOF.eucFam n hn a)
      = (if 0 < LinearMap.det A.toLinearMap then (1 : ℤ) else -1)
        • Work.PTGeometric.HOF.eucFam n hn (A a) := by
  have hmem0 : ∀ x : EucN n, x ∉ ({0} : Set (EucN n)) →
      (TopCat.ofHom (A : C(EucN n, EucN n))) x ∉ ({0} : Set (EucN n)) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    exact hx (hA.1 (by simpa using h))
  -- the origin case, from the action on the local cohomology
  have hzero : ∀ (B : EucN n →L[ℝ] EucN n) (hB : Function.Bijective B)
      (hmem : ∀ x : EucN n, x ∉ ({0} : Set (EucN n)) →
        (TopCat.ofHom (B : C(EucN n, EucN n))) x ∉ ({0} : Set (EucN n))),
      Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (B : C(EucN n, EucN n)))
          ({0} : Set (EucN n)) ({0} : Set (EucN n)) hmem
          (Work.PTGeometric.HOF.eucFam n hn 0)
        = orSignGen n B • Work.PTGeometric.HOF.eucFam n hn 0 := by
    intro B hB hmem
    refine eucFam_linear_action_zero_of_coh_gen n hn B hB ?_ ?_ hmem
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      intro h
      exact hx (hB.1 (by simpa using h))
    · intro ξ
      exact Work.ThomBordism.PosAtlas.cohLinearAction hn B hB ξ
  -- the pair condition at the base point `a`
  have hmemA : ∀ x : EucN n, x ∉ ({a} : Set (EucN n)) →
      (TopCat.ofHom (A : C(EucN n, EucN n))) x ∉ ({A a} : Set (EucN n)) := by
    intro x hx h
    simp only [Set.mem_singleton_iff] at hx h
    exact hx (hA.1 (by simpa using h))
  have hmap : TopCat.ofHom ⟨fun z => A z, A.continuous⟩ = TopCat.ofHom (A : C(EucN n, EucN n)) := by
    apply TopCat.ext; intro z; rfl
  have hmain := eucFam_linear_action_of_zero_gen n hn A hA hzero a hmemA
  rw [show Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom ⟨fun z => A z, A.continuous⟩)
        ({a} : Set (EucN n)) ({A a} : Set (EucN n))
        (fun z hz => by
          simp only [Set.mem_singleton_iff] at hz ⊢
          exact fun h => hz (hA.1 h))
        (Work.PTGeometric.HOF.eucFam n hn a)
      = Work.PTGeometric.HOF.RelHmapOf n (TopCat.ofHom (A : C(EucN n, EucN n)))
        ({a} : Set (EucN n)) ({A a} : Set (EucN n)) hmemA
        (Work.PTGeometric.HOF.eucFam n hn a) from
      LinearMap.congr_fun (Work.PTGeometric.HOF.RelHmapOf_congr (n := n) hmap _ _)
        (Work.PTGeometric.HOF.eucFam n hn a)]
  exact hmain

end

end Work.ThomBordism.PosAtlas
