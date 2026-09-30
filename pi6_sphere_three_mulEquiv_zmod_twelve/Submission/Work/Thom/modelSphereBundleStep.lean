import Mathlib
import Submission.Work.Thom.ModelGeometry
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.CohHomotopyEquiv
import Submission.Work.Thom.mLowerContractible

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# The two hypotheses of the suspension step for the model sphere bundle

This module proves, for the model geometry `X = B × ℝ^{n+1}` of the trivial bundle of rank `n+1`,
`A = B × S^{n+1}` its sphere bundle and `A₁ = B × (mLower n)` the part of the sphere bundle lying
over the closed lower disc `mLower n ⊆ S^{n+1}`, the two hypotheses consumed by
`Work.Thom.suspensionStep_bijective`:

* the restriction `H^*(X) → H^*(A)` is injective (it is split by the pullback along any section
  `B → A`, since `X → B` is a homotopy equivalence), and
* the composite `H^*(X) → H^*(A) → H^*(A₁)` is bijective (the inclusion `A₁ ↪ X` is a homotopy
  equivalence: its inverse collapses the fibre to the lower disc).

The geometric input is `Work.Thom.mLowerContractible`: `mLower n` is contractible.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- The point of `mLower n` supplied by contractibility: the closed lower region is nonempty. -/
theorem nonempty_mLower (n : ℕ) : (mLower n).Nonempty := by
  refine ⟨Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1), ?_⟩
  constructor
  · have h : ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1)‖ ^ 2 = 1 := by
      rw [Work.Morse.snocLp_norm_sq]; simp
    nlinarith [norm_nonneg (Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1))]
  · rw [Work.Morse.snocLp_ofLp_last]; norm_num

/-- `mLower n` consists of unit vectors, so it is contained in the unit sphere `mSph (n+1)`. -/
theorem mLower_subset_mSph (n : ℕ) : mLower n ⊆ mSph (n + 1) := fun _ hv => hv.1

/-- **The inclusion of the lower disc into the trivial bundle is a homotopy equivalence.**

The inclusion `{p : B × ℝ^{n+1} | p.2 ∈ mLower n} ↪ B × ℝ^{n+1}` is a homotopy equivalence: a
homotopy inverse collapses the fibre to a point `y₀ ∈ mLower n`.  The composite
`inclusion ∘ collapse` is `x ↦ (x.1, y₀)`, homotopic to the identity by the straight-line homotopy
in `ℝ^{n+1}`; the composite `collapse ∘ inclusion` moves the fibre point along a nullhomotopy of
the identity of `mLower n`, which exists because `mLower n` is contractible
(`Work.Thom.mLowerContractible`).  The map on the first coordinate is untouched throughout, so
this is not just an abstract homotopy equivalence but the inclusion itself. -/
theorem subtypeMap_mLower_homotopyEquiv (B : Type) [TopologicalSpace B] (n : ℕ) :
    ∃ e : ContinuousMap.HomotopyEquiv
        ↥{p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mLower n}
        (B × EuclideanSpace ℝ (Fin (n + 1))),
      e.toFun = subtypeMap {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mLower n} := by
  set T : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mLower n} with hT
  haveI : ContractibleSpace ↥(mLower n) := mLowerContractible n
  obtain ⟨y0, hy0⟩ := id_nullhomotopic ↥(mLower n)
  have hy0h : (ContinuousMap.id ↥(mLower n)).Homotopic
      (ContinuousMap.const ↥(mLower n) y0) := hy0
  let γ : C(unitInterval × ↥(mLower n), ↥(mLower n)) := hy0h.some.toContinuousMap
  have hγ0 : ∀ z : ↥(mLower n), γ (0, z) = z := fun z => hy0h.some.map_zero_left z
  have hγ1 : ∀ z : ↥(mLower n), γ (1, z) = y0 := fun z => hy0h.some.map_one_left z
  have hcont : Continuous (fun x : B × EuclideanSpace ℝ (Fin (n + 1)) =>
      (⟨(x.1, y0.1), y0.2⟩ : ↥T)) :=
    Continuous.subtype_mk (continuous_fst.prodMk continuous_const) (fun _ => y0.2)
  let h : C(B × EuclideanSpace ℝ (Fin (n + 1)), ↥T) :=
    ⟨fun x => ⟨(x.1, y0.1), y0.2⟩, hcont⟩
  have hμcont : Continuous (fun q : unitInterval × ↥T =>
      (⟨q.2.1.2, q.2.2⟩ : ↥(mLower n))) :=
    Continuous.subtype_mk (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
      (fun q => q.2.2)
  let μ : C(unitInterval × ↥T, ↥(mLower n)) := ⟨fun q => ⟨q.2.1.2, q.2.2⟩, hμcont⟩
  let ν : C(unitInterval × ↥T, unitInterval × ↥(mLower n)) :=
    ⟨fun q => (q.1, μ q), continuous_fst.prodMk μ.continuous⟩
  let γc : C(unitInterval × ↥T, ↥(mLower n)) := γ.comp ν
  have hHcont : Continuous (fun q : unitInterval × ↥T =>
      (⟨(q.2.1.1, (γc q).1), (γc q).2⟩ : ↥T)) :=
    Continuous.subtype_mk
      (((continuous_fst).comp (continuous_subtype_val.comp continuous_snd)).prodMk
        ((continuous_subtype_val).comp γc.continuous))
      (fun q => (γc q).2)
  have H1 : ContinuousMap.Homotopy (ContinuousMap.id ↥T) (h.comp (subtypeMap T)) :=
    { toFun := fun q => ⟨(q.2.1.1, (γc q).1), (γc q).2⟩
      continuous_toFun := hHcont
      map_zero_left := by
        intro p
        apply Subtype.ext
        have hz : γc (0, p) = μ (0, p) := by
          change γ (ν (0, p)) = μ (0, p)
          rw [show ν (0, p) = (0, μ (0, p)) from rfl, hγ0]
        rw [hz]
        rfl
      map_one_left := by
        intro p
        apply Subtype.ext
        have hz : γc (1, p) = y0 := by
          change γ (ν (1, p)) = y0
          rw [show ν (1, p) = (1, μ (1, p)) from rfl, hγ1]
        rw [hz]
        rfl }
  have H2 : ContinuousMap.Homotopy ((subtypeMap T).comp h)
      (ContinuousMap.id (B × EuclideanSpace ℝ (Fin (n + 1)))) :=
    { toFun := fun tx => (tx.2.1, (1 - (tx.1 : ℝ)) • y0.1 + (tx.1 : ℝ) • tx.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro x
        apply Prod.ext
        · rfl
        · show (1 - ((0 : unitInterval) : ℝ)) • y0.1 + ((0 : unitInterval) : ℝ) • x.2
              = ((subtypeMap T) (h x)).2
          rw [show ((subtypeMap T) (h x)).2 = y0.1 from rfl]
          simp
      map_one_left := by
        intro x
        apply Prod.ext
        · rfl
        · show (1 - ((1 : unitInterval) : ℝ)) • y0.1 + ((1 : unitInterval) : ℝ) • x.2 = x.2
          simp }
  refine ⟨ContinuousMap.HomotopyEquiv.mk (subtypeMap T) h ⟨H1.symm⟩ ⟨H2⟩, rfl⟩

/-- **The two hypotheses of the suspension step for the model sphere bundle.**  Let `A := B × sph (n+1)` be the sphere bundle of rank `n+1` as a subspace of `B × ℝ^{n+1}`, and let `A₁ ⊆ A` be the part lying over the lower region `mLower n`.  Then (i) the restriction `H^*(B × ℝ^{n+1}) → H^*(A)` is injective, and (ii) the composite `H^*(B × ℝ^{n+1}) → H^*(A) → H^*(A₁)` is bijective. -/
theorem modelSphereBundleStep (B : Type) [TopologicalSpace B] (n : ℕ) :
    (∀ m, Function.Injective
        ((CohMap (subtypeMap {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)})
          ℤ m).hom))
      ∧ (∀ m, Function.Bijective
        (((CohMap (subtypeMap {q : {p : B × EuclideanSpace ℝ (Fin (n + 1)) |
              p.2 ∈ mSph (n + 1)} | ((q : B × EuclideanSpace ℝ (Fin (n + 1))).2) ∈ mLower n})
            ℤ m).hom).comp
          ((CohMap (subtypeMap {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)})
            ℤ m).hom))) := by
  set S1 : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)} with hS1
  set S2 : Set S1 := {q : S1 | ((q : B × EuclideanSpace ℝ (Fin (n + 1))).2) ∈ mLower n} with hS2
  set A1 : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mLower n} with hA1
  constructor
  · -- (i) the restriction `H^*(X) → H^*(A)` is injective
    intro m
    show Function.Injective ((CohMap (subtypeMap S1) ℤ m).hom)
    -- a point of the sphere, to build a section of the sphere bundle over `B`
    let p0 : EuclideanSpace ℝ (Fin (n + 1)) := Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1)
    have hp0 : p0 ∈ mSph (n + 1) := by
      show ‖p0‖ = 1
      have h : ‖p0‖ ^ 2 = 1 := by
        show ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1)‖ ^ 2 = 1
        rw [Work.Morse.snocLp_norm_sq]; norm_num
      nlinarith [norm_nonneg p0]
    -- the projection `X → B` is a homotopy equivalence (the fibre is contractible)
    let projX : C(B × EuclideanSpace ℝ (Fin (n + 1)), B) := ⟨Prod.fst, continuous_fst⟩
    let sX : C(B, B × EuclideanSpace ℝ (Fin (n + 1))) := ⟨fun b => (b, p0), by fun_prop⟩
    have key : ∀ x : B × EuclideanSpace ℝ (Fin (n + 1)), (sX.comp projX) x = (x.1, p0) := by
      intro x
      simp only [ContinuousMap.comp_apply]
      change sX x.1 = (x.1, p0)
      rfl
    have h1 : (sX.comp projX).Homotopic
        (ContinuousMap.id (B × EuclideanSpace ℝ (Fin (n + 1)))) := by
      refine ⟨⟨fun tx : unitInterval × (B × EuclideanSpace ℝ (Fin (n + 1))) =>
          (tx.2.1, (1 - (tx.1 : ℝ)) • p0 + (tx.1 : ℝ) • tx.2.2), by fun_prop⟩, ?_, ?_⟩
      · intro x; rw [key x]; simp
      · intro x; apply Prod.ext <;> simp
    have h2 : (projX.comp sX).Homotopic (ContinuousMap.id B) := by
      have heq : projX.comp sX = ContinuousMap.id B := by ext b; rfl
      simpa [heq] using ContinuousMap.Homotopic.refl (ContinuousMap.id B)
    let HE : ContinuousMap.HomotopyEquiv (B × EuclideanSpace ℝ (Fin (n + 1))) B :=
      ContinuousMap.HomotopyEquiv.mk projX sX h1 h2
    have hbij : Function.Bijective (CohMap projX ℤ m).hom :=
      bijective_CohMap_of_homotopyEquiv HE ℤ m
    -- the projection of the sphere bundle to `B` has a section, so it is injective on cohomology
    let projA : C(↥S1, B) := projX.comp (subtypeMap S1)
    let sA : C(B, ↥S1) :=
      ⟨fun b => ⟨(b, p0), hp0⟩, Continuous.subtype_mk (continuous_id.prodMk continuous_const)
        (fun _ => hp0)⟩
    have hinj_projA : Function.Injective (CohMap projA ℤ m).hom := by
      have hcomp : (CohMap sA ℤ m).hom.comp (CohMap projA ℤ m).hom
          = (CohMap (projA.comp sA) ℤ m).hom := CohMap_linear_comp sA projA ℤ m
      have hid : projA.comp sA = ContinuousMap.id B := by ext b; rfl
      rw [hid, CohMap_id] at hcomp
      intro x y hxy
      have hx := LinearMap.congr_fun hcomp x
      have hy := LinearMap.congr_fun hcomp y
      simp only [LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at hx hy
      rw [hxy] at hx
      exact hx.symm.trans hy
    have hkey : ∀ z, (CohMap (subtypeMap S1) ℤ m).hom ((CohMap projX ℤ m).hom z)
        = (CohMap projA ℤ m).hom z := by
      intro z
      have := LinearMap.congr_fun (CohMap_linear_comp (subtypeMap S1) projX ℤ m) z
      simpa only [LinearMap.comp_apply] using this
    intro x y hxy
    obtain ⟨x', rfl⟩ := hbij.2 x
    obtain ⟨y', rfl⟩ := hbij.2 y
    have hQ : (CohMap projA ℤ m).hom x' = (CohMap projA ℤ m).hom y' := by
      rw [← hkey x', ← hkey y']; exact hxy
    rw [hinj_projA hQ]
  · -- (ii) the composite `H^*(X) → H^*(A) → H^*(A₁)` is bijective
    intro m
    show Function.Bijective
      (((CohMap (subtypeMap S2) ℤ m).hom).comp ((CohMap (subtypeMap S1) ℤ m).hom))
    let cc : C(↥S2, B × EuclideanSpace ℝ (Fin (n + 1))) :=
      (subtypeMap S1).comp (subtypeMap S2)
    have hcomp : ((CohMap (subtypeMap S2) ℤ m).hom).comp
          ((CohMap (subtypeMap S1) ℤ m).hom) = (CohMap cc ℤ m).hom :=
      CohMap_linear_comp (subtypeMap S2) (subtypeMap S1) ℤ m
    rw [hcomp]
    -- the homeomorphism `A₁ ↪ A ↪ X` is the inclusion `{p | p.2 ∈ mLower n} ↪ X`
    have hsub : mLower n ⊆ mSph (n + 1) := mLower_subset_mSph n
    have hf1 : Continuous (fun p : ↥A1 => (p.1 : B × EuclideanSpace ℝ (Fin (n + 1)))) :=
      continuous_subtype_val
    have hf2 : Continuous (fun q : ↥S2 => ((q : ↥S1) : B × EuclideanSpace ℝ (Fin (n + 1)))) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hcont : Continuous (fun p : ↥A1 => (⟨⟨p.1, hsub p.2⟩, p.2⟩ : ↥S2)) :=
      Continuous.subtype_mk (Continuous.subtype_mk hf1 (fun p => hsub p.2)) (fun p => p.2)
    have hcont2 : Continuous (fun q : ↥S2 =>
        (⟨(q : B × EuclideanSpace ℝ (Fin (n + 1))), q.2⟩ : ↥A1)) :=
      Continuous.subtype_mk hf2 (fun q => q.2)
    let einv : C(↥A1, ↥S2) := ⟨fun p => ⟨⟨p.1, hsub p.2⟩, p.2⟩, hcont⟩
    let e : C(↥S2, ↥A1) := ⟨fun q => ⟨(q : B × EuclideanSpace ℝ (Fin (n + 1))), q.2⟩, hcont2⟩
    have he_left : einv.comp e = ContinuousMap.id ↥S2 := by
      apply ContinuousMap.ext; intro q; apply Subtype.ext; apply Subtype.ext; rfl
    have he_right : e.comp einv = ContinuousMap.id ↥A1 := by
      apply ContinuousMap.ext; intro p; apply Subtype.ext; rfl
    have h1' : (einv.comp e).Homotopic (ContinuousMap.id ↥S2) := by rw [he_left]
    have h2' : (e.comp einv).Homotopic (ContinuousMap.id ↥A1) := by rw [he_right]
    let HE' : ContinuousMap.HomotopyEquiv ↥S2 ↥A1 :=
      ContinuousMap.HomotopyEquiv.mk e einv h1' h2'
    have hbijE : Function.Bijective (CohMap e ℤ m).hom :=
      bijective_CohMap_of_homotopyEquiv HE' ℤ m
    -- the inclusion of the lower disc into `X` is a homotopy equivalence
    obtain ⟨HEA1, hHEA1⟩ := subtypeMap_mLower_homotopyEquiv B n
    have hbijA1 : Function.Bijective (CohMap (subtypeMap A1) ℤ m).hom := by
      have h2 := bijective_CohMap_of_homotopyEquiv HEA1 ℤ m
      rwa [hHEA1] at h2
    have hceq : cc = (subtypeMap A1).comp e := by
      apply ContinuousMap.ext; intro q; rfl
    rw [hceq, ← CohMap_linear_comp e (subtypeMap A1) ℤ m]
    simpa only [LinearMap.coe_comp] using hbijE.comp hbijA1

end

end Work.Thom
