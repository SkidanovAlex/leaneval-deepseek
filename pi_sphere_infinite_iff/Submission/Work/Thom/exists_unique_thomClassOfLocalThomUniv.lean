import Mathlib
import Submission.Work.Thom.nonempty_thomClass_of_localThom_univ
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.relCohMV_honest_les

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-!
# Uniqueness of the Thom class with prescribed restriction to the piece over the whole base

`Work.Thom.nonempty_thomClass_of_localThom_univ` proves that local Thom data `T` over the whole
base `Set.univ` produce a `ThomClass Z n`; this module sharpens the statement to an `∃!`: there is
exactly one `ThomClass Z n` whose class restricts to `T.τ` along the identification of the piece
`X|_univ` of the total space with `X = Z.TotalSpace`.

* **Existence** is the transfer step of `Work.Thom.cupMap_transfer_bwdA`: the preimage `τ'` of
  `T.τ` under the (bijective) restriction `H^n(X,X∖0) → H^n(X|_univ, X|_univ∖0)` has bijective cup
  map over `↥(Set.univ : Set B)`; the base `↥(Set.univ : Set B)` is then replaced by `B` through the
  canonical homeomorphism `B ≃ ↥(Set.univ : Set B)` (`Work.Thom.CohMap_comp`, homotopy-free
  bookkeeping).
* **Uniqueness** is injectivity of the restriction map: two Thom classes satisfying the same
  equation have the same class `τ`, and a `ThomClass` is determined by its class because the second
  field (`isThom`) is a proposition.

The proof is the proof of `Work.Thom.nonempty_thomClass_of_localThom_univ` with the transport
equation kept instead of discarded, plus the two-line uniqueness argument.
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type} {n : ℕ}

/-- **A `ThomClass` is determined by its class**: the Thom isomorphism condition is a proposition. -/
theorem thomClass_ext {Z : RealBundle B F ι} {n : ℕ} {T₁ T₂ : ThomClass Z n}
    (h : T₁.τ = T₂.τ) : T₁ = T₂ := by
  cases T₁ with
  | mk τ₁ h₁ =>
    cases T₂ with
    | mk τ₂ h₂ =>
      cases h
      rfl

/-- **Existence and uniqueness of the Thom class restricting to local Thom data over `Set.univ`.**

The class is transported from the piece `X|_univ` of the total space to `X` along the (identity)
homeomorphism of pairs `X|_univ ≃ₜ X` (`Work.Thom.cupMap_transfer_bwdA`), and the base
`↥(Set.univ : Set B)` is identified with `B`; uniqueness follows since a `ThomClass` is determined
by its class (`Work.Thom.thomClass_ext`) and the restriction map is injective. -/
theorem exists_unique_thomClassOfLocalThomUniv {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (T : Work.Thom.LocalThom Z n Set.univ) :
    ∃! Tc : Work.Thom.ThomClass Z n,
      (Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(Z.proj ⁻¹' (Set.univ : Set B)), Z.TotalSpace))
        {y : ↥(Z.proj ⁻¹' (Set.univ : Set B)) | (y : Z.TotalSpace) ∈ Work.Thom.zeroComplement Z}
        (Work.Thom.zeroComplement Z) (fun y hy => hy) ℤ n).hom Tc.τ = T.τ := by
  classical
  -- the piece `X|_univ` is `X` itself, through the canonical homeomorphism
  let e : ↥(Z.proj ⁻¹' (Set.univ : Set B)) ≃ₜ Z.TotalSpace :=
    { toFun := Subtype.val
      invFun := fun p => ⟨p, Set.mem_univ p⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun p => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk (fun _ => trivial) }
  let Bs : Set ↥(Z.proj ⁻¹' (Set.univ : Set B)) :=
    {y : ↥(Z.proj ⁻¹' (Set.univ : Set B)) | (y : Z.TotalSpace) ∈ zeroComplement Z}
  let f : C(↥(Z.proj ⁻¹' (Set.univ : Set B)), Z.TotalSpace) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have he : ∀ y : ↥(Z.proj ⁻¹' (Set.univ : Set B)), y ∈ Bs ↔ e y ∈ zeroComplement Z :=
    fun y => Iff.rfl
  have hf : ∀ y ∈ Bs, f y ∈ zeroComplement Z := fun y hy => (he y).mp hy
  -- the restriction of the relative cohomology along `X|_univ ↪ X` is bijective
  have hfbij : ∀ m, Function.Bijective (relCohMap f Bs (zeroComplement Z) hf ℤ m).hom :=
    fun m => bijective_relCohMap_of_homeomorphA Bs (zeroComplement Z) e (fun y => Iff.rfl) ℤ m
  -- the two projections to `↥(Set.univ : Set B)`
  let πX : C(Z.TotalSpace, ↥(Set.univ : Set B)) :=
    ⟨fun p => ⟨Z.proj p, trivial⟩, Z.continuous_proj.subtype_mk (fun _ => trivial)⟩
  let πY : C(↥(Z.proj ⁻¹' (Set.univ : Set B)), ↥(Set.univ : Set B)) := pieceProj Z Set.univ
  have hπ : πX.comp f = πY := rfl
  -- the local Thom isomorphism of `T` is the cup map of `T.τ` over `↥(Set.univ : Set B)`
  have hτ : ∀ k, Function.Bijective (fun x : Coh ℤ k ↥(Set.univ : Set B) =>
      (mixedCupC ℤ Bs k n) ((CohMap πY ℤ k).hom x) T.τ) := by
    intro k
    have hfun : (fun x : Coh ℤ k ↥(Set.univ : Set B) =>
        (mixedCupC ℤ Bs k n) ((CohMap πY ℤ k).hom x) T.τ)
        = ⇑(localThomMap Z n Set.univ T.τ k) := by
      funext x
      rw [localThomMap_apply]
      rfl
    rw [hfun]
    exact T.isThom k
  -- transport of the class to the total space, keeping the equation
  obtain ⟨τ', hτ'eq, hτ'bij⟩ :=
    cupMap_transfer_bwdA f (zeroComplement Z) Bs hf hfbij πX πY hπ n T.τ hτ
  -- replace the base `↥(Set.univ : Set B)` by `B`
  let φ : C(B, ↥(Set.univ : Set B)) :=
    ⟨fun x => ⟨x, trivial⟩, continuous_id.subtype_mk (fun _ => trivial)⟩
  let g : C(↥(Set.univ : Set B), B) := subtypeMap Set.univ
  have hgφ : g.comp φ = ContinuousMap.id B := by ext x; rfl
  have hφg : φ.comp g = ContinuousMap.id ↥(Set.univ : Set B) := by ext y; rfl
  have hφbij : ∀ k, Function.Bijective (CohMap φ ℤ k).hom := by
    intro k
    have h1 : ((CohMap g ℤ k).hom).comp ((CohMap φ ℤ k).hom) = LinearMap.id := by
      have h := CohMap_comp g φ ℤ k
      rw [hφg, CohMap_id] at h
      have h2 := congrArg (fun f : Coh ℤ k ↥(Set.univ : Set B) ⟶
        Coh ℤ k ↥(Set.univ : Set B) => f.hom) h.symm
      simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h2
    have h2 : ((CohMap φ ℤ k).hom).comp ((CohMap g ℤ k).hom) = LinearMap.id := by
      have h := CohMap_comp φ g ℤ k
      rw [hgφ, CohMap_id] at h
      have h3 := congrArg (fun f : Coh ℤ k B ⟶ Coh ℤ k B => f.hom) h.symm
      simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h3
    constructor
    · intro a b hab
      have ha := LinearMap.congr_fun h1 a
      have hb := LinearMap.congr_fun h1 b
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
      rw [hab] at ha
      exact ha.symm.trans hb
    · intro b
      exact ⟨(CohMap g ℤ k).hom b, LinearMap.congr_fun h2 b⟩
  -- the Thom map over `B` is bijective
  have hthom : ∀ k, Function.Bijective (thomMap Z n τ' k) := by
    intro k
    have hCoh : (CohMap πX ℤ k).hom
        = ((CohMap (bundleProj Z) ℤ k).hom).comp ((CohMap φ ℤ k).hom) := by
      have h := CohMap_linear_comp (bundleProj Z) φ ℤ k
      have hπX : πX = φ.comp (bundleProj Z) := by ext p; rfl
      rw [hπX]
      exact h.symm
    have hcomp : Function.Bijective
        ((fun y : Coh ℤ k B => (mixedCupC ℤ (zeroComplement Z) k n)
          ((CohMap (bundleProj Z) ℤ k).hom y) τ') ∘ (CohMap φ ℤ k).hom) := by
      rw [show ((fun y : Coh ℤ k B => (mixedCupC ℤ (zeroComplement Z) k n)
            ((CohMap (bundleProj Z) ℤ k).hom y) τ') ∘ (CohMap φ ℤ k).hom)
          = (fun x : Coh ℤ k ↥(Set.univ : Set B) =>
              (mixedCupC ℤ (zeroComplement Z) k n) ((CohMap πX ℤ k).hom x) τ') from by
        funext x
        simp only [Function.comp_apply]
        rw [LinearMap.congr_fun hCoh x]
        rfl]
      exact hτ'bij k
    have hF : Function.Bijective (fun y : Coh ℤ k B =>
        (mixedCupC ℤ (zeroComplement Z) k n) ((CohMap (bundleProj Z) ℤ k).hom y) τ') := by
      have hψ := hφbij k
      constructor
      · intro a b hab
        obtain ⟨a', rfl⟩ := hψ.2 a
        obtain ⟨b', rfl⟩ := hψ.2 b
        exact congrArg (CohMap φ ℤ k).hom (hcomp.1 hab)
      · intro c
        obtain ⟨x, hx⟩ := hcomp.2 c
        exact ⟨(CohMap φ ℤ k).hom x, hx⟩
    exact hF
  refine ⟨⟨τ', hthom⟩, hτ'eq, ?_⟩
  -- uniqueness
  intro Tc hTc
  have h2 : (relCohMap f Bs (zeroComplement Z) hf ℤ n).hom (Tc.τ)
      = (relCohMap f Bs (zeroComplement Z) hf ℤ n).hom τ' := by
    rw [hTc, hτ'eq]
  exact thomClass_ext ((hfbij n).1 h2)

end

end Work.Thom
