import Mathlib
import Submission.Work.Serre.bijective_mixedCup_of_openCover
import Submission.Work.Serre.bijective_mixedCup_of_openCover_zero
import Submission.Work.RatHurewicz.bijective_mixedCup_of_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two-subset gluing of the mixed cup bijectivity

`Work.Serre.bijective_mixedCup_of_openCover` glues the local bijectivity of `x ↦ x ⌣ U₀` over an
open cover `X = U ∪ V` of the *whole* space `X`, with the class `U₀` living on `X`.  The cellular
step of the Serre argument needs the same gluing inside a subspace: the class `U₀` lives on
`↥(Uc ∪ Vc)` only.  This file reduces that case to the cover version by working in the subspace
`Y := ↥(Uc ∪ Vc)`: its pieces are `{y : Y | (y : X) ∈ Uc}` and `{y : Y | (y : X) ∈ Vc}`, and the
local hypotheses over `↥Uc`, `↥Vc`, `↥(Uc ∩ Vc)` of the target are transported to the corresponding
pieces of `Y` along the canonical homeomorphisms `↥W ≃ₜ ↥{y : Y | (y : X) ∈ W}`
(`Work.RatHurewicz.bijective_mixedCup_of_homeo` for the bijectivity,
`Work.Thom.bijective_relCohMap_of_homeomorphA` for the vanishing hypotheses).

Main result: `Work.Serre.bijective_mixedCup_of_two_subset`.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-- The canonical homeomorphism `↥W ≃ₜ ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W}` for `W ⊆ Uc ∪ Vc`. -/
def twoSubsetHomeo {X : Type} [TopologicalSpace X] (Uc Vc W : Set X) (hW : W ⊆ Uc ∪ Vc) :
    ↥W ≃ₜ ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} where
  toFun x := ⟨⟨x.1, hW x.2⟩, x.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem twoSubsetHomeo_apply {X : Type} [TopologicalSpace X] (Uc Vc W : Set X)
    (hW : W ⊆ Uc ∪ Vc) (x : ↥W) :
    (twoSubsetHomeo Uc Vc W hW x : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W})
      = ⟨⟨x.1, hW x.2⟩, x.2⟩ := rfl

theorem twoSubsetHomeo_symm_apply {X : Type} [TopologicalSpace X] (Uc Vc W : Set X)
    (hW : W ⊆ Uc ∪ Vc) (y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W}) :
    (twoSubsetHomeo Uc Vc W hW).symm y = ⟨y.1.1, y.2⟩ := rfl

/-- Transport of the local bijectivity of the cup map from a piece `↥W` of `X` to the
corresponding piece of `↥(Uc ∪ Vc)`. -/
theorem bijective_cup_twoSubset {X : Type} [TopologicalSpace X] (A Uc Vc W : Set X)
    (hW : W ⊆ Uc ∪ Vc) (n₀ m : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ ↥(Uc ∪ Vc) {y : ↥(Uc ∪ Vc) | (y : X) ∈ A})
    (hb : Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥W =>
      (Work.Thom.mixedCupC ℚ {y : ↥W | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap
          (⟨fun x => ⟨x.1, hW x.2⟩, by fun_prop⟩ : C(↥W, ↥(Uc ∪ Vc)))
          {y : ↥W | (y : X) ∈ A} {y : ↥(Uc ∪ Vc) | (y : X) ∈ A}
          (fun _ hy => hy) ℚ n₀).hom U₀))) :
    Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} =>
      (Work.Thom.mixedCupC ℚ {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W}, ↥(Uc ∪ Vc)))
          {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} | (y : X) ∈ A}
          {y : ↥(Uc ∪ Vc) | (y : X) ∈ A}
          (fun _ hy => hy) ℚ n₀).hom U₀)) := by
  have h1 := Work.RatHurewicz.bijective_mixedCup_of_homeo
    (e := (twoSubsetHomeo Uc Vc W hW).symm)
    ({y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} | (y : X) ∈ A})
    ({y : ↥W | (y : X) ∈ A}) (fun x => Iff.rfl) m n₀
    ((Work.Thom.relCohMap
      (⟨fun x => ⟨x.1, hW x.2⟩, by fun_prop⟩ : C(↥W, ↥(Uc ∪ Vc)))
      {y : ↥W | (y : X) ∈ A} {y : ↥(Uc ∪ Vc) | (y : X) ∈ A}
      (fun _ hy => hy) ℚ n₀).hom U₀)
    hb
  have hcomp : ((⟨fun x => ⟨x.1, hW x.2⟩, by fun_prop⟩ : C(↥W, ↥(Uc ∪ Vc))).comp
      ((twoSubsetHomeo Uc Vc W hW).symm :
        C(↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W}, ↥W)))
      = (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W}, ↥(Uc ∪ Vc))) := by
    ext y
    rfl
  have h2 : Work.Thom.relCohMap
        (((⟨fun x => ⟨x.1, hW x.2⟩, by fun_prop⟩ : C(↥W, ↥(Uc ∪ Vc))).comp
          ((twoSubsetHomeo Uc Vc W hW).symm :
            C(↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W}, ↥W))))
        ({y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} | (y : X) ∈ A})
        ({y : ↥(Uc ∪ Vc) | (y : X) ∈ A}) (fun _ hy => hy) ℚ n₀
      = Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W}, ↥(Uc ∪ Vc)))
        ({y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} | (y : X) ∈ A})
        ({y : ↥(Uc ∪ Vc) | (y : X) ∈ A}) (fun _ hy => hy) ℚ n₀ :=
    Work.Thom.relCohMap_congrA _ _ hcomp _ _ ℚ n₀
  rw [Work.Thom.relCohMap_compA_apply
      ({y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} | (y : X) ∈ A})
      ({y : ↥W | (y : X) ∈ A})
      ({y : ↥(Uc ∪ Vc) | (y : X) ∈ A})
      ((twoSubsetHomeo Uc Vc W hW).symm)
      (⟨fun x => ⟨x.1, hW x.2⟩, by fun_prop⟩ : C(↥W, ↥(Uc ∪ Vc)))
      (fun _ hy => hy) (fun _ hy => hy) (fun _ hy => hy) ℚ n₀ U₀] at h1
  rw [h2] at h1
  exact h1

/-- Transport of the vanishing of the relative cohomology of a piece. -/
theorem subsingleton_relCoh_twoSubset {X : Type} [TopologicalSpace X] (A Uc Vc W : Set X)
    (hW : W ⊆ Uc ∪ Vc) (n : ℕ)
    (h : Subsingleton ↥(Work.Thom.RelCoh ℚ n ↥W {y : ↥W | (y : X) ∈ A})) :
    Subsingleton ↥(Work.Thom.RelCoh ℚ n ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W}
      {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} | (y : X) ∈ A}) := by
  have hb : Function.Bijective (Work.Thom.relCohMap
      ((twoSubsetHomeo Uc Vc W hW).symm)
      ({y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} | (y : X) ∈ A})
      ({y : ↥W | (y : X) ∈ A}) (fun _ hy => hy) ℚ n).hom :=
    Work.Thom.bijective_relCohMap_of_homeomorphA
      ({y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W} | (y : X) ∈ A})
      ({y : ↥W | (y : X) ∈ A}) ((twoSubsetHomeo Uc Vc W hW).symm) (fun x => Iff.rfl) ℚ n
  haveI := h
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := hb.surjective a
  obtain ⟨y, hy⟩ := hb.surjective b
  rw [← hx, ← hy, Subsingleton.elim x y]

theorem bijective_mixedCup_of_two_subset {X : Type} [TopologicalSpace X] (A : Set X)
    (Uc Vc : Set X) (hUo : IsOpen Uc) (hVo : IsOpen Vc)
    (n₀ K : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ ↥(Uc ∪ Vc) {y : ↥(Uc ∪ Vc) | (y : X) ∈ A})
    (hvanU : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥Uc {y : ↥Uc | (y : X) ∈ A}))
    (hvanV : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥Vc {y : ↥Vc | (y : X) ∈ A}))
    (hvanUV : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥(Uc ∩ Vc)
      {y : ↥(Uc ∩ Vc) | (y : X) ∈ A}))
    (hlocU : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥Uc =>
      (Work.Thom.mixedCupC ℚ {y : ↥Uc | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap
          (⟨fun x => ⟨x.1, Or.inl x.2⟩, by fun_prop⟩ : C(↥Uc, ↥(Uc ∪ Vc)))
          {y : ↥Uc | (y : X) ∈ A} {y : ↥(Uc ∪ Vc) | (y : X) ∈ A}
          (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocV : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥Vc =>
      (Work.Thom.mixedCupC ℚ {y : ↥Vc | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap
          (⟨fun x => ⟨x.1, Or.inr x.2⟩, by fun_prop⟩ : C(↥Vc, ↥(Uc ∪ Vc)))
          {y : ↥Vc | (y : X) ∈ A} {y : ↥(Uc ∪ Vc) | (y : X) ∈ A}
          (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocUV : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(Uc ∩ Vc) =>
      (Work.Thom.mixedCupC ℚ {y : ↥(Uc ∩ Vc) | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap
          (⟨fun y => ⟨y.1, Or.inl y.2.1⟩, by fun_prop⟩ : C(↥(Uc ∩ Vc), ↥(Uc ∪ Vc)))
          {y : ↥(Uc ∩ Vc) | (y : X) ∈ A} {y : ↥(Uc ∪ Vc) | (y : X) ∈ A}
          (fun _ hy => hy) ℚ n₀).hom U₀))) :
    ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(Uc ∪ Vc) =>
      (Work.Thom.mixedCupC ℚ {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} m n₀) x U₀) := by
  classical
  have hUo' : IsOpen {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} :=
    hUo.preimage continuous_subtype_val
  have hVo' : IsOpen {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} :=
    hVo.preimage continuous_subtype_val
  have hcov' : {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} ∪ {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc}
      = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      rcases y.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hlocU' : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} =>
      (Work.Thom.mixedCupC ℚ {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc}, ↥(Uc ∪ Vc)))
          {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} | (y : X) ∈ A}
          {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom U₀)) :=
    fun m hm => bijective_cup_twoSubset A Uc Vc Uc (fun _ hx => Or.inl hx) n₀ m U₀ (hlocU m hm)
  have hlocV' : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} =>
      (Work.Thom.mixedCupC ℚ {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc}, ↥(Uc ∪ Vc)))
          {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} | (y : X) ∈ A}
          {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom U₀)) :=
    fun m hm => bijective_cup_twoSubset A Uc Vc Vc (fun _ hx => Or.inr hx) n₀ m U₀ (hlocV m hm)
  have hlocUV' : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc ∩ Vc} =>
      (Work.Thom.mixedCupC ℚ {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc ∩ Vc} | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc ∩ Vc}, ↥(Uc ∪ Vc)))
          {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc ∩ Vc} | (y : X) ∈ A}
          {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} (fun _ hy => hy) ℚ n₀).hom U₀)) :=
    fun m hm => bijective_cup_twoSubset A Uc Vc (Uc ∩ Vc) (fun _ hy => Or.inl hy.1) n₀ m U₀
      (hlocUV m hm)
  have hvanU' : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc}
      {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} | (y : X) ∈ A}) :=
    subsingleton_relCoh_twoSubset A Uc Vc Uc (fun _ hx => Or.inl hx) (n₀ - 1) hvanU
  have hvanV' : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc}
      {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} | (y : X) ∈ A}) :=
    subsingleton_relCoh_twoSubset A Uc Vc Vc (fun _ hx => Or.inr hx) (n₀ - 1) hvanV
  have hvanUV' : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1)
      ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc ∩ Vc}
      {y : ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc ∩ Vc} | (y : X) ∈ A}) :=
    subsingleton_relCoh_twoSubset A Uc Vc (Uc ∩ Vc) (fun _ hy => Or.inl hy.1) (n₀ - 1) hvanUV
  intro m hm
  rcases Nat.eq_zero_or_pos m with hm0 | hpos
  · subst hm0
    exact bijective_mixedCup_of_openCover_zero
      ({y : ↥(Uc ∪ Vc) | (y : X) ∈ A})
      ({y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc})
      ({y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc})
      hUo' hVo' hcov' n₀ U₀ hvanU' hvanV' hvanUV'
      (hlocU' 0 hm) (hlocV' 0 hm) (hlocUV' 0 hm)
  · exact bijective_mixedCup_of_openCover
      ({y : ↥(Uc ∪ Vc) | (y : X) ∈ A})
      ({y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc})
      ({y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc})
      hUo' hVo' hcov' n₀ K U₀ hlocU' hlocV' hlocUV' m hpos hm

end

end Work.Serre
