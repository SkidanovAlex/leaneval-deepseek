/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The Mayer–Vietoris sequence on cohomology

`mvAlpha` and `mvBeta` (`MVBasic.lean`) are maps of cochain complexes, so they descend to the
cohomology `H`.  This file records the resulting linear maps on cohomology, together with the
computation rules on the class of a cocycle.  The exactness of the resulting long exact sequence
is proved elsewhere.
-/
import Mathlib
import Submission.Work.Cohomology.MVApply

open CategoryTheory Simplicial Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Cohomology

noncomputable section

/-- The restriction map of the Mayer–Vietoris sequence on cohomology. -/
def mvAlphaH (S : SSet.{0}) (A B : S.Subcomplex) (j : ℕ) :
    H S ℚ j →ₗ[ℚ] H A ℚ j × H B ℚ j :=
  LinearMap.prod (H.map ℚ A.ι j) (H.map ℚ B.ι j)

@[simp] lemma mvAlphaH_apply (S : SSet.{0}) (A B : S.Subcomplex) (j : ℕ) (x : H S ℚ j) :
    mvAlphaH S A B j x = (H.map ℚ A.ι j x, H.map ℚ B.ι j x) := rfl

/-- The difference of the restrictions of the Mayer–Vietoris sequence on cohomology. -/
def mvBetaH (S : SSet.{0}) (A B : S.Subcomplex) (j : ℕ) :
    H A ℚ j × H B ℚ j →ₗ[ℚ] H (A ⊓ B : S.Subcomplex) ℚ j :=
  ((H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) j).comp
      (LinearMap.fst ℚ _ _))
    - ((H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) j).comp
      (LinearMap.snd ℚ _ _))

@[simp] lemma mvBetaH_apply (S : SSet.{0}) (A B : S.Subcomplex) (j : ℕ)
    (x : H A ℚ j × H B ℚ j) :
    mvBetaH S A B j x
      = H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) j x.1
        - H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) j x.2 := rfl

/-- The computation rule for `mvAlphaH` on the class of a cocycle. -/
lemma mvAlphaH_mk (S : SSet.{0}) (A B : S.Subcomplex) (j : ℕ) (u : Cochain S ℚ j)
    (hu : u ∈ cycles S ℚ j) :
    mvAlphaH S A B j (H.mk u hu)
      = (H.mk (pullbackCo ℚ A.ι u) (pullbackCo_mem_cycles A.ι hu),
         H.mk (pullbackCo ℚ B.ι u) (pullbackCo_mem_cycles B.ι hu)) := by
  ext <;> simp [H.map_mk]

/-- The computation rule for `mvBetaH` on the classes of cocycles: the difference of the two
restrictions. -/
lemma mvBetaH_mk (S : SSet.{0}) (A B : S.Subcomplex) (j : ℕ)
    {u : Cochain A ℚ j} {v : Cochain B ℚ j} (hu : u ∈ cycles A ℚ j) (hv : v ∈ cycles B ℚ j) :
    mvBetaH S A B j (H.mk u hu, H.mk v hv)
      = H.mk (pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) u)
          (pullbackCo_mem_cycles _ hu)
        - H.mk (pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) v)
          (pullbackCo_mem_cycles _ hv) := by
  simp [H.map_mk]

/-- The cohomology-level `mvAlpha` is injective in degree `0`. -/
theorem mvAlphaH_injective_zero (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) :
    Function.Injective (mvAlphaH S A B 0) := by
  have hmem : ∀ σ : S.obj (op ⦋0⦌), σ ∈ A.obj (op ⦋0⦌) ∨ σ ∈ B.obj (op ⦋0⦌) := by
    intro σ
    have h : σ ∈ (A ⊔ B).obj (op ⦋0⦌) := by rw [hAB]; trivial
    exact h
  have hzero : ∀ z : H S ℚ 0, mvAlphaH S A B 0 z = 0 → z = 0 := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ : ∃ c : Cochain S ℚ 0, ∃ hc : c ∈ cycles S ℚ 0, H.mk c hc = z :=
      ⟨(Quot.out z).1, (Quot.out z).2, Quot.out_eq z⟩
    have hz' : mvAlphaH S A B 0 (H.mk c hc) = 0 := by rw [hzc]; exact hz
    have hA : H.map ℚ A.ι 0 (H.mk c hc) = 0 := by
      have h := congrArg Prod.fst hz'
      simpa [mvAlphaH_apply] using h
    have hB : H.map ℚ B.ι 0 (H.mk c hc) = 0 := by
      have h := congrArg Prod.snd hz'
      simpa [mvAlphaH_apply] using h
    have hAc : pullbackCo ℚ A.ι c = 0 := by
      have h1 : H.mk (pullbackCo ℚ A.ι c) (pullbackCo_mem_cycles A.ι hc) = 0 := by
        rw [← H.map_mk ℚ A.ι c hc]
        exact hA
      have h2 : pullbackCo ℚ A.ι c ∈ boundaries A ℚ 0 := by
        have h3 := (H.mk_eq_mk_iff (pullbackCo ℚ A.ι c) 0 (pullbackCo_mem_cycles A.ι hc)
          (Submodule.zero_mem _)).mp h1
        rw [sub_zero] at h3
        simpa only [boundariesInCycles, Submodule.mem_comap, Submodule.subtype_apply] using h3
      rwa [show boundaries A ℚ 0 = (⊥ : Submodule ℚ (Cochain A ℚ 0)) from rfl,
        Submodule.mem_bot] at h2
    have hBc : pullbackCo ℚ B.ι c = 0 := by
      have h1 : H.mk (pullbackCo ℚ B.ι c) (pullbackCo_mem_cycles B.ι hc) = 0 := by
        rw [← H.map_mk ℚ B.ι c hc]
        exact hB
      have h2 : pullbackCo ℚ B.ι c ∈ boundaries B ℚ 0 := by
        have h3 := (H.mk_eq_mk_iff (pullbackCo ℚ B.ι c) 0 (pullbackCo_mem_cycles B.ι hc)
          (Submodule.zero_mem _)).mp h1
        rw [sub_zero] at h3
        simpa only [boundariesInCycles, Submodule.mem_comap, Submodule.subtype_apply] using h3
      rwa [show boundaries B ℚ 0 = (⊥ : Submodule ℚ (Cochain B ℚ 0)) from rfl,
        Submodule.mem_bot] at h2
    rw [← hzc]
    rw [show (0 : H S ℚ 0) = H.mk 0 (Submodule.zero_mem _) from rfl]
    rw [H.mk_eq_mk_iff]
    rw [show boundaries S ℚ 0 = (⊥ : Submodule ℚ (Cochain S ℚ 0)) from rfl, Submodule.mem_bot]
    ext σ
    rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    rcases hmem σ with hσ | hσ
    · have h := congrFun hAc (⟨σ, hσ⟩ : (A : SSet).obj (op ⦋0⦌))
      exact h
    · have h := congrFun hBc (⟨σ, hσ⟩ : (B : SSet).obj (op ⦋0⦌))
      exact h
  intro x y hxy
  have hz : mvAlphaH S A B 0 (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have := hzero (x - y) hz
  rwa [sub_eq_zero] at this

end

end Submission.Cohomology
