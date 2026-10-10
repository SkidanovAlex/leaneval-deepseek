import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.TwistField.asTwistFieldTrue_basic
import Submission.Work.MotC5N3.LamAS.root_eq_asRoot_add
import Submission.Work.MotT.coeffAlgEquiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The coefficient action on `Work.MotC5N3.OmA K D` and its interaction with the AS twist fields

Let `K = K`, `Kb = Work.MotC5N3.KbA K = AlgebraicClosure K`, `Om = Work.MotC5N3.OmA K D = Kb(E)`, and let
`Φ : Om ≃ₐ[𝕜] Om` be the **coefficient action** of an `𝕜`-algebra automorphism `σ` of `Kb`
(`Work.MotT.coeffAlgEquiv`): it acts on the constants by `σ` and fixes the geometric coordinates
`x, y`, hence fixes the Klein coordinates `κᵢ` and their ratios `κᵢ/κ₀`.

This file collects the consequences that the `α`-reduction of the LAM node
(`Work.MotC5N3.Nodes.lam_AS_alpha`) needs:

* `Φ` maps the subfield `Work.MotC5N3.kleinField K D` onto itself, and `asFieldL D g` onto `asFieldL D (β g)`
  where `β` is the automorphism of `K` that `σ` induces;
* `Φ` conjugates the fixed field of a cyclic group to the fixed field of the conjugate group.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.MotC5N3.Alpha
open IntermediateField

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-! ## §1 The coefficient action fixes the Klein coordinates -/

/-- **The coefficient action of `σ` on `Work.MotC5N3.OmA K D`.**  There is `Φ : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D` acting on the
constants by `σ`, fixing the Klein coordinates `κᵢ` and hence their ratios `κᵢ/κ₀`. -/
theorem exists_coeffAut (D : Work.MotV.KleinData 𝕜) (σ : Work.MotC5N3.KbA K ≃ₐ[𝕜] Work.MotC5N3.KbA K) :
    ∃ Φ : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D,
      (∀ c : Work.MotC5N3.KbA K, Φ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c)) ∧
      (∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i)
        = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i) ∧
      (∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
          / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
        = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
          / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) := by
  obtain ⟨g, hgconst, hgX, hgY⟩ := Work.MotT.coeffAlgEquiv 𝕜 D.E (Work.MotC5N3.KbA K) σ
  have hbas : ∀ m : Fin 5, g (Work.MotV.kleinBas D (Work.MotC5N3.KbA K) m)
      = Work.MotV.kleinBas D (Work.MotC5N3.KbA K) m := by
    intro m
    fin_cases m <;> simp [Work.MotV.kleinBas, hgX, hgY]
  have hcoord : ∀ i : Fin 5, g (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i)
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i := by
    intro i
    simp only [Work.MotV.kleinCoord_eq_sum, map_sum, map_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    · rw [hgconst, AlgEquiv.commutes σ (D.coord i m)]
    · exact hbas m
  exact ⟨g, hgconst, hcoord, fun i => by rw [map_div₀, hcoord i, hcoord 0]⟩

/-! ## §2 Preservation of the subfields -/

/-- The `K`-scalars are carried to `K`-scalars (with the index changed by `β`). -/
theorem coeffAut_algebraMap_K (D : Work.MotV.KleinData 𝕜)
    (β : K ≃ₐ[𝕜] K) (σ : Work.MotC5N3.KbA K ≃ₐ[𝕜] Work.MotC5N3.KbA K)
    (hσβ : ∀ c : K, σ (algebraMap (K) (Work.MotC5N3.KbA K) c)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β c))
    (Φ : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D)
    (hΦc : ∀ c : Work.MotC5N3.KbA K, Φ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c)) (c : K) :
    Φ (algebraMap (K) (Work.MotC5N3.OmA K D) c)
      = algebraMap (K) (Work.MotC5N3.OmA K D) (β c) := by
  rw [IsScalarTower.algebraMap_apply (K) (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c, hΦc,
    hσβ c,
    ← IsScalarTower.algebraMap_apply (K) (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (β c)]

/-- **`Φ` preserves the base field `K(E) = Work.MotC5N3.kleinField K D`.** -/
theorem coeffAut_kleinField_le (D : Work.MotV.KleinData 𝕜)
    (β : K ≃ₐ[𝕜] K) (σ : Work.MotC5N3.KbA K ≃ₐ[𝕜] Work.MotC5N3.KbA K)
    (hσβ : ∀ c : K, σ (algebraMap (K) (Work.MotC5N3.KbA K) c)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β c))
    (Φ : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D)
    (hΦc : ∀ c : Work.MotC5N3.KbA K, Φ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
    (x : Work.MotC5N3.OmA K D) (hx : x ∈ Work.MotC5N3.kleinField K D) :
    Φ x ∈ Work.MotC5N3.kleinField K D := by
  set S : IntermediateField (K) (Work.MotC5N3.OmA K D) :=
    { carrier := {x | Φ x ∈ Work.MotC5N3.kleinField K D}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add]
        exact IntermediateField.add_mem _ ha hb
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul]
        exact IntermediateField.mul_mem _ ha hb
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv₀]
        exact IntermediateField.inv_mem _ ha
      algebraMap_mem' := fun c => by
        show Φ (algebraMap (K) (Work.MotC5N3.OmA K D) c) ∈ Work.MotC5N3.kleinField K D
        rw [coeffAut_algebraMap_K D β σ hσβ Φ hΦc c]
        exact IntermediateField.algebraMap_mem _ _ } with hSdef
  have hle : Work.MotC5N3.kleinField K D ≤ S := by
    rw [Work.MotC5N3.kleinField, IntermediateField.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    show Φ (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) ∈ Work.MotC5N3.kleinField K D
    rw [hΦratio i]
    exact IntermediateField.subset_adjoin (K) _
      (Set.mem_range_self i)
  exact hle hx

/-- The same statement for `Φ⁻¹` (which satisfies the same hypotheses with `(β⁻¹, σ⁻¹)`). -/
theorem coeffAut_kleinField_le_symm (D : Work.MotV.KleinData 𝕜)
    (β : K ≃ₐ[𝕜] K) (σ : Work.MotC5N3.KbA K ≃ₐ[𝕜] Work.MotC5N3.KbA K)
    (hσβ : ∀ c : K, σ (algebraMap (K) (Work.MotC5N3.KbA K) c)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β c))
    (Φ : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D)
    (hΦc : ∀ c : Work.MotC5N3.KbA K, Φ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) :
    ∀ x : Work.MotC5N3.OmA K D, Φ x ∈ Work.MotC5N3.kleinField K D → x ∈ Work.MotC5N3.kleinField K D := by
  have hσβ' : ∀ c : K, σ.symm (algebraMap (K) (Work.MotC5N3.KbA K) c)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β.symm c) := by
    intro c
    have h := hσβ (β.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq σ).mpr h.symm
  have hΦc' : ∀ c : Work.MotC5N3.KbA K,
      Φ.symm (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ.symm c) := by
    intro c
    have h := hΦc (σ.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq Φ).mpr h.symm
  have hΦratio' : ∀ i : Fin 5, Φ.symm (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
      / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
    intro i
    exact (AlgEquiv.symm_apply_eq Φ).mpr (hΦratio i).symm
  intro x hx
  have h1 := coeffAut_kleinField_le D β.symm σ.symm hσβ' Φ.symm hΦc' hΦratio' (Φ x) hx
  rwa [AlgEquiv.symm_apply_apply] at h1

/-- **`Φ` maps `Work.MotC5N3.kleinField K D` onto itself.** -/
theorem coeffAut_kleinField_iff (D : Work.MotV.KleinData 𝕜)
    (β : K ≃ₐ[𝕜] K) (σ : Work.MotC5N3.KbA K ≃ₐ[𝕜] Work.MotC5N3.KbA K)
    (hσβ : ∀ c : K, σ (algebraMap (K) (Work.MotC5N3.KbA K) c)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β c))
    (Φ : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D)
    (hΦc : ∀ c : Work.MotC5N3.KbA K, Φ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
    (x : Work.MotC5N3.OmA K D) :
    Φ x ∈ Work.MotC5N3.kleinField K D ↔ x ∈ Work.MotC5N3.kleinField K D :=
  ⟨coeffAut_kleinField_le_symm D β σ hσβ Φ hΦc hΦratio x,
    coeffAut_kleinField_le D β σ hσβ Φ hΦc hΦratio x⟩

/-- **The root-field generator maps to a generator of the regraded root field.** -/
theorem coeffAut_asRoot (D : Work.MotV.KleinData 𝕜)
    (β : K ≃ₐ[𝕜] K) (σ : Work.MotC5N3.KbA K ≃ₐ[𝕜] Work.MotC5N3.KbA K)
    (hσβ : ∀ c : K, σ (algebraMap (K) (Work.MotC5N3.KbA K) c)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β c))
    (Φ : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D)
    (hΦc : ∀ c : Work.MotC5N3.KbA K, Φ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c))
    (g : K) :
    Φ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g))
      ∈ Work.MotC5N3.asFieldL D (β g) := by
  rw [hΦc, Work.MotC5N3.asFieldL]
  have hroot : (σ (Work.MotC5N3.asRoot g)) ^ 5 - σ (Work.MotC5N3.asRoot g)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β g) := by
    have h := congrArg σ (Work.MotC5N3.asRoot_spec g)
    rw [map_sub, map_pow] at h
    rw [h, hσβ]
  obtain ⟨k, hk⟩ := Work.MotC5N3.LamAS.root_eq_asRoot_add (β g) hroot
  rw [hk, map_add]
  refine IntermediateField.add_mem _ ?_ ?_
  · refine IntermediateField.subset_adjoin (K) _ (Or.inr ?_)
    exact IntermediateField.subset_adjoin (K) _ (Set.mem_singleton _)
  · refine IntermediateField.subset_adjoin (K) _ (Or.inl ?_)
    have hcast : algebraMap ℤ (Work.MotC5N3.KbA K) ((k : Fin 5) : ℤ)
        = algebraMap (K) (Work.MotC5N3.KbA K)
            (algebraMap ℤ (K) ((k : Fin 5) : ℤ)) :=
      (IsScalarTower.algebraMap_apply ℤ (K) (Work.MotC5N3.KbA K) _).symm
    rw [hcast, ← IsScalarTower.algebraMap_apply (K) (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)]
    exact IntermediateField.algebraMap_mem _ _

/-- **`Φ` maps `asFieldL D g` into `asFieldL D (β g)`.** -/
theorem coeffAut_asFieldL_le (D : Work.MotV.KleinData 𝕜)
    (β : K ≃ₐ[𝕜] K) (σ : Work.MotC5N3.KbA K ≃ₐ[𝕜] Work.MotC5N3.KbA K)
    (hσβ : ∀ c : K, σ (algebraMap (K) (Work.MotC5N3.KbA K) c)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β c))
    (Φ : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D)
    (hΦc : ∀ c : Work.MotC5N3.KbA K, Φ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
    (g : K) (x : Work.MotC5N3.OmA K D) (hx : x ∈ Work.MotC5N3.asFieldL D g) :
    Φ x ∈ Work.MotC5N3.asFieldL D (β g) := by
  set T : IntermediateField (K) (Work.MotC5N3.OmA K D) :=
    { carrier := {x | Φ x ∈ Work.MotC5N3.asFieldL D (β g)}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add]
        exact IntermediateField.add_mem _ ha hb
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul]
        exact IntermediateField.mul_mem _ ha hb
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv₀]
        exact IntermediateField.inv_mem _ ha
      algebraMap_mem' := fun c => by
        show Φ (algebraMap (K) (Work.MotC5N3.OmA K D) c) ∈ Work.MotC5N3.asFieldL D (β g)
        rw [coeffAut_algebraMap_K D β σ hσβ Φ hΦc c, Work.MotC5N3.asFieldL]
        exact IntermediateField.subset_adjoin (K) _ (Or.inl (IntermediateField.algebraMap_mem _ _)) } with hTdef
  have hle : Work.MotC5N3.asFieldL D g ≤ T := by
    rw [Work.MotC5N3.asFieldL]
    refine sup_le ?_ ?_
    · intro y hy
      show Φ y ∈ Work.MotC5N3.asFieldL D (β g)
      rw [Work.MotC5N3.asFieldL]
      exact IntermediateField.subset_adjoin (K) _
        (Or.inl (coeffAut_kleinField_le D β σ hσβ Φ hΦc hΦratio y hy))
    · rw [IntermediateField.adjoin_le_iff]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact coeffAut_asRoot D β σ hσβ Φ hΦc g
  exact hle hx

/-- **`Φ` maps `asFieldL D g` onto `asFieldL D (β g)`.** -/
theorem coeffAut_asFieldL_iff (D : Work.MotV.KleinData 𝕜)
    (β : K ≃ₐ[𝕜] K) (σ : Work.MotC5N3.KbA K ≃ₐ[𝕜] Work.MotC5N3.KbA K)
    (hσβ : ∀ c : K, σ (algebraMap (K) (Work.MotC5N3.KbA K) c)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β c))
    (Φ : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D)
    (hΦc : ∀ c : Work.MotC5N3.KbA K, Φ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
    (g : K) (x : Work.MotC5N3.OmA K D) :
    Φ x ∈ Work.MotC5N3.asFieldL D (β g) ↔ x ∈ Work.MotC5N3.asFieldL D g := by
  refine ⟨?_, coeffAut_asFieldL_le D β σ hσβ Φ hΦc hΦratio g x⟩
  intro hx
  have hσβ' : ∀ c : K, σ.symm (algebraMap (K) (Work.MotC5N3.KbA K) c)
      = algebraMap (K) (Work.MotC5N3.KbA K) (β.symm c) := by
    intro c
    have h := hσβ (β.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq σ).mpr h.symm
  have hΦc' : ∀ c : Work.MotC5N3.KbA K,
      Φ.symm (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ.symm c) := by
    intro c
    have h := hΦc (σ.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq Φ).mpr h.symm
  have hΦratio' : ∀ i : Fin 5, Φ.symm (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
      / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
    intro i
    exact (AlgEquiv.symm_apply_eq Φ).mpr (hΦratio i).symm
  have h1 := coeffAut_asFieldL_le D β.symm σ.symm hσβ' Φ.symm hΦc' hΦratio' (β g) (Φ x) hx
  rw [show β.symm (β g) = g from β.symm_apply_apply g] at h1
  rwa [AlgEquiv.symm_apply_apply] at h1

end Work.MotC5N3.Alpha