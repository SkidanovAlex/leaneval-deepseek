import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.LamAS.root_eq_asRoot_add
import Submission.Work.MotT.coeffAlgEquiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The coefficient action on `Om D` and its interaction with the AS twist fields

Let `K = RatFunc 𝕜`, `Kb = Kb 𝕜 = AlgebraicClosure K`, `Om = Om D = Kb(E)`, and let
`Φ : Om ≃ₐ[𝕜] Om` be the **coefficient action** of an `𝕜`-algebra automorphism `σ` of `Kb`
(`Work.MotT.coeffAlgEquiv`): it acts on the constants by `σ` and fixes the geometric coordinates
`x, y`, hence fixes the Klein coordinates `κᵢ` and their ratios `κᵢ/κ₀`.

This file collects the consequences that the `α`-reduction of the LAM node
(`Work.MotV5.Nodes.lam_AS_alpha`) needs:

* `Φ` maps the subfield `kleinField D` onto itself, and `asFieldL D g` onto `asFieldL D (β g)`
  where `β` is the automorphism of `K` that `σ` induces;
* `Φ` conjugates the fixed field of a cyclic group to the fixed field of the conjugate group.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.MotV5.Alpha

open IntermediateField

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## §1 The coefficient action fixes the Klein coordinates -/

/-- **The coefficient action of `σ` on `Om D`.**  There is `Φ : Om D ≃ₐ[𝕜] Om D` acting on the
constants by `σ`, fixing the Klein coordinates `κᵢ` and hence their ratios `κᵢ/κ₀`. -/
theorem exists_coeffAut (D : Work.MotV.KleinData 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜) :
    ∃ Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D,
      (∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c)) ∧
      (∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
        = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i) ∧
      (∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
          / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
        = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
          / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) := by
  obtain ⟨g, hgconst, hgX, hgY⟩ := Work.MotT.coeffAlgEquiv 𝕜 D.E (Work.MotV.Kb 𝕜) σ
  have hbas : ∀ m : Fin 5, g (Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) m)
      = Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) m := by
    intro m
    fin_cases m <;> simp [Work.MotV.kleinBas, hgX, hgY]
  have hcoord : ∀ i : Fin 5, g (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i := by
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
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c))
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c)) (c : RatFunc 𝕜) :
    Φ (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (β c) := by
  rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c, hΦc,
    hσβ c,
    ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (β c)]

/-- **`Φ` preserves the base field `K(E) = kleinField D`.** -/
theorem coeffAut_kleinField_le (D : Work.MotV.KleinData 𝕜)
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c))
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
    (x : Work.MotV.Om D) (hx : x ∈ Work.MotV5.kleinField D) :
    Φ x ∈ Work.MotV5.kleinField D := by
  set S : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
    { carrier := {x | Φ x ∈ Work.MotV5.kleinField D}
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
        show Φ (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c) ∈ Work.MotV5.kleinField D
        rw [coeffAut_algebraMap_K D β σ hσβ Φ hΦc c]
        exact IntermediateField.algebraMap_mem _ _ } with hSdef
  have hle : Work.MotV5.kleinField D ≤ S := by
    rw [Work.MotV5.kleinField, IntermediateField.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    show Φ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) ∈ Work.MotV5.kleinField D
    rw [hΦratio i]
    exact IntermediateField.subset_adjoin (RatFunc 𝕜) _
      (Set.mem_range_self i)
  exact hle hx

/-- The same statement for `Φ⁻¹` (which satisfies the same hypotheses with `(β⁻¹, σ⁻¹)`). -/
theorem coeffAut_kleinField_le_symm (D : Work.MotV.KleinData 𝕜)
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c))
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) :
    ∀ x : Work.MotV.Om D, Φ x ∈ Work.MotV5.kleinField D → x ∈ Work.MotV5.kleinField D := by
  have hσβ' : ∀ c : RatFunc 𝕜, σ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β.symm c) := by
    intro c
    have h := hσβ (β.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq σ).mpr h.symm
  have hΦc' : ∀ c : Work.MotV.Kb 𝕜,
      Φ.symm (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ.symm c) := by
    intro c
    have h := hΦc (σ.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq Φ).mpr h.symm
  have hΦratio' : ∀ i : Fin 5, Φ.symm (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
      / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 := by
    intro i
    exact (AlgEquiv.symm_apply_eq Φ).mpr (hΦratio i).symm
  intro x hx
  have h1 := coeffAut_kleinField_le D β.symm σ.symm hσβ' Φ.symm hΦc' hΦratio' (Φ x) hx
  rwa [AlgEquiv.symm_apply_apply] at h1

/-- **`Φ` maps `kleinField D` onto itself.** -/
theorem coeffAut_kleinField_iff (D : Work.MotV.KleinData 𝕜)
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c))
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
    (x : Work.MotV.Om D) :
    Φ x ∈ Work.MotV5.kleinField D ↔ x ∈ Work.MotV5.kleinField D :=
  ⟨coeffAut_kleinField_le_symm D β σ hσβ Φ hΦc hΦratio x,
    coeffAut_kleinField_le D β σ hσβ Φ hΦc hΦratio x⟩

/-- **The root-field generator maps to a generator of the regraded root field.** -/
theorem coeffAut_asRoot (D : Work.MotV.KleinData 𝕜)
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c))
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (g : RatFunc 𝕜) :
    Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
      ∈ Work.MotV5.asFieldL D (β g) := by
  rw [hΦc, Work.MotV5.asFieldL]
  have hroot : (σ (Work.MotV5.asRoot g)) ^ 5 - σ (Work.MotV5.asRoot g)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β g) := by
    have h := congrArg σ (Work.MotV5.asRoot_spec g)
    rw [map_sub, map_pow] at h
    rw [h, hσβ]
  obtain ⟨k, hk⟩ := Work.MotV5.LamAS.root_eq_asRoot_add (β g) hroot
  rw [hk, map_add]
  refine IntermediateField.add_mem _ ?_ ?_
  · refine IntermediateField.subset_adjoin (RatFunc 𝕜) _ (Or.inr ?_)
    exact IntermediateField.subset_adjoin (RatFunc 𝕜) _ (Set.mem_singleton _)
  · refine IntermediateField.subset_adjoin (RatFunc 𝕜) _ (Or.inl ?_)
    have hcast : algebraMap ℤ (Work.MotV.Kb 𝕜) ((k : Fin 5) : ℤ)
        = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)
            (algebraMap ℤ (RatFunc 𝕜) ((k : Fin 5) : ℤ)) :=
      (IsScalarTower.algebraMap_apply ℤ (RatFunc 𝕜) (Work.MotV.Kb 𝕜) _).symm
    rw [hcast, ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D)]
    exact IntermediateField.algebraMap_mem _ _

/-- **`Φ` maps `asFieldL D g` into `asFieldL D (β g)`.** -/
theorem coeffAut_asFieldL_le (D : Work.MotV.KleinData 𝕜)
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c))
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
    (g : RatFunc 𝕜) (x : Work.MotV.Om D) (hx : x ∈ Work.MotV5.asFieldL D g) :
    Φ x ∈ Work.MotV5.asFieldL D (β g) := by
  set T : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
    { carrier := {x | Φ x ∈ Work.MotV5.asFieldL D (β g)}
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
        show Φ (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c) ∈ Work.MotV5.asFieldL D (β g)
        rw [coeffAut_algebraMap_K D β σ hσβ Φ hΦc c, Work.MotV5.asFieldL]
        exact IntermediateField.subset_adjoin (RatFunc 𝕜) _ (Or.inl (IntermediateField.algebraMap_mem _ _)) } with hTdef
  have hle : Work.MotV5.asFieldL D g ≤ T := by
    rw [Work.MotV5.asFieldL]
    refine sup_le ?_ ?_
    · intro y hy
      show Φ y ∈ Work.MotV5.asFieldL D (β g)
      rw [Work.MotV5.asFieldL]
      exact IntermediateField.subset_adjoin (RatFunc 𝕜) _
        (Or.inl (coeffAut_kleinField_le D β σ hσβ Φ hΦc hΦratio y hy))
    · rw [IntermediateField.adjoin_le_iff]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact coeffAut_asRoot D β σ hσβ Φ hΦc g
  exact hle hx

/-- **`Φ` maps `asFieldL D g` onto `asFieldL D (β g)`.** -/
theorem coeffAut_asFieldL_iff (D : Work.MotV.KleinData 𝕜)
    (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[𝕜] Work.MotV.Kb 𝕜)
    (hσβ : ∀ c : RatFunc 𝕜, σ (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β c))
    (Φ : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hΦc : ∀ c : Work.MotV.Kb 𝕜, Φ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hΦratio : ∀ i : Fin 5, Φ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
    (g : RatFunc 𝕜) (x : Work.MotV.Om D) :
    Φ x ∈ Work.MotV5.asFieldL D (β g) ↔ x ∈ Work.MotV5.asFieldL D g := by
  refine ⟨?_, coeffAut_asFieldL_le D β σ hσβ Φ hΦc hΦratio g x⟩
  intro hx
  have hσβ' : ∀ c : RatFunc 𝕜, σ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (β.symm c) := by
    intro c
    have h := hσβ (β.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq σ).mpr h.symm
  have hΦc' : ∀ c : Work.MotV.Kb 𝕜,
      Φ.symm (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ.symm c) := by
    intro c
    have h := hΦc (σ.symm c)
    rw [AlgEquiv.apply_symm_apply] at h
    exact (AlgEquiv.symm_apply_eq Φ).mpr h.symm
  have hΦratio' : ∀ i : Fin 5, Φ.symm (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
      / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 := by
    intro i
    exact (AlgEquiv.symm_apply_eq Φ).mpr (hΦratio i).symm
  have h1 := coeffAut_asFieldL_le D β.symm σ.symm hσβ' Φ.symm hΦc' hΦratio' (β g) (Φ x) hx
  rw [show β.symm (β g) = g from β.symm_apply_apply g] at h1
  rwa [AlgEquiv.symm_apply_apply] at h1

end Work.MotV5.Alpha
