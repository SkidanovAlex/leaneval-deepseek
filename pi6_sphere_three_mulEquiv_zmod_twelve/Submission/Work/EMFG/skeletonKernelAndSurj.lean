import Mathlib
import Submission.Work.EMFG.skeletonAux
import Submission.Work.EMFG.skeletonCellClasses_generate

/-!
# The `k = 1` comparison: kernel and surjectivity of the two structure maps of the `1`-skeleton

Let `Z` and `P` be two range models of `K(A,1)` (i.e. `Work.Serre.IsEMSpaceUpTo A 1 N`), with a
group isomorphism `Λ : π₁(Z,z₀) ≃* π₁(P,p₀)` obtained from the two model structures.  We consider
the two maps out of the `1`-skeleton `Skeleton Z z₀` (the wedge of one circle per based loop of
`Z`):

* `skeletonMap Z z₀ : Skeleton Z z₀ → Z`, the structure map of the skeleton of `Z`;
* `skeletonLoopMap z₀ p₀ Λ : Skeleton Z z₀ → P`, sending the cell of `w` to a loop of `P`
  representing `Λ [w]`.

This file proves, in the form needed by the `k = 1` comparison, that

* both induced maps `π₁(Skeleton Z z₀) → π₁(Z,z₀)` and `π₁(Skeleton Z z₀) → π₁(P,p₀)` are
  **surjective**, and
* they have the **same kernel**.

The single computation behind both is `piMapN_skeletonLoopMap_eq`:
`π₁ (skeletonLoopMap Λ) = Λ ∘ π₁ (skeletonMap)`, which follows from
`Work.EMFG.skeletonCellClasses_generate` (the `1`-cells generate `π₁` of the skeleton) together
with the two cell-class computations `piMapN_skeletonMap_skeletonCellClass` and
`piMapN_skeletonLoopMap_skeletonCellClass`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.EMFG

open Work.Serre.SPC

noncomputable section

/-- **The computation of `π₁` of the loop map**: on `π₁`, `skeletonLoopMap z₀ p₀ Λ` is `Λ`
composed with the structure map `skeletonMap Z z₀`.  Since the `1`-cells generate `π₁` of the
skeleton, it suffices to check this on the cell classes. -/
theorem piMapN_skeletonLoopMap_eq {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    {P : Type} [TopologicalSpace P] (p₀ : P)
    (Λ : HomotopyGroup (Fin 1) Z z₀ ≃* HomotopyGroup (Fin 1) P p₀) :
    ∀ α : HomotopyGroup (Fin 1) (Skeleton Z z₀) (skeletonBase Z z₀),
      Work.Serre.piMapN (skeletonLoopMap z₀ p₀ Λ) 1 (skeletonBase Z z₀) α
        = Λ (Work.Serre.piMapN (skeletonMap Z z₀) 1 (skeletonBase Z z₀) α) := by
  intro α
  -- the two group homomorphisms out of `π₁(Skeleton Z z₀)` to be shown equal
  let ψ : HomotopyGroup (Fin 1) (Skeleton Z z₀) (skeletonBase Z z₀) →* HomotopyGroup (Fin 1) P p₀ :=
    Work.StemsB.πmap (skeletonLoopMap z₀ p₀ Λ) 0 (skeletonBase Z z₀)
  let χ : HomotopyGroup (Fin 1) (Skeleton Z z₀) (skeletonBase Z z₀) →* HomotopyGroup (Fin 1) P p₀ :=
    Λ.toMonoidHom.comp (Work.StemsB.πmap (skeletonMap Z z₀) 0 (skeletonBase Z z₀))
  have hgen : Subgroup.closure (Set.range (skeletonCellClass Z z₀)) = ⊤ :=
    skeletonCellClass_closure_eq_top Z z₀
  -- the two homomorphisms agree on the cell classes
  have key : ∀ β ∈ Subgroup.closure (Set.range (skeletonCellClass Z z₀)), ψ β = χ β := by
    intro β hβ
    refine Subgroup.closure_induction (p := fun γ _ => ψ γ = χ γ) ?_ ?_ ?_ ?_ hβ
    · intro x hx
      obtain ⟨w, rfl⟩ := hx
      change Work.Serre.piMapN (skeletonLoopMap z₀ p₀ Λ) 1 (skeletonBase Z z₀)
          (skeletonCellClass Z z₀ w)
        = Λ (Work.Serre.piMapN (skeletonMap Z z₀) 1 (skeletonBase Z z₀)
            (skeletonCellClass Z z₀ w))
      rw [piMapN_skeletonLoopMap_skeletonCellClass, piMapN_skeletonMap_skeletonCellClass]
      rfl
    · rw [map_one, map_one]
    · intro x y _ _ hx hy
      rw [map_mul, map_mul, hx, hy]
    · intro x _ hx
      rw [map_inv, map_inv, hx]
  have hfun : ψ = χ := skeletonCellClasses_generate Z z₀ ψ χ (fun w => key _ (by
    rw [hgen]; exact Subgroup.mem_top _))
  change ψ α = χ α
  rw [hfun]

/-- **The loop map is surjective on `π₁`**: `Λ` is a group isomorphism and `skeletonMap` is onto on
`π₁`. -/
theorem skeletonLoopMap_piMapN_surjective {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    {P : Type} [TopologicalSpace P] (p₀ : P)
    (Λ : HomotopyGroup (Fin 1) Z z₀ ≃* HomotopyGroup (Fin 1) P p₀) :
    Function.Surjective (Work.Serre.piMapN (skeletonLoopMap z₀ p₀ Λ) 1 (skeletonBase Z z₀)) := by
  intro β
  obtain ⟨α, hα⟩ := skeletonMap_piOne_surjective Z z₀ (Λ.symm β)
  refine ⟨α, ?_⟩
  rw [piMapN_skeletonLoopMap_eq z₀ p₀ Λ α, hα]
  exact MulEquiv.apply_symm_apply Λ β

/-- **Kernel and surjectivity of the two structure maps of the `1`-skeleton.**  For two range
models `Z`, `P` of `K(A,1)` with the group isomorphism `Λ` between their `π₁`, the structure maps
`skeletonMap Z z₀ : Skeleton Z z₀ → Z` and `skeletonLoopMap z₀ p₀ Λ : Skeleton Z z₀ → P` are both
surjective on `π₁`, and they have the same kernel. -/
theorem skeletonKernelAndSurj (A : Type) [AddCommGroup A] (N : ℕ)
    (Z : Type) [TopologicalSpace Z] (z₀ : Z)
    (hZ : Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N Z z₀)
    (P : Type) [TopologicalSpace P] (p₀ : P)
    (hP : Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N P p₀) :
    Function.Surjective (Work.Serre.piMapN (Work.Serre.SPC.skeletonMap Z z₀) 1
        (Work.Serre.SPC.skeletonBase Z z₀))
    ∧ Function.Surjective (Work.Serre.piMapN
        (Work.EMFG.skeletonLoopMap z₀ p₀ (hZ.1.some.trans hP.1.some.symm)) 1
        (Work.Serre.SPC.skeletonBase Z z₀))
    ∧ (∀ a : HomotopyGroup (Fin 1) (Work.Serre.SPC.Skeleton Z z₀) (Work.Serre.SPC.skeletonBase Z z₀),
        Work.Serre.piMapN (Work.Serre.SPC.skeletonMap Z z₀) 1 (Work.Serre.SPC.skeletonBase Z z₀) a = 1 ↔
        Work.Serre.piMapN (Work.EMFG.skeletonLoopMap z₀ p₀ (hZ.1.some.trans hP.1.some.symm)) 1
          (Work.Serre.SPC.skeletonBase Z z₀) a = 1) := by
  refine ⟨Work.Serre.SPC.skeletonMap_piOne_surjective Z z₀,
    skeletonLoopMap_piMapN_surjective z₀ p₀ (hZ.1.some.trans hP.1.some.symm), ?_⟩
  intro a
  rw [piMapN_skeletonLoopMap_eq z₀ p₀ (hZ.1.some.trans hP.1.some.symm) a]
  exact (MulEquiv.map_eq_one_iff (hZ.1.some.trans hP.1.some.symm)).symm

end

end Work.EMFG
