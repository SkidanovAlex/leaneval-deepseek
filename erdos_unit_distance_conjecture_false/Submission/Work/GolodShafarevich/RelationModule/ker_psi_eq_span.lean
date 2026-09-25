import Mathlib
import Submission.Work.GolodShafarevich.Defs
import Submission.Work.GolodShafarevich.Setup
import Submission.Work.GolodShafarevich.RelationModule.Defs
import Submission.Work.GolodShafarevich.RelationModule.psi_id_injective
import Submission.Work.GolodShafarevich.RelationModule.Vfun_mem_span_of_mem_normalClosure
import Submission.Work.GolodShafarevich.RelationModule.ker_groupAlgMap
import Submission.Work.GolodShafarevich.RelationModule.ker_psi_le_span_comp

/-!
# The kernel of `ψ` is the relation module

`ker ψ = span_{k[G]} { V (R j) }`, where `V` is the Fox derivative vector and
`R` a set of relators whose normal closure is `ker φ`.
-/

open scoped MonoidAlgebra

namespace Work.GolodShafarevich.RelationModule

open Work.GolodShafarevich

variable {k : Type*} [CommRing k] {d : ℕ}

/-- The Fox derivative vector for `φ` is obtained from the one for the identity
by applying `groupAlgMap`. -/
theorem Vfun_eq_mapDomain_id {G : Type*} [Group G] (φ : FreeGroup (Fin d) →* G)
    (w : FreeGroup (Fin d)) :
    Vfun k φ w = fun i => groupAlgMap k φ (Vfun k (MonoidHom.id (FreeGroup (Fin d))) w i) := by
  change Vfun k φ w = fun i =>
    MonoidAlgebra.mapDomainAlgHom k k φ (Vfun k (MonoidHom.id (FreeGroup (Fin d))) w i)
  rw [← Vfun_comp (ι := φ) (f := MonoidHom.id (FreeGroup (Fin d))), MonoidHom.comp_id]

/-- The hard inclusion in the surjective case. -/
theorem ker_psi_le_span_surjective {G : Type*} [Group G]
    (φ : FreeGroup (Fin d) →* G) (hφ : Function.Surjective φ) {r : ℕ}
    (R : Fin r → FreeGroup (Fin d)) (hR : φ.ker = Subgroup.normalClosure (Set.range R)) :
    LinearMap.ker (psi k φ) ≤
      Submodule.span (MonoidAlgebra k G) (Set.range (fun j => Vfun k φ (R j))) := by
  have hR1 : ∀ j, φ (R j) = 1 := fun j =>
    MonoidHom.mem_ker.mp (hR ▸ Subgroup.subset_normalClosure ⟨j, rfl⟩)
  intro x hx
  rw [LinearMap.mem_ker] at hx
  -- lift `x` along the surjection `k[F_d] → k[G]`
  have hsurj : ∀ i : Fin d, ∃ a : MonoidAlgebra k (FreeGroup (Fin d)),
      groupAlgMap k φ a = x i := fun i => groupAlgMap_surjective φ hφ (x i)
  choose xt hxt using hsurj
  -- `ψ̃ xt` lies in the kernel of `groupAlgMap k φ`
  have hbker : psi k (MonoidHom.id (FreeGroup (Fin d))) xt ∈ RingHom.ker (groupAlgMap k φ) := by
    rw [RingHom.mem_ker, groupAlgMap_psi_id]
    rw [show (fun i => groupAlgMap k φ (xt i)) = x from funext hxt, hx]
  rw [ker_groupAlgMap] at hbker
  -- the span of `of n - 1` lies in the image of `ψ̃` applied to the relation vectors
  set P : Submodule (MonoidAlgebra k (FreeGroup (Fin d)))
      (Fin d → MonoidAlgebra k (FreeGroup (Fin d))) :=
    Submodule.span (MonoidAlgebra k (FreeGroup (Fin d)))
      (Set.range (fun n : φ.ker =>
        Vfun k (MonoidHom.id (FreeGroup (Fin d))) (n : FreeGroup (Fin d)))) with hP
  have hle : Submodule.span (MonoidAlgebra k (FreeGroup (Fin d)))
      (Set.range (fun n : φ.ker =>
        MonoidAlgebra.of k (FreeGroup (Fin d)) (n : FreeGroup (Fin d)) - 1)) ≤
      Submodule.map (psi k (MonoidHom.id (FreeGroup (Fin d)))) P := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    refine Submodule.mem_map.mpr ⟨Vfun k (MonoidHom.id (FreeGroup (Fin d))) (n : FreeGroup (Fin d)),
      Submodule.subset_span ⟨n, rfl⟩, ?_⟩
    rw [psi_Vfun]
    rfl
  obtain ⟨y, hyP, hyb⟩ := Submodule.mem_map.mp (hle hbker)
  have hyx : y = xt := psi_id_injective hyb
  have hxtP : xt ∈ P := hyx ▸ hyP
  -- push forward along `groupAlgMap`
  have hmain : ∀ z ∈ P, (fun i => groupAlgMap k φ (z i)) ∈
      Submodule.span (MonoidAlgebra k G) (Set.range (fun j => Vfun k φ (R j))) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨n, rfl⟩ := hv
      rw [← Vfun_eq_mapDomain_id]
      exact Vfun_mem_span_of_mem_normalClosure φ R hR1 (n : FreeGroup (Fin d)) (hR ▸ n.2)
    | zero =>
      have h0 : (fun i => groupAlgMap k φ
          ((0 : Fin d → MonoidAlgebra k (FreeGroup (Fin d))) i)) = 0 := by
        ext i; simp
      rw [h0]; exact Submodule.zero_mem _
    | add a b _ _ iha ihb =>
      have h : (fun i => groupAlgMap k φ ((a + b) i)) =
          (fun i => groupAlgMap k φ (a i)) + (fun i => groupAlgMap k φ (b i)) := by
        ext i; simp [Pi.add_apply]
      rw [h]; exact Submodule.add_mem _ iha ihb
    | smul c a _ iha =>
      have h : (fun i => groupAlgMap k φ ((c • a) i)) =
          (groupAlgMap k φ c) • (fun i => groupAlgMap k φ (a i)) := by
        ext i; simp [Pi.smul_apply, smul_eq_mul]
      rw [h]; exact Submodule.smul_mem _ _ iha
  rw [show x = (fun i => groupAlgMap k φ (xt i)) from funext (fun i => (hxt i).symm)]
  exact hmain xt hxtP

/-- The kernel of `ψ` is the relation module, i.e. the span of the Fox derivative
vectors of the relators. -/
theorem ker_psi_eq_span {k : Type*} [CommRing k] {d r : ℕ} {G : Type*} [Group G]
    (φ : FreeGroup (Fin d) →* G) (R : Fin r → FreeGroup (Fin d))
    (hR : φ.ker = Subgroup.normalClosure (Set.range R)) :
    LinearMap.ker (psi k φ) =
      Submodule.span (MonoidAlgebra k G) (Set.range (fun j => Vfun k φ (R j))) := by
  have hR1 : ∀ j, φ (R j) = 1 := fun j =>
    MonoidHom.mem_ker.mp (hR ▸ Subgroup.subset_normalClosure ⟨j, rfl⟩)
  refine le_antisymm ?_ (span_le_ker_psi φ R hR1)
  have hker : φ.rangeRestrict.ker = Subgroup.normalClosure (Set.range R) := by
    rw [MonoidHom.ker_rangeRestrict, hR]
  exact ker_psi_le_span_comp φ.range.subtype (Subgroup.subtype_injective _) φ.rangeRestrict R
    (ker_psi_le_span_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ) R hker)

end Work.GolodShafarevich.RelationModule
