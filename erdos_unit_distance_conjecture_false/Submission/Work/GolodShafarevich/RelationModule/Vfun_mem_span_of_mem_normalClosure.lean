import Mathlib
import Submission.Work.GolodShafarevich.Setup
import Submission.Work.GolodShafarevich.RelationModule.Defs

namespace Work.GolodShafarevich.RelationModule

theorem Vfun_mem_span_of_mem_normalClosure {k : Type*} [CommRing k] {d r : ℕ} {G : Type*} [Group G]
    (φ : FreeGroup (Fin d) →* G) (R : Fin r → FreeGroup (Fin d)) (hR : ∀ j, φ (R j) = 1)
    (n : FreeGroup (Fin d)) (hn : n ∈ Subgroup.normalClosure (Set.range R)) :
    Work.GolodShafarevich.Vfun k φ n ∈
      Submodule.span (MonoidAlgebra k G)
        (Set.range (fun j => Work.GolodShafarevich.Vfun k φ (R j))) := by
  -- The normal closure is the subgroup closure of all conjugates of the relators;
  -- induct on `n` lying in that closure.
  have hn' : n ∈ Subgroup.closure (Group.conjugatesOfSet (Set.range R)) := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem x hx =>
    -- A conjugate `c * R j * c⁻¹` of a relator: since `φ (R j) = 1`, its derivative
    -- vector is the scalar `of (φ c)` times the derivative vector of `R j`.
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ⟨j, rfl⟩, hc⟩ := hx
    rw [isConj_iff] at hc
    obtain ⟨c, rfl⟩ := hc
    rw [Work.GolodShafarevich.Vfun_conj k φ (hR j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  | one =>
    rw [Work.GolodShafarevich.Vfun_one]
    exact Submodule.zero_mem _
  | mul x y _ _ ihx ihy =>
    -- Fox chain rule: `V(x * y) = V(x) + of (φ x) • V(y)`.
    have hV : Work.GolodShafarevich.Vfun k φ (x * y) =
        Work.GolodShafarevich.Vfun k φ x +
          MonoidAlgebra.of k G (φ x) • Work.GolodShafarevich.Vfun k φ y := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact Work.GolodShafarevich.Vfun_mul k φ x y i
    rw [hV]
    exact Submodule.add_mem _ ihx (Submodule.smul_mem _ _ ihy)
  | inv x _ ihx =>
    rw [Work.GolodShafarevich.Vfun_inv]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ ihx)

end Work.GolodShafarevich.RelationModule
