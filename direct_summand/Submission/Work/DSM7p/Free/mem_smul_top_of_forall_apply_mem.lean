import Mathlib

namespace Work.DSM7p.Free

universe a

/-- If every value of a linear functional on a finite free module `F` lies in an ideal `I`, then the
functional lies in `I • ⊤` (finiteness of `F` is essential). -/
theorem mem_smul_top_of_forall_apply_mem {A : Type a} [CommRing A]
    {F : Type a} [AddCommGroup F] [Module A F] [Module.Free A F] [Module.Finite A F]
    (I : Ideal A) (f : F →ₗ[A] A) (h : ∀ x : F, f x ∈ I) :
    f ∈ (I • ⊤ : Submodule A (F →ₗ[A] A)) := by
  classical
  -- A finite free module has a finite basis `b`; expand `f` in the dual basis `b.coord`.
  let b := Module.Free.chooseBasis A F
  rw [← Module.Basis.sum_dual_apply_smul_coord b f]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem_smul (h (b i)) Submodule.mem_top

end Work.DSM7p.Free
