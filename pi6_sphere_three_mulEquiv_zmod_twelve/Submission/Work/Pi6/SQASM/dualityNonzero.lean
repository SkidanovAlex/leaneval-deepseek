import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.kronH_natural
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.Pi6.SQASM.kronH_natural_commRing
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.SQASM

noncomputable section

/-- **Kronecker duality over a field is faithful on zero-ness.**  For a field `F` and a continuous
map `f : X → Y`, the induced map on singular cohomology `f^* : Hⁿ(Y;F) → Hⁿ(X;F)` (`Work.Pi6.cmap`)
vanishes if and only if the induced map on singular homology `f_* : Hₙ(X;F) → Hₙ(Y;F)`
(`Work.Pi6.hmap`) vanishes.  Route: the Kronecker pairing
`kronH F (TopCat.toSSet.obj X) n : Hⁿ(X;F) →ₗ (Hₙ(X;F) →ₗ[F] F)` is bijective over a field
(`Work.Cohomology.kronH_bijective_field`) and natural (`Work.Cohomology.kronH_natural` is proved
over `ℤ`; generalise its proof to an arbitrary `CommRing R`), so `f^*` is conjugate to the
transpose of `f_*`, and over a field a linear map is zero iff its transpose is. -/
theorem dualityNonzero (F : Type) [Field F] {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) :
    (Work.Pi6.cmap F f n ≠ 0) ↔ (Work.Pi6.hmap F f n ≠ 0) := by
  have hnat : ∀ (α : Coh F Y n) (c : HR F X n),
      Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of Y)) n α
          ((hmap F f n).hom c)
        = Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of X)) n
            ((cmap F f n).hom α) c := by
    intro α c
    exact kronH_natural_commRing F (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) n α c
  constructor
  · intro hc hh
    apply hc
    have hm : (hmap F f n).hom = 0 := by rw [hh, ModuleCat.hom_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    have hα : Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of X)) n
        ((cmap F f n).hom α) = 0 := by
      apply LinearMap.ext
      intro c
      rw [← hnat α c]
      simp only [hm, LinearMap.zero_apply, map_zero]
    exact (Work.Cohomology.kronH_bijective_field F (TopCat.toSSet.obj (TopCat.of X)) n).1
      (hα.trans (map_zero (Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of X)) n)).symm)
  · intro hh hc
    apply hh
    have hm : (cmap F f n).hom = 0 := by rw [hc, ModuleCat.hom_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (Module.forall_dual_apply_eq_zero_iff (V := ↥(HR F Y n)) F
      ((hmap F f n).hom c)).mp (fun φ => by
      obtain ⟨α, rfl⟩ := (Work.Cohomology.kronH_bijective_field F (TopCat.toSSet.obj (TopCat.of Y)) n).2 φ
      exact (hnat α c).trans (by simp only [hm, LinearMap.zero_apply, map_zero]))

end

end Work.Pi6.SQASM
