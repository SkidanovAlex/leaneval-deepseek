import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SdIter
import Submission.Work.Cohomology.exists_iter_small
import Submission.Work.Cohomology.exists_small_homotopy
import Submission.Work.Cohomology.Sd_isSmallChain
import Submission.Work.SSSR.Cohomology.Chains
import Submission.Work.SSSR.Cohomology.Sd_comm
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Cohomology
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
namespace Work.SSSR.Cohomology

noncomputable section

variable {X : TopCat}

/-! ## The generators span the singular chains -/

/-- **A submodule of the singular chains which contains every generator is everything.** -/
theorem mem_of_gen (X : TopCat) (n : ℕ) (P : Submodule R ↥((singularChains R X).X n))
    (hgen : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌, gen X n σ ∈ P) : P = ⊤ := by
  letI : Module R (↥((singularChains R X).X n) ⧸ P) := Submodule.Quotient.module P
  let q : (singularChains R X).X n ⟶ ModuleCat.of R (↥((singularChains R X).X n) ⧸ P) :=
    ModuleCat.ofHom (Submodule.mkQ P)
  have hleg : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌,
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ ≫ q = 0 := by
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    show Submodule.Quotient.mk (gen X n σ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hgen σ
  have hq : q = 0 := by
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := ModuleCat.of R R) (n := n)
    intro σ
    simpa using hleg σ
  refine Submodule.eq_top_iff'.mpr fun c => ?_
  have h2 : ModuleCat.Hom.hom q c = ModuleCat.Hom.hom (0 : (singularChains R X).X n ⟶
      ModuleCat.of R (↥((singularChains R X).X n) ⧸ P)) c := by rw [hq]
  rw [ModuleCat.hom_zero, LinearMap.zero_apply] at h2
  have h3 : ModuleCat.Hom.hom q = Submodule.mkQ P := rfl
  rw [h3, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

end

end Work.SSSR.Cohomology
