import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Kunneth.kunnethCrossExistence
import Submission.Work.Kunneth.CohKunneth.Value

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Kunneth

theorem kunnethCoh_value (X Y : SSet) (n : ℕ)
    (hYproj : ∀ q, Module.Projective ℤ ↥((Work.Kunneth.sChain Y).X q))
    (hYfree : ∀ q, Module.Free ℤ ↥((Work.Kunneth.sChain Y).homology q))
    (hYfin : ∀ q, Module.Finite ℤ ↥((Work.Kunneth.sChain Y).homology q)) :
    ∃ e : ((Work.Cohomology.cochainC ℤ (Work.Kunneth.sProd X Y)).homology n)
        ≅ Work.Kunneth.kunnethTarget X Y n,
      ∀ (p q : ℕ) (hpq : p + q = n)
        (a : ↥((Work.Cohomology.cochainC ℤ X).homology p))
        (b : ↥((Work.Cohomology.cochainC ℤ Y).homology q)),
        e.hom.hom (CategoryTheory.eqToHom (congrArg (fun k => (Work.Cohomology.cochainC ℤ
            (Work.Kunneth.sProd X Y)).homology k) hpq) (Work.Kunneth.crossH X Y p q a b))
          ⟨(p, q), hpq⟩ = a ⊗ₜ[ℤ] b := by
  exact kunnethCoh_value_aux X Y n hYproj hYfree hYfin

end Work.Kunneth
