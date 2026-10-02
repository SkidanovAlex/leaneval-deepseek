import Mathlib
import Submission.Work.SignatureBordism.Intersection
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.kronH_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Naturality of the intersection form under pullback

Let `f : X ⟶ Y` be a continuous map and `c ∈ H_{2k}(X;R)` a homology class.  The intersection
form of `X` (see `Submission/Work/SignatureBordism/Intersection.lean`) evaluated on the pullbacks
of two cohomology classes `x, x' ∈ H^k(Y;R)` equals the intersection form of `Y` evaluated on
`x, x'` against the push-forward `f_* c`:

`interForm ℝ X k k c (f*x) (f*x') = interForm ℝ Y k k (f_* c) x x'`.

This is the combination of two naturalities:

* `Work.Cohomology.cupNaturalH` — the cup product is natural under pullback,
  `f*(x ⌣ x') = f*x ⌣ f*x'`;
* `Work.Cohomology.kronH_natural` — the Kronecker pairing satisfies
  `⟨α, f_* c⟩ = ⟨f* α, c⟩`.

Both sides are written out with `interForm_apply` as a Kronecker pairing of a cup product, and then
these two lemmas identify them.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Bordism

theorem interForm_pullback {X Y : TopCat} (f : X ⟶ Y) (k : ℕ)
    (c : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj X)).homology (k + k))
    (x x' : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj Y)).homology k) :
    Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj X) k k c
        (Work.Cohomology.singularCohomologyMap ℤ X Y f k x)
        (Work.Cohomology.singularCohomologyMap ℤ X Y f k x')
      = Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj Y) k k
          (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) (k + k) c) x x' := by
  rw [Work.SignatureBordism.interForm_apply, Work.SignatureBordism.interForm_apply]
  rw [Work.Cohomology.kronH_natural X Y f (k + k)
    (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Y) k k x x') c]
  rw [← Work.Cohomology.cupNaturalH ℤ f k k x x']

end Work.Bordism
