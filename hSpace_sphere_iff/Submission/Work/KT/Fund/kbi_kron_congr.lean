import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.k0_basic

namespace Work.KT.Fund

/-- The product of `K₀` respects the classes of idempotents: for `CommRing R` and idempotents
`a, a', b, b'`, equal classes imply equal classes of the Kronecker products.  This is the
well-definedness of the ring multiplication `[p]·[q] = [p ⊗ q]` (`Work.KT.k0Mul`) on the classes
of idempotents (`Work.KT.k0Mul_cls_kron`). -/
theorem kbi_kron_congr {R : Type} [CommRing R] (a a' b b' : Work.KT.Mat R)
    (ha : a.IsIdem) (ha' : a'.IsIdem) (hb : b.IsIdem) (hb' : b'.IsIdem)
    (h1 : Work.KT.cls a = Work.KT.cls a') (h2 : Work.KT.cls b = Work.KT.cls b') :
    Work.KT.cls (a.kron b) = Work.KT.cls (a'.kron b') := by
  have hcomm : ∀ x y : R, x * y = y * x := fun x y => mul_comm x y
  rw [← Work.KT.k0Mul_cls_kron (A := R) hcomm ha hb,
    ← Work.KT.k0Mul_cls_kron (A := R) hcomm ha' hb', h1, h2]

end Work.KT.Fund
