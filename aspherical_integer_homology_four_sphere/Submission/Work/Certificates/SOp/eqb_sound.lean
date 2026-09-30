import Mathlib
import Submission.Work.Certificates.Sparse
import Submission.Work.Certificates.SVec.toFun_append
import Submission.Work.Certificates.SVec.toFun_insert

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates

namespace SVec

/-- Normalisation of a sparse vector preserves its semantics: dropping zero coefficients and
combining equal indices does not change the represented element of `Fin n → ℤ`. -/
private theorem toFun_norm {n : ℕ} (v : SVec n) : toFun (norm v) = toFun v := by
  induction v with
  | nil => rfl
  | cons p ps ih =>
    have h1 : norm (p :: ps) = insert p (norm ps) := rfl
    rw [h1, toFun_insert, ih, show p :: ps = [p] ++ ps from rfl, toFun_append]

end SVec

namespace SOp

/-- Soundness of the sparse equality test for operators: if `eqb A B` returns `true`, then the
two sparse operators represent the same matrix.  Componentwise it reduces to the fact that
`eqb` compares normal forms and that `SVec.norm` preserves the semantics `SVec.toFun`. -/
theorem eqb_sound {n m : ℕ} {A B : SOp n m} (h : eqb A B = true) :
    toMatrix A = toMatrix B := by
  ext i j
  have hj := List.mem_finRange j
  have h1 : (A.img j).eqb (B.img j) = true := (List.all_eq_true.mp h) j hj
  have h2 : SVec.norm (A.img j) = SVec.norm (B.img j) := by
    simpa [SVec.eqb] using h1
  simp only [SOp.toMatrix]
  rw [← SVec.toFun_norm (A.img j), ← SVec.toFun_norm (B.img j), h2]

end SOp

end Work.Certificates
