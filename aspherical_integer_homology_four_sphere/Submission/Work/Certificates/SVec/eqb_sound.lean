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


namespace Work.Certificates.SVec

/-- Normalisation of a sparse vector preserves its semantics: dropping zero coefficients and
combining equal indices does not change the represented element of `Fin n → ℤ`.  This is proved
by induction on the list, using that `insert` adds exactly the contribution of the inserted
pair (`toFun_insert`) and that `toFun` is additive under concatenation (`toFun_append`). -/
private theorem toFun_norm_aux {n : ℕ} (v : SVec n) : toFun (norm v) = toFun v := by
  induction v with
  | nil => rfl
  | cons p ps ih =>
    have h1 : norm (p :: ps) = insert p (norm ps) := rfl
    rw [h1, toFun_insert, ih, show p :: ps = [p] ++ ps from rfl, toFun_append]

/-- Soundness of the sparse equality test: `eqb` compares normal forms, and normalisation
preserves `toFun`, so vectors with equal normal forms represent the same function
`Fin n → ℤ`. -/
theorem eqb_sound {n : ℕ} {a b : List (Fin n × ℤ)} (h : eqb a b = true) :
    toFun a = toFun b := by
  have h' : norm a = norm b := of_decide_eq_true (by simpa [eqb] using h)
  rw [← toFun_norm_aux a, h', toFun_norm_aux b]

end Work.Certificates.SVec
