import Mathlib
import Submission.Work.PTCert.labelData
import Submission.Work.PTCert.sigmaGroupFacts

namespace Work.PTCert

/-! Guidance from the project lead (the requester): these are the conjugator witnesses used by
`labelPrinciple` in the proof of `LabelIdentity` (`Submission/Work/PTCert/labelIdentity.lean`).
Read `Submission/Work/PTCert/labelData.lean` first: it defines `TIdx`, `tElt`, `tLab`, `labRep` and
provides the three `ClassSem` witnesses `key_conj`, `tgt_conj`, `res_conj`.

Case-split on `t : TIdx = (Σ r : Fin 18, Fin (ngE r.1)) ⊕ Fin 6561 ⊕ (Fin ncls × Bool)`:
* `t = Sum.inl ⟨r, g⟩`: `tElt t = lprod 5 (keyWord r.1 g.1)`, `tLab t = gcls (keyOf r.1 g.1)`,
  `labRep (tLab t) = lprod 5 (canonW (gcls (keyOf r.1 g.1)))` — `labelData.key_conj` gives the σ.
* `t = Sum.inr (Sum.inl p)`: `labelData.tgt_conj` (with `p.1 < 6561`).
* `t = Sum.inr (Sum.inr (c, false))`: take `σ = 1`, which lies in `Sg` by
  `(Submission.Work.PTCert.sigmaGroupFacts 5).1.1`; `labRep c.1 = lprod 5 (canonW c.1) = tElt t`.
* `t = Sum.inr (Sum.inr (c, true))`: `labelData.res_conj` (with `c.1 < ncls`), whose conclusion is
  `σ * (lprod 5 (canonW c.1))⁻¹ * σ⁻¹ = lprod 5 (canonW (icls c.1))`, matching `tElt`/`tLab`.

Watch the definitional reductions of `tElt`, `tLab`, `labRep` on the constructors; `Nat` coercions
`c.1` versus `↑c` should be handled by `simp`/`exact`. -/

open Submission.PTCert Submission.PTCert.G
open Work.PTCert.LabelData
open scoped BigOperators

set_option maxRecDepth 10000

/-- **The conjugator witnesses.**  Every term of the labelled decomposition `Σ_{t : TIdx} tCoef t •
of (tElt t)` of a certificate is conjugate (by an element of the signed-permutation group
`Sg = SigmaSet 5`) to the representative `labRep (tLab t)` of its label.  This is exactly the
`hconj` hypothesis consumed by `labelPrinciple`. -/
theorem conjWitness (hC : ClassSem) (t : TIdx) :
    ∃ σ ∈ Sg, σ * tElt t * σ⁻¹ = labRep (tLab t) := by
  rcases t with t | t
  · -- keys: `(r, g)` ↦ `gcls (keyOf r g)`
    obtain ⟨r, g⟩ := t
    exact key_conj hC r.2 g.2
  · rcases t with t | t
    · -- targets: `p` ↦ `tcls p`
      exact tgt_conj hC t.2
    · -- residual classes, with sign
      obtain ⟨c, b⟩ := t
      rcases b with _ | _
      · -- `+`: the class itself, conjugated by `1`
        exact ⟨1, (sigmaGroupFacts 5).1.1, by simp [tElt, tLab, labRep]⟩
      · -- `-`: the inverse class `icls c`
        exact res_conj hC c.2

end Work.PTCert
