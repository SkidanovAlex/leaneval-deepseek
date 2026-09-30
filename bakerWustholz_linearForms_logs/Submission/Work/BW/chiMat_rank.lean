import Mathlib
import Submission.Work.BW.wuestholzDefs
import Submission.Work.BW.ellW_eq_rank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The rank of the matrix of linear forms `chiFun` is `ℓ = dim W − dim (W ∩ Lie G')`, both for
`ε = true` (the `ρ` character rows) and for `ε = false` (adding the `G_a`-coordinate).  For
`ε = false` this is immediate from `ellW_eq_rank`; for `ε = true` one rewrites
`chiFun M (w k) (uIdxEmb j)` (where `uIdxEmb (ε := true) j = Fin.castSucc j`) to
`∑ i, M j i * w k i.succ`.  Both conjuncts close with a single `rw [ellW_eq_rank …]` plus the
`Fin`-index bookkeeping. -/
theorem chiMat_rank {N q ρ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (M : Fin ρ → Fin N → ℤ) :
    (chiMat w M true).rank = ellW w true M ∧ (chiMat w M false).rank = ellW w false M := by
  constructor
  · rw [(ellW_eq_rank w M).1]
    have hmat : chiMat w M true =
        Matrix.of (fun (j : Fin ρ) (k : Fin q) => ∑ i : Fin N, (M j i : ℂ) * w k i.succ) := by
      ext j k
      simp only [chiMat, Matrix.of_apply]
      rw [show uIdxEmb (ε := true) j = Fin.castSucc j from Fin.ext rfl, chiFun_castSucc]
    rw [hmat]
  · rw [(ellW_eq_rank w M).2]
    have hmat : chiMat w M false =
        Matrix.of (fun (j : Fin (ρ + 1)) (k : Fin q) => chiFun M (w k) j) := by
      ext j k
      simp only [chiMat, Matrix.of_apply]
      rw [show uIdxEmb (ε := false) j = j from Fin.ext rfl]
    rw [hmat]

end Work.BW
