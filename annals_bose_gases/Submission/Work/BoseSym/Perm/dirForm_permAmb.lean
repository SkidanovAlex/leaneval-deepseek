import Mathlib.Data.Real.Basic
import Submission.Work.BoseSym.Perm.potSq_permAmb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Perm

/-- The Dirichlet form `dirForm W p = gSq p + potSq W p` is invariant under the
particle permutation action, for a permutation-invariant potential `W`.

Both summands are separately invariant: the kinetic part `gSq` because
`permAmb` permutes the gradient components and `permLp` is an isometry
(`gSq_permAmb`), and the potential part because of `potSq_permAmb`. -/
theorem dirForm_permAmb {N : ℕ} {W : Conf N → ℝ} (hW : ∀ σ x, W (tauPerm N σ x) = W x)
    (σ : Equiv.Perm (Fin N)) (p : Amb N) : dirForm W (permAmb N σ p) = dirForm W p := by
  simp only [dirForm]
  rw [gSq_permAmb σ p, potSq_permAmb hW σ p]

end Work.BoseSym.Perm
