import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB7.Estimates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.a_eq` — the inverse of the Bogoliubov substitution (FS `eq:asInTermsOfbs`)

FS solve `b_k = a_k + α_k a_{-k}†` for the bare annihilation operator:

  `a_k = (b_k - α_k b_{-k}†)/(1 - α_k²)`.

On the `FockData` interface this is a purely algebraic identity between the linear
operators `F.a i`, `F.bOp E.alpha i` and `F.bOpDag E.alpha (-i)`; the only
non-algebraic input is that the scalar `1 - α_i²` is invertible, i.e. non-zero.
Under the standing hypothesis `EstHyp` (`eq:BoverA`, `2|ℬ| ≤ 𝒜`, together with
`𝒜 > 0`) one has `|α_i| ≤ ½ < 1`, so `1 - α_i² ≥ ½ > 0`
(`Work.BoseB7.half_le_one_sub_alphaCoef_sq`, `one_sub_alphaCoef_sq_pos`).

The identity itself is the elementary cancellation

  `b_k - α_k b_{-k}† = (a_k + α_k a_{-k}†) - α_k (a_{-k}† + α_{-k} a_k)
    = (1 - α_k α_{-k}) a_k = (1 - α_k²) a_k`,

where `α_{-k} = α_k` is `EstHyp.alphaEven` and `α_k α_k = α_k²`.  We verify it
pointwise on `F.H` and then cancel the scalar `(1 - α_k²)⁻¹ (1 - α_k²) = 1`.
-/

noncomputable section

namespace Work.BoseB7

theorem a_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (h : Work.BoseB7.EstHyp F E) (i : Mode) :
    F.a i = (1 - E.alpha i ^ 2)⁻¹ • (F.bOp E.alpha i - (E.alpha i) • F.bOpDag E.alpha (-i)) := by
  -- `1 - α_i² > 0` from FS's smallness `2|ℬ_i| ≤ 𝒜_i` and `𝒜_i > 0`.
  have hpos : 0 < 1 - E.alpha i ^ 2 := by
    have hB : |E.B i| < E.A i := by
      have h1 := h.Bsmall i
      have h2 := abs_nonneg (E.B i)
      linarith [h.Apos i]
    exact one_sub_alphaCoef_sq_pos (h.Apos i) hB
  have hne : 1 - E.alpha i ^ 2 ≠ 0 := ne_of_gt hpos
  -- unfold `bOp`, `bOpDag`, use `α_{-i} = α_i` and `-(-i) = i`
  ext φ
  simp only [FockData.bOp, FockData.bOpDag, h.alphaEven i, neg_neg, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.add_apply]
  set A := F.a i φ
  set C := F.aDag (-i) φ
  set α := E.alpha i
  -- the cancellation `(a + α a†) - α(a† + α a) = (1-α²) a`, pointwise
  have hinner : A + α • C - α • (C + α • A) = (1 - α ^ 2) • A := by
    rw [smul_add, smul_smul, sq, sub_smul, one_smul]
    abel
  rw [hinner, smul_smul, inv_mul_cancel₀ hne, one_smul]

end Work.BoseB7
