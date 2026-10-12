import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Submission.Work.BoseB7.spectLe_nOp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.bp_aDag_self_le` — one creation operator at a spectral state

FS §10 constantly needs to bound the norm of a state to which a *single*
creation operator has been applied, e.g. when Cauchy–Schwarz is applied to
`Σ_s c_s ã_s†(…)`.  The relevant identity is the CCR at coinciding indices:

  `‖a_k†Φ‖² = ⟨Φ, a_k a_k† Φ⟩ = ⟨Φ, (a_k†a_k + ccrK k k)Φ⟩ = ‖a_kΦ‖² + ccrK k k‖Φ‖²`

(`aDag_adjoint`, then `ccr`), and both terms are controlled by one hypothesis:
`‖a_kΦ‖² = ⟨Φ, n_kΦ⟩ ≤ 𝓜‖Φ‖²` is the spectral window restricted to the single
mode `k` (`Work.BoseB7.spectLe_nOp`), while `ccrK k k ≤ 1` is the box-commutator
bound `hccr` (in the symmetric case `ccrK k k = ccrK (-k) (-k)`).

The statement is written for `-i` with `hi : i ≠ 0`, i.e. for `k = -i`, the
mode that occurs in the definitions of `bOp`/`bOpDag`.

## Contents

* `FockData.bp_aDag_self` — the CCR identity `‖a_k†Φ‖² = ‖a_kΦ‖² + ccrK k k‖Φ‖²`
  for an arbitrary mode `k`.
* `bp_aDag_self_le` — the requested bound, at a state in FS's spectral window.
-/

noncomputable section

namespace Work.BoseB7

/-- **The CCR identity at coinciding indices.**  Applying `a_k` to `a_k†Φ` and
using `[a_k, a_k†] = ccrK k k`, the Fock norm of the created state is

  `‖a_k†Φ‖² = ⟨Φ, a_k a_k† Φ⟩ = ⟨Φ, a_k†a_k Φ⟩ + ccrK k k·‖Φ‖² = ‖a_kΦ‖² + ccrK k k‖Φ‖²`.

No hypothesis on `k` is used; `ccrK k k` need not be real-positive. -/
theorem FockData.bp_aDag_self {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode) (k : Mode) (Φ : F.H) :
    F.bp (F.aDag k Φ) (F.aDag k Φ)
      = F.bp (F.a k Φ) (F.a k Φ) + F.ccrK k k * F.normSq Φ := by
  -- `a_k (a_k† Φ) = a_k† (a_k Φ) + ccrK k k • Φ`
  have hcomm : F.a k (F.aDag k Φ) = F.aDag k (F.a k Φ) + F.ccrK k k • Φ := by
    have h := LinearMap.congr_fun (F.ccr k k) Φ
    simpa using h
  rw [F.aDag_adjoint k Φ (F.aDag k Φ), hcomm, map_add, map_smul, smul_eq_mul,
    FockData.normSq]
  rw [F.bp_symm Φ (F.aDag k (F.a k Φ)), F.aDag_adjoint k (F.a k Φ) Φ]

/-- **One creation operator at a state in the spectral window.**  If
`⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²` and `|ccrK k k| ≤ 1`, then for `k = -i ≠ 0`

  `‖a_k†Φ‖² ≤ (𝓜 + 1)‖Φ‖²`.

The two summands of the CCR identity are estimated by the spectral window
(`spectLe_nOp`, single mode `k ≠ 0`) and by `ccrK k k ≤ |ccrK k k| ≤ 1`. -/
theorem bp_aDag_self_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (i : Mode) {Φ : F.H}
    (hspec : F.SpectLe E.bigM Φ) (hi : i ≠ 0) (hccr : |F.ccrK (-i) (-i)| ≤ 1) :
    F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ) ≤ (E.bigM + 1) * F.normSq Φ := by
  have hne : (-i : Mode) ≠ 0 := neg_ne_zero.mpr hi
  -- the CCR identity at `k = -i`
  have hkey := F.bp_aDag_self (-i) Φ
  -- the single-mode spectral window
  have hspec' : F.bp (F.nOp (-i) Φ) Φ ≤ E.bigM * F.normSq Φ :=
    spectLe_nOp F E hspec (-i) hne
  have hkin : F.bp (F.a (-i) Φ) (F.a (-i) Φ) ≤ E.bigM * F.normSq Φ := by
    simpa only [FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint] using hspec'
  -- the commutator is at most `1`
  have hccr' : F.ccrK (-i) (-i) ≤ 1 := le_trans (le_abs_self _) hccr
  have hnorm : 0 ≤ F.normSq Φ := F.bp_nonneg Φ
  have hcomm : F.ccrK (-i) (-i) * F.normSq Φ ≤ 1 * F.normSq Φ :=
    mul_le_mul_of_nonneg_right hccr' hnorm
  linarith [hkey, hkin, hcomm]

end Work.BoseB7
