import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.BoseB7.spectLe_nOp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.a_aDag_le` — the quadratic form of `a_k a_k†` inside the window

On the `FockData` interface the commutator `[a_i, a_i†] = F.ccrK i i` is a
*scalar* (`FockData.ccr`), so for every state `Φ`

  `a_i a_i† Φ = a_i† a_i Φ + (ccrK i i) • Φ`.

Taking the `bp`-quadratic form and using that `a_i†` is the `bp`-adjoint of `a_i`
gives the exact identity

  `⟨Φ, a_i a_i† Φ⟩ = ‖a_i Φ‖² + ccrK i i · ‖Φ‖²`.

The two terms are then bounded by the spectral window: `‖a_i Φ‖² = ⟨Φ, n_i Φ⟩ ≤
𝓜‖Φ‖²` (`Work.BoseB7.spectLe_nOp`) and `ccrK i i · ‖Φ‖² ≤ |ccrK i i| · ‖Φ‖² ≤
‖Φ‖²` under the hypothesis `|ccrK i i| ≤ 1`.  Hence

  `⟨Φ, a_i a_i† Φ⟩ ≤ (𝓜 + 1)‖Φ‖²`,

which is the factor of `𝓜 + 1` that the error functions `err1`, `err4` and
`controlErr` of FS §10 carry (FS's `𝓜` count of excited particles plus the
diagonal commutator of the mode).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

/-- **The quadratic form of `a_i a_i†`.**  Inside FS's spectral window
`⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²`, and assuming the mode's diagonal commutator is controlled by
`|ccrK i i| ≤ 1`, the state `a_i a_i† Φ` costs at most `𝓜 + 1` per unit of `‖Φ‖²`:

  `⟨Φ, a_i a_i† Φ⟩ ≤ (𝓜 + 1)‖Φ‖²`. -/
theorem a_aDag_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (i : Mode) {Φ : F.H}
    (hspec : F.SpectLe E.bigM Φ) (hi : i ≠ 0) (hccr : |F.ccrK i i| ≤ 1) :
    F.bp (F.a i (F.aDag i Φ)) Φ ≤ (E.bigM + 1) * F.normSq Φ := by
  -- the CCR at the operator level, evaluated at `Φ`
  have hpt : F.a i (F.aDag i Φ) = F.aDag i (F.a i Φ) + (F.ccrK i i) • Φ := by
    have h := congrArg (fun (T : F.H →ₗ[ℝ] F.H) => T Φ) (F.ccr i i)
    simpa using h
  -- linearity of `bp` in its first argument + adjointness: the exact identity
  have hsplit : F.bp (F.a i (F.aDag i Φ)) Φ
      = F.bp (F.a i Φ) (F.a i Φ) + F.ccrK i i * F.normSq Φ := by
    rw [hpt]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [F.aDag_adjoint i (F.a i Φ) Φ]
    rw [FockData.normSq]
  -- the diagonal part is bounded by the window
  have hdiag : F.bp (F.a i Φ) (F.a i Φ) ≤ E.bigM * F.normSq Φ := by
    have h := Work.BoseB7.spectLe_nOp F E hspec i hi
    simp only [FockData.nOp, FockData.normSq, LinearMap.comp_apply] at h
    rwa [F.aDag_adjoint i (F.a i Φ) Φ] at h
  -- the commutator term
  have hle : F.ccrK i i ≤ 1 := le_trans (le_abs_self _) hccr
  have hnn : 0 ≤ F.normSq Φ := by
    rw [FockData.normSq]; exact F.bp_nonneg Φ
  have hccrb : F.ccrK i i * F.normSq Φ ≤ 1 * F.normSq Φ :=
    mul_le_mul_of_nonneg_right hle hnn
  calc F.bp (F.a i (F.aDag i Φ)) Φ
      = F.bp (F.a i Φ) (F.a i Φ) + F.ccrK i i * F.normSq Φ := hsplit
    _ ≤ E.bigM * F.normSq Φ + 1 * F.normSq Φ := add_le_add hdiag hccrb
    _ = (E.bigM + 1) * F.normSq Φ := by ring

end Work.BoseB7
