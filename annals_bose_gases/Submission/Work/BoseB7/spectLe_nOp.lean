import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseB7.Estimates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.spectLe_nOp` — one mode of the spectral window

FS's spectral window `eq:LocalizedAftercNumber` / `eq:LocalizedNPlus` is the
*quadratic-form* bound `⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²` on the total excited-particle number
`n₊ = Σ_{k ≠ 0} a_k†a_k`.  Every estimate of §10, however, is applied mode by
mode (e.g. the factors `𝓜` in the error functions `err1`, `err4`, `controlErr`
come from bounding a single `a_k†a_k`).  This file records that the window is
inherited by each individual mode:

  `⟨Φ, a_i†a_i Φ⟩ ≤ 𝓜‖Φ‖²` for `i ≠ 0`.

The proof is the observation that `⟨Φ, a_j†a_j Φ⟩ = ‖a_jΦ‖² ≥ 0` for *every*
mode `j` (the adjointness field `aDag_adjoint`, plus positivity of `bp`), so that
the `i`-th term of the sum `n₊` is at most the whole sum.  No hypothesis on `𝓜`
is needed: `hspec` is used exactly as it stands.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

/-- Each diagonal number operator is non-negative as a quadratic form:
`⟨Φ, a_i†a_i Φ⟩ = ‖a_iΦ‖² ≥ 0`.  (Directly from the adjointness field; no
spectral hypothesis is used.) -/
theorem bp_nOp_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (i : Mode) (Φ : F.H) :
    0 ≤ F.bp (F.nOp i Φ) Φ := by
  show 0 ≤ F.bp (F.aDag i (F.a i Φ)) Φ
  rw [F.aDag_adjoint i (F.a i Φ) Φ]
  exact F.bp_nonneg _

/-- The quadratic form of `n₊ = Σ_{k ≠ 0} n_k` is the sum of the quadratic forms
of its summands (linearity of `bp` in its *first* argument: `bp` is a linear map
`H →ₗ[ℝ] (H →ₗ[ℝ] ℝ)`). -/
theorem bp_nPlus_eq_sum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (Φ : F.H) :
    F.bp (F.nPlus Φ) Φ
      = ∑ j ∈ excited Mode, F.bp (F.nOp j Φ) Φ := by
  simp [FockData.nPlus, map_sum]

/-- The `i`-th term of `n₊` is dominated by `n₊` itself (`i ≠ 0`), because every
term of the sum is non-negative. -/
theorem bp_nOp_le_bp_nPlus {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (i : Mode) (hi : i ≠ 0) (Φ : F.H) :
    F.bp (F.nOp i Φ) Φ ≤ F.bp (F.nPlus Φ) Φ := by
  rw [Work.BoseB7.bp_nPlus_eq_sum F Φ]
  exact Finset.single_le_sum (fun j _ => Work.BoseB7.bp_nOp_nonneg F j Φ)
    (show i ∈ excited Mode from Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)

/-- **The spectral window is inherited by each mode**: if `Φ` has at most `𝓜`
excited particles in the quadratic-form sense, then `⟨Φ, a_i†a_i Φ⟩ ≤ 𝓜‖Φ‖²`
for every mode `i ≠ 0`. -/
theorem spectLe_nOp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) {Φ : F.H}
    (hspec : F.SpectLe E.bigM Φ) (i : Mode) (hi : i ≠ 0) :
    F.bp (F.nOp i Φ) Φ ≤ E.bigM * F.normSq Φ :=
  calc F.bp (F.nOp i Φ) Φ ≤ F.bp (F.nPlus Φ) Φ :=
        Work.BoseB7.bp_nOp_le_bp_nPlus F i hi Φ
    _ ≤ E.bigM * F.normSq Φ := hspec

end Work.BoseB7
