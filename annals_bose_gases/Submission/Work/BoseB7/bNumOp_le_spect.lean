import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7.bOpDag_adjoint
import Submission.Work.BoseB7.bp_aDag_self_le
import Submission.Work.BoseB7.sum_a_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.bNumOp_le_spect` — the squeezed number operator inside the spectral window

FS `thm:BogHamDiag` diagonalises the quadratic part of the box Hamiltonian into
`Σ_k D_k b_k†b_k` with `b_k = a_k + α_k a_{-k}†` (`FockDefs.bOp`,
`FockDefs.bNumOp`).  Every estimate of FS §10 that has to *pay* for this
diagonalisation (the `P_H`-integrals `(2π)^{-3}ℓ³∫_{P_H}D_kb_k†b_k dk`, and the
localised versions `dNumOpR`) needs a bound on the quadratic form of a *single*
squeezed number operator in terms of the spectral window
`F.SpectLe E.bigM Φ` (`⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²`) and the norm:

  `⟨Φ, b_i†b_i Φ⟩ ≤ 4(1 + α_i²)(𝓜 + 1)‖Φ‖²`  for `i ≠ 0`, `0 ≤ α_i ≤ 1`.

## The proof

`b_i†` is the adjoint of `b_i` for *every* `α` (`bOpDag_adjoint`), so the left
side is a square:

  `⟨Φ, b_i†b_i Φ⟩ = ⟨b_iΦ, b_iΦ⟩ = ‖a_iΦ + α_i a_{-i}†Φ‖²`.

Writing `u = a_iΦ`, `v = a_{-i}†Φ`, `X = ‖u‖²`, `Y = ‖v‖²`, `Z = ⟨u,v⟩`, the
expansion is `X + 2α_iZ + α_i²Y`, and the three ingredients are:

* `X ≤ 𝓜‖Φ‖²`: `⟨a_iΦ,a_iΦ⟩ = ⟨Φ, n_iΦ⟩ ≤ ⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²`, because `n_i` is
  a nonnegative summand of `n₊` for `i ≠ 0` (`spectLe_nOp`);
* `Y ≤ (𝓜+1)‖Φ‖²`: `Y = ⟨Φ, a_{-i}a_{-i}†Φ⟩ = ⟨Φ, n_{-i}Φ⟩ + ccrK(-i,-i)‖Φ‖²`,
  by the box commutator `F.ccr` at the *diagonal* pair `(-i,-i)` (this is why the
  hypothesis on the kernel is `|ccrK j j| ≤ 1`), and then `spectLe_nOp` at `-i`
  together with `|ccrK (-i) (-i)| ≤ 1` — the `+1` of the statement; this is the
  separate lemma `Work.BoseB7.bp_aDag_self_le` (proved alongside this file and
  imported here),
* `2Z ≤ X + Y`: the pair bound for the symmetric positive semidefinite form
  `bp` (`SumABound.bp_abs_le`, no square roots).

Since `Φ ≠ 0` forces `𝓜 ≥ 0` (`0 ≤ ⟨Φ,n₊Φ⟩ ≤ 𝓜‖Φ‖²` and `‖Φ‖² > 0`), we get
`X + 2α_iZ + α_i²Y ≤ (4𝓜+2)‖Φ‖² ≤ 4(1+α_i²)(𝓜+1)‖Φ‖²` for `α_i ∈ [0,1]`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

section Helpers

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/- Auxiliary bounds local to this file (kept in a namespace so that they cannot
collide with the same-named results of the rest of the chapter). -/
namespace BNumOpAux

/-- The quadratic form of the total excited number operator `n₊` is nonnegative:
it is the sum of the nonnegative single-mode forms `⟨Φ, n_jΦ⟩ = ‖a_jΦ‖²`. -/
theorem bp_nPlus_nonneg (F : Work.BoseB7.FockData Mode) (Φ : F.H) :
    0 ≤ F.bp (F.nPlus Φ) Φ := by
  rw [Work.BoseB7.bp_nPlus_eq_sum F Φ]
  exact Finset.sum_nonneg fun j _ => Work.BoseB7.bp_nOp_nonneg F j Φ

/-- `⟨a_iΦ, a_iΦ⟩ = ‖a_iΦ‖² ≤ 𝓜‖Φ‖²` for an excited mode `i ≠ 0`: it is the
`i`-th term of the spectral window. -/
theorem bp_a_self_le (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (i : Mode) {Φ : F.H} (hspec : F.SpectLe E.bigM Φ) (hi : i ≠ 0) :
    F.bp (F.a i Φ) (F.a i Φ) ≤ E.bigM * F.normSq Φ := by
  rw [← F.aDag_adjoint i (F.a i Φ) Φ]
  exact Work.BoseB7.spectLe_nOp F E hspec i hi

end BNumOpAux

end Helpers

theorem bNumOp_le_spect {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (α : Mode → ℝ) (i : Mode)
    {Φ : F.H} (hspec : F.SpectLe E.bigM Φ) (hi : i ≠ 0) (hα0 : 0 ≤ α i) (hα1 : α i ≤ 1)
    (hccr : ∀ j : Mode, |F.ccrK j j| ≤ 1) :
    F.bp (F.bNumOp α i Φ) Φ ≤ 4 * (1 + α i ^ 2) * (E.bigM + 1) * F.normSq Φ := by
  by_cases hN : F.normSq Φ = 0
  · -- the degenerate case `Φ = 0`
    have hΦ : Φ = 0 := F.bp_def Φ hN
    subst hΦ
    simp [FockData.bNumOp, FockData.bOp, FockData.bOpDag, FockData.normSq]
  obtain ⟨hN0, hNne⟩ : 0 ≤ F.normSq Φ ∧ F.normSq Φ ≠ 0 := ⟨F.bp_nonneg Φ, hN⟩
  have hNpos : 0 < F.normSq Φ := lt_of_le_of_ne hN0 (Ne.symm hNne)
  -- `𝓜 ≥ 0`, since `0 ≤ ⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²` and `‖Φ‖² > 0`
  have hM0 : 0 ≤ E.bigM := by
    have h : 0 ≤ E.bigM * F.normSq Φ :=
      le_trans (Work.BoseB7.BNumOpAux.bp_nPlus_nonneg F Φ) hspec
    exact nonneg_of_mul_nonneg_left h hNpos
  -- the three numerical ingredients
  have hX : F.bp (F.a i Φ) (F.a i Φ) ≤ E.bigM * F.normSq Φ :=
    Work.BoseB7.BNumOpAux.bp_a_self_le F E i hspec hi
  have hY : F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ) ≤ (E.bigM + 1) * F.normSq Φ :=
    Work.BoseB7.bp_aDag_self_le F E i hspec hi (hccr (-i))
  have hZ : 2 * F.bp (F.a i Φ) (F.aDag (-i) Φ)
      ≤ F.bp (F.a i Φ) (F.a i Φ) + F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ) := by
    have h := Work.BoseB7.SumABound.bp_abs_le F (F.a i Φ) (F.aDag (-i) Φ)
    have h' := le_abs_self (F.bp (F.a i Φ) (F.aDag (-i) Φ))
    linarith
  have hX0 : 0 ≤ F.bp (F.a i Φ) (F.a i Φ) := F.bp_nonneg _
  have hY0 : 0 ≤ F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ) := F.bp_nonneg _
  -- the pairing of `b_i†b_i`
  have hL : F.bp (F.bNumOp α i Φ) Φ = F.bp (F.bOp α i Φ) (F.bOp α i Φ) := by
    simp only [FockData.bNumOp, LinearMap.comp_apply]
    exact Work.BoseB7.bOpDag_adjoint F α i (F.bOp α i Φ) Φ
  -- expansion in `u = a_iΦ`, `v = a_{-i}†Φ`
  have hexp : F.bp (F.bOp α i Φ) (F.bOp α i Φ)
      = F.bp (F.a i Φ) (F.a i Φ) + 2 * α i * F.bp (F.a i Φ) (F.aDag (-i) Φ)
        + α i ^ 2 * F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ) := by
    simp only [FockData.bOp, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [F.bp_symm (F.aDag (-i) Φ) (F.a i Φ)]
    ring
  rw [hL, hexp]
  -- the final arithmetic
  have hA : 2 * α i * F.bp (F.a i Φ) (F.aDag (-i) Φ)
      ≤ α i * (F.bp (F.a i Φ) (F.a i Φ) + F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ)) := by
    have h := mul_le_mul_of_nonneg_left hZ hα0
    linarith
  have hXY0 : 0 ≤ F.bp (F.a i Φ) (F.a i Φ) + F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ) := by
    linarith
  have hB : α i * (F.bp (F.a i Φ) (F.a i Φ) + F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ))
      ≤ F.bp (F.a i Φ) (F.a i Φ) + F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ) := by
    have h := mul_le_mul_of_nonneg_right hα1 hXY0
    linarith
  have hsq : α i ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
  have hC : α i ^ 2 * F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ)
      ≤ F.bp (F.aDag (-i) Φ) (F.aDag (-i) Φ) := by
    have h := mul_le_mul_of_nonneg_right hsq hY0
    linarith
  nlinarith [hA, hB, hC, hX, hY, hM0, hN0, sq_nonneg (α i)]

end Work.BoseB7
