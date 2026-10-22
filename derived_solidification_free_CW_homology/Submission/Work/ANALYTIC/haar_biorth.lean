import Mathlib
import Submission.Work.ANALYTIC.HaarBasisDefs
import Submission.Work.ANALYTIC.HaarPar
import Submission.Work.ANALYTIC.haar_offdiag

/-!
# Biorthogonality of the Haar/Schauder basis of `C(T,ℤ)` (AN3, REFS/03 §4)

For an infinite light profinite set `T`, the two families defined in
`Submission/Work/ANALYTIC/HaarDefs.lean` are dual bases of `LC T = LocallyConstant ↥T ℤ`:

* `phiJ T j : LC T →+ ℤ` — the functionals `λ ↦ λ(a_j) - λ(p_j)` (and the evaluation at the base
  point `s₀` for the extra index `∞`), and
* `fJ T j : LC T` — the indicators of the level-`n(j)` cylinders of the enumerated new points
  `a_j` (and the constant function `1` for the extra index `∞`),

with `phiJ T i (fJ T j) = if i = j then 1 else 0`.  The second half of the duality (every `λ` is
the finite sum `Σ_j (phiJ j λ) • fJ j`) is `haar_expand`; together they give the basis iso
`haar_basisIso`.

The proof is the following case analysis.

* `i = j = ∞`: `1(s₀) = 1`.
* `i = j = (n : ℕ)`: `phi n (fCyl n) = fCyl n (a_n) - fCyl n (p_n) = 1 - 0`, using
  `Haar.fCyl_self` and `Haar.fCyl_par_self` (the parent `p_n` has level `< n(n)`, so it lies
  outside the cylinder of `a_n`).
* `i = ∞`, `j = (m : ℕ)`: `fCyl m (s₀) = 0` (`Haar.fCyl_s₀`).
* `i = (n : ℕ)`, `j = ∞`: `phi n 1 = 1 - 1 = 0` (`Haar.phi_one`).
* `i = (n : ℕ)`, `j = (m : ℕ)`, `n ≠ m`: `phi n (fCyl m) = fCyl m (a_n) - fCyl m (p_n)` and both
  terms are equal (or both vanish), according to whether `n(m) + 1 ≤ n(n)` or `n(n) ≤ n(m)`; this
  is `Work.ANALYTIC.haar_offdiag` (proved in `Submission/Work/ANALYTIC/haar_offdiag.lean` from the
  level facts collected in `Submission/Work/ANALYTIC/HaarPar.lean`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Work.ANALYTIC

namespace Haar

variable (T : LightProfinite.{0}) [Infinite T]

/-! ## The diagonal pairing of `phi` and `fCyl` -/

/-- **Diagonal biorthogonality**: `phi n (fCyl n) = 1`. -/
theorem phi_fCyl_self (n : ℕ) : phi T n (fCyl T n) = 1 := by
  rw [phi, fCyl_self, fCyl_par_self, sub_zero]

/-! ## The pairing of `phiJ` and `fJ` -/

/-- **Diagonal biorthogonality** for the extended index set `ℕ ∪ {∞}`. -/
theorem phiJ_fJ_self (i : JIdx) : phiJ T i (fJ T i) = 1 := by
  induction i using OnePoint.rec with
  | infty =>
    rw [phiJ_inf, fJ_inf]
    exact LocallyConstant.one_apply _
  | coe n =>
    rw [phiJ_coe, fJ_coe]
    exact phi_fCyl_self T n

/-- **Off-diagonal biorthogonality** for the extended index set `ℕ ∪ {∞}`.  The case of two finite
indices is `Work.ANALYTIC.haar_offdiag` (proved from the level facts of
`Submission/Work/ANALYTIC/HaarPar.lean`); the remaining cases are the base point and the constant
function. -/
theorem phiJ_fJ_ne {i j : JIdx} (h : i ≠ j) : phiJ T i (fJ T j) = 0 := by
  induction i using OnePoint.rec with
  | infty =>
    induction j using OnePoint.rec with
    | infty => exact absurd rfl h
    | coe m =>
      rw [phiJ_inf, fJ_coe]
      exact fCyl_s₀ T m
  | coe n =>
    induction j using OnePoint.rec with
    | infty =>
      rw [phiJ_coe, fJ_inf]
      exact phi_one T n
    | coe m =>
      rw [phiJ_coe, fJ_coe]
      exact haar_offdiag T n m (fun hh => h (OnePoint.coe_eq_coe.mpr hh))

end Haar

/-- **Biorthogonality of the Haar/Schauder basis**: the functionals `phiJ T i` and the basis
elements `fJ T j` of `Submission/Work/ANALYTIC/HaarDefs.lean` are dual to each other,
`phiJ T i (fJ T j) = if i = j then 1 else 0` (REFS/03 §4). -/
theorem haar_biorth (T : LightProfinite.{0}) [Infinite T] (i j : Work.ANALYTIC.Haar.JIdx) :
    (i = j → Work.ANALYTIC.Haar.phiJ T i (Work.ANALYTIC.Haar.fJ T j) = 1) ∧
      (i ≠ j → Work.ANALYTIC.Haar.phiJ T i (Work.ANALYTIC.Haar.fJ T j) = 0) := by
  constructor
  · intro h
    rw [h]
    exact Haar.phiJ_fJ_self T j
  · intro h
    exact Haar.phiJ_fJ_ne T h

end Work.ANALYTIC
