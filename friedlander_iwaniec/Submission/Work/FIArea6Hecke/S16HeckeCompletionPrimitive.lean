/-
# `Submission.Work.FIArea6Hecke.S16HeckeCompletionPrimitive`

Hecke's functional equation (*FI* §16, (16.17)) for the completed Hecke `L`-function of the
Grössencharacter `ψ_m(z) = χ(z)(z/|z|)^m` of `ℚ(i)`, in the form the §16 contour shift consumes:
for a **primitive** strict character `χ` of modulus `4d` and **every** integer weight `m ∈ ℤ` there
is an entire function `Lam` with

  `Lam s = heckeArch d m s · heckeLSeries χ m s`,   `heckeArch d m s = (4d/π)^s·Γ(s + |m|/2)`,

on the half-plane `re s > 1 + |m|/2` (the half-plane of absolute convergence of the Dirichlet
series).  `Lam` is then the analytic continuation of the completed `L`-function.

## The proof

* **`m ≥ 0`** (`completion_of_nat`).  The library supplies Hecke's theorem
  (`S16Hecke.heckeFE_primitive`, via the theta transformation law for primitive `χ`) only under the
  extra hypothesis `unitSum χ m ≠ 0`, which *does* fail for some primitive `χ`
  (then the "odd" theta series `thetaOdd = unitSum · thetaHol` degenerates).  The remedy is the
  *twist* `twist χ m = χ·ν` of `h1166TwistDefs`, where `ν(z) = (primaryUnit z)^{-j}` is a character
  of `(ℤ[i]/4d)^*` trivial on the primary coset `1 + (1+i)³ℤ[i]`:

  * `twist χ m` agrees with `χ` on every *primary* element (`thetaHol_twist_eq.twist_eq_of_isPrimary`),
    and `heckeLam` only sees primary elements, so `heckeLam (twist χ m) m = heckeLam χ m` — the two
    `L`-functions are literally equal;
  * `unitSum (twist χ m) m = 4 ≠ 0` (`twist_unitSum`);
  * `twist χ m` is again primitive (`twist_isPrimitive`) and strict (`twistAux.twist_isCharMod4dStrict`).

  Applying `heckeFE_primitive` to `twist χ m` therefore completes the `L`-function of `χ` itself.

* **`m < 0`** (`completion_of_neg`).  Write `k = -m > 0`.  The conjugate character
  `χ̄(z) = conj (χ z)` is again primitive strict (`isPrimitive4d_conj`), so the `m ≥ 0` case applies
  to `χ̄` and `k`.  Taking `Lam s = conj (Lam₀ (conj s))` (entire, since `conj ∘ f ∘ conj` is
  holomorphic whenever `f` is) and using `heckeLSeries_conj` (`L(s, ψ_{χ,-k}) = conj L(conj s, ψ_{χ̄,k})`),
  `Complex.Gamma_conj` and `Complex.cpow_conj` gives the claim.

* **All `m ∈ ℤ`** (`S16HeckeCompletionPrimitive`): case split on the sign of `m`.
-/
import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.GaussFourier
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea5.S16Hecke.thetaOdd_eq_unitSum_mul_thetaHol
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea5.S16Hecke.heckeFE_of_theta
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.h1166TwistDefs
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea5.S16Hecke.twist_unitSum
import Submission.Work.FIArea5.S16Hecke.twistAux
import Submission.Work.FIArea5.S16Hecke.GaussBasic
import Submission.Work.FIArea5.S16Hecke.primaryWeightDefs
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_conj

set_option autoImplicit false

namespace Work.FIArea6Hecke

open scoped BigOperators

noncomputable section

/-! ## 1. The `L`-function does not change under the twist -/

/-- The twist is the identity on the primary coset, and `psi`/`heckeLam` only see primary
elements: the Hecke eigenvalues (and hence the Dirichlet series) are unchanged. -/
lemma heckeLam_twist (chi : GaussianInt → ℂ) (m : ℕ) (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam (Work.FIArea5.S16Hecke.twist chi m) (m : ℤ) n =
      Work.FIArea5.S16Hecke.heckeLam chi (m : ℤ) n := by
  classical
  simp only [Work.FIArea5.S16Hecke.heckeLam]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  rw [Finset.mem_filter] at hz
  simp only [Work.FIArea5.S16Hecke.psi]
  rw [Work.FIArea5.S16Hecke.twist_eq_of_isPrimary chi m hz.2.1]

/-- Consequently the Hecke `L`-series is unchanged by the twist. -/
lemma heckeLSeries_twist (chi : GaussianInt → ℂ) (m : ℕ) :
    Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea5.S16Hecke.twist chi m) (m : ℤ) =
      Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) := by
  funext s
  simp only [Work.FIArea5.S16Hecke.heckeLSeries]
  congr 1
  funext n
  exact heckeLam_twist chi m n

/-! ## 2. The case `m ≥ 0` -/

end

end Work.FIArea6Hecke
