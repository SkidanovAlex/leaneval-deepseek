import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotC5N3.RulingX2.SlicePhi
import Submission.Work.MotC5N3.ZiasSliceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ZiasSliceFhatEq`: the slice generators are the explicitly tabulated `fhat_k`

`Work.MotC5N3.slice a b g k` is the `X 2 = 1` slice of the `k`-th cubic `zcubAS a b g k` of the AS
residual curve, while `Work.MotC5N3.RulingX2.Slice.fhatF a b g k` is the explicit tabulation of the
same polynomial (the files `Submission/Work/MotC5N3/RulingX2/SliceD/S0.lean`–`S5.lean`), obtained by
expanding the substitution `X 2 ↦ 1`.  The proof expands both sides — the left one by unfolding
`slicePhi = MvPolynomial.aeval` — and normalises them with `ring_nf`, reducing the integer
coefficients modulo the characteristic `5` via `reduce_mod_char!`.

Three formal points are worth recording:

* `reduce_mod_char` determines the characteristic of a type from a *local* declaration, so the
  `haveI` below is essential (a global `CharP` instance would not be found);
* Mathlib has no `CharP` instance for `MvPolynomial`, whence `mvPolynomial_charP`;
* the case split on `k : Fin 5` must substitute `k` by the *elaborated* numeral `0, …, 4` of the
  statement (here this is done by `rw` with a disjunction `k = 0 ∨ ⋯ ∨ k = 4`); the literals
  produced by `fin_cases` are not recognised by `Matrix.cons_val_zero`, and an unreduced `![…] k`
  blocks the simp expansion of `aeval`.

-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Work.MotC5N3.RulingX2

open MvPolynomial

/-- `MvPolynomial σ R` inherits the characteristic of `R` (Mathlib has no such instance).  It is
stated as a theorem rather than an instance so that it can be introduced as a *local* hypothesis,
which is the form `reduce_mod_char` looks for. -/
theorem mvPolynomial_charP {R : Type*} [CommSemiring R] (σ : Type*) (p : ℕ) [CharP R p] :
    CharP (MvPolynomial σ R) p where
  cast_eq_zero_iff n := by
    have h : ((n : MvPolynomial σ R) = 0) ↔ ((n : R) = 0) := by
      rw [← map_natCast (MvPolynomial.C : R →+* MvPolynomial σ R) n]
      exact MvPolynomial.C_eq_zero
    exact h.trans (CharP.cast_eq_zero_iff R p n)

theorem ZiasSliceFhatEq (K : Type) [Field K] [CharP K 5] (a b g : K) (k : Fin 5) :
    Work.MotC5N3.slice a b g k = Work.MotC5N3.RulingX2.Slice.fhatF a b g k := by
  haveI : CharP (MvPolynomial (Fin 2) K) 5 := mvPolynomial_charP (Fin 2) 5
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by fin_cases k <;> decide
  rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;>
    simp only [Work.MotC5N3.slice, Work.MotC5N3.slicePhi, Work.MotAS.zcubAS,
      Work.MotAS.kleinRAS, Work.MotAS.kleinRAS0, Work.MotAS.kleinRAS1, Work.MotAS.kleinRAS2,
      Work.MotAS.kleinRAS3, Work.MotAS.kleinRAS4,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
      map_one, map_zero, map_add, map_mul, map_pow, map_sub, map_ofNat,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
      Work.MotC5N3.RulingX2.Slice.fhatF,
      Work.MotC5N3.RulingX2.Slice.fhat0, Work.MotC5N3.RulingX2.Slice.fhat0_p0,
      Work.MotC5N3.RulingX2.Slice.fhat0_p1,
      Work.MotC5N3.RulingX2.Slice.fhat1, Work.MotC5N3.RulingX2.Slice.fhat1_p0,
      Work.MotC5N3.RulingX2.Slice.fhat1_p1,
      Work.MotC5N3.RulingX2.Slice.fhat2, Work.MotC5N3.RulingX2.Slice.fhat2_p0,
      Work.MotC5N3.RulingX2.Slice.fhat2_p1,
      Work.MotC5N3.RulingX2.Slice.fhat3,
      Work.MotC5N3.RulingX2.Slice.fhat4] <;>
    ring_nf <;> reduce_mod_char! <;> ring_nf <;> reduce_mod_char! <;>
    ring_nf <;> reduce_mod_char!

end Work.MotC5N3.RulingX2
