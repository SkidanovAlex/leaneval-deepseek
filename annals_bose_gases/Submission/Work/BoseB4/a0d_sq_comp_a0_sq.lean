import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `(a₀†)²(a₀)²` in terms of `(a₀)²(a₀†)²`

The fourth relation of the ladder calculus for the condensate mode of the
bosonic Fock space: the CCR `[a₀, a₀†] = 1` (proved as `ccr` in
`Submission/Work/BoseB4/Defs.lean`) implies

    (a₀†)² a₀² = a₀² (a₀†)² - 4 a₀ a₀† + 2,

the operator form of `n(n-1) = (n+1)(n+2) - 4(n+1) + 2` on the `n`-th
condensate level.  The proof is pure ring algebra: from `A Ad = Ad A + 1`
in any ring one first gets `A Ad² = Ad² A + 2 Ad`, and the identity follows
by moving one factor `A` past `Ad²`.
-/

namespace Work.BoseB4

/-- **The abstract algebra core.**  In any ring, `A * Ad = Ad * A + 1` implies
`(Ad * Ad) * (A * A) = (A * A) * (Ad * Ad) - 4 * (A * Ad) + 2 * 1`. -/
private lemma comp_sq_sq_ring {R : Type*} [Ring R] (A Ad : R)
    (h : A * Ad = Ad * A + 1) :
    (Ad * Ad) * (A * A) = (A * A) * (Ad * Ad) - 4 * (A * Ad) + 2 * 1 := by
  -- Step one: move `A` past `Ad * Ad`.
  have h2 : A * (Ad * Ad) = (Ad * Ad) * A + 2 * Ad := by
    calc A * (Ad * Ad) = (A * Ad) * Ad := by rw [mul_assoc]
    _ = (Ad * A + 1) * Ad := by rw [h]
    _ = (Ad * A) * Ad + Ad := by rw [add_mul, one_mul]
    _ = Ad * (A * Ad) + Ad := by rw [mul_assoc]
    _ = Ad * (Ad * A + 1) + Ad := by rw [h]
    _ = Ad * (Ad * A) + Ad + Ad := by rw [mul_add, mul_one]
    _ = (Ad * Ad) * A + 2 * Ad := by rw [← mul_assoc, two_mul, add_assoc]
  have h2' : (Ad * Ad) * A = A * (Ad * Ad) - 2 * Ad := by
    rw [eq_sub_iff_add_eq]; exact h2.symm
  have hAdA : Ad * A = A * Ad - 1 := by
    rw [eq_sub_iff_add_eq]; exact h.symm
  -- Step two: move one factor `A` past `Ad * Ad`, and use `Ad * A = A * Ad - 1`.
  calc (Ad * Ad) * (A * A) = ((Ad * Ad) * A) * A := by noncomm_ring
  _ = (A * (Ad * Ad) - 2 * Ad) * A := by rw [h2']
  _ = A * ((Ad * Ad) * A) - 2 * (Ad * A) := by noncomm_ring
  _ = A * (A * (Ad * Ad) - 2 * Ad) - 2 * (A * Ad - 1) := by rw [h2', hAdA]
  _ = (A * A) * (Ad * Ad) - 4 * (A * Ad) + 2 * 1 := by noncomm_ring

/-- The same identity for endomorphisms of a complex module, in the
`.comp`/`•` shape used by the Fock-space layer. -/
private lemma comp_sq_sq_endo {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A Ad : M →ₗ[ℂ] M) (h : A.comp Ad = Ad.comp A + 1) :
    (Ad.comp Ad).comp (A.comp A)
      = (A.comp A).comp (Ad.comp Ad) - (4 : ℂ) • (A.comp Ad)
        + (2 : ℂ) • (1 : M →ₗ[ℂ] M) := by
  have key : (Ad * Ad) * (A * A) = (A * A) * (Ad * Ad) - 4 * (A * Ad) + 2 * 1 :=
    comp_sq_sq_ring A Ad h
  simp only [← Module.End.mul_eq_comp, Algebra.smul_def, map_ofNat]
  exact key

/-- **Condensate ladder, fourth relation:** `(a₀†)²(a₀)² = (a₀)²(a₀†)² - 4 a₀a₀† + 2`,
a consequence of the CCR `[a₀, a₀†] = 1` (`ccr`). -/
theorem a0d_sq_comp_a0_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    ((Work.BoseB4.a0d : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E).comp Work.BoseB4.a0d).comp
        (Work.BoseB4.a0.comp Work.BoseB4.a0)
      = (Work.BoseB4.a0.comp Work.BoseB4.a0).comp (Work.BoseB4.a0d.comp Work.BoseB4.a0d)
        - (4 : ℂ) • (Work.BoseB4.a0.comp Work.BoseB4.a0d : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E)
        + (2 : ℂ) • (1 : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E) :=
  comp_sq_sq_endo a0 a0d ccr

end Work.BoseB4
