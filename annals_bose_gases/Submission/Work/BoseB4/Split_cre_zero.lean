import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.Split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Split_cre_zero` — the condensate creation operator under the split

The mode lattice `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` splits as
`𝔉(ℂθ) ⊗ 𝔉(θ^⊥)` via `Work.BoseB4.split`, the `ℝ`-linear isometry sending the
monomial `x^α` to

    √((α 0)! · (α|_{j≠0})!) · e_{α 0} ⊗ |α|_{j≠0}⟩

(coefficient `fockW (α 0) (restOf α)` on the condensate level `α 0`).  Under this
identification the lattice creation of the condensate mode, `cre m 0` (multiplication
by `x_0`), must correspond to the abstract condensate creation `a0d`.

The verification is one computation on basis vectors: on `Finsupp.single α 1` both
sides are `Finsupp.single (α 0 + 1) (…)`, and the two coefficients agree because the
Fock weight gains exactly the factor `√(α 0 + 1)` when the condensate occupation is
raised (`fockW_succ`, from `(n+1)! = (n+1)·n!`), which is precisely the `sq (n+1)`
factor of `a0d`.  Linearity in the input (`b • single α 1 = single α b`) and
`Finsupp.lhom_ext` then give the operator identity.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

/-- `split` on a basis vector of the mode lattice: the `α`-monomial accumulates the
condensate weight `√((α 0)!)` and the excited weight `√((restOf α)!)`. -/
private lemma split_single_apply {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) (r : ℝ) :
    split (Finsupp.single α r) = r • Finsupp.single (α 0)
      (toCFock (Excited m)
        (Finsupp.single (restOf α) (((fockW (α 0) (restOf α) : ℝ) : ℂ)))) := by
  rw [split, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The Fock weight gains the factor `√(n+1)` when the condensate occupation is raised:
`√((n+1)! · β!) = √(n+1) · √(n! · β!)`, from `(n+1)! = (n+1)·n!`. -/
private lemma fockW_succ {m : ℕ} [NeZero m] (n : ℕ) (β : Excited m →₀ ℕ) :
    fockW (n + 1) β = Real.sqrt (((n + 1 : ℕ) : ℝ)) * fockW n β := by
  unfold fockW
  rw [Nat.factorial_succ]
  push_cast
  rw [mul_assoc, Real.sqrt_mul (by positivity)]

/-- Adding a condensate quantum does not change the excited part of a multi-index. -/
private lemma restOf_add_e_zero {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) :
    restOf (α + e m 0) = restOf α := by
  have hz : Finsupp.subtypeDomain (fun j : Fin m => j ≠ 0) (e m 0) = 0 := by
    ext j
    rw [Finsupp.subtypeDomain_apply, Finsupp.zero_apply]
    simp [e, Finsupp.single_eq_of_ne j.2]
  rw [restOf, restOf, Finsupp.subtypeDomain_add, hz, add_zero]

/-- The condensate occupation of `α + e_0` is `α 0 + 1`. -/
private lemma apply_add_e_zero {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) :
    (α + e m 0) 0 = α 0 + 1 := by
  rw [Finsupp.add_apply, e]
  simp

/-- The operator identity on the basis vectors `Finsupp.single α 1`. -/
private lemma split_cre_zero_basis {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) :
    split (cre m 0 (Finsupp.single α 1)) = a0d (split (Finsupp.single α 1)) := by
  rw [cre, Finsupp.lsum_single, Finsupp.lsingle_apply]
  rw [split_single_apply, split_single_apply]
  simp only [one_smul]
  rw [a0d_single]
  rw [apply_add_e_zero, restOf_add_e_zero]
  apply congrArg (Finsupp.single (α 0 + 1))
  rw [← (toCFock (Excited m)).map_smul]
  rw [Finsupp.smul_single]
  apply congrArg (toCFock (Excited m))
  apply congrArg (Finsupp.single (restOf α))
  rw [smul_eq_mul, sq, ← Complex.ofReal_mul, fockW_succ]

theorem Split_cre_zero {m : ℕ} [NeZero m] :
    (Work.BoseB4.split).comp (Work.BoseB4.cre m 0)
      = (((Work.BoseB4.a0d : Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)) →ₗ[ℂ]
            Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)))).restrictScalars ℝ).comp
          Work.BoseB4.split := by
  refine Finsupp.lhom_ext fun α b => ?_
  have hb : Finsupp.single α b = b • Finsupp.single α (1 : ℝ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hb]
  simp only [LinearMap.comp_apply, map_smul]
  rw [split_cre_zero_basis]
  rfl

end Work.BoseB4
