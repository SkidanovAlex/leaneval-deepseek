import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.Split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Split_ann_zero` — the condensate annihilation operator under `split`

The mode lattice `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` splits as
`𝔉(ℂθ) ⊗ 𝔉(θ^⊥)` through `Work.BoseB4.split`, the `ℝ`-linear map sending the
monomial `x^α` to

    √((α 0)! · (α|_{j≠0})!) · e_{α 0} ⊗ |α|_{j≠0}⟩,

i.e. with Fock weight `Work.BoseB4.fockW (α 0) (restOf α)` on the condensate
level `α 0`.  The present lemma is the *annihilation* half of the dictionary: the
lattice operator `ann m 0 = ∂/∂x_0` (mode `0`) corresponds to the abstract
condensate annihilation `a0`,

    split ∘ ann m 0 = a0 ∘ split,

the mode-lattice instance of FS §8's operator correspondence (its companions being
`Split_cre_zero`, `Split_ann_excited`, `Split_cre_excited`).

## The proof

`RealFock m = (Fin m →₀ ℕ) →₀ ℝ` is the free `ℝ`-module on the multi-indices, so by
`Finsupp.lhom_ext` it suffices to check the identity on the basis vectors
`Finsupp.single α c`.  There

* `ann m 0 (single α c) = (α 0 · c) • single (α - e₀) 1`, while
  `(α - e₀) 0 = α 0 - 1` and `restOf (α - e₀) = restOf α`;
* `split (single α c) = c • single (α 0) (splitW α)`, and
  `a0 (single n v) = single (n - 1) (√n • v)`;

so both sides reduce to
`Finsupp.single (α 0 - 1) (r • toCFock (single (restOf α) 1))` with of the two real
coefficients

    α 0 · c · √((α 0 - 1)! · β!)   and   c · √(α 0) · √((α 0)! · β!),   β = restOf α,

which agree because the Fock weight gains exactly the factor `√(α 0)` when the
condensate occupation is raised: `n · fockW (n - 1) β = √n · fockW n β`
(`fockW_nsmul_sub_one`, from `n! = n · (n-1)!`).  That single number-theoretic
identity — together with the `Finsupp` bookkeeping around `α - e₀`, `restOf`,
`toCFock` and the smul/`Finsupp.single` interface — is the whole content.

The helpers are public: `split_single_az`, `splitW_sub_e`, `sq_smul_splitW`,
`fockW_nsmul_sub_one` and `sq_mul_fockW` are the reusable pieces of the condensate
dictionary.
-/

noncomputable section

open scoped lp Finsupp

namespace Work.BoseB4

set_option autoImplicit false

section

variable {m : ℕ} [NeZero m]

/-- The image of a single multi-index under `split`, with the Fock weight split off:
`split (Finsupp.single α c) = c • Finsupp.single (α 0) (splitW α)`. -/
noncomputable def splitW (α : Fin m →₀ ℕ) : cfock (Excited m) :=
  toCFock (Excited m) (Finsupp.single (restOf α) (((fockW (α 0) (restOf α) : ℝ) : ℂ)))

/-- `split` on a basis vector: the condensate occupation `α 0` is the level, and the
Fock weight `fockW (α 0) (restOf α)` is carried by the coefficient. -/
lemma split_single_az (α : Fin m →₀ ℕ) (c : ℝ) :
    split (Finsupp.single α c) = c • Finsupp.single (α 0) (splitW α) := by
  simp only [split, splitW, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The lattice annihilation `ann m 0` on a basis vector: the derivative `∂/∂x₀`
lowers the condensate occupation and produces the factor `α 0`. -/
lemma ann_zero_single (α : Fin m →₀ ℕ) (c : ℝ) :
    ann m 0 (Finsupp.single α c) = ((α 0 : ℝ) * c) • Finsupp.single (α - e m 0) 1 := by
  simp only [ann, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul]
  rw [mul_comm]

/-- Removing one condensate quantum lowers the condensate occupation by one. -/
lemma sub_e_apply_zero (α : Fin m →₀ ℕ) :
    ((α - e m 0 : Fin m →₀ ℕ) : Fin m → ℕ) 0 = α 0 - 1 := by
  simp [Finsupp.tsub_apply, e]

/-- Removing one condensate quantum does not change the excited part. -/
lemma restOf_sub_e (α : Fin m →₀ ℕ) : restOf (α - e m 0) = restOf α := by
  ext j; simp [restOf, Finsupp.subtypeDomain_apply, Finsupp.tsub_apply, e, j.2]

/-- `splitW` on `α - e₀`: the excited part and the reference vector
`toCFock (single (restOf α) 1)` are unchanged, only the scalar
`fockW (α 0 - 1) (restOf α)` is left over. -/
lemma splitW_sub_e (α : Fin m →₀ ℕ) :
    splitW (α - e m 0)
      = (((fockW (α 0 - 1) (restOf α) : ℝ) : ℂ) •
          toCFock (Excited m) (Finsupp.single (restOf α) 1)) := by
  rw [splitW, sub_e_apply_zero, restOf_sub_e, ← Finsupp.smul_single_one, map_smul]

/-- `sq (α 0) • splitW α` as a scalar times the reference vector: the abstract
annihilation factor `√(α 0)` multiplies the Fock weight of the *unchanged* index. -/
lemma sq_smul_splitW (α : Fin m →₀ ℕ) :
    sq (α 0) • splitW α
      = (sq (α 0) * ((fockW (α 0) (restOf α) : ℝ) : ℂ)) •
          toCFock (Excited m) (Finsupp.single (restOf α) 1) := by
  rw [splitW, ← map_smul, Finsupp.smul_single', ← Finsupp.smul_single_one, map_smul]

/-- **The Fock weight gains the factor `√n` when the condensate occupation is raised**:
`n · √((n-1)! · β!) = √n · √(n! · β!)`, from `n! = n · (n-1)!`. -/
lemma fockW_nsmul_sub_one (n : ℕ) (β : Excited m →₀ ℕ) :
    (n : ℝ) * fockW (n - 1) β = Real.sqrt (n : ℝ) * fockW n β := by
  match n with
  | 0 => simp [fockW]
  | k + 1 =>
    have hk : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    have hfac : (((k + 1).factorial : ℕ) : ℝ) * mfacG β
        = ((k : ℝ) + 1) * (((k.factorial : ℕ) : ℝ) * mfacG β) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hstep : Real.sqrt ((((k + 1).factorial : ℕ) : ℝ) * mfacG β)
        = Real.sqrt ((k : ℝ) + 1) * Real.sqrt (((k.factorial : ℕ) : ℝ) * mfacG β) := by
      rw [hfac]; exact Real.sqrt_mul (by positivity) _
    calc ((k + 1 : ℕ) : ℝ) * fockW ((k + 1) - 1) β
        = ((k : ℝ) + 1) * Real.sqrt (((k.factorial : ℕ) : ℝ) * mfacG β) := by
          rw [Nat.add_sub_cancel, fockW, hk]
      _ = Real.sqrt ((k : ℝ) + 1) * (Real.sqrt ((k : ℝ) + 1)
            * Real.sqrt (((k.factorial : ℕ) : ℝ) * mfacG β)) := by
          rw [← mul_assoc, Real.mul_self_sqrt (show (0:ℝ) ≤ (k:ℝ)+1 by positivity)]
      _ = Real.sqrt ((k + 1 : ℕ) : ℝ) * fockW (k + 1) β := by
          rw [fockW, hstep, hk]

/-- The complex form of `fockW_nsmul_sub_one`: `sq n · √(n! · β!) = n · √((n-1)! · β!)`,
which is exactly the coefficient match between `a0` and `ann m 0`. -/
lemma sq_mul_fockW (n : ℕ) (β : Excited m →₀ ℕ) :
    sq n * ((fockW n β : ℝ) : ℂ) = ((n : ℝ) : ℂ) * ((fockW (n - 1) β : ℝ) : ℂ) := by
  rw [sq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, fockW_nsmul_sub_one]

end

/-- The mode-lattice condensate annihilation `ann m 0 = ∂/∂x₀` corresponds, under the
`⟨condensate | excited⟩` split of the mode lattice, to the abstract condensate
annihilation `a0`. -/
theorem Split_ann_zero {m : ℕ} [NeZero m] :
    (Work.BoseB4.split).comp (Work.BoseB4.ann m 0)
      = (((Work.BoseB4.a0 : Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)) →ₗ[ℂ]
            Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)))).restrictScalars ℝ).comp
          Work.BoseB4.split := by
  let a0R : FockCore (cfock (Excited m)) →ₗ[ℝ] FockCore (cfock (Excited m)) :=
    ((a0 : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)))).restrictScalars ℝ
  have key : (split.comp (ann m 0)) = (a0R.comp split) := by
    -- it suffices to check the identity on the basis vectors `Finsupp.single α c`
    refine Finsupp.lhom_ext fun α c => ?_
    have hL : (split.comp (ann m 0)) (Finsupp.single α c)
        = ((α 0 : ℝ) * c) • Finsupp.single (α 0 - 1) (splitW (α - e m 0)) := by
      rw [LinearMap.comp_apply, ann_zero_single, map_smul, split_single_az, one_smul,
        sub_e_apply_zero]
    have hR : (a0R.comp split) (Finsupp.single α c)
        = c • Finsupp.single (α 0 - 1) (sq (α 0) • splitW α) := by
      rw [LinearMap.comp_apply, split_single_az, map_smul]
      show c • a0 (Finsupp.single (α 0) (splitW α))
          = c • Finsupp.single (α 0 - 1) (sq (α 0) • splitW α)
      rw [a0_single]
    -- both sides are `Finsupp.single (α 0 - 1)` applied to a scalar multiple of the
    -- reference vector `toCFock (single (restOf α) 1)`; match the two scalars
    rw [hL, hR, splitW_sub_e, sq_smul_splitW, Finsupp.smul_single, Finsupp.smul_single]
    apply congrArg (Finsupp.single (α 0 - 1))
    rw [← smul_assoc, Complex.real_smul, ← smul_assoc, Complex.real_smul]
    rw [Complex.ofReal_mul, sq_mul_fockW]
    congr 1
    ring
  exact key

end Work.BoseB4
