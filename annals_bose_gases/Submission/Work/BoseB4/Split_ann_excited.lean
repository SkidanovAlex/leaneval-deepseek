import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.FockW_sub_single_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Split_ann_excited` — the excited-mode annihilation under `split`

The mode lattice `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` splits, through
`Work.BoseB4.split`, as the tensor product of the condensate mode with the Fock
space of the excited modes: `split` sends the monomial `x^α` to the Fock weight
`√((α 0)! · (α|_{j≠0})!)` times the pair `(α 0, α|_{j≠0})`.

The present lemma is the *annihilation* half of the excited-mode dictionary: for
every excited mode `j ≠ 0`, the lattice derivative `ann m j.1 = ∂/∂x_{j}` (which
lowers the `j`-occupation and produces the factor `α j.1`) corresponds to the
abstract annihilation `annC j`,

    split ∘ ann m j.1 = lift (annC (Excited m) j) ∘ split,

the mode-lattice instance of FS §8's operator correspondence.  Its companions are
`Split_ann_zero`, `Split_cre_zero` and `Split_cre_excited`.

## The proof

By `Finsupp.lhom_ext` it suffices to check both sides on the basis vectors
`Finsupp.single α c` of `RealFock m = (Fin m →₀ ℕ) →₀ ℝ`.  There

* `ann m j.1 (single α c) = ((α j.1) · c) • single (α - e_j) 1`, with
  `(α - e_j) 0 = α 0` (because `j ≠ 0`) and `restOf (α - e_j) = restOf α - e_j`;
* `split (single α c) = c • single (α 0) (splitVec α)` where `splitVec α` is the
  weighted basis vector `toCFock (single (restOf α) (fockW (α 0) (restOf α)))`, and
  `annC j (splitVec α) = fockW (α 0) (restOf α) · √((restOf α) j) • toCFock (single (restOf α - e_j) 1)`
  by the `Finsupp`-level formula for `annF` on a single basis vector;

so both sides are `Finsupp.single (α 0)` applied to a scalar multiple of the same
vector `splitVec (α - e_j)`, and the two scalars agree by the Fock weight identity

    (β j) · fockW n (β - e_j) = √(β j) · fockW n β      (`FockW_sub_single_mul`),

i.e. `β! = (β j) · (β - e_j)!`: raising the `j`-occupation gains exactly the
factor `√(β j)`, which is the abstract annihilation weight.
-/

noncomputable section

open scoped lp Finsupp

namespace Work.BoseB4

set_option autoImplicit false

/-- The lattice annihilation on a basis vector: the derivative gains the factor `α l`. -/
lemma ann_single_basis {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (c : ℝ) :
    ann m l (Finsupp.single α c) = ((α l : ℝ) * c) • Finsupp.single (α - e m l) 1 := by
  rw [ann, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul, mul_comm]

variable {m : ℕ} [NeZero m]

/-- The image of a basis multi-index under `split`, with the Fock weight absorbed:
`split (Finsupp.single α c) = c • Finsupp.single (α 0) (splitVec α)`. -/
noncomputable def splitVec (α : Fin m →₀ ℕ) : cfock (Excited m) :=
  toCFock (Excited m) (Finsupp.single (restOf α) (((fockW (α 0) (restOf α) : ℝ) : ℂ)))

/-- `split` on a basis vector: the level is the condensate occupation `α 0`. -/
lemma split_single_basis (α : Fin m →₀ ℕ) (c : ℝ) :
    split (Finsupp.single α c) = c • Finsupp.single (α 0) (splitVec α) := by
  simp only [split, splitVec, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The abstract annihilation `annF` on a basis vector: it lowers the occupation of
the mode `j` and produces the weight `√(γ_j)`. -/
lemma annF_single {X : Type*} [DecidableEq X] (j : X) (β : X →₀ ℕ) (c : ℂ) :
    annF X j (Finsupp.single β c) =
      (c * ((Real.sqrt (β j) : ℝ) : ℂ)) • Finsupp.single (β - Finsupp.single j 1) (1 : ℂ) := by
  rw [annF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul]

lemma annC_toCFock {X : Type*} [DecidableEq X] (j : X) (f : (X →₀ ℕ) →₀ ℂ) :
    annC X j (toCFock X f) = toCFock X (annF X j f) := by
  simp [annC]

/-- Removing an excited quantum leaves the condensate occupation unchanged. -/
lemma sub_e_apply_zero_excited (j : Excited m) (α : Fin m →₀ ℕ) :
    ((α - e m j.1 : Fin m →₀ ℕ) : Fin m → ℕ) 0 = α 0 := by
  simp [Finsupp.tsub_apply, e, Ne.symm j.2]

/-- Removing the excited quantum `e_j` from the excited part of a multi-index. -/
lemma restOf_sub_e_excited (j : Excited m) (α : Fin m →₀ ℕ) :
    restOf (α - e m j.1) = restOf α - Finsupp.single j 1 := by
  ext γ
  simp only [restOf, Finsupp.subtypeDomain_apply, Finsupp.tsub_apply, e]
  congr 1
  by_cases h : γ = j
  · subst h; simp
  · rw [Finsupp.single_eq_of_ne h]
    rw [Finsupp.single_eq_of_ne (show (γ : Fin m) ≠ j.1 from fun hc => h (Subtype.ext hc))]

/-- `splitVec` on `α - e_j`: only the Fock weight changes. -/
lemma splitVec_sub_e (j : Excited m) (α : Fin m →₀ ℕ) :
    splitVec (α - e m j.1)
      = (((fockW (α 0) (restOf α - Finsupp.single j 1) : ℝ) : ℂ) •
          toCFock (Excited m) (Finsupp.single (restOf α - Finsupp.single j 1) 1)) := by
  rw [splitVec, sub_e_apply_zero_excited, restOf_sub_e_excited, ← Finsupp.smul_single_one, map_smul]

/-- `annC j` on the weighted basis vector `splitVec α`: it lowers the mode-`j`
occupation with the abstract weight `√((restOf α) j)`. -/
lemma annC_splitVec (j : Excited m) (α : Fin m →₀ ℕ) :
    annC (Excited m) j (splitVec α)
      = (((fockW (α 0) (restOf α) : ℝ) : ℂ) * ((Real.sqrt ((restOf α) j) : ℝ) : ℂ)) •
          toCFock (Excited m) (Finsupp.single (restOf α - Finsupp.single j 1) 1) := by
  rw [splitVec, annC_toCFock, annF_single, map_smul]

/-- The Fock weight identity in the form used below: `FockW_sub_single_mul` with
`β j` rewritten as `α j.1` (`restOf α` is the restriction of `α` to `j ≠ 0`). -/
lemma fockW_weight (j : Excited m) (α : Fin m →₀ ℕ) :
    (α j.1 : ℝ) * fockW (α 0) (restOf α - Finsupp.single j 1)
      = Real.sqrt ((restOf α) j) * fockW (α 0) (restOf α) := by
  rw [show (restOf α) j = α j.1 from Finsupp.subtypeDomain_apply]
  exact FockW_sub_single_mul (α 0) (restOf α) j

/-- The complex form of `fockW_weight`. -/
lemma fockW_weight_complex (j : Excited m) (α : Fin m →₀ ℕ) :
    ((α j.1 : ℝ) : ℂ) * ((fockW (α 0) (restOf α - Finsupp.single j 1) : ℝ) : ℂ)
      = ((Real.sqrt ((restOf α) j) : ℝ) : ℂ) * ((fockW (α 0) (restOf α) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, fockW_weight]

/-- **The mode-lattice annihilation of an excited mode corresponds to the abstract
annihilation `annC`** (FS §8's operator correspondence on the mode lattice). -/
theorem Split_ann_excited {m : ℕ} [NeZero m] (j : Work.BoseB4.Excited m) :
    (Work.BoseB4.split).comp (Work.BoseB4.ann m j.1)
      = (((Work.BoseB4.lift (Work.BoseB4.annC (Work.BoseB4.Excited m) j) : Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)) →ₗ[ℂ]
            Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)))).restrictScalars ℝ).comp
          Work.BoseB4.split := by
  let annCR : FockCore (cfock (Excited m)) →ₗ[ℝ] FockCore (cfock (Excited m)) :=
    ((lift (annC (Excited m) j) : FockCore (cfock (Excited m)) →ₗ[ℂ]
      FockCore (cfock (Excited m)))).restrictScalars ℝ
  have key : (split.comp (ann m j.1)) = (annCR.comp split) := by
    refine Finsupp.lhom_ext fun α c => ?_
    have hL : (split.comp (ann m j.1)) (Finsupp.single α c)
        = (((α j.1 : ℝ) * c) • Finsupp.single (α 0) (splitVec (α - e m j.1))) := by
      rw [LinearMap.comp_apply, ann_single_basis, map_smul, split_single_basis, one_smul,
        sub_e_apply_zero_excited]
    have hR : (annCR.comp split) (Finsupp.single α c)
        = (c • Finsupp.single (α 0) (annC (Excited m) j (splitVec α))) := by
      rw [LinearMap.comp_apply, split_single_basis, map_smul, LinearMap.restrictScalars_apply,
        lift_single]
    rw [hL, hR, splitVec_sub_e, annC_splitVec, Finsupp.smul_single, Finsupp.smul_single]
    apply congrArg (Finsupp.single (α 0))
    rw [← smul_assoc, Complex.real_smul, ← smul_assoc, Complex.real_smul]
    congr 1
    rw [Complex.ofReal_mul, mul_comm (((α j.1 : ℝ) : ℂ)) ((c : ℝ) : ℂ), mul_assoc,
      fockW_weight_complex j α,
      mul_comm (((Real.sqrt ((restOf α) j) : ℝ) : ℂ))
        (((fockW (α 0) (restOf α) : ℝ) : ℂ))]
  exact key

end Work.BoseB4
