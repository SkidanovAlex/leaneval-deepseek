import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.Split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Split_cre_excited` — the excited creation operators under the split

The mode lattice `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` splits as
`𝔉(ℂθ) ⊗ 𝔉(θ^⊥)` via `Work.BoseB4.split`, the `ℝ`-linear isometry sending the
monomial `x^α` to

    √((α 0)! · (α|_{j≠0})!) · e_{α 0} ⊗ |α|_{j≠0}⟩

(condensate level `α 0`, coefficient `fockW (α 0) (restOf α)`, excited part
`restOf α`).  For an *excited* mode `j` (`j.1 ≠ 0`), the lattice creation
`cre m j.1` (multiplication by `x_{j.1}`) raises only the excited occupation, so
under the split it must correspond to the levelwise lift of the abstract excited
creation `creC (Excited m) j`.

The verification is one computation on basis vectors.  On `Finsupp.single α 1`
both sides are `Finsupp.single (α 0) (…)` (the condensate level `α 0` is
unchanged because `j.1 ≠ 0`), the excited multi-index becomes
`restOf α + single j 1`, and the two coefficients agree because the Fock weight
gains exactly the factor `√((restOf α) j + 1)` when the `j`-occupation is raised:

    `fockW n (β + single j 1) = √((β j) + 1) · fockW n β`

(from `(k+1)! = (k+1)·k!` for `mfacG`, i.e. `mfacG (β + single j 1)
= ((β j : ℝ) + 1) * mfacG β`).  This is precisely the `√(γ_j + 1)` factor of
`creF`.  Linearity in the input (`b • single α 1 = single α b`) and
`Finsupp.lhom_ext` then give the operator identity.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-! ## Auxiliary computations on multi-indices -/

/-- `split` on a basis vector of the mode lattice: the `α`-monomial accumulates
the condensate weight `√((α 0)!)` and the excited weight `√((restOf α)!)`. -/
private lemma split_single_apply {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) (r : ℝ) :
    split (Finsupp.single α r) = r • Finsupp.single (α 0)
      (toCFock (Excited m)
        (Finsupp.single (restOf α) (((fockW (α 0) (restOf α) : ℝ) : ℂ)))) := by
  rw [split, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The multi-index factorial `mfacG` is nonnegative. -/
private lemma mfacG_nonneg {ι : Type*} (β : ι →₀ ℕ) : 0 ≤ mfacG β := by
  rw [mfacG, Finsupp.prod]
  exact Finset.prod_nonneg fun a _ => by positivity

/-- On a finite index type, `mfacG β = ∏_l (β_l)!`: the factors outside the
support are `0! = 1`. -/
private lemma mfacG_eq_prod_univ {ι : Type*} [Fintype ι] (β : ι →₀ ℕ) :
    mfacG β = ∏ l : ι, ((β l).factorial : ℝ) := by
  rw [mfacG, Finsupp.prod]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro x _ hx
  rw [Finsupp.notMem_support_iff.mp hx]
  simp

/-- Raising the `j`-occupation by one multiplies the multi-index factorial by
`(β j : ℝ) + 1`: `mfacG (β + single j 1) = ((β j : ℝ) + 1) * mfacG β`. -/
private lemma mfacG_add_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι →₀ ℕ) (j : ι) :
    mfacG (β + Finsupp.single j (1:ℕ)) = ((β j : ℝ) + 1) * mfacG β := by
  rw [mfacG_eq_prod_univ, mfacG_eq_prod_univ]
  have h1 := Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)
    (fun l => (((β + Finsupp.single j (1:ℕ) : ι →₀ ℕ) l).factorial : ℝ))
  have h2 := Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)
    (fun l => ((β l).factorial : ℝ))
  rw [h1, h2]
  have hjv : (β + Finsupp.single j (1:ℕ) : ι →₀ ℕ) j = β j + 1 := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [hjv, Nat.factorial_succ]
  have hprod : ∏ x ∈ Finset.univ \ {j},
        (((β + Finsupp.single j (1:ℕ) : ι →₀ ℕ) x).factorial : ℝ)
      = ∏ x ∈ Finset.univ \ {j}, ((β x).factorial : ℝ) := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hxj : x ≠ j := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_singleton.mpr h)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hxj, add_zero]
  rw [hprod]
  push_cast
  ring

/-- The Fock weight gains the factor `√((β j) + 1)` when the `j`-occupation is
raised by one. -/
private lemma fockW_add_single {m : ℕ} [NeZero m] (n : ℕ)
    (β : Excited m →₀ ℕ) (j : Excited m) :
    fockW n (β + Finsupp.single j (1:ℕ)) = fockW n β * Real.sqrt ((β j : ℝ) + 1) := by
  rw [fockW, fockW, mfacG_add_single]
  rw [show (n.factorial : ℝ) * (((β j : ℝ) + 1) * mfacG β)
      = (n.factorial : ℝ) * mfacG β * ((β j : ℝ) + 1) by ring]
  rw [Real.sqrt_mul (mul_nonneg (by positivity) (mfacG_nonneg β))]

/-! ## The excited part of the multi-index -/

/-- Adding a quantum to the excited mode `j` (`j.1 ≠ 0`) adds `single j 1` to the
excited part of the multi-index. -/
private lemma restOf_add_e {m : ℕ} [NeZero m] (j : Excited m) (α : Fin m →₀ ℕ) :
    restOf (α + e m j.1) = restOf α + Finsupp.single j (1:ℕ) := by
  rw [restOf, restOf, Finsupp.subtypeDomain_add]
  congr 1
  ext k
  rw [Finsupp.subtypeDomain_apply, e]
  by_cases h : k = j
  · subst h; simp
  · rw [Finsupp.single_eq_of_ne h]
    exact Finsupp.single_eq_of_ne (fun hh => h (Subtype.ext hh))

/-- Adding a quantum to the excited mode `j` (`j.1 ≠ 0`) leaves the condensate
occupation unchanged. -/
private lemma apply_add_e {m : ℕ} [NeZero m] (j : Excited m) (α : Fin m →₀ ℕ) :
    (α + e m j.1) 0 = α 0 := by
  rw [Finsupp.add_apply, e, Finsupp.single_eq_of_ne (Ne.symm j.2), add_zero]

/-! ## The creation operators on the two sides -/

/-- `creC` is the image of `creF` under the linear equivalence `toCFock`. -/
private lemma creC_toCFock {X : Type*} [DecidableEq X] (j : X)
    (x : (X →₀ ℕ) →₀ ℂ) :
    creC X j (toCFock X x) = toCFock X (creF X j x) := by
  rw [creC, LinearMap.comp_apply, LinearMap.comp_apply]
  simp

/-- The excited creation `creC j` on a basis vector: it raises the `j`-occupation
and multiplies the coefficient by `√(γ_j + 1)`. -/
private lemma creC_toCFock_single {X : Type*} [DecidableEq X] (j : X)
    (γ : X →₀ ℕ) (c : ℂ) :
    creC X j (toCFock X (Finsupp.single γ c))
      = toCFock X (((c * ((Real.sqrt ((γ j : ℝ) + 1) : ℝ) : ℂ)))
          • Finsupp.single (γ + Finsupp.single j (1:ℕ)) (1 : ℂ)) := by
  rw [creC_toCFock, creF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul]

/-- The operator identity on the basis vectors `Finsupp.single α 1`. -/
private lemma split_cre_excited_basis {m : ℕ} [NeZero m] (j : Excited m)
    (α : Fin m →₀ ℕ) :
    split (cre m j.1 (Finsupp.single α (1:ℝ)))
      = lift (creC (Excited m) j) (split (Finsupp.single α (1:ℝ))) := by
  rw [cre, Finsupp.lsum_single, Finsupp.lsingle_apply]
  rw [split_single_apply, split_single_apply]
  simp only [one_smul]
  rw [lift_single]
  rw [creC_toCFock_single]
  rw [apply_add_e, restOf_add_e]
  congr 1
  have hk1 : Finsupp.single (restOf α + Finsupp.single j (1:ℕ))
        (((fockW (α 0) (restOf α + Finsupp.single j (1:ℕ)) : ℝ) : ℂ))
      = (((fockW (α 0) (restOf α + Finsupp.single j (1:ℕ)) : ℝ) : ℂ))
          • Finsupp.single (restOf α + Finsupp.single j (1:ℕ)) (1 : ℂ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hk1]
  congr 1
  rw [← Complex.ofReal_mul, fockW_add_single]

/-! ## The identity -/

theorem Split_cre_excited {m : ℕ} [NeZero m] (j : Work.BoseB4.Excited m) :
    (Work.BoseB4.split).comp (Work.BoseB4.cre m j.1)
      = (((Work.BoseB4.lift (Work.BoseB4.creC (Work.BoseB4.Excited m) j) : Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)) →ₗ[ℂ]
            Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)))).restrictScalars ℝ).comp
          Work.BoseB4.split := by
  refine Finsupp.lhom_ext fun α b => ?_
  have hb : Finsupp.single α b = b • Finsupp.single α (1 : ℝ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hb]
  simp only [LinearMap.comp_apply, map_smul]
  rw [split_cre_excited_basis]
  rfl

end Work.BoseB4
