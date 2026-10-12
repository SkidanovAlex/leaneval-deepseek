import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseB4.CFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.annC_creC_ccr` — the canonical commutation relation on the complex Fock core

`Work.BoseB4.CFock` presents the complex Fock core `(X →₀ ℕ) →₀ ℂ` as a submodule
`cfock X` of `ℓ²(X →₀ ℕ)` and defines the two ladder operators of a mode `j`:

* `annF X j` — the *normalised* annihilation, `(annF j) (single γ c) = c·√(γ_j) • single (γ - e_j)`,
* `creF X j` — the *normalised* creation, `(creF j) (single γ c) = c·√(γ_j + 1) • single (γ + e_j)`,

together with their images `annC X j`, `creC X j` on `cfock X` (the conjugates of
`annF`, `creF` under the linear equivalence `toCFock X`).

Here we prove the **canonical commutation relation** for these normalised operators,

  `[a_i, a_j^†] = δ_{ij} · 1`   on `cfock X`,

i.e. `(annC X i).comp (creC X j) = (creC X j).comp (annC X i) + (if i = j then 1 else 0)`,
an operator identity on `cfock X`.  With the normalised (occupation-basis) weights this
is the standard CCR `[a_i, a_j^†] = δ_{ij}`; the `√·` weights cancel in the mixed scalar
products, and the diagonal contribution `+1` comes from `(γ_i + 1) - γ_i = 1`, exactly as
for the un-normalised lattice operators (`Work.BoseB4.Ann_cre_ccr`) but with the `γ_i = 0`
boundary case of the lowering step absorbed by the vanishing weight `√0 = 0`.

## The proof

Everything is checked on the basis `Finsupp.single γ c` of `(X →₀ ℕ) →₀ ℂ` (the
`Finsupp.lsum`-extensionality `Finsupp.lhom_ext`), where the two composites are the
explicitly computed shifts

* `annF i (creF j (single γ c)) = (c·√(γ_j+1)·√((γ+e_j)_i)) • single ((γ+e_j) - e_i)`,
* `creF j (annF i (single γ c)) = (c·√(γ_i)·√(((γ-e_i)_j)+1)) • single ((γ-e_i) + e_j)`;

the index shifts are compared by `add_single_sub_single_ne` (`i ≠ j`) and
`add_single_sub_single_self`/`sub_single_add_single_self` (`i = j`), and the scalar
comparison is the elementary identity `√(n+1)² = √n·√((n-1)+1) + 1` (`sqrt_diag`, proved
by `Real.mul_self_sqrt`), which is *uniform* in `n` — the `n = 0` case being killed by
`√0 = 0` on the right and `n + 1 = 1` on the left.  Finally the identity is transported
from `(X →₀ ℕ) →₀ ℂ` to `cfock X` along the linear equivalence `toCFock X`
(`annC X j (toCFock X f) = toCFock X (annF X j f)` and its creation twin).
-/

noncomputable section

open scoped lp

namespace Work.BoseB4

set_option autoImplicit false

/-! ## 1. The two ladder operators on a basis vector -/

/-- `annF X j` on a basis vector: it lowers the `j`-occupation and gains the weight
`√(γ_j)`. -/
private lemma annF_single {X : Type*} [DecidableEq X] (j : X) (γ : X →₀ ℕ) (c : ℂ) :
    annF X j (Finsupp.single γ c)
      = (c * (Real.sqrt ((γ j : ℝ)) : ℂ)) • Finsupp.single (γ - Finsupp.single j 1) (1 : ℂ) := by
  rw [annF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul]

/-- `creF X j` on a basis vector: it raises the `j`-occupation with weight `√(γ_j + 1)`. -/
private lemma creF_single {X : Type*} [DecidableEq X] (j : X) (γ : X →₀ ℕ) (c : ℂ) :
    creF X j (Finsupp.single γ c)
      = (c * (Real.sqrt ((γ j : ℝ) + 1) : ℂ))
        • Finsupp.single (γ + Finsupp.single j 1) (1 : ℂ) := by
  rw [creF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul]

/-- The annihilation-after-creation composite on a basis vector, in closed form. -/
private lemma annF_creF_single {X : Type*} [DecidableEq X] (i j : X) (γ : X →₀ ℕ) (c : ℂ) :
    annF X i (creF X j (Finsupp.single γ c))
      = ((c * (Real.sqrt ((γ j : ℝ) + 1) : ℂ))
          * (Real.sqrt (((γ + Finsupp.single j 1 : X →₀ ℕ) i : ℝ)) : ℂ))
        • Finsupp.single ((γ + Finsupp.single j 1) - Finsupp.single i 1) (1 : ℂ) := by
  rw [creF_single, map_smul, annF_single, smul_smul, one_mul]

/-- The creation-after-annihilation composite on a basis vector, in closed form. -/
private lemma creF_annF_single {X : Type*} [DecidableEq X] (i j : X) (γ : X →₀ ℕ) (c : ℂ) :
    creF X j (annF X i (Finsupp.single γ c))
      = ((c * (Real.sqrt ((γ i : ℝ)) : ℂ))
          * (Real.sqrt (((γ - Finsupp.single i 1 : X →₀ ℕ) j : ℝ) + 1) : ℂ))
        • Finsupp.single ((γ - Finsupp.single i 1) + Finsupp.single j 1) (1 : ℂ) := by
  rw [annF_single, map_smul, creF_single, smul_smul, one_mul]

/-! ## 2. The scalar identity `√(n+1)² = √n·√((n-1)+1) + 1`

This is the diagonal heart of the CCR: raising the `n`-th occupation and lowering it
again gains exactly one quantum, the loss `√n·√((n-1)+1)` being `√n² = n`.  Note that
the identity is uniform in `n : ℕ`: for `n = 0` the natural-number subtraction `n - 1`
is `0` and both `√0 = 0` and the left-hand side `n + 1 = 1` match. -/

private lemma sqrt_diag (c : ℂ) (n : ℕ) :
    (c * (Real.sqrt ((n : ℝ) + 1) : ℂ)) * (Real.sqrt ((n : ℝ) + 1) : ℂ)
      = (c * (Real.sqrt ((n : ℝ)) : ℂ)) * (Real.sqrt (((n - 1 : ℕ) : ℝ) + 1) : ℂ) + c := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; norm_num
  · have h1 : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
      have hh : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
      exact_mod_cast hh
    have h2 : (Real.sqrt ((n : ℝ)) : ℂ) * (Real.sqrt ((n : ℝ)) : ℂ) = (n : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
      norm_num
    have h3 : (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((n : ℝ) + 1) : ℂ)
        = ((n : ℂ) + 1) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      ring
    rw [h1, mul_assoc, mul_assoc, h3, h2]
    ring

/-! ## 3. Index shifts of multi-indices

All statements are pointwise evaluations of the shifts `γ ↦ γ ± single j 1`. -/

/-- Raising the `i`-th occupation and evaluating there. -/
private lemma add_single_apply_self {X : Type*} [DecidableEq X] (i : X) (γ : X →₀ ℕ) :
    (γ + Finsupp.single i 1 : X →₀ ℕ) i = γ i + 1 := by
  rw [Finsupp.add_apply, Finsupp.single_eq_same]

/-- Raising another occupation `e_j` (`j ≠ i`) leaves the `i`-th occupation unchanged. -/
private lemma add_single_apply_ne {X : Type*} [DecidableEq X] {i j : X} (h : i ≠ j)
    (γ : X →₀ ℕ) :
    (γ + Finsupp.single j 1 : X →₀ ℕ) i = γ i := by
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, add_zero]

/-- Lowering the `i`-th occupation and evaluating there. -/
private lemma sub_single_apply_self {X : Type*} [DecidableEq X] (i : X) (γ : X →₀ ℕ) :
    (γ - Finsupp.single i 1 : X →₀ ℕ) i = γ i - 1 := by
  rw [Finsupp.tsub_apply, Finsupp.single_eq_same]

/-- Lowering another occupation `e_i` (`i ≠ j`) leaves the `j`-th occupation unchanged. -/
private lemma sub_single_apply_ne {X : Type*} [DecidableEq X] {i j : X} (h : i ≠ j)
    (γ : X →₀ ℕ) :
    (γ - Finsupp.single i 1 : X →₀ ℕ) j = γ j := by
  rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (Ne.symm h), tsub_zero]

/-- Raising then lowering the same occupation is the identity. -/
private lemma add_single_sub_single_self {X : Type*} [DecidableEq X] (i : X) (γ : X →₀ ℕ) :
    (γ + Finsupp.single i 1) - Finsupp.single i 1 = γ := by
  ext k
  simp only [Finsupp.tsub_apply, Finsupp.add_apply]
  by_cases hk : k = i
  · subst hk; rw [Finsupp.single_eq_same]; omega
  · rw [Finsupp.single_eq_of_ne hk]; simp

/-- Lowering then raising the same occupation returns `γ`, provided the occupation
`γ i` was non-zero; for `γ i = 0` the lowering step is a no-op and the identity fails,
which is exactly why the annihilation weight `√(γ i)` is what makes the diagonal CCR
work. -/
private lemma sub_single_add_single_self {X : Type*} [DecidableEq X] {i : X} (γ : X →₀ ℕ)
    (h : γ i ≠ 0) :
    (γ - Finsupp.single i 1) + Finsupp.single i 1 = γ := by
  ext k
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  by_cases hk : k = i
  · subst hk
    rw [Finsupp.single_eq_same]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)
  · rw [Finsupp.single_eq_of_ne hk]; simp

/-- For `i ≠ j` the two shifts commute, so the order of raising `e_j` and lowering
`e_i` is irrelevant. -/
private lemma add_single_sub_single_ne {X : Type*} [DecidableEq X] {i j : X} (h : i ≠ j)
    (γ : X →₀ ℕ) :
    (γ + Finsupp.single j 1) - Finsupp.single i 1
      = (γ - Finsupp.single i 1) + Finsupp.single j 1 := by
  ext k
  simp only [Finsupp.tsub_apply, Finsupp.add_apply]
  by_cases hki : k = i
  · subst hki
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne h]
    simp
  · by_cases hkj : k = j
    · subst hkj
      rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm h)]
      simp
    · rw [Finsupp.single_eq_of_ne hki, Finsupp.single_eq_of_ne hkj]
      simp

/-! ## 4. The CCR on the Finsupp model -/

/-- The canonical commutation relation on basis vectors. -/
private lemma annF_creF_single_ccr {X : Type*} [DecidableEq X] (i j : X) (γ : X →₀ ℕ)
    (c : ℂ) :
    annF X i (creF X j (Finsupp.single γ c))
      = creF X j (annF X i (Finsupp.single γ c))
        + (if i = j then Finsupp.single γ c else 0) := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, annF_creF_single, creF_annF_single, add_single_sub_single_self i γ,
      add_single_apply_self i γ, sub_single_apply_self i γ]
    rw [← Finsupp.smul_single_one γ c]
    by_cases h0 : γ i = 0
    · rw [h0]; simp
    · rw [sub_single_add_single_self γ h0, ← add_smul]
      have hcast : ((γ i + 1 : ℕ) : ℝ) = ((γ i : ℝ) + 1) := by push_cast; ring
      rw [hcast]
      congr 1
      exact sqrt_diag c (γ i)
  · rw [if_neg hij, annF_creF_single, creF_annF_single, add_single_sub_single_ne hij γ,
      add_single_apply_ne hij γ, sub_single_apply_ne hij γ, add_zero]
    congr 1
    ring

/-- The canonical commutation relation on the Finsupp model `(X →₀ ℕ) →₀ ℂ`. -/
private lemma annF_creF_ccr {X : Type*} [DecidableEq X] (i j : X) :
    (annF X i).comp (creF X j)
      = (creF X j).comp (annF X i) + (if i = j then 1 else 0) := by
  apply Finsupp.lhom_ext
  intro γ c
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [annF_creF_single_ccr]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij, Module.End.one_apply]
  · rw [if_neg hij, if_neg hij, LinearMap.zero_apply]

/-! ## 5. Transport to the complex Fock core -/

/-- `annC` is the image of `annF` under the linear equivalence `toCFock`. -/
private lemma annC_toCFock {X : Type*} [DecidableEq X] (j : X) (f : (X →₀ ℕ) →₀ ℂ) :
    annC X j (toCFock X f) = toCFock X (annF X j f) := by
  simp [annC]

/-- `creC` is the image of `creF` under the linear equivalence `toCFock`. -/
private lemma creC_toCFock {X : Type*} [DecidableEq X] (j : X) (f : (X →₀ ℕ) →₀ ℂ) :
    creC X j (toCFock X f) = toCFock X (creF X j f) := by
  simp [creC]

theorem annC_creC_ccr {X : Type*} [DecidableEq X] (i j : X) :
    (Work.BoseB4.annC X i).comp (Work.BoseB4.creC X j)
      = (Work.BoseB4.creC X j).comp (Work.BoseB4.annC X i)
        + (if i = j then 1 else 0) := by
  have hF := annF_creF_ccr (X := X) i j
  apply LinearMap.ext
  intro x
  rcases (toCFock X).surjective x with ⟨y, rfl⟩
  have hy := LinearMap.congr_fun hF y
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at hy ⊢
  simp only [creC_toCFock, annC_toCFock]
  by_cases hij : i = j
  · rw [if_pos hij] at hy ⊢
    rw [Module.End.one_apply] at hy
    rw [Module.End.one_apply]
    rw [← map_add]
    exact congrArg (toCFock X) hy
  · rw [if_neg hij] at hy ⊢
    rw [LinearMap.zero_apply, add_zero] at hy
    rw [LinearMap.zero_apply, add_zero]
    exact congrArg (toCFock X) hy

end Work.BoseB4
