/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# First- and second-order bounds for derivatives of finite products

For a finite family `u : ι → E → ℂ` of `ℂ`-valued functions on a real normed space `E`, the
product `z ↦ ∏ i, u i z` has derivative
`∑ i, (∏ j ≠ i, u j z) • fderiv ℝ (u i) z`.  If all factors are bounded by `1`, the norm of
that derivative is at most the sum of the individual derivative bounds; and if moreover each
factor and each factor's derivative is Lipschitz on the pair `(x,y)`, so is the derivative of
the product, with the explicit constant `(∑ L) * (∑ M) + ∑ Md`.
-/
import Mathlib

noncomputable section

open scoped BigOperators

namespace Work.NN.Core.Lev

/-- A finite product of complex numbers of norm `≤ 1` has norm `≤ 1`. -/
lemma norm_prod_le_one_of_le_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℂ)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) : ‖∏ i ∈ s, b i‖ ≤ 1 := by
  rw [norm_prod]
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      rw [Finset.prod_insert his]
      have h1a : ‖b i‖ ≤ 1 := hb i (Finset.mem_insert_self i s)
      have h1b : ∏ j ∈ s, ‖b j‖ ≤ 1 := ih (fun j hj => hb j (Finset.mem_insert_of_mem hj))
      calc ‖b i‖ * ∏ j ∈ s, ‖b j‖ ≤ 1 * 1 :=
            mul_le_mul h1a h1b (Finset.prod_nonneg fun j _ => norm_nonneg _) zero_le_one
        _ = 1 := by norm_num

/-- **Difference of finite products.**  If `a` and `b` take values of norm `≤ 1` on `s`, and
`‖a i - b i‖ ≤ L i * t` there, then `‖∏ a - ∏ b‖ ≤ (∑ L i) * t` on `s` (for `t ≥ 0` and
`L ≥ 0`). -/
lemma norm_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℂ)
    (L : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (hL0 : ∀ i ∈ s, 0 ≤ L i) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) (hd : ∀ i ∈ s, ‖a i - b i‖ ≤ L i * t) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ (∑ i ∈ s, L i) * t := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      rw [Finset.prod_insert his, Finset.prod_insert his, Finset.sum_insert his]
      have hAi : ‖a i‖ ≤ 1 := ha i (Finset.mem_insert_self i s)
      have hdi : ‖a i - b i‖ ≤ L i * t := hd i (Finset.mem_insert_self i s)
      have hLi : 0 ≤ L i := hL0 i (Finset.mem_insert_self i s)
      have ha' : ∀ j ∈ s, ‖a j‖ ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hb' : ∀ j ∈ s, ‖b j‖ ≤ 1 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
      have hL0' : ∀ j ∈ s, 0 ≤ L j := fun j hj => hL0 j (Finset.mem_insert_of_mem hj)
      have hd' : ∀ j ∈ s, ‖a j - b j‖ ≤ L j * t := fun j hj => hd j (Finset.mem_insert_of_mem hj)
      have ih' := ih hL0' ha' hb' hd'
      have hprodb : ‖∏ j ∈ s, b j‖ ≤ 1 := norm_prod_le_one_of_le_one s b hb'
      have heq : a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j)
          = a i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j))
            + (a i - b i) * (∏ j ∈ s, b j) := by ring
      have hkey : ‖a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j)‖
          ≤ ‖a i‖ * ‖(∏ j ∈ s, a j) - (∏ j ∈ s, b j)‖
            + ‖a i - b i‖ * ‖∏ j ∈ s, b j‖ := by
        rw [heq]
        calc ‖a i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j)) + (a i - b i) * (∏ j ∈ s, b j)‖
            ≤ ‖a i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j))‖
              + ‖(a i - b i) * (∏ j ∈ s, b j)‖ := norm_add_le _ _
          _ = ‖a i‖ * ‖(∏ j ∈ s, a j) - (∏ j ∈ s, b j)‖
              + ‖a i - b i‖ * ‖∏ j ∈ s, b j‖ := by rw [norm_mul, norm_mul]
      calc ‖a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j)‖
          ≤ ‖a i‖ * ‖(∏ j ∈ s, a j) - (∏ j ∈ s, b j)‖
            + ‖a i - b i‖ * ‖∏ j ∈ s, b j‖ := hkey
        _ ≤ 1 * ((∑ j ∈ s, L j) * t) + (L i * t) * 1 := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul hAi ih' (norm_nonneg _) zero_le_one
            · exact mul_le_mul hdi hprodb (norm_nonneg _) (mul_nonneg hLi ht)
        _ = (L i + ∑ j ∈ s, L j) * t := by ring

/-- **First-order bound on the derivative of a finite product** of `ℂ`-valued functions. -/
theorem fderiv_finset_prod_norm_le {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] (u : ι → E → ℂ) (x : E) {M : ι → ℝ}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x)
    (hM : ∀ i, ‖fderiv ℝ (u i) x‖ ≤ M i) (h1 : ∀ i, ‖u i x‖ ≤ 1) :
    ‖fderiv ℝ (fun z => ∏ i, u i z) x‖ ≤ ∑ i, M i := by
  have hfd : fderiv ℝ (fun z => ∏ i, u i z) x
      = ∑ i, (∏ j ∈ Finset.univ.erase i, u j x) • fderiv ℝ (u i) x :=
    fderiv_finset_prod (u := Finset.univ) (g := u) (x := x) (fun i _ => hu i)
  rw [hfd]
  calc ‖∑ i, (∏ j ∈ Finset.univ.erase i, u j x) • fderiv ℝ (u i) x‖
      ≤ ∑ i, ‖(∏ j ∈ Finset.univ.erase i, u j x) • fderiv ℝ (u i) x‖ := norm_sum_le _ _
    _ ≤ ∑ i, M i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        have hP : ‖∏ j ∈ Finset.univ.erase i, u j x‖ ≤ 1 :=
          norm_prod_le_one_of_le_one _ _ fun j _ => h1 j
        calc ‖∏ j ∈ Finset.univ.erase i, u j x‖ * ‖fderiv ℝ (u i) x‖ ≤ 1 * M i :=
              mul_le_mul hP (hM i) (norm_nonneg _) zero_le_one
          _ = M i := one_mul _

/-- **Second-order (Lipschitz) bound on the derivative of a finite product** of `ℂ`-valued
functions. -/
theorem fderiv_finset_prod_sub_le {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] (u : ι → E → ℂ) (x y : E) {L M Md : ι → ℝ}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) (hv : ∀ i, DifferentiableAt ℝ (u i) y)
    (hL0 : ∀ i, 0 ≤ L i) (hM0 : ∀ i, 0 ≤ M i) (hMd0 : ∀ i, 0 ≤ Md i)
    (hM : ∀ i, ‖fderiv ℝ (u i) x‖ ≤ M i)
    (hL : ∀ i, ‖u i x - u i y‖ ≤ L i * ‖x - y‖)
    (hMd : ∀ i, ‖fderiv ℝ (u i) x - fderiv ℝ (u i) y‖ ≤ Md i * ‖x - y‖)
    (h1x : ∀ i, ‖u i x‖ ≤ 1) (h1y : ∀ i, ‖u i y‖ ≤ 1) :
    ‖fderiv ℝ (fun z => ∏ i, u i z) x - fderiv ℝ (fun z => ∏ i, u i z) y‖
      ≤ ((∑ i, L i) * (∑ i, M i) + ∑ i, Md i) * ‖x - y‖ := by
  have hfdx : fderiv ℝ (fun z => ∏ i, u i z) x
      = ∑ i, (∏ j ∈ Finset.univ.erase i, u j x) • fderiv ℝ (u i) x :=
    fderiv_finset_prod (u := Finset.univ) (g := u) (x := x) (fun i _ => hu i)
  have hfdy : fderiv ℝ (fun z => ∏ i, u i z) y
      = ∑ i, (∏ j ∈ Finset.univ.erase i, u j y) • fderiv ℝ (u i) y :=
    fderiv_finset_prod (u := Finset.univ) (g := u) (x := y) (fun i _ => hv i)
  rw [hfdx, hfdy]
  have hsub : ∀ i, ‖(∏ j ∈ Finset.univ.erase i, u j x) • fderiv ℝ (u i) x
        - (∏ j ∈ Finset.univ.erase i, u j y) • fderiv ℝ (u i) y‖
      ≤ ((∑ j, L j) * M i + Md i) * ‖x - y‖ := by
    intro i
    have hdiff : (∏ j ∈ Finset.univ.erase i, u j x) • fderiv ℝ (u i) x
        - (∏ j ∈ Finset.univ.erase i, u j y) • fderiv ℝ (u i) y
        = ((∏ j ∈ Finset.univ.erase i, u j x) - (∏ j ∈ Finset.univ.erase i, u j y))
            • fderiv ℝ (u i) x
          + (∏ j ∈ Finset.univ.erase i, u j y) • (fderiv ℝ (u i) x - fderiv ℝ (u i) y) := by
      module
    have hP : ‖(∏ j ∈ Finset.univ.erase i, u j x) - (∏ j ∈ Finset.univ.erase i, u j y)‖
        ≤ (∑ j, L j) * ‖x - y‖ := by
      have h := norm_prod_sub_prod_le (Finset.univ.erase i) (fun j => u j x) (fun j => u j y) L
        (norm_nonneg _) (fun j _ => hL0 j) (fun j _ => h1x j) (fun j _ => h1y j)
        (fun j _ => hL j)
      refine le_trans h (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun j _ _ => hL0 j)
    have hPy : ‖∏ j ∈ Finset.univ.erase i, u j y‖ ≤ 1 :=
      norm_prod_le_one_of_le_one _ _ fun j _ => h1y j
    have hti : 0 ≤ ‖x - y‖ := norm_nonneg _
    rw [hdiff]
    calc ‖((∏ j ∈ Finset.univ.erase i, u j x) - (∏ j ∈ Finset.univ.erase i, u j y))
            • fderiv ℝ (u i) x
          + (∏ j ∈ Finset.univ.erase i, u j y) • (fderiv ℝ (u i) x - fderiv ℝ (u i) y)‖
        ≤ ‖((∏ j ∈ Finset.univ.erase i, u j x) - (∏ j ∈ Finset.univ.erase i, u j y))
            • fderiv ℝ (u i) x‖
          + ‖(∏ j ∈ Finset.univ.erase i, u j y) • (fderiv ℝ (u i) x - fderiv ℝ (u i) y)‖ :=
          norm_add_le _ _
      _ = ‖(∏ j ∈ Finset.univ.erase i, u j x) - (∏ j ∈ Finset.univ.erase i, u j y)‖
            * ‖fderiv ℝ (u i) x‖
          + ‖∏ j ∈ Finset.univ.erase i, u j y‖
            * ‖fderiv ℝ (u i) x - fderiv ℝ (u i) y‖ := by rw [norm_smul, norm_smul]
      _ ≤ ((∑ j, L j) * ‖x - y‖) * M i + 1 * (Md i * ‖x - y‖) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul hP (hM i) (norm_nonneg _)
              (mul_nonneg (Finset.sum_nonneg fun j _ => hL0 j) hti)
          · exact mul_le_mul hPy (hMd i) (norm_nonneg _) zero_le_one
      _ = ((∑ j, L j) * M i + Md i) * ‖x - y‖ := by ring
  calc ‖∑ i, (∏ j ∈ Finset.univ.erase i, u j x) • fderiv ℝ (u i) x
        - ∑ i, (∏ j ∈ Finset.univ.erase i, u j y) • fderiv ℝ (u i) y‖
      = ‖∑ i, ((∏ j ∈ Finset.univ.erase i, u j x) • fderiv ℝ (u i) x
          - (∏ j ∈ Finset.univ.erase i, u j y) • fderiv ℝ (u i) y)‖ := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖(∏ j ∈ Finset.univ.erase i, u j x) • fderiv ℝ (u i) x
          - (∏ j ∈ Finset.univ.erase i, u j y) • fderiv ℝ (u i) y‖ := norm_sum_le _ _
    _ ≤ ∑ i, ((∑ j, L j) * M i + Md i) * ‖x - y‖ := Finset.sum_le_sum fun i _ => hsub i
    _ = ((∑ i, L i) * (∑ i, M i) + ∑ i, Md i) * ‖x - y‖ := by
        have h1 : ∑ i, ((∑ j, L j) * M i + Md i) * ‖x - y‖
            = (∑ i, ((∑ j, L j) * M i + Md i)) * ‖x - y‖ := (Finset.sum_mul _ _ _).symm
        simp only [h1, Finset.sum_add_distrib, Finset.mul_sum]

end Work.NN.Core.Lev
