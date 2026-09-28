import Mathlib

namespace Work.HP.HP2

open Polynomial Finset

/-- If `t` and all `u j` lie in `[-1,1]`, then `∏_{j∈s} |t - u j| ≤ 2^{#s}`. -/
theorem prod_abs_sub_le_two_pow {ι : Type*} (s : Finset ι) (t : ℝ)
    (ht : t ∈ Set.Icc (-1:ℝ) 1) (u : ι → ℝ) (hu : ∀ j, u j ∈ Set.Icc (-1:ℝ) 1) :
    ∏ j ∈ s, |t - u j| ≤ 2 ^ s.card := by
  calc ∏ j ∈ s, |t - u j| ≤ ∏ _j ∈ s, (2:ℝ) := by
        refine Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => ?_)
        rw [abs_le]
        exact ⟨by linarith [(ht.1), (hu j).2], by linarith [(ht.2), (hu j).1]⟩
    _ = 2 ^ s.card := Finset.prod_const 2

/-- Lower bound on a product of distances: if every `|y - u j|`, `j ∈ s`, is at least `sep > 0`,
then `sep^{#s} ≤ ∏_{j∈s} |y - u j|`. -/
theorem pow_le_prod_abs_sub {ι : Type*} (s : Finset ι) (y : ℝ) (u : ι → ℝ) {sep : ℝ}
    (hsep : 0 < sep) (h : ∀ j ∈ s, sep ≤ |y - u j|) :
    sep ^ s.card ≤ ∏ j ∈ s, |y - u j| := by
  calc sep ^ s.card = ∏ _j ∈ s, sep := (Finset.prod_const sep).symm
    _ ≤ ∏ j ∈ s, |y - u j| :=
        Finset.prod_le_prod₀ (fun j _ => le_of_lt hsep) (fun j hj => h j hj)

/-- **Lagrange bound.** If `p` has degree `≤ D` and `|p| ≤ lam` at `D+1` nodes `x i ∈ [-1,1]` that
are pairwise `sep`-separated (`sep > 0`), then `|p| ≤ (D+1)^2 * lam * 2^D / sep^D` on `[-1,1]`.

Route.  `p = Lagrange.interpolate univ x (fun i => p.eval (x i))` (`Lagrange.eq_interpolate`, using
`p.degree < D+1` and the distinctness of the nodes).  Evaluating the explicit form
`Lagrange.interpolate_eq_sum` at `t ∈ [-1,1]` gives
`p.eval t = ∑ i, (p.eval (x i) / ∏_{j≠i}(x i - x j)) * ∏_{j≠i}(t - x j)`.  Every summand has
absolute value at most `lam * 2^D / sep^D`: the numerator value is `≤ lam`, the product
`∏_{j≠i}|t - x j| ≤ 2^D` because `t` and the nodes all lie in `[-1,1]`, and the denominator is
`≥ sep^D` because all its factors are `≥ sep`.  Summing over the `D+1` indices and using
`D+1 ≤ (D+1)^2` gives the claim. -/
theorem lagrange_eval_bound (D : ℕ) (p : Polynomial ℝ) (hdeg : p.natDegree ≤ D)
    (x : Fin (D+1) → ℝ) (hxI : ∀ i, x i ∈ Set.Icc (-1:ℝ) 1)
    {sep lam : ℝ} (hsep : 0 < sep) (hlam : 0 ≤ lam)
    (hx : ∀ i j, i ≠ j → sep ≤ |x i - x j|) (hval : ∀ i, |p.eval (x i)| ≤ lam) :
    ∀ t ∈ Set.Icc (-1:ℝ) 1, |p.eval t| ≤ ((D:ℝ)+1)^2 * lam * 2^D / sep^D := by
  intro t ht
  -- The nodes are pairwise distinct, hence `x` is injective on `univ`.
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have h := hx i j hne
    rw [hij, sub_self, abs_zero] at h
    linarith
  have hinjOn : Set.InjOn x (Finset.univ : Finset (Fin (D+1))) := hinj.injOn
  have hcard : (Finset.univ : Finset (Fin (D+1))).card = D + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
  -- `p.degree < #univ = D + 1`.
  have hdeg' : p.degree < ((Finset.univ : Finset (Fin (D+1))).card : WithBot ℕ) := by
    rw [hcard]
    exact lt_of_le_of_lt (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hdeg))
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))
  have hpq : p = Lagrange.interpolate (Finset.univ : Finset (Fin (D+1))) x (fun i => p.eval (x i)) :=
    Lagrange.eq_interpolate hinjOn hdeg'
  -- Explicit evaluation of the Lagrange interpolant.
  have key : p.eval t = ∑ i ∈ (Finset.univ : Finset (Fin (D+1))),
      (p.eval (x i) / ∏ j ∈ (Finset.univ.erase i : Finset (Fin (D+1))), (x i - x j)) *
      (∏ j ∈ (Finset.univ.erase i : Finset (Fin (D+1))), (t - x j)) := by
    conv_lhs => rw [hpq]
    rw [Lagrange.interpolate_eq_sum]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  -- Per-summand bound.
  have hterm : ∀ i : Fin (D+1),
      |(p.eval (x i) / ∏ j ∈ (Finset.univ.erase i : Finset (Fin (D+1))), (x i - x j)) *
       (∏ j ∈ (Finset.univ.erase i : Finset (Fin (D+1))), (t - x j))|
      ≤ lam * 2^D / sep^D := by
    intro i
    set er : Finset (Fin (D+1)) := Finset.univ.erase i with her
    have hcard' : er.card = D := by
      rw [her, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    -- The denominator is at least `sep^D`.
    have hA : sep ^ D ≤ |∏ j ∈ er, (x i - x j)| := by
      rw [abs_prod]
      have h := pow_le_prod_abs_sub er (x i) x hsep (fun j hj => ?_)
      · rwa [hcard'] at h
      · rw [her, Finset.mem_erase] at hj
        exact hx i j (Ne.symm hj.1)
    -- The second product is at most `2^D`.
    have hB : |∏ j ∈ er, (t - x j)| ≤ 2 ^ D := by
      rw [abs_prod]
      have h := prod_abs_sub_le_two_pow er t ht x hxI
      rwa [hcard'] at h
    rw [abs_mul, abs_div]
    have hBnn : 0 ≤ |∏ j ∈ er, (t - x j)| := abs_nonneg _
    have hle1 : |p.eval (x i)| / |∏ j ∈ er, (x i - x j)| ≤ lam / sep ^ D :=
      div_le_div₀ hlam (hval i) (pow_pos hsep D) hA
    calc |p.eval (x i)| / |∏ j ∈ er, (x i - x j)| * |∏ j ∈ er, (t - x j)|
        ≤ (lam / sep ^ D) * 2 ^ D :=
          mul_le_mul hle1 hB hBnn (div_nonneg hlam (pow_nonneg hsep.le D))
      _ = lam * 2 ^ D / sep ^ D := by ring
  rw [key]
  calc |∑ i ∈ (Finset.univ : Finset (Fin (D+1))),
          (p.eval (x i) / ∏ j ∈ (Finset.univ.erase i : Finset (Fin (D+1))), (x i - x j)) *
          (∏ j ∈ (Finset.univ.erase i : Finset (Fin (D+1))), (t - x j))|
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin (D+1))),
          |(p.eval (x i) / ∏ j ∈ (Finset.univ.erase i : Finset (Fin (D+1))), (x i - x j)) *
          (∏ j ∈ (Finset.univ.erase i : Finset (Fin (D+1))), (t - x j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin (D+1))), lam * 2^D / sep^D :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((D:ℝ)+1) * (lam * 2^D / sep^D) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((D:ℝ)+1)^2 * lam * 2^D / sep^D := by
        have hnn : ((D:ℝ)+1) ≤ ((D:ℝ)+1)^2 := by
          have h0 : (0:ℝ) ≤ (D:ℝ)+1 := by positivity
          have h1 : (1:ℝ) ≤ (D:ℝ)+1 := by
            have := Nat.cast_nonneg (α:=ℝ) D; linarith
          simpa [pow_two] using le_mul_of_one_le_left h0 h1
        have hc : 0 ≤ lam * 2^D / sep^D := by positivity
        calc ((D:ℝ)+1) * (lam * 2^D / sep^D)
            ≤ ((D:ℝ)+1)^2 * (lam * 2^D / sep^D) := mul_le_mul_of_nonneg_right hnn hc
          _ = ((D:ℝ)+1)^2 * lam * 2^D / sep^D := by ring

end Work.HP.HP2
