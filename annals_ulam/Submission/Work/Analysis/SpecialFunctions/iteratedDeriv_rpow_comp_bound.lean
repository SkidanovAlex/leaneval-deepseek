import Mathlib

namespace Work.Analysis.SpecialFunctions

open Finset

/-- The `k`-th derivative of `y ↦ y ^ p` is `(p)_k * y^(p-k)`, where `(p)_k` is the
descending Pochhammer polynomial. -/
private lemma iteratedDeriv_rpow (p ρ : ℝ) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => y ^ p) ρ
      = (descPochhammer ℝ k).eval p * ρ ^ (p - (k : ℝ)) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

/-- Uniform bound for the descending Pochhammer polynomial evaluated at `p`,
for all degrees `k ≤ n + 1`. -/
private lemma abs_descPochhammer_eval_le (p : ℝ) {k n : ℕ} (hk : k ≤ n + 1) :
    |(descPochhammer ℝ k).eval p| ≤ ∏ i ∈ Finset.range (n + 2), (1 + |p| + (i : ℝ)) := by
  rw [descPochhammer_eval_eq_prod_range, Finset.abs_prod]
  have h1 : ∏ i ∈ Finset.range k, |p - (i : ℝ)| ≤
      ∏ i ∈ Finset.range k, (1 + |p| + (i : ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro i _; exact abs_nonneg _
    · intro i _
      have hle : |p - (i : ℝ)| ≤ |p| + (i : ℝ) := by
        rw [abs_sub_le_iff]
        constructor
        · have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
          linarith [le_abs_self p, hi]
        · linarith [neg_le_abs p]
      linarith
  have h2 : ∏ i ∈ Finset.range k, (1 + |p| + (i : ℝ)) ≤
      ∏ i ∈ Finset.range (n + 2), (1 + |p| + (i : ℝ)) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i _; positivity
    · intro i _ _
      have ha : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have hb : (0 : ℝ) ≤ |p| := abs_nonneg p
      linarith
  exact le_trans h1 h2

theorem iteratedDeriv_rpow_comp_bound {p : ℝ} {n : ℕ} {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, ∀ Φ : ℝ → ℝ, ContDiffAt ℝ (n + 1) Φ 0 → c ≤ Φ 0 →
      (∀ j ≤ n + 1, |iteratedDeriv j Φ 0| ≤ C) →
      |iteratedDeriv (n + 1) (fun x : ℝ => (Φ x) ^ p) 0| ≤ K * (1 + c ^ (p - (n + 1))) := by
  let B : ℝ := ∏ i ∈ Finset.range (n + 2), (1 + |p| + (i : ℝ))
  have hBnn : 0 ≤ B := by
    show 0 ≤ ∏ i ∈ Finset.range (n + 2), (1 + |p| + (i : ℝ))
    exact Finset.prod_nonneg (fun i _ => by positivity)
  refine ⟨∑ σ : OrderedFinpartition (n + 1),
      B * max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ))) * C ^ σ.length, ?_⟩
  intro Φ hΦ hΦc hderiv
  have hΦC : Φ 0 ≤ C := by
    have h0 := hderiv 0 (Nat.zero_le _)
    rw [iteratedDeriv_zero] at h0
    exact le_trans (le_abs_self _) h0
  have hΦpos : 0 < Φ 0 := lt_of_lt_of_le hc hΦc
  have hg : ContDiffAt ℝ (n + 1) (fun y : ℝ => y ^ p) (Φ 0) :=
    Real.contDiffAt_rpow_const (n := n + 1) (Or.inl hΦpos.ne')
  rw [show (fun x : ℝ => (Φ x) ^ p) = (fun y : ℝ => y ^ p) ∘ Φ from rfl]
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition (𝕜 := ℝ) (g := fun y : ℝ => y ^ p)
      (f := Φ) (x := 0) (i := n + 1) hg hΦ (le_refl _)]
  have hbound : |∑ σ : OrderedFinpartition (n + 1),
        iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0) *
          ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0|
      ≤ ∑ σ : OrderedFinpartition (n + 1),
        B * max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ))) * C ^ σ.length := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ) (Finset.sum_le_sum ?_)
    intro σ _
    have hmax : 0 ≤ max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ))) :=
      le_trans (Real.rpow_nonneg hc.le _) (le_max_left _ _)
    have hA : |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0)|
        ≤ B * max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ))) := by
      rw [iteratedDeriv_rpow, abs_mul, abs_of_nonneg (Real.rpow_nonneg hΦpos.le _)]
      refine mul_le_mul (abs_descPochhammer_eval_le p σ.length_le) ?_
        (Real.rpow_nonneg hΦpos.le _) hBnn
      by_cases h : 0 ≤ p - (σ.length : ℝ)
      · exact le_trans (Real.rpow_le_rpow hΦpos.le hΦC h) (le_max_right _ _)
      · exact le_trans (Real.rpow_le_rpow_of_nonpos hc hΦc (lt_of_not_ge h).le) (le_max_left _ _)
    have hP : |∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0| ≤ C ^ σ.length := by
      rw [Finset.abs_prod]
      calc ∏ j : Fin σ.length, |iteratedDeriv (σ.partSize j) Φ 0|
          ≤ ∏ _j : Fin σ.length, C :=
            Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hderiv _ (σ.partSize_le j))
        _ = C ^ σ.length := by simp [Finset.prod_const]
    calc |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0) *
            ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0|
        = |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0)| *
            |∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0| := abs_mul _ _
      _ ≤ (B * max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ)))) * C ^ σ.length :=
            mul_le_mul hA hP (abs_nonneg _) (mul_nonneg hBnn hmax)
      _ = B * max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ))) * C ^ σ.length := by ring
  have hKnn : 0 ≤ ∑ σ : OrderedFinpartition (n + 1),
        B * max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ))) * C ^ σ.length :=
    Finset.sum_nonneg fun σ _ =>
      mul_nonneg (mul_nonneg hBnn (le_trans (Real.rpow_nonneg hc.le _) (le_max_left _ _)))
        (pow_nonneg hC _)
  calc |∑ σ : OrderedFinpartition (n + 1), iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ 0) *
          ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ 0|
      ≤ ∑ σ : OrderedFinpartition (n + 1),
          B * max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ))) * C ^ σ.length := hbound
    _ = (∑ σ : OrderedFinpartition (n + 1),
          B * max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ))) * C ^ σ.length) * 1 :=
        (mul_one _).symm
    _ ≤ (∑ σ : OrderedFinpartition (n + 1),
          B * max (c ^ (p - (σ.length : ℝ))) (C ^ (p - (σ.length : ℝ))) * C ^ σ.length) *
          (1 + c ^ (p - (n + 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ hKnn
        have h1 : (0 : ℝ) ≤ c ^ (p - (n + 1)) := Real.rpow_nonneg hc.le _
        linarith

end Work.Analysis.SpecialFunctions
