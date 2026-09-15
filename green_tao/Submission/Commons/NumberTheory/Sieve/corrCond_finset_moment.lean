import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_data
import Submission.Commons.Analysis.Convex.sum_pow_le_card_pow_mul_sum_pow_of_one_le

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Sieve

/-- **Correlation condition in finset form, with explicit moments.**  From the `m₀`-correlation
condition with `m₀ = 2 ^ d` we can extract a *single* weight `τ` whose `q`-th moment is bounded
by `(2 ^ d - 1) ^ (q - 1) · ∑_{2 ≤ m ≤ 2 ^ d} max (C m q) 0`, and which controls the correlation
of `d`-dimensional "cube" configurations: for every finset `A` of at least two cube vertices,
`𝔼_y ∏_{ω ∈ A} ν (y + ω · h) ≤ ∑_{ω ∈ A} ∑_{ω' ∈ A, ω' ≠ ω} τ (ω' · h - ω · h)`.

The weight is the sum `τ = ∑_{m ∈ Icc 2 (2 ^ d)} τ_m` of the individual weights supplied by the
correlation condition; the factor `2 ^ d - 1` is the number of such `m`, and the explicit moment
bound comes from the power-mean inequality. -/
theorem corrCond_finset_moment {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ}
    {C : ℕ → ℕ → ℝ} (hC : Commons.NumberTheory.Sieve.CorrCond p ν (2 ^ d) C) :
    ∃ τ : ZMod p → ℝ, (∀ x, 0 ≤ τ x) ∧
      (∀ q : ℕ, 1 ≤ q → ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ x) ^ q
        ≤ (((2 ^ d - 1 : ℕ)) : ℝ) ^ (q - 1)
          * ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, max (C m.1 q) 0) ∧
      (∀ A : Finset (Fin d → Bool), 2 ≤ A.card → ∀ h : Fin d → ZMod p,
        ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p,
            ∏ ω ∈ A, ν (y + ∑ i, (if ω i then h i else 0))
          ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'),
              τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0)))) := by
  classical
  have hτm : ∀ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, ∃ τ : ZMod p → ℝ, (∀ x, 0 ≤ τ x) ∧
      (∀ q : ℕ, 1 ≤ q → ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ x) ^ q ≤ C m.1 q) ∧
      ∀ h : Fin m.1 → ZMod p,
        ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ∏ i, ν (x + h i)
          ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), τ (h i - h j) := by
    intro m
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp m.2
    exact hC m.1 (by omega) hm2
  choose τm hτm0 hτmmom hτmcorr using hτm
  set L : ℕ := 2 ^ d - 1 with hLdef
  have hLcard : (Finset.univ : Finset {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}).card = L := by
    rw [hLdef, Finset.card_univ, Fintype.card_coe, Nat.card_Icc]
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    omega
  set τ : ZMod p → ℝ := fun x => ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, τm m x with hτdef
  have hτ0 : ∀ x, 0 ≤ τ x := fun x => Finset.sum_nonneg fun m _ => hτm0 m x
  have hNpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by positivity
  have hNne : ((Fintype.card (ZMod p) : ℝ)) ≠ 0 := ne_of_gt hNpos
  refine ⟨τ, hτ0, ?_, ?_⟩
  · intro q hq
    have hpm : ∀ x : ZMod p, (∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, τm m x) ^ q ≤
        (L : ℝ) ^ (q - 1) * ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, (τm m x) ^ q := by
      intro x
      rw [← hLcard]
      exact Commons.Analysis.Convex.sum_pow_le_card_pow_mul_sum_pow_of_one_le
        (Finset.univ) (fun m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)} => τm m x) q hq
        (fun m _ => hτm0 m x)
    have hA : (∑ x, (∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, τm m x) ^ q) ≤
        (L : ℝ) ^ (q - 1) *
          ∑ x, ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, (τm m x) ^ q := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => hpm x
    have hB : (∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, ∑ x, (τm m x) ^ q) ≤
        (Fintype.card (ZMod p) : ℝ) *
          ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, max (C m.1 q) 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m _
      have h1 : ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τm m x) ^ q ≤ max (C m.1 q) 0 :=
        le_trans (hτmmom m q hq) (le_max_left _ _)
      have h2 := mul_le_mul_of_nonneg_left h1 hNpos.le
      have h3 : ((Fintype.card (ZMod p) : ℝ)) *
            (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τm m x) ^ q)
          = ∑ x, (τm m x) ^ q := by
        rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
      rw [h3] at h2
      exact h2
    calc ((Fintype.card (ZMod p) : ℝ))⁻¹ *
          ∑ x, (∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, τm m x) ^ q
        ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ *
            ((L : ℝ) ^ (q - 1) *
              ∑ x, ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, (τm m x) ^ q) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = ((Fintype.card (ZMod p) : ℝ))⁻¹ *
            ((L : ℝ) ^ (q - 1) *
              ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, ∑ x, (τm m x) ^ q) := by
          rw [Finset.sum_comm]
      _ ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ *
            ((L : ℝ) ^ (q - 1) *
              ((Fintype.card (ZMod p) : ℝ) *
                ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, max (C m.1 q) 0)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hB (by positivity)
      _ = (L : ℝ) ^ (q - 1) *
            ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, max (C m.1 q) 0 := by
          field_simp
  · intro A hA h
    have hk1 : 1 ≤ A.card := by omega
    have hm2 : 1 < A.card := by omega
    have hmle : A.card ≤ 2 ^ d :=
      calc A.card ≤ (Finset.univ : Finset (Fin d → Bool)).card :=
            Finset.card_le_card fun x _ => Finset.mem_univ x
        _ = 2 ^ d := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_bool]
    have hmem : A.card ∈ Finset.Icc 2 (2 ^ d) := Finset.mem_Icc.mpr ⟨by omega, hmle⟩
    set hs : Fin A.card → ZMod p :=
      fun i => ∑ j, (if ((enumEquiv A).symm i).1 j then h j else 0) with hsdef
    set u : (Fin d → Bool) → ZMod p :=
      fun ω => ∑ i, (if ω i then h i else 0) with hudef
    have hcorrA := hτmcorr ⟨A.card, hmem⟩ hs
    have hτle : ∀ x : ZMod p, τm ⟨A.card, hmem⟩ x ≤ τ x := by
      intro x
      rw [hτdef]
      exact Finset.single_le_sum (f := fun m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)} => τm m x)
        (fun m _ => hτm0 m x) (Finset.mem_univ (⟨A.card, hmem⟩ :
          {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}))
    have hsu : ∀ x : {ω // ω ∈ A}, hs (enumEquiv A x) = u x.1 := by
      intro x
      simp only [hsdef, hudef, Equiv.symm_apply_apply]
    have hprod : ∀ y : ZMod p, (∏ ω ∈ A, ν (y + u ω)) = ∏ i : Fin A.card, ν (y + hs i) := by
      intro y
      rw [prod_enum A (fun ω => ν (y + u ω))]
    have h1 : (∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), τ (hs i - hs j))
        = ∑ i : Fin A.card, ∑ j : Fin A.card,
            (if j ≠ i then τ (hs i - hs j) else 0) := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_filter]
    have h2 : (∑ i : Fin A.card, ∑ j : Fin A.card,
            (if j ≠ i then τ (hs i - hs j) else 0))
        = ∑ x : {ω // ω ∈ A}, ∑ y : {ω // ω ∈ A},
            (if y ≠ x then τ (u x.1 - u y.1) else 0) := by
      rw [show (∑ i : Fin A.card, ∑ j : Fin A.card,
            (if j ≠ i then τ (hs i - hs j) else 0))
          = ∑ i : Fin A.card, ∑ y : {ω // ω ∈ A},
              (if enumEquiv A y ≠ i then τ (hs i - hs (enumEquiv A y)) else 0) from by
            apply Finset.sum_congr rfl; intro i _
            exact (Equiv.sum_comp (enumEquiv A)
              (fun j => if j ≠ i then τ (hs i - hs j) else 0)).symm]
      rw [show (∑ i : Fin A.card, ∑ y : {ω // ω ∈ A},
              (if enumEquiv A y ≠ i then τ (hs i - hs (enumEquiv A y)) else 0))
          = ∑ x : {ω // ω ∈ A}, ∑ y : {ω // ω ∈ A},
              (if enumEquiv A y ≠ enumEquiv A x
                then τ (hs (enumEquiv A x) - hs (enumEquiv A y)) else 0) from
            (Equiv.sum_comp (enumEquiv A) (fun i => ∑ y : {ω // ω ∈ A},
              (if enumEquiv A y ≠ i then τ (hs i - hs (enumEquiv A y)) else 0))).symm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      rw [hsu x, hsu y]
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne : ¬ (enumEquiv A y = enumEquiv A x) :=
          fun hh => hyx ((enumEquiv A).injective hh)
        simp [hyx, hne]
    have h3 : (∑ x : {ω // ω ∈ A}, ∑ y : {ω // ω ∈ A},
            (if y ≠ x then τ (u x.1 - u y.1) else 0))
        = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω') := by
      rw [← sum_attach_eq A (fun ω => ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω'))]
      apply Finset.sum_congr rfl; intro x _
      rw [show (∑ ω' ∈ A.filter (fun ω' => ω' ≠ ↑x), τ (u ↑x - u ω'))
          = ∑ y : {ω // ω ∈ A}, (if y.1 ≠ x.1 then τ (u x.1 - u y.1) else 0) from by
            rw [Finset.sum_filter,
              ← sum_attach_eq A (fun ω' => if ω' ≠ ↑x then τ (u ↑x - u ω') else 0)]]
      apply Finset.sum_congr rfl; intro y _
      by_cases hyx : y.1 = x.1
      · have hyx' : y = x := Subtype.ext hyx
        simp [hyx, hyx']
      · have : ¬ (y = x) := fun hh => hyx (congrArg Subtype.val hh)
        simp [hyx, this]
    have hprod_swap : (∑ p ∈ A.product A, (if p.2 ≠ p.1 then τ (u p.1 - u p.2) else 0))
        = ∑ p ∈ A.product A, (if p.1 ≠ p.2 then τ (u p.2 - u p.1) else 0) := by
      refine Finset.sum_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, (Finset.mem_product.mp hp).1⟩
      · intro p hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, (Finset.mem_product.mp hp).1⟩
      · intro p hp; rfl
      · intro p hp; rfl
      · intro p hp
        by_cases hne : p.2 ≠ p.1
        · have hne' : p.1 ≠ p.2 := hne.symm
          simp [hne, hne']
        · have hne' : ¬ (p.1 ≠ p.2) := fun hh => hne hh.symm
          simp [hne, hne']
    have hswap : (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω'))
        = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω) := by
      rw [show (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω'))
          = ∑ p ∈ A.product A, (if p.2 ≠ p.1 then τ (u p.1 - u p.2) else 0) from by
            rw [show (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω'))
                = ∑ ω ∈ A, ∑ ω' ∈ A, (if ω' ≠ ω then τ (u ω - u ω') else 0) from by
                  apply Finset.sum_congr rfl; intro ω _; rw [Finset.sum_filter]]
            exact (Finset.sum_product (s := A) (t := A)
              (f := fun p : (Fin d → Bool) × (Fin d → Bool) =>
                if p.2 ≠ p.1 then τ (u p.1 - u p.2) else 0)).symm]
      rw [show (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω))
          = ∑ p ∈ A.product A, (if p.1 ≠ p.2 then τ (u p.2 - u p.1) else 0) from by
            rw [show (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω))
                = ∑ ω ∈ A, ∑ ω' ∈ A, (if ω ≠ ω' then τ (u ω' - u ω) else 0) from by
                  apply Finset.sum_congr rfl; intro ω _; rw [Finset.sum_filter]]
            exact (Finset.sum_product (s := A) (t := A)
              (f := fun p : (Fin d → Bool) × (Fin d → Bool) =>
                if p.1 ≠ p.2 then τ (u p.2 - u p.1) else 0)).symm]
      exact hprod_swap
    have hstep : (∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            τm ⟨A.card, hmem⟩ (hs i - hs j))
        ≤ ∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), τ (hs i - hs j) := by
      apply Finset.sum_le_sum; intro i _
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
        (Finset.sum_le_sum fun j _ => hτle _)
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨Finset.mem_univ _, by omega⟩
      · intro j _ _
        exact hτm0 ⟨A.card, hmem⟩ _
    calc ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, ∏ ω ∈ A, ν (y + u ω)
        = ((Fintype.card (ZMod p) : ℝ))⁻¹ *
            ∑ y : ZMod p, ∏ i : Fin A.card, ν (y + hs i) := by
          rw [Finset.sum_congr rfl fun y _ => hprod y]
      _ ≤ ∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            τm ⟨A.card, hmem⟩ (hs i - hs j) := hcorrA
      _ ≤ ∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), τ (hs i - hs j) := hstep
      _ = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω') := by rw [h1, h2, h3]
      _ = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω) := hswap
      _ = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))) := by
          rw [hudef]

end Commons.NumberTheory.Sieve
