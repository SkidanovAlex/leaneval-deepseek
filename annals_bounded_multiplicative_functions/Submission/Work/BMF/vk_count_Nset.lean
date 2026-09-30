import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.space_count
import Submission.Work.BMF.vkN.rpow_theta_facts
import Submission.Work.BMF.vkN.increment_mem_of_deriv_bounds
import Submission.Work.BMF.vkN.final_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset
open scoped BigOperators

/-- **Crude counting bound for Heath-Brown's `Nset`.**  If `f` has its `k`-th derivative in
`[lam, A*lam]` on `(0, M+1)` with `A*lam ≤ 1/4` and `H = (A*lam)^(-1/k)`, then the number of
pairs `(m,n) ∈ [1,M]²` for which `f^{(j)}(m)/j! - f^{(j)}(n)/j!` is within `2H^{-j}` of an
integer for every `1 ≤ j ≤ k-1` (this is the set `Work.BMF.Nset k M f H`) is at most
`K · A² · (k-1)! · M · (1 + A*lam*M) · (1 + H)`.

Route.  Only the condition `j = k-1` is used.  For fixed `m` put
`g(x) = (f^{(k-1)}(x) - f^{(k-1)}(m))/(k-1)!`; the condition says `‖g n‖ ≤ 2H^{-(k-1)}` for the
`n` in question, while the mean value form gives
`g' = f^{(k)}/(k-1)! ∈ [lam/(k-1)!, A lam/(k-1)!]` on `(0,M)`, so the increments of `g` lie in
`[lam/(k-1)!, A lam/(k-1)!]`.  Since `H = (A lam)^{-1/k}` and `H^{k-1} ≥ 4^{(k-1)/k} ≥ 2`
(from `A lam ≤ 1/4`, `k ≥ 3`), the tolerance `theta = 2H^{-(k-1)}` is `≤ 1`, and since
`H^{-(k-1)} = A lam H` we may apply `Work.BMF.space_count` with `mu = lam/(k-1)!`, `A₀ = A` to
bound the number of admissible `n` by `100 (1 + A lam M/(k-1)!) (1 + 2A (k-1)! H)`.  Summing
over the `M` values of `m` and absorbing the constant factors into `K · A² (k-1)! (1 + H)`
gives the claim. -/
theorem vk_count_Nset :
    ∃ K : ℝ, 0 < K ∧ ∀ (k M : ℕ) (f : ℝ → ℝ) (H lam A : ℝ),
      3 ≤ k → 1 ≤ M → 0 < lam → 1 ≤ A → A * lam ≤ 1 / 4 → 1 ≤ H →
      H = (A * lam) ^ (-(1 / (k : ℝ))) →
      ContinuousOn (fun x => iteratedDeriv (k - 1) f x) (Set.Icc 0 (M : ℝ)) →
      DifferentiableOn ℝ (fun x => iteratedDeriv (k - 1) f x) (Set.Ioo 0 (M : ℝ)) →
      (∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) ((M : ℝ) + 1) →
        lam ≤ iteratedDeriv k f x ∧ iteratedDeriv k f x ≤ A * lam) →
      (((Nset k M f H).ncard : ℕ) : ℝ) ≤
        K * A ^ 2 * ((Nat.factorial (k - 1) : ℕ) : ℝ) * (M : ℝ) * (1 + A * lam * M) * (1 + H) := by
  classical
  refine ⟨200, by norm_num, ?_⟩
  intro k M f H lam A hk hM hlam hA hAlam hH1 hHdef hcont hdiff hder
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hAlam0 : (0 : ℝ) < A * lam := mul_pos hA0 hlam
  have hfact1 : (1 : ℝ) ≤ ((Nat.factorial (k - 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (k - 1)) : 1 ≤ Nat.factorial (k - 1))
  have hfact : (0 : ℝ) < ((Nat.factorial (k - 1) : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hfact1
  obtain ⟨hH1', hHpow, htheta_bound⟩ :=
    vkN.rpow_theta_facts (k := k) hk (u := A * lam) (H := H) hAlam0 hAlam hHdef
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH1'
  set theta : ℝ := 2 * H ^ (-(((k - 1 : ℕ) : ℝ))) with htheta_def
  have htheta_eq : theta = 2 * A * lam * H := by rw [htheta_def, hHpow]; ring
  have htheta0 : (0 : ℝ) ≤ theta := by
    rw [htheta_def]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hH0.le _)
  have htheta1 : theta ≤ 1 := by rw [htheta_def]; exact htheta_bound
  have hderiv_eq : ∀ x : ℝ,
      deriv (fun y : ℝ => iteratedDeriv (k - 1) f y) x = iteratedDeriv k f x := by
    intro x
    have hfun : deriv (fun y : ℝ => iteratedDeriv (k - 1) f y) = iteratedDeriv k f := by
      rw [← iteratedDeriv_succ (n := k - 1) (f := f)]
      congr 1
      omega
    rw [hfun]
  -- the comparison function `g m` for a fixed row `m`
  set g : ℕ → ℝ → ℝ := fun m x =>
    (iteratedDeriv (k - 1) f x - iteratedDeriv (k - 1) f (m : ℝ))
      / ((Nat.factorial (k - 1) : ℕ) : ℝ) with hg_def
  -- rows: membership in `Nset` forces the `j = k-1` condition for the comparison function
  have hrow_sub : ∀ m : ℕ,
      (Finset.Icc 1 M).filter (fun n : ℕ => (m, n) ∈ Nset k M f H) ⊆
        (Finset.Icc 1 M).filter (fun n : ℕ => nint (g m (n : ℝ)) ≤ theta) := by
    intro m n hn
    rw [Finset.mem_filter] at hn ⊢
    obtain ⟨hnIcc, hnN⟩ := hn
    refine ⟨hnIcc, ?_⟩
    simp only [Nset, Set.mem_ofPred_eq] at hnN
    obtain ⟨-, -, hcond⟩ := hnN
    obtain ⟨z, hz⟩ := hcond (k - 1) (by omega) le_rfl
    have hgn : g m (n : ℝ) =
        - (iteratedDeriv (k - 1) f (m : ℝ) / ((Nat.factorial (k - 1) : ℕ) : ℝ)
            - iteratedDeriv (k - 1) f (n : ℝ) / ((Nat.factorial (k - 1) : ℕ) : ℝ)) := by
      simp only [hg_def]
      ring
    rw [hgn, nint_neg, htheta_def]
    exact le_trans (nint_le_abs _ z) hz
  -- the counting bound of `space_count` for each row
  have hspace : ∀ m : ℕ,
      (((Finset.Icc 1 M).filter (fun n : ℕ => nint (g m (n : ℝ)) ≤ theta)).card : ℝ)
        ≤ 100 * (1 + A * (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)) * (M : ℝ))
            * (1 + theta / (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ))) := by
    intro m
    have hmu : (0 : ℝ) < lam / ((Nat.factorial (k - 1) : ℕ) : ℝ) := div_pos hlam hfact
    refine space_count M (g m) (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)) A theta
      hmu hA htheta0 htheta1 ?_ ?_
    · intro n hn1 hnM
      have hb := vkN.increment_mem_of_deriv_bounds (N := M)
        (F := fun x : ℝ => iteratedDeriv (k - 1) f x) (D := iteratedDeriv k f)
        (c := lam) (C := A * lam) hcont hdiff hderiv_eq hder hn1 hnM
      have hginc : g m ((n : ℝ) + 1) - g m (n : ℝ) =
          (iteratedDeriv (k - 1) f ((n : ℝ) + 1) - iteratedDeriv (k - 1) f (n : ℝ))
            / ((Nat.factorial (k - 1) : ℕ) : ℝ) := by
        simp only [hg_def]
        ring
      rw [hginc]
      exact (div_le_div_iff_of_pos_right hfact).mpr hb.1
    · intro n hn1 hnM
      have hb := vkN.increment_mem_of_deriv_bounds (N := M)
        (F := fun x : ℝ => iteratedDeriv (k - 1) f x) (D := iteratedDeriv k f)
        (c := lam) (C := A * lam) hcont hdiff hderiv_eq hder hn1 hnM
      have hginc : g m ((n : ℝ) + 1) - g m (n : ℝ) =
          (iteratedDeriv (k - 1) f ((n : ℝ) + 1) - iteratedDeriv (k - 1) f (n : ℝ))
            / ((Nat.factorial (k - 1) : ℕ) : ℝ) := by
        simp only [hg_def]
        ring
      rw [hginc, ← mul_div_assoc]
      exact (div_le_div_iff_of_pos_right hfact).mpr hb.2
  -- assemble: count the rows
  set An : ℕ → Finset ℕ :=
    fun m => (Finset.Icc 1 M).filter (fun n : ℕ => (m, n) ∈ Nset k M f H) with hAn
  set T : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 M).biUnion (fun m => (An m).image (fun n : ℕ => (m, n))) with hT
  have hNsub : Nset k M f H ⊆ (↑T : Set (ℕ × ℕ)) := by
    intro p hp
    simp only [Nset, Set.mem_ofPred_eq] at hp
    rw [Finset.mem_coe, hT, Finset.mem_biUnion]
    refine ⟨p.1, hp.1, ?_⟩
    rw [Finset.mem_image]
    refine ⟨p.2, ?_, rfl⟩
    rw [hAn, Finset.mem_filter]
    exact ⟨hp.2.1, by simp only [Nset, Set.mem_ofPred_eq]; exact hp⟩
  have hTncard : (Nset k M f H).ncard ≤ T.card := by
    have h := Set.ncard_le_ncard hNsub (Finset.finite_toSet T)
    simpa [Set.ncard_coe_finset] using h
  have hTcard : (T.card : ℝ) ≤ ∑ m ∈ Finset.Icc 1 M, ((An m).card : ℝ) := by
    have hnat : T.card ≤ ∑ m ∈ Finset.Icc 1 M, (An m).card := by
      have h1 : ((Finset.Icc 1 M).biUnion (fun m => (An m).image (fun n : ℕ => (m, n)))).card
          ≤ ∑ m ∈ Finset.Icc 1 M, ((An m).image (fun n : ℕ => (m, n))).card :=
        Finset.card_biUnion_le
      rw [hT]
      refine le_trans h1 ?_
      apply Finset.sum_le_sum
      intro m _
      rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
    calc (T.card : ℝ) ≤ ((∑ m ∈ Finset.Icc 1 M, (An m).card : ℕ) : ℝ) := by
          exact_mod_cast hnat
      _ = ∑ m ∈ Finset.Icc 1 M, ((An m).card : ℝ) := by push_cast; ring
  have hsum_le : ∑ m ∈ Finset.Icc 1 M, ((An m).card : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, (100 * (1 + A * (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)) * (M : ℝ))
          * (1 + theta / (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)))) := by
    apply Finset.sum_le_sum
    intro m _
    have h1 : (An m).card ≤
        ((Finset.Icc 1 M).filter (fun n : ℕ => nint (g m (n : ℝ)) ≤ theta)).card := by
      apply Finset.card_le_card
      rw [hAn]
      exact hrow_sub m
    exact le_trans (by exact_mod_cast h1) (hspace m)
  have hsum_const : ∑ m ∈ Finset.Icc 1 M,
        (100 * (1 + A * (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)) * (M : ℝ))
          * (1 + theta / (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ))))
      = (M : ℝ) * (100 * (1 + A * (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)) * (M : ℝ))
          * (1 + theta / (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)))) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  calc ((Nset k M f H).ncard : ℝ)
      ≤ (T.card : ℝ) := by exact_mod_cast hTncard
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ((An m).card : ℝ) := hTcard
    _ ≤ ∑ m ∈ Finset.Icc 1 M, (100 * (1 + A * (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)) * (M : ℝ))
          * (1 + theta / (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)))) := hsum_le
    _ = (M : ℝ) * (100 * (1 + A * (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)) * (M : ℝ))
          * (1 + theta / (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)))) := hsum_const
    _ ≤ 200 * A ^ 2 * ((Nat.factorial (k - 1) : ℕ) : ℝ) * (M : ℝ) * (1 + A * lam * M) * (1 + H) :=
        vkN.final_arith hM hk2 hlam hA hH0.le htheta_eq

end Work.BMF
