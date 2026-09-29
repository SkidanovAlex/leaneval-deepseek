import Mathlib
import Submission.Work.TMComp.LEBridge
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Cocycle.continuous_frob_iterC
import Submission.Work.TMC7Core.Lyap.lyap_nonneg
import Submission.Work.TMC7Core.Trig

/-!
# `LEFurman` — the locally uniform upper bound (component C4, part 2)

For irrational `α`, `E₀ ∈ ℂ` and `ε > 0` there are `r > 0` and `n₀` with

`log ‖A_n(x;E)‖_F ≤ n (L(E₀) + ε)`  for all `n ≥ n₀`, `‖E - E₀‖ < r` and all `x ∈ ℝ`

(AJ §9, [Fur]: Furman's theorem that for a uniquely ergodic base the *uniform* Lyapunov
exponent equals the averaged one).

The proof is the standard amortisation: fix a scale `k` with
`L_k = (1/k)∫₀¹ log ‖A_k‖ < L + ε/3`; the rotation by `kα` is irrational, so the Birkhoff
averages of the fixed continuous function `y ↦ log ‖A_k(y,E₀)‖` converge *uniformly* to
their mean (Weyl).  Writing `n = mk + r`, subadditivity bounds `log ‖A_n‖` by the `m`
blocks together with one leftover block, whose contribution is `O(1)`: hence
`log ‖A_n‖ ≤ O(1) + n (L + ε/3) + n ε/3 + n ε/3 = n (L + ε)` for large `n`.

The four analytic inputs (Weyl, continuity in `E` at a fixed scale, boundedness of the
low scales, and the subadditive decomposition) are hypotheses here, so that this file
only contains the amortisation and its `ε`-arithmetic.
-/

noncomputable section

namespace Work.TMComp

open MeasureTheory Filter

theorem furman_of_pieces
    (weyl : ∀ (β : ℝ), Irrational β → ∀ (f : ℝ → ℝ), Continuous f →
      (∀ x : ℝ, f (x + 1) = f x) →
      TendstoUniformly
        (fun (n : ℕ) (x : ℝ) => (∑ j ∈ Finset.range n, f (x + (j : ℝ) * β)) / (n : ℝ))
        (fun _ => ∫ x in (0 : ℝ)..1, f x) atTop)
    (energy_cont : ∀ (α lam : ℝ) (E₀ : ℂ) (k : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (E : ℂ) (x : ℝ), ‖E - E₀‖ ≤ 1 →
        |Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k x))
          - Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k x))|
            ≤ C * ‖E - E₀‖)
    (low_bound : ∀ (α lam : ℝ) (E₀ : ℂ) (k : ℕ), ∃ B : ℝ,
      ∀ (r : ℕ) (E : ℂ) (x : ℝ), r ≤ k → ‖E - E₀‖ ≤ 1 →
        Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E r x)) ≤ B)
    (decomp : ∀ (α lam : ℝ) (E : ℂ) (k n : ℕ) (x : ℝ), 1 ≤ k →
      Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E n x)) ≤
        Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E (n % k)
          (x + ((n / k : ℕ) : ℝ) * (k : ℝ) * α))) +
        ∑ j ∈ Finset.range (n / k),
          Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k
            (x + (j : ℝ) * (k : ℝ) * α))))
    (α lam : ℝ) (hα : Irrational α) (E₀ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ E : ℂ, ‖E - E₀‖ < r → ∀ x : ℝ,
      Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E n x))
        ≤ (n : ℝ) * (Work.TMC7Core.lyap α lam E₀ + ε) := by
  -- the finite-scale averages are nonnegative
  have hLk_nonneg : ∀ N : ℕ, 0 ≤ Work.TMC7Core.lyapAvg α lam E₀ N := by
    intro N
    rw [Work.TMC7Core.lyapAvg]
    refine div_nonneg ?_ (by positivity)
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro y _
    refine Real.log_nonneg ?_
    have h := Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
      (Work.TMC7Core.det_iterC α lam E₀ N y)
    linarith [Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)]
  have hL0 : 0 ≤ Work.TMC7Core.lyap α lam E₀ := Work.TMC7Core.Lyap.lyap_nonneg α lam E₀
  -- STEP 1: choose the scale
  obtain ⟨k, hk1, hklt⟩ : ∃ k : ℕ, 1 ≤ k ∧
      Work.TMC7Core.lyapAvg α lam E₀ k < Work.TMC7Core.lyap α lam E₀ + ε / 3 := by
    have hbdd : BddBelow (Set.range fun N : ℕ => Work.TMC7Core.lyapAvg α lam E₀ (N + 1)) :=
      ⟨0, by rintro y ⟨N, rfl⟩; exact hLk_nonneg (N + 1)⟩
    have hlt : (⨅ N : ℕ, Work.TMC7Core.lyapAvg α lam E₀ (N + 1))
        < Work.TMC7Core.lyap α lam E₀ + ε / 3 := by
      rw [← Work.TMC7Core.lyap_eq_iInf_lyapAvg]
      linarith
    obtain ⟨N, hN⟩ := (ciInf_lt_iff hbdd).mp hlt
    exact ⟨N + 1, Nat.succ_le_succ (Nat.zero_le N), by simpa using hN⟩
  have hkpos : 0 < k := hk1
  have hkne : (k : ℝ) ≠ 0 := by positivity
  -- STEP 2: the fixed-scale function and its uniform equidistribution
  let F : ℝ → ℝ := fun y => Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k y))
  have hFdef : ∀ y, F y
      = Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k y)) := fun y => rfl
  have hFpos : ∀ y, 0 < Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k y) := fun y =>
    lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num))
      (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
        (Work.TMC7Core.det_iterC α lam E₀ k y))
  have hFcont : Continuous F := by
    refine (Work.TMC7Core.Cocycle.continuous_frob_iterC α lam E₀ k).log (fun y => ?_)
    exact ne_of_gt (hFpos y)
  have hFper : ∀ y : ℝ, F (y + 1) = F y := by
    intro y
    show Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k (y + 1)))
      = Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k y))
    rw [Work.TMC7Core.iterC_periodic]
  have hFnonneg : ∀ y : ℝ, 0 ≤ F y := by
    intro y
    rw [hFdef y]
    refine Real.log_nonneg ?_
    have h := Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
      (Work.TMC7Core.det_iterC α lam E₀ k y)
    linarith [Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)]
  have hweyl := weyl ((k : ℝ) * α) (hα.natCast_mul (Nat.pos_iff_ne_zero.mp hkpos))
    F hFcont hFper
  have hweyl_ev : ∀ᶠ m : ℕ in atTop, ∀ y : ℝ,
      (∑ j ∈ Finset.range m, F (y + (j : ℝ) * ((k : ℝ) * α))) / (m : ℝ)
        ≤ (∫ y in (0 : ℝ)..1, F y) + ε / 6 := by
    have h := (Metric.tendstoUniformly_iff.mp hweyl) (ε / 6) (by linarith)
    filter_upwards [h] with m hm
    intro y
    have h2 := hm y
    rw [Real.dist_eq] at h2
    have h3 : (∑ j ∈ Finset.range m, F (y + (j : ℝ) * ((k : ℝ) * α))) / (m : ℝ)
        - (∫ y in (0 : ℝ)..1, F y) < ε / 6 := by
      rw [abs_sub_comm] at h2
      exact (abs_lt.mp h2).2
    linarith
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hweyl_ev
  -- STEP 3: continuity in the energy at scale `k`, and the low-scale bound
  obtain ⟨C, hCpos, hC⟩ := energy_cont α lam E₀ k
  obtain ⟨B, hB⟩ := low_bound α lam E₀ k
  -- STEP 4: the index threshold
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, 3 * B < (N₀ : ℝ) * ε := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (3 * B / ε)
    refine ⟨N₀, ?_⟩
    rw [div_lt_iff₀ hε] at hN₀
    linarith
  refine ⟨min 1 (ε / (6 * C)), lt_min one_pos (div_pos hε (by positivity)),
    max (k * M) (max 1 N₀), ?_⟩
  intro n hn E hE x
  -- geometric facts about the index `n`
  have hm : M ≤ n / k := by
    have h1 : k * M ≤ n := le_trans (le_max_left _ _) hn
    have h2 : M * k ≤ n := by rwa [Nat.mul_comm] at h1
    rwa [Nat.le_div_iff_mul_le hkpos]
  have hnN : N₀ ≤ n :=
    le_trans (le_max_right 1 N₀) (le_trans (le_max_right (k * M) (max 1 N₀)) hn)
  have hnormE : ‖E - E₀‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hE (min_le_left _ _))
  have hCE : C * ‖E - E₀‖ ≤ ε / 6 := by
    have h1 : ‖E - E₀‖ < ε / (6 * C) := lt_of_lt_of_le hE (min_le_right _ _)
    have h2 : C * ‖E - E₀‖ < C * (ε / (6 * C)) := mul_lt_mul_of_pos_left h1 hCpos
    have h3 : C * (ε / (6 * C)) = ε / 6 := by field_simp
    linarith [h2, h3.le, h3.ge]
  -- the three estimates
  have hdecomp := decomp α lam E k n x hk1
  have hlow : Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E (n % k)
      (x + ((n / k : ℕ) : ℝ) * (k : ℝ) * α))) ≤ B :=
    hB (n % k) E _ (Nat.le_of_lt (Nat.mod_lt _ hkpos)) hnormE
  have hEcont : ∀ j : ℕ,
      Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k
        (x + (j : ℝ) * (k : ℝ) * α)))
        ≤ F (x + (j : ℝ) * (k : ℝ) * α) + ε / 6 := by
    intro j
    have h := hC E (x + (j : ℝ) * (k : ℝ) * α) hnormE
    have habs := (abs_le.mp h).2
    rw [hFdef (x + (j : ℝ) * (k : ℝ) * α)]
    linarith
  have hsumE : (∑ j ∈ Finset.range (n / k), Real.log (Work.TMC7Core.frob
        (Work.TMC7Core.iterC α lam E k (x + (j : ℝ) * (k : ℝ) * α))))
      ≤ ∑ j ∈ Finset.range (n / k), (F (x + (j : ℝ) * (k : ℝ) * α) + ε / 6) :=
    Finset.sum_le_sum (fun j _ => hEcont j)
  have hsplit : (∑ j ∈ Finset.range (n / k), (F (x + (j : ℝ) * (k : ℝ) * α) + ε / 6))
      = (∑ j ∈ Finset.range (n / k), F (x + (j : ℝ) * (k : ℝ) * α))
        + ((n / k : ℕ) : ℝ) * (ε / 6) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hweylsum : (∑ j ∈ Finset.range (n / k), F (x + (j : ℝ) * (k : ℝ) * α))
      ≤ ((n / k : ℕ) : ℝ) * ((∫ y in (0 : ℝ)..1, F y) + ε / 6) := by
    by_cases hm0 : n / k = 0
    · simp [hm0]
    · have hmpos : (0 : ℝ) < ((n / k : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hm0
      have harg : (∑ j ∈ Finset.range (n / k), F (x + (j : ℝ) * ((k : ℝ) * α)))
          = ∑ j ∈ Finset.range (n / k), F (x + (j : ℝ) * (k : ℝ) * α) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        congr 1
        ring
      have h' : (∑ j ∈ Finset.range (n / k), F (x + (j : ℝ) * (k : ℝ) * α))
            / ((n / k : ℕ) : ℝ) ≤ (∫ y in (0 : ℝ)..1, F y) + ε / 6 := by
        rw [← harg]
        exact hM (n / k) hm x
      rw [div_le_iff₀ hmpos] at h'
      linarith [mul_comm ((∫ y in (0 : ℝ)..1, F y) + ε / 6) ((n / k : ℕ) : ℝ)]
  -- the integral of `F` against the chosen scale
  have hFbound : (∫ y in (0 : ℝ)..1, F y)
      ≤ (k : ℝ) * (Work.TMC7Core.lyap α lam E₀ + ε / 3) := by
    have hcongr : (∫ y in (0 : ℝ)..1, F y)
        = ∫ y in (0 : ℝ)..1,
            Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k y)) := by
      refine intervalIntegral.integral_congr ?_
      intro y _
      rfl
    rw [hcongr]
    have h2 : ((∫ y in (0 : ℝ)..1,
          Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k y))) / (k : ℝ)) * (k : ℝ)
        < (Work.TMC7Core.lyap α lam E₀ + ε / 3) * (k : ℝ) := by
      have h3 := hklt
      simp only [Work.TMC7Core.lyapAvg] at h3
      exact mul_lt_mul_of_pos_right h3 (by positivity)
    rw [div_mul_cancel₀ _ hkne] at h2
    linarith [h2]

  -- the arithmetic assembly
  have hmk : ((n / k : ℕ) : ℝ) * (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self n k
  have hLε : 0 ≤ Work.TMC7Core.lyap α lam E₀ + ε / 3 := by linarith
  have hprod1 : ((n / k : ℕ) : ℝ) * (∫ y in (0 : ℝ)..1, F y)
      ≤ (n : ℝ) * (Work.TMC7Core.lyap α lam E₀ + ε / 3) := by
    calc ((n / k : ℕ) : ℝ) * (∫ y in (0 : ℝ)..1, F y)
        ≤ ((n / k : ℕ) : ℝ) * ((k : ℝ) * (Work.TMC7Core.lyap α lam E₀ + ε / 3)) :=
          mul_le_mul_of_nonneg_left hFbound (by positivity)
      _ = (((n / k : ℕ) : ℝ) * (k : ℝ)) * (Work.TMC7Core.lyap α lam E₀ + ε / 3) := by ring
      _ ≤ (n : ℝ) * (Work.TMC7Core.lyap α lam E₀ + ε / 3) :=
          mul_le_mul_of_nonneg_right hmk hLε
  have hprod2 : ((n / k : ℕ) : ℝ) * (ε / 6) + ((n / k : ℕ) : ℝ) * (ε / 6)
      ≤ (n : ℝ) * (ε / 3) := by
    have h2 : ((n / k : ℕ) : ℝ) * (ε / 3) ≤ (n : ℝ) * (ε / 3) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self n k) (by linarith)
    calc ((n / k : ℕ) : ℝ) * (ε / 6) + ((n / k : ℕ) : ℝ) * (ε / 6)
        = ((n / k : ℕ) : ℝ) * (ε / 3) := by ring
      _ ≤ (n : ℝ) * (ε / 3) := h2
  have hBle : B ≤ (n : ℝ) * (ε / 3) := by
    have h1 : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    nlinarith [hN₀, h1, hε]
  have hmain : Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E n x))
      ≤ B + (∑ j ∈ Finset.range (n / k), Real.log (Work.TMC7Core.frob
          (Work.TMC7Core.iterC α lam E k (x + (j : ℝ) * (k : ℝ) * α)))) :=
    le_trans hdecomp (add_le_add hlow le_rfl)
  calc Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E n x))
      ≤ B + (∑ j ∈ Finset.range (n / k), Real.log (Work.TMC7Core.frob
          (Work.TMC7Core.iterC α lam E k (x + (j : ℝ) * (k : ℝ) * α)))) := hmain
    _ ≤ B + (∑ j ∈ Finset.range (n / k), (F (x + (j : ℝ) * (k : ℝ) * α) + ε / 6)) := by
        linarith [hsumE]
    _ = B + ((∑ j ∈ Finset.range (n / k), F (x + (j : ℝ) * (k : ℝ) * α))
          + ((n / k : ℕ) : ℝ) * (ε / 6)) := by rw [hsplit]
    _ ≤ (n : ℝ) * (Work.TMC7Core.lyap α lam E₀ + ε) := by
        nlinarith [hweylsum, hprod1, hprod2, hBle]

end Work.TMComp
