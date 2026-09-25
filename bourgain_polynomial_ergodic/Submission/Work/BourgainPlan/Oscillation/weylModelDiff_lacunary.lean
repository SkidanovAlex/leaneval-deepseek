import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_inv_pow_summable
import Submission.Work.BourgainPlan.Maximal.model_pre
import Submission.Work.BourgainPlan.Maximal.l2_defs

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

open Work.BourgainPlan.Maximal

/-!
# The Weyl kernel minus its major-arc model: bounded, with summable lacunary increments

`model_pre` bounds the difference

`D_N(θ) = polyWeylKernel P N θ - polyMajorArcModelPre P (1/4) N θ`

by `C N^{-c₀}` for `N ≥ 3`.  This file extracts from it the two facts the oscillation
reduction needs, along the lacunary scales `N_i = ⌊ρ^i⌋` (`ρ > 1`):

* a uniform bound `B` for `D_{N_i}(θ)` on `θ ∈ (0,1]`: for `N ≥ 3` this is the decay bound, and
  the finitely many scales `N ≤ 2` are covered by the trivial bound `‖Weyl‖ ≤ 1` and the crude
  bound `‖model‖ ≤ c + 2` on the model (`c = lead P`);
* weights `a i > 0` dominating the increments `‖D_{N_{i+1}}(θ) - D_{N_i}(θ)‖`.  Since `⌊ρ^i⌋` is
  nondecreasing, the increment is at most `2 C' ⌊ρ^i⌋^{-c₀}`, so `a i = 2 C' 2^{c₀} ⌊ρ^i⌋^{-c₀}`
  works, and `∑_{i ∈ S} a i ≤ 2 C' 2^{c₀} · sup_S ∑_{i∈S} ⌊ρ^i⌋^{-c₀} < ∞` by
  `lacunary_inv_pow_summable`.

This is the input `hb`/`hinc` of `oscZ_of_multiplier_family`: the family
`m i θ = D_{⌊ρ^i⌋}(θ)` is uniformly bounded with summable increments, so the oscillation of the
true Weyl multiplier family can be replaced by that of the model family.
-/

/-- The Weyl kernel is a mean of `N` unit complex numbers, hence has norm at most one. -/
private lemma norm_polyWeylKernel_le_one (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) :
    ‖polyWeylKernel P N θ‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [polyWeylKernel]
  · have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hscal : ‖((((N : ℝ))⁻¹) : ℂ)‖ = (N:ℝ)⁻¹ := by
      rw [show ((((N : ℝ))⁻¹) : ℂ) = ((N : ℂ))⁻¹ by push_cast; ring, norm_inv,
        Complex.norm_natCast]
    have hsum : ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
        (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ ≤ (N:ℝ) := by
      calc ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
              (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖
          ≤ ∑ n ∈ Finset.range N, ‖Complex.exp (2 * Real.pi * Complex.I *
              (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ := norm_sum_le _ _
        _ = ∑ _n ∈ Finset.range N, (1:ℝ) := by
            apply Finset.sum_congr rfl
            intro n _
            exact norm_exp_two_pi_I_mul _
        _ = (N:ℝ) := by simp
    calc ‖polyWeylKernel P N θ‖
        = ‖((((N : ℝ))⁻¹) : ℂ)‖ * ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
            (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ := by
          rw [polyWeylKernel, norm_mul]
      _ ≤ (N:ℝ)⁻¹ * (N:ℝ) := by
          rw [hscal]
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hN0)

/-- For `N ≤ 2` the major-arc model is bounded by the number of arc terms of its single block,
`(lead P + 2).toNat`: the arc family has radius `N^{-(d-1/4)}` and `⌊N^{1/4}⌋ ≤ 1`, so the model
collapses to the single denominator `q = 1`. -/
private lemma norm_polyMajorArcModelPre_le_small (P : Polynomial ℤ) {N : ℕ} (hN : N ≤ 2)
    (θ : ℝ) :
    ‖polyMajorArcModelPre P ((1:ℝ)/4) N θ‖ ≤ ((P.leadingCoeff + 2).toNat : ℝ) := by
  have hx0 : (0:ℝ) ≤ (N:ℝ) ^ ((1:ℝ)/4) := Real.rpow_nonneg (by positivity) _
  have hx2 : (N:ℝ) ^ ((1:ℝ)/4) < 2 := by
    have h1 : (N:ℝ) ^ ((1:ℝ)/4) ≤ (2:ℝ) ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN) (by norm_num)
    have h2 : (2:ℝ) ^ ((1:ℝ)/4) < (2:ℝ) ^ (1:ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hF1 : ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊ ≤ 1 := by
    have h' : ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊ < 2 := (Nat.floor_lt hx0).mpr hx2
    omega
  have hterm : ∀ q ∈ Finset.Icc 1 ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊,
      ‖polyMajorArcBlockPre P ((1:ℝ)/4) N θ q‖ ≤ ((P.leadingCoeff + 2).toNat : ℝ) := by
    intro q hq
    have hq1 : q = 1 := by
      have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have h2 : q ≤ ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊ := (Finset.mem_Icc.mp hq).2
      omega
    subst hq1
    simpa using norm_polyMajorArcBlockPre_le P ((1:ℝ)/4) N 1 θ
  have hcard : (Finset.Icc 1 ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊).card ≤ 1 := by
    have hsub : Finset.Icc 1 ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊ ⊆ ({1} : Finset ℕ) := by
      intro q hq
      have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have h2 : q ≤ ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊ := (Finset.mem_Icc.mp hq).2
      simp only [Finset.mem_singleton]
      omega
    have := Finset.card_le_card hsub
    simpa using this
  have hnonneg : (0:ℝ) ≤ ((P.leadingCoeff + 2).toNat : ℝ) := by positivity
  rw [polyMajorArcModelPre]
  calc ‖∑ q ∈ Finset.Icc 1 ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊,
        polyMajorArcBlockPre P ((1:ℝ)/4) N θ q‖
      ≤ ∑ _q ∈ Finset.Icc 1 ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊,
          ((P.leadingCoeff + 2).toNat : ℝ) :=
        le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
    _ = ((Finset.Icc 1 ⌊(N:ℝ) ^ ((1:ℝ)/4)⌋₊).card : ℝ) * ((P.leadingCoeff + 2).toNat : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * ((P.leadingCoeff + 2).toNat : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hnonneg
        exact_mod_cast hcard
    _ = ((P.leadingCoeff + 2).toNat : ℝ) := one_mul _

/-- The lacunary scale is at least one. -/
private lemma one_le_lacScale (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) : 1 ≤ lacScale ρ i :=
  Nat.le_floor (by simpa using one_le_pow₀ (le_of_lt hρ) (n := i))

/-- The lacunary scale is nondecreasing. -/
private lemma lacScale_le_succ (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) :
    lacScale ρ i ≤ lacScale ρ (i + 1) :=
  Nat.floor_mono (pow_le_pow_right₀ (le_of_lt hρ) (Nat.le_succ i))

theorem weylModelDiff_lacunary (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree)
    (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ (a : ℕ → ℝ) (B D : ℝ), 0 ≤ B ∧ 0 ≤ D ∧ (∀ i, 0 < a i) ∧
      (∀ S : Finset ℕ, Finset.sum S (fun i => a i) ≤ D) ∧
      (∀ i (θ : ℝ), θ ∈ Set.Ioc (0:ℝ) 1 →
        ‖Work.BourgainPlan.Maximal.polyWeylKernel P
            (Work.BourgainPlan.Oscillation.lacScale ρ i) θ
          - Work.BourgainPlan.Maximal.polyMajorArcModelPre P ((1:ℝ)/4)
            (Work.BourgainPlan.Oscillation.lacScale ρ i) θ‖ ≤ B) ∧
      (∀ i (θ : ℝ), θ ∈ Set.Ioc (0:ℝ) 1 →
        ‖(Work.BourgainPlan.Maximal.polyWeylKernel P
              (Work.BourgainPlan.Oscillation.lacScale ρ (i+1)) θ
            - Work.BourgainPlan.Maximal.polyMajorArcModelPre P ((1:ℝ)/4)
              (Work.BourgainPlan.Oscillation.lacScale ρ (i+1)) θ)
          - (Work.BourgainPlan.Maximal.polyWeylKernel P
              (Work.BourgainPlan.Oscillation.lacScale ρ i) θ
            - Work.BourgainPlan.Maximal.polyMajorArcModelPre P ((1:ℝ)/4)
              (Work.BourgainPlan.Oscillation.lacScale ρ i) θ)‖ ≤ a i) := by
  obtain ⟨c₀, C, hc₀, hC, hmaj⟩ := Work.BourgainPlan.Maximal.model_pre P hc hd
  obtain ⟨G, hG0, hG⟩ := lacunary_inv_pow_summable ρ hρ c₀ hc₀
  have hc1 : (1:ℝ) ≤ (P.leadingCoeff : ℝ) := by
    have h : (1:ℤ) ≤ P.leadingCoeff := hc
    exact_mod_cast h
  -- the number of arc terms of a single block, expressed in `ℝ`
  have hlead : ((P.leadingCoeff + 2).toNat : ℝ) = (P.leadingCoeff : ℝ) + 2 := by
    have h : (0:ℤ) ≤ P.leadingCoeff + 2 := by omega
    exact_mod_cast (Int.toNat_of_nonneg h)
  let K : ℝ := 2 ^ c₀
  have hKpos : 0 < K := by positivity
  have hK1 : 1 ≤ K := Real.one_le_rpow (by norm_num) hc₀.le
  let C' : ℝ := max C (((P.leadingCoeff : ℝ) + 3) * K)
  have hC'pos : 0 < C' := by
    have h1 : (1:ℝ) ≤ ((P.leadingCoeff : ℝ) + 3) * K := by
      have h2 : (1:ℝ) ≤ (P.leadingCoeff : ℝ) + 3 := by linarith
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ ((P.leadingCoeff : ℝ) + 3) * K :=
            mul_le_mul h2 hK1 (by norm_num) (by linarith)
    exact lt_of_lt_of_le (by norm_num) (le_trans h1 (le_max_right _ _))
  -- the decay bound, made uniform in `N ≥ 1`
  have hdiff : ∀ (N : ℕ) (θ : ℝ), 1 ≤ N → θ ∈ Set.Ioc (0:ℝ) 1 →
      ‖polyWeylKernel P N θ - polyMajorArcModelPre P ((1:ℝ)/4) N θ‖
        ≤ C' * (N:ℝ) ^ (-c₀) := by
    intro N θ hN1 hθ
    by_cases h3 : 3 ≤ N
    · refine le_trans (hmaj N θ h3 (le_of_lt hθ.1) hθ.2) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left C _) (Real.rpow_nonneg (by positivity) _)
    · have hsmall : ‖polyWeylKernel P N θ - polyMajorArcModelPre P ((1:ℝ)/4) N θ‖
          ≤ (P.leadingCoeff : ℝ) + 3 := by
        have h1 := norm_polyWeylKernel_le_one P N θ
        have h2 := norm_polyMajorArcModelPre_le_small P (N := N) (by omega) θ
        rw [hlead] at h2
        calc ‖polyWeylKernel P N θ - polyMajorArcModelPre P ((1:ℝ)/4) N θ‖
            ≤ ‖polyWeylKernel P N θ‖ + ‖polyMajorArcModelPre P ((1:ℝ)/4) N θ‖ :=
              norm_sub_le _ _
          _ ≤ 1 + ((P.leadingCoeff : ℝ) + 2) := add_le_add h1 h2
          _ = (P.leadingCoeff : ℝ) + 3 := by ring
      have hN2 : N ≤ 2 := by omega
      have hK2 : (2:ℝ) ^ (-c₀) * K = 1 := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) c₀))
      have hmono : (2:ℝ) ^ (-c₀) ≤ (N:ℝ) ^ (-c₀) :=
        Real.rpow_le_rpow_of_nonpos (x := (N:ℝ)) (y := 2) (z := -c₀)
          (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast hN2) (by linarith)
      calc ‖polyWeylKernel P N θ - polyMajorArcModelPre P ((1:ℝ)/4) N θ‖
          ≤ (P.leadingCoeff : ℝ) + 3 := hsmall
        _ = (((P.leadingCoeff : ℝ) + 3) * K) * (2:ℝ) ^ (-c₀) := by
            rw [mul_assoc, mul_comm K ((2:ℝ) ^ (-c₀)), hK2, mul_one]
        _ ≤ C' * (2:ℝ) ^ (-c₀) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _)
        _ ≤ C' * (N:ℝ) ^ (-c₀) := mul_le_mul_of_nonneg_left hmono (le_of_lt hC'pos)
  refine ⟨fun i => 2 * C' * K * ((lacScale ρ i : ℝ)) ^ (-c₀), C', 2 * C' * K * G,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `0 ≤ B`
    exact le_of_lt hC'pos
  · -- `0 ≤ D`
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC'pos))
      (le_of_lt hKpos)) hG0
  · -- `0 < a i`
    intro i
    have hNi : (1:ℕ) ≤ lacScale ρ i := one_le_lacScale ρ hρ i
    have hpos : (0:ℝ) < (lacScale ρ i : ℝ) := by exact_mod_cast (by omega : 0 < lacScale ρ i)
    exact mul_pos (mul_pos (mul_pos (by norm_num) hC'pos) hKpos)
      (Real.rpow_pos_of_pos hpos (-c₀))
  · -- summability of `a`
    intro S
    rw [← Finset.mul_sum S (fun i => ((lacScale ρ i : ℝ)) ^ (-c₀)) (2 * C' * K)]
    exact mul_le_mul_of_nonneg_left (hG S)
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC'pos)) (le_of_lt hKpos))
  · -- uniform bound
    intro i θ hθ
    have hNi : (1:ℕ) ≤ lacScale ρ i := one_le_lacScale ρ hρ i
    refine le_trans (hdiff (lacScale ρ i) θ hNi hθ) ?_
    have h1 : ((lacScale ρ i : ℝ)) ^ (-c₀) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hNi) (by linarith)
    calc C' * ((lacScale ρ i : ℝ)) ^ (-c₀) ≤ C' * 1 :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hC'pos)
      _ = C' := mul_one C'
  · -- increments
    intro i θ hθ
    have hNi : (1:ℕ) ≤ lacScale ρ i := one_le_lacScale ρ hρ i
    have hNi' : (1:ℕ) ≤ lacScale ρ (i + 1) := one_le_lacScale ρ hρ (i + 1)
    have hle : lacScale ρ i ≤ lacScale ρ (i + 1) := lacScale_le_succ ρ hρ i
    have h1 := hdiff (lacScale ρ (i + 1)) θ hNi' hθ
    have h2 := hdiff (lacScale ρ i) θ hNi hθ
    have hmono : ((lacScale ρ (i + 1) : ℝ)) ^ (-c₀) ≤ ((lacScale ρ i : ℝ)) ^ (-c₀) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hle) (by linarith)
    have htri : ‖(polyWeylKernel P (lacScale ρ (i + 1)) θ
            - polyMajorArcModelPre P ((1:ℝ)/4) (lacScale ρ (i + 1)) θ)
          - (polyWeylKernel P (lacScale ρ i) θ
            - polyMajorArcModelPre P ((1:ℝ)/4) (lacScale ρ i) θ)‖
        ≤ C' * ((lacScale ρ (i + 1) : ℝ)) ^ (-c₀) + C' * ((lacScale ρ i : ℝ)) ^ (-c₀) :=
      le_trans (norm_sub_le _ _) (add_le_add h1 h2)
    calc ‖(polyWeylKernel P (lacScale ρ (i + 1)) θ
            - polyMajorArcModelPre P ((1:ℝ)/4) (lacScale ρ (i + 1)) θ)
          - (polyWeylKernel P (lacScale ρ i) θ
            - polyMajorArcModelPre P ((1:ℝ)/4) (lacScale ρ i) θ)‖
        ≤ C' * ((lacScale ρ (i + 1) : ℝ)) ^ (-c₀) + C' * ((lacScale ρ i : ℝ)) ^ (-c₀) := htri
      _ ≤ C' * ((lacScale ρ i : ℝ)) ^ (-c₀) + C' * ((lacScale ρ i : ℝ)) ^ (-c₀) :=
          add_le_add (mul_le_mul_of_nonneg_left hmono (le_of_lt hC'pos)) le_rfl
      _ = 2 * C' * ((lacScale ρ i : ℝ)) ^ (-c₀) := by ring
      _ ≤ 2 * C' * K * ((lacScale ρ i : ℝ)) ^ (-c₀) := by
          have hx : 0 ≤ ((lacScale ρ i : ℝ)) ^ (-c₀) := Real.rpow_nonneg (by positivity) _
          have h2C : 0 ≤ 2 * C' := by linarith [hC'pos]
          calc 2 * C' * ((lacScale ρ i : ℝ)) ^ (-c₀)
              = 2 * C' * (1 * ((lacScale ρ i : ℝ)) ^ (-c₀)) := by ring
            _ ≤ 2 * C' * (K * ((lacScale ρ i : ℝ)) ^ (-c₀)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK1 hx) h2C
            _ = 2 * C' * K * ((lacScale ρ i : ℝ)) ^ (-c₀) := by ring

end Work.BourgainPlan.Oscillation
