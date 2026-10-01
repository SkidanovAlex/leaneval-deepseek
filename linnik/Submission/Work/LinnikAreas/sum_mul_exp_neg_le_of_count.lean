import Mathlib
import Submission.Work.LinnikAreas.sum_staircase_factor
import Submission.Work.LinnikAreas.count_filter_le_exp

namespace Work.LinnikAreas

/-- **One layer of the layer-cake.**  If `Λ ≤ lam` and `lam - Λ ≤ K`, then `exp (-a * lam)` is at most
`(1 - exp (-a))⁻¹` times the staircase sum `∑_{k ≤ K} (exp (-a (Λ+k)) - exp (-a (Λ+k+1))) 1[lam ≤ Λ+k+1]`:
the terms of the staircase with `k ≥ ⌊lam - Λ⌋` telescope, and the truncated tail loses at most the
factor `exp (-a)`.

This is the single-value (per-zero) estimate underlying the layer-cake bound. -/
lemma exp_neg_mul_le_staircase {a : ℝ} (ha : 0 < a) {Λ : ℝ} (K : ℕ) {lam : ℝ}
    (hlamΛ : Λ ≤ lam) (hlamK : lam - Λ ≤ (K : ℝ)) :
    (1 - Real.exp (-a)) * Real.exp (-a * lam) ≤
      ∑ k ∈ Finset.range (K + 1),
        (Real.exp (-a * (Λ + (k:ℝ))) - Real.exp (-a * (Λ + (k:ℝ) + 1))) *
          (if lam ≤ Λ + (k:ℝ) + 1 then (1 : ℝ) else 0) := by
  set j : ℕ := Nat.floor (lam - Λ) with hjdef
  have hj0 : (0:ℝ) ≤ lam - Λ := by linarith
  have hjle : (j:ℝ) ≤ lam - Λ := by rw [hjdef]; exact Nat.floor_le hj0
  have hjK : j ≤ K := by rw [hjdef]; exact Nat.floor_le_of_le hlamK
  have hΛj : Λ + (j:ℝ) ≤ lam := by linarith
  have hlt : lam < Λ + (j:ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (lam - Λ); rw [← hjdef] at h; linarith
  have h1ma : (0:ℝ) ≤ 1 - Real.exp (-a) := by
    have h : Real.exp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  -- telescoping of the staircase over a full range of indices
  have key : ∀ N : ℕ, ∑ k ∈ Finset.range N,
        (Real.exp (-a * (Λ + (k:ℝ))) - Real.exp (-a * (Λ + (k:ℝ) + 1)))
      = Real.exp (-a * Λ) - Real.exp (-a * (Λ + (N:ℝ))) := by
    intro N
    have h1 : ∑ k ∈ Finset.range N,
          (Real.exp (-a * (Λ + (k:ℝ))) - Real.exp (-a * (Λ + (k:ℝ) + 1)))
        = ∑ k ∈ Finset.range N,
            ((fun i : ℕ => Real.exp (-a * (Λ + (i:ℝ)))) k -
              (fun i : ℕ => Real.exp (-a * (Λ + (i:ℝ)))) (k+1)) := by
      apply Finset.sum_congr rfl; intro k _
      simp only
      congr 2
      push_cast
      ring
    rw [h1, Finset.sum_range_sub']
    congr 1
    push_cast
    ring_nf
  have htel : ∑ k ∈ Finset.Ico j (K+1),
        (Real.exp (-a * (Λ + (k:ℝ))) - Real.exp (-a * (Λ + (k:ℝ) + 1)))
      = Real.exp (-a * (Λ + (j:ℝ))) - Real.exp (-a * (Λ + ((K:ℝ) + 1))) := by
    rw [Finset.sum_Ico_eq_sub _ (by omega), key, key]
    push_cast
    ring_nf
  calc (1 - Real.exp (-a)) * Real.exp (-a*lam)
      ≤ (1 - Real.exp (-a)) * Real.exp (-a*(Λ + (j:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ h1ma
          apply Real.exp_le_exp.mpr
          nlinarith [hΛj]
    _ ≤ Real.exp (-a*(Λ+(j:ℝ))) - Real.exp (-a*(Λ+((K:ℝ)+1))) := by
          have h2 : Real.exp (-a*(Λ + ((K:ℝ)+1))) ≤ Real.exp (-a) * Real.exp (-a*(Λ+(j:ℝ))) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have h3 : (j:ℝ) + 1 ≤ ((K:ℝ) + 1) := by exact_mod_cast Nat.succ_le_succ hjK
            nlinarith
          have hid : (1 - Real.exp (-a)) * Real.exp (-a*(Λ+(j:ℝ)))
              = Real.exp (-a*(Λ+(j:ℝ))) - Real.exp (-a)*Real.exp (-a*(Λ+(j:ℝ))) := by ring
          linarith
    _ = ∑ k ∈ Finset.Ico j (K+1),
          (Real.exp (-a * (Λ+(k:ℝ))) - Real.exp (-a * (Λ+(k:ℝ)+1))) := htel.symm
    _ ≤ ∑ k ∈ Finset.Ico j (K+1),
          (Real.exp (-a * (Λ+(k:ℝ))) - Real.exp (-a * (Λ+(k:ℝ)+1))) *
            (if lam ≤ Λ + (k:ℝ) + 1 then (1:ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkj : (j:ℝ) ≤ (k:ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hk).1
          have hcond : lam ≤ Λ + (k:ℝ) + 1 := by linarith
          rw [if_pos hcond, mul_one]
    _ ≤ ∑ k ∈ Finset.range (K+1),
          (Real.exp (-a * (Λ+(k:ℝ))) - Real.exp (-a * (Λ+(k:ℝ)+1))) *
            (if lam ≤ Λ + (k:ℝ) + 1 then (1:ℝ) else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
          · intro k _ _
            have hd : 0 ≤ Real.exp (-a*(Λ+(k:ℝ))) - Real.exp (-a*(Λ+(k:ℝ)+1)) := by
              apply sub_nonneg.mpr
              apply Real.exp_le_exp.mpr
              nlinarith
            by_cases hc : lam ≤ Λ + (k:ℝ) + 1
            · rw [if_pos hc, mul_one]; exact hd
            · rw [if_neg hc, mul_zero]

/-- **Layer-cake / dyadic summation bound.**  Given a finite family of "zeros" `i ∈ S` with
nonnegative weights `m i`, values `lam i ∈ [Λ, L]`, and a counting hypothesis saying that the total
weight of the sub-family with `lam i ≤ t` is at most `D * lam₁ * exp (c * t)` for every
`t ∈ [Λ, L]`, with `0 ≤ c < a₀`, the weighted exponential sum is at most
`D * lam₁ * exp c * exp ((c - a₀) Λ) / (1 - exp (c - a₀))`.

(Proof idea, in the style of `Work.LinnikAreas.abel_lam` in
`Submission/Work/LinnikAreas/siegelRestHigh.lean`: with `K = ⌈L - Λ⌉₊`, telescoping gives for every
`λ ∈ [Λ, L]`
`(1 - exp (-a₀)) * exp (-a₀ λ) ≤ ∑_{k ∈ range (K+1)} (exp (-a₀ (Λ + k)) - exp (-a₀ (Λ + k + 1))) * 1[λ < Λ+k+1]`;
multiply by `m i` and sum over `i ∈ S`, swap the two sums, apply the counting hypothesis at
`t = min (Λ + k + 1) L` (every `lam i ≤ L` makes this cut-off legitimate) and bound the resulting
geometric series. When `S = ∅` the goal is `0 ≤ ... `, so no hypothesis `Λ ≤ L` is needed.) -/
theorem sum_mul_exp_neg_le_of_count {ι : Type*} (S : Finset ι) (m lam : ι → ℝ)
    {a₀ Λ L D lam₁ c : ℝ} (ha₀ : 0 < a₀) (hc0 : 0 ≤ c) (hca₀ : c < a₀)
    (hD : 0 < D) (hΛ : 0 < Λ) (hlam₁ : 0 < lam₁)
    (hm : ∀ i ∈ S, 0 ≤ m i)
    (hlam : ∀ i ∈ S, Λ ≤ lam i) (hlamL : ∀ i ∈ S, lam i ≤ L)
    (hcount : ∀ t : ℝ, Λ ≤ t → t ≤ L →
      (∑ i ∈ S.filter (fun i => lam i ≤ t), m i) ≤ D * lam₁ * Real.exp (c * t)) :
    ∑ i ∈ S, m i * Real.exp (-a₀ * lam i)
      ≤ D * lam₁ * Real.exp c * Real.exp ((c - a₀) * Λ) / (1 - Real.exp (c - a₀)) := by
  have hposm : 0 < 1 - Real.exp (-a₀) := by
    have h : Real.exp (-a₀) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hden : 0 < 1 - Real.exp (c - a₀) := by
    have h : Real.exp (c - a₀) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rcases Finset.eq_empty_or_nonempty S with hS | hS
  · -- no zeros: the left side vanishes and the right side is nonnegative
    subst hS
    simp only [Finset.sum_empty]
    exact div_nonneg (by positivity) (le_of_lt hden)
  · obtain ⟨i₀, hi₀⟩ := hS
    have hΛL : Λ ≤ L := le_trans (hlam i₀ hi₀) (hlamL i₀ hi₀)
    -- the counting hypothesis at the dyadic cut-offs, extended past `L`
    have hcnt : ∀ k : ℕ, (∑ i ∈ S.filter (fun i => lam i ≤ Λ + (k:ℝ) + 1), m i)
        ≤ D * lam₁ * Real.exp (c * (Λ + (k:ℝ) + 1)) :=
      fun k => count_filter_le_exp S m lam hc0 hm hlamL hΛL hcount k
    set K : ℕ := ⌈L - Λ⌉₊ with hKdef
    have hK : L - Λ ≤ (K : ℝ) := by rw [hKdef]; exact Nat.le_ceil _
    -- step 1: the per-zero layer-cake estimate, multiplied by `m i` and summed over `S`
    have hA : (1 - Real.exp (-a₀)) * (∑ i ∈ S, m i * Real.exp (-a₀ * lam i))
        ≤ ∑ i ∈ S, ∑ k ∈ Finset.range (K+1),
            m i * ((Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
              (if lam i ≤ Λ + (k:ℝ) + 1 then (1:ℝ) else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hpt := exp_neg_mul_le_staircase ha₀ (K := K) (hlam i hi) (by linarith [hlamL i hi, hK])
      calc (1 - Real.exp (-a₀)) * (m i * Real.exp (-a₀ * lam i))
          = m i * ((1 - Real.exp (-a₀)) * Real.exp (-a₀ * lam i)) := by ring
        _ ≤ m i * (∑ k ∈ Finset.range (K+1),
              (Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
                (if lam i ≤ Λ + (k:ℝ) + 1 then (1:ℝ) else 0)) :=
            mul_le_mul_of_nonneg_left hpt (hm i hi)
        _ = ∑ k ∈ Finset.range (K+1),
              m i * ((Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
                (if lam i ≤ Λ + (k:ℝ) + 1 then (1:ℝ) else 0)) := by
            rw [Finset.mul_sum]
    -- step 2: interchange the two sums, turning the inner sum into the counting function at a cut-off
    have hB : ∑ i ∈ S, ∑ k ∈ Finset.range (K+1),
            m i * ((Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
              (if lam i ≤ Λ + (k:ℝ) + 1 then (1:ℝ) else 0))
        = ∑ k ∈ Finset.range (K+1),
            (Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
              (∑ i ∈ S.filter (fun i => lam i ≤ Λ + (k:ℝ) + 1), m i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : lam i ≤ Λ + (k:ℝ) + 1
      · simp only [h, if_true, mul_one]
        ring
      · simp [h]
    -- step 3: bound the counting function at each cut-off by the counting hypothesis
    have hC : ∑ k ∈ Finset.range (K+1),
            (Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
              (∑ i ∈ S.filter (fun i => lam i ≤ Λ + (k:ℝ) + 1), m i)
        ≤ ∑ k ∈ Finset.range (K+1),
            (Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
              (D * lam₁ * Real.exp (c * (Λ + (k:ℝ) + 1))) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left (hcnt k)
      apply sub_nonneg.mpr
      apply Real.exp_le_exp.mpr
      nlinarith
    -- step 4: the staircase weights collapse to a geometric partial sum
    have hD4 : ∑ k ∈ Finset.range (K+1),
            (Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
              (D * lam₁ * Real.exp (c * (Λ + (k:ℝ) + 1)))
        = D * lam₁ * Real.exp c * (1 - Real.exp (-a₀)) * Real.exp ((c - a₀) * Λ)
            * ∑ k ∈ Finset.range (K+1), (Real.exp (c - a₀))^k :=
      sum_staircase_factor a₀ c Λ D lam₁ K
    -- step 5: the geometric series is bounded by its sum
    have hq0 : 0 ≤ Real.exp (c - a₀) := Real.exp_nonneg _
    have hq1 : Real.exp (c - a₀) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hgeo : ∑ k ∈ Finset.range (K+1), (Real.exp (c - a₀))^k ≤ 1 / (1 - Real.exp (c - a₀)) := by
      have h := geom_sum_Ico_le_of_lt_one (x := Real.exp (c - a₀)) hq0 hq1 (m := 0) (n := K+1)
      rw [Nat.Ico_zero_eq_range, pow_zero] at h
      exact h
    have hCst : 0 ≤ D * lam₁ * Real.exp c * (1 - Real.exp (-a₀)) * Real.exp ((c - a₀) * Λ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hD) (le_of_lt hlam₁))
        (Real.exp_nonneg c)) (le_of_lt hposm)) (Real.exp_nonneg _)
    have hE : D * lam₁ * Real.exp c * (1 - Real.exp (-a₀)) * Real.exp ((c - a₀) * Λ)
          * (∑ k ∈ Finset.range (K+1), (Real.exp (c - a₀))^k)
        ≤ D * lam₁ * Real.exp c * (1 - Real.exp (-a₀)) * Real.exp ((c - a₀) * Λ)
          * (1 / (1 - Real.exp (c - a₀))) :=
      mul_le_mul_of_nonneg_left hgeo hCst
    -- assembly
    have key : (1 - Real.exp (-a₀)) * (∑ i ∈ S, m i * Real.exp (-a₀ * lam i))
        ≤ (1 - Real.exp (-a₀)) *
            (D * lam₁ * Real.exp c * Real.exp ((c - a₀) * Λ) / (1 - Real.exp (c - a₀))) := by
      calc (1 - Real.exp (-a₀)) * (∑ i ∈ S, m i * Real.exp (-a₀ * lam i))
          ≤ ∑ i ∈ S, ∑ k ∈ Finset.range (K+1),
              m i * ((Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
                (if lam i ≤ Λ + (k:ℝ) + 1 then (1:ℝ) else 0)) := hA
        _ = ∑ k ∈ Finset.range (K+1),
              (Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
                (∑ i ∈ S.filter (fun i => lam i ≤ Λ + (k:ℝ) + 1), m i) := hB
        _ ≤ ∑ k ∈ Finset.range (K+1),
              (Real.exp (-a₀*(Λ+(k:ℝ))) - Real.exp (-a₀*(Λ+(k:ℝ)+1))) *
                (D * lam₁ * Real.exp (c * (Λ + (k:ℝ) + 1))) := hC
        _ = D * lam₁ * Real.exp c * (1 - Real.exp (-a₀)) * Real.exp ((c - a₀) * Λ)
              * (∑ k ∈ Finset.range (K+1), (Real.exp (c - a₀))^k) := hD4
        _ ≤ D * lam₁ * Real.exp c * (1 - Real.exp (-a₀)) * Real.exp ((c - a₀) * Λ)
              * (1 / (1 - Real.exp (c - a₀))) := hE
        _ = (1 - Real.exp (-a₀)) *
              (D * lam₁ * Real.exp c * Real.exp ((c - a₀) * Λ) / (1 - Real.exp (c - a₀))) := by
            ring
    exact le_of_mul_le_mul_left key hposm

end Work.LinnikAreas
