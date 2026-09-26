import Mathlib

/-!
# Polynomial decay of the derivatives of `s ↦ g (√s)` for Schwartz `g`

For a Schwartz function `g : ℝ → ℂ` and every `m N : ℕ`, the function
`s ↦ g (√s)` has its `m`-th derivative decaying faster than `s ^ (-N)` on
`[1, ∞)`: there is a constant `C` with

`s ^ N * ‖iteratedDeriv m (fun s => g (Real.sqrt s)) s‖ ≤ C` for all `s ≥ 1`.

This is proved by applying Faà di Bruno's formula
(`iteratedDeriv_scomp_eq_sum_orderedFinpartition`) to the composition
`g ∘ Real.sqrt`: every term of the resulting sum is a product of iterated
derivatives of `Real.sqrt` at `s` (all bounded on `[1, ∞)`, because every part
size in an `OrderedFinpartition` is positive, so the exponent
`1/2 - k` is nonpositive) with an iterated derivative of `g` at `√s`, which
decays faster than any polynomial since `g` is Schwartz.

## Main results

* `Work.RadialSpace.iteratedDeriv_sqrt_eq`: the explicit form
  `iteratedDeriv k (fun s => Real.sqrt s) s = sqrtCoeff k * s ^ (1/2 - k)`.
* `Work.RadialSpace.iteratedDeriv_comp_sqrt_pow_mul_le`: the decay estimate.
-/

set_option linter.unusedVariables false

open Filter Topology
open scoped ContDiff

namespace Work.RadialSpace

/-- The coefficient `∏_{i<k} (1/2 - i)` appearing in the `k`-th derivative of `√·`. -/
noncomputable def sqrtCoeff (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, ((1:ℝ)/2 - (i:ℝ))

lemma sqrtCoeff_zero : sqrtCoeff 0 = 1 := by simp [sqrtCoeff]

lemma sqrtCoeff_succ (k : ℕ) : sqrtCoeff (k+1) = sqrtCoeff k * ((1:ℝ)/2 - (k:ℝ)) := by
  simp [sqrtCoeff, Finset.prod_range_succ]

/-- The `k`-th derivative of the square root, in closed form. -/
lemma iteratedDeriv_sqrt_eq (k : ℕ) : ∀ {s : ℝ}, 0 < s →
    iteratedDeriv k (fun s => Real.sqrt s) s = sqrtCoeff k * s ^ ((1/2 : ℝ) - (k:ℝ)) := by
  induction k with
  | zero => intro s _; simp [Real.sqrt_eq_rpow, sqrtCoeff_zero]
  | succ k ih =>
      intro s hs
      rw [iteratedDeriv_succ]
      have hmem : ∀ᶠ t in 𝓝 s, 0 < t := isOpen_Ioi.mem_nhds hs
      have heq : iteratedDeriv k (fun s => Real.sqrt s) =ᶠ[𝓝 s]
          fun t => sqrtCoeff k * t ^ ((1/2:ℝ)-(k:ℝ)) :=
        hmem.mono (fun t ht => ih ht)
      rw [heq.deriv_eq]
      rw [deriv_const_mul _ (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hs))).differentiableAt]
      rw [Real.deriv_rpow_const]
      rw [sqrtCoeff_succ]
      have he : ((1/2:ℝ) - (k:ℝ)) - 1 = (1/2:ℝ) - ((k:ℝ)+1) := by ring
      rw [he]
      push_cast
      ring

/-- On `[1, ∞)` the derivatives of `√·` are uniformly bounded (every order `≥ 1`). -/
lemma abs_iteratedDeriv_sqrt_le (k : ℕ) (hk : 1 ≤ k) {s : ℝ} (hs : 1 ≤ s) :
    ‖iteratedDeriv k (fun s => Real.sqrt s) s‖ ≤ |sqrtCoeff k| := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  rw [iteratedDeriv_sqrt_eq k hs0, norm_mul, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hs0) _)]
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hle1 : s ^ ((1/2:ℝ)-(k:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  exact mul_le_of_le_one_right (abs_nonneg _) hle1

/-- **Polynomial decay of the derivatives of `s ↦ g (√s)`.**

For a Schwartz function `g` (evenness is not needed, but is part of the statement
as requested) and any `m N : ℕ`, the quantity `s ^ N * ‖D^m (g ∘ √·) s‖` is
bounded on `[1, ∞)`. -/
theorem iteratedDeriv_comp_sqrt_pow_mul_le (g : SchwartzMap ℝ ℂ) (he : Function.Even (⇑g))
    (m N : ℕ) : ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s →
      s ^ N * ‖iteratedDeriv m (fun s => g (Real.sqrt s)) s‖ ≤ C := by
  set B : ℝ := 1 + ∑ k ∈ Finset.range (m+1), |sqrtCoeff k| with hB
  have hB1 : 1 ≤ B := by
    rw [hB]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => abs_nonneg (sqrtCoeff k)))
  set S : ℝ := 1 + ∑ k ∈ Finset.range (m+1), SchwartzMap.seminorm ℝ (2*N) k g with hS
  refine ⟨(Fintype.card (OrderedFinpartition m) : ℝ) * B^m * S, ?_⟩
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsN : 0 ≤ s^N := pow_nonneg (le_of_lt hs0) N
  have hfb := iteratedDeriv_scomp_eq_sum_orderedFinpartition (𝕜 := ℝ) (g := ⇑g)
      (f := fun s => Real.sqrt s) (x := s) (n := ∞) (i := m)
      ((g.smooth (⊤ : ℕ∞)).contDiffAt) (Real.contDiffAt_sqrt (ne_of_gt hs0))
      (by exact_mod_cast le_top)
  have hgoal : iteratedDeriv m (fun s => g (Real.sqrt s)) s =
      ∑ c : OrderedFinpartition m, (∏ j, iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s) •
        iteratedDeriv c.length (⇑g) (Real.sqrt s) := hfb
  rw [hgoal]
  have hterm : ∀ c : OrderedFinpartition m,
      s^N * ‖(∏ j, iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s) •
        iteratedDeriv c.length (⇑g) (Real.sqrt s)‖ ≤ B^m * S := by
    intro c
    have hnorm : ‖(∏ j, iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s) •
          iteratedDeriv c.length (⇑g) (Real.sqrt s)‖ =
        (∏ j, ‖iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s‖) *
          ‖iteratedDeriv c.length (⇑g) (Real.sqrt s)‖ := by
      rw [norm_smul, norm_prod]
    rw [hnorm]
    have hprod : (∏ j, ‖iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s‖) ≤ B^m := by
      have heach : ∀ j, ‖iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s‖ ≤ B := by
        intro j
        have h1 : ‖iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s‖ ≤
            |sqrtCoeff (c.partSize j)| :=
          abs_iteratedDeriv_sqrt_le _ (c.partSize_pos j) hs
        have h2 : |sqrtCoeff (c.partSize j)| ≤ B := by
          rw [hB]
          have hmem : c.partSize j ∈ Finset.range (m+1) :=
            Finset.mem_range.mpr (Nat.lt_succ_of_le (c.partSize_le j))
          calc |sqrtCoeff (c.partSize j)| ≤ ∑ k ∈ Finset.range (m+1), |sqrtCoeff k| :=
                Finset.single_le_sum (s := Finset.range (m+1)) (f := fun k => |sqrtCoeff k|)
                  (fun k _ => abs_nonneg (sqrtCoeff k)) hmem
            _ ≤ 1 + ∑ k ∈ Finset.range (m+1), |sqrtCoeff k| := le_add_of_nonneg_left (by norm_num)
        linarith
      calc (∏ j, ‖iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s‖)
          ≤ ∏ j, B := Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => heach j)
        _ = B ^ c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ B ^ m := pow_le_pow_right₀ hB1 c.length_le
    have hgl : s^N * ‖iteratedDeriv c.length (⇑g) (Real.sqrt s)‖ ≤ S := by
      have hsemi : s^N * ‖iteratedDeriv c.length (⇑g) (Real.sqrt s)‖ ≤
          SchwartzMap.seminorm ℝ (2*N) c.length g := by
        have h1 := SchwartzMap.le_seminorm' ℝ (2*N) c.length g (Real.sqrt s)
        have h2 : |Real.sqrt s| ^ (2*N) = s^N := by
          rw [abs_of_nonneg (Real.sqrt_nonneg s), pow_mul, Real.sq_sqrt (le_of_lt hs0)]
        rwa [h2] at h1
      have h3 : SchwartzMap.seminorm ℝ (2*N) c.length g ≤ S := by
        rw [hS]
        have hmem : c.length ∈ Finset.range (m+1) :=
          Finset.mem_range.mpr (Nat.lt_succ_of_le c.length_le)
        calc SchwartzMap.seminorm ℝ (2*N) c.length g
            ≤ ∑ k ∈ Finset.range (m+1), SchwartzMap.seminorm ℝ (2*N) k g :=
              Finset.single_le_sum (s := Finset.range (m+1))
                (f := fun k => SchwartzMap.seminorm ℝ (2*N) k g) (fun k _ => by positivity) hmem
          _ ≤ 1 + ∑ k ∈ Finset.range (m+1), SchwartzMap.seminorm ℝ (2*N) k g :=
              le_add_of_nonneg_left (by norm_num)
      linarith
    have hkey : s^N * ((∏ j, ‖iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s‖) *
          ‖iteratedDeriv c.length (⇑g) (Real.sqrt s)‖)
        = (∏ j, ‖iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s‖) *
          (s^N * ‖iteratedDeriv c.length (⇑g) (Real.sqrt s)‖) := by ring
    rw [hkey]
    exact mul_le_mul hprod hgl (by positivity) (pow_nonneg (le_trans zero_le_one hB1) m)
  calc s^N * ‖∑ c : OrderedFinpartition m, (∏ j, iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s) • iteratedDeriv c.length (⇑g) (Real.sqrt s)‖
      ≤ s^N * ∑ c : OrderedFinpartition m, ‖(∏ j, iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s) • iteratedDeriv c.length (⇑g) (Real.sqrt s)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hsN
    _ = ∑ c : OrderedFinpartition m, s^N * ‖(∏ j, iteratedDeriv (c.partSize j) (fun s => Real.sqrt s) s) • iteratedDeriv c.length (⇑g) (Real.sqrt s)‖ :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ c : OrderedFinpartition m, B^m * S := Finset.sum_le_sum (fun c _ => hterm c)
    _ = (Fintype.card (OrderedFinpartition m) : ℝ) * B^m * S := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Work.RadialSpace
