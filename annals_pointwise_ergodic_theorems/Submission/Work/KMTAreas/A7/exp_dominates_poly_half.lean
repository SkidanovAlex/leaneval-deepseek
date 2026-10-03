import Mathlib

namespace Work.KMTAreas.A7

open Filter Asymptotics

/-- The exponential `2 ^ (ρ * L)` dominates the polynomial-ish expression
`a * (1 + L * 2 ^ (ρ * L / 2) + L) + b * L + c` uniformly in `L : ℕ`, for `0 < ρ ≤ 1`
and `a, b, c ≥ 0`. -/
theorem exp_dominates_poly_half (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℕ,
      a * (1 + (L : ℝ) * (2 : ℝ) ^ (ρ * (L : ℝ) / 2) + (L : ℝ)) + b * (L : ℝ) + c
        ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) + K := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set lam : ℝ := ρ * Real.log 2 with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; exact mul_pos hρ hlog
  have hlam2 : lam / 2 < lam := by linarith
  -- rewrite the two exponentials `2 ^ (ρ * t)` and `2 ^ (ρ * t / 2)` as `Real.exp`
  have hpow : ∀ t : ℝ, (2:ℝ) ^ (ρ * t) = Real.exp (lam * t) := by
    intro t
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), hlamdef]
    congr 1
    ring
  have hpow2 : ∀ t : ℝ, (2:ℝ) ^ (ρ * t / 2) = Real.exp ((lam/2) * t) := by
    intro t
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), hlamdef]
    congr 1
    ring
  -- the asymptotics: the whole polynomial-ish expression is `o(2 ^ (ρ t))`
  have h1 : (fun t : ℝ => (a + c) + (a + b) * t + a * (t * Real.exp ((lam/2) * t)))
      =o[atTop] (fun t : ℝ => Real.exp (lam * t)) := by
    have hcst : (fun _ : ℝ => (1:ℝ)) =o[atTop] (fun t : ℝ => Real.exp (lam * t)) := by
      simpa [Real.rpow_zero] using (isLittleO_rpow_exp_pos_mul_atTop (0:ℝ) hlam :
        (fun x : ℝ => x ^ (0:ℝ)) =o[atTop] fun x => Real.exp (lam * x))
    have hAc : (fun _ : ℝ => (a + c)) =o[atTop] (fun t : ℝ => Real.exp (lam * t)) := by
      have := hcst.const_mul_left (a + c)
      simpa using this
    have hlin : (fun t : ℝ => (a + b) * t) =o[atTop] (fun t : ℝ => Real.exp (lam * t)) := by
      have h := isLittleO_rpow_exp_pos_mul_atTop (1:ℝ) hlam
      have h' : (fun x : ℝ => x) =o[atTop] fun x => Real.exp (lam * x) := by
        simpa [Real.rpow_one] using h
      have := h'.const_mul_left (a + b)
      simpa using this
    have hexp : (fun t : ℝ => a * (t * Real.exp ((lam/2) * t)))
        =o[atTop] (fun t : ℝ => Real.exp (lam * t)) := by
      have h := isLittleO_exp_mul_rpow_of_lt (1:ℝ) hlam2
      have h' : (fun t : ℝ => t * Real.exp ((lam/2) * t))
          =o[atTop] fun t => Real.exp (lam * t) := by
        simpa [Real.rpow_one, mul_comm] using h
      have := h'.const_mul_left a
      simpa using this
    have := (hAc.add hlin).add hexp
    simpa using this
  have hEv : ∀ᶠ t : ℝ in atTop,
      (a + c) + (a + b) * t + a * (t * Real.exp ((lam/2) * t))
        ≤ Real.exp (lam * t) := by
    filter_upwards [h1.bound zero_lt_one] with t ht
    have hGpos : 0 < Real.exp (lam * t) := Real.exp_pos _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hGpos, one_mul] at ht
    exact (le_abs_self _).trans ht
  obtain ⟨T, hT⟩ := eventually_atTop.1 hEv
  let N : ℕ := ⌈T⌉₊ + 1
  let F : ℕ → ℝ := fun L => a * (1 + (L:ℝ) * (2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) + b*(L:ℝ) + c
  let K : ℝ := max 0 (∑ L ∈ Finset.range N, F L)
  refine ⟨K, le_max_left _ _, ?_⟩
  have hK : 0 ≤ K := le_max_left _ _
  intro L
  show F L ≤ (2:ℝ)^(ρ*(L:ℝ)) + K
  rcases lt_or_ge L N with hL | hL
  · -- finitely many small `L`: absorb into `K`
    have hmem : L ∈ Finset.range N := Finset.mem_range.mpr hL
    have hnonneg : ∀ i ∈ Finset.range N, 0 ≤ F i := by
      intro i _
      dsimp only [F]
      have hi1 : 0 ≤ (2:ℝ)^(ρ*(i:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
      have hi2 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
      have hprod : 0 ≤ (i:ℝ) * (2:ℝ)^(ρ*(i:ℝ)/2) := mul_nonneg hi2 hi1
      have ht1 : 0 ≤ a * (1 + (i:ℝ) * (2:ℝ)^(ρ*(i:ℝ)/2) + (i:ℝ)) :=
        mul_nonneg ha (by linarith)
      have ht2 : 0 ≤ b * (i:ℝ) := mul_nonneg hb hi2
      linarith
    have hsingle : F L ≤ ∑ i ∈ Finset.range N, F i :=
      Finset.single_le_sum (f := F) hnonneg hmem
    have hmax : (∑ i ∈ Finset.range N, F i) ≤ K := le_max_right _ _
    have hle : F L ≤ K := hsingle.trans hmax
    have hRHS : 0 ≤ (2:ℝ)^(ρ*(L:ℝ)) := Real.rpow_nonneg (by norm_num) _
    linarith
  · -- large `L`: the exponential dominates
    have hTN : T ≤ (N:ℝ) := by
      have h1 : T ≤ ((⌈T⌉₊ : ℕ) : ℝ) := Nat.le_ceil T
      have h2 : ((⌈T⌉₊ : ℕ) : ℝ) ≤ (N:ℝ) := by
        dsimp only [N]
        exact_mod_cast Nat.le_succ ⌈T⌉₊
      linarith
    have hTL : T ≤ (L:ℝ) := by
      have h2 : (N:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
      linarith
    have hpt := hT (L:ℝ) hTL
    have hFL : F L = (a + c) + (a + b) * (L:ℝ)
        + a * ((L:ℝ) * Real.exp ((lam/2) * (L:ℝ))) := by
      dsimp only [F]
      rw [hpow2]
      ring
    have hRL : (2:ℝ)^(ρ*(L:ℝ)) = Real.exp (lam * (L:ℝ)) := hpow (L:ℝ)
    rw [hFL, hRL]
    linarith

end Work.KMTAreas.A7
