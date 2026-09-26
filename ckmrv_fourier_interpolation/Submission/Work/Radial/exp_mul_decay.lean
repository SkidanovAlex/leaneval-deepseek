import Mathlib

/-!
# Multiplying a rapidly decaying smooth function by the Gaussian weight

`Work.Radial.exp_mul_decay` is a closure property of the one-sided rapidly decaying
class used in the CKMRV Fourier interpolation argument: if all one-sided iterated
derivatives of `Ξ : ℝ → ℂ` decay faster than every polynomial against the weight
`t ↦ exp (-π y t)` (`y > 0`), then the same is true of the product
`s ↦ exp (-π y s) * Ξ s`, with a threshold uniform in the order `j ≤ J`.

The proof is the binomial (Leibniz) expansion of the `j`-th derivative of the product
together with the exact value of the iterated derivatives of the Gaussian factor,
`(d/ds)^n exp (-c s) = (-c)^n exp (-c s)`.
-/

namespace Work.Radial

/-- `HasDerivAt` for the Gaussian factor `s ↦ exp (-(c * s))`. -/
lemma exp_neg_mul_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(c * s))) (Real.exp (-(c * t)) * (-c)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (-c) * s) (-c) t := by
    simpa using (hasDerivAt_id t).const_mul (-c)
  have h2 := h1.exp
  simpa [neg_mul] using h2

/-- The `n`-th one-sided iterated derivative of `s ↦ exp (-(c * s))` on `[0, ∞)`. -/
lemma iteratedDerivWithin_exp_neg_mul (c : ℝ) (n : ℕ) :
    Set.EqOn (iteratedDerivWithin n (fun s : ℝ => Real.exp (-(c * s))) (Set.Ici 0))
      (fun s : ℝ => (-c) ^ n * Real.exp (-(c * s))) (Set.Ici 0) := by
  induction n with
  | zero => intro t ht; simp [iteratedDerivWithin_zero]
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun y hy => ih hy) (ih ht)]
    have hd : HasDerivWithinAt (fun s : ℝ => (-c) ^ n * Real.exp (-(c * s)))
        ((-c) ^ n * (Real.exp (-(c * t)) * (-c))) (Set.Ici 0) t :=
      ((exp_neg_mul_hasDerivAt c t).const_mul ((-c) ^ n)).hasDerivWithinAt
    rw [hd.derivWithin ((uniqueDiffOn_Ici 0) t ht), pow_succ]
    ring

/-- Norm form of `iteratedDerivWithin_exp_neg_mul`, for `c ≥ 0` and `t ≥ 0`. -/
lemma norm_iteratedDerivWithin_exp_neg_mul (c : ℝ) (hc : 0 ≤ c) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖iteratedDerivWithin n (fun s : ℝ => Real.exp (-(c * s))) (Set.Ici 0) t‖
      = c ^ n * Real.exp (-(c * t)) := by
  rw [iteratedDerivWithin_exp_neg_mul c n ht]
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_nonneg hc, abs_of_pos (Real.exp_pos _)]

theorem exp_mul_decay (y : ℝ) (hy : 0 < y) (Ξ : ℝ → ℂ)
    (hsm : ContDiffOn ℝ ⊤ Ξ (Set.Ici 0))
    (hdec : ∀ j K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(Real.pi * y * t)) *
        ‖iteratedDerivWithin j Ξ (Set.Ici 0) t‖ ≤ ε)
    (J K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ j : ℕ, j ≤ J →
      (1 + t) ^ K * ‖iteratedDerivWithin j
        (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * Ξ s) (Set.Ici 0) t‖ ≤ ε := by
  let c : ℝ := Real.pi * y
  have hcpos : 0 < c := by dsimp only [c]; positivity
  have hcle : 0 ≤ c := hcpos.le
  have hBpos : 0 < (1 + c) ^ J := by positivity
  have hstep : ∀ m ∈ Finset.range (J + 1), ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(c * t)) * ‖iteratedDerivWithin m Ξ (Set.Ici 0) t‖
        ≤ ε / (1 + c) ^ J := by
    intro m hm
    exact hdec m K (ε / (1 + c) ^ J) (div_pos hε hBpos)
  have hkey : ∀ s : Finset ℕ, (∀ m ∈ s, ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(c * t)) * ‖iteratedDerivWithin m Ξ (Set.Ici 0) t‖
        ≤ ε / (1 + c) ^ J) →
      ∃ T : ℝ, ∀ m ∈ s, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(c * t)) * ‖iteratedDerivWithin m Ξ (Set.Ici 0) t‖
        ≤ ε / (1 + c) ^ J := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert a s ha ih =>
      intro h
      obtain ⟨Ta, hTa⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨Ts, hTs⟩ := ih (fun m hm => h m (Finset.mem_insert_of_mem hm))
      refine ⟨max Ta Ts, fun m hm t ht => ?_⟩
      rcases Finset.mem_insert.mp hm with rfl | hm'
      · exact hTa t (le_trans (le_max_left _ _) ht)
      · exact hTs m hm' t (le_trans (le_max_right _ _) ht)
  obtain ⟨T0, hT0⟩ := hkey (Finset.range (J + 1)) hstep
  refine ⟨max T0 1, fun t ht j hj => ?_⟩
  have htT0 : T0 ≤ t := le_trans (le_max_left T0 1) ht
  have ht0 : 0 ≤ t := by linarith [le_trans (le_max_right T0 1) ht]
  have h1t : 0 < 1 + t := by linarith
  have hW : ContDiffOn ℝ ⊤ (fun s : ℝ => Real.exp (-(c * s))) (Set.Ici 0) := by fun_prop
  have hmono : (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * Ξ s)
      = fun s : ℝ => Real.exp (-(c * s)) • Ξ s := by
    funext s
    rw [RCLike.real_smul_eq_coe_mul]
    rfl
  rw [hmono]
  have hsum_le : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c ^ i ≤ (1 + c) ^ J := by
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c ^ i
        = (c + 1) ^ j := by
          rw [add_pow c 1 j]
          apply Finset.sum_congr rfl
          intro i hi
          rw [one_pow, mul_one]
          ring
      _ = (1 + c) ^ j := by ring
      _ ≤ (1 + c) ^ J := pow_le_pow_right₀ (by linarith) hj
  calc (1 + t) ^ K * ‖iteratedDerivWithin j (fun s : ℝ => Real.exp (-(c * s)) • Ξ s)
          (Set.Ici 0) t‖
      = (1 + t) ^ K * ‖iteratedFDerivWithin ℝ j (fun s : ℝ => Real.exp (-(c * s)) • Ξ s)
          (Set.Ici 0) t‖ := by
        rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    _ ≤ (1 + t) ^ K * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun s : ℝ => Real.exp (-(c * s))) (Set.Ici 0) t‖ *
          ‖iteratedFDerivWithin ℝ (j - i) Ξ (Set.Ici 0) t‖ :=
        mul_le_mul_of_nonneg_left
          (norm_iteratedFDerivWithin_smul_le hW hsm (uniqueDiffOn_Ici 0) ht0 le_top)
          (pow_nonneg h1t.le K)
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c ^ i *
          ((1 + t) ^ K * Real.exp (-(c * t)) * ‖iteratedDerivWithin (j - i) Ξ (Set.Ici 0) t‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin
              (f := fun s : ℝ => Real.exp (-(c * s))),
            norm_iteratedDerivWithin_exp_neg_mul c hcle i ht0,
            norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin (f := Ξ)]
        ring
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c ^ i * (ε / (1 + c) ^ J) := by
        apply Finset.sum_le_sum
        intro i hi
        have hji : j - i ≤ J := le_trans (Nat.sub_le j i) hj
        have hmem : j - i ∈ Finset.range (J + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hji)
        have hnn : 0 ≤ (j.choose i : ℝ) * c ^ i := by positivity
        exact mul_le_mul_of_nonneg_left (hT0 (j - i) hmem t htT0) hnn
    _ = (ε / (1 + c) ^ J) * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ ≤ (ε / (1 + c) ^ J) * (1 + c) ^ J := by
        exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = ε := by rw [div_mul_cancel₀ ε (ne_of_gt hBpos)]

end Work.Radial
