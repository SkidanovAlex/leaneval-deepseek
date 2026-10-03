import Mathlib

namespace Work.Pert.Ksub2

/-- Shadowing defect estimate: if `p` is an `f₀`-pseudo-orbit that is an actual `f₀`-orbit
(`hrec`), `f₀` is `L`-Lipschitz on the `R`-balls around the orbit (`hLip`), `f` is `ε`-close
to `f₀` there (`hclose`), and the seed and the accumulated error are small (`hseed`, `hsmall`),
then both the `f`- and `f₀`-orbits of `a` stay within `R` of `p`, and the defect between the
two orbits at time `n` is at most `ε * n * L ^ n`. -/
theorem shadow_defect_le {f₀ f : ℂ → ℂ} {p : ℕ → ℂ} {a : ℂ} {n : ℕ} {L ε R : ℝ}
    (hR : 0 < R) (hε : 0 ≤ ε) (hL : 1 ≤ L)
    (hrec : ∀ j : ℕ, j < n → f₀ (p j) = p (j + 1))
    (hLip : ∀ j : ℕ, j ≤ n → ∀ x y : ℂ, ‖x - p j‖ ≤ R → ‖y - p j‖ ≤ R →
      ‖f₀ x - f₀ y‖ ≤ L * ‖x - y‖)
    (hclose : ∀ j : ℕ, j ≤ n → ∀ x : ℂ, ‖x - p j‖ ≤ R → ‖f x - f₀ x‖ ≤ ε)
    (hseed : L ^ n * ‖a - p 0‖ ≤ R / 2)
    (hsmall : ε * (n : ℝ) * L ^ n ≤ R / 2) :
    (∀ j : ℕ, j ≤ n → ‖f^[j] a - p j‖ ≤ R ∧ ‖f₀^[j] a - p j‖ ≤ R) ∧
      ‖f^[n] a - f₀^[n] a‖ ≤ ε * (n : ℝ) * L ^ n := by
  have hL0 : (0:ℝ) ≤ L := le_trans zero_le_one hL
  -- Simultaneous induction: trapping of both orbits, the Lipschitz growth of the `f₀`-orbit,
  -- and the defect bound `‖fᵏa - f₀ᵏa‖ ≤ ε·k·Lᵏ`.
  have key : ∀ j : ℕ, j ≤ n →
      ‖f^[j] a - p j‖ ≤ R ∧ ‖f₀^[j] a - p j‖ ≤ R ∧
      ‖f₀^[j] a - p j‖ ≤ L^j * ‖a - p 0‖ ∧
      ‖f^[j] a - f₀^[j] a‖ ≤ ε * (j:ℝ) * L^j := by
    intro j
    induction j with
    | zero =>
      intro _
      have hseed0 : ‖a - p 0‖ ≤ R / 2 := by
        have h1 : (1:ℝ) ≤ L^n := one_le_pow₀ hL
        have h2 : (1:ℝ) * ‖a - p 0‖ ≤ L^n * ‖a - p 0‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        rw [one_mul] at h2
        linarith
      have hR2 : R / 2 ≤ R := by linarith
      refine ⟨le_trans hseed0 hR2, le_trans hseed0 hR2, ?_, ?_⟩
      · simp
      · simp
    | succ k ih =>
      intro hk
      have hk_le : k ≤ n := by omega
      have hk_lt : k < n := by omega
      obtain ⟨hf1, hf2, hf3, hf4⟩ := ih hk_le
      have hpw : L^(k+1) ≤ L^n := pow_le_pow_right₀ hL hk
      have hf0R : L^(k+1) * ‖a - p 0‖ ≤ R / 2 := by
        have := mul_le_mul_of_nonneg_right hpw (norm_nonneg (a - p 0))
        linarith [this, hseed]
      -- `f₀`-distance grows by the Lipschitz factor.
      have hA : ‖f₀^[k+1] a - p (k+1)‖ ≤ L^(k+1) * ‖a - p 0‖ := by
        rw [Function.iterate_succ_apply', ← hrec k hk_lt]
        calc ‖f₀ (f₀^[k] a) - f₀ (p k)‖
            ≤ L * ‖f₀^[k] a - p k‖ :=
              hLip k hk_le (f₀^[k] a) (p k) hf2 (by rw [sub_self, norm_zero]; exact hR.le)
          _ ≤ L * (L^k * ‖a - p 0‖) := mul_le_mul_of_nonneg_left hf3 hL0
          _ = L^(k+1) * ‖a - p 0‖ := by rw [pow_succ]; ring
      -- Defect recurrence `e_{k+1} ≤ ε + L·e_k`, solved by `e_k ≤ ε·k·Lᵏ`.
      have hB : ‖f^[k+1] a - f₀^[k+1] a‖ ≤ ε * ((k+1:ℕ):ℝ) * L^(k+1) := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have htri := norm_sub_le_norm_sub_add_norm_sub (f (f^[k] a)) (f₀ (f^[k] a)) (f₀ (f₀^[k] a))
        have hc : ‖f (f^[k] a) - f₀ (f^[k] a)‖ ≤ ε := hclose k hk_le (f^[k] a) hf1
        have hl : ‖f₀ (f^[k] a) - f₀ (f₀^[k] a)‖ ≤ L * ‖f^[k] a - f₀^[k] a‖ :=
          hLip k hk_le (f^[k] a) (f₀^[k] a) hf1 hf2
        have hl2 : L * ‖f^[k] a - f₀^[k] a‖ ≤ L * (ε * (k:ℝ) * L^k) :=
          mul_le_mul_of_nonneg_left hf4 hL0
        have hX1 : (1:ℝ) ≤ L^k * L := by rw [← pow_succ]; exact one_le_pow₀ hL
        have hcast : ((k+1:ℕ):ℝ) = (k:ℝ) + 1 := by push_cast; ring
        have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        have hk0' : (0:ℝ) ≤ ε * (k:ℝ) := mul_nonneg hε hk0
        have harith : ε + L * (ε * (k:ℝ) * L^k) ≤ ε * ((k+1:ℕ):ℝ) * L^(k+1) := by
          rw [hcast, pow_succ]
          nlinarith [hε, hX1, hk0, hk0']
        linarith [htri, hc, hl, hl2, harith]
      -- Trapping of the perturbed orbit.
      have hC : ‖f^[k+1] a - p (k+1)‖ ≤ R := by
        have htri := norm_sub_le_norm_sub_add_norm_sub (f^[k+1] a) (f₀^[k+1] a) (p (k+1))
        have hstep : ε * ((k+1:ℕ):ℝ) * L^(k+1) ≤ R / 2 := by
          have hkn : ((k+1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hk
          have h1 : ε * ((k+1:ℕ):ℝ) ≤ ε * (n:ℝ) := mul_le_mul_of_nonneg_left hkn hε
          have h2 : ε * ((k+1:ℕ):ℝ) * L^(k+1) ≤ ε * (n:ℝ) * L^n :=
            mul_le_mul h1 hpw (pow_nonneg hL0 _) (mul_nonneg hε (Nat.cast_nonneg n))
          linarith [h2, hsmall]
        linarith [htri, hB, hA, hstep, hf0R]
      exact ⟨hC, by linarith [hA, hf0R, hR], hA, hB⟩
  have hPn := key n le_rfl
  exact ⟨fun j hj => ⟨(key j hj).1, (key j hj).2.1⟩, hPn.2.2.2⟩

end Work.Pert.Ksub2
