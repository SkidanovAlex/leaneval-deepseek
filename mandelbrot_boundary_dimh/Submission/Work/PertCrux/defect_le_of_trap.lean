import Mathlib
import Submission.Work.Pert.Ksub2.shadow_defect_le

namespace Work.PertCrux

/-- **Shadowing defect estimate with trap-only hypotheses.**
If the `f₀`-orbit of `a` is trapped in the `R/4`-balls around `p j` for `j ≤ n`, `f₀` is
`L`-Lipschitz on the `R`-balls around `p j` for `j < n`, `f` is `ε`-close to `f₀` there,
and the accumulated error `ε n L^n` is at most `R/4`, then the `f`-orbit of `a` stays within
`R` of `p` and the defect at time `n` is at most `ε n L^n`. -/
theorem defect_le_of_trap {f₀ f : ℂ → ℂ} {p : ℕ → ℂ} {a : ℂ} {n : ℕ} {L ε R : ℝ}
    (hR : 0 < R) (hε : 0 ≤ ε) (hL : 1 ≤ L)
    (hLip : ∀ j : ℕ, j < n → ∀ x y : ℂ, ‖x - p j‖ ≤ R → ‖y - p j‖ ≤ R →
      ‖f₀ x - f₀ y‖ ≤ L * ‖x - y‖)
    (hclose : ∀ j : ℕ, j < n → ∀ x : ℂ, ‖x - p j‖ ≤ R → ‖f x - f₀ x‖ ≤ ε)
    (hf0trap : ∀ j : ℕ, j ≤ n → ‖f₀^[j] a - p j‖ ≤ R / 4)
    (hsmall : ε * (n : ℝ) * L ^ n ≤ R / 4) :
    (∀ j : ℕ, j ≤ n → ‖f^[j] a - p j‖ ≤ R) ∧ ‖f^[n] a - f₀^[n] a‖ ≤ ε * (n : ℝ) * L ^ n := by
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL
  have key : ∀ j : ℕ, j ≤ n →
      ‖f^[j] a - p j‖ ≤ R ∧ ‖f^[j] a - f₀^[j] a‖ ≤ ε * (j : ℝ) * L ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · have h := hf0trap 0 (Nat.zero_le n)
        simp only [Function.iterate_zero_apply] at h ⊢
        linarith
      · simp
    | succ k ih =>
      intro hk
      have hk_le : k ≤ n := by omega
      have hk_lt : k < n := by omega
      obtain ⟨htrapk, hdefk⟩ := ih hk_le
      have hf0k : ‖f₀^[k] a - p k‖ ≤ R := le_trans (hf0trap k hk_le) (by linarith)
      have hstep : ‖f^[k + 1] a - f₀^[k + 1] a‖ ≤ ε + L * (ε * (k : ℝ) * L ^ k) := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have htri := norm_sub_le_norm_sub_add_norm_sub (f (f^[k] a)) (f₀ (f^[k] a))
          (f₀ (f₀^[k] a))
        have hc : ‖f (f^[k] a) - f₀ (f^[k] a)‖ ≤ ε := hclose k hk_lt (f^[k] a) htrapk
        have hl : ‖f₀ (f^[k] a) - f₀ (f₀^[k] a)‖ ≤ L * ‖f^[k] a - f₀^[k] a‖ :=
          hLip k hk_lt (f^[k] a) (f₀^[k] a) htrapk hf0k
        linarith [htri, hc, hl, mul_le_mul_of_nonneg_left hdefk hL0]
      have hmain : ‖f^[k + 1] a - f₀^[k + 1] a‖ ≤ ε * ((k + 1 : ℕ) : ℝ) * L ^ (k + 1) := by
        have hX1 : (1 : ℝ) ≤ L ^ k * L := by rw [← pow_succ]; exact one_le_pow₀ hL
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hk0' : (0 : ℝ) ≤ ε * (k : ℝ) := mul_nonneg hε hk0
        have harith : ε + L * (ε * (k : ℝ) * L ^ k) ≤ ε * ((k + 1 : ℕ) : ℝ) * L ^ (k + 1) := by
          rw [hcast, pow_succ]
          nlinarith [hε, hX1, hk0, hk0']
        linarith [hstep, harith]
      refine ⟨?_, hmain⟩
      have hstep2 : ε * ((k + 1 : ℕ) : ℝ) * L ^ (k + 1) ≤ ε * (n : ℝ) * L ^ n := by
        have hkn : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
        have hpw : L ^ (k + 1) ≤ L ^ n := pow_le_pow_right₀ hL hk
        have h1 : ε * ((k + 1 : ℕ) : ℝ) ≤ ε * (n : ℝ) := mul_le_mul_of_nonneg_left hkn hε
        exact mul_le_mul h1 hpw (pow_nonneg hL0 _) (mul_nonneg hε (Nat.cast_nonneg n))
      have hf0k1 : ‖f₀^[k + 1] a - p (k + 1)‖ ≤ R / 4 := hf0trap (k + 1) hk
      have htri2 := norm_sub_le_norm_sub_add_norm_sub (f^[k + 1] a) (f₀^[k + 1] a) (p (k + 1))
      linarith [htri2, hmain, hstep2, hf0k1, hsmall]
  have hPn := key n le_rfl
  exact ⟨fun j hj => (key j hj).1, hPn.2⟩

end Work.PertCrux
