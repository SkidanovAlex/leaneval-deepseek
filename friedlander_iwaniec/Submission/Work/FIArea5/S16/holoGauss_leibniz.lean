import Mathlib

namespace Work.FIArea5.S16

/-- Iterated derivatives commute with the left shift `s ↦ a + s`: the `n`-th derivative of
`t ↦ f (a + t)` at `t` is the `n`-th derivative of `f` at `a + t`. -/
theorem iteratedDeriv_comp_const_add_apply (n : ℕ) (f : ℂ → ℂ) (a t : ℂ) :
    iteratedDeriv n (fun s : ℂ => f (a + s)) t = iteratedDeriv n f (a + t) :=
  congr_fun (iteratedDeriv_comp_const_add n f a) t

/-- Chain rule for the rotated shift `s ↦ b + I * s` (weighted by the Cauchy–Riemann
factor `I`): the `n`-th derivative of `t ↦ f (b + I * t)` at `t` is
`I ^ n` times the `n`-th derivative of `f` at `b + I * t`. -/
theorem iteratedDeriv_comp_const_I_apply (n : ℕ) (f : ℂ → ℂ) (b : ℂ)
    (h : ContDiff ℂ (n : ℕ∞) f) (t : ℂ) :
    iteratedDeriv n (fun s : ℂ => f (b + Complex.I * s)) t
      = Complex.I ^ n * iteratedDeriv n f (b + Complex.I * t) := by
  have hg : ContDiff ℂ (n : ℕ∞) (fun y : ℂ => f (b + y)) := h.comp (by fun_prop)
  have key := congr_fun (iteratedDeriv_comp_const_mul (𝕜 := ℂ) hg Complex.I) t
  have key2 := congr_fun (iteratedDeriv_comp_const_add n f b) (Complex.I * t)
  rw [show (fun s : ℂ => f (b + Complex.I * s))
        = (fun x => (fun y => f (b + y)) (Complex.I * x)) from rfl, key, key2]

/-- **Leibniz rule for the holomorphic Gaussian product.**  For a smooth (complex-analytic)
`W : ℂ → ℂ`, the `m`-th derivative at `0` of `t ↦ W (a + t) · W (b + I t)` is the Leibniz
sum `∑_l C(m,l) · I^l · W^{(m-l)}(a) · W^{(l)}(b)` (the factor `I^l` coming from the
Cauchy–Riemann chain rule for the second factor). -/
theorem holoGauss_leibniz {W : ℂ → ℂ} (hW : ContDiff ℂ (⊤ : ℕ∞) W) (m : ℕ) (a b : ℂ) :
    iteratedDeriv m (fun t : ℂ => W (a + t) * W (b + Complex.I * t)) 0
      = ∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * Complex.I ^ l *
          iteratedDeriv (m - l) W a * iteratedDeriv l W b := by
  have hWn : ContDiff ℂ (m : ℕ∞) W := hW.of_le (by exact_mod_cast le_top)
  have hWa : ContDiff ℂ (m : ℕ∞) (fun t : ℂ => W (a + t)) := hWn.comp (by fun_prop)
  have hWb : ContDiff ℂ (m : ℕ∞) (fun t : ℂ => W (b + Complex.I * t)) :=
    hWn.comp (by fun_prop)
  rw [show (fun t : ℂ => W (a + t) * W (b + Complex.I * t))
        = (fun t : ℂ => W (b + Complex.I * t)) * (fun t : ℂ => W (a + t)) from by
      funext t; exact mul_comm _ _]
  rw [iteratedDeriv_mul hWb.contDiffAt hWa.contDiffAt]
  apply Finset.sum_congr rfl
  intro l hl
  have hWl : ContDiff ℂ (l : ℕ∞) W :=
    hWn.of_le (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hl))
  rw [iteratedDeriv_comp_const_I_apply l W b hWl 0,
    iteratedDeriv_comp_const_add_apply (m - l) W a 0]
  simp only [mul_zero, add_zero]
  ring_nf

end Work.FIArea5.S16
