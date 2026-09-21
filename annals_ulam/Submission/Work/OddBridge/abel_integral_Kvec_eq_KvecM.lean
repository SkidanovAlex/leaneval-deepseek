import Mathlib
import Submission.Work.OddBridge.Defs

namespace Work.OddBridge

/-- The Abel integral of `Kvec` equals the Abel integral of `KvecM`: the two kernels agree at
every `σ` with `s < σ ≤ 1`, and at `σ ≤ s` the weight `(σ - s)^{-1/2}` vanishes, so the two
integrands `Kvec … i / √(σ - s)` and `KvecM … i / √(σ - s)` agree on all of `[s,1]`. -/
theorem abel_integral_Kvec_eq_KvecM (n : ℕ) {h x y : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hae : ∀ s σ : ℝ, a ≤ s → s < σ → σ ≤ 1 →
      Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ))
    {s : ℝ} (hs : a ≤ s) (hs1 : s ≤ 1) :
    (∫ σ in s..1, (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0
        / Real.sqrt (σ - s))
      = (∫ σ in s..1, (Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0
        / Real.sqrt (σ - s)) ∧
    (∫ σ in s..1, (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1
        / Real.sqrt (σ - s))
      = (∫ σ in s..1, (Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1
        / Real.sqrt (σ - s)) := by
  have key : ∀ i : Fin 2, ∀ σ ∈ Set.uIcc s 1,
      (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i / Real.sqrt (σ - s)
      = (Work.OddBridge.KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i
        / Real.sqrt (σ - s) := by
    intro i σ hσ
    rw [Set.uIcc_of_le hs1] at hσ
    rcases le_or_gt σ s with h | h
    · have h0 : σ - s ≤ 0 := by linarith
      rw [Real.sqrt_eq_zero_of_nonpos h0, div_zero, div_zero]
    · have h1 : σ ≤ 1 := hσ.2
      rw [← hae s σ hs h h1]
  exact ⟨intervalIntegral.integral_congr (key 0), intervalIntegral.integral_congr (key 1)⟩

end Work.OddBridge
