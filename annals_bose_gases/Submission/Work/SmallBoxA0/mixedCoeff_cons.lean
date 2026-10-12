import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxA0.MixedModeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

lemma mixedCoeff_cons {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (b : Bool) (ε : Fin n → Bool) (k0 : ℕ)
    (k : Fin n → ℕ) (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Continuous F) :
    (∫ x in Commons.Analysis.Fourier.boxSet (n + 1) ℓ, F x * ∏ i : Fin (n + 1),
        Work.SmallBoxA0.mixedMode ℓ ((Fin.cons b ε : Fin (n + 1) → Bool) i)
          ((Fin.cons k0 k : Fin (n + 1) → ℕ) i) (x i))
      = ∫ rest in Commons.Analysis.Fourier.boxSet n ℓ,
          (∫ a in (-(ℓ / 2))..(ℓ / 2), F (Fin.cons a rest) * Work.SmallBoxA0.mixedMode ℓ b k0 a)
            * ∏ i : Fin n, Work.SmallBoxA0.mixedMode ℓ (ε i) (k i) (rest i) := by
  have hcont : Continuous (fun x : Fin (n+1) → ℝ => F x * ∏ i : Fin (n+1),
        mixedMode ℓ ((Fin.cons b ε : Fin (n+1) → Bool) i)
          ((Fin.cons k0 k : Fin (n+1) → ℕ) i) (x i)) := by
    apply Continuous.mul hF
    apply continuous_finsetProd
    intro i _
    unfold Work.SmallBoxA0.mixedMode
    split <;> fun_prop
  have hLHS : (∫ x in Commons.Analysis.Fourier.boxSet (n + 1) ℓ, F x * ∏ i : Fin (n + 1),
        mixedMode ℓ ((Fin.cons b ε : Fin (n + 1) → Bool) i)
          ((Fin.cons k0 k : Fin (n + 1) → ℕ) i) (x i))
      = ∫ rest in Commons.Analysis.Fourier.boxSet n ℓ,
          (∫ a in Commons.Analysis.Fourier.boxB ℓ, F (Fin.cons a rest) * mixedMode ℓ b k0 a)
            * ∏ i : Fin n, mixedMode ℓ (ε i) (k i) (rest i) := by
    rw [Commons.Analysis.Fourier.setIntegral_boxSet_succ_swap n ℓ _ hcont]
    apply MeasureTheory.setIntegral_congr_fun (Commons.Analysis.Fourier.measurableSet_boxSet n ℓ)
    intro rest _
    beta_reduce
    have hprod : ∀ a : ℝ, (∏ i : Fin (n+1), mixedMode ℓ ((Fin.cons b ε : Fin (n+1) → Bool) i)
            ((Fin.cons k0 k : Fin (n+1) → ℕ) i) ((Fin.cons a rest : Fin (n+1) → ℝ) i))
        = mixedMode ℓ b k0 a * ∏ i : Fin n, mixedMode ℓ (ε i) (k i) (rest i) := by
      intro a
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    rw [MeasureTheory.setIntegral_congr_fun (Commons.Analysis.Fourier.measurableSet_boxB ℓ)
          (fun a _ => by rw [hprod a])]
    rw [← MeasureTheory.integral_mul_const]
    apply MeasureTheory.setIntegral_congr_fun (Commons.Analysis.Fourier.measurableSet_boxB ℓ)
    intro a _
    ring
  rw [hLHS]
  apply MeasureTheory.setIntegral_congr_fun (Commons.Analysis.Fourier.measurableSet_boxSet n ℓ)
  intro rest _
  beta_reduce
  rw [Commons.Analysis.Fourier.setIntegral_boxB_eq_interval hℓ]

end Work.SmallBoxA0
