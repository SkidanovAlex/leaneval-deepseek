import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs
import Submission.Work.LinnikAreas.Density4.thetaDiag_sum_bounds
import Submission.Work.LinnikAreas.Density4.thetaDiag_h_one_add_integral_le

/-!
# The full majorant sum is bounded by `Γ(σ) A^σ`

For `0 < σ ≤ 1` and `A > 0` the majorant `tdH σ A n = n^{σ-1} e^{-n/A}` satisfies

  `∑_{2 ≤ n ≤ N} n^{σ-1} e^{-n/A} ≤ Γ(σ) A^σ`,

with no restriction on `A` (in particular no `A ≥ 1`), and for every `N : ℕ`.

The proof is the integral test.  Set `h t = t^{σ-1} e^{-t/A}`.  Since `σ ≤ 1` (so `σ - 1 ≤ 0` and
`t ↦ t^{σ-1}` is antitone on `(0,∞)`) and the exponential is antitone, `h` is antitone on `[1,∞)`,
hence (Mathlib's `AntitoneOn.sum_Ico_le_integral`)

  `∑_{1 ≤ n < N} h (n+1) = ∑_{2 ≤ n ≤ N} h n ≤ ∫_{(1,∞)} h ≤ ∫_{(0,∞)} h`,

the last inequality because `h ≥ 0` on `(0,∞)`.  The Gamma integral
(`thetaDiag_integral_Ioi`) evaluates the last integral as `A^σ Γ(σ)` for every `A > 0`.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- **The majorant sum is bounded by `Γ(σ) A^σ`** (for all `A > 0`, all `N`).

This is the "conclusion (I)" of the diagonal evaluation: the whole tail
`∑_{n≥2} n^{σ-1} e^{-n/A}` is already dominated by the full Gamma integral
`∫₀^∞ t^{σ-1} e^{-t/A} dt = Γ(σ) A^σ`. -/
theorem tdH_sum_le_Gamma (σ A : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 0 < A) (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, Work.LinnikAreas.Density4.tdH σ A n) ≤ Real.Gamma σ * A ^ σ := by
  set f : ℝ → ℝ := fun t => t^(σ-1) * Real.exp (-t/A) with hf
  -- `f` is the integrand `t^{σ-1} e^{-t/A}`, and `f n = tdH σ A n` for `n : ℕ`.
  have hanti : AntitoneOn f (Ici ((1:ℕ):ℝ)) := by
    rw [hf]; simpa using thetaDiag_h_antitone σ A hσ1 hA
  have hint1 : IntegrableOn f (Ioi ((1:ℕ):ℝ)) := by
    rw [hf]; simpa using thetaDiag_h_integrableOn σ A hσ1 hA
  have hnonneg1 : ∀ t ∈ Ioi ((1:ℕ):ℝ), 0 ≤ f t := by
    intro t ht
    rw [hf]
    exact mul_nonneg (Real.rpow_nonneg (by linarith [mem_Ioi.mp ht]) _) (Real.exp_pos _).le
  -- integrability at `0` as well, so that `∫_{(1,∞)} ≤ ∫_{(0,∞)}`
  have hint0 : IntegrableOn f (Ioi (0:ℝ)) := by
    rw [hf]
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ-1) (b := 1/A)
      (by linarith) one_pos (by positivity)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    rw [show -(1/A) * x = -x/A by ring]
  have hnonneg0 : ∀ t ∈ Ioi (0:ℝ), 0 ≤ f t := by
    intro t ht
    rw [hf]
    exact mul_nonneg (Real.rpow_nonneg (by linarith [mem_Ioi.mp ht]) _) (Real.exp_pos _).le
  -- the integral test on `[1, N]`
  have hmono : AntitoneOn f (Icc ((1:ℕ):ℝ) (N:ℝ)) := hanti.mono (fun x hx => hx.1)
  have hsum : (∑ n ∈ Finset.Ico 1 N, f ↑(n+1)) ≤ ∫ x in Ioi ((1:ℕ):ℝ), f x :=
    AntitoneOn.sum_Ico_le_integral hmono hint1 hnonneg1
  -- `∑_{n ∈ Icc 2 N} f n = ∑_{k ∈ Ico 1 N} f (k+1)`
  have hreindex : (∑ n ∈ Finset.Icc 2 N, f (n:ℝ)) = ∑ n ∈ Finset.Ico 1 N, f ↑(n+1) := by
    rw [show Finset.Icc 2 N = Finset.Ico 2 (N+1) from rfl,
      ← Finset.sum_Ico_add' (fun n : ℕ => f (n:ℝ)) 1 N 1]
  have hle : (∑ n ∈ Finset.Icc 2 N, f (n:ℝ)) ≤ ∫ x in Ioi (0:ℝ), f x := by
    rw [hreindex]
    refine le_trans hsum (setIntegral_mono_set hint0 ?_ ?_)
    · exact ae_restrict_of_forall_mem measurableSet_Ioi hnonneg0
    · exact Filter.Eventually.of_forall
        (fun x hx => lt_trans (by norm_num : (0:ℝ) < ((1:ℕ):ℝ)) (mem_Ioi.mp hx))
  have hInt : ∫ x in Ioi (0:ℝ), f x = Real.Gamma σ * A^σ := by
    rw [hf, thetaDiag_integral_Ioi σ A hσ hA]; ring
  calc (∑ n ∈ Finset.Icc 2 N, Work.LinnikAreas.Density4.tdH σ A n)
      = ∑ n ∈ Finset.Icc 2 N, f (n:ℝ) := Finset.sum_congr rfl (fun n _ => by rw [tdH, hf])
    _ ≤ Real.Gamma σ * A^σ := le_trans hle (le_of_eq hInt)

end Work.LinnikAreas.Density4
