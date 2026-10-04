import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GN.tools
import Submission.Work.Diff.STE.GN.holder2_int

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The order-`2` Hölder estimate for the Nirenberg step on the torus

`gnP m 1 = 2m`, and the target `Work.Diff.STE.GN.holder_pd_order2`

```
∫ ‖∂ᵢ f‖ ^ (2m - 2) · ‖∂ᵢ² f‖ ≤ (∫ ‖∂ᵢ f‖ ^ (2m)) ^ ((2m-2)/(2m)) · (∫ ‖∂ᵢ² f‖ ^ m) ^ (1/m)
```

is nothing but **Hölder's inequality** applied to `U := ‖∂ᵢ f‖ ^ (2m-2)` and `V := ‖∂ᵢ² f‖`
with the conjugate exponents `a := 2m/(2m-2)` and `a' := 2m/2 = m`: indeed
`1/a + 1/a' = (2m-2)/(2m) + 1/m = 1`, `U^a = ‖∂ᵢ f‖ ^ (2m)` and `V^{a'} = ‖∂ᵢ² f‖ ^ m`.

The auxiliary lemma `holder_int_two_exp` is the general shape (arbitrary continuous nonnegative
`F, G : (ι → ℝ) → ℝ`, exponent `2m`), proved from the already available Hölder inequality
`Work.Diff.STE.GN.holder2_int` on the unit cube; the target follows by unfolding
`gnP m 1 = 2 * m` and taking `F x = ‖∂ᵢ f x‖`, `G x = ‖∂ᵢ² f x‖`, both continuous because
partial derivatives of a smooth function are smooth (`contDiff_pdVec_top`).
-/

noncomputable section

namespace Work.Diff.STE.GN

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Hölder's inequality with the exponents of the second-order Nirenberg step.**

For continuous nonnegative `F, G` on the unit cube and `2 ≤ m`,

`∫ F ^ (2m - 2) * G ≤ (∫ F ^ (2m)) ^ ((2m-2)/(2m)) * (∫ G ^ m) ^ (1/m)`.

This is Hölder with conjugate exponents `2m/(2m-2)` and `m`, applied to
`F ^ (2m-2)` and `G`. -/
theorem holder_int_two_exp (m : ℕ) (hm : 2 ≤ m)
    (F G : (ι → ℝ) → ℝ) (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x) :
    (∫ x in Work.Diff.STE.unitCube (ι := ι), F x ^ (2 * (m : ℝ) - 2) * G x)
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι), F x ^ (2 * (m : ℝ)))
          ^ ((2 * (m : ℝ) - 2) / (2 * (m : ℝ)))
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), G x ^ (m : ℝ)) ^ (1 / (m : ℝ)) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hq0 : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hq2 : (0 : ℝ) < 2 * (m : ℝ) - 2 := by linarith
  -- the two conjugate exponents are `≥ 1`
  have hb1 : (1 : ℝ) ≤ (2 * (m : ℝ)) / (2 * (m : ℝ) - 2) := by
    rw [le_div_iff₀ hq2]; linarith
  have hc1 : (1 : ℝ) ≤ (2 * (m : ℝ)) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]; linarith
  have hbc : 1 / ((2 * (m : ℝ)) / (2 * (m : ℝ) - 2)) + 1 / ((2 * (m : ℝ)) / 2) = 1 := by
    field_simp
    ring
  have hFcont : Continuous (fun x => F x ^ (2 * (m : ℝ) - 2)) :=
    hF.rpow_const (fun x => Or.inr (by linarith))
  have hH := holder2_int (ι := ι) ((2 * (m : ℝ)) / (2 * (m : ℝ) - 2)) ((2 * (m : ℝ)) / 2)
    hb1 hc1 hbc (fun x => F x ^ (2 * (m : ℝ) - 2)) G hFcont hG
    (fun x => Real.rpow_nonneg (hF0 x) _) hG0
  -- the powers `(F ^ (2m-2)) ^ (2m/(2m-2)) = F ^ (2m)`
  have hpow : ∀ x : ι → ℝ,
      (F x ^ (2 * (m : ℝ) - 2)) ^ ((2 * (m : ℝ)) / (2 * (m : ℝ) - 2))
        = F x ^ (2 * (m : ℝ)) := by
    intro x
    rw [← Real.rpow_mul (hF0 x)]
    congr 1
    rw [mul_comm]
    exact div_mul_cancel₀ _ (ne_of_gt hq2)
  have hI2 : (∫ x in Work.Diff.STE.unitCube (ι := ι), G x ^ ((2 * (m : ℝ)) / 2))
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), G x ^ (m : ℝ) := by
    simp only [show (2 * (m : ℝ)) / 2 = (m : ℝ) from by ring]
  have he1 : 1 / ((2 * (m : ℝ)) / (2 * (m : ℝ) - 2)) = (2 * (m : ℝ) - 2) / (2 * (m : ℝ)) := by
    field_simp
  have he3 : 1 / ((2 * (m : ℝ)) / 2) = 1 / (m : ℝ) := by
    rw [show (2 * (m : ℝ)) / 2 = (m : ℝ) from by ring]
  calc (∫ x in Work.Diff.STE.unitCube (ι := ι), F x ^ (2 * (m : ℝ) - 2) * G x)
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (F x ^ (2 * (m : ℝ) - 2)) ^ ((2 * (m : ℝ)) / (2 * (m : ℝ) - 2)))
          ^ (1 / ((2 * (m : ℝ)) / (2 * (m : ℝ) - 2)))
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), G x ^ ((2 * (m : ℝ)) / 2))
            ^ (1 / ((2 * (m : ℝ)) / 2)) := hH
    _ = (∫ x in Work.Diff.STE.unitCube (ι := ι), F x ^ (2 * (m : ℝ)))
          ^ ((2 * (m : ℝ) - 2) / (2 * (m : ℝ)))
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), G x ^ (m : ℝ)) ^ (1 / (m : ℝ)) := by
        simp_rw [hpow]
        rw [he1, he3, hI2]

theorem holder_pd_order2 {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (hm : 2 ≤ m)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ι) :
    (∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.pd i f x‖ ^ (Work.Diff.STE.gnP m 1 - 2)
          * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i f) x‖)
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1)
          ^ ((Work.Diff.STE.gnP m 1 - 2) / Work.Diff.STE.gnP m 1)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i f) x‖ ^ (m : ℝ)) ^ (1 / (m : ℝ)) := by
  -- first and second partial derivatives of a smooth function are smooth, hence continuous
  have hcont1 : Continuous (fun x : ι → ℝ => ‖Work.Diff.STE.pd i f x‖) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i f) := by
      have h := Work.Diff.STE.contDiff_pdVec_top (k := 1) (fun _ : Fin 1 => i) f hf
      simpa [Work.Diff.STE.pdVec, Work.Diff.STE.pdList] using h
    exact h1.continuous.norm
  have hcont2 : Continuous (fun x : ι → ℝ => ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i f) x‖) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i f) := by
      have h := Work.Diff.STE.contDiff_pdVec_top (k := 1) (fun _ : Fin 1 => i) f hf
      simpa [Work.Diff.STE.pdVec, Work.Diff.STE.pdList] using h
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i (Work.Diff.STE.pd i f)) := by
      have h := Work.Diff.STE.contDiff_pdVec_top (k := 1) (fun _ : Fin 1 => i)
        (Work.Diff.STE.pd i f) h1
      simpa [Work.Diff.STE.pdVec, Work.Diff.STE.pdList] using h
    exact h2.continuous.norm
  have h := holder_int_two_exp (ι := ι) m hm (fun x => ‖Work.Diff.STE.pd i f x‖)
    (fun x => ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i f) x‖) hcont1 hcont2
    (fun x => norm_nonneg _) (fun x => norm_nonneg _)
  simpa only [Work.Diff.STE.gnP, Nat.cast_one, div_one] using h

end Work.Diff.STE.GN
