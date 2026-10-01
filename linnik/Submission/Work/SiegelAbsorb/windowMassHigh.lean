import Mathlib
import Submission.Work.SiegelAbsorb.windowMassRegion
import Submission.Work.LinnikAreas.pairCountHeight_dom

namespace Work.SiegelAbsorb

open scoped Classical BigOperators

lemma windowMassHigh {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₃ H θ : ℝ} (hC₃ : 0 < C₃) (hH : 0 < H) (hθ : 0 < θ)
    (hcnt : ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₃ * Real.exp ((9 / 2) * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log (q : ℝ) ≤ H * Real.log (q : ℝ))
    (hgt : ∀ z ∈ S, θ * Real.log (q : ℝ) < Work.LinnikContract.lamOf q z.2)
    (hle : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ Real.log (q : ℝ)) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ C₃ * H ^ (3 / 2 : ℝ) * Real.exp (9 / 2)
          * Real.exp (-(2 / 5) * (θ * Real.log (q : ℝ))) / (1 - Real.exp (-(2 / 5))) := by
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hΛ : 0 < θ * Real.log (q : ℝ) := mul_pos hθ hlogq
  have hmain := windowMassRegion (q := q) hq χ₁ β₁
    (C := C₃) (H := H) (a₀ := 49/10) (c := 9/2)
    (Λ := θ * Real.log (q:ℝ)) (L := Real.log (q:ℝ))
    hC₃ hH (by norm_num) (by norm_num) (by norm_num) hΛ hcnt S hzm hexc him
    (fun z hz => le_of_lt (hgt z hz)) hle
  rw [show (9/(2:ℝ) - 49/10) = -(2/5) from by norm_num] at hmain
  exact hmain

end Work.SiegelAbsorb
