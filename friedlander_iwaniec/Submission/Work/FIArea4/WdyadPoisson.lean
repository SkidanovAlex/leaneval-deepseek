import Mathlib
import Submission.Commons.Analysis.Fourier.poisson_step_d

/-!
# Poisson summation over a residue class

`Σ_{s ≡ c (q)} f(s) = (1/q) Σ_{k∈ℤ} f̂(k/q) e(kc/q)`
-/

namespace Work.FIArea4

open scoped FourierTransform

noncomputable section

/-- Poisson summation for the arithmetic progression `s ≡ c (mod q)`. -/
theorem poisson_residue (F : ℝ → ℂ) (hc : Continuous F) {b : ℝ} (hb : 1 < b)
    (hF : F =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (hF' : 𝓕 F =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (q : ℕ) (hq : 0 < q) (c : ℝ) :
    (∑' m : ℤ, F (c + ((m * (q:ℤ) : ℤ) : ℝ)))
      = (1 / (q:ℝ)) * ∑' k : ℤ, 𝓕 F ((k:ℝ)/(q:ℝ)) * Complex.exp (2*Real.pi*Complex.I*c*(k:ℝ)/(q:ℝ)) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have h := Commons.Analysis.Fourier.poisson_step_d F hc hb hF hF' (q:ℝ) hqpos c
  -- h : ∑' m, F (c + ↑m * ↑q) = (1/↑q) * ∑' k, 𝓕F (↑k/↑q) * exp(2πI c k/q)
  have h2 : (fun m : ℤ => F (c + ((m * (q:ℤ) : ℤ) : ℝ))) = (fun m : ℤ => F (c + (m:ℝ) * (q:ℝ))) := by
    funext m; congr 1; push_cast; ring
  rw [h2, h]
  congr 1

end

end Work.FIArea4
