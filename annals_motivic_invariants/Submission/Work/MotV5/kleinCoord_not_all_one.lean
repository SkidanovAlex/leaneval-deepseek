import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem kleinCoord_not_all_one (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (hsm : D.a ^ 2 - D.a * D.b - D.b ^ 2 ≠ 0) :
    ¬ ∀ i : Fin 5, Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 = 1 := by
  intro h
  have h0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.coord0_ne (Work.MotV.Kb 𝕜)
  -- All ratios equal `1` force all Klein coordinates to coincide with `κ₀`.
  have hc : ∀ i : Fin 5, Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 := by
    intro i
    have hi := h i
    rwa [div_eq_one_iff_eq h0] at hi
  -- `κ` lies on the Klein quintic, so `p₀(κ) = 0`.
  have hk := hD.klein_eq (Work.MotV.Kb 𝕜) 0
  rw [Work.MotK.kleinP_zero, Work.MotK.kleinP0] at hk
  rw [hc 2, hc 3, hc 1, hc 4] at hk
  -- The coefficients of the Pfaffians are the images of `a, b` in `Om D = K̄(E)`.
  have hAB : algebraMap 𝕜 (Work.MotV.Om D) (D.a ^ 2 - D.a * D.b - D.b ^ 2) ≠ 0 := by
    intro hh
    exact hsm (FaithfulSMul.algebraMap_injective 𝕜 (Work.MotV.Om D) (by simpa using hh))
  have hA2 : (algebraMap 𝕜 (Work.MotV.Om D) D.a) ^ 2
      - algebraMap 𝕜 (Work.MotV.Om D) D.a * algebraMap 𝕜 (Work.MotV.Om D) D.b
      - (algebraMap 𝕜 (Work.MotV.Om D) D.b) ^ 2 ≠ 0 := by
    have hmap : algebraMap 𝕜 (Work.MotV.Om D) (D.a ^ 2 - D.a * D.b - D.b ^ 2)
        = (algebraMap 𝕜 (Work.MotV.Om D) D.a) ^ 2
          - algebraMap 𝕜 (Work.MotV.Om D) D.a * algebraMap 𝕜 (Work.MotV.Om D) D.b
          - (algebraMap 𝕜 (Work.MotV.Om D) D.b) ^ 2 := by
      simp only [map_sub, map_mul, map_pow]
    rw [← hmap]
    exact hAB
  -- `p₀` at the all-equal point factors as `(a² - ab - b²) · κ₀²`.
  have key : (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) ^ 2
      * ((algebraMap 𝕜 (Work.MotV.Om D) D.a) ^ 2
        - algebraMap 𝕜 (Work.MotV.Om D) D.a * algebraMap 𝕜 (Work.MotV.Om D) D.b
        - (algebraMap 𝕜 (Work.MotV.Om D) D.b) ^ 2) = 0 := by
    linear_combination (norm := first | refl_ring1 | ring1) hk
  have hc0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 = 0 := by
    rcases mul_eq_zero.mp key with h1 | h2
    · exact (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h1
    · exact absurd h2 hA2
  exact h0 hc0

end Work.MotV5
