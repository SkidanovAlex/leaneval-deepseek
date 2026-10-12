import ChallengeDeps
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1.boxPIndFibreMassB1
import Submission.Work.LocRepoint.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.w2_sub_w1_pointwise` — the exact pointwise form of the `lm:w2>w1` gap

For the corpus's localised kernels

    w₁ = wSmall1Pair h M ℓ d u = wSmallPair M ℓ d u (g0 v h) ,
    w₂ = wSmallPair M ℓ d u (g2 v h) ,     g2 = g0·(1+ω₀) ,  ω₀ = Classical.choose h ,

the *difference* `w₂ − w₁` is the χ-localised, ω-weighted numerator:

    w₂(x,y) − w₁(x,y) = χ_B(x)·χ_B(y)·( (g0 v h)(x−y)·ω₀(x−y)
                                          / (convScaleSmall M (ℓd) (x−y) · convScale ℓ (x−y)) ) ,

with `χ_B = chiSmallB M ℓ d u`.  This is the unfolding that turns the `lm:w2>w1` mass
comparison into the *correlation* estimate

    ∬ χ(x)χ(y)ψ(x−y)  ≥  c·(∫ψ)·chiMass ,      ψ = (g0·ω₀)/E ,

which is what `Work.BoseFixB1.w2Mass_gap_fibre_nondegen` needs (with `E = convScaleSmall·convScale`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

/-- **Unfolding of `wSmallPair`**: the localised kernel is
`χ_B(x)·(h(x−y)/(convScaleSmall M (ℓd)(x−y)·convScale ℓ(x−y)))·χ_B(y)`. -/
theorem wSmallPair_eq_chi_mul (M : ℕ) (ℓ d : ℝ) (u x y : 𝔼3) (f : 𝔼3 → ℝ) :
    Submission.BoseGases.wSmallPair M ℓ d u f x y
      = Submission.BoseGases.chiSmallB M ℓ d u x
          * (f (x - y) / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
              * Submission.BoseGases.convScale ℓ (x - y)))
          * Submission.BoseGases.chiSmallB M ℓ d u y := by
  simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  ring

/-- `g2 = g0·(1 + ω₀)` and `g2 − g0 = g0·ω₀` pointwise (`ω₀ = Classical.choose h`). -/
theorem g2_sub_g0 {v : 𝔼3 → ℝ}
    (h : ∃ w : 𝔼3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (z : 𝔼3) :
    Submission.BoseGases.g2 v h z - Submission.BoseGases.g0 v h z
      = Submission.BoseGases.g0 v h z * Classical.choose h z := by
  simp only [Submission.BoseGases.g2, Submission.BoseGases.g0]
  ring

/-- **The pointwise `lm:w2>w1` gap.**  The difference of the two localised kernels is the
`χ_B`-sandwich of the ω-weighted numerator `g0·ω₀`, divided by the two convolution scales. -/
theorem w2_sub_w1_pointwise {v : 𝔼3 → ℝ}
    (h : ∃ w : 𝔼3 → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u x y : 𝔼3) :
    Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y
      - Submission.BoseGases.wSmall1Pair h M ℓ d u x y
      = Submission.BoseGases.chiSmallB M ℓ d u x
          * (Submission.BoseGases.g0 v h (x - y) * Classical.choose h (x - y)
              / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
                  * Submission.BoseGases.convScale ℓ (x - y)))
          * Submission.BoseGases.chiSmallB M ℓ d u y := by
  rw [wSmallPair_eq_chi_mul M ℓ d u x y (Submission.BoseGases.g2 v h),
    show Submission.BoseGases.wSmall1Pair h M ℓ d u x y
      = Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) x y from rfl,
    wSmallPair_eq_chi_mul M ℓ d u x y (Submission.BoseGases.g0 v h)]
  have hg : Submission.BoseGases.g2 v h (x - y) - Submission.BoseGases.g0 v h (x - y)
      = Submission.BoseGases.g0 v h (x - y) * Classical.choose h (x - y) :=
    g2_sub_g0 h (x - y)
  rw [← hg]
  ring

end Work.BoseFixB1
