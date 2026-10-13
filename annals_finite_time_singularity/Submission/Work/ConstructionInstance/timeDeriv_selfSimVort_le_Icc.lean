import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.ConstructionInstance.Reduced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The `∂ₜ` box of the constructed vorticity, in the `Icc`-normalised form.**

`bddDt_selfSimVort` gives `λ̄(t)²·‖∂ₜω(y,t)‖ ≤ K·(20p + Cg + Cg')` on `preWindow T`.  On the
initial strip `[0,S]` one has `λ̄(t) ≥ m > 0` (`hmle`), hence `m² ≤ λ̄(t)²`, and dividing the box
by `λ̄(t)²` and comparing the resulting reciprocal factors gives the stated uniform bound
`‖∂ₜω(y,t)‖ ≤ K·(20p + Cg + Cg')/m²` for every `t ∈ [0,S]`. -/
theorem timeDeriv_selfSimVort_le_Icc {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    {Cg Cg' K : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => profile p g z' θ) (Work.Spaces.pz (profile p g) z θ) z)
    {L : ℝ} {lam : ℝ → ℝ} {T S m : ℝ} (hK : 0 ≤ K)
    (hlam : ∀ t ∈ preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t)
    (hlamd : ∀ t ∈ preWindow T, |deriv lam t| ≤ K)
    (hm : 0 < m) (hsub : Set.Icc (0 : ℝ) S ⊆ preWindow T)
    (hmle : ∀ t ∈ Set.Icc (0 : ℝ) S, m ≤ lam t)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S) (y : R3) :
    ‖FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t‖
      ≤ K * (20 * p + Cg + Cg') / m ^ 2 := by
  have htT : t ∈ preWindow T := hsub ht
  have hbox : (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t‖
      ≤ K * (20 * p + Cg + Cg') :=
    bddDt_selfSimVort hp hp1 hgbdd hg2 hgdiff hK hlam hlamdif hlamd htT y
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgbdd 0 0 le_rfl hI0)
  have hCg' : 0 ≤ Cg' := by simpa using hg2 0 0 le_rfl hI0
  have hsum : 0 ≤ 20 * p + Cg + Cg' := by linarith
  have hmlt : m ≤ lam t := hmle t ht
  have hlt : 0 < lam t := lt_of_lt_of_le hm hmlt
  have hlt2 : 0 < (lam t) ^ 2 := by positivity
  have hm2 : 0 < m ^ 2 := by positivity
  have hsq : m ^ 2 ≤ (lam t) ^ 2 := by nlinarith [hm.le, hmlt]
  have hKh : 0 ≤ K * (20 * p + Cg + Cg') := mul_nonneg hK hsum
  calc ‖FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t‖
      = (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t‖
          / (lam t) ^ 2 :=
        (mul_div_cancel_left₀ _ (ne_of_gt hlt2)).symm
    _ ≤ K * (20 * p + Cg + Cg') / (lam t) ^ 2 :=
        div_le_div_of_nonneg_right hbox hlt2.le
    _ ≤ K * (20 * p + Cg + Cg') / m ^ 2 :=
        div_le_div_of_nonneg_left hKh hm2 hsq

end Work.ConstructionInstance
