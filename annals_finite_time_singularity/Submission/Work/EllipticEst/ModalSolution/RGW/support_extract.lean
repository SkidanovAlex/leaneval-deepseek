import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.EllipticEst.ModalSolution.RGW

/-- For a compactly supported `C²` function `ψ` whose topological support lies in the open
half-line `(0, ∞)`, one can find a strictly positive interval `(a, b)` containing the
topological support of `ψ` and on whose complement `ψ`, `deriv ψ` and `deriv (deriv ψ)`
all vanish.

The two vanishing properties on the complement of `(a,b)` are cheap consequences of Tychonoff's
lemma: outside `tsupport ψ` the function `ψ` is eventually `0`, hence so are its derivatives (and
`tsupport (deriv ψ) ⊆ tsupport ψ`).  The genuine content is the existence of the interval, which
uses compactness of `tsupport ψ` (extreme value theorem for the `min`, and `bddAbove`) together
with the positivity of every point of `tsupport ψ`. -/
theorem support_extract (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport ψ ⊆ Set.Ioo a b ∧
      ∀ z : ℝ, z ∉ Set.Ioo a b → ψ z = 0 ∧ deriv ψ z = 0 ∧ deriv (deriv ψ) z = 0 := by
  have hab : ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport ψ ⊆ Set.Ioo a b := by
    rcases Set.eq_empty_or_nonempty (tsupport ψ) with hem | hne
    · exact ⟨1, 2, by norm_num, by norm_num, by simp [hem]⟩
    · -- nonempty compact set, all of whose points are `> 0`
      obtain ⟨m, hmK, hm⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
      obtain ⟨M, hMK, hM⟩ := hc.exists_isMaxOn hne continuous_id.continuousOn
      have hmpos : 0 < m := hs hmK
      have hmM : m ≤ M := hm hMK
      refine ⟨m / 2, M + 1, by linarith, by linarith, fun y hy => ⟨?_, ?_⟩⟩
      · have h1 : m ≤ y := hm hy
        linarith
      · have h2 : y ≤ M := hM hy
        linarith
  obtain ⟨a, b, ha, hab', hsub⟩ := hab
  refine ⟨a, b, ha, hab', hsub, fun z hz => ?_⟩
  -- `z` is outside `tsupport ψ` and hence outside `tsupport (deriv ψ)`
  have hzK : z ∉ tsupport ψ := fun h => hz (hsub h)
  exact ⟨image_eq_zero_of_notMem_tsupport hzK, deriv_of_notMem_tsupport hzK,
    deriv_of_notMem_tsupport (fun h => hzK (tsupport_deriv_subset h))⟩

end Work.EllipticEst.ModalSolution.RGW
