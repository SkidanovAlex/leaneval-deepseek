import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

/-- A `C^∞` function with compact support on a normed space has **uniformly bounded
iterated derivatives** of every order: `f` vanishes outside `tsupport f`, each
`iteratedFDeriv ℝ k f` is continuous (as `f` is `C^k`) and its support is contained in
`tsupport f`, so it is bounded there by compactness. -/
theorem uniform_idfb_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ∀ k : ℕ, ContDiff ℝ k f) (hcs : HasCompactSupport f) :
    ∃ G : ℕ → ℝ, (∀ k, 0 ≤ G k) ∧ ∀ k (x : E), ‖iteratedFDeriv ℝ k f x‖ ≤ G k := by
  have hK : IsCompact (tsupport f) := hcs.isCompact
  have key : ∀ k : ℕ, ∃ A : ℝ, ∀ x : E, ‖iteratedFDeriv ℝ k f x‖ ≤ A := by
    intro k
    have hcont : Continuous (iteratedFDeriv ℝ k f) :=
      ContDiff.continuous_iteratedFDeriv' (m := k) (hf k)
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max A 0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport f
    · exact le_trans (hA x hx) (le_max_left _ _)
    · have hx' : x ∉ Function.support (iteratedFDeriv ℝ k f) :=
        fun h => hx (support_iteratedFDeriv_subset k h)
      simp only [Function.mem_support, not_not] at hx'
      rw [hx', norm_zero]
      exact le_max_right _ _
  choose A hA using key
  exact ⟨fun k => max (A k) 0, fun k => le_max_right _ _, fun k x =>
    le_trans (hA k x) (le_max_left _ _)⟩

end Work.BoseFixB3.CS.Pieces
