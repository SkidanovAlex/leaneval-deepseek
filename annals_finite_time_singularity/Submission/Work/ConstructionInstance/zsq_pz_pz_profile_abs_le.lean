import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- If `H` is odd in its second variable then so is `pz H`: the `z`-derivative is taken
pointwise in `z`, so it commutes with the reflection `θ ↦ -θ` (`deriv.neg`). -/
theorem pz_odd_of_odd {H : ℝ → ℝ → ℝ} (hodd : ∀ z θ : ℝ, H z (-θ) = - H z θ) :
    ∀ z θ : ℝ, Work.Spaces.pz H z (-θ) = - Work.Spaces.pz H z θ := by
  intro z θ
  have h1 : (fun z' : ℝ => H z' (-θ)) = fun z' => -(H z' θ) := by
    funext z'; exact hodd z' θ
  rw [Work.Spaces.pz, h1, Work.Spaces.pz]
  exact deriv.neg

theorem zsq_pz_pz_profile_abs_le {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ} (hg0 : ∀ z : ℝ, g z 0 = 0) {Cg'' : ℝ}
    (hgdiff2 : ∀ z θ : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz (Work.ConstructionInstance.profile p g) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile p g)) z θ) z)
    (hg3 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile p g)) z θ| ≤ Cg'') :
    ∀ z θ : ℝ, 0 < z → |θ| ≤ Real.pi / 2 →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile p g)) z θ|
        ≤ Cg'' := by
  -- the profile is odd in `θ`
  have hodd : ∀ z θ : ℝ, profile p g z (-θ) = - profile p g z θ := profile_odd hp hg0
  -- hence its two iterated `z`-derivatives are odd in `θ`
  have hodd1 : ∀ z θ : ℝ, Work.Spaces.pz (profile p g) z (-θ) = - Work.Spaces.pz (profile p g) z θ :=
    fun z θ => pz_odd_of_odd hodd z θ
  have hodd2 : ∀ z θ : ℝ,
      Work.Spaces.pz (Work.Spaces.pz (profile p g)) z (-θ)
        = - Work.Spaces.pz (Work.Spaces.pz (profile p g)) z θ :=
    fun z θ => pz_odd_of_odd hodd1 z θ
  intro z θ hz hθ
  have hb := abs_le.mp hθ
  by_cases hθ0 : 0 ≤ θ
  · exact hg3 z θ hz.le ⟨hθ0, hb.2⟩
  · have hθneg : θ < 0 := not_le.mp hθ0
    have hmem : -θ ∈ Work.Spaces.Iθ := ⟨by linarith, by linarith [hb.1]⟩
    have hP : z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) z θ
        = -(z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) z (-θ)) := by
      rw [hodd2 z θ]; ring
    rw [hP, abs_neg]
    exact hg3 z (-θ) hz.le hmem

end Work.ConstructionInstance
