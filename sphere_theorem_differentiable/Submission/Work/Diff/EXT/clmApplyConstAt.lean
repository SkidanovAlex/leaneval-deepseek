import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unnecessarySimpa false

namespace Work.Diff.EXT

/-- Evaluation at a fixed vector commutes with taking iterated Fréchet derivatives:
the `i`-th derivative of `y ↦ (c y) u` is the `i`-th derivative of `c` post-composed
with the continuous linear map `L ↦ L u`. -/
theorem clmApplyConstAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {c : E → F →L[ℝ] G} {x : E} (hc : ContDiffAt ℝ (⊤ : ℕ∞) c x)
    {i : ℕ} {u : F} {m : Fin i → E} :
    (iteratedFDeriv ℝ i (fun y => (c y) u) x) m = ((iteratedFDeriv ℝ i c x) m) u := by
  set g : (F →L[ℝ] G) →L[ℝ] G := ContinuousLinearMap.apply ℝ G u with hg
  have h1 : (fun y => (c y) u) = g ∘ c := by funext y; simp [hg]
  rw [h1, g.iteratedFDeriv_comp_left hc (by simpa using (le_top : (i : WithTop ℕ∞) ≤ ⊤))]
  simp [hg]

end Work.Diff.EXT
