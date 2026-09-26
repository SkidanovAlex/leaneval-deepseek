import Mathlib
import Submission.Work.TorusCover.Basic

/-!
# Two curves with the same winding vector are homotopic through closed curves

If `γ₀` and `γ₁` are curves in the range of a parametrised torus `P` which admit periodic lifts
with the *same* winding vector `v`, then they are homotopic through closed curves in the range of
`P`.

Indeed, write `Λ₀`, `Λ₁` for the two periodic lifts (`Λᵢ (t + 2π) = Λᵢ t + periodShift v`), and
consider the straight-line homotopy of the lifts in the parameter plane

`Λ s t = (1 - s) • Λ₀ t + s • Λ₁ t`.

It is continuous in `(s, t)`, and because both lifts advance by the same period shift `periodShift v`
over one period, `Λ s (t + 2π) = Λ s t + periodShift v`, so

`H (s, t) = psiMap P.psi (Λ s t)`

is `2π`-periodic in `t` (the parametrisation is invariant under `periodShift v`) and takes values
in the range of `psiMap P.psi` by construction.  Its restrictions to `s = 0` and `s = 1` are `γ₀`
and `γ₁`, so it witnesses `HomotopicClosed P.psi γ₀ γ₁`.

Note that the straight-line homotopy of the lifts makes no use of the hypothesis that the two
curves agree at the base point; that hypothesis is part of the requested statement but is not
needed for this direction.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

namespace Work.TorusCover

noncomputable section

set_option linter.unusedVariables false in
theorem homotopicClosed_of_hasWinding (P : Work.TorusCover.TorusParam)
    {γ₀ γ₁ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    (hbase : γ₀ 0 = γ₁ 0) {v : ℤ × ℤ} (hv₀ : Work.TorusCover.HasWinding P.psi γ₀ v)
    (hv₁ : Work.TorusCover.HasWinding P.psi γ₁ v) :
    Work.TorusCover.HomotopicClosed P.psi γ₀ γ₁ := by
  obtain ⟨Λ₀, hΛ₀⟩ := hv₀
  obtain ⟨Λ₁, hΛ₁⟩ := hv₁
  have hcont₀ : Continuous Λ₀ := hΛ₀.1.1
  have hcont₁ : Continuous Λ₁ := hΛ₁.1.1
  have hmap₀ : ∀ t, P.psi (Λ₀ t).1 (Λ₀ t).2 = γ₀ t := hΛ₀.1.2
  have hmap₁ : ∀ t, P.psi (Λ₁ t).1 (Λ₁ t).2 = γ₁ t := hΛ₁.1.2
  have hper₀ : ∀ t, Λ₀ (t + 2 * Real.pi) = Λ₀ t + periodShift v := hΛ₀.2
  have hper₁ : ∀ t, Λ₁ (t + 2 * Real.pi) = Λ₁ t + periodShift v := hΛ₁.2
  refine ⟨fun st : ℝ × ℝ => psiMap P.psi ((1 - st.1) • Λ₀ st.2 + st.1 • Λ₁ st.2),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of the straight-line homotopy of the lifts
    apply P.contDiff.continuous.comp
    fun_prop
  · -- `s = 0` gives `γ₀`
    intro t
    change psiMap P.psi ((1 - (0:ℝ)) • Λ₀ t + (0:ℝ) • Λ₁ t) = γ₀ t
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    rw [psiMap_apply]
    exact hmap₀ t
  · -- `s = 1` gives `γ₁`
    intro t
    change psiMap P.psi ((1 - (1:ℝ)) • Λ₀ t + (1:ℝ) • Λ₁ t) = γ₁ t
    simp only [sub_self, zero_smul, one_smul, zero_add]
    rw [psiMap_apply]
    exact hmap₁ t
  · -- every level set is `2π`-periodic
    intro s t
    have harg : (1 - s) • Λ₀ (t + 2 * Real.pi) + s • Λ₁ (t + 2 * Real.pi)
        = ((1 - s) • Λ₀ t + s • Λ₁ t) + periodShift v := by
      rw [hper₀ t, hper₁ t]
      module
    simp only [harg, TorusParam.psiMap_add_periodShift]
  · -- values lie in the range of the parametrisation
    intro s t
    exact Set.mem_range_self _

end

end Work.TorusCover
