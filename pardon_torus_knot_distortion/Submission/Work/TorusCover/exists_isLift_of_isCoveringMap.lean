import Mathlib
import Submission.Work.TorusCover.Basic

namespace Work.TorusCover

/-- **Existence of lifts through a covering parametrised torus.**

If the parametrisation `psiMap psi : ℝ × ℝ → R3` induces a covering map onto its range, then
every continuous curve `γ` in `R3` whose image lies in the range of `psiMap psi` admits a lift
`Λ : ℝ → ℝ × ℝ` through `psi`, and the lift can be prescribed at the single point `0`: given
`p₀` with `psiMap psi p₀ = γ 0` there is a lift `Λ` with `Λ 0 = p₀`.

This is the covering-space path-lifting theorem applied to the map
`psiMapToRange psi : ℝ × ℝ → Set.range (psiMap psi)`, using that `ℝ` is simply connected and
locally path connected. -/
theorem exists_isLift_of_isCoveringMap (P : Work.TorusCover.TorusParam)
    (hcov : IsCoveringMap (Work.TorusCover.psiMapToRange P.psi))
    {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (hγ : Continuous γ)
    (himg : ∀ t, γ t ∈ Set.range (Work.TorusCover.psiMap P.psi)) (p₀ : ℝ × ℝ)
    (hp₀ : Work.TorusCover.psiMap P.psi p₀ = γ 0) :
    ∃ Λ : ℝ → ℝ × ℝ, Work.TorusCover.IsLift P.psi γ Λ ∧ Λ 0 = p₀ := by
  -- view `γ` as a continuous map into the range of `psiMap psi`
  let γbar : C(ℝ, Set.range (psiMap P.psi)) :=
    ⟨fun t => ⟨γ t, himg t⟩, hγ.subtype_mk himg⟩
  -- the prescribed starting point is a lift of `γbar 0`
  have he : psiMapToRange P.psi p₀ = γbar 0 := Subtype.ext hp₀
  -- covering-space lifting theorem for the simply connected, locally path connected `ℝ`
  obtain ⟨F, ⟨hF0, hF⟩, _⟩ :=
    hcov.existsUnique_continuousMap_lifts γbar 0 p₀ he
  refine ⟨fun t => F t, ⟨F.2, ?_⟩, ?_⟩
  · intro t
    have h := congrArg Subtype.val (congr_fun hF t)
    simpa [psiMap, γbar] using h
  · simpa using hF0

end Work.TorusCover
