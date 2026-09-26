import Mathlib
import Submission.Work.TorusCover.Basic

/-!
# Every closed curve in the range of a parametrised torus (which is a covering) has a winding
vector

Let `psi : ℝ → ℝ → R3` be a parametrised torus (periodic in each variable, injective modulo the
period lattice `2πℤ²`), viewed as a map `psiMap psi : ℝ × ℝ → R3` onto its range and as the
covering map `psiMapToRange psi : ℝ × ℝ → range (psiMap psi)`.

If `psiMapToRange psi` is a covering map and `γ : ℝ → R3` is a continuous, `2π`-periodic curve
with values in the range of `psiMap psi`, then `γ` has a winding vector: it lifts to a continuous
`Λ : ℝ → ℝ × ℝ` with `psiMap psi (Λ t) = γ t`, and periodicity of `γ` forces the displacement
`Λ (t + 2π) - Λ t` to be a *constant* element of the period lattice `2πℤ²`, i.e.
`Λ (t + 2π) = Λ t + periodShift v` for a fixed `v : ℤ × ℤ`.

The proof is the standard lifting theorem for covering spaces:

* `ℝ` is simply connected and locally path connected, so `γ`, viewed as a map into the base
  `range (psiMap psi)`, lifts uniquely to `Λ` (`IsCoveringMap.existsUnique_continuousMap_lifts`);
* `Λ (t + 2π) - Λ t` lies in the period lattice for every `t` (injectivity modulo `2π`);
* `t ↦ Λ (t + 2π) - Λ t` is continuous and the period lattice is discrete, hence constant.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.TorusCover

noncomputable section

/-- **Lifting a closed curve.**  A continuous curve with values in the range of `psiMap P.psi`
lifts to a continuous curve `Λ : ℝ → ℝ × ℝ` through `psiMap P.psi`, normalised so that
`Λ 0` is a prescribed point of the fibre over `γ 0`. -/
theorem exists_isLift_continuous (P : Work.TorusCover.TorusParam)
    (hcov : IsCoveringMap (Work.TorusCover.psiMapToRange P.psi))
    {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (hγ : Continuous γ)
    (himg : ∀ t, γ t ∈ Set.range (Work.TorusCover.psiMap P.psi)) (p₀ : ℝ × ℝ)
    (hp₀ : Work.TorusCover.psiMap P.psi p₀ = γ 0) :
    ∃ Λ : ℝ → ℝ × ℝ, Continuous Λ ∧ (∀ t, Work.TorusCover.psiMap P.psi (Λ t) = γ t) ∧
      Λ 0 = p₀ := by
  -- `γ` as a continuous map into the base of the covering
  let f : C(ℝ, Set.range (psiMap P.psi)) := ⟨fun t => ⟨γ t, himg t⟩, hγ.subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts f 0 p₀ (Subtype.ext hp₀)
  have hlift : ∀ t : ℝ, psiMap P.psi (F t) = γ t := by
    intro t
    simpa [f] using congrArg Subtype.val (congr_fun hFlift t)
  exact ⟨fun t => F t, F.continuous, hlift, hF0⟩

/-- **Existence of a winding vector.**  A continuous, `2π`-periodic curve with values in the range
of a parametrised torus whose parametrisation is a covering map has a winding vector. -/
theorem exists_hasWinding_of_isCoveringMap (P : Work.TorusCover.TorusParam)
    (hcov : IsCoveringMap (Work.TorusCover.psiMapToRange P.psi))
    {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (hγ : Continuous γ)
    (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (Work.TorusCover.psiMap P.psi)) :
    ∃ v : ℤ × ℤ, Work.TorusCover.HasWinding P.psi γ v := by
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℝ × ℝ, psiMap P.psi p₀ = γ 0 := himg 0
  obtain ⟨Λ, hcont, hlift, -⟩ := exists_isLift_continuous P hcov hγ himg p₀ hp₀
  -- the displacement over one period is a continuous lattice-valued function of `t`
  have hmem : ∀ t : ℝ, Λ (t + 2 * Real.pi) - Λ t ∈ lattice := by
    intro t
    rw [← P.psiMap_eq_iff]
    rw [hlift (t + 2 * Real.pi), hper t, ← hlift t]
  have hcontd : Continuous fun t : ℝ => Λ (t + 2 * Real.pi) - Λ t :=
    (hcont.comp (continuous_id.add_const (2 * Real.pi))).sub hcont
  -- ... hence constant, because the period lattice is discrete
  have hconst : ∀ t : ℝ, Λ (t + 2 * Real.pi) - Λ t = Λ (2 * Real.pi) - Λ 0 := by
    intro t
    have := isPreconnected_univ.constant_of_mapsTo isDiscrete_lattice hcontd.continuousOn
      (fun s _ => hmem s) (mem_univ t) (mem_univ (0 : ℝ))
    simpa using this
  obtain ⟨v, hv⟩ := (mem_lattice_iff _).mp (by simpa using hmem 0)
  exact ⟨v, Λ, ⟨hcont, hlift⟩, fun t =>
    sub_eq_iff_eq_add'.mp (by rw [hconst t]; exact hv.symm)⟩

end

end Work.TorusCover
