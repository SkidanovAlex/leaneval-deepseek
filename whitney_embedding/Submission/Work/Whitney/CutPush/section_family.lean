import Mathlib
import Submission.Work.Whitney.CutPush.bump_family

/-!
# Turning a `ContDiffOn` section into a globally smooth family (rung 3 of the parametric tower)

`CutPush/NOTES_STATE_S57.md` §4.  Rung 2 (`graph_family.lean`) needs its local-inverse family to be
*globally jointly smooth*, whereas `exists_ift_data` supplies, for each parameter, only a `ContDiffOn` local
inverse on `O t ×ˢ W t`.  This file isolates the conversion, in two generic steps:

* `contDiff_bump_mul_contDiffOn` — if `f` is `C^∞` on an open `U` and `χ` is a smooth bump with
  `tsupport χ ⊆ U`, then `x ↦ χ x • f x` is globally `C^∞`.  (At a point of `U` it is a product of smooth
  maps; outside `U` the bump vanishes on a neighbourhood, so the product is locally `0`.)
* `exists_contDiff_agreeing_near` — every point `x₀` of an open `U` has a radius `δ > 0` and a *globally*
  smooth `F'` with `F' = f` on the ball of radius `δ` around `x₀`.

Instantiating at `E := ℝ × ↥P`, `f := Function.uncurry h`, `U := O ×ˢ W` and `x₀ := (s₀, w₀)` gives exactly
the globally smooth family that `contDiff_family_graph_function` consumes, agreeing with the local inverse on
a *ball* around `(s₀, w₀)` — i.e. on a box in the slice parameter and the base point, which is the region on
which the left-inverse property is used.
-/

namespace Work.Whitney.CutPush

open scoped Topology ContDiff

set_option linter.unusedVariables false

/-- **A bump-multiplied `ContDiffOn` map is globally smooth.** -/
theorem contDiff_bump_mul_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) {χ : E → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχsupp : tsupport χ ⊆ U) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hχsupp h)
    have hmem : (tsupport χ)ᶜ ∈ 𝓝 x := (isClosed_tsupport χ).isOpen_compl.mem_nhds hx'
    have hev : (fun y => χ y • f y) =ᶠ[𝓝 x] 0 :=
      Filter.mem_of_superset hmem fun y hy => by
        have hy' : y ∉ Function.support χ := fun h => hy (subset_tsupport χ h)
        simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hy'
        simp [hy']
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hev

/-- **A globally smooth map agreeing with a `ContDiffOn` map near a point.** -/
theorem exists_contDiff_agreeing_near {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ (F' : E → F) (δ : ℝ), 0 < δ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F' ∧
      ∀ x, dist x x₀ ≤ δ → F' x = f x := by
  obtain ⟨χ, δ, hδ, hχc, hχ1, hχνn, hχsupp⟩ := exists_contDiffBump_near hU hx₀
  exact ⟨fun x => χ x • f x, δ, hδ, contDiff_bump_mul_contDiffOn hU hf hχc hχsupp,
    fun x hx => by
      show χ x • f x = f x
      rw [hχ1 x hx, one_smul]⟩

end Work.Whitney.CutPush
