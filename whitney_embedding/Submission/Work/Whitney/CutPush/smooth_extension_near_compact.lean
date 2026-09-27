import Mathlib
import Submission.Work.Whitney.CutPush.bump_on_compact

/-!
# Extending a smooth function from an open set, near a compact subset

`Work.Whitney.CutPush.exists_contDiff_extension_near_compact`: a function that is `C^∞` on an open set
`Ω` can be extended to a globally `C^∞` function agreeing with it on a whole neighbourhood `V` of any
prescribed compact `K ⊆ Ω`.

The construction is the standard one: put a smooth bump `χ` (equal to `1` on an open `V ⊇ K`, supported
in a thickening `W ⊆ Ω`) and take

    g' x = χ x • (if x ∈ Ω then g x else 0).

At a point of `W` (an *open* set inside `Ω`) the indicator agrees with `g` on a neighbourhood, so `g'` is
locally `χ • g`; outside `tsupport χ` the function `g'` vanishes on a neighbourhood.  On `V` we have
`χ = 1` and `V ⊆ Ω`, so `g' = g`.

This is the brick that globalises the graph function of the last step of the collar flattening
(`CutPush/NOTES_STATE_S60.md` §2): the sheet's graph function is defined on an open `Ω ⊆ K'` and has to
be made global before the fibered shear can use it.
-/

namespace Work.Whitney.CutPush

open scoped Topology ContDiff
open Metric

/-- **Smooth extension near a compact set.** -/
theorem exists_contDiff_extension_near_compact {m : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin m))) (hΩ : IsOpen Ω)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hKc : IsCompact K) (hKΩ : K ⊆ Ω)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g Ω) :
    ∃ (g' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
      (V : Set (EuclideanSpace ℝ (Fin m))),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g' ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧ ∀ x ∈ V, g' x = g x := by
  classical
  obtain ⟨δ, hδpos, hδΩ⟩ := hKc.exists_cthickening_subset_open hΩ hKΩ
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hWΩ : thickening (δ / 2) K ⊆ Ω := fun x hx =>
    hδΩ (thickening_subset_cthickening_of_le (by linarith) K hx)
  obtain ⟨χ, V, hχc, hVo, hKV, hVW, hχ1, hχsupp⟩ :=
    exists_contDiffBump_one_on_open_of_compact (isOpen_thickening) hKc
      (self_subset_thickening hhalf K)
  refine ⟨fun x => χ x • (if x ∈ Ω then g x else 0), V, ?_, hVo, hKV,
    fun x hx => hWΩ (hVW hx), fun x hx => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ thickening (δ / 2) K
    · have hpΩ : p ∈ Ω := hWΩ hp
      have heq : (fun x => χ x • (if x ∈ Ω then g x else 0)) =ᶠ[𝓝 p] fun x => χ x • g x := by
        filter_upwards [hΩ.mem_nhds hpΩ] with x hx
        simp only [hx, if_pos]
      exact (hχc.contDiffAt.smul (hg.contDiffAt (hΩ.mem_nhds hpΩ))).congr_of_eventuallyEq heq
    · have hpχ : p ∉ tsupport χ := fun h => hp (hχsupp h)
      have hcompl : (tsupport χ)ᶜ ∈ 𝓝 p := (isClosed_tsupport χ).isOpen_compl.mem_nhds hpχ
      have heq : (fun x => χ x • (if x ∈ Ω then g x else 0))
          =ᶠ[𝓝 p] fun _ => (0 : EuclideanSpace ℝ (Fin m)) := by
        filter_upwards [hcompl] with x hx
        have hx0 : χ x = 0 := by
          by_contra h
          exact hx (subset_closure (Function.mem_support.mpr h))
        simp only [hx0, zero_smul]
      exact (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin m)))).congr_of_eventuallyEq heq
  · simp only [hχ1 x hx, one_smul, if_pos (hWΩ (hVW hx))]

end Work.Whitney.CutPush
