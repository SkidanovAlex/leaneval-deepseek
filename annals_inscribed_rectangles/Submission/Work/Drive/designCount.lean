import Mathlib
import Submission.Work.Drive.parityCore_of_dense_count
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.linCapping

/-!
# The design's count `n`, and the wall from its three remaining properties

`Work.Drive.parityCore_of_countOnZc_dense` (`Submission/Work/Drive/parityCore_of_dense_count.lean`)
turns the wall `ParityCore γ` into four properties of one count `n : ℝ/ℤ → ℝ/ℤ → ZMod 2`
(`hn1` translation invariance, `hn2` antisymmetry, `hn4` local constancy, `hdense` the functional
identity on a *dense* set of triples; see `Submission/Work/Drive/CHAINPARITY_REDUCTION.md`).

This file instantiates `n` at the design's count — the lead's `sideCount` of
`Submission/Work/Drive/sideCountDefs.lean`, against the *rotation family* of the chart, with a fixed
pair `(A, A')` of projective-class perturbations:

> `designCount Q A A' c ψ u = Odd (coreSideCount (linCapping A ∘ Q) c
>   (linCapping A' ∘ rotPresentation Q u))`.

The point of the file is that **`hn1` is then *definitional***: the count is a function of the angle
difference by construction, so the wall is reduced to the three statements `hn2`, `hn4`, `hdense` about
`designCount` — which is the form in which the counting lane proves them (`hn4` = L6,
`Drive/odd_ncard_famMeet_iff`; `hn2` = Hugelmeyer's Lemma 3 in the reference-plane form; `hdense` =
Lemma 4 at the generic triples).

The perturbations are fixed once and for all, and this is *forced* by the definition: the cut
`diskCut (linCapping A ∘ Q) (sweep (linCapping B ∘ rotPresentation Q w))` depends on both `A` and `B`,
so `n` is a function of the angle only if the pair `(A, A')` does not vary with `u` (or with the
triple).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

/-- **The design's count**: the parity of the number of meets of the core loop of the perturbed chart
`linCapping A ∘ Q` with the clamped sweep of the rotated (and perturbed) plane presentation
`linCapping A' ∘ rotPresentation Q u`. -/
def designCount (Q : ℂ → CappingSpace) (A A' : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (ψ : ℝ → ℝ)
    (u : UnitAddCircle) : ZMod 2 :=
  if Odd (coreSideCount (fun z => linCapping A (Q z)) c
    (fun y => linCapping A' (rotPresentation Q u y))) then 1 else 0

/-- The `ZMod 2` value of `designCount` is `1` exactly at the angles where the count is odd. -/
lemma designCount_eq_one_iff (Q : ℂ → CappingSpace) (A A' : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ)
    (ψ : ℝ → ℝ) (u : UnitAddCircle) :
    designCount Q A A' c ψ u = 1 ↔
      Odd (coreSideCount (fun z => linCapping A (Q z)) c
        (fun y => linCapping A' (rotPresentation Q u y))) := by
  rw [designCount]
  by_cases h : Odd (coreSideCount (fun z => linCapping A (Q z)) c
    (fun y => linCapping A' (rotPresentation Q u y)))
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h1 => absurd h1 zero_ne_one, fun h2 => absurd h2 h⟩

/-- **The wall from the three remaining properties of the design's count.**  With `n` instantiated at
`designCount`, the translation invariance `hn1` of `parityCore_of_countOnZc_dense` is *definitional*
(proved below by `rfl`), so everything that is left is `hn2` (antisymmetry, Hugelmeyer's Lemma 3 — in
the reference-plane form), `hn4` (locality, L6) and `hdense` (Lemma 4 on a dense set of triples). -/
theorem parityCore_of_designCount {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (Q : ℂ → CappingSpace) (A A' : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (ψ : ℝ → ℝ)
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ →
      designCount Q A A' c ψ (v - u) + designCount Q A A' c ψ (u - v) = 1)
    (hn4 : ∀ x : Zc γ, ∀ᶠ y : Zc γ in 𝓝 x,
      designCount Q A A' c ψ (y : UnitAddCircle) = designCount Q A A' c ψ (x : UnitAddCircle))
    (hdense : ∀ a c' : UnitAddCircle, a ∈ Zc γ → c' ∈ Zc γ → a + c' ∈ Zc γ →
      (a, c') ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Zc γ ∧ q.2 ∈ Zc γ ∧ q.1 + q.2 ∈ Zc γ ∧
          designCount Q A A' c ψ q.1 * designCount Q A A' c ψ (q.1 + q.2)
            + designCount Q A A' c ψ (-q.1) * designCount Q A A' c ψ q.2
            + designCount Q A A' c ψ (-(q.1 + q.2)) * designCount Q A A' c ψ (-q.2) = 1}) :
    ParityCore γ := by
  refine parityCore_of_countOnZc_dense (γ := γ) hγ (fun u v => designCount Q A A' c ψ (v - u))
    (fun u v => by simp) ?_ ?_ ?_
  · intro u v hv
    simpa using hn2 u v hv
  · intro x
    simpa using hn4 x
  · intro a c' ha hc' hac
    simpa using hdense a c' ha hc' hac

end

end Work.Drive
