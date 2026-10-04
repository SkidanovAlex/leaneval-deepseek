import Mathlib
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.uhlenbeck_frame_kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Uhlenbeck frame along a Ricci flow, in the model-space (coerced) form

Given a Ricci flow `G` on `[0,T)` (`Submission.Diff.IsRicciFlow`) and a point `x`, there is a family
of frames `e s : Fin (finrank ℝ E) → TₓM`, `G s`-orthonormal for every `s ∈ [0,T)`, whose derivative
at the single time `t` is the **Uhlenbeck/Ricci rule**

`∂ₛ eᵢ = ∑ⱼ Ric(eᵢ, eⱼ) • eⱼ`,

i.e. the frame moves by the Ricci endomorphism and has no rotational part.

The point of this module is the *coerced* (model space) form of the statement: `TangentSpace I x` is
definitionally `E`, and downstream consumers (the curvature-evolution contract `CurvEvolution` and
the matrix-valued frames of the Shi-estimate chapter) want the frame as a family of `E`-vectors, with
the derivative written explicitly as a finite sum in `E`.

## Structure of the proof

* `Work.Diff.GE.uhlenbeck_frame_exists_kit` (in `uhlenbeck_frame_kit.lean`, which rests on the
  matrix square-root family `matrix_sqrt_family_kit` and the symmetry of the Ricci tensor
  `ricAt_symm_kit`) produces a frame `e` together with *some* derivative vectors `v i`, subject to
  the pairing condition `⟨v i, e t j⟩ = Ric(e t i, e t j)`; that is the primitive, "coordinate-free"
  form in which the construction naturally lands.
* `Work.Diff.GE.uhlenbeck_coe_of_pair` below is the elementary linear-algebra bridge turning that
  data into the explicit Uhlenbeck form: an orthonormal frame of `TₓM` of cardinality `finrank ℝ E`
  spans, so a vector is determined by its pairings with it, and expanding
  `v i = ∑ⱼ ⟨v i, e t j⟩ • e t j` (`Work.Diff.GE.sum_smul_inner_eq_self`) and substituting the
  pairing condition gives `v i = ∑ⱼ Ric(e t i, e t j) • e t j`.
* The target `Work.Diff.GE.uhlenbeck_frame_coe` is then immediate.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]

/-- **The Uhlenbeck rule from the pairing condition.**  If `e` is a family of `G s`-orthonormal
frames of `TₓM` and `v` are derivative vectors of `e` at `t` whose pairings with the frame at `t`
are the Ricci tensor, then the derivative of `e ᵢ` at `t` (within `[0,T)`) is the explicit finite
sum `∑ⱼ Ric(eᵢ, eⱼ) • eⱼ` in `E`.

This is the linear-algebra bridge between the "pairing" form of the Uhlenbeck frame — which is what
the matrix square-root construction produces — and the "explicit sum" form consumed by the
curvature-evolution machinery. -/
theorem uhlenbeck_coe_of_pair
    (G : ℝ → SMet I M) (T t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M)
    (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
    (v : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hON : ∀ s ∈ Set.Ico 0 T, IsONFrame (G s) x (e s))
    (hv : ∀ i, HasDerivWithinAt (fun s : ℝ ↦ e s i) (v i) (Set.Ico 0 T) t)
    (hpair : ∀ i j, (G t).inner x (v i) (e t j)
      = ricAt (lcOf (G t)) x (e t i) (e t j)) :
    ∃ e' : ℝ → Fin (Module.finrank ℝ E) → E,
      (∀ s ∈ Set.Ico 0 T, IsONFrame (G s) x (e' s)) ∧
      ∀ i, HasDerivWithinAt (fun s : ℝ ↦ e' s i)
        ((∑ j, ricAt (lcOf (G t)) x (e' t i) (e' t j) • e' t j
          : TangentSpace I x) : E) (Set.Ico 0 T) t := by
  refine ⟨fun s i ↦ (e s i : E), fun s hs ↦ hON s hs, fun i ↦ ?_⟩
  by_cases hn : 0 < Module.finrank ℝ E
  · -- expand `v i` in the `G t`-orthonormal frame `e t`
    have hexp : ∑ j, (G t).inner x (v i) (e t j) • e t j = v i :=
      sum_smul_inner_eq_self (I := I) (M := M) (G t) x hn (e t) (hON t ht) (v i)
    have hv' : v i = ∑ j, ricAt (lcOf (G t)) x (e t i) (e t j) • e t j := by
      rw [← hexp]
      exact Finset.sum_congr rfl fun j _ => by rw [hpair i j]
    have hder : HasDerivWithinAt (fun s : ℝ ↦ e s i)
        (∑ j, ricAt (lcOf (G t)) x (e t i) (e t j) • e t j) (Set.Ico 0 T) t := by
      rw [← hv']
      exact hv i
    exact hder
  · -- degenerate case: `Fin (finrank ℝ E)` is empty
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    exact Fin.elim0 (h0 ▸ i)

/-- **The Uhlenbeck frame along a Ricci flow, in the coerced model-space form**: there is a family
of frames at `x`, `G s`-orthonormal for all `s ∈ [0,T)`, whose `s`-derivative at `t` is the
Uhlenbeck/Ricci rule `∑ⱼ Ric(eᵢ, eⱼ) • eⱼ`. -/
theorem uhlenbeck_frame_coe
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hflow : Submission.Diff.IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M) :
    ∃ e : ℝ → Fin (Module.finrank ℝ E) → E,
      (∀ s ∈ Set.Ico 0 T, Submission.Diff.IsONFrame (G s) x (e s)) ∧
      ∀ i, HasDerivWithinAt (fun s : ℝ ↦ e s i)
        ((∑ j, Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (e t i) (e t j) • e t j
          : TangentSpace I x) : E) (Set.Ico 0 T) t := by
  obtain ⟨e, v, hON, hv, hpair⟩ := uhlenbeck_frame_exists_kit hLC G T hflow t ht x
  exact uhlenbeck_coe_of_pair G T t ht x e v hON hv hpair

end Work.Diff.GE
