import Mathlib
import Submission.Work.CriticalSet.All
import Submission.Work.UnitGreen.Defs

/-!
# Regular levels of a unit-pole Green function (the exhaustion of `X ∖ {z₀}`)

`Submission/Work/CriticalSet/*` contains, sorry-free, the whole *local* theory of the critical
points and the regular level sets of a harmonic function on a Riemann surface: the critical set is
discrete (`criticalSet_isDiscreteIn`), hence countable in a second countable surface, so the
critical *values* are countable and regular values are abundant; at a regular point the level set is
locally the graph of a `C¹` function (`levelSet_isLocalGraph`, the implicit function theorem in
`ℝ²`), and the frontier of the superlevel set is the level set.  That chapter is stated for the
predicate `Submission.HasGreenFunctionWeak`, which is **unsatisfiable** on a non-compact `X`
(`Submission.not_exists_hasGreenFunctionWeak_of_not_compact`: it asks the superlevel set
`{x | ε ≤ E x}` itself to be compact, whereas for a genuine Green function that set is a punctured
neighbourhood of the pole and hence not closed).  Consequently every theorem of that chapter with
that hypothesis is vacuous.

This module **ports the chapter to the satisfiable predicate** `Work.UnitGreen.IsUnitGreenFunctionAt`
(and hence to `Work.Parabolic.IsGreenFunctionAt`), whose superlevel clause is the correct
*relative compactness* one, `IsCompact (closure {x | ε ≤ E x})`.  The only step of the port that is
not a direct citation is `notLocallyConstantOn_of_isUnitGreenFunction`, whose proof is the same
argument as the vacuous original with the final compactness step redone: from
`{x | E x ≤ E x₀} ⊆ closure {x | E x ≤ E x₀}` compact one gets `X ⊆ closure {x | E x ≤ E x₀} ∪ {z₀}`
compact, contradicting `¬ CompactSpace X`.

## Main results

* `notLocallyConstantOn_of_isUnitGreenFunction` — `E` is nowhere locally constant off the pole;
* `countable_criticalValues_of_isUnitGreenFunction` — the critical values of `E` are countable;
* `exists_regularLevel_of_isUnitGreenFunction` — regular levels exist below every `ε₀ > 0`, with
  the level set locally a `C¹` graph and the superlevel set relatively compact;
* `exists_pos_le_on_isCompact` — the superlevel sets exhaust `X ∖ {z₀}`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.Mori

open Work.CriticalSet

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A unit-pole Green function is nowhere locally constant off the pole.**

The proof is that of `Work.CriticalSet.notLocallyConstantOn_of_hasGreenFunctionWeak`, whose only
input is the harmonicity of `E` off `z₀` and the relative compactness of its superlevel sets; the
final step uses relative compactness (the correct hypothesis) in place of compactness of the
superlevel set itself. -/
theorem notLocallyConstantOn_of_isUnitGreenFunction {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) (hX : ¬ CompactSpace X) :
    NotLocallyConstantOn E (punctured z₀) := by
  have hharm : Submission.HarmonicOnX E (punctured z₀) := hE.1.2.1
  have hKcomp : ∀ ε : ℝ, 0 < ε → IsCompact (closure {y : X | ε ≤ E y}) := hE.1.2.2
  intro x hx hconst
  have hxne : x ≠ z₀ := mem_punctured.mp hx
  set A : Set X := locallyConstantSet E with hAdef
  have hAopen : IsOpen A := by rw [hAdef]; exact isOpen_locallyConstantSet E
  have hxmem : x ∈ A := by rw [hAdef]; exact hconst
  have hclos : ∀ y ∈ punctured z₀, y ∈ closure A → y ∈ A := by
    intro y hy hycl
    rw [hAdef] at hycl ⊢
    exact mem_locallyConstantSet_of_mem_closure (hharm y hy) hycl
  have hpreconn : IsPreconnected (punctured z₀) := isPreconnected_punctured z₀
  have hVA : punctured z₀ ⊆ A := by
    rcases IsPreconnected.subset_or_subset hAopen isClosed_closure.isOpen_compl
        (Set.disjoint_left.mpr fun a ha ha' => ha' (subset_closure ha))
        (fun y hy => by
          by_cases h : y ∈ A
          · exact Or.inl h
          · exact Or.inr fun hcl => h (hclos y hy hcl))
        hpreconn with h | h
    · exact h
    · exact absurd (subset_closure hxmem) (h hx)
  have hconstV : ∀ y ∈ punctured z₀, E y = E x := by
    have : PreconnectedSpace ↥(punctured z₀) := isPreconnected_iff_preconnectedSpace.mp hpreconn
    have hloc : IsLocallyConstant (fun y : ↥(punctured z₀) => E (y : X)) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro y'
      have hy'A : (y' : X) ∈ A := hVA y'.2
      rw [hAdef] at hy'A
      exact (continuous_subtype_val.continuousAt).eventually hy'A
    intro y hy
    exact (IsLocallyConstant.apply_eq_of_isPreconnected hloc isPreconnected_univ
      (x := (⟨x, hx⟩ : ↥(punctured z₀))) (y := (⟨y, hy⟩ : ↥(punctured z₀)))
      (mem_univ _) (mem_univ _)).symm
  have hcx : 0 < E x := hE.1.1 x hxne
  have hsub : (univ : Set X) ⊆ closure {y : X | E x ≤ E y} ∪ {z₀} := by
    intro y _
    by_cases hy : y = z₀
    · exact Or.inr hy
    · exact Or.inl (subset_closure (hconstV y (mem_punctured.mpr hy)).ge)
  exact hX (isCompact_univ_iff.mp
    (IsCompact.of_isClosed_subset ((hKcomp (E x) hcx).union isCompact_singleton)
      isClosed_univ hsub))

/-- **The critical values of a unit-pole Green function are countable.** -/
theorem countable_criticalValues_of_isUnitGreenFunction {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) (hX : ¬ CompactSpace X) :
    (E '' criticalSet E (punctured z₀)).Countable := by
  refine (countable_of_isDiscreteIn (criticalSet_isDiscreteIn (isOpen_punctured z₀)
    hE.1.2.1 (notLocallyConstantOn_of_isUnitGreenFunction hE hX)) ?_).image E
  intro x hx
  exact hx.1

/-- **Regular levels of a unit-pole Green function exist below every positive level.**

For every `ε₀ > 0` there is `ε ∈ (0, ε₀)` which is a regular value of `E` on the punctured surface,
whose level set is locally a `C¹` graph, and whose superlevel set is relatively compact.  These are
the pieces of the exhaustion of `X ∖ {z₀}` by compact bordered surfaces. -/
theorem exists_regularLevel_of_isUnitGreenFunction {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) (hX : ¬ CompactSpace X) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧
      IsRegularValueOn E (punctured z₀) ε ∧ LevelSetIsLocallyGraphOn E (punctured z₀) ε ∧
      IsCompact (closure {x : X | ε ≤ E x}) := by
  intro ε₀ hε₀
  have hcount := countable_criticalValues_of_isUnitGreenFunction hE hX
  have hdense : Dense ((E '' criticalSet E (punctured z₀))ᶜ) :=
    Set.Countable.dense_compl ℝ hcount
  obtain ⟨ε, hεnot, hεI⟩ :=
    hdense.exists_mem_open (U := Set.Ioo (0 : ℝ) ε₀) isOpen_Ioo (Set.nonempty_Ioo.mpr hε₀)
  have hεpos : 0 < ε := hεI.1
  have hreg : IsRegularValueOn E (punctured z₀) ε := by
    intro x hx hxε hcrit
    exact hεnot ⟨x, ⟨hx, hcrit⟩, hxε⟩
  exact ⟨ε, hεpos, hεI.2, hreg,
    fun x hx hxε => levelSet_isLocalGraph (hE.1.2.1 x hx) fun hcrit => hreg x hx hxε hcrit,
    hE.1.2.2 ε hεpos⟩

/-- **The superlevel sets of a unit-pole Green function exhaust the punctured surface.**  Every
compact subset of `X ∖ {z₀}` is contained in `{x | ε ≤ E x}` for some `ε > 0`. -/
theorem exists_pos_le_on_isCompact {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) {K : Set X} (hK : IsCompact K)
    (hKsub : K ⊆ punctured z₀) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ E x := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne fun x hx =>
    (Submission.HarmonicOnXAt.continuousAt (hE.1.2.1 x (hKsub hx))).continuousWithinAt
  have hx₀ne : x₀ ≠ z₀ := by simpa [punctured] using hKsub hx₀K
  refine ⟨E x₀ / 2, by linarith [hE.1.1 x₀ hx₀ne], fun x hx => ?_⟩
  have hle : E x₀ ≤ E x := hmin hx
  linarith [hE.1.1 x₀ hx₀ne]

end Work.Mori
