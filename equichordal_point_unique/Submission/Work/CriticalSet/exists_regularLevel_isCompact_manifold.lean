import Submission.Work.CriticalSet.Defs
import Submission.Work.CriticalSet.countable_criticalValues
import Submission.Work.CriticalSet.levelSet_isLocalGraph
import Submission.Work.CriticalSet.notLocallyConstantOn_of_hasGreenFunctionWeak
import Submission.Work.Modulus.puncturedConnected

/-!
# Regular levels of a Green function: the exhaustion shape

The main deliverable of this chapter: for a weak Green function `E` at `z₀` on a non-compact
connected Riemann surface `X`, there are regular levels of `E` arbitrarily close to `0`.  For every
such `ε`,

* `ε > 0` is a regular value of `E` on `X ∖ {z₀}` (`Work.CriticalSet.IsRegularValueOn`),
* every point of the level set `{E = ε}` has a neighbourhood on which the level set is a `C¹` graph
  (`Work.CriticalSet.LevelSetIsLocallyGraphOn`, from the implicit function theorem), and
* the superlevel set `{E ≥ ε}` is compact,

so `{E ≥ ε}` is a compact sub-surface with smooth (`C¹`) boundary `{E = ε}`, and these exhaust
`X ∖ {z₀}` as `ε ↘ 0`.

The proof uses no Sard theorem.  The critical points of `E` on the punctured surface are isolated
(`Work.CriticalSet.criticalSet_isDiscreteIn`), hence countable in a second countable surface, hence
their values — the critical values — are countable; the complement of a countable subset of `ℝ` is
dense, so it meets `(0, ε₀)`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.CriticalSet

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The punctured surface `X ∖ {z₀}` is preconnected (`Work.Modulus.puncturedConnected`). -/
theorem isPreconnected_punctured (z₀ : X) : IsPreconnected (punctured z₀) := by
  haveI : ConnectedSpace (Work.Modulus.puncturedOpens z₀) := Work.Modulus.puncturedConnected z₀
  have h : IsPreconnected (Set.univ : Set (Work.Modulus.puncturedOpens z₀)) := isPreconnected_univ
  have h2 : IsPreconnected ((Subtype.val : (Work.Modulus.puncturedOpens z₀) → X) ''
      (Set.univ : Set (Work.Modulus.puncturedOpens z₀))) :=
    h.image (Subtype.val : (Work.Modulus.puncturedOpens z₀) → X) continuous_subtype_val.continuousOn
  have himg : ((Subtype.val : (Work.Modulus.puncturedOpens z₀) → X) ''
      (Set.univ : Set (Work.Modulus.puncturedOpens z₀))) = ({z₀}ᶜ : Set X) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have h3 : IsPreconnected ({z₀}ᶜ : Set X) := by rwa [himg] at h2
  have hset : ({z₀}ᶜ : Set X) = punctured z₀ := by
    rw [Set.compl_eq_univ_diff]; rfl
  rwa [hset] at h3

/-- **Regular levels of a Green function, from the nonconstancy hypothesis.**

If `E` is nowhere locally constant on `X ∖ {z₀}` (which holds for a Green function on a non-compact
surface, see `Work.CriticalSet.notLocallyConstantOn_of_hasGreenFunctionWeak`), then regular levels
of `E` are arbitrarily small. -/
theorem exists_regularLevel_of_nonconstant {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionWeak z₀ E) (hnlc : NotLocallyConstantOn E (punctured z₀)) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ∃ ε : ℝ, IsRegularLevel E z₀ ε ∧ ε < ε₀ := by
  have hcount := countable_criticalValues_of_hasGreenFunctionWeak hE hnlc
  intro ε₀ hε₀
  have hdense : Dense ((E '' criticalSet E (punctured z₀))ᶜ) :=
    Set.Countable.dense_compl ℝ hcount
  obtain ⟨ε, hεnot, hεI⟩ :=
    hdense.exists_mem_open (U := Set.Ioo (0 : ℝ) ε₀) isOpen_Ioo (Set.nonempty_Ioo.mpr hε₀)
  have hεpos : 0 < ε := hεI.1
  have hreg : IsRegularValueOn E (punctured z₀) ε := by
    intro x hx hxε hcrit
    exact hεnot ⟨x, ⟨hx, hcrit⟩, hxε⟩
  refine ⟨ε, ⟨hεpos, hreg, ?_, hE.2.2 ε hεpos⟩, hεI.2⟩
  intro x hx hxε
  exact levelSet_isLocalGraph (hE.2.1 x hx) fun hcrit => hreg x hx hxε hcrit

/-- **Regular levels of a weak Green function on a non-compact surface.**

For `z₀ : X` and `E : X → ℝ` with the weak Green function data at `z₀`, on a non-compact connected
second countable Riemann surface, the regular levels of `E` below any `ε₀ > 0` exist.  Each one gives
the compact sub-surface `{E ≥ ε}` with smooth boundary `{E = ε}` of the exhaustion argument. -/
theorem exists_regularLevel_isCompact_manifold {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionWeak z₀ E) (hX : ¬ CompactSpace X) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ∃ ε : ℝ, IsRegularLevel E z₀ ε ∧ ε < ε₀ :=
  exists_regularLevel_of_nonconstant hE
    (notLocallyConstantOn_of_hasGreenFunctionWeak hE (isPreconnected_punctured z₀) hX)

/-- **The superlevel sets exhaust the punctured surface.**  Every compact subset of `X ∖ {z₀}` is
contained in `{E ≥ ε}` for some `ε > 0`. -/
theorem exists_pos_le_on_isCompact {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionWeak z₀ E) {K : Set X} (hK : IsCompact K)
    (hKsub : K ⊆ punctured z₀) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ E x := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne fun x hx =>
    (Submission.HarmonicOnXAt.continuousAt (hE.2.1 x (hKsub hx))).continuousWithinAt
  have hx₀ne : x₀ ≠ z₀ := by simpa [punctured] using hKsub hx₀K
  refine ⟨E x₀ / 2, by linarith [hE.1 x₀ hx₀ne], fun x hx => ?_⟩
  have hle : E x₀ ≤ E x := hmin hx
  linarith [hE.1 x₀ hx₀ne]

end Work.CriticalSet
