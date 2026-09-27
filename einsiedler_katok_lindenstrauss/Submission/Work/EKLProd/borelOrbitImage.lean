import Mathlib
import Submission.Work.EKLContract.All

/-!
# The orbit image of `V ε ∩ U` is Borel

`Work.EKLContract.SL3 = SL₃(ℝ)` is realized as the closed subspace `{A | A.det = 1}` of the
`3 × 3` real matrices.  Mathlib knows that the matrix space (a finite product of copies of `ℝ`)
is second countable and locally compact, but instance search does not unfold the `def`
`Matrix`, so `SL₃(ℝ)` inherits neither.  The four instances below repair that.

With the topology at hand we prove the lemma: for a **closed** subgroup `U ≤ SL₃(ℝ)`, any point
`x₀ ∈ X₃ = SL₃(ℝ)/SL₃(ℤ)` and any `ε`, the set

`(fun u => u • x₀) '' (V ε ∩ U)`

is Borel in `X₃`.

The point is that `V ε` is *open* and `SL₃(ℝ)` is locally compact and second countable, so
`↥(V ε)` is σ-compact (`sigmaCompactSpace_of_locallyCompact_secondCountable`).  Inside it, the
set `{g | (g : SL₃(ℝ)) ∈ U}` is closed (as `U` is closed), hence σ-compact, and so is
`V ε ∩ U`.  Its image under the continuous orbit map is σ-compact, and compact subsets of the
Hausdorff space `X₃` are measurable, so a countable union of them is measurable.

For `ε ≤ 0` we have `V ε = ∅`, which is σ-compact outright.
-/

set_option linter.style.haveILetI false

namespace Work.EKLProd

open MeasureTheory Topology
open Work.EKLContract

instance instSecondCountableTopologyMatrix3 :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))

instance instLocallyCompactSpaceMatrix3 :
    LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))

instance instSecondCountableTopologySL3 : SecondCountableTopology SL3 :=
  inferInstanceAs
    (SecondCountableTopology ↥({A : Matrix (Fin 3) (Fin 3) ℝ | A.det = 1} : Set _))

instance instLocallyCompactSpaceSL3 : LocallyCompactSpace SL3 :=
  (isClosed_eq (continuous_id.matrix_det (n := Fin 3) (R := ℝ)) continuous_const).locallyCompactSpace

/-- For a closed subgroup `U ≤ SL₃(ℝ)` the set `V ε ∩ U` is σ-compact: it is contained in the
open set `V ε`, whose subspace is σ-compact, in which `V ε ∩ U` is closed (because `U` is). -/
lemma isSigmaCompact_V_inter (U : Subgroup SL3) (hU : IsClosed (U : Set SL3)) (ε : ℝ) :
    IsSigmaCompact ((V ε ∩ (U : Set SL3)) : Set SL3) := by
  by_cases hε : 0 < ε
  · -- `V ε` is open, so `↥(V ε)` is a locally compact second countable space, hence σ-compact
    have hO : IsOpen (V ε) := (Work.EKLContract.Lemmas.V_open_one ε hε).1
    haveI : LocallyCompactSpace ↥(V ε) := hO.locallyCompactSpace
    haveI : SecondCountableTopology ↥(V ε) := inferInstance
    haveI : SigmaCompactSpace ↥(V ε) := sigmaCompactSpace_of_locallyCompact_secondCountable
    -- inside `↥(V ε)`, the set of points lying in the closed subgroup `U` is closed
    have hs : IsSigmaCompact ({g : ↥(V ε) | (g : SL3) ∈ (U : Set SL3)} : Set ↥(V ε)) :=
      IsSigmaCompact.of_isClosed_subset isSigmaCompact_univ
        (hU.preimage continuous_subtype_val) (Set.subset_univ _)
    have h2 := (Subtype.isSigmaCompact_iff (p := fun g : SL3 => g ∈ V ε)).mp hs
    have himg : (Subtype.val '' ({g : ↥(V ε) | (g : SL3) ∈ (U : Set SL3)}) : Set SL3)
        = V ε ∩ (U : Set SL3) := by
      ext x
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g.2, hg⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨⟨x, hx1⟩, hx2, rfl⟩
    rwa [himg] at h2
  · -- `ε ≤ 0` forces `V ε = ∅`
    have hV : V ε = ∅ := by
      ext g
      refine ⟨fun hg => ?_, fun h => absurd h (Set.notMem_empty g)⟩
      have h00 : |g 0 0 - (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0| < ε := hg 0 0
      have h1 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 1 := by simp
      rw [h1] at h00
      have := abs_nonneg (g 0 0 - 1)
      have hε' : ε ≤ 0 := le_of_not_gt hε
      linarith
    rw [hV, Set.empty_inter]
    exact isSigmaCompact_empty

theorem borelOrbitImage (U : Subgroup Work.EKLContract.SL3) (hU : IsClosed (U : Set Work.EKLContract.SL3)) (x₀ : Work.EKLContract.X3) (ε : ℝ) :
    MeasurableSet ((fun u : Work.EKLContract.SL3 => u • x₀) '' (Work.EKLContract.V ε ∩ (U : Set Work.EKLContract.SL3))) := by
  have hcont : Continuous (fun u : SL3 => u • x₀) := by fun_prop
  have hsc := IsSigmaCompact.image hcont (isSigmaCompact_V_inter U hU ε)
  obtain ⟨K, hK, hcov⟩ := hsc
  rw [← hcov]
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

end Work.EKLProd
