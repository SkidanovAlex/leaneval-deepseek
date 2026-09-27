import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.finite_nearStab

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- **Minimal positive displacement.**  For a discrete subgroup `D` of `PO 1 1` whose orbit of the
base point `0` contains a point distinct from `0`, the set of positive displacement values
`{hdist 0 (h • 0) | h ∈ D}` attains a minimum.

The proof is the standard properness argument: an element `h₀ ∈ D` with positive displacement gives a
radius `R := hdist 0 (h₀ • 0)`, and `finite_nearStab` says that `{γ ∈ D | hdist 0 (γ • 0) ≤ R}` is
finite.  The positive displacements occurring there form a finite nonempty set of reals, whose
minimum is the required `g₀`; every element with displacement `> R` is immediately out of the
running because `g₀` stays inside the `R`-ball. -/
theorem minimalPositiveDisplacement (hA : Submission.Mostow.POActionProp 1)
    (hI : Submission.Mostow.HypIsometryProp 1)
    (D : Subgroup (LeanEval.Geometry.MostowRigidity.PO 1 1))
    (hdisc : IsDiscrete (SetLike.coe D))
    (hex : ∃ h ∈ D, 0 < Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (h • (0 : Submission.Mostow.E 1))) :
    ∃ g₀ ∈ D, 0 < Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) ∧
      ∀ h ∈ D, 0 < Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (h • (0 : Submission.Mostow.E 1)) →
        Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) ≤
          Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (h • (0 : Submission.Mostow.E 1)) := by
  classical
  obtain ⟨h₀, hh₀D, hh₀pos⟩ := hex
  have hA' : POBasic 1 := POBasic.ofProp hA
  have hI' : HypIsoData 1 := HypIsoData.ofProp hI
  -- the finite set of elements of `D` displacing `0` by at most the displacement of `h₀`
  have hfin : {γ : D | hdist (0 : E 1) ((γ : PO 1 1) • (0 : E 1)) ≤
      hdist (0 : E 1) (h₀ • (0 : E 1))}.Finite :=
    finite_nearStab hA' hI' hdisc _
  let T : Finset D := hfin.toFinset
  have hmemT : ∀ γ : D, γ ∈ T ↔
      hdist (0 : E 1) ((γ : PO 1 1) • (0 : E 1)) ≤ hdist (0 : E 1) (h₀ • (0 : E 1)) := by
    intro γ
    exact Set.Finite.mem_toFinset hfin
  -- the positive-displacement part of it
  let T' : Finset D := T.filter (fun γ => 0 < hdist (0 : E 1) ((γ : PO 1 1) • (0 : E 1)))
  have hT'ne : T'.Nonempty := by
    refine ⟨⟨h₀, hh₀D⟩, ?_⟩
    simp only [T', Finset.mem_filter]
    exact ⟨(hmemT ⟨h₀, hh₀D⟩).mpr le_rfl, hh₀pos⟩
  obtain ⟨g', hg'T', hg'min⟩ :=
    Finset.exists_min_image T' (fun γ : D => hdist (0 : E 1) ((γ : PO 1 1) • (0 : E 1))) hT'ne
  refine ⟨(g' : PO 1 1), g'.2, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hg'T').2
  · intro h hhD hpos
    by_cases hle : hdist (0 : E 1) (((⟨h, hhD⟩ : D) : PO 1 1) • (0 : E 1)) ≤
        hdist (0 : E 1) (h₀ • (0 : E 1))
    · have hmem : (⟨h, hhD⟩ : D) ∈ T' := by
        simp only [T', Finset.mem_filter]
        exact ⟨(hmemT ⟨h, hhD⟩).mpr hle, hpos⟩
      have := hg'min ⟨h, hhD⟩ hmem
      exact this
    · have hg'T : g' ∈ T := (Finset.mem_filter.mp hg'T').1
      have hg'R : hdist (0 : E 1) ((g' : PO 1 1) • (0 : E 1)) ≤
          hdist (0 : E 1) (h₀ • (0 : E 1)) := (hmemT g').mp hg'T
      have hlt : hdist (0 : E 1) (h₀ • (0 : E 1)) <
          hdist (0 : E 1) (((⟨h, hhD⟩ : D) : PO 1 1) • (0 : E 1)) := not_le.mp hle
      exact le_trans hg'R (le_of_lt hlt)

end Work.Mostow
