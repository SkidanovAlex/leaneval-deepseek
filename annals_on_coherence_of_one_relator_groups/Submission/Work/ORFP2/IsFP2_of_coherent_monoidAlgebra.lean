
import Mathlib
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.CosetProj
import Submission.Work.ORFP2.Descent
import Submission.Work.ORFP2.range_augMapA_eq_augIdeal

set_option autoImplicit false
set_option linter.style.haveILetI false

open MonoidAlgebra

namespace Work.ORFP2

/-- The transfer `coherence of k[G] ⟹ FP₂ of a finitely generated subgroup`: if every finitely
generated (left) ideal of `k[G]` is finitely presented, then every finitely generated subgroup
`H ≤ G` is of type `FP₂` over `k`. -/
theorem IsFP2_of_coherent_monoidAlgebra (k : Type*) [CommRing k] (G : Type*) [Group G]
    (H : Subgroup G) (hH : H.FG)
    (h : ∀ I : Ideal (MonoidAlgebra k G), I.FG → Module.FinitePresentation (MonoidAlgebra k G) I) :
    IsFP2 k H := by
  classical
  have hfgH : Group.FG ↥H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨S, hS⟩ := Group.isMulFG_iff.mp hfgH
  have hIfg : (LinearMap.range (augMapB k G H S)).FG := by
    rw [show LinearMap.range (augMapB k G H S)
        = Submodule.span (MonoidAlgebra k G)
            (Set.range fun s : S => MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) from
      Finsupp.range_linearCombination (MonoidAlgebra k G)]
    exact Submodule.fg_span (Set.finite_range _)
  haveI hfpI : Module.FinitePresentation (MonoidAlgebra k G) (LinearMap.range (augMapB k G H S)) :=
    h _ hIfg
  have hK : (LinearMap.ker (augMapB k G H S)).FG := by
    let l : (S →₀ MonoidAlgebra k G) →ₗ[MonoidAlgebra k G] (LinearMap.range (augMapB k G H S)) :=
      (augMapB k G H S).codRestrict _ (fun x => LinearMap.mem_range_self _ x)
    have hl : Function.Surjective l := by
      intro y
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩
    have hker : LinearMap.ker l = LinearMap.ker (augMapB k G H S) := by
      ext x
      simp [l, LinearMap.mem_ker]
    have h1 := Module.FinitePresentation.fg_ker l hl
    rwa [hker] at h1
  have hN : (LinearMap.ker (augMapA k H S)).FG :=
    fg_ker_augMapA_of_fg_ker_augMapB k H S hK
  have hrangeA : LinearMap.range (augMapA k H S) = augIdeal k H :=
    range_augMapA_eq_augIdeal k H S hS
  haveI : Module.FinitePresentation (MonoidAlgebra k H) (S →₀ MonoidAlgebra k H) := inferInstance
  change Module.FinitePresentation (MonoidAlgebra k H) (augIdeal k H)
  rw [← hrangeA]
  let lA : (S →₀ MonoidAlgebra k H) →ₗ[MonoidAlgebra k H] (LinearMap.range (augMapA k H S)) :=
    (augMapA k H S).codRestrict _ (fun x => LinearMap.mem_range_self _ x)
  have hlA : Function.Surjective lA := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  have hkerA : LinearMap.ker lA = LinearMap.ker (augMapA k H S) := by
    ext x
    simp [lA, LinearMap.mem_ker]
  refine Module.finitePresentation_of_surjective lA hlA ?_
  rwa [hkerA]

end Work.ORFP2
