import Mathlib
import Submission.Work.Smooth.Plane.All

namespace Work.CountedPinch

/-- **A covering of `D ∩ F` by finitely many disjoint embedded arcs of `F` is a transversality
witness.**

`TransversePlane P D` is the statement that `F ∩ D` is the union of finitely many pairwise disjoint
simple closed curves of `F` and embedded arcs of `F`, each lying in `D`.  Here the first family is
taken *empty* and the second family is the given family of arcs `a : Fin n → C(ArcInterval, R3)`,
which lies in `D` (`hmemD`) and on the surface `F = P.carrier` (`hmem`), is embedded (`hinj`) and
pairwise disjoint (`hdisj`), and *covers* `D ∩ F` (`hcov`).  All the conditions are then immediate:
the ones about closed curves are vacuous, and the remaining ones are exactly the hypotheses. -/
theorem transversePlane_of_arcs {P : Work.CoreTopology.ParamTorus} {D : Set LeanEval.KnotTheory.PardonDistortion.R3} {n : ℕ}
    (a : Fin n → C(Work.Smooth.Plane.ArcInterval, LeanEval.KnotTheory.PardonDistortion.R3))
    (hinj : ∀ j : Fin n, Function.Injective (a j))
    (hmem : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ P.carrier)
    (hmemD : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ D)
    (hdisj : Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j')))
    (hcov : ∀ x : LeanEval.KnotTheory.PardonDistortion.R3, x ∈ D → x ∈ P.carrier →
      ∃ j : Fin n, x ∈ Set.range (a j)) :
    Work.Smooth.Plane.TransversePlane P D := by
  refine ⟨Empty, inferInstance, fun i => i.elim, Fin n, inferInstance, a,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact i.elim
  · intro i; exact i.elim
  · intro i; exact i.elim
  · exact hinj
  · exact hmemD
  · exact hmem
  · exact hdisj
  · intro j i; exact i.elim
  · intro x hx hxP; exact Or.inr (hcov x hx hxP)

end Work.CountedPinch
