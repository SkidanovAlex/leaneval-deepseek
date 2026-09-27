import Mathlib
import Submission.Work.EQ.tailP_bdd_near_puncture

namespace Work.EQ

open Filter _root_.Topology
open Complex
open Classical

noncomputable section

/-- **The branch label of a step is constant on a preconnected parameter set.**  Generalises
`Work.EQ.label_dichotomy` (stated there for a complex parameter domain) to an arbitrary
topological parameter space `X`, which is what a path `ℝ → ChainData` needs.

If `P`, `Q` are continuous on a preconnected `D`, satisfy the equichordal relation pointwise, and
the backward radicand of `Q` lies in the slit plane on `D`, then the backward branch `P = -Q ±
(Q - O₁)/ρ'` used at `P` is the same sign `s` at every point of `D`. -/
theorem label_dichotomy_cont {a : ℝ} {X : Type*} [TopologicalSpace X] {D : Set X} {P Q : X → ℂ × ℂ}
    (hD : IsPreconnected D) (hP : ContinuousOn P D) (hQ : ContinuousOn Q D)
    (hrel : ∀ ζ ∈ D, EqRelC a (P ζ) (Q ζ))
    (hslit : ∀ ζ ∈ D, ((Q ζ).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (Q ζ).2 ^ 2 ∈ Complex.slitPlane) :
    (∀ ζ ∈ D, P ζ = invBranch a true (Q ζ)) ∨ (∀ ζ ∈ D, P ζ = invBranch a false (Q ζ)) := by
  haveI : PreconnectedSpace D := Subtype.preconnectedSpace hD
  have hPc : Continuous (fun ζ : D => P (ζ : X)) := hP.domRestrict
  have hQc : Continuous (fun ζ : D => Q (ζ : X)) := hQ.domRestrict
  have hgc : ∀ s : Bool, Continuous (fun ζ : D => invBranch a s (Q (ζ : X))) := by
    intro s
    refine continuous_iff_continuousAt.mpr fun ζ => ?_
    have hinner : ContinuousAt (fun x : D => Q (x : X)) ζ := hQc.continuousAt
    have hout : ContinuousAt (invBranch a s) ((fun x : D => Q (x : X)) ζ) :=
      (analyticAt_invBranch (a := a) (s := s) (hslit (ζ : X) ζ.2)).continuousAt
    exact hout.comp (f := fun x : D => Q (x : X)) (x := ζ) hinner
  set A : Set D := {ζ | P (ζ : X) = invBranch a true (Q (ζ : X))} with hAdef
  set B : Set D := {ζ | P (ζ : X) = invBranch a false (Q (ζ : X))} with hBdef
  have hAcl : IsClosed A := isClosed_eq hPc (hgc true)
  have hBcl : IsClosed B := isClosed_eq hPc (hgc false)
  have hsub : (Set.univ : Set D) ⊆ A ∪ B := by
    intro ζ _
    have hne := Complex.slitPlane_ne_zero (hslit (ζ : X) ζ.2)
    have hne' : bsq (subO1 a (Q (ζ : X))) ≠ 0 := by simpa only [subO1, bsq] using hne
    rcases eqRelC_solutions (hrel (ζ : X) ζ.2) hne' with hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
  have hdisj : (Set.univ : Set D) ∩ (A ∩ B) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ζ hz => ?_
    obtain ⟨-, hzA, hzB⟩ := hz
    exact invBranch_true_ne_false_of_slit (hslit (ζ : X) ζ.2) (hzA.symm.trans hzB)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_univ : IsPreconnected (Set.univ : Set D)) A B hAcl hBcl hsub hdisj)
    with hh | hh
  · left; intro ζ hζ; exact hh (Set.mem_univ (⟨ζ, hζ⟩ : D))
  · right; intro ζ hζ; exact hh (Set.mem_univ (⟨ζ, hζ⟩ : D))

end

end Work.EQ
