import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.finite_translates_inter_compact

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

/-- If a point `p` is such that every isometry `g` fixing both boundary points `ξ`, `η` translates
`p` by exactly `|busemann ξ (g • 0)|`, then the elements of a discrete subgroup `Λ` fixing both
`ξ` and `η` with `|busemann ξ (· • 0)| ≤ R` are finite: each of them moves `p` by at most `R`, so
they all land in the compact hyperbolic ball of radius `R` about `p`, which a discrete subgroup
meets finitely. -/
theorem pairStabBusemannNearFinite (n : ℕ) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Λ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Λ))
    (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (p : E n)
    (hp : ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
      hdist p (g • p) = |busemann ξ (g • (0 : E n))|) (R : ℝ) :
    {γ : Λ | bd (γ : PO n 1) ξ = ξ ∧ bd (γ : PO n 1) η = η ∧
      |busemann ξ ((γ : PO n 1) • (0 : E n))| ≤ R}.Finite := by
  have hK : IsCompact {v : E n | hdist p v ≤ R} := hI.2.2.2.2.2.1 p R
  have hfin : {γ : Λ | (((fun u : E n => (γ : PO n 1) • u) '' ({p} : Set (E n))) ∩
      {v : E n | hdist p v ≤ R}).Nonempty}.Finite :=
    finite_translates_inter_compact n hA hI (Γ := Λ) hdisc
      (isCompact_singleton : IsCompact ({p} : Set (E n))) hK
  refine hfin.subset ?_
  rintro γ ⟨hbξ, hbη, hbR⟩
  exact ⟨(γ : PO n 1) • p, ⟨⟨p, rfl, rfl⟩, by
    show hdist p ((γ : PO n 1) • p) ≤ R
    rw [hp (γ : PO n 1) hbξ hbη]
    exact hbR⟩⟩

end Work.Mostow
