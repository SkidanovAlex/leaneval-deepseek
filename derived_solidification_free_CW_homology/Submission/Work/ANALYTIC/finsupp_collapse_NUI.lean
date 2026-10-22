import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

namespace Work.ANALYTIC

open _root_.LightCondensed
open Opposite

/-! ### Classification of the morphisms `∗ ⟶ ℕ∪{∞}`

The source `∗ = pt` is the one point light profinite set, so a morphism `u : ∗ ⟶ S` into a light
profinite set is determined by the point `u () ∈ S` (`ConcreteCategory.hom_ext`), and the point at
infinity of `ℕ∪{∞}` is exactly `LightCondensed.ι`.  These two observations classify the morphisms
`∗ ⟶ ℕ∪{∞}`: they are the finite points `ptAt (some m)` (`m : ℕ`) together with `ι`. -/

/-- Every morphism `u : ∗ ⟶ S` out of the one point light profinite set is the point map
`ptAt (u ())`. -/
lemma pt_eq_ptAt {S : LightProfinite.{0}} (u : Work.ATOM.pt ⟶ S) :
    u = Work.ATOM.ptAt (S := S) (u PUnit.unit) := by
  apply ConcreteCategory.hom_ext
  intro x
  rw [Work.ATOM.ptAt_apply]

/-- The point map at infinity of `ℕ∪{∞}` is `LightCondensed.ι`. -/
lemma ptAt_infty_eq_iota :
    (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty)
      (OnePoint.infty : ↥LightProfinite.NatUnionInfty)) = LightCondensed.ι := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- Classification of the morphisms `∗ ⟶ ℕ∪{∞}`: such a morphism is either the point at
infinity (`LightCondensed.ι`) or a finite point `ptAt (some m)`. -/
lemma eq_iota_or_exists_ptAt_some (u : Work.ATOM.pt ⟶ LightProfinite.NatUnionInfty) :
    u = LightCondensed.ι ∨
      ∃ m : ℕ, u = Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty) (OnePoint.some m) := by
  cases hv : u PUnit.unit with
  | none => exact Or.inl (by rw [pt_eq_ptAt u, hv]; exact ptAt_infty_eq_iota)
  | some m => exact Or.inr ⟨m, by rw [pt_eq_ptAt u, hv]; rfl⟩

/-- The generators `homFreeEquiv ∗ ℤ[ℕ∪{∞}] (zmap u)` of `ℤ[ℕ∪{∞}](∗)` (`u : ∗ ⟶ ℕ∪{∞}`) satisfy
no relations other than the evident one: a finite combination whose coefficients at all the finite
points `k ∈ ℕ` vanish is concentrated at the point `∞` (i.e. at `ι`).

Route: any `u : ∗ ⟶ ℕ∪{∞}` is `ptAt (u ())` (`ConcreteCategory.hom_ext`, `∗` is the one-point
set), and `ptAt ∞ = LightCondensed.ι`; then `Finsupp.induction` (or `Finsupp.sum` manipulations)
reduces the two sides.  No property of `ℤ[ℕ∪{∞}]` beyond this classification of the maps is used. -/
theorem finsupp_collapse_NUI (c : (Work.ATOM.pt ⟶ LightProfinite.NatUnionInfty) →₀ ℤ)
    (h : ∀ m : ℕ, c (Work.ATOM.ptAt (OnePoint.some m)) = 0) :
    c.sum (fun u n => n • Work.ATOM.homFreeEquiv Work.ATOM.pt
        (Work.ATOM.zfree LightProfinite.NatUnionInfty) (Work.ATOM.zmap u))
      = (c LightCondensed.ι) • Work.ATOM.homFreeEquiv Work.ATOM.pt
          (Work.ATOM.zfree LightProfinite.NatUnionInfty) (Work.ATOM.zmap LightCondensed.ι) := by
  classical
  -- `eq_iota_or_exists_ptAt_some` says that `c` is supported at `ι`, so it is a multiple of
  -- `Finsupp.single ι (c ι)`; the sum over a single generator is immediate.
  have hc : c = Finsupp.single LightCondensed.ι (c LightCondensed.ι) := by
    ext u
    by_cases hu : u = LightCondensed.ι
    · subst hu
      exact Finsupp.single_eq_same.symm
    · rw [Finsupp.single_eq_of_ne hu]
      rcases eq_iota_or_exists_ptAt_some u with hι | ⟨m, hm⟩
      · exact absurd hι hu
      · rw [hm]
        exact h m
  rw [hc, Finsupp.sum_single_index (by simp), Finsupp.single_eq_same]

end Work.ANALYTIC

/-- Convenience alias for `Work.ANALYTIC.Work.ANALYTIC.finsupp_collapse_NUI`, for callers that
refer to the lemma under the name `Work.ANALYTIC.finsupp_collapse_NUI`. -/
theorem finsupp_collapse_NUI (c : (Work.ATOM.pt ⟶ LightProfinite.NatUnionInfty) →₀ ℤ)
    (h : ∀ m : ℕ, c (Work.ATOM.ptAt (OnePoint.some m)) = 0) :
    c.sum (fun u n => n • Work.ATOM.homFreeEquiv Work.ATOM.pt
        (Work.ATOM.zfree LightProfinite.NatUnionInfty) (Work.ATOM.zmap u))
      = (c LightCondensed.ι) • Work.ATOM.homFreeEquiv Work.ATOM.pt
          (Work.ATOM.zfree LightProfinite.NatUnionInfty) (Work.ATOM.zmap LightCondensed.ι) :=
  Work.ANALYTIC.Work.ANALYTIC.finsupp_collapse_NUI c h
