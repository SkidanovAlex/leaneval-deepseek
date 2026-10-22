import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ATOM.Toolkit

open CategoryTheory LightProfinite

/-- The canonical point map `* ⟶ T'` followed by `π : T' ⟶ T` is the point map at the image
point: `ptAt t ≫ π = ptAt (π t)`. -/
lemma ptAt_comp {T' T : LightProfinite.{0}} (π : T' ⟶ T) (t : ↥T') :
    Work.ATOM.ptAt t ≫ π = Work.ATOM.ptAt (π t) := by
  ext ⟨⟩
  simp [Work.ATOM.ptAt]

/-- **The value of a descended morphism at a point.**  If `ψ : ℤ[T] ⟶ M` is obtained from
`φ : ℤ[T'] ⟶ M` by descent along a morphism `π : T' ⟶ T` (i.e. `zmap π ≫ ψ = φ`), then evaluating
`ψ` at the image `π t` of a point `t : T'` gives the same as evaluating `φ` at `t`.  Proof: apply
`Work.ATOM.homFreeEquiv` at the point `Work.ATOM.pt` and use `Work.ATOM.homFreeEquiv_naturality`
(from `Submission/Work/ATOM/zdesc.lean`), together with `ptAt t ≫ π = ptAt (π t)`. -/
theorem homFreeEquiv_value_of_descend {T' T : LightProfinite.{0}} (π : T' ⟶ T)
    {M : LightCondAb} (φ : Work.ATOM.zfree T' ⟶ M) (ψ : Work.ATOM.zfree T ⟶ M)
    (h : Work.ATOM.zmap π ≫ ψ = φ) (t : ↥T') :
    Work.ATOM.homFreeEquiv Work.ATOM.pt M
        (Work.ATOM.zmap (Work.ATOM.ptAt (π t)) ≫ ψ) =
      Work.ATOM.homFreeEquiv Work.ATOM.pt M (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ φ) := by
  -- Both arguments of `homFreeEquiv` are the *same* morphism `ℤ[*] ⟶ M`: pulling `φ = zmap π ≫ ψ`
  -- back along `ℤ[ptAt t]` and using functoriality of `zmap` together with `ptAt t ≫ π = ptAt (π t)`
  -- gives `zmap (ptAt t) ≫ φ = zmap (ptAt (π t)) ≫ ψ`.
  have hmor : Work.ATOM.zmap (Work.ATOM.ptAt (π t)) ≫ ψ
      = Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ φ := by
    rw [← h, ← Category.assoc, ← Functor.map_comp]
    rw [← ptAt_comp π t]
  exact congrArg (Work.ATOM.homFreeEquiv Work.ATOM.pt M) hmor

end Work.ATOM.Toolkit
