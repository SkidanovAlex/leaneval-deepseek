import Mathlib
import Submission.Work.DSCOH.Basic

namespace Work.DSCOH

theorem resAt_comp {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {S T U : Finset (Fin n)} (h₁ : S ⊆ T) (h₂ : T ⊆ U) :
    resAt (A := A) (n := n) (M := M) (h₁.trans h₂) =
      (resAt (A := A) (n := n) (M := M) h₂).comp (resAt (A := A) (n := n) (M := M) h₁) := by
  -- Both sides are `Poly A n`-linear maps defined on the localization at `S`; it suffices to
  -- check that they agree after precomposition with `M → M[1/X_S]`.
  have hunit : ∀ x : subS (A := A) S,
      IsUnit (algebraMap (Poly A n)
        (Module.End (Poly A n) (locAt (A := A) (M := M) U)) x) :=
    fun x => IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (subS (A := A) U) M)
      ⟨x.1, subS_mono (A := A) (h₁.trans h₂) x.2⟩
  refine IsLocalizedModule.ext (S := subS (A := A) S)
    (f := LocalizedModule.mkLinearMap (subS (A := A) S) M) hunit ?_
  ext m
  -- `resAt h` sends the image of `m` to the image of `m`, so the composite is the same map.
  simp only [LinearMap.comp_apply, resAt, LocalizedModule.liftOfLE,
    IsLocalizedModule.liftOfLE_apply]

end Work.DSCOH
