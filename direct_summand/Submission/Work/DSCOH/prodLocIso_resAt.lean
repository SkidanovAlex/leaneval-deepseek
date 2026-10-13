import Mathlib
import Submission.Work.DSCOH.ProdLocIsoBase

namespace Work.DSCOH

/-- The structure map `resAt` on an explicit fraction `m/s`: it only replaces the submonoid
`subS S` by the larger submonoid `subS T`.  This is the general-module version of
`Work.DSCOH.resAt_mk` (which is stated for `M = Poly A n`). -/
lemma resAt_mk_general {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {S T : Finset (Fin n)} (h : S ⊆ T) (m : M) (s : subS (A := A) S) :
    resAt (A := A) (n := n) (M := M) h (LocalizedModule.mk m s) =
      LocalizedModule.mk m ⟨(s : Poly A n), subS_mono (A := A) h s.2⟩ := by
  rw [IsLocalizedModule.mk_eq_mk', resAt, LocalizedModule.liftOfLE,
    IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

/-- `prodLocIso` is natural with respect to the restriction maps `resAt`: identifying the
localization of the finite product `∏_{j : Fin r} S` with the product of the localizations
commutes with inverting more variables. -/
theorem prodLocIso_resAt {A : Type*} [CommRing A] {n : ℕ} {r : ℕ}
    {S T : Finset (Fin n)} (h : S ⊆ T)
    (x : LocalizedModule (subS (A := A) S) (Fin r → Poly A n)) :
    prodLocIso (A := A) (n := n) T r (resAt (A := A) (n := n) (M := Fin r → Poly A n) h x)
      = fun j => resAt (A := A) (n := n) (M := Poly A n) h
          ((prodLocIso (A := A) (n := n) S r x) j) := by
  -- Every element of a localization is a fraction `g/s`, so it suffices to compare the two
  -- `Poly A n`-linear maps on the generators `LocalizedModule.mk g s`.
  induction x using LocalizedModule.induction_on with
  | _ g s =>
    rw [resAt_mk_general h, prodLocIso_mk, prodLocIso_mk]
    funext j
    simp only []
    rw [resAt_mk_general h]

end Work.DSCOH
