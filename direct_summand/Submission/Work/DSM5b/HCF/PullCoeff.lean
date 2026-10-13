/-
# The "pullback" coefficient system of a graded module, on the `ULift` index type

The chart Čech complex `Work.DSCOH.chartCech ℳ` of a graded module over `R[X_0,…,X_{n-1}]` is
indexed by the *finsets* `S ⊆ Fin n` (products over the `(q+1)`-element subsets).  The sorted
tuple complex `Work.DSM5b.stcComplex 𝒜` of a coefficient system is indexed by the *increasing
tuples* of a linearly ordered index type.

To compare the two for the Rees module `ℳ = reesGr t` we need the coefficient system

  `pullCoeff ℳ : CoeffSys R (ULift (Fin n))`,  `S ↦ degZero ℳ (S.image down)`,

whose values are degree-zero parts of chart localisations of `ℳ` (these live in the universe of
`R` and `ℳ`, which is why the index type has to be `ULift.{u} (Fin n)`).

It is constructed as a sub-system (`Work.DSM5b.CoeffSys.SubSys.toCoeff`) of the coefficient system
of chart localisations `S ↦ locAt ℳ (S.image down)`, so that its restriction maps are the
restrictions of the `ℳ`-localisation maps `Work.DSCOH.resAt`.
-/
import Mathlib
import Submission.Work.DSM5b.HCF.ReesDefs
import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSM5b.HCF.SubSys
import Submission.Work.DSCOH.resAt_degZero
import Submission.Work.DSCOH.resAt_id
import Submission.Work.DSCOH.resAt_comp

open MvPolynomial Polynomial

namespace Work.DSCOH

/-- The chart localisation maps `resAt` depend on the inclusion only through the inclusion. -/
lemma resAt_congr' {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {S T : Finset (Fin n)} {h h' : S ⊆ T} :
    resAt (A := A) (n := n) (M := M) h = resAt (A := A) (n := n) (M := M) h' := by
  unfold resAt LocalizedModule.liftOfLE IsLocalizedModule.liftOfLE
  congr 1

end Work.DSCOH

namespace Work.DSM5b.HCF

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The coefficient system of chart localisations of a graded module `ℳ`, on the finite subsets of
`ULift.{u} (Fin n)`: the value at `S` is `ℳ[1/X_{S.image down}]`. -/
noncomputable def locAtCoeff (M : Type u) [AddCommGroup M] [Module R M]
    [Module (Work.DSCOH.Poly R n) M] [IsScalarTower R (Work.DSCOH.Poly R n) M] :
    Work.DSM5b.CoeffSys R (ULift.{u} (Fin n)) where
  M S := Work.DSCOH.locAt (A := R) (n := n) (M := M) (S.image ULift.down)
  inst₁ := fun _ => inferInstance
  inst₂ := fun _ => inferInstance
  res := fun {_ _} h => (Work.DSCOH.resAt (A := R) (n := n) (M := M)
    (Finset.image_subset_image (f := ULift.down) h)).restrictScalars R
  res_self S := by
    refine LinearMap.ext fun x => ?_
    rw [Work.DSCOH.resAt_congr' (A := R) (n := n) (M := M)
      (h := Finset.image_subset_image (f := ULift.down) (le_refl S))
      (h' := le_refl (S.image ULift.down))]
    rw [Work.DSCOH.resAt_id]
    rfl
  res_comp {S T V} h₁ h₂ := by
    have key : (Work.DSCOH.resAt (A := R) (n := n) (M := M)
          (Finset.image_subset_image (f := ULift.down) (h₁.trans h₂) :
            S.image ULift.down ⊆ V.image ULift.down)) =
        ((Work.DSCOH.resAt (A := R) (n := n) (M := M)
            (Finset.image_subset_image (f := ULift.down) h₂)).comp
          (Work.DSCOH.resAt (A := R) (n := n) (M := M)
            (Finset.image_subset_image (f := ULift.down) h₁))) := by
      rw [Work.DSCOH.resAt_congr' (A := R) (n := n) (M := M)
        (h := Finset.image_subset_image (f := ULift.down) (h₁.trans h₂))
        (h' := ((Finset.image_subset_image (f := ULift.down) h₁).trans
          (Finset.image_subset_image (f := ULift.down) h₂) :
            S.image ULift.down ⊆ V.image ULift.down))]
      rw [Work.DSCOH.resAt_comp]
    have key2 := congrArg (LinearMap.restrictScalars R) key
    rw [LinearMap.restrictScalars_comp] at key2
    exact key2.symm

/-- The sub-system of the degree-zero parts of the chart localisations. -/
noncomputable def degZeroSubSys {M : Type u} [AddCommGroup M] [Module R M]
    [Module (Work.DSCOH.Poly R n) M] [IsScalarTower R (Work.DSCOH.Poly R n) M]
    (ℳ : ℕ → Submodule R M) [SetLike.GradedSMul (Work.DSCOH.homSub R n) ℳ] :
    Work.DSM5b.CoeffSys.SubSys (locAtCoeff (n := n) (R := R) M) where
  N S := Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ (S.image ULift.down)
  res_mem := by
    intro S T h x hx
    exact Work.DSCOH.resAt_degZero (A := R) (n := n) (M := M) (ℳ := ℳ)
      (Finset.image_subset_image (f := ULift.down) h) x hx

/-- The **pullback coefficient system** of a graded module `ℳ`: on the finite subsets of
`ULift.{u} (Fin n)`, the value at `S` is the degree-zero part of the chart localisation of `ℳ` at
the finset `S.image ULift.down ⊆ Fin n`, with the restriction maps induced by `Work.DSCOH.resAt`. -/
noncomputable def pullCoeff {M : Type u} [AddCommGroup M] [Module R M]
    [Module (Work.DSCOH.Poly R n) M] [IsScalarTower R (Work.DSCOH.Poly R n) M]
    (ℳ : ℕ → Submodule R M) [SetLike.GradedSMul (Work.DSCOH.homSub R n) ℳ] :
    Work.DSM5b.CoeffSys R (ULift.{u} (Fin n)) :=
  Work.DSM5b.CoeffSys.SubSys.toCoeff (locAtCoeff (n := n) (R := R) (M := M))
    (degZeroSubSys (n := n) (R := R) ℳ)

end Work.DSM5b.HCF
