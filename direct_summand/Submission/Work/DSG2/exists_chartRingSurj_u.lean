import Mathlib
import Submission.Work.DSG2.Defs
import Submission.Work.DSG2.ExistsImmersionAux.Defs
import Submission.Work.DSG2.Psi_Phi
import Submission.Work.DSG2.ChartRingDefs

/-!
# DSG2: a surjection from the chart ring of `ℙⁿ` onto `A[y_0,…,y_{n-1}]`, universe-general

`Work.DSG2.chartRing A n i` is the coordinate ring of the `i`-th standard affine chart
`D₊(xᵢ) ⊆ ℙⁿ_A`, the degree-zero part of the localization of `A[x₀,…,xₙ]` at the powers of
`Xᵢ`.  The dehomogenization map `Work.DSG2.Psi` (dehomogenizing `Xᵢ ↦ 1`) is a surjection
onto `A[y_0,…,y_{n-1}]`, with right inverse `Work.DSG2.Phi` (`Psi ∘ Phi = id`), and it is a map
of `A`-algebras: it sends the constant `chartAto a` of the chart ring to `C a`.

This is the universe-general companion of the pinned `Work.DSG2.exists_chartRingSurj`: the
binders `(A : Type*)` below allow instantiating `A` at an arbitrary universe, which the
`A : Type = Type 0` version cannot.
-/

open MvPolynomial HomogeneousLocalization

namespace Work.DSG2

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `Psi ∘ Phi = id`, at an arbitrary universe: `Psi` is a left inverse of `Phi`, hence in
particular surjective. -/
theorem Psi_Phi_u_aux (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (g : MvPolynomial (Fin n) A) : Psi A n i (Phi A n i g) = g := by
  have h : (Psi A n i).comp (Phi A n i) = RingHom.id (MvPolynomial (Fin n) A) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, RingHom.id_apply] using Psi_Phi_C A n i a
    · intro k
      simpa only [RingHom.comp_apply, RingHom.id_apply] using Psi_Phi_X A n i k
  exact RingHom.congr_fun h g

/-- The chart structure map `chartAto` coincides with the map `AtoAway` used in the
dehomogenization set-up, at an arbitrary universe. -/
theorem chartAto_eq_AtoAway_u_aux (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) :
    chartAto A n i = AtoAway A n i := by
  have hA : AtoA0 A n = algebraMap A (chartGrading A n 0) := by ext a; rfl
  ext a
  simp only [chartAto, AtoAway, hA]

/-- The dehomogenization map `Psi` sends the constants of the chart ring to constants. -/
theorem Psi_chartAto_u_aux (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) (a : A) :
    Psi A n i (chartAto A n i a) = MvPolynomial.C a := by
  rw [chartAto_eq_AtoAway_u_aux A n i, ← Psi_Phi_C A n i a, Phi, MvPolynomial.eval₂Hom_C]
  rfl

theorem exists_chartRingSurj_u (A : Type*) [CommRing A] (n : ℕ) (i : Fin (n + 1)) :
    ∃ ψ₀ : Work.DSG2.chartRing A n i →+* MvPolynomial (Fin n) A,
      Function.Surjective ψ₀ ∧ ∀ a : A, ψ₀ (Work.DSG2.chartAto A n i a) = MvPolynomial.C a := by
  exact ⟨Psi A n i, fun q => ⟨Phi A n i q, Psi_Phi_u_aux A n i q⟩, Psi_chartAto_u_aux A n i⟩

end Work.DSG2
