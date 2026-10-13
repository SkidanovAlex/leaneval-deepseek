import Mathlib
import Submission.Work.DSG2.ChartRingDefs

/-!
# DSG2: the dehomogenization maps `Phi` and `Psi` of the standard charts of `ℙⁿ`

`Work.DSG2.Phi : A[Y₀,…,Y_{n-1}] →+* Away 𝒜 (X i)` sends `Y_k` to `X_{i.succAbove k}/X_i`,
and `Work.DSG2.Psi` is induced by the dehomogenization `X_i ↦ 1`, `X_j ↦ Y_{j≠i}`.

Here we prove the compatibility `Psi (Phi g) = g`, i.e. that `Psi` is a left inverse of
`Phi`; this is one half of the statement that `Phi` is an isomorphism onto the standard
chart ring of `ℙⁿ`.
-/

open MvPolynomial HomogeneousLocalization

universe u

namespace Work.DSG2

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `Psi` is the composite of `dehomLift` with the coercion of a homogeneous localization
element to the ordinary localization, i.e. it is `dehomLift` applied to `z.val`. -/
theorem Psi_apply (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (z : Away (chartGrading A n) (MvPolynomial.X i)) :
    Psi A n i z = dehomLift A n i z.val := by
  rw [Psi, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]

/-- `dehomLift` sends a basic fraction `a / (X i)^j` of the localization away from `X i` to the
dehomogenization `dehom a` of its numerator. -/
theorem dehomLift_mk (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (a : MvPolynomial (Fin (n + 1)) A) (j : ℕ) :
    dehomLift A n i (Localization.mk a ⟨MvPolynomial.X i ^ j, j, rfl⟩) = dehom A n i a := by
  rw [dehomLift]
  rw [Localization.awayLift_mk (dehom A n i) (MvPolynomial.X i) a 1
    (dehom_X_self_mul_one A n i) j]
  simp

/-- `Psi ∘ Phi` fixes the constants. -/
theorem Psi_Phi_C (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) (a : A) :
    Psi A n i (Phi A n i (MvPolynomial.C a)) = MvPolynomial.C a := by
  rw [Phi, MvPolynomial.eval₂Hom_C, Psi_apply, val_AtoAway, dehomLift_algebraMap, dehom,
    MvPolynomial.eval₂Hom_C]

/-- `Psi ∘ Phi` fixes the coordinate functions `Y_k = X_{i.succAbove k} / X_i`. -/
theorem Psi_Phi_X (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) (k : Fin n) :
    Psi A n i (Phi A n i (MvPolynomial.X k)) = MvPolynomial.X k := by
  rw [Phi, MvPolynomial.eval₂Hom_X', Psi_apply, e, HomogeneousLocalization.Away.val_mk,
    dehomLift_mk, dehom_succAbove]

theorem Psi_Phi (A : Type) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (g : MvPolynomial (Fin n) A) :
    Work.DSG2.Psi A n i (Work.DSG2.Phi A n i g) = g := by
  have h : (Psi A n i).comp (Phi A n i) = RingHom.id (MvPolynomial (Fin n) A) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, RingHom.id_apply] using Psi_Phi_C A n i a
    · intro k
      simpa only [RingHom.comp_apply, RingHom.id_apply] using Psi_Phi_X A n i k
  exact RingHom.congr_fun h g

end Work.DSG2
