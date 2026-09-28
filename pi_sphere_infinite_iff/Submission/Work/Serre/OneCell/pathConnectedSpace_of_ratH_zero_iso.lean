import Mathlib
import Submission.Work.Serre.OneCell.Prelim
import Submission.Work.Serre.pathConnectedSpace_of_ratAcyclic

/-!
# `H₀(X;ℚ) ≅ ℚ` forces `X` to be path connected

Mathlib computes the zeroth singular homology with coefficients in a ring `R` as the free
`R`-module on the set of path components, `TopCat.singularHomology₀Iso :
H₀(X;R) ≅ ∐ (fun _ : ZerothHomotopy X ↦ R)`.  The point of this file is the converse direction
of `Work.Serre.ratH_zero_of_pathConnected`: if that free module is isomorphic to `ℚ` (i.e. it has a
single generator), then there is exactly one path component, i.e. `X` is path connected.

The mathematical content is the elementary algebraic fact that a coproduct `∐_I ℚ` of copies of the
field `ℚ` is isomorphic to `ℚ` only when the index type `I` is a singleton:

* if `I` is empty the coproduct is the initial object, so all endomorphisms of `∐_I ℚ` are equal
  (there are no coproduct injections to separate them), in particular `𝟙 = 0`, whence `ℚ` would be a
  subsingleton;
* if `i ≠ j` are two elements, the two elements `Σ.ι i 1` and `Σ.ι j 1` of `∐_I ℚ` are separated by
  the two projections `Σ.π i`, `Σ.π j` (`= 1` and `= 0`), while an isomorphism `Ψ : ∐_I ℚ ≅ ℚ`
  forces them to be linearly dependent (`ℚ` is one-dimensional): writing `a = Ψ (Σ.ι i 1) ≠ 0` and
  `b = Ψ (Σ.ι j 1)` we get `Σ.ι j 1 = (b / a) • Σ.ι i 1` by injectivity, and applying `Σ.π i`
  yields the contradiction `0 = b / a`.

The main theorem is the specialisation to `I = ZerothHomotopy X`, using
`pathConnectedSpace_iff_zerothHomotopy`.
-/

namespace Work.Serre.OneCell

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

noncomputable section

open Work.Serre

/-- **A coproduct of copies of `ℚ` is isomorphic to `ℚ` only over a singleton index set.**

This is the algebraic heart of `pathConnectedSpace_of_ratH_zero_iso`: it is applied to the index
type `ZerothHomotopy X`. -/
theorem nonempty_and_subsingleton_of_sigma_iso_self {I : Type}
    (Ψ : (∐ fun _ : I => h0Coeff) ≅ h0Coeff) : Nonempty I ∧ Subsingleton I := by
  classical
  refine ⟨?_, ?_⟩
  · -- `I` is not empty: if it were, `∐_I ℚ` would be the initial object, so `𝟙 = 0` on it, and
    -- conjugating by the isomorphism would give `𝟙 = 0` on `ℚ`.
    by_contra hne
    rw [not_nonempty_iff] at hne
    have hzero : (𝟙 (∐ fun _ : I => h0Coeff)) = 0 := by
      apply Sigma.hom_ext
      intro i
      exact isEmptyElim i
    have hΨhom : Ψ.hom = 0 := by
      rw [← Category.id_comp Ψ.hom, hzero, zero_comp]
    have hone : (𝟙 h0Coeff) = 0 := by
      rw [← Ψ.inv_hom_id, hΨhom, comp_zero]
    haveI : Subsingleton ↥h0Coeff := subsingleton_of_id_eq_zero hone
    exact one_ne_zero (Subsingleton.elim (1 : ↥h0Coeff) 0)
  · -- `I` has at most one element: two distinct indices would give two linearly independent
    -- elements of the one-dimensional space `∐_I ℚ ≅ ℚ`.
    rw [subsingleton_iff]
    intro i j
    by_contra hij
    set e : ↥(∐ fun _ : I => h0Coeff) ≃ₗ[ℚ] ↥h0Coeff := Ψ.toLinearEquiv
    let xi : ↥(∐ fun _ : I => h0Coeff) := (Sigma.ι (fun _ : I => h0Coeff) i) (1 : ℚ)
    let xj : ↥(∐ fun _ : I => h0Coeff) := (Sigma.ι (fun _ : I => h0Coeff) j) (1 : ℚ)
    -- the two "coordinate" functionals separate the two generators
    have hdiag : ∀ k : I,
        (Sigma.π (fun _ : I => h0Coeff) k) ((Sigma.ι (fun _ : I => h0Coeff) k) (1 : ℚ)) =
          (1 : ℚ) := by
      intro k
      have h := congrArg (fun (f : h0Coeff ⟶ h0Coeff) => (ConcreteCategory.hom f) (1 : ℚ))
        (Sigma.ι_π_eq_id (fun _ : I => h0Coeff) k)
      rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
      exact h
    have hpi : (Sigma.π (fun _ : I => h0Coeff) i) xi = (1 : ℚ) := hdiag i
    have hpjj : (Sigma.π (fun _ : I => h0Coeff) j) xj = (1 : ℚ) := hdiag j
    have hpj : (Sigma.π (fun _ : I => h0Coeff) i) xj = 0 := by
      have h := congrArg (fun (f : h0Coeff ⟶ h0Coeff) => (ConcreteCategory.hom f) (1 : ℚ))
        (Sigma.ι_π_of_ne (fun _ : I => h0Coeff) (Ne.symm hij))
      rw [ConcreteCategory.comp_apply] at h
      simpa using h
    -- both generators are nonzero, hence have nonzero image under the isomorphism
    have hei : e xi ≠ 0 := by
      intro h
      have hxi : xi = 0 := e.injective (by rw [h, map_zero])
      rw [hxi, map_zero] at hpi
      exact one_ne_zero hpi.symm
    have hej : e xj ≠ 0 := by
      intro h
      have hxj : xj = 0 := e.injective (by rw [h, map_zero])
      rw [hxj, map_zero] at hpjj
      exact one_ne_zero hpjj.symm
    -- in the one-dimensional target the two images are linearly dependent
    have key : (e xj / e xi) • xi = xj := by
      apply e.injective
      rw [map_smul, smul_eq_mul]
      exact div_mul_cancel₀ (e xj) hei
    -- but the first coordinate functional kills `xj` and evaluates to `e xj / e xi` on the left
    have h3 := congrArg (ConcreteCategory.hom (Sigma.π (fun _ : I => h0Coeff) i)) key
    rw [map_smul, hpi, hpj, smul_eq_mul, mul_one] at h3
    exact hej (by rw [← div_mul_cancel₀ (e xj) hei, h3, zero_mul])

/-- **`H₀(X;ℚ) ≅ ℚ` implies that `X` has a single path component.**

Mathlib's `TopCat.singularHomology₀Iso` identifies `H₀(X;ℚ)` with the coproduct of copies of `ℚ`
indexed by the path components of `X`; the hypothesis of the theorem therefore says that this
coproduct is isomorphic to `ℚ`, and `nonempty_and_subsingleton_of_sigma_iso_self` applies. -/
theorem nonempty_and_subsingleton_zerothHomotopy_of_h0_iso {X : Type} [TopologicalSpace X]
    (h : Nonempty (ratH (TopCat.of X) 0 ≅ h0Coeff)) :
    Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) := by
  obtain ⟨Φ⟩ := h
  set Ψ : (∐ fun _ : ZerothHomotopy (TopCat.of X) => h0Coeff) ≅ h0Coeff :=
    (h0Iso (TopCat.of X)).symm ≪≫ Φ with hΨ
  exact nonempty_and_subsingleton_of_sigma_iso_self Ψ

/-- **`H₀(X;ℚ) ≅ ℚ` forces `X` to be path connected.**  The zeroth rational homology of `X` is
the free `ℚ`-module on `π₀(X)`; being one-dimensional (isomorphic to `ℚ`) it therefore has exactly
one generator, i.e. `X` has exactly one path component. -/
theorem pathConnectedSpace_of_ratH_zero_iso {X : Type} [TopologicalSpace X]
    (h : Nonempty (Work.Serre.ratH (TopCat.of X) 0 ≅ ModuleCat.of ℚ ℚ)) :
    PathConnectedSpace X := by
  exact pathConnectedSpace_iff_zerothHomotopy.mpr
    (nonempty_and_subsingleton_zerothHomotopy_of_h0_iso h)

end

end Work.Serre.OneCell
