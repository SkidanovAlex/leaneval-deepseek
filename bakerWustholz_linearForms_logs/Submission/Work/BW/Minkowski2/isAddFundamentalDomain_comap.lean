import Mathlib
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.Minkowski2.mem_latOf_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Preimage of a fundamental domain under an injective endomorphism

Let `T : ℝᵈ → ℝᵈ` be an injective (hence bijective) `ℝ`-linear endomorphism and let
`D ⊆ ℝᵈ` be a fundamental domain for the standard lattice `ℤᵈ = latOf 1`.  Then

* `T ⁻¹' D` is a fundamental domain for the pullback lattice `T ⁻¹' ℤᵈ` (the `comap` of
  `latOf 1` along `T`), with respect to Lebesgue measure, and
* that pullback lattice is countable (it is a discrete `ℤ`-lattice, being the image of `ℤᵈ`
  under the linear bijection `T⁻¹`).

The proof is a direct application of `MeasureTheory.IsAddFundamentalDomain.preimage_of_equiv`:
`T` is quasi-measure-preserving for Lebesgue measure (it has nonzero determinant), and the
inverse of `T` gives a bijection between `ℤᵈ` and `T ⁻¹' ℤᵈ` which is compatible with the
translations.  The countability is then transferred along the same bijection.
-/

namespace Work.BW.Minkowski2

open MeasureTheory Matrix Module

/-- `Work.BW.latOf 1` is the `ℤ`-span of the standard basis of `ℝᵈ`. -/
lemma latOf_one_eq_span_basisFun {d : ℕ} :
    Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))
      = Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ) := by
  have hfun : (fun j : Fin d => fun i => (((1 : Matrix (Fin d) (Fin d) ℤ) i j : ℤ) : ℝ))
      = ⇑(Pi.basisFun ℝ (Fin d)) := by
    funext j i
    rw [Pi.basisFun_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  rw [Work.BW.latOf, hfun]

theorem isAddFundamentalDomain_comap {d : ℕ} (T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hT : Function.Injective T) :
    MeasureTheory.IsAddFundamentalDomain
        ((Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)).comap (T.restrictScalars ℤ)).toAddSubgroup
        (T ⁻¹' ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) MeasureTheory.volume
      ∧ Countable ((Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)).comap (T.restrictScalars ℤ)) := by
  classical
  -- The standard lattice is the `ℤ`-span of the standard basis.
  have hspan := latOf_one_eq_span_basisFun (d := d)
  -- The standard fundamental domain is a fundamental domain for `ℤᵈ`.
  have fund : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup
      (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) volume :=
    ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin d)) volume
  -- `T` as a linear equivalence (it is an injective endomorphism of a finite dimensional space).
  let e : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) := LinearEquiv.ofInjectiveEndo T hT
  have hdet : LinearMap.det T ≠ 0 := (LinearEquiv.isUnit_det' e).ne_zero
  have hqmp : Measure.QuasiMeasurePreserving (⇑T) volume volume :=
    Measure.LinearMap.quasiMeasurePreserving volume T hdet
  have hsymm : ∀ x : Fin d → ℝ, T (e.symm x) = x := fun x => by
    change (e : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (e.symm x) = x
    simp
  -- The inverse of `T` identifies `ℤᵈ` with `T ⁻¹' ℤᵈ`.
  let ee : (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup →
      ((Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)).comap (T.restrictScalars ℤ)).toAddSubgroup :=
    fun g => ⟨e.symm (g : Fin d → ℝ), by
      change T (e.symm (g : Fin d → ℝ)) ∈ Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)
      rw [hsymm (g : Fin d → ℝ)]
      exact hspan ▸ g.2⟩
  have hbij : Function.Bijective ee := by
    constructor
    · intro a b hab
      have h : e.symm (a : Fin d → ℝ) = e.symm (b : Fin d → ℝ) := by
        have := congrArg Subtype.val hab
        simpa only [ee] using this
      exact Subtype.ext (e.symm.injective h)
    · intro h
      refine ⟨⟨e (h : Fin d → ℝ), ?_⟩, ?_⟩
      · show e (h : Fin d → ℝ) ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))
        exact hspan.symm ▸ h.2
      · ext
        dsimp only [ee]
        simp
  -- The bijection is compatible with the translations.
  have hef : ∀ g : (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup,
      Function.Semiconj (⇑T) (fun x => ee g +ᵥ x) (fun x => g +ᵥ x) := by
    intro g x
    dsimp only [Function.Semiconj]
    rw [AddSubgroup.vadd_def, AddSubgroup.vadd_def, vadd_eq_add, vadd_eq_add, map_add]
    rw [show T (ee g : Fin d → ℝ) = (g : Fin d → ℝ) by
      dsimp only [ee]
      exact hsymm (g : Fin d → ℝ)]
  constructor
  · exact fund.preimage_of_equiv (f := ⇑T) hqmp (e := ee) hbij hef
  · have hG : Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup :=
      inferInstanceAs (Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))))
    exact (Equiv.countable_iff (Equiv.ofBijective ee hbij)).mp hG

end Work.BW.Minkowski2
