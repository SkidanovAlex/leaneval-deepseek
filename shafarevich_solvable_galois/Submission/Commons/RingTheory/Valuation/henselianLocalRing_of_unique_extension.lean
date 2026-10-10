import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.exists_irreducible_factor_of_residue_root
import Submission.Commons.RingTheory.Valuation.natDegree_map_eq_one_of_irreducible_of_unique_extension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

theorem henselianLocalRing_of_unique_extension {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F'] (V : ValuationSubring F) (W : ValuationSubring F') (hW : W.comap (algebraMap F F') = V) (huniq : ∀ W' : ValuationSubring F', W'.comap (algebraMap F F') = V → W' = W) : HenselianLocalRing V := by
  -- Every `F`-automorphism of the separable closure preserves `W`.
  have hstab : ∀ σ : F' ≃ₐ[F] F', W.comap (σ : F' →+* F') = W := by
    intro σ
    refine huniq (W.comap (σ : F' →+* F')) ?_
    rw [ValuationSubring.comap_comap]
    have hcomp : (σ : F' →+* F').comp (algebraMap F F') = algebraMap F F' := by
      ext x; exact σ.commutes x
    rw [hcomp, hW]
  constructor
  intro f hf a₀ h1 h2
  -- Extract the irreducible factor of `f` that carries the approximate root `a₀`.
  obtain ⟨g, hgmonic, hgirr, hgdvd, hga, hgda⟩ :=
    exists_irreducible_factor_of_residue_root V f hf a₀ h1 h2
  -- Uniqueness of the extension forces this factor to be linear.
  have hdeg : (g.map (algebraMap V F)).natDegree = 1 :=
    natDegree_map_eq_one_of_irreducible_of_unique_extension V W hW hstab g hgmonic hgirr a₀ hga hgda
  have hgnat : g.natDegree = 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective V F)] at hdeg
    exact hdeg
  have hgeq : g = Polynomial.X + Polynomial.C (g.coeff 0) := hgmonic.eq_X_add_C hgnat
  obtain ⟨h, hh⟩ := hgdvd
  have hgval : g.eval a₀ = a₀ + g.coeff 0 := by
    rw [hgeq]; simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  -- `-(g.coeff 0)` is the root of `f` we are looking for.
  refine ⟨-(g.coeff 0), ?_, ?_⟩
  · rw [Polynomial.IsRoot, hh, hgeq]
    simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  · have : -(g.coeff 0) - a₀ = -(g.eval a₀) := by rw [hgval]; ring
    rw [this]
    exact neg_mem hga

end Commons.RingTheory.Valuation
