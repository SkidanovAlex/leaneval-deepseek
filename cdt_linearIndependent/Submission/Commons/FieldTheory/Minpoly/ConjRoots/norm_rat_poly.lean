import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial
open scoped BigOperators

noncomputable section

namespace Commons.FieldTheory.Minpoly.ConjRoots

set_option linter.style.haveILetI false

/-- Product over `ℂ`-embeddings of `σ (G(pb.gen))` equals the product of `G(w)` over the
`ℂ`-roots (with multiplicity) of the minimal polynomial of `pb.gen`. -/
lemma prod_embeddings_aeval {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    (pb : PowerBasis ℚ L) (G : ℚ[X]) :
    (∏ σ : L →ₐ[ℚ] ℂ, σ (aeval pb.gen G)) =
      (((minpoly ℚ pb.gen).aroots ℂ).map (fun w : ℂ => (G.map (algebraMap ℚ ℂ)).eval w)).prod := by
  classical
  let m := (minpoly ℚ pb.gen).aroots ℂ
  have hm_sep : ((minpoly ℚ pb.gen).map (algebraMap ℚ ℂ)).Separable := by
    exact Polynomial.Separable.map (Irreducible.separable (minpoly.irreducible pb.isIntegral_gen))
  have hm_nodup : m.Nodup := by
    simpa [m, Polynomial.aroots_def] using (Polynomial.nodup_roots hm_sep)
  calc
    (∏ σ : L →ₐ[ℚ] ℂ, σ (aeval pb.gen G))
        = ∏ σ : L →ₐ[ℚ] ℂ, aeval (σ pb.gen) G := by
            apply Finset.prod_congr rfl
            intro σ hs
            exact (Polynomial.aeval_algHom_apply σ pb.gen G).symm
    _ = (∏ y : {y : ℂ // y ∈ m}, aeval (y : ℂ) G) := by
            refine Fintype.prod_equiv pb.liftEquiv' _ _ ?_
            intro σ
            rw [PowerBasis.liftEquiv'_apply_coe]
    _ = (m.map (fun w : ℂ => aeval w G)).prod := by
            rw [Finset.prod_mem_multiset m (fun y : {y : ℂ // y ∈ m} => aeval (y : ℂ) G)
              (fun w : ℂ => aeval w G) (by intro y; rfl)]
            rw [Finset.prod_eq_multiset_prod m.toFinset]
            rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hm_nodup]
    _ = (((minpoly ℚ pb.gen).aroots ℂ).map (fun w : ℂ => (G.map (algebraMap ℚ ℂ)).eval w)).prod := by
            change (((minpoly ℚ pb.gen).aroots ℂ).map (fun w : ℂ => aeval w G)).prod =
                  (((minpoly ℚ pb.gen).aroots ℂ).map (fun w : ℂ => (G.map (algebraMap ℚ ℂ)).eval w)).prod
            apply congrArg Multiset.prod
            apply Multiset.map_congr rfl
            intro w hw
            rw [Polynomial.aeval_def, ← Polynomial.eval_map]

/-- For an algebraic `z : ℂ` over `ℚ` and a rational polynomial `G`, the
product of the values `G(w)` over the `ℂ`-roots (with multiplicity) of the
minimal polynomial of `z` is a rational number (the norm of `G(z)` in
`ℚ(z)/ℚ`). -/
lemma norm_rat_poly {z : ℂ} (hz : IsAlgebraic ℚ z) (G : ℚ[X]) :
    ∃ r : ℚ,
      (((minpoly ℚ z).aroots ℂ).map (fun w : ℂ => (G.map (algebraMap ℚ ℂ)).eval w)).prod
        = (r : ℂ) := by
  classical
  have hzI : IsIntegral ℚ z := (isAlgebraic_iff_isIntegral.mp hz)
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({z} : Set ℂ)
  let pb : PowerBasis ℚ L := IntermediateField.adjoin.powerBasis hzI
  haveI : FiniteDimensional ℚ L := IntermediateField.adjoin.finiteDimensional hzI
  haveI : Algebra.IsSeparable ℚ L := inferInstance
  let y : L := aeval pb.gen G
  have hm : minpoly ℚ pb.gen = minpoly ℚ z := by
    calc
      minpoly ℚ pb.gen = minpoly ℚ ((algebraMap L ℂ) pb.gen) := by
        exact (minpoly.algebraMap_eq (algebraMap L ℂ).injective pb.gen).symm
      _ = minpoly ℚ z := by
        simp [pb]
  refine ⟨Algebra.norm ℚ y, ?_⟩
  calc
    (((minpoly ℚ z).aroots ℂ).map (fun w : ℂ => (G.map (algebraMap ℚ ℂ)).eval w)).prod
        = (((minpoly ℚ pb.gen).aroots ℂ).map (fun w : ℂ => (G.map (algebraMap ℚ ℂ)).eval w)).prod := by
            rw [hm]
    _ = (∏ σ : L →ₐ[ℚ] ℂ, σ (aeval pb.gen G)) := (prod_embeddings_aeval pb G).symm
    _ = (∏ σ : L →ₐ[ℚ] ℂ, σ y) := by rfl
    _ = algebraMap ℚ ℂ (Algebra.norm ℚ y) := by
            exact (Algebra.norm_eq_prod_embeddings ℚ ℂ y).symm
    _ = (Algebra.norm ℚ y : ℂ) := by rfl

end Commons.FieldTheory.Minpoly.ConjRoots