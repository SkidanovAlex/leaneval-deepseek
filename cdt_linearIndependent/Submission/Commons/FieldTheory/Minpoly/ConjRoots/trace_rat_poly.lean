import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Trace.Basic

open Polynomial
open scoped BigOperators

noncomputable section

open IntermediateField

namespace Commons.FieldTheory.Minpoly.ConjRoots

/-- For a multiset with no duplicates, a sum over the subtype of elements equals the
multiset sum of the image. -/
lemma multiset_nodup_sum_subtype {α M : Type*} [AddCommMonoid M] [DecidableEq α]
    (m : Multiset α) (hm : m.Nodup) (f : α → M) :
    (∑ x : {y : α // y ∈ m}, f x.1) = (m.map f).sum := by
  rw [Finset.sum_mem_multiset m (f := fun x : {y : α // y ∈ m} => f x.1) (g := f)]
  · rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hm]
  · intro x; rfl

/-- For an algebraic `z : ℂ` over `ℚ` and a rational polynomial `G`, the sum
of the values `G(w)` over the `ℂ`-roots (with multiplicity) of the minimal
polynomial of `z` is a rational number (the trace of `G(z)` in `ℚ(z)/ℚ`,
identified with the sum over the conjugate embeddings). -/
lemma trace_rat_poly {z : ℂ} (hz : IsAlgebraic ℚ z) (G : ℚ[X]) :
    ∃ r : ℚ,
      (((minpoly ℚ z).aroots ℂ).map (fun w : ℂ => (G.map (algebraMap ℚ ℂ)).eval w)).sum
        = (r : ℂ) := by
  have hzint : IsIntegral ℚ z := (isAlgebraic_iff_isIntegral).mp hz
  let L : IntermediateField ℚ ℂ := ℚ⟮z⟯
  let gen : L := IntermediateField.AdjoinSimple.gen ℚ z
  let y : L := aeval gen G
  haveI : FiniteDimensional ℚ L := IntermediateField.adjoin.finiteDimensional hzint
  haveI hisAlg : Algebra.IsAlgebraic ℚ L := IntermediateField.isAlgebraic_adjoin_simple hzint
  haveI hisInt : Algebra.IsIntegral ℚ L :=
    ⟨fun x => (isAlgebraic_iff_isIntegral).mp (Algebra.IsAlgebraic.isAlgebraic x)⟩
  haveI hsep : Algebra.IsSeparable ℚ L := Algebra.IsSeparable.of_integral ℚ L
  let pb : PowerBasis ℚ L := IntermediateField.adjoin.powerBasis hzint
  refine ⟨Algebra.trace ℚ L y, ?_⟩
  have htr : algebraMap ℚ ℂ (Algebra.trace ℚ L y) = ∑ σ : L →ₐ[ℚ] ℂ, σ y := by
    exact trace_eq_sum_embeddings ℂ (K := ℚ) (L := L) (x := y)
  have hP : minpoly ℚ pb.gen = minpoly ℚ z := by
    change minpoly ℚ (IntermediateField.AdjoinSimple.gen ℚ z) = minpoly ℚ z
    exact IntermediateField.minpoly_gen ℚ z
  have hnoduproots : ((minpoly ℚ z).aroots ℂ).Nodup := by
    rw [Polynomial.aroots_def]
    apply Polynomial.nodup_roots
    exact Polynomial.Separable.map (minpoly.irreducible hzint).separable
  have haeval : ∀ w : ℂ, aeval w G = (G.map (algebraMap ℚ ℂ)).eval w := by
    intro w
    rw [Polynomial.aeval_def, Polynomial.eval_map]
  have hsum_root : (∑ σ : L →ₐ[ℚ] ℂ, σ y) =
      ∑ w : {w : ℂ // w ∈ (minpoly ℚ pb.gen).aroots ℂ}, aeval w.1 G := by
    refine Fintype.sum_equiv pb.liftEquiv' (f := fun σ : L →ₐ[ℚ] ℂ => σ y)
      (g := fun w : {w : ℂ // w ∈ (minpoly ℚ pb.gen).aroots ℂ} => aeval w.1 G) ?_
    intro σ
    dsimp [y]
    rw [PowerBasis.liftEquiv'_apply_coe]
    rw [Polynomial.aeval_algHom_apply]
    rfl
  have hmap : (((minpoly ℚ z).aroots ℂ).map (fun w : ℂ => (G.map (algebraMap ℚ ℂ)).eval w)).sum
      = (((minpoly ℚ z).aroots ℂ).map (fun w : ℂ => aeval w G)).sum := by
    exact congrArg Multiset.sum (Multiset.map_congr rfl (fun w _ => (haeval w).symm))
  have hsub : (((minpoly ℚ z).aroots ℂ).map (fun w : ℂ => aeval w G)).sum
      = (∑ w : {w : ℂ // w ∈ (minpoly ℚ z).aroots ℂ}, aeval w.1 G) := by
    exact (multiset_nodup_sum_subtype ((minpoly ℚ z).aroots ℂ) hnoduproots
      (fun w : ℂ => aeval w G)).symm
  have hsum_root' : (∑ w : {w : ℂ // w ∈ (minpoly ℚ z).aroots ℂ}, aeval w.1 G)
      = (∑ σ : L →ₐ[ℚ] ℂ, σ y) := by
    rw [hP] at hsum_root
    exact hsum_root.symm
  have htr2 : (∑ σ : L →ₐ[ℚ] ℂ, σ y) = algebraMap ℚ ℂ (Algebra.trace ℚ L y) := htr.symm
  exact (hmap.trans hsub).trans (hsum_root'.trans htr2)

end Commons.FieldTheory.Minpoly.ConjRoots