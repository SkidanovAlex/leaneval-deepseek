import Mathlib

namespace NK.LocalReciprocityLubinTate.Unramified

universe u

/-- **The norm of a polynomial in a root is the resultant.**  Let `E ∈ F[X]` be monic and
irreducible over a field `F` of characteristic `0`, and let `g ∈ F[X]` be arbitrary.  Then, in the
field `AdjoinRoot E = F[X]/(E)` (whose canonical generator is `AdjoinRoot.root E`), the norm down to
`F` of the class of `g` is the resultant of `E` and `g`:
`Algebra.norm F (AdjoinRoot.mk E g) = Polynomial.resultant E g`.

PROOF ROUTE.  `AdjoinRoot.mk E g = AdjoinRoot.mk E (g % E)` (`AdjoinRoot.mk_self`) and
`(g % E).natDegree < E.natDegree` (`Polynomial.natDegree_modByMonic_lt`, `E` monic).  Let
`L := AdjoinRoot E`, which is a field of degree `d = E.natDegree` over `F`
(`AdjoinRoot.instField` needs `Fact (Irreducible E)`; `AdjoinRoot.powerBasis` gives the power basis
`1, root, …, root^(d-1)`), so `Algebra.IsSeparable F L` holds in characteristic `0`.  In
`Ω := AlgebraicClosure F` (algebraically closed), Mathlib's `Algebra.norm_eq_prod_embeddings` gives
`algebraMap F Ω (Algebra.norm F x) = ∏ σ : L →ₐ[F] Ω, σ x`.  The embeddings `σ` correspond
bijectively to the roots of `E` in `Ω` through `σ ↦ σ (AdjoinRoot.root E)`
(`IntermediateField.algHomAdjoinIntegralEquiv`, or directly `AdjoinRoot.lift`:
`σ (mk g) = aeval (σ root) g`).  Hence
`Algebra.norm F (mk g) = ∏_{α : E(α) = 0} g(α)`, and the right-hand side is
`Polynomial.resultant E g` by `Polynomial.resultant_eq_prod_eval` (with `f := E`,
`hf : E.Splits` over `Ω`, `E.monic` so `leadingCoeff = 1`), transported back along the injective
`algebraMap F Ω`. -/
theorem norm_adjoinRoot_eq_resultant {F : Type u} [Field F] [CharZero F] (E : Polynomial F)
    (hmon : E.Monic) (hirr : Irreducible E) (g : Polynomial F) :
    Algebra.norm F (AdjoinRoot.mk E g) = Polynomial.resultant E g := by
  classical
  haveI : Fact (Irreducible E) := ⟨hirr⟩
  -- `AdjoinRoot E` is a finite (hence, in characteristic zero, separable) extension of `F`.
  haveI : Module.Finite F (AdjoinRoot E) := hmon.finite_adjoinRoot
  haveI : Algebra.IsIntegral F (AdjoinRoot E) := Algebra.IsIntegral.of_finite F _
  haveI : Algebra.IsSeparable F (AdjoinRoot E) := inferInstance
  let Ω := AlgebraicClosure F
  -- It suffices to compare the two sides inside the algebraic closure of `F`.
  apply (algebraMap F Ω).injective
  -- The norm is the product of the conjugates.
  rw [Algebra.norm_eq_prod_embeddings F Ω (AdjoinRoot.mk E g)]
  -- **Step 1.**  The product of the conjugates of `mk E g` is the product of `g` over the roots of
  -- `E`: the `F`-embeddings of `AdjoinRoot E` are the evaluations at the roots of `E`.
  have hA : (∏ σ : AdjoinRoot E →ₐ[F] Ω, σ (AdjoinRoot.mk E g))
      = ((E.map (algebraMap F Ω)).roots.map (fun α => Polynomial.aeval α g)).prod := by
    let pb := AdjoinRoot.powerBasis hmon.ne_zero
    have hgen : pb.gen = AdjoinRoot.root E := AdjoinRoot.powerBasis_gen _
    have hmin : minpoly F pb.gen = E := AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon
    -- Replace the `F`-embeddings by the roots of the minimal polynomial of `pb.gen` via
    -- `PowerBasis.liftEquiv'`, which sends `σ` to `σ pb.gen`.
    rw [@Fintype.prod_equiv (AdjoinRoot E →ₐ[F] Ω) _ _ _ _ _
        pb.liftEquiv' (fun σ => σ (AdjoinRoot.mk E g)) (fun y => Polynomial.aeval (y : Ω) g) (by
          intro σ
          rw [PowerBasis.liftEquiv'_apply_coe, ← AdjoinRoot.aeval_eq g,
            ← Polynomial.aeval_algHom_apply σ (AdjoinRoot.root E) g]
          rw [hgen])]
    -- Turn the product over the subtype of roots into a product over the multiset of roots
    -- (`(map (algebraMap F Ω) E).roots` is duplicate free as `E` is separable).
    rw [hmin, Polynomial.aroots_def]
    rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr
        (Polynomial.nodup_roots (hirr.separable.map (f := algebraMap F Ω)))]
    intro x
    rfl
  -- **Step 2.**  The resultant of `E` and `g` is the same product of `g` over the roots of `E`.
  have hB : (algebraMap F Ω) (E.resultant g)
      = ((E.map (algebraMap F Ω)).roots.map (fun α => Polynomial.aeval α g)).prod := by
    rw [← Polynomial.resultant_map_map E g E.natDegree g.natDegree (algebraMap F Ω)]
    rw [← Polynomial.Monic.natDegree_map hmon (algebraMap F Ω),
        ← Polynomial.natDegree_map_eq_of_injective (algebraMap F Ω).injective g]
    -- Over an algebraically closed field the resultant is `leadingCoeff ^ n` times the product of
    -- `g` over the roots of `E`.
    rw [Polynomial.resultant_eq_prod_eval (E.map (algebraMap F Ω)) (g.map (algebraMap F Ω))
      ((g.map (algebraMap F Ω)).natDegree) le_rfl (IsAlgClosed.splits _)]
    rw [Polynomial.leadingCoeff_map_of_injective (algebraMap F Ω).injective, hmon.leadingCoeff,
      map_one, one_pow, one_mul]
    simp only [Polynomial.eval_map_algebraMap]
  rw [hA, hB]

end NK.LocalReciprocityLubinTate.Unramified
