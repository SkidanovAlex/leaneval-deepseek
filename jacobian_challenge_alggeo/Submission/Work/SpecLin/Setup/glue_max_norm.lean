import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.SpecLin.Setup

/-- Given a finite free extension of domains `C → B`, the contraction of a maximal ideal `N` of `B`
is maximal in `C`, and the norm of any element `a ∈ N` lies in that contraction. -/
theorem glue_max_norm {C B : Type u} [CommRing C] [IsDomain C] [CommRing B] [IsDomain B]
    [Algebra C B] (hinj : Function.Injective (algebraMap C B))
    [Module.Finite C B] [Module.Free C B]
    (N : Ideal B) [N.IsMaximal] (a : B) (haN : a ∈ N) :
    (N.comap (algebraMap C B)).IsMaximal ∧
      Algebra.norm C a ∈ N.comap (algebraMap C B) := by
  constructor
  · -- `B` is finite (hence integral) over `C`, and the contraction of a maximal ideal along an
    -- integral extension is maximal.
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := C) (S := B) N
  · -- It remains to show `algebraMap C B (Algebra.norm C a) ∈ N`.
    rw [Ideal.mem_comap]
    -- It suffices to prove the stronger statement that this element lies in `Ideal.span {a}`.
    have hJ : algebraMap C B (Algebra.norm C a) ∈ Ideal.span ({a} : Set B) := by
      -- Cayley–Hamilton for the endomorphism `x ↦ a * x`.
      have hCH : Polynomial.aeval a (LinearMap.charpoly (Algebra.lmul C B a)) = 0 :=
        Algebra.aeval_self_charpoly_lmul a
      -- Split off the constant coefficient: `p = X * p.divX + C (p.coeff 0)`.
      have hh : Polynomial.aeval a (LinearMap.charpoly (Algebra.lmul C B a))
          = a * Polynomial.aeval a (Polynomial.divX (LinearMap.charpoly (Algebra.lmul C B a)))
            + algebraMap C B ((LinearMap.charpoly (Algebra.lmul C B a)).coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add (LinearMap.charpoly (Algebra.lmul C B a))]
        rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      -- Hence the constant term is `-(a * _)`, so lies in `Ideal.span {a}`.
      have hkey : algebraMap C B ((LinearMap.charpoly (Algebra.lmul C B a)).coeff 0)
          = -(a * Polynomial.aeval a
                (Polynomial.divX (LinearMap.charpoly (Algebra.lmul C B a)))) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        rw [hh] at hCH
        exact hCH
      have hmem : algebraMap C B ((LinearMap.charpoly (Algebra.lmul C B a)).coeff 0)
          ∈ Ideal.span ({a} : Set B) := by
        rw [hkey]
        exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton a)))
      -- The norm is `±` the constant coefficient of the characteristic polynomial.
      have hnorm : Algebra.norm C a
          = (-1 : C) ^ Module.finrank C B
              * (LinearMap.charpoly (Algebra.lmul C B a)).coeff 0 := by
        rw [Algebra.norm_apply]
        exact LinearMap.det_eq_sign_charpoly_coeff _
      rw [hnorm, map_mul]
      exact Ideal.mul_mem_left _ (algebraMap C B ((-1 : C) ^ Module.finrank C B)) hmem
    exact (Ideal.span_singleton_le_iff_mem (x := a) N).mpr haN hJ

end Work.SpecLin.Setup
