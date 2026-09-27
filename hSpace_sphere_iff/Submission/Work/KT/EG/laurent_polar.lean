import Mathlib
import Submission.Work.KT.EG.kappaRedDefs
import Submission.Work.KT.Fund.Laurent

namespace Work.KT.EG

/-- `polyMap` of a constant is the pull-back of the constant, with no compactness hypothesis. -/
lemma polar_polyMap_C (X : Type) [TopologicalSpace X] (a : C(X, ℂ)) :
    polyMap X (Polynomial.C a)
      = (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))) a :=
  Polynomial.eval₂_C _ _

/-- `polyMap` of the variable is the coordinate unit `z`, with no compactness hypothesis. -/
lemma polar_polyMap_X (X : Type) [TopologicalSpace X] :
    polyMap X Polynomial.X = (zUnit X : C(X × Sph ℂ, ℂ)) :=
  Polynomial.eval₂_X _ _

/-- `laurentMap` of `Polynomial.toLaurent q` is `polyMap q`, with no compactness hypothesis
(the compactness instances in `laurentMap_toLaurent` are not used by its proof). -/
lemma polar_laurentMap_toLaurent {X : Type} [TopologicalSpace X] (q : Polynomial C(X, ℂ)) :
    Work.KT.laurentMap X (Polynomial.toLaurent q) = polyMap X q := by
  have h : (Work.KT.laurentMap X).comp (Polynomial.toLaurent (R := C(X, ℂ)))
      = polyMap X := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, Polynomial.toLaurent_C, Work.KT.laurentMap_C, polar_polyMap_C]
    · rw [RingHom.comp_apply, Polynomial.toLaurent_X, Work.KT.laurentMap_T, zpow_one,
        polar_polyMap_X]
  exact congrFun (congrArg DFunLike.coe h) q

/-- **The polar part of a Laurent polynomial matrix is polynomial.** Any matrix of Laurent
polynomials over `C(X, ℂ)`, multiplied by a sufficiently high power of the coordinate unit `z`, is
the image of a matrix of *polynomials*: `P.map laurentMap = z^{-N} • q.map polyMap` for some `N`
and some `q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))`.

Route: `LaurentPolynomial` has finite support; let `N` be the maximum of `-k` over the support
(for empty support take `N = 0`); write `P` as a finite sum of monomials `C (P k) * T k` and
multiply by `T^N`. Use the multiplicativity of `Work.KT.laurentMap`, `Work.KT.laurentMap_C`,
`Work.KT.laurentMap_T`, `Polynomial.toLaurent_C`, `Polynomial.toLaurent_X ^ k` and
`Work.KT.EG.laurentMap_toLaurent` (in `Work.KT.EG.kappaRedDefs`). -/
theorem laurent_polar (X : Type) [TopologicalSpace X] (m : ℕ)
    (P : Matrix (Fin m) (Fin m) (LaurentPolynomial C(X, ℂ))) :
    ∃ (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))),
      P.map (Work.KT.laurentMap X)
        = (((Work.KT.zUnit X) ^ (-(N : ℤ)) : (C(X × Sph ℂ, ℂ))ˣ) : C(X × Sph ℂ, ℂ))
            • (q.map (Work.KT.EG.polyMap X)) := by
  classical
  -- For each entry of `P`, clear negative powers using `exists_T_pow`.
  choose n qq hq using fun (ij : Fin m × Fin m) =>
    LaurentPolynomial.exists_T_pow (P ij.1 ij.2)
  -- `N` is the largest exponent needed, uniformly over all entries.
  set N : ℕ := Finset.univ.sup n with hN
  -- Entrywise: `laurentMap (P i j) = z^{-N} * polyMap (q_ij * X^(N - n_ij))`.
  have key : ∀ i j, Work.KT.laurentMap X (P i j)
      = (↑((Work.KT.zUnit X) ^ (-(N : ℤ))) : C(X × Sph ℂ, ℂ))
          * polyMap X (qq (i, j) * Polynomial.X ^ (N - n (i, j))) := by
    intro i j
    have hle : n (i, j) ≤ N := by
      rw [hN]; exact Finset.le_sup (Finset.mem_univ (i, j))
    have hexp : (↑(n (i, j)) : ℤ) + ↑(N - n (i, j)) = ↑N := by
      rw [Nat.cast_sub hle]; ring
    -- `toLaurent` of the corrected entry is `P i j * T^N`.
    have h1 : Polynomial.toLaurent (qq (i, j) * Polynomial.X ^ (N - n (i, j)))
        = P i j * LaurentPolynomial.T (N : ℤ) := by
      rw [map_mul, Polynomial.toLaurent_X_pow, hq (i, j), LaurentPolynomial.mul_T_assoc, hexp]
    -- Evaluating at `T ↦ z` gives `polyMap … = laurentMap (P i j) * z^N`.
    have h2 : polyMap X (qq (i, j) * Polynomial.X ^ (N - n (i, j)))
        = Work.KT.laurentMap X (P i j) * ↑(Work.KT.zUnit X ^ (N : ℤ)) := by
      rw [← polar_laurentMap_toLaurent, h1, map_mul, Work.KT.laurentMap_T]
    have h3 : (Work.KT.zUnit X ^ (-(N : ℤ)) * Work.KT.zUnit X ^ (N : ℤ)
        : (C(X × Sph ℂ, ℂ))ˣ) = 1 := by
      rw [← _root_.zpow_add, neg_add_cancel, zpow_zero]
    -- Multiply `h2` on the left by `z^{-N}` and cancel.
    rw [h2, ← mul_assoc,
      mul_comm (↑(Work.KT.zUnit X ^ (-(N : ℤ))) : C(X × Sph ℂ, ℂ))
        (Work.KT.laurentMap X (P i j)),
      mul_assoc, ← Units.val_mul, h3, Units.val_one, mul_one]
  refine ⟨N, fun i j => qq (i, j) * Polynomial.X ^ (N - n (i, j)), ?_⟩
  refine Matrix.ext fun i j => ?_
  change Work.KT.laurentMap X (P i j)
      = (↑((Work.KT.zUnit X) ^ (-(N : ℤ))) : C(X × Sph ℂ, ℂ))
          * polyMap X (qq (i, j) * Polynomial.X ^ (N - n (i, j)))
  exact key i j

end Work.KT.EG
