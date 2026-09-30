import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveFacts.KrullDim

universe u

/-- **The Kähler differentials of a standard étale algebra over a polynomial ring over a field
are free of rank `n`.**  If `S` is standard étale over `P = MvPolynomial (Fin n) K` (with `K` a
field), then `Ω[S⁄K]` is free of rank `n` over `S`.

Indeed `P → S` is formally étale (`Algebra.Etale → Algebra.FormallyEtale`), so
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` (`Mathlib/RingTheory/Etale/Kaehler.lean`)
gives `S ⊗[P] Ω[P⁄K] ≃ₗ[S] Ω[S⁄K]`; and `Ω[P⁄K]` has `P`-basis
`KaehlerDifferential.mvPolynomialBasis K (Fin n) : Basis (Fin n) P Ω[P⁄K]`
(`Mathlib/RingTheory/Kaehler/Polynomial.lean`), so its base change to `S` (`Module.Basis.baseChange`,
`Mathlib/LinearAlgebra/TensorProduct/Basis.lean`) is free of rank `n`.
Alternative shorter route: `RingHom.Etale ↔ IsStandardSmoothOfRelativeDimension 0`, `.comp` and
`.mvPolynomial` give `IsStandardSmoothOfRelativeDimension n K S`, then
`Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`. -/
theorem rank_kaehler_of_isStandardEtale {K : Type u} [Field K] {n : ℕ} {S : Type u} [CommRing S]
    [Algebra K S] (a : Algebra (MvPolynomial (Fin n) K) S)
    (h : @Algebra.IsStandardEtale (MvPolynomial (Fin n) K) S _ _ a)
    [IsScalarTower K (MvPolynomial (Fin n) K) S] [Nontrivial S] :
    Module.rank S (KaehlerDifferential K S) = n := by
  -- Realise the given algebra structure `a` as the working instance.
  letI := a
  -- `S` is standard étale over `P = MvPolynomial (Fin n) K`, hence étale over `P`.
  haveI : Algebra.IsStandardEtale (MvPolynomial (Fin n) K) S := h
  haveI : Algebra.Etale (MvPolynomial (Fin n) K) S := inferInstance
  -- Étale = standard smooth of relative dimension `0`.
  have h0 : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin n) K) S :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  -- `P` is standard smooth of relative dimension `n` over `K`.
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K (MvPolynomial (Fin n) K) :=
    inferInstance
  -- Composition gives standard smoothness of relative dimension `0 + n = n` over `K`.
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K S := by
    have hcomp := Algebra.IsStandardSmoothOfRelativeDimension.trans (n := n) (m := 0) (R := K)
      (S := MvPolynomial (Fin n) K) (T := S)
    simpa using hcomp
  exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n

end Work.CurveFacts.KrullDim
