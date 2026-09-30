import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open KaehlerDifferential
open scoped TensorProduct

namespace Work.Normality

/-- Let `K` be a field, `A` a `K`-algebra with a submersive presentation `Pr` (generators `ι`,
relations `σ`), and let `P := MvPolynomial ↥(Set.range Pr.map)ᶜ K` be the polynomial ring in the
generators *not* occurring in the relation map, mapping to `A` by `X k ↦ Pr.val k`.  Then the
natural map `A ⊗[P] Ω[P⁄K] → Ω[A⁄K]` is bijective.

Both directions are read off the two bases.  `Ω[P⁄K]` is free on `{dX_k}`
(`KaehlerDifferential.mvPolynomialBasis`, or `SubmersivePresentation.mvPolynomial` of `P` over
`K`), so `A ⊗[P] Ω[P⁄K]` is free on `{1 ⊗ dX_k}`, and `mapBaseChange` sends `1 ⊗ dX_k` to
`KaehlerDifferential.map K K P A (D K P (X k)) = KaehlerDifferential.D K A (algebraMap P A (X k))
= KaehlerDifferential.D K A (Pr.val k)`, which is the basis
`Algebra.SubmersivePresentation.basisKaehler` of `Ω[A⁄K]` (indexed by the same type).
Hence the map is an isomorphism of free `A`-modules: surjective because a submodule containing a
basis is `⊤`; injective by defining the inverse on `Pr.basisKaehler` via `Basis.constr` sending
`Pr.basisKaehler k` to `1 ⊗ dX_k`. -/
theorem bijective_mapBaseChange_complement {K A ι σ : Type*} [Field K] [CommRing A] [Algebra K A]
    [Finite σ] (Pr : Algebra.SubmersivePresentation K A ι σ)
    [Algebra (MvPolynomial ↥(Set.range Pr.map)ᶜ K) A]
    [IsScalarTower K (MvPolynomial ↥(Set.range Pr.map)ᶜ K) A]
    (hφ : ∀ k : ↥(Set.range Pr.map)ᶜ,
      (algebraMap (MvPolynomial ↥(Set.range Pr.map)ᶜ K) A) (MvPolynomial.X k) = Pr.val k.1) :
    Function.Bijective
      (KaehlerDifferential.mapBaseChange K (MvPolynomial ↥(Set.range Pr.map)ᶜ K) A) := by
  classical
  -- The basis `{1 ⊗ dX_k}` of `A ⊗[P] Ω[P⁄K]`.
  let e : Module.Basis ↥(Set.range Pr.map)ᶜ A
      (A ⊗[MvPolynomial ↥(Set.range Pr.map)ᶜ K] Ω[MvPolynomial ↥(Set.range Pr.map)ᶜ K⁄K]) :=
    (KaehlerDifferential.mvPolynomialBasis K ↥(Set.range Pr.map)ᶜ).baseChange A
  let f := KaehlerDifferential.mapBaseChange K (MvPolynomial ↥(Set.range Pr.map)ᶜ K) A
  -- The candidate inverse, sending `Pr.basisKaehler k ↦ 1 ⊗ dX_k`.
  let g : Ω[A⁄K] →ₗ[A]
      (A ⊗[MvPolynomial ↥(Set.range Pr.map)ᶜ K] Ω[MvPolynomial ↥(Set.range Pr.map)ᶜ K⁄K]) :=
    Pr.basisKaehler.constr A (fun k => e k)
  -- `f` sends the basis `e` to the basis `Pr.basisKaehler`.
  have hf : ∀ k, f (e k) = Pr.basisKaehler k := by
    intro k
    show KaehlerDifferential.mapBaseChange K (MvPolynomial ↥(Set.range Pr.map)ᶜ K) A
      ((KaehlerDifferential.mvPolynomialBasis K ↥(Set.range Pr.map)ᶜ).baseChange A k)
      = Pr.basisKaehler k
    rw [Module.Basis.baseChange_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D, hφ k]
    exact (Algebra.SubmersivePresentation.basisKaehler_apply Pr k).symm
  have hg_apply : ∀ k, g (Pr.basisKaehler k) = e k := by
    intro k
    show (Pr.basisKaehler.constr A (fun k => e k)) (Pr.basisKaehler k) = e k
    rw [Module.Basis.constr_basis]
  have hgf : g.comp f = LinearMap.id := by
    apply Module.Basis.ext (b := e)
    intro k
    rw [LinearMap.comp_apply, hf k, hg_apply k, LinearMap.id_apply]
  have hfg : f.comp g = LinearMap.id := by
    apply Module.Basis.ext (b := Pr.basisKaehler)
    intro k
    rw [LinearMap.comp_apply, hg_apply k, hf k, LinearMap.id_apply]
  constructor
  · intro x y hxy
    have h2 : (g.comp f) x = (g.comp f) y := by
      show g (f x) = g (f y)
      rw [hxy]
    rw [hgf] at h2
    simpa using h2
  · intro y
    refine ⟨g y, ?_⟩
    show f (g y) = y
    rw [← LinearMap.comp_apply, hfg, LinearMap.id_apply]

end Work.Normality
