import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.Kummer.kummer_equiv

/-!
# Kummer duality: the Galois group is dual to the group of Kummer generator classes

Let `K` be a field containing a primitive `p`-th root of unity `ζ` (`p` prime) and let `L/K` be a
finite Galois extension whose Galois group `G = Gal(L/K)` is abelian of exponent dividing `p`.

Write `Δ = Lˣ^p ∩ Kˣ` for the group of Kummer generators and `Δ/K^{×p}` for the group of Kummer
generator classes.  Kummer duality (`Work.CFT.Kummer.kummer_equiv`) identifies
`Δ/K^{×p} ≃* Hom(G, μ_p(L))`, where `μ_p(L) = rootsOfUnity p L ≅ ℤ/p` is cyclic of order `p`.

The content of the present file is the *self-duality* of a finite elementary abelian `p`-group:
a finite commutative group `A` all of whose elements satisfy `a ^ p = 1` is (non-canonically)
isomorphic to its dual `Hom(A, ℤ/p)`.  Indeed `A`, viewed additively, is a finite dimensional
`𝔽_p`-vector space, and any finite dimensional vector space is (non-canonically) isomorphic to its
linear dual via a choice of basis.  Applying this to `A = G` and to `A = Δ/K^{×p}` and splicing the
two isomorphisms through Kummer duality yields

`G ≃* Hom(Δ/K^{×p}, μ_p(L))`,

which is the statement proved here.

## Main result

* `Work.CFT.Kummer.kummer_dual_galois`
-/

open Additive Multiplicative

noncomputable section

namespace Work.CFT.Kummer

/-! ## Auxiliary lemmas -/

/-- Postcomposition with a multiplicative equivalence, as a multiplicative equivalence of the
monoids of monoid homomorphisms out of a fixed monoid. -/
private def monoidHomMulEquivCongrRight {M A N : Type*} [Monoid M] [CommMonoid A] [CommMonoid N]
    (e : A ≃* N) : (M →* A) ≃* (M →* N) where
  toFun f := e.toMonoidHom.comp f
  invFun f := e.symm.toMonoidHom.comp f
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_mul' f g := by ext x; simp

/-- If a field `L` contains a primitive `p`-th root of unity `ζ`, then the group `μ_p(L)` of `p`-th
roots of unity of `L` is cyclic of order `p`, i.e. isomorphic to `Multiplicative (ZMod p)`. -/
private theorem rootsOfUnity_mulEquiv_zmod {L : Type*} [Field L] (p : ℕ) [NeZero p] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot ζ p) : Nonempty (rootsOfUnity p L ≃* Multiplicative (ZMod p)) := by
  have hsub : (Subgroup.zpowers ζ : Subgroup Lˣ) = rootsOfUnity p L := hζ.zpowers_eq
  have e : ↥(Subgroup.zpowers ζ) ≃* ↥(rootsOfUnity p L) :=
    { toFun := fun x => ⟨x.1, by rw [← hsub]; exact x.2⟩
      invFun := fun y => ⟨y.1, by rw [hsub]; exact y.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => rfl }
  exact ⟨(MulEquiv.multiplicativeAdditive (H := rootsOfUnity p L)).symm.trans
    (AddEquiv.toMultiplicative ((MulEquiv.toAdditive e.symm).trans hζ.zmodEquivZPowers.symm))⟩

/-- **Self-duality of a finite elementary abelian `p`-group.**  A group `A` in which all
elements satisfy `a ^ p = 1` and all elements commute is (non-canonically) isomorphic to its dual
`A →* ℤ/p` (written multiplicatively as `Multiplicative (ZMod p)`).

Additively, `A` is a finite dimensional `𝔽_p`-vector space; choosing a basis, `A` is linearly
isomorphic to its linear dual `Module.Dual (ZMod p) (Additive A) = (Additive A →ₗ[ZMod p] ZMod p)`,
and additive homomorphisms between `ZMod p`-modules are automatically `ZMod p`-linear. -/
private theorem self_dual_equiv (p : ℕ) (hp : p.Prime) (A : Type*) [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) [Finite A] (hexp : ∀ a : A, a ^ p = 1) :
    Nonempty (A ≃* (A →* Multiplicative (ZMod p))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : AddCommGroup (Additive A) :=
    { (inferInstance : AddGroup (Additive A)) with add_comm := fun x y => hcomm x.toMul y.toMul }
  haveI : Module (ZMod p) (Additive A) :=
    AddCommGroup.zmodModule (fun x => by
      have h : (p • x : Additive A) = Additive.ofMul (x.toMul ^ p) := rfl
      rw [hexp] at h
      simpa using h)
  haveI : Module.Finite (ZMod p) (Additive A) := Module.Finite.of_finite
  let b := Module.Basis.ofVectorSpace (ZMod p) (Additive A)
  let φ : Additive A ≃ₗ[ZMod p] Module.Dual (ZMod p) (Additive A) := b.toDualEquiv
  refine ⟨(MulEquiv.multiplicativeAdditive (H := A)).symm.trans <|
    (AddEquiv.toMultiplicative φ.toAddEquiv).trans <|
    (AddEquiv.toMultiplicative (AddMonoidHom.toZModLinearMapEquiv p).symm).trans <|
    (AddEquiv.toMultiplicative (AddMonoidHom.toMultiplicativeRightAddEquiv (M := A)
      (N := ZMod p))).trans
      (MulEquiv.multiplicativeAdditive (H := (A →* Multiplicative (ZMod p))))⟩

/-! ## Kummer duality for the Galois group -/
/-- **The perfect Kummer pairing.** For `L/K` finite Galois abelian of exponent dividing `p` and
`μ_p ⊆ K`, the Kummer pairing `Gal(L/K) × (Lˣ^p ∩ Kˣ)/Kˣ^p → μ_p(L)`,
`(σ, a) ↦ σ(α)/α` for `α^p = a`, is perfect: `Gal(L/K) ≃* ((Lˣ^p ∩ Kˣ)/Kˣ^p →* μ_p(L))`.  This is
the group-theoretic content behind the Kummer description of exponent-`p` abelian extensions by
their Kummer generators, and the finite-level shadow of the identification of `G_S/Φ(G_S)` with
the Pontryagin dual of `V_S/K^{×p}`. -/
theorem kummer_dual_galois (p : ℕ) (hp : p.Prime) {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ p)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ p = 1) (hab : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) :
    Nonempty ((L ≃ₐ[K] L) ≃*
      (Work.CFT.Kummer.kummerGeneratorsQuotient K L p →* rootsOfUnity p L)) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- the image of `ζ` in `L` is a primitive `p`-th root of unity
  let ζL : Lˣ := Units.map (algebraMap K L).toMonoidHom ζ
  have hζL : IsPrimitiveRoot ζL p :=
    hζ.map_of_injective (Units.map_injective (RingHom.injective (algebraMap K L)))
  obtain ⟨eμ⟩ := rootsOfUnity_mulEquiv_zmod p ζL hζL
  -- Kummer duality
  obtain ⟨eE⟩ := kummer_equiv (K := K) (L := L) p hp ζ hζ
  -- finiteness of the Galois group, of `μ_p(L)`, and hence of `Δ/K^{×p}`
  haveI : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  haveI : Fintype (rootsOfUnity p L) := Fintype.ofFinite _
  haveI : Finite ((L ≃ₐ[K] L) →* rootsOfUnity p L) :=
    Finite.of_injective
      (fun f : (L ≃ₐ[K] L) →* rootsOfUnity p L => (f : (L ≃ₐ[K] L) → rootsOfUnity p L))
      (fun f g h => MonoidHom.ext (congrFun h))
  haveI : Finite (Work.CFT.Kummer.kummerGeneratorsQuotient K L p) :=
    Finite.of_injective
      (fun b : Work.CFT.Kummer.kummerGeneratorsQuotient K L p => eE b) eE.injective
  -- the Kummer generator classes have exponent dividing `p`
  have hexpB : ∀ b : Work.CFT.Kummer.kummerGeneratorsQuotient K L p, b ^ p = 1 := fun b =>
    quotient_pow_eq_one (p := p)
      (fun (y : kummerGenerators K L p) => Subgroup.mem_comap.mpr
        (mem_pthPowerSubgroup.mpr ⟨(y : Kˣ), rfl⟩)) b
  -- self-duality of both elementary abelian `p`-groups
  obtain ⟨dA⟩ := self_dual_equiv p hp (L ≃ₐ[K] L) hab hexp
  obtain ⟨dB⟩ := self_dual_equiv p hp (Work.CFT.Kummer.kummerGeneratorsQuotient K L p)
    (fun a b => mul_comm a b) hexpB
  -- assemble: G ≅ Hom(G, 𝔽_p) ≅ Hom(G, μ_p) ≅ Δ/K^{×p} ≅ Hom(Δ/K^{×p}, 𝔽_p) ≅ Hom(Δ/K^{×p}, μ_p)
  exact ⟨((dA.trans (monoidHomMulEquivCongrRight eμ.symm)).trans eE.symm).trans
    (dB.trans (monoidHomMulEquivCongrRight eμ.symm))⟩

end Work.CFT.Kummer
