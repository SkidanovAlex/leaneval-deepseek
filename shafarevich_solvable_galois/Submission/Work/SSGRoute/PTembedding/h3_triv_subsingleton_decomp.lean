import Mathlib.FieldTheory.KrullTopology
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PT.H3Transfer
import Submission.Work.SSGRoute.PT.h3_units_adicCompletion_eq_zero
import Submission.Work.SSGRoute.PT.p_dvd_H2_units_adicCompletion
import Submission.Work.SSGRoute.PTembedding.h3_triv_subsingleton_of_units_divisible
import Submission.Work.SSGRoute.isHomeomorph_localGaloisEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H³(D_A, 𝔽_p) = 0` for the decomposition group of a finite place

For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` and a prime `p` such
that `k` contains a primitive `p`-th root of unity, the third continuous cohomology of the
decomposition group `D_A = decomp k A` with trivial coefficients `𝔽_p = Triv p` vanishes:

`Subsingleton (H³(D_A, 𝔽_p))`.

## The mathematics

`D_A` is the decomposition group of the place `A` of `Ω`, hence the absolute Galois group of the
local field `κ = k_𝔭` obtained by completing `k` at the prime `𝔭` of `k` below `A`
(`Work.SSGRoute.isHomeomorph_localGaloisEquiv`, via `NK.Mine.localGaloisEquiv`, an isomorphism of
*topological* groups).  For a non-archimedean local field `κ` one has `cd_p(G_κ) ≤ 2`
(Serre, *Cohomologie galoisienne*, II §5; Neukirch–Schmidt–Wingberg 7.1.8), so
`H³(G_κ, 𝔽_p) = 0`.

The vanishing at the completion is available in this workspace as
`Work.SSGRoute.PTembedding.h3_triv_subsingleton_of_units_divisible`, which runs the Kummer
sequence `0 → μ_p → κ̄ˣ →^{p} κ̄ˣ → 0` through the `2 → 3` segment of the long exact sequence:
`δ³ : H²(G_κ, κ̄ˣ) → H³(G_κ, μ_p)` is zero because multiplication by `p` is onto `H²` (local class
field theory: `H²(G_κ, κ̄ˣ) ≅ Br(κ) ≅ ℚ/ℤ` is divisible, `PT.p_dvd_H2_units_adicCompletion`),
so `H³(G_κ, μ_p) ≅ H³(G_κ, κ̄ˣ) = 0` (`PT.h3_units_adicCompletion_eq_zero`), and `μ_p ≅ 𝔽_p`
because `ζ_p ∈ κ` — this is exactly where the hypothesis `ζ ∈ k` is used.

The conclusion for `D_A` is then a transport of `Subsingleton` along the homeomorphic isomorphism
of topological groups `G_κ ≅ D_A` using `Work.SSGRoute.PT.h3Transfer` (the coefficients `𝔽_p` are
trivial, so the coefficient isomorphism is the identity).
-/

namespace Work.SSGRoute.PTembedding

open scoped Pointwise
open IsDedekindDomain.HeightOneSpectrum

theorem h3_triv_subsingleton_decomp (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζk : ζ ∈ (⊥ : IntermediateField k Ω)) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p) ↥(SSGRoute.decomp k A)) := by
  classical
  -- `Ω` is a separable closure of `k` (characteristic zero)
  have hSepΩ : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  -- the prime `𝔭` of `k` below `A`, and the completion `κ = k_𝔭`
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    Submission.NeukirchUchida.primeOf A hA
  have hspec : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 :=
    Submission.NeukirchUchida.primeOf_spec A hA
  -- `ζ` travels to `κ`
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hζk
  rw [← hy] at hζ
  -- ## the vanishing at the completion
  have hlocal : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p)
      (Work.AbsoluteKummer.G (𝔭.adicCompletion k))) := by
    refine Work.SSGRoute.PTembedding.h3_triv_subsingleton_of_units_divisible p 𝔭 ?_ ?_
      (algebraMap k (𝔭.adicCompletion k) y) ?_
    · -- `H³(G_κ, κ̄ˣ) = 0`
      exact Work.SSGRoute.PT.h3_units_adicCompletion_eq_zero 𝔭
    · -- `H²(G_κ, κ̄ˣ)` is `p`-divisible
      intro x
      exact Work.SSGRoute.PT.p_dvd_H2_units_adicCompletion p 𝔭 x
    · -- the image of the primitive root is primitive
      exact (hζ.of_map_of_injective (algebraMap k Ω).injective).map_of_injective
        (algebraMap k (𝔭.adicCompletion k)).injective
  -- ## the identification `D_A ≃* Gal(κ̄/κ)` is a homeomorphism
  let _ : Algebra (𝔭.adicCompletion k) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hspec).toAlgebra
  have halg : ∀ z : 𝔭.adicCompletion k,
      (algebraMap (𝔭.adicCompletion k) (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hspec z := fun _ => rfl
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hspec) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k 𝔭 :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔭 A hspec
  -- `D_A ≃* Gal(κ^sep/κ)`, a homeomorphism for the Krull topologies
  let e₁ : ↥(SSGRoute.decomp k A) ≃*
      Gal(SeparableClosure (𝔭.adicCompletion k)/𝔭.adicCompletion k) :=
    NK.Mine.localGaloisEquiv 𝔭 A hspec halg hW
  have he₁ : IsHomeomorph (e₁ : ↥(SSGRoute.decomp k A) →
      Gal(SeparableClosure (𝔭.adicCompletion k)/𝔭.adicCompletion k)) :=
    Work.SSGRoute.isHomeomorph_localGaloisEquiv k Ω A hA
  -- the two separable closures `κ^sep` and `κ̄` of `κ` are isomorphic over `κ`
  have hSepAlg : IsSepClosure (𝔭.adicCompletion k) (AlgebraicClosure (𝔭.adicCompletion k)) :=
    IsSepClosure.of_isAlgClosure_of_perfectField _ _
  let eS : SeparableClosure (𝔭.adicCompletion k) ≃ₐ[𝔭.adicCompletion k]
      AlgebraicClosure (𝔭.adicCompletion k) :=
    IsSepClosure.equiv (𝔭.adicCompletion k) (SeparableClosure (𝔭.adicCompletion k))
      (AlgebraicClosure (𝔭.adicCompletion k))
  -- `Gal(κ^sep/κ) ≃* Gal(κ̄/κ)`, again a homeomorphism
  let e₂ : Gal(SeparableClosure (𝔭.adicCompletion k)/𝔭.adicCompletion k) ≃*
      Work.AbsoluteKummer.G (𝔭.adicCompletion k) := AlgEquiv.autCongr eS
  have he₂ : IsHomeomorph (e₂ : Gal(SeparableClosure (𝔭.adicCompletion k)/𝔭.adicCompletion k) →
      Work.AbsoluteKummer.G (𝔭.adicCompletion k)) := NK.Mine.isHomeomorph_autCongr eS
  -- ## transfer the vanishing along the homeomorphic isomorphism
  have hΦ : IsHomeomorph ((e₁.trans e₂).symm : Work.AbsoluteKummer.G (𝔭.adicCompletion k) →
      ↥(SSGRoute.decomp k A)) :=
    NK.Mine.isHomeomorph_symm (e₁.trans e₂) (NK.Mine.isHomeomorph_trans e₁ e₂ he₁ he₂)
  have hΨ : ∀ (g' : Work.AbsoluteKummer.G (𝔭.adicCompletion k))
      (m' : Work.SSGRoute.Triv p),
      (AddEquiv.refl (Work.SSGRoute.Triv p)) (g' • m') =
        (e₁.trans e₂).symm g' • (AddEquiv.refl (Work.SSGRoute.Triv p)) m' := fun _ _ => rfl
  exact ⟨fun a b => (Work.SSGRoute.PT.h3Transfer ((e₁.trans e₂).symm) hΦ
    (AddEquiv.refl (Work.SSGRoute.Triv p)) hΨ).symm.injective (hlocal.elim _ _)⟩

end Work.SSGRoute.PTembedding
