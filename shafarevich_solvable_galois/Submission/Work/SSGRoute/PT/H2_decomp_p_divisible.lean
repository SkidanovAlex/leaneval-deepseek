import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.homCoindDefs
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.SSGRoute.PT.resH2
import Submission.Work.SSGRoute.PTembedding.h3_decomp_subsingleton
import Submission.Work.SSGRoute.PTembedding.kummer_ses_decomp
import Submission.Work.SSGRoute.range_mapH2_eq_ker_deltaH3
import Submission.Work.SSGRoute.adjoin_primitiveRoot_isGalois_coprime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `p`-divisibility of `H²(D_A, Ωˣ)` for the decomposition group of a finite place

For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` over `k` and a prime
`p`, the second continuous cohomology of the decomposition group `D_A = decomp k A` with
coefficients in the units of `Ω` is `p`-divisible:

`∀ x : H²(D_A, Ωˣ), ∃ y, p • y = x`.

## The mathematics

`D_A` is the absolute Galois group of the local field `κ = k_𝔭` obtained by completing `k` at the
prime `𝔭` of `k` below `A`, so `H²(D_A, Ωˣ) ≅ Br(κ) ≅ ℚ/ℤ` is divisible; this is the local part of
Shafarevich's theorem (the `p = 2` correction of Shafarevich's paper: the relevant local Brauer
groups are divisible).

## The formal proof

Rather than identifying `H²(D_A, Ωˣ)` with the local Brauer group, the proof uses the *Kummer
sequence* over `D_A` and the vanishing of `H³(D_A, μ_p)`:

* `0 → μ_p(Ω) → Ωˣ →^{p} Ωˣ → 0` is a short exact sequence of discrete `D_A`-modules
  (`MupCard.exists_kummerSES_decomp`, with `M = μ_p ⊆ k(ζ_p)`);
* in the `2 → 3` segment of the long exact sequence the connecting map
  `δ³ : H²(D_A, Ωˣ) → H³(D_A, μ_p)` has the image of `H²(π)` — i.e. of multiplication by `p` — as
  its kernel (`range_mapH2_eq_ker_deltaH3`);
* `H³(D_A, μ_p) = 0` because `cd_p(D_A) ≤ 2` (`PTembedding.h3_decomp_subsingleton`, the local
  vanishing `H³` of a decomposition group, in turn coming from the `p`-Sylow route and the
  `p`-divisibility of the local Brauer group `H²(G_κ, κ̄ˣ)`), so `δ³ = 0` and multiplication by `p`
  on `H²(D_A, Ωˣ)` is surjective.

The hypothesis `IsFinPlace k A` is exactly what makes `D_A` the absolute Galois group of a
non-archimedean local field: a `ValuationSubring` of `Ω` is the unit ball of an ultrametric
valuation, so archimedean places are not represented by `ValuationSubring`s (see
`HomFormReduction.isFinPlace_iff_ne_top`).
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

open Work.SSGRoute.PTembedding.MupCard

theorem H2_decomp_p_divisible (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    ∀ x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)), ∃ y, p • y = x := by
  classical
  -- `Ω` has characteristic `0` and contains a primitive `p`-th root of unity.
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI hAlgCl : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hNeZero : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  -- the field `K = k(ζ)` is finite Galois over `k`, and contains every `p`-th root of unity of `Ω`
  obtain ⟨hgalζ, hfinζ, _hcopζ⟩ := Work.SSGRoute.adjoin_primitiveRoot_isGalois_coprime p k Ω ζ hζ
  let K : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hfinK : FiniteDimensional k K := hfinζ
  haveI hgalK : IsGalois k K := hgalζ
  have hζK : ζ ∈ K := IntermediateField.subset_adjoin k ({ζ} : Set Ω) (Set.mem_singleton ζ)
  haveI hFt : Fintype (K ≃ₐ[k] K) := AlgEquiv.fintype k K
  haveI hcomm : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (MuAdd p K) :=
    Work.SSGRoute.PTembedding.MupCard.instSMulCommClassMuAdd (p := p) K
  -- the Kummer sequence `0 → μ_p(K) → Ωˣ →^{p} Ωˣ → 0` over `D_A`
  obtain ⟨S, _hSiota, hSpi⟩ :=
    exists_kummerSES_decomp (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) A hA
  -- `H³(D_A, μ_p) = 0` (`cd_p(D_A) ≤ 2` at the decomposition group of a finite place)
  let P : Sylow p (K ≃ₐ[k] K) := default
  have h3van : Subsingleton (Work.SSGRoute.H3 (M := MuAdd p K) ↥(SSGRoute.decomp k A)) :=
    Work.SSGRoute.PTembedding.h3_decomp_subsingleton p k Ω K ζ hζ hζK P A hA (M := MuAdd p K)
  haveI : Subsingleton (Work.SSGRoute.H3 (M := MuAdd p K) ↥(SSGRoute.decomp k A)) := h3van
  -- hence the connecting map `δ³ : H²(D_A, Ωˣ) → H³(D_A, μ_p)` vanishes,
  -- and `H²(Ωˣ →^{p} Ωˣ)` is surjective
  have hdelta : S.deltaH3 = 0 := AddMonoidHom.ext (fun x => Subsingleton.elim _ _)
  have hrange : (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant).range = ⊤ := by
    rw [Work.SSGRoute.range_mapH2_eq_ker_deltaH3 S, hdelta, AddMonoidHom.ker_zero]
  have hsurj : Function.Surjective (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant) :=
    AddMonoidHom.range_eq_top.mp hrange
  -- the projection `π` of the Kummer sequence is multiplication by `p` on `Ωˣ`
  have hpi : ∀ a : Additive (Units Ω), S.pi a = p • a :=
    fun a => (hSpi a).trans (powPi_eq_nsmul a)
  have key : ∀ z : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant z = p • z := by
    intro z
    obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))).comap
        (Work.AbsoluteKummer.Z2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))).subtype) z
    rw [← hc]
    show Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant
        (Work.AbsoluteKummer.H2π ↥(SSGRoute.decomp k A) (Additive (Units Ω)) c)
      = p • Work.AbsoluteKummer.H2π ↥(SSGRoute.decomp k A) (Additive (Units Ω)) c
    rw [Work.AbsoluteKummer.mapH2_H2π]
    have hz : Work.AbsoluteKummer.mapZ2 S.pi S.pi_equivariant c = p • c := by
      apply Subtype.ext
      funext q
      change S.pi ((c : ↥(SSGRoute.decomp k A) × ↥(SSGRoute.decomp k A) → Additive (Units Ω)) q)
        = p • ((c : ↥(SSGRoute.decomp k A) × ↥(SSGRoute.decomp k A) → Additive (Units Ω)) q)
      exact hpi _
    rw [hz, map_nsmul]
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  exact ⟨y, (key y).symm.trans hy⟩

end Work.SSGRoute.PT
