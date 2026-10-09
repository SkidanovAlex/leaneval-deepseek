import Mathlib
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
import Submission.Work.SSGRoute.TPatom.characterSeparation
import Submission.Work.SSGRoute.TPatom.detectionSingleBlock
import Submission.Work.SSGRoute.TPatom.blockSystemTransversal
import Submission.Work.SSGRoute.TPatom.shapiroTransport
import Submission.Work.SSGRoute.TatePoitouRoute.exists_shapiro_c
import Submission.Work.SSGRoute.Sha2Lib.levelCocycleDatum_of_components
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.TPatom.noninvariantLevelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-cocycle datum in the non-invariant case (the `TPatom` route)

This file is the interface between the *geometric* input of the non-invariant case of node `C6`
and the cohomological assembly (`Shapiro` cocycle + value formula + single-block detection) that
turns it into `PTdualControl.LevelCocycleDatum`.

## The geometric input

`exists_concentratedLevelData` (delegated, module `…TPatom.concentratedLevelData`) is the pure
arithmetic-geometric statement: for every `γ ∈ Gal(K/k)` there are

* a finite Galois level `L ⊇ K` over `k` inside `Ω`, a place `q' | w` with `p ∤ e(q'|q)`,
* an element `d ∈ D_{q'}` generating `D_{q'}/(D_{q'} ∩ Gal(L/K₁))` with `d ^ f` in the coefficient
  subgroup `H = Gal(L/K₁) = galRes⁻¹ N`,
* a character `y : H →* 𝔽_p`

such that

* the Shapiro cocycle of `y` vanishes on the inertia at `q'` (spelled: `y` kills the normal closure
  of the inertia in `Gal(L/k)`), and
* **concentration**: `y (c g (d ^ f)) = 1` exactly for the `g` whose image in `Gal(K/k)` avoids the
  double coset `D_w · γ · N` — i.e. the character detects only the blocks (places of `K₁` over
  `q ∩ k`) in the class of `γ`.

The concentration is the arithmetic content (a Kummer extension of `K₁` which is inert exactly at
the place corresponding to `γ`, built by Grünwald–Wang).  Everything else in this file is the
assembly: the Shapiro cocycle of `exists_shapiroCocycle_res`, the value formula of
`coindValueFormula_dirac` and the single-block detection `shapiroValue_ne_zero_of_single_block`.
-/

namespace Work.SSGRoute.TPatom

open CategoryTheory
open scoped Pointwise

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-- **The geometric input of the non-invariant case** (see the module docstring). -/
theorem exists_concentratedLevelData (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (γ : K ≃ₐ[k] K) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p)
      (d : ↥L ≃ₐ[k] ↥L) (f : ℕ)
      (hdH : d ^ f ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L))
      (y : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)) →* Multiplicative (ZMod p)),
      d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
      0 < f ∧
      (∀ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q'),
        ∃ m : ℕ, δ⁻¹ * d ^ m ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ m : ℕ, 0 < m → m < f → d ^ m ∉ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ x : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)),
        (x : ↥L ≃ₐ[k] ↥L) ∈
          Subgroup.normalClosure {σ : ↥L ≃ₐ[k] ↥L | SSGRoute.PTExt.IsInertiaAt q' σ} →
        y x = 1) ∧
      (∀ x : ↥L ≃ₐ[k] ↥L,
        y (TatePoitouRoute.cfunc (N.comap (SSGRoute.PTExt.galRes k K ↥L)) x
            (⟨d ^ f, hdH⟩ : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)))) = 1 ↔
          SSGRoute.PTExt.galRes k K ↥L x ∉
            concSet k K w N γ) := by
  sorry

end Work.SSGRoute.TPatom

namespace Work.SSGRoute.TPatom

theorem noninvariantLevelDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0)
    (hnoninv : μ.hom (⟨fun _ => 1, fun _ _ => rfl⟩ : (Rep.coind N.subtype
        (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))).V) = 0) :
    Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) μ := by
  sorry

end Work.SSGRoute.TPatom
