import Mathlib
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
import Submission.Work.SSGRoute.Sha2Lib.levelCocycleDatum_of_components
import Submission.Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg
import Submission.Work.SSGRoute.Sha2Lib.detectorInvariantCase
import Submission.Work.Sha2Lib.rankOneLevelCocycleRoute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-cocycle datum of the rank-one brick: the constant-detected case

`Work.Sha2Lib.rankOneLevelDatumExists` asks for the datum
`LevelCocycleDatum p k K Ω w q hwq (coind_N^Γ 𝔽_p) μ` for **every** nonzero `D_w`-equivariant
functional `μ`.  This file settles the case in which `μ` does not kill the constant element
`1_M ∈ M.V` (the `Γ`-fixed vector of the coinduced permutation module) — one half of the case split
of the target (the other half, `μ(1_M) = 0`, is the genuinely open one; see
`Submission/Work/Sha2Lib/NOTE_rankOneLevelDatum_session2.md`).

The proof needs **no** Shapiro cocycle, no value formula and no Grünwald: the *constant* cocycle

  `z γ := (ψ γ).val • 1_M`      (`ψ` the additive character of `Gal(L/k)` attached to a character)

is a `1`-cocycle of `res_{galRes} M` as soon as `1_M` is `Γ`-fixed — this is the proved
`Work.SSGRoute.Sha2Lib.invariantCocycle`.  Choosing `L, q', ψ` from the proved
`Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg` (which kills the inertia —
so `z` vanishes pointwise there — and is nontrivial on some `σ ∈ D_{q'}`), the detecting value is

  `μ (z σ) = (ψ σ).val • μ (1_M) ≠ 0`

because `μ (1_M)` has additive order `p` and `0 < (ψ σ).val < p`.
-/

namespace Work.Sha2Lib

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

theorem levelCocycleDatum_of_constant (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
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
    (hconst : μ.hom (⟨fun _ : K ≃ₐ[k] K => (1 : ZMod p), by intro n g; rfl⟩ :
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))).V) ≠ 0) :
    Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K (AlgebraicClosure K) w q hwq
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) μ := by
  classical
  haveI : p.Prime := Fact.out
  -- ## the level, the place and the character
  obtain ⟨L, hnfL, hfdL, hgalL, q', hq'lies, he, _hf, χ, hχinertia, hχne⟩ :=
    Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg p k K
      (AlgebraicClosure K) q
  letI : NumberField ↥L := hnfL
  letI : FiniteDimensional k ↥L := hfdL
  letI : IsGalois k ↥L := hgalL
  -- ## the place lies over `w`, and the ramification index is prime to `p`
  have hq'w : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w := by
    rw [hwq]
    exact NK.GlobalCFT.Place.liesOver_ofFinite hq'lies
  have hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx q.asIdeal q'.asIdeal q.ne_bot, he]
    exact Nat.coprime_one_left p
  -- ## shorthand
  let M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
    Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))
  let A : Rep.{0} SSGRoute.PTExt.Coeff (↥L ≃ₐ[k] ↥L) :=
    Rep.res (SSGRoute.PTExt.galRes k K ↥L) M
  -- ## the additive character of `Gal(L/k)`
  let f : Additive (↥L ≃ₐ[k] ↥L) →+ ZMod p :=
    { toFun := fun a => Multiplicative.toAdd (χ (Additive.toMul a))
      map_zero' := by simp
      map_add' := by intro a b; simp }
  -- ## the constant (`Γ`-fixed) vector of the coinduced module
  let m : A.V := ⟨fun _ : K ≃ₐ[k] K => (1 : ZMod p), by intro n g; rfl⟩
  have hm : ∀ γ : ↥L ≃ₐ[k] ↥L, A.ρ γ m = m := by
    intro γ
    apply Subtype.ext
    funext g
    show m.val (g * SSGRoute.PTExt.galRes k K ↥L γ) = 1
    rfl
  -- ## the constant cocycle
  have hpTors : ∀ x : A.V, p • x = 0 := by
    intro x
    exact Work.Sha2Lib.coindPerm_psmul p k K N x
  have hcoc : (fun γ : ↥L ≃ₐ[k] ↥L => (f (Additive.ofMul γ)).val • m) ∈
      groupCohomology.cocycles₁ A :=
    Work.SSGRoute.Sha2Lib.invariantCocycle A p hpTors f m hm
  refine Work.SSGRoute.Sha2Lib.levelCocycleDatum_of_components p k K (AlgebraicClosure K) w q hwq
    M μ L q' hq'w hcop
    ⟨fun γ : ↥L ≃ₐ[k] ↥L => (f (Additive.ofMul γ)).val • m, hcoc⟩ ?_ ?_
  · -- ## the inertia clause: `ψ` kills the inertia at `q'`
    intro γ hγ
    have h1 : f (Additive.ofMul γ) = 0 := by
      show Multiplicative.toAdd (χ (Additive.toMul (Additive.ofMul γ))) = 0
      rw [toMul_ofMul, hχinertia γ hγ]
      rfl
    show (f (Additive.ofMul γ)).val • m = 0
    rw [h1]
    simp
  · -- ## the detection clause
    obtain ⟨σ, hσmem, hσχ⟩ := hχne
    refine ⟨σ, hσmem, ?_⟩
    have hfne : f (Additive.ofMul σ) ≠ 0 := by
      intro h0
      refine hσχ ?_
      have h1 : Multiplicative.toAdd (χ σ) = (0 : ZMod p) := h0
      exact Multiplicative.toAdd.injective (by rw [h1]; rfl)
    have hval : (f (Additive.ofMul σ)).val ≠ 0 := fun h =>
      hfne ((ZMod.val_eq_zero _).mp h)
    have hpos : 0 < (f (Additive.ofMul σ)).val := Nat.pos_of_ne_zero hval
    have hlt : (f (Additive.ofMul σ)).val < p := ZMod.val_lt _
    -- `μ m` has additive order `p`
    have hmne : μ.hom m ≠ 0 := hconst
    have hptors : p • (μ.hom m) = 0 := by
      have hpm : (p : ℕ) • m = 0 := hpTors m
      calc p • (μ.hom m) = μ.hom ((p : ℕ) • m) := (map_nsmul μ.hom p m).symm
        _ = μ.hom 0 := by rw [hpm]
        _ = 0 := map_zero μ.hom
    have hord : addOrderOf (μ.hom m) = p := by
      have h1 : addOrderOf (μ.hom m) ∣ p :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr hptors
      have h2 : addOrderOf (μ.hom m) ≠ 1 := fun h =>
        hmne (AddMonoid.addOrderOf_eq_one_iff.mp h)
      exact ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ h1).resolve_left h2
    show μ.hom ((f (Additive.ofMul σ)).val • m) ≠ 0
    rw [map_nsmul]
    intro h0
    have h2 : addOrderOf (μ.hom m) ∣ (f (Additive.ofMul σ)).val :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    rw [hord] at h2
    have h3 : p ≤ (f (Additive.ofMul σ)).val := Nat.le_of_dvd hpos h2
    omega

end Work.Sha2Lib
