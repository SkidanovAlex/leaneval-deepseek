import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.PTdualControl.detectorDescent_main
import Submission.Work.SSGRoute.PTdualControl.isGalois_adjoin_isPrimitiveRoot
import Submission.Work.SSGRoute.PTdualControl.not_dvd_finrank_adjoin_isPrimitiveRoot
import Submission.Work.SSGRoute.PTdualControl.isCyclotomicExtension_adjoin_isPrimitiveRoot
import Submission.Work.SSGRoute.E9Nodes.e9_inertia_restrict
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified detector (`C6`) reduced to its `μ_p ⊆ K` case

The node `Work.Sha2Lib.unramifiedDetector` is stated for an *arbitrary* finite Galois extension
`K/k` of number fields and carries **no** hypothesis `μ_p ⊆ K`.  Every arithmetic route to it on
disk (Kummer theory / Shapiro--Grünwald, in `SSGRoute/E7cC`, `Work/Sha2Lib`, `SSGRoute/Sha2Lib`)
performs Kummer theory over `K` and therefore needs a primitive `p`-th root of unity *in* `K`; the
gap is documented in `Submission/Work/Sha2Lib/PING_indNormal_needs_mu_p_in_K.md` (whose suggested
fix (2) is precisely the brick proved here).

The two ingredients are

* the **base-change descent** `Work.SSGRoute.PTdualControl.IsUnramifiedDetector.of_baseChange`
  (`Submission/Work/SSGRoute/PTdualControl/detectorDescent_main.lean`): if the detector holds for
  `K'/k` at a place `w' | w` with the coefficient module `res_{K'/K} M`, and `p ∤ [K' : K]`, then it
  holds for `K/k` at `w` with `M`;
* the **`ζ_p`-adjoin** `K' = K⟮ζ_p⟯ ⊆ Ω`: its degree over `K` is at most `p - 1`, hence prime to
  `p`, and it contains a primitive `p`-th root of unity *by construction* — so the arithmetic lanes'
  `μ_p ⊆ K` theorems apply to it verbatim.

Since `Ω` is algebraically closed and an algebra over the number field `k`, it has characteristic
zero and hence contains a primitive `p`-th root of unity `ζ`; the level `K⟮ζ⟯` is then a
`{p}`-cyclotomic extension of `K` (`isCyclotomicExtension_adjoin_isPrimitiveRoot`), so it is
finite (`IsCyclotomicExtension.finiteDimensional`), Galois over `K`
(`IsCyclotomicExtension.isGalois`), Galois over `k` (`isGalois_adjoin_isPrimitiveRoot`) and a
number field (`IsCyclotomicExtension.numberField`); finally `p ∤ [K⟮ζ⟯ : K]`
(`not_dvd_finrank_adjoin_isPrimitiveRoot`).

## Main result

`unramifiedDetector_of_mup` : the node `C6` for an arbitrary finite Galois `K/k`, from the single
hypothesis `IsUnramifiedDetectorMup p k Ω` — the *same* statement with the extra hypothesis that `K`
contains a primitive `p`-th root of unity.  That is the form in which the arithmetic lanes
(`E7cC`, `Sha2Lib`, `SSGStage`) produce the node.
-/

namespace Work.SSGRoute.PTdualControl

open scoped IntermediateField
open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- An algebraically closed field which is an algebra over a number field has characteristic
zero. -/
theorem charZero_of_numberField_algebra (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] : CharZero Ω :=
  charZero_of_injective_algebraMap (algebraMap k Ω).injective

/-- An algebraically closed field of characteristic zero contains a primitive `p`-th root of
unity. -/
theorem exists_isPrimitiveRoot_of_isAlgClosed (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [CharZero Ω] : ∃ ζ : Ω, IsPrimitiveRoot ζ p := by
  haveI : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω p

/-- **The node `C6` in the case `μ_p ⊆ K`.**

This is the statement of node `C6` (`Work.Sha2Lib.unramifiedDetector`,
`Work.SSGRoute.Sha2Lib.IsUnramifiedDetector`) for an arbitrary finite Galois extension `K/k` of
number fields, with the *additional* hypothesis that `K` contains a primitive `p`-th root of unity
— the hypothesis under which Kummer theory over `K` is available, and hence the case the arithmetic
lanes prove.

`unramifiedDetector_of_mup` below shows that this single case implies the node in general. -/
def IsUnramifiedDetectorMup (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Algebra K Ω] [IsScalarTower k K Ω],
    (∃ ζ : K, IsPrimitiveRoot ζ p) →
    ∀ (w : NK.GlobalCFT.Place K)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (hwq : w = NK.GlobalCFT.Place.ofFinite q)
      (_hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
      (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M], (∀ m : M, p • m = 0) →
      (∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) →
      Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M

/-- **The `μ_p ⊄ K` gap of the node `C6` is closed.**

If the unramified detector holds whenever the field contains a primitive `p`-th root of unity
(`hMup`), then it holds for *every* finite Galois extension `K/k` of number fields — the statement
of `Work.Sha2Lib.unramifiedDetector`.

Proof: let `ζ ∈ Ω` be a primitive `p`-th root of unity (it exists because `Ω` is algebraically
closed and an algebra over the number field `k`), put `K' = K⟮ζ⟯ ⊆ Ω` and pick a place `q'` of `K'`
over `q`.  Then `[K' : K] ≤ p - 1`, so `p ∤ [K' : K]`, and `K'` contains a primitive `p`-th root of
unity, so `hMup` applies to `K'` with the pulled-back coefficient module `res_{K'/K} M` — with the
inertia hypothesis transported along `K ⊆ K'` (`e9_inertia_restrict`).  The base-change descent
`IsUnramifiedDetector.of_baseChange` then descends the detector back to `K`. -/
theorem unramifiedDetector_of_mup (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (hMup : IsUnramifiedDetectorMup p k Ω)
    (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Algebra K Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M := by
  haveI hchar : CharZero Ω := charZero_of_numberField_algebra k Ω
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isAlgClosed p Ω
  -- the cyclotomic level `K⟮ζ⟯` and its structure
  haveI hcyc : IsCyclotomicExtension ({p} : Set ℕ) K ↥(K⟮ζ⟯) :=
    isCyclotomicExtension_adjoin_isPrimitiveRoot p ζ hζ
  haveI hfdK : FiniteDimensional K ↥(K⟮ζ⟯) :=
    IsCyclotomicExtension.finiteDimensional ({p} : Set ℕ) K ↥(K⟮ζ⟯)
  haveI hgalK : IsGalois K ↥(K⟮ζ⟯) :=
    IsCyclotomicExtension.isGalois ({p} : Set ℕ) K ↥(K⟮ζ⟯)
  haveI hnf : NumberField ↥(K⟮ζ⟯) :=
    IsCyclotomicExtension.numberField ({p} : Set ℕ) K ↥(K⟮ζ⟯)
  haveI hfdk : FiniteDimensional k ↥(K⟮ζ⟯) := Module.Finite.trans K ↥(K⟮ζ⟯)
  haveI hgalk : IsGalois k ↥(K⟮ζ⟯) := isGalois_adjoin_isPrimitiveRoot p ζ hζ
  haveI htower : IsScalarTower k ↥(K⟮ζ⟯) Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have hpd : ¬ p ∣ Module.finrank K ↥(K⟮ζ⟯) := not_dvd_finrank_adjoin_isPrimitiveRoot p ζ hζ
  -- a place of `K⟮ζ⟯` over `q`
  obtain ⟨q', hq'L⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := ↥(K⟮ζ⟯)) q
  have hq'place : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite q) := NK.GlobalCFT.Place.liesOver_ofFinite hq'L
  -- the `μ_p ⊆ K⟮ζ⟯` case, applied with the pulled-back module
  have hζmem : ζ ∈ (K⟮ζ⟯ : IntermediateField K Ω) := IntermediateField.subset_adjoin K _ (by simp)
  have hζ' : IsPrimitiveRoot (⟨ζ, hζmem⟩ : ↥(K⟮ζ⟯)) p := by
    refine ⟨?_, fun l hl => hζ.dvd_of_pow_eq_one l ?_⟩
    · exact Subtype.ext (by simpa using hζ.pow_eq_one)
    · exact congrArg (fun x : ↥(K⟮ζ⟯) => (x : Ω)) hl
  have hLI : q'.asIdeal.LiesOver q.asIdeal := by
    rcases hq'place with ⟨w₀, v₀, h1, h2, h3⟩ | ⟨Q, Q₀, h1, h2, h3⟩
    · exact absurd h1 (by simp [NK.GlobalCFT.Place.ofFinite, NK.GlobalCFT.Place.ofInfinite])
    · have hQ : Q = q' := (NK.GlobalCFT.Place.ofFinite_inj.mp h1).symm
      have hQ₀ : Q₀ = q := (NK.GlobalCFT.Place.ofFinite_inj.mp h2).symm
      rwa [hQ, hQ₀] at h3
  have hpq' : ((p : NumberField.RingOfIntegers ↥(K⟮ζ⟯)) ∉ q'.asIdeal) := by
    intro hp
    refine hpq ?_
    rw [hLI.over, Ideal.mem_under]
    simpa using hp
  have hI' : ∀ σ : ↥(K⟮ζ⟯) ≃ₐ[k] ↥(K⟮ζ⟯), SSGRoute.PTExt.IsInertiaAt q' σ →
      ∀ n : Rep.res (SSGRoute.PTExt.galRes k K ↥(K⟮ζ⟯)) M,
        (Rep.res (SSGRoute.PTExt.galRes k K ↥(K⟮ζ⟯)) M).ρ σ n = n := by
    intro σ hσ n
    have hτ : SSGRoute.PTExt.IsInertiaAt q (SSGRoute.PTExt.galRes k K ↥(K⟮ζ⟯) σ) :=
      Work.SSGRoute.E9Nodes.e9_inertia_restrict k K ↥(K⟮ζ⟯) q q' hLI σ
        (SSGRoute.PTExt.galRes k K ↥(K⟮ζ⟯) σ)
        (fun x => (AlgEquiv.restrictNormal_commutes σ K x).symm) hσ
    exact hI (SSGRoute.PTExt.galRes k K ↥(K⟮ζ⟯) σ) hτ n
  have hdet : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k ↥(K⟮ζ⟯) Ω
      (NK.GlobalCFT.Place.ofFinite q') q' rfl (Rep.res (SSGRoute.PTExt.galRes k K ↥(K⟮ζ⟯)) M) :=
    hMup ↥(K⟮ζ⟯) ⟨⟨ζ, hζmem⟩, hζ'⟩ (NK.GlobalCFT.Place.ofFinite q') q' rfl hpq'
      (Rep.res (SSGRoute.PTExt.galRes k K ↥(K⟮ζ⟯)) M) hM hI'
  -- descend
  refine IsUnramifiedDetector.of_baseChange p k K ↥(K⟮ζ⟯) Ω w q hwq
    (NK.GlobalCFT.Place.ofFinite q') q' rfl ?_ hpd M hM hdet
  rw [hwq]
  exact hq'place

end Work.SSGRoute.PTdualControl
