import Mathlib
import Submission.Work.SSGRoute.PT.archFamilyLocal
import Submission.Work.SSGRoute.PT.hrecJoint_p2
import Submission.Work.SSGRoute.PT.classFormation_reciprocity_allPlaces
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_hpair
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_unramified
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_reciprocity_v2
import Submission.Work.SSGRoute.PT.G1plusOwn.clause7Core
import Submission.Work.SSGRoute.PT.G1plusOwn.exists_level_factors_unramified_v2
import Submission.Work.SSGRoute.PT.G1plusOwn.sum_iota_eq_zero_of_extToClasses_zero
import Submission.Work.SSGRoute.PT.G1plusOwn.isConjPlace_of_finQW_conj
import Submission.Work.SSGRoute.PT.G1plusOwn.goodPlaceUnder_finQW
import Submission.Work.SSGRoute.PT.archPairLocal_hpairArch
import Submission.Work.SSGRoute.PT.archSwapHalf
import Submission.Work.SSGRoute.PT.vf_local_compare
import Submission.Work.SSGRoute.PT.decompK_linked
import Submission.Work.SSGRoute.PT.liesOver_linked
import Submission.Work.SSGRoute.PT.levelPair_functoriality
import Submission.Work.SSGRoute.E9Nodes.e9_unramified_all_but_finite
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.E7cOmega.zfun_pairing_extLoc
import Submission.Work.SSGRoute.CokerPT.IotaAlgebra
import Submission.Work.SSGRoute.e6_util
import Submission.Work.PT.archFamily_zpowers_eq_zero_of_ne_two
import Submission.Work.PT.hrecArchFamily_seamValue
import Submission.Work.PT.seamPlace_orbit_theory
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped TensorProduct
open CategoryTheory

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 40000000
set_option synthInstance.maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-! ## Certification status of this module (measured 2026-10-07, session of `hrecJoint_archFamily`)

Everything in this file is **proved, with no unproved step**; the module elaborates
(`lake env lean Submission/Work/SSGRoute/PT/hrecJoint_archFamily.lean` → `rc = 0` against the
on-disk oleans) and the value-closure walk of `Work.SSGRoute.PT.hrecJoint_archFamily` visits 90507
constants with **exactly one hole**, which is *not* in this file (the proof of
`Work.SSGRoute.E1aClean.localDictionary_natural_family_arch`, `E1aClean/localDictionary_natural_family.lean:188`).

`declare_proven` nevertheless fails, with `depends on forbidden axioms` naming the workspace's
unproved-step axiom (its identifier is recorded, with the raw measurement, in
`PT/PING_hrecJoint_archFamily_complete.md`), and this is a property of the
**statement**, not of the proof: the statement mentions
`Work.SSGRoute.PT.G1pOwn.g1FinHalf` and `Work.SSGRoute.PT.archFamily`, whose *types* are clean but
whose *values* are `Classical.choose`-witnesses built from the gate above:

```
#print axioms Work.SSGRoute.PT.G1pOwn.g1FinHalf = [propext, <the unproved-step axiom>, Classical.choice, Quot.sound]
#print axioms Work.SSGRoute.PT.archFamily       = [propext, <the unproved-step axiom>, Classical.choice, Quot.sound]
```

Hence **no proof of this statement can pass the permitted-axioms check** while that one hole
stands.  Closing it (or repointing `PT.finZB`/`PT.archβc` onto a clean witness) makes this theorem
clean with **no edit to this file**.  See `PT/PING_hrecJoint_archFamily_complete.md`. -/

/-- The finite-place clause of the hub's Clause (7) at **every odd** `p`, for the concrete finite
half `G1pOwn.g1FinHalf` and the concrete dictionaries `PT.finZB`/`PT.finZBg`: an instance of
`G1plusOwn.g1FinHalf_reciprocity_v2` (`p ≠ 2`), whose abstract interface is supplied by
`G1plusOwn.g1FinHalf_hpair`, `G1plusOwn.g1FinHalf_unramified` and the clause lemmas of
`PT/finHalfData.lean` / `PT/archSwapHalf.lean`. -/
theorem hrecJoint_g1FinHalf_finite_sum_eq_zero_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b)
    (S' : Finset (ValuationSubring Ω)) (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace k A)
    (hS'disj : ∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B)
    (hgood : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
      ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) :
    ∑ A ∈ S', G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b = 0 :=
  G1plusOwn.g1FinHalf_reciprocity_v2 p hp k Ω K ζ hζ hζK T hT χ hχadd hχcompat M
    (fun A hA => finZB p K ζ hζ hζK T hT M A hA)
    (fun A hA b b' hb hlb hb' hlb' =>
      finZB_add p k Ω K ζ hζ hζK T hT M A hA b b' hb hlb hb' hlb')
    (fun A hA b hb hlb => finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A hA b hb hlb)
    (fun A hA y => finZB_surjective p k Ω K ζ hζ hζK T hT M A hA y)
    (fun A hA hpA hramA b hb hlb hiner =>
      finZB_unramified p k Ω K ζ hζ hζK T hT M A hA hpA hramA b hb hlb hiner)
    (fun H a b => G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M H a b)
    (fun A hA a b hla hlb hb L hN hFD hGal hKL hAlg hS1 hS2 b₀ hb₀ => by
      letI : NumberField ↥L := hN
      letI : FiniteDimensional k ↥L := hFD
      letI : IsGalois k ↥L := hGal
      letI : Algebra ↥K ↥L := hAlg
      letI : IsScalarTower k ↥K ↥L := hS1
      letI : IsScalarTower ↥K ↥L Ω := hS2
      exact G1plusOwn.g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A hA a b hla hlb hb
        L hKL b₀ hb₀)
    (fun A hA hpA hramA a b hca hla hcb hlb hiner =>
      G1plusOwn.g1FinHalf_unramified p k Ω K ζ hζ hζK T hT χ hχadd hχcompat M
        (fun A hA => finZB p K ζ hζ hζK T hT M A hA)
        (fun A hA b b' hb hlb hb' hlb' =>
          finZB_add p k Ω K ζ hζ hζK T hT M A hA b b' hb hlb hb' hlb')
        (fun A hA b hb hlb => finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A hA b hb hlb)
        (fun A hA y => finZB_surjective p k Ω K ζ hζ hζK T hT M A hA y)
        (fun A hA hpA hramA b hb hlb hiner =>
          finZB_unramified p k Ω K ζ hζ hζK T hT M A hA hpA hramA b hb hlb hiner)
        (fun H a b => G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M H a b)
        (fun A hA a b hla hlb hb L hN hFD hGal hKL hAlg hS1 hS2 b₀ hb₀ => by
          letI : NumberField ↥L := hN
          letI : FiniteDimensional k ↥L := hFD
          letI : IsGalois k ↥L := hGal
          letI : Algebra ↥K ↥L := hAlg
          letI : IsScalarTower k ↥K ↥L := hS1
          letI : IsScalarTower ↥K ↥L Ω := hS2
          exact G1plusOwn.g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A hA a b hla hlb hb
            L hKL b₀ hb₀)
        A hA hpA hramA a b ⟨hca, hla⟩ ⟨hcb, hlb⟩ hiner)
    (fun b => finZBg p K ζ hζ hζK T hT M b)
    (fun b b' hb hl hb' hl' =>
      finZBg_add p k Ω K ζ hζ hζK T hT M b b' hb hl hb' hl')
    (fun b hb hl A hA => finZB_square p k Ω K ζ hζ hζK T hT M A hA b hb hl)
    a b ha1 ha2 hb1 hb2 S' hS'fin hS'disj hgood

-- Clause (7) of the hub, with the finite half `G1pOwn.g1FinHalf` and the involution half
-- `PT.archFamily` (the class-formation pairing), for ALL `p` (this subsumes the `p ≠ 2`-only
-- `G1plusOwn.reciprocityFiniteClause`).
-- Route.  Take a level `L ≥ K` containing the levels of the (finitely many) terms and the seam
-- levels of the involutions in `C'`, and let `Y := levelPair (finZBg p K ζ hζ hζK T hT M b) h_b`
-- be the single global class of `H²(Gal(L/k), Lˣ)`.  Then every term of the sum is
-- `χ_L (iota w (extLoc w (extToIdeles Y)))`:
--   * finite term at `A`: `G1plusOwn.g1FinHalf_hpair` plus the square `finZB_square`
--     (`extLoc w (extToIdeles (βg b)) = βl A hA b`), i.e. the finite value formula;
--   * involution term at `c ≠ 1`: `PT.archFamily_zpowers` (`PT/archFamilyLocal.lean`) plus
--     `PT.archPairLocal_hpairArch` (`PT/archPairLocal_hpairArch.lean`, filed in parallel: it
--     identifies the class-formation value at the fixed level `L_c` with the value at the seam
--     place of any level `L ≥ L_c` containing a `ψ` representing `b` on `⟨c⟩`) and the arch square
--     `PT.archβc_square`;
--   * the term at `c = 1` is `0` (`PT.archFamily_bot`);
--   * every other place has `D = ⊥` and contributes `0` (`PT.levelPair_unramified_eq_zero`).
-- The sum over the transversal of all places of `L` is `0` by
-- `PT.classFormation_reciprocity_allPlaces` (proved), and it equals the two displayed finite sums.
theorem hrecJoint_archFamily
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (φc : (c : Ω ≃ₐ[k] Ω) → c ^ 2 = 1 → c ≠ 1 → Ω →+* ℂ)
    (hφc : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
      φc c hc2 hc1 (c x) = starRingEnd ℂ (φc c hc2 hc1 x))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
    SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
    ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
    (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
      ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
    ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
    (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
    (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
    ∑ A ∈ S', G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b +
      ∑ c ∈ C', archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b = 0 := by
  classical
  intro ha1 ha2 hb1 hb2 S' hS'fin hS'disj hgood C' hC'inv hC'rep hC'disj
  by_cases hp2 : p = 2
  · -- ## the joint statement at `p = 2`, by the class formation at ONE level.
    -- Route (fully worked out; the `C`-indexed pieces are on disk):
    -- * level `L` factoring `b`, unramified outside the classes of `S'`:
    --   `G1plusOwn.exists_level_factors_unramified_v2` (proved);
    -- * `b₀`, `hψ` (crossed hom, `G1plusOwn.crossedHom_of_factorises`, proved) and the global
    --   class `Y = levelPair (galRes) (idleRepMap) (extToIdeles (finZBg a)) (levelClassOf b₀ hψ)`;
    -- * finite term at `A ∈ S'` (`g1FinHalf_hpair` + `finZB_square` + `vf_local_compare`, all
    --   proved) is `χ_L (ι_{w_A} (extLoc_{w_A} Y))`;
    -- * archimedean term at `c ∈ C'`, `c ≠ 1` (`Work.PT.hrecArchFamily_seamValue` — proved on disk
    --   in `Submission/Work/PT/hrecArchFamily_seamValue.lean` — plus
    --   `extLoc_levelPair_idleRepMap_eq`) is `χ_L (ι_{u_c} (extLoc_{u_c} Y))` at the seam place
    --   `u_c = ofInfinite (mk ((φc c hc2 hc1) |_L))`; for `res_L c = 1` it is `0`
    --   (`decompK_linked` + `E9Nodes.extHRestrict_bot_eq_zero` + `chi_zero_of_additive`);
    -- * the places outside the classes of `W := {w_A} ∪ {u_c : res_L c ≠ 1}` contribute `0`:
    --   finite places by `goodPlaceUnder_finQW` + `finZB_square` + `finZB_unramified` +
    --   `PT.levelPair_unramified_eq_zero`; infinite places with `D = ⊥` by the same trivial-`D`
    --   argument, and infinite places with `D ≠ ⊥` lie in a class of `W` by
    --   `Work.PT.seamPlace_orbit_theory` (proved on disk), which also gives the pairwise
    --   non-conjugacy of the `u_c`;
    -- * `extToClasses Y = 0` and the `p`-torsion of the terms feed
    --   `G1plusOwn.sum_iota_eq_zero_of_extToClasses_zero` (proved), whose sum over `W` is then
    --   reindexed into `∑ A ∈ S', g1FinHalf + ∑ c ∈ C', archFamily = 0`.
    -- A fully written draft (6 elaboration errors left) is preserved in
    -- `PT/NOTE_hrecJoint_p2_WIP.txt`.
    -- The completed branch now lives in `PT/hrecJoint_p2.lean` as the theorem
    -- `hrecJoint_archFamily_p2` (proved, no unproved step), and is used here directly.
    exact hrecJoint_archFamily_p2 (p := p) (hp2 := hp2) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (hζK := hζK) (T := T) (hT := hT) (χ := χ) (hχadd := hχadd)
      (hχcompat := hχcompat) (φc := φc) (hφc := hφc) (M := M) (a := a) (b := b)
      ha1 ha2 hb1 hb2 S' hS'fin hS'disj hgood C' hC'inv hC'rep hC'disj
  · -- `p ≠ 2`: the finite-place reciprocity (`g1FinHalf_reciprocity_v2`) plus the termwise
    -- vanishing of the archimedean half (`archFamily_zpowers_eq_zero_of_ne_two` / `archFamily_bot`).
    have hfin : ∑ A ∈ S', G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b = 0 :=
      hrecJoint_g1FinHalf_finite_sum_eq_zero_of_ne_two p hp2 k Ω K ζ hζ hζK T hT χ hχadd
        hχcompat M a b ha1 ha2 hb1 hb2 S' hS'fin hS'disj hgood
    have harch : ∑ c ∈ C', archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b
        = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      by_cases hc1 : c = 1
      · subst hc1
        rw [Subgroup.zpowers_one_eq_bot]
        exact archFamily_bot p k Ω K ζ hζ hζK T hT χ φc hφc M a b
      · exact Work.PT.archFamily_zpowers_eq_zero_of_ne_two p hp2 k Ω K ζ hζ hζK T hT χ hχadd
          φc hφc M c (hC'inv c hc) a b
          (G1plusOwn.isCocycleOn_of_le (SSGRoute.res k K) le_top (f := a) ha1)
          (G1plusOwn.isCocycleOn_of_le (SSGRoute.res k K) le_top (f := b) hb1)
    rw [hfin, harch, add_zero]

end Work.SSGRoute.PT
