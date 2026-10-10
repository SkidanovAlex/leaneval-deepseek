import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.twistLayer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # Step (E) of the Step-4 assembly: the local-cyclicity bridge

This module supplies the last unpinned piece of the Step-4 assembly (SW pp. 30–31, the local
target choice at the places where the ramification is new).

## The mechanism, in one line

At a place `A` where the level-`τ` solution is trivial (`φ|D_A = 1`), one has `D_A ≤ G_K`, so the
`Gal(K/ℚ)`-action on `E(n,τ)` is *trivial* on `D_A` and hence every `1`-coboundary vanishes on
`D_A` (`Work.SSGRoute.eq_zero_of_isCoboundaryOn`).  Theorem 13 gives, at each place of the finite
set `S`, that `x` differs from the prescribed local datum `z_A` (= the formal corestriction of `y`)
by a coboundary on `D_A` (`hxsplit` of `Work.SSGRoute.step4_transport_of_sha13_psi`); therefore

  `x σ = z_A σ` **pointwise** on `D_A`,

and if `z_A` is the local target `η_A` produced by `Work.SSGRoute.step4_local_target` (the datum
which makes the twist of `ψ` by `η_A` cyclic and inertia-generated at `A`), then the same holds for
the twist of `ψ` by `x` *by pointwise equality alone*.  That is the whole content of item (5) at
the places of `S`; outside the conjugates of `S` it is
`Work.SSGRoute.twist_cyclic_of_psi_trivial` together with Theorem 13's cyclicity clause.

## Contents

* `flowTwistE_congr_of_eq_on` : pointwise equality of two coefficient functions on a subgroup
  gives pointwise equality of the twists.
* `step4_local_cyclic_of_eq_on` : **the bridge.**  A local target `η` at `A` together with
  pointwise agreement of `x` with `η` on `D_A` yields the full local cyclicity bundle of the twist
  of `ψ` by `x` at `A`: `IsCyclic` of the closure of the image and inertia-generation.
* `eq_on_decomp_of_sub_coboundary` : the "pointwise" input: if `x - z` is a coboundary on `D_A` and
  `D_A ≤ G_K`, then `x = z` on `D_A`.

The two remaining inputs of the assembly are then exactly the two arithmetic sorries:
`coker_obstruction` (which realises the prescribed local data `η` by the class `y` over `K`) and
`shafarevich_theorem13` (which gives `x = cor y` with the coboundary clauses used here).

## The (A)–(F) assembly bundle, in full (the hand-off spec)

The remaining work item of the Step-4 lane is the lemma

  `step4_items_assembly : ∃ hxmul, IsLocConstOn ⊤ x ∧ (T¹ clause) ∧ (involution clause) ∧
    (x ramified ⇒ φ = 1) ∧ (item (5)) ∧ (item (6)) ∧ (x = 0 on T⁰)`

whose hypotheses are *exactly* the outputs of the four pieces, and nothing else:

* the level-`n` stage-3 clauses for `(φ, ψ)`: `IsScholzSolution p K n i j φ`,
  `LiftsFlow ψ φ`, `IsOpen ψ.ker`, `hψquot`, and the dichotomy `hProp` for `ψ`
  (these are delivered by the push-down, `Work.SSGRoute.properStage_pushdown`);

* `T⁰` with `⨆ A ∈ T⁰, (decomp ℚ A).map ψ = flowEKer p (K ≃ₐ[ℚ] K) n i j` and
  `IsCyclic` at every `A ∈ T⁰` (Chebotarev, `exists_T0_cyclic_of_surjective`);

* the transported arithmetic conclusion at the level-`n` datum, i.e. the hypothesis bundle of
  `Work.SSGRoute.step4_transport_of_sha13_psi` (`Λ`, `hΛker`, `S`, `hSfin`, `hSram`, `sec`,
  `hsec`, `y`, `hyT`, `hy0`, `x`, `hxcoc` = the `hxmul` witness, `hxsplit`, `hxnot`,
  `hxinertia`); its conclusion gives items (2) and (4) *immediately*, and with `LiftsFlow`
  item (4) becomes `∀σ ∈ D_A, φ σ = 1`;

* item (1) is `hxloc` (Theorem 13's local-constancy clause), item (3) is Theorem 13's involution
  clause, item (8) is `hxT⁰` (the paper's `x_p = 0` for `p ∈ T⁰`, from `T⁰ ⊆ S` with the local
  datum `0` at `T⁰`, which makes `x` a coboundary — hence zero, as `D_A ≤ G_K` — on `D_A`);

* item (5), in the two cases:
  – `A` conjugate to an element of `S`, `A ∉ T⁰`, `φ|D_A = 1`: the `hreal` shape of
    `step4_local_cyclic_of_eq_on` above — an `η` with the local-target bundle and `x = η`
    pointwise on `D_A`.  The pointwise agreement is what Theorem 13's `hxsplit` gives, by
    `eq_on_decomp_of_sub_coboundary` above (`D_A ≤ G_K`, so the coboundary ambiguity vanishes);
    the `η`-bundle is `Work.SSGRoute.step4_local_target` (already sorry-free), realised by `y`
    on the `coker_obstruction` side;
  – `A` not conjugate to any element of `S`: if `¬ IsSplitIn ℚ Λ A` then both `ψ` and `x` are
    unramified on `I_A ∩ G_K` (`hΛker` and `hxinertia`), so the twist itself is unramified there
    and item (5) is vacuous; if `IsSplitIn ℚ Λ A` then `ψ` is trivial on `D_A` and Theorem 13's
    cyclicity clause (`hcycOut` above) plus `Work.SSGRoute.twist_cyclic_of_psi_trivial`
    (sorry-free) gives the cyclicity;

* item (6): on `D_A` where the twist ramifies, either `φ(D_A) = 1` (item (5) and
  `Work.SSGRoute.inertia_map_eq_flowTwistEHom`, sorry-free, give the inertia statement), or
  `φ(D_A) ≠ 1`, in which case `A` is conjugate to an element of `S` and `hxnot` makes `x` a
  coboundary on `D_A`, so `Work.SSGRoute.isCyclic_map_flowTwistEHom_of_isCoboundaryOn` and
  `Work.SSGRoute.inertia_generates_flowTwistEHom_iff` (both sorry-free) transfer the cyclic branch.

Every lemma named besides `coker_obstruction` and `shafarevich_theorem13` is on disk and
`sorry`-free, and the two named ones supply precisely the `y`/`x` bundle above. -/

namespace Work.SSGRoute

open SSGRoute
open Work.CohomologicalShrinking

set_option maxHeartbeats 1000000

/-- **Pointwise equality of the coefficients gives pointwise equality of the twists.** -/
theorem flowTwistE_congr_of_eq_on (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (n i j : ℕ)
    {x η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j}
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    {H : Subgroup SSGRoute.GalQ} (heq : ∀ σ ∈ H, x σ = η σ) :
    ∀ σ ∈ H, flowTwistE p K n i j x ψ σ = flowTwistE p K n i j η ψ σ := by
  intro σ hσ
  simp only [flowTwistE, flowTwist, heq σ hσ]

/-- **The local-cyclicity bridge (step (E) of the assembly).**

At a finite place `A` not over `p` where the level-`τ` solution is trivial on `D_A` and `D_A ≤ G_K`,
suppose `x` agrees pointwise on `D_A` with a *local target* `η` — a datum additive on `D_A`, locally
constant, vanishing on the inertia, and such that the twist of `ψ` by `η` has cyclic local group
generated by the inertia (`Work.SSGRoute.step4_local_target` supplies such an `η`).  Then the twist
of `ψ` by `x` has the same two properties.

The hypothesis `∀ σ ∈ D_A, x σ = η σ` is exactly what Theorem 13 gives at the places of `S` (after
the coboundary ambiguity is killed by the triviality of the action on `D_A ≤ G_K`, see
`eq_on_decomp_of_sub_coboundary`), and what `coker_obstruction` realises on the `y`-side. -/
theorem step4_local_cyclic_of_eq_on (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (A : ValuationSubring SSGRoute.QBar)
    (hreal : ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
      (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
      IsCyclic (Subgroup.closure
        ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
      ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ) :
    IsCyclic (Subgroup.closure
        ((flowTwistE p K n i j x ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
      ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        flowTwistE p K n i j x ψ τ = flowTwistE p K n i j x ψ σ := by
  obtain ⟨η, -, -, -, hcyc, hinertia, heq⟩ := hreal
  have hfun := flowTwistE_congr_of_eq_on p K n i j ψ (H := SSGRoute.decomp ℚ A) heq
  have hset : flowTwistE p K n i j x ψ '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ)
      = flowTwistE p K n i j η ψ '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ) := by
    refine Set.ext fun y => ?_
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ, (hfun σ hσ).symm⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ, hfun σ hσ⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact hcyc
  · intro σ hσ
    obtain ⟨τ, hτ, hτeq⟩ := hinertia σ hσ
    have hτD : τ ∈ SSGRoute.decomp ℚ A := hτ.1
    exact ⟨τ, hτ, by rw [hfun τ hτD, hfun σ hσ, hτeq]⟩

/-- **The pointwise input to the bridge.**  If `x - z` is a `1`-coboundary on `D_A` and
`D_A ≤ G_K` (so that the `Gal(K/ℚ)`-action is trivial on `D_A`), then `x` and `z` agree pointwise
on `D_A`.  This is the step which turns Theorem 13's coboundary clause `hxsplit` at a place of `S`
into the pointwise agreement required by `step4_local_cyclic_of_eq_on`. -/
theorem eq_on_decomp_of_sub_coboundary (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (x z : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (A : ValuationSubring SSGRoute.QBar)
    (hDK : ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup)
    (h : SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A)
      (fun σ => x σ - z σ)) :
    ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = z σ := by
  intro σ hσ
  have h0 : x σ - z σ = 0 := eq_zero_of_isCoboundaryOn p K n i j h σ hσ (hDK σ hσ)
  exact sub_eq_zero.mp h0

end Work.SSGRoute
