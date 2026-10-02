import Mathlib
import Submission.Work.StemsB.AToolsR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Transfer of the cup-map property along a map of pairs, in a *range*

`Work.StemsB.cupMap_transfer_iffR` transports the statement "the map
`x ↦ π^*(x) ⌣ σ` is bijective in **every** degree" along a map of pairs `f` whose induced map
on relative cohomology is bijective in **every** degree.

The Thom statements of this project (`Work.Serre.ThomCylAt`, `Work.Serre.EulerFibreRange`,
`Work.Serre.ThomIsoCylFibreRange`, ...) are only stated in a *range* of degrees (the range dictated
by the vanishing of the rational homology of the fibre), and in that situation the map of pairs
whose relative cohomology has to be checked is typically only an isomorphism in the range as well.
The present file provides the range-limited forms: if `f` induces bijections on relative
cohomology in all degrees `≤ K`, then the cup-map property in the range `k + n ≤ K` transfers in
both directions.

The proofs are the ones of `Work.StemsB.cupMap_transfer_iffR` (naturality of the mixed cup product
`Work.StemsB.mixedCupC_pairNaturalR` plus the two-out-of-three argument for bijections), with every
`IsIso`/bijectivity hypothesis restricted to the range that is actually used: at degree `k` the
argument consumes the relative cohomology at degree `k + n` and the cup map at degree `k`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

/-- **Transport of the cup-map property along a map of pairs, in a range.**

Let `f : C(Y,X)` map the pair `(Y,B)` into the pair `(X,A)`, let `πX : C(X,Z)`, `πY : C(Y,Z)`
satisfy `πX ∘ f = πY`, let `σ ∈ H^n(X,A;R)` and let `K : ℕ`.

If `f^* : H^m(X,A;R) → H^m(Y,B;R)` is bijective for every `m ≤ K`, then for every `k` with
`k + n ≤ K`:
  `x ↦ πX^*(x) ⌣ σ` is bijective (on `H^k(Z;R)`)  ⟺
  `x ↦ πY^*(x) ⌣ f^*(σ)` is bijective (on `H^k(Z;R)`). -/
theorem cupMap_transfer_iffR_range {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (R : Type) [CommRing R]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (K : ℕ) (hfbij : ∀ m, m ≤ K →
      Function.Bijective (Work.Thom.relCohMap f B A hf R m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (σ : Work.Thom.RelCoh R n X A) :
    (∀ k, k + n ≤ K → Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R A k n) ((Work.Thom.CohMap πX R k).hom x) σ)) ↔
      (∀ k, k + n ≤ K → Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R B k n) ((Work.Thom.CohMap πY R k).hom x)
          ((Work.Thom.relCohMap f B A hf R n).hom σ))) := by
  have hCoh : ∀ (k : ℕ) (x : Work.Thom.Coh R k Z),
      (Work.Thom.CohMap f R k).hom ((Work.Thom.CohMap πX R k).hom x)
      = (Work.Thom.CohMap πY R k).hom x := by
    intro k x
    have h := LinearMap.congr_fun (Work.Thom.CohMap_linear_comp f πX R k) x
    simp only [LinearMap.comp_apply] at h
    rw [h, hπ]
  have key : ∀ (k : ℕ) (x : Work.Thom.Coh R k Z),
      (Work.Thom.mixedCupC R B k n) ((Work.Thom.CohMap πY R k).hom x)
          ((Work.Thom.relCohMap f B A hf R n).hom σ)
        = (Work.Thom.relCohMap f B A hf R (k + n)).hom
            ((Work.Thom.mixedCupC R A k n) ((Work.Thom.CohMap πX R k).hom x) σ) := by
    intro k x
    rw [Work.StemsB.mixedCupC_pairNaturalR R f B A hf k n ((Work.Thom.CohMap πX R k).hom x) σ,
      hCoh k x]
  constructor
  · intro h k hk
    rw [funext (key k)]
    exact (hfbij (k + n) hk).comp (h k hk)
  · intro h k hk
    refine ⟨fun a b hab => ?_, fun b => ?_⟩
    · have h2 := congrArg (fun z => (Work.Thom.relCohMap f B A hf R (k + n)).hom z) hab
      rw [← key k a, ← key k b] at h2
      exact (h k hk).1 h2
    · obtain ⟨x, hx⟩ := (h k hk).2 ((Work.Thom.relCohMap f B A hf R (k + n)).hom b)
      exact ⟨x, (hfbij (k + n) hk).1 (by
        dsimp only at hx
        rw [key k x] at hx
        exact hx)⟩

/-- **The forward form** (in a range): a Thom class on the `X`-side descends to one on the
`Y`-side, with the cup-map property in the range `k + n ≤ K`. -/
theorem cupMap_transfer_fwdR_range {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (R : Type) [CommRing R]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (K : ℕ) (hfbij : ∀ m, m ≤ K →
      Function.Bijective (Work.Thom.relCohMap f B A hf R m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (σ : Work.Thom.RelCoh R n X A)
    (hσ : ∀ k, k + n ≤ K → Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R A k n) ((Work.Thom.CohMap πX R k).hom x) σ)) :
    ∀ k, k + n ≤ K → Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R B k n) ((Work.Thom.CohMap πY R k).hom x)
          ((Work.Thom.relCohMap f B A hf R n).hom σ)) :=
  (cupMap_transfer_iffR_range R f A B hf K hfbij πX πY hπ n σ).mp hσ

/-- **The backward form** (in a range): a Thom class on the `Y`-side lifts to one on the `X`-side,
with the cup-map property in the range `k + n ≤ K`. -/
theorem cupMap_transfer_bwdR_range {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (R : Type) [CommRing R]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (K : ℕ) (hfbij : ∀ m, m ≤ K →
      Function.Bijective (Work.Thom.relCohMap f B A hf R m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (τ : Work.Thom.RelCoh R n Y B)
    (hK : n ≤ K)
    (hτ : ∀ k, k + n ≤ K → Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R B k n) ((Work.Thom.CohMap πY R k).hom x) τ)) :
    ∃ τ' : Work.Thom.RelCoh R n X A,
      (Work.Thom.relCohMap f B A hf R n).hom τ' = τ ∧
      ∀ k, k + n ≤ K → Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R A k n) ((Work.Thom.CohMap πX R k).hom x) τ') := by
  obtain ⟨σ, hσ⟩ := (hfbij n hK).2 τ
  exact ⟨σ, hσ, (cupMap_transfer_iffR_range R f A B hf K hfbij πX πY hπ n σ).mpr
    (by rw [hσ]; exact hτ)⟩

end

end Work.Serre.DiscPair
