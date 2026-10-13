/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The perfected model of `RΓ(X,𝒪_X)`: injectivity, root surjectivity, almost acyclicity

This module assembles, from the three clauses of `DSMap.Mix2.AlmostAcyc` proved in
`PerfAcyclic.lean`, `almostAcyc_zero_gen.lean` and `almostAcyc_succ.lean`, the statement that
the coaugmented Čech complex `W → Č(U, 𝒪_X^{1/p^∞})` of the perfected structure presheaf is
almost acyclic, together with the two ring-theoretic properties of `ψW : Γ(X,⊤) → W` needed by
node `PERF`: injectivity and the statement that `W` is generated over `Γ(X,⊤)` by the root tower
(`W` is the perfection of `Γ(X,⊤)`, so every element is `ψW x` to some `p`-power root).
-/
import Mathlib
import Submission.Work.DSEQP.PerfAcyclic
import Submission.Work.DSEQP.perf_frobEquiv_symm_of
import Submission.Work.DSMap.Mix2

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (.of A)} {ι : Type u}

/-- The canonical map `Γ(X,⊤) → W` into the perfection is injective. -/
theorem ψW_injective (S : PerfSetup A p X f) : Function.Injective S.ψW := by
  haveI := isReduced_gamma (X := X) (⊤ : X.Opens)
  intro x y h
  have hsub : Perf.of (Γ(X, ⊤)) p (S.hpU ⊤) 0 (x - y) = 0 := by
    change S.ψW (x - y) = 0
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp
    (Perf.of_eq_zero (R := Γ(X, ⊤)) (p := p) (hp := S.hpU ⊤) hsub)

/-- The `n`-fold inverse Frobenius applied to `ψW x` is the level `n` representative of `x`. -/
theorem frobEquiv_symm_iter_ψW (S : PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (n : ℕ) (x : Γ(X, ⊤)) :
    ((frobeniusEquiv S.W p).symm^[n]) (S.ψW x) = Perf.of (Γ(X, ⊤)) p (S.hpU ⊤) n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    haveI := S.charP_gamma
    exact perf_frobEquiv_symm_of (Γ(X, ⊤)) p (S.hpU ⊤) n x

/-- Every element of `W` is the `n`-th `p`-power root of the image of some global section. -/
theorem exists_frobEquiv_symm_iter (S : PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (w : S.W) :
    ∃ (n : ℕ) (x : Γ(X, ⊤)), w = ((frobeniusEquiv S.W p).symm^[n]) (S.ψW x) := by
  obtain ⟨n, x, hx⟩ := Perf.exists_of (R := Γ(X, ⊤)) (p := p) (hp := S.hpU ⊤) w
  exact ⟨n, x, by rw [S.frobEquiv_symm_iter_ψW n x]; exact hx.symm⟩

/-- **The almost acyclicity of the perfected Čech complex**, assembled from its three clauses.
Clause 1 is the hypothesis `h1`, clause 2 the hypothesis `h2`, clause 3 the hypothesis `h3`
(the ideal is `⊥`, so the memberships `∈ ⊥ • ⊤` become equalities). -/
theorem almostAcyc_perf (S : PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (U : ι → X.Opens) (g : A)
    (h1 : ∀ w : S.W, (S.eK U).hom w = 0 → ∀ k, S.varpi g k * w = 0)
    (h2 : ∀ (ϖ : S.W) (z : (S.K U).X 0), ((S.K U).d 0 1).hom z = 0 →
      ∃ w : S.W, ϖ • z = (S.eK U).hom w)
    (h3 : ∀ (q k : ℕ) (z : (S.K U).X (q + 1)), ((S.K U).d (q + 1) (q + 2)).hom z = 0 →
      ∃ y : (S.K U).X q, S.varpi g k • z = ((S.K U).d q (q + 1)).hom y) :
    DSMap.Mix2.AlmostAcyc (fun k => ((frobeniusEquiv S.W p).symm^[k]) (S.ψW (DSMap.phi A X f g)))
      ⊥ (S.K U) (S.eK U) := by
  change DSMap.Mix2.AlmostAcyc (fun k => S.varpi g k) ⊥ (S.K U) (S.eK U)
  refine ⟨?_, ?_, ?_⟩
  · intro w hw k
    have hw0 : (S.eK U).hom w = 0 := by
      have hmem : (S.eK U).hom w ∈ (⊥ : Submodule S.W ((S.K U).X 0)) := by
        simpa only [Submodule.bot_smul] using hw
      simpa using hmem
    simpa only [Submodule.bot_smul, Submodule.mem_bot] using h1 w hw0 k
  · intro z hz k
    have hz0 : ((S.K U).d 0 1).hom z = 0 := by
      have hmem : ((S.K U).d 0 1).hom z ∈ (⊥ : Submodule S.W ((S.K U).X 1)) := by
        simpa only [Submodule.bot_smul] using hz
      simpa using hmem
    obtain ⟨w, hw⟩ := h2 (S.varpi g k) z hz0
    refine ⟨w, ?_⟩
    rw [Submodule.bot_smul, hw, sub_self]
    exact Submodule.zero_mem _
  · intro q z hz k
    have hz0 : ((S.K U).d (q + 1) (q + 2)).hom z = 0 := by
      have hmem : ((S.K U).d (q + 1) (q + 2)).hom z
          ∈ (⊥ : Submodule S.W ((S.K U).X (q + 2))) := by
        simpa only [Submodule.bot_smul] using hz
      simpa using hmem
    obtain ⟨y, hy⟩ := h3 q k z hz0
    refine ⟨y, ?_⟩
    rw [Submodule.bot_smul, hy, sub_self]
    exact Submodule.zero_mem _

end PerfSetup

end Work.DSEQP
