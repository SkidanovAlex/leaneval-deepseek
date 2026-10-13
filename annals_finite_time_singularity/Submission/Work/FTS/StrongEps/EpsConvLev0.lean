/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsConvLev0.lean`

The *level-`0`* convergence package `Work.FTS.StrongEps.ConvLev0H6` at **every** fake time
`τ ∈ Icc 0 T`, from

* the honesty hypotheses of the scheme (every slice `C^∞` on the open quadrant, honestly in `ℋ⁶`,
  uniformly bounded in `ℋ⁶`), which make the extraction `EpsConvSubseq` applicable at the *given*
  time `τ` and hence supply an *honest* limit there (this is what fixes the junk-integral gap of
  the sibling `EpsConvAll`);
* the level-`0` package at every **rational** time along the same subsequence `φ`;
* the `τ`-Lipschitz modulus `hequi` **of the profiles themselves** (the `(0,0)`-slot only — this is
  the difference from `EpsConvAllH`, whose modulus `hequi` is for all slots of order `≤ 4`).

The proof is the level-`0` shadow of `EpsConvAllH`:

1. apply `EpsConvSubseq` to the profile sequence `n ↦ slice (G (φ n)) τ`, obtaining a
   subsequence `ψ` of `φ` together with a limit `g` carrying the whole extraction package (the
   `C⁴`-clause and the `ℋ⁶`-bound of the conclusion are `g`'s, so no lower semicontinuity or
   congruence of integrals is needed);
2. the *profile* sequence at `τ` is uniformly Cauchy on every compact `K ⊆ Q0`: by `hequi` it is
   uniformly (in `n` and in `p ∈ K`) within `C |τ - σ|` of the profile sequence at a nearby
   **rational** time `σ`, which is Cauchy by `hconv` (`EpsConvH.uniform_cauchy_of_dense_lipschitz`
   plus density of `ℚ`, `EpsConvH.exists_rat_mem_Icc_close`);
3. a uniformly Cauchy sequence with a convergent subsequence converges to the same limit
   (`EpsConvH.of_uniform_cauchy`), so the profiles of the full `φ`-sequence converge to `g`.

The two general helpers of `EpsConvAllH` (`of_uniform_cauchy`, `uniform_cauchy_of_dense_lipschitz`,
`exists_rat_mem_Icc_close`) are imported and reused.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.ConvLev0Defs
import Submission.Work.FTS.StrongEps.EpsConvSubseq
import Submission.Work.FTS.StrongEps.EpsConvRat
import Submission.Work.FTS.StrongEps.EpsConvAllH

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

theorem EpsConvLev0 {α B T : ℝ} (hα : 0 < α) {G : ℕ → Work.FTS.Galerkin.Fam} {F : ℝ → Work.FTS.Galerkin.Fn} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hsm : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hhon : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice (G n) τ))
    (hb : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice (G n) τ) ≤ B)
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T ∩ Set.range (fun q : ℚ => (q : ℝ)),
      Work.FTS.StrongEps.ConvLev0H6 α B (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ) (F τ))
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K,
        ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |Work.FTS.Galerkin.slice (G n) τ p.1 p.2 - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2| ≤ C * |τ - τ'|) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∃ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.ConvLev0H6 α B (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ) f := by
  intro τ hτ
  -- the fresh extraction at the given time `τ` (source of the `C⁴`- and `ℋ⁶`-clauses)
  obtain ⟨ψ, g, hψ, hg⟩ := Work.FTS.StrongEps.EpsConvSubseq (α := α) (B := B) hα
    (G := fun n => Work.FTS.Galerkin.slice (G (φ n)) τ)
    (fun n k => hsm (φ n) τ hτ k)
    (fun n => hhon (φ n) τ hτ)
    (fun n => hb (φ n) τ hτ)
  refine ⟨g, ?_, hg.2.1, hg.2.2⟩
  intro K hK hKQ
  obtain ⟨C, hC, hCe⟩ := hequi K hK hKQ
  -- the subsequence `φ ∘ ψ` converges (its `(0,0)`-slot is the profile itself)
  have hsub : TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => Work.FTS.Galerkin.slice (G (φ (ψ n))) τ p.1 p.2)
      (fun p => g p.1 p.2) Filter.atTop K := by
    have h := hg.1 K hK hKQ 0 0 (by norm_num)
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] using h
  -- density of the rationals in `Icc 0 T`
  have hdense : ∀ τ' ∈ Set.Icc (0:ℝ) T, ∀ δ : ℝ, 0 < δ →
      ∃ σ ∈ Set.Icc (0:ℝ) T ∩ Set.range (fun q : ℚ => (q:ℝ)), |σ - τ'| ≤ δ :=
    fun τ' hτ' δ hδ => EpsConvH.exists_rat_mem_Icc_close hτ' hδ
  -- the `τ`-Lipschitz modulus, restricted to the profiles (the `(0,0)`-slot)
  have hlip : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ σ' ∈ Set.Icc (0:ℝ) T, ∀ n : ℕ, ∀ p ∈ K,
      |Work.FTS.Galerkin.slice (G (φ n)) σ p.1 p.2
        - Work.FTS.Galerkin.slice (G (φ n)) σ' p.1 p.2| ≤ C * |σ - σ'| :=
    fun σ hσ σ' hσ' n p hp => hCe (φ n) p hp σ hσ σ' hσ'
  -- the rational-time package, as the convergence of the profile family
  have hconvK : ∀ σ ∈ Set.Icc (0:ℝ) T ∩ Set.range (fun q : ℚ => (q:ℝ)),
      ∃ L : ℝ × ℝ → ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ p ∈ K,
        |Work.FTS.Galerkin.slice (G (φ n)) σ p.1 p.2 - L p| < ε := by
    intro σ hσ
    refine ⟨fun p => F σ p.1 p.2, fun ε hε => ?_⟩
    have h := (Metric.tendstoUniformlyOn_iff.mp ((hconv σ hσ).1 K hK hKQ)) ε hε
    filter_upwards [h] with n hn p hp
    have hn' := hn p hp
    simpa only [Real.dist_eq, abs_sub_comm] using hn'
  have hcau := EpsConvH.uniform_cauchy_of_dense_lipschitz (X := ℝ × ℝ) (s := K) (T := T)
    (D := Set.range (fun q : ℚ => (q:ℝ)))
    (u := fun σ n p => Work.FTS.Galerkin.slice (G (φ n)) σ p.1 p.2)
    (C := C) hC hdense hlip hconvK τ hτ
  refine EpsConvH.of_uniform_cauchy hψ.tendsto_atTop ?_ hsub
  intro ε hε
  obtain ⟨N, hN⟩ := hcau ε hε
  exact ⟨N, fun m hm n hn x hx => by rw [Real.dist_eq]; exact hN m hm n hn x hx⟩

end Work.FTS.StrongEps
