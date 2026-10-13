/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsConvAllTau.lean`

The *level-`5`* (full slot) convergence package `Work.FTS.StrongEps.ConvLocUnifH6` at **every**
fake time `τ ∈ [0,T]`, from

* the honesty hypotheses of the scheme (`hsm`: every slice is `C^∞` on the open quadrant;
  `hhon`: every slice lies in the honest weighted space `ℋ⁶`; `hb`: a uniform `ℋ⁶`-bound for
  *all* `n` and `τ ∈ [0,T]`),
* the level-`0` package at every **rational** time along the subsequence `φ` (`hconv`),
* the `τ`-Lipschitz modulus of the **profiles themselves** (`hequi`: the `(0,0)`-slot only —
  this is the difference from `EpsConvAllH`, whose modulus covers all slots of order `≤ 4`).

So the statement proved here has a *stronger* conclusion than `EpsConvLev0` (which only recovers
the profile convergence at `τ`) and *weaker* hypotheses than `EpsConvAllH` (level-`0`
equicontinuity only).

## The argument

The point is that the higher slots need **no** hypothesis beyond the honesty of the slices: they
are pinned by the profile limit, because the derivatives of a function on an open set are local.

1. *The profiles at `τ` are uniformly Cauchy on every compact `K ⊆ Q0`.*  By `hequi` the profiles
   at `τ` differ from those at a rational `σ` by at most `C |τ - σ|`, uniformly in `n` and in the
   point of `K`; at `σ` they converge by `hconv`.  This is
   `EpsConvH.uniform_cauchy_of_dense_lipschitz` plus the density of `ℚ`
   (`EpsConvH.exists_rat_mem_Icc_close`).
2. *A candidate limit.*  The extraction `EpsConvSubseq` applies to the profile sequence at `τ`
   (that is where `hsm`, `hhon`, `hb` are consumed) and produces a subsequence `ψ` and a limit
   `g` carrying the whole package along `φ ∘ ψ`.  By `EpsConvH.of_uniform_cauchy` — Cauchy plus
   one convergent subsequence — the **full** profile sequence converges to `g` on every compact
   subset of `Q0`.
3. *Every subsequence has a further subsequence with the same limit.*  For any `u : ℕ → ℕ` with
   `u → ∞`, the extraction applies again to `n ↦ slice (G (φ (u n))) τ`, giving `ψ'` and `g'`;
   and `g' = g` on `Q0`, because both are limits of the same Cauchy profile sequence.  Since
   `g' = g` on the *open* quadrant, all the slots of `g'` and `g` agree there (locality of the
   iterated derivatives, `mixed_congr_of_quad`), so the slot `(j,i)` of the sub-subsequence
   converges to `mixed j i g`.
4. *Sub-subsequence principle.*  In a metric space a sequence converges to `L` as soon as every
   subsequence has a further subsequence converging to `L` (`tendstoUniformlyOn_of_subseq`, fed
   by `Filter.exists_seq_forall_of_frequently`).  This upgrades (3) to the convergence of the
   full slot sequence (and (2) already covers the level-`0` slot).

The `C⁴`- and `ℋ⁶`-clauses of the conclusion are inherited from the extraction in step 2, so no
lower semicontinuity or congruence of integrals is needed.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsConvLev0
import Submission.Work.FTS.StrongEps.EpsConvSubseq
import Submission.Work.FTS.StrongEps.ConvLev0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsConvTau

set_option autoImplicit false

/-! ## The sub-subsequence principle -/

/-- **A sequence converges to a limit as soon as every subsequence has a further subsequence
converging to that limit.**  Stated for `ℝ`-valued functions with the uniformity of uniform
convergence on a set `s`; the index map `u` only has to tend to infinity (repetitions are
allowed, which is what an extraction lemma produces).

Proof: if the conclusion failed, then `ε ≤ dist (f x) (F n x)` would hold *frequently* (with a
witness `x ∈ s`); `Filter.exists_seq_forall_of_frequently` turns that into a sequence `ns → ∞` of
bad indices, and the hypothesis applied to `ns` contradicts badness at a large index. -/
theorem tendstoUniformlyOn_of_subseq {X : Type*} {s : Set X} {F : ℕ → X → ℝ} {f : X → ℝ}
    (h : ∀ u : ℕ → ℕ, Tendsto u atTop atTop → ∃ ψ : ℕ → ℕ, Tendsto ψ atTop atTop ∧
      TendstoUniformlyOn (fun n => F ((u ∘ ψ) n)) f atTop s) :
    TendstoUniformlyOn F f atTop s := by
  by_contra hc
  rw [Metric.tendstoUniformlyOn_iff] at hc
  have hbad : ∃ ε > 0, ∃ᶠ n in atTop, ∃ x ∈ s, ε ≤ dist (f x) (F n x) := by
    by_contra hcon
    refine hc fun ε hε => ?_
    by_contra hnot
    refine hcon ⟨ε, hε, (Filter.not_eventually.mp hnot).mono ?_⟩
    intro n hn
    push Not at hn
    exact ⟨hn.choose, hn.choose_spec.1, hn.choose_spec.2⟩
  obtain ⟨ε, hε, hfreq⟩ := hbad
  obtain ⟨ns, hns, hbad'⟩ := Filter.exists_seq_forall_of_frequently hfreq
  obtain ⟨ψ, _, hconv⟩ := h ns hns
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  obtain ⟨n, hn⟩ := (hconv ε hε).exists
  exact not_lt.mpr (hbad' (ψ n)).choose_spec.2 (hn _ (hbad' (ψ n)).choose_spec.1)

/-! ## Locality of the mixed derivatives on the open quadrant -/

/-- Two functions agreeing on the open quadrant have the same iterated mixed derivatives there
(no smoothness needed: this is the locality of `deriv`).  The `D_θ`-analogue of
`Work.FTS.EllipticEst.SmoothOpen.DzIter_congr`. -/
theorem mixed_congr_of_quad {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) (j i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i f z θ = Work.Spaces.mixed j i g z θ := by
  have hDth : ∀ i : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i f z θ = Work.Spaces.DthIter i g z θ := by
    intro i
    induction i with
    | zero => exact fun z θ hz h1 h2 => h z θ hz h1 h2
    | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n f z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]
  intro z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i f) (G := Work.Spaces.DthIter i g)
    (fun z θ hz h1 h2 => hDth i z θ hz h1 h2) j z θ hz h1 h2

end Work.FTS.StrongEps.EpsConvTau

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

-- the statement carries the hypothesis `hφ`, which the proof does not need
set_option linter.unusedVariables false in
theorem EpsConvAllTau {α B T : ℝ} (hα : 0 < α) {G : ℕ → Work.FTS.Galerkin.Fam}
    {F : ℝ → Work.FTS.Galerkin.Fn} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hsm : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) τ))
        Work.FTS.EllipticEst.Q0)
    (hhon : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice (G n) τ))
    (hb : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice (G n) τ) ≤ B)
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T ∩ Set.range (fun q : ℚ => (q : ℝ)),
      Work.FTS.StrongEps.ConvLev0H6 α B (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ)
        (F τ))
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
        ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |Work.FTS.Galerkin.slice (G n) τ p.1 p.2
            - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2| ≤ C * |τ - τ'|) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∃ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ)
        f := by
  intro τ hτ
  -- **Step 1.** the profiles at `τ` are uniformly Cauchy on every compact subset of `Q0`:
  -- `hequi` compares them with the profiles at a rational time, where `hconv` gives convergence.
  have hcau : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ p ∈ K,
        |slice (G (φ m)) τ p.1 p.2 - slice (G (φ n)) τ p.1 p.2| < ε := by
    intro K hK hKQ ε hε
    obtain ⟨C, hC, hCe⟩ := hequi K hK hKQ
    exact EpsConvH.uniform_cauchy_of_dense_lipschitz (X := ℝ × ℝ) (s := K) (T := T)
      (D := Set.range (fun q : ℚ => (q : ℝ)))
      (u := fun σ n p => slice (G (φ n)) σ p.1 p.2) (C := C) hC
      (fun τ' hτ' δ hδ => EpsConvH.exists_rat_mem_Icc_close hτ' hδ)
      (fun σ hσ σ' hσ' n p hp => hCe (φ n) p hp σ hσ σ' hσ')
      (fun σ hσ => by
        refine ⟨fun p => F σ p.1 p.2, fun ε' hε' => ?_⟩
        have h := (Metric.tendstoUniformlyOn_iff.mp ((hconv σ hσ).1 K hK hKQ)) ε' hε'
        filter_upwards [h] with n hn p hp
        have hn' := hn p hp
        rw [Real.dist_eq, abs_sub_comm] at hn'
        exact hn')
      τ hτ ε hε
  -- **Step 2.** the extraction at the given time `τ` (this is where the honesty hypotheses are
  -- consumed); it produces the candidate limit `g` and its `C⁴`- and `ℋ⁶`-clauses.
  obtain ⟨ψ, g, hψ, hg⟩ := Work.FTS.StrongEps.EpsConvSubseq (α := α) (B := B) hα
    (G := fun n => slice (G (φ n)) τ)
    (fun n k => hsm (φ n) τ hτ k)
    (fun n => hhon (φ n) τ hτ)
    (fun n => hb (φ n) τ hτ)
  refine ⟨g, ?_, hg.2.1, hg.2.2⟩
  -- the profiles of the *full* sequence converge to `g` (Cauchy + convergent subsequence)
  have hfullAll : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => slice (G (φ n)) τ p.1 p.2)
        (fun p => g p.1 p.2) atTop K := by
    intro K hK hKQ
    refine EpsConvH.of_uniform_cauchy hψ.tendsto_atTop ?_ ?_
    · intro ε hε
      obtain ⟨N, hN⟩ := hcau K hK hKQ ε hε
      exact ⟨N, fun m hm n hn x hx => by rw [Real.dist_eq]; exact hN m hm n hn x hx⟩
    · have h := hg.1 K hK hKQ 0 0 (by norm_num)
      simpa only [Function.comp_def, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero]
        using h
  -- **Steps 3 and 4.** every subsequence has a further subsequence with the *same* limit; the
  -- sub-subsequence principle then gives the slot convergence of the full sequence.
  intro K hK hKQ j i hji
  refine EpsConvTau.tendstoUniformlyOn_of_subseq ?_
  intro u hu
  obtain ⟨ψ', g', hψ', hg'⟩ := Work.FTS.StrongEps.EpsConvSubseq (α := α) (B := B) hα
    (G := fun n => slice (G (φ (u n))) τ)
    (fun n k => hsm (φ (u n)) τ hτ k)
    (fun n => hhon (φ (u n)) τ hτ)
    (fun n => hb (φ (u n)) τ hτ)
  refine ⟨ψ', hψ'.tendsto_atTop, ?_⟩
  -- the further extraction has the same profile limit as the extraction of step 2
  have hfullAll' : ∀ K' : Set (ℝ × ℝ), IsCompact K' → K' ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => slice (G (φ n)) τ p.1 p.2)
        (fun p => g' p.1 p.2) atTop K' := by
    intro K' hK' hK'Q
    refine EpsConvH.of_uniform_cauchy (hu.comp hψ'.tendsto_atTop) ?_ ?_
    · intro ε hε
      obtain ⟨N, hN⟩ := hcau K' hK' hK'Q ε hε
      exact ⟨N, fun m hm n hn x hx => by rw [Real.dist_eq]; exact hN m hm n hn x hx⟩
    · have h := hg'.1 K' hK' hK'Q 0 0 (by norm_num)
      simpa only [Function.comp_def, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero]
        using h
  have hEqOn : ∀ p ∈ Work.FTS.EllipticEst.Q0, g' p.1 p.2 = g p.1 p.2 := by
    intro p hp
    have hsub : ({p} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro q hq
      rw [Set.mem_singleton_iff] at hq
      rwa [hq]
    exact tendsto_nhds_unique
      ((hfullAll' {p} isCompact_singleton hsub).tendsto_at (Set.mem_singleton p))
      ((hfullAll {p} isCompact_singleton hsub).tendsto_at (Set.mem_singleton p))
  -- on the open quadrant the two limits have the same slots, hence so do they on `K`
  have hslotEq : ∀ p ∈ K,
      Work.Spaces.mixed j i g' p.1 p.2 = Work.Spaces.mixed j i g p.1 p.2 := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
    exact EpsConvTau.mixed_congr_of_quad
      (fun z θ hz hθ0 hθ1 => hEqOn (z, θ) (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩))
      j i p.1 p.2 hz hθ0 hθ1
  exact (hg'.1 K hK hKQ j i hji).congr_right hslotEq

end Work.FTS.StrongEps
