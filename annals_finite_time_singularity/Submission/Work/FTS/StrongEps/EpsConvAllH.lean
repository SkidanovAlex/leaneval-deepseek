/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongEps.EpsConvAllH` — the convergence package at *every* time

`Submission/Work/FTS/StrongEps/EpsConvAll.lean` proves the same statement from the two
hypotheses `hconv` (the package at the *rational* times) and `hequi` (a `τ`-Lipschitz modulus for
the slots of order `≤ 4`) **alone** — and that statement is false: the `HkNorm α 6 (F τ) ≤ B`
clause of `hconv` is a *junk-integral* clause (`HkSq` is a Bochner integral, which is `0`
whenever its integrand is not integrable), so it holds vacuously for profiles of infinite honest
`ℋ⁶`-size, while the limit at an irrational time is pinned by the slot clause alone.  See
`EpsConvAllRefute.lean` / `NOTES_EpsConvAll_FALSE.md` for the machine-checked refutation.

The present lemma adds the *honesty* hypotheses that make the statement true:

* `hsm` — every slice is `C^∞` on the open quadrant,
* `hhon` — every slice lies in the honest weighted space `ℋ⁶` (`HkMem α 6`),
* `hb` — a uniform `ℋ⁶`-bound `HkNorm α 6 (slice (G n) τ) ≤ B` for *all* `n` and `τ ∈ [0,T]`.

Under those, the extraction `EpsConvSubseq` applies at the *given* time `τ`, producing a
subsequence `ψ` of `φ` and a limit `g` with the whole package along `φ ∘ ψ`.  It remains to
recover the convergence of the *full* sequence `n ↦ slice (G (φ n)) τ`, which is where `hconv`
and `hequi` are used (and only there):

* by `hequi`, the slot families at `τ` and at a nearby rational `σ` are uniformly (in `n` and in
  the point) within `C |τ - σ|` of each other, and by `hconv` the family at `σ` converges; hence
  the family at `τ` is *uniformly Cauchy* on every compact subset of the quadrant
  (`uniform_cauchy_of_dense_lipschitz` + density of `ℚ`);
* a uniformly Cauchy sequence that has a convergent subsequence converges to the same limit
  (`of_uniform_cauchy`), so the slots of the full sequence converge to the slots of `g`.

The two `C⁴`- and `ℋ⁶`-clauses of the conclusion are then inherited from the extraction.

The helper lemmas are kept in the namespace `Work.FTS.StrongEps.EpsConvH` and are general
(`ℝ`-valued functions on a type, indexed by `ℕ`, with a real parameter).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsConvSubseq
import Submission.Work.FTS.StrongEps.EpsConvRat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsConvH

set_option autoImplicit false

/-- **A uniformly Cauchy sequence that has a convergent subsequence converges** (to the same
limit).  The index map `A` is the subsequence; it only has to tend to infinity. -/
theorem of_uniform_cauchy {X β : Type*} [PseudoMetricSpace β]
    {s : Set X} {F : ℕ → X → β} {f : X → β} {A : ℕ → ℕ}
    (hA : Tendsto A atTop atTop)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ s, dist (F m x) (F n x) < ε)
    (hs : TendstoUniformlyOn (F ∘ A) f atTop s) :
    TendstoUniformlyOn F f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hs ⊢
  intro ε hε
  have hε2 : (0:ℝ) < ε/2 := by linarith
  obtain ⟨N, hN⟩ := hc (ε/2) hε2
  have h1 : ∀ᶠ n in atTop, ∀ x ∈ s, dist (f x) (F (A n) x) < ε/2 := hs (ε/2) hε2
  filter_upwards [h1, eventually_ge_atTop N, hA.eventually (eventually_ge_atTop N)]
    with n hn hnN hAn
  intro x hx
  calc dist (f x) (F n x)
      ≤ dist (f x) (F (A n) x) + dist (F (A n) x) (F n x) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add (hn x hx) (hN (A n) hAn n hnN x hx)
    _ = ε := by ring

/-- **Uniform Cauchy from convergence on a dense set of parameters.**  Let `u σ n p` be a family
of `ℝ`-valued sequences indexed by `n`, depending on a real parameter `σ`.  If

* `u · n p` is `C`-Lipschitz in `σ`, uniformly in `n` and `p ∈ s`,
* `u σ · p` converges for every `σ` in `Icc 0 T ∩ D`, `D` dense in `Icc 0 T` in the sense of
  `hdense`,

then `u τ · p` is uniformly (in `p ∈ s`) Cauchy for every `τ ∈ Icc 0 T`. -/
theorem uniform_cauchy_of_dense_lipschitz {X : Type*} {s : Set X} {T : ℝ} {D : Set ℝ}
    {u : ℝ → ℕ → X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdense : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ δ : ℝ, 0 < δ →
      ∃ σ ∈ Set.Icc (0 : ℝ) T ∩ D, |σ - τ| ≤ δ)
    (hlip : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ σ' ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ, ∀ p ∈ s,
      |u σ n p - u σ' n p| ≤ C * |σ - σ'|)
    (hconv : ∀ σ ∈ Set.Icc (0 : ℝ) T ∩ D, ∃ L : X → ℝ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ p ∈ s, |u σ n p - L p| < ε) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ p ∈ s,
      |u τ m p - u τ n p| < ε := by
  intro τ hτ ε hε
  have hC1 : (0:ℝ) < C + 1 := by linarith
  have hδpos : (0:ℝ) < ε / (8 * (C + 1)) := by positivity
  obtain ⟨σ, hσ, hστ⟩ := hdense τ hτ (ε / (8 * (C + 1))) hδpos
  obtain ⟨L, hL⟩ := hconv σ hσ
  have hε4 : (0:ℝ) < ε/4 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hL (ε/4) hε4)
  have key : C * (ε / (8 * (C + 1))) ≤ ε / 8 := by
    have h3 : C / (C + 1) ≤ 1 := by rw [div_le_one hC1]; linarith
    calc C * (ε / (8 * (C + 1))) = (C / (C + 1)) * (ε / 8) := by field_simp
      _ ≤ 1 * (ε / 8) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ε / 8 := by ring
  refine ⟨N, fun m hm n hn p hp => ?_⟩
  have hm' : |u σ m p - L p| < ε/4 := hN m hm p hp
  have hn' : |u σ n p - L p| < ε/4 := hN n hn p hp
  have hmτ : |u τ m p - u σ m p| ≤ ε/8 := by
    have h := hlip τ hτ σ hσ.1 m p hp
    refine le_trans h (le_trans (mul_le_mul_of_nonneg_left ?_ hC) key)
    rw [abs_sub_comm]; exact hστ
  have hnτ : |u σ n p - u τ n p| ≤ ε/8 := by
    have h := hlip σ hσ.1 τ hτ n p hp
    refine le_trans h (le_trans (mul_le_mul_of_nonneg_left ?_ hC) key)
    exact hστ
  have hmid : |u σ m p - u σ n p| < ε/2 := by
    have h1 : u σ m p - u σ n p = (u σ m p - L p) - (u σ n p - L p) := by ring
    rw [h1]
    have htri : |(u σ m p - L p) - (u σ n p - L p)|
        ≤ |u σ m p - L p| + |u σ n p - L p| :=
      abs_sub_le_iff.mpr
        ⟨by linarith [le_abs_self (u σ m p - L p), neg_le_abs (u σ n p - L p)],
         by linarith [le_abs_self (u σ n p - L p), neg_le_abs (u σ m p - L p)]⟩
    linarith
  have htri2 : |u τ m p - u σ m p + (u σ m p - u σ n p) + (u σ n p - u τ n p)|
      ≤ |u τ m p - u σ m p| + |u σ m p - u σ n p| + |u σ n p - u τ n p| :=
    abs_add_three _ _ _
  calc |u τ m p - u τ n p|
      = |(u τ m p - u σ m p) + (u σ m p - u σ n p) + (u σ n p - u τ n p)| := by ring_nf
    _ ≤ |u τ m p - u σ m p| + |u σ m p - u σ n p| + |u σ n p - u τ n p| := htri2
    _ < ε := by linarith

/-- The rationals are dense in `Icc 0 T`: every `τ ∈ Icc 0 T` is within `δ` of a *rational*
point of `Icc 0 T`. -/
theorem exists_rat_mem_Icc_close {T τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ ∈ Set.Icc (0:ℝ) T ∩ Set.range (fun q : ℚ => (q:ℝ)), |σ - τ| ≤ δ := by
  rcases lt_or_eq_of_le (le_trans hτ.1 hτ.2) with hT | hT
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (x := max 0 (τ - δ)) (y := min T (τ + δ))
      (max_lt (lt_min hT (by linarith [hτ.1])) (lt_min (by linarith [hτ.2]) (by linarith)))
    refine ⟨(q:ℝ), ⟨?_, ⟨q, rfl⟩⟩, ?_⟩
    · rw [Set.mem_Icc]
      exact ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hq1),
             le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _))⟩
    · rw [abs_le]
      exact ⟨by linarith [lt_of_le_of_lt (le_max_right _ _) hq1],
             by linarith [lt_of_lt_of_le hq2 (min_le_right _ _)]⟩
  · have hτ0 : τ = 0 := le_antisymm (le_trans hτ.2 (le_of_eq hT.symm)) hτ.1
    refine ⟨0, ⟨?_, ⟨0, by norm_num⟩⟩, ?_⟩
    · rw [Set.mem_Icc]; exact ⟨le_rfl, le_of_eq hT⟩
    · rw [hτ0, sub_zero, abs_zero]; exact le_of_lt hδ

end Work.FTS.StrongEps.EpsConvH

namespace Work.FTS.StrongEps

open Work.FTS.StrongEps.EpsConvH

-- the statement carries the hypothesis `hφ`, which the proof does not need
set_option linter.unusedVariables false in
theorem EpsConvAllH {α B T : ℝ} (hα : 0 < α) {G : ℕ → Work.FTS.Galerkin.Fam}
    {F : ℝ → Work.FTS.Galerkin.Fn} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hsm : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hhon : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice (G n) τ))
    (hb : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice (G n) τ) ≤ B)
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T ∩ Set.range (fun q : ℚ => (q : ℝ)),
      Work.FTS.StrongEps.ConvLocUnifH6 α B
        (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ) (F τ))
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ) p.1 p.2
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ') p.1 p.2|
            ≤ C * |τ - τ'|) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∃ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.ConvLocUnifH6 α B
        (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ) f := by
  intro τ hτ
  -- the extraction at the given time `τ` (this is where the honesty hypotheses are consumed)
  obtain ⟨ψ, g, hψ, hg⟩ := Work.FTS.StrongEps.EpsConvSubseq (α := α) (B := B) hα
    (G := fun n => Work.FTS.Galerkin.slice (G (φ n)) τ)
    (fun n k => hsm (φ n) τ hτ k)
    (fun n => hhon (φ n) τ hτ)
    (fun n => hb (φ n) τ hτ)
  refine ⟨g, ?_, hg.2.1, hg.2.2⟩
  -- the slot convergence of the *full* sequence at `τ`
  intro K hK hKQ j i hji
  obtain ⟨C, hC, hCe⟩ := hequi K hK hKQ
  have hsub := hg.1 K hK hKQ j i hji
  have hdense : ∀ τ' ∈ Set.Icc (0:ℝ) T, ∀ δ : ℝ, 0 < δ →
      ∃ σ ∈ Set.Icc (0:ℝ) T ∩ Set.range (fun q : ℚ => (q:ℝ)), |σ - τ'| ≤ δ :=
    fun τ' hτ' δ hδ => exists_rat_mem_Icc_close hτ' hδ
  have hlip : ∀ σ ∈ Set.Icc (0:ℝ) T, ∀ σ' ∈ Set.Icc (0:ℝ) T, ∀ n : ℕ, ∀ p ∈ K,
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G (φ n)) σ) p.1 p.2
        - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G (φ n)) σ') p.1 p.2|
        ≤ C * |σ - σ'| :=
    fun σ hσ σ' hσ' n p hp => hCe (φ n) j i hji p hp σ hσ σ' hσ'
  have hconvK : ∀ σ ∈ Set.Icc (0:ℝ) T ∩ Set.range (fun q : ℚ => (q:ℝ)), ∃ L : ℝ × ℝ → ℝ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ p ∈ K,
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G (φ n)) σ) p.1 p.2 - L p| < ε := by
    intro σ hσ
    refine ⟨fun p => Work.Spaces.mixed j i (F σ) p.1 p.2, fun ε hε => ?_⟩
    have h := (Metric.tendstoUniformlyOn_iff.mp ((hconv σ hσ).1 K hK hKQ j i hji)) ε hε
    filter_upwards [h] with n hn p hp
    have hn' := hn p hp
    rw [Real.dist_eq, abs_sub_comm] at hn'
    exact hn'
  have hcau := uniform_cauchy_of_dense_lipschitz (X := ℝ × ℝ) (s := K) (T := T)
    (D := Set.range (fun q : ℚ => (q:ℝ))) (u := fun σ n p =>
      Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G (φ n)) σ) p.1 p.2)
    (C := C) hC hdense hlip hconvK τ hτ
  refine of_uniform_cauchy hψ.tendsto_atTop ?_ hsub
  intro ε hε
  obtain ⟨N, hN⟩ := hcau ε hε
  exact ⟨N, fun m hm n hn x hx => by rw [Real.dist_eq]; exact hN m hm n hn x hx⟩

end Work.FTS.StrongEps
