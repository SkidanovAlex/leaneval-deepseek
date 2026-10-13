/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsConvRat.lean` — the diagonal over the fake times

The extraction `Work.FTS.StrongEps.EpsConvSubseq` produces, from *one* sequence of profiles with a
uniform `ℋ⁶`-bound, a subsequence and a limit carrying the full convergence package
`Work.FTS.StrongEps.ConvLocUnifH6`.  The scheme of `E5` however needs this *simultaneously* at every
(time) slice of a sequence of *families* `G n : ℝ → ℝ → ℝ → ℝ` (`Fam`), the hypotheses being
uniform in `τ ∈ [0,T]`.

This module performs the standard diagonal extraction over the *countable* set of rational times:

* `Work.FTS.StrongEps.tendstoUniformlyOn_comp_index` / `..._congr_index` — uniform convergence
  survives reindexing (and eventual reindexing) by a map tending to infinity;
* `Work.FTS.StrongEps.ConvLocUnifH6.comp_index` / `.congr_ae` — the same for the whole
  `ConvLocUnifH6` package;
* `Work.FTS.StrongEps.EpsConvRat` — from a sequence of families with a uniform `ℋ⁶`-bound at every
  `τ ∈ [0,T]`, one strictly increasing `φ` and limits `f τ` at every *rational* `τ ∈ [0,T]`.

The construction: fix a surjection `e : ℕ → ℚ`.  At level `k` apply `EpsConvSubseq` to the family
`n ↦ slice (G (ψ n)) (e k)`; the extraction gives `S k ψ`, and `W` is the iteration
`W 0 = id`, `W (k+1) = W k ∘ S k (W k)`.  The diagonal is `φ n = W n n` (strictly increasing because
`S k ψ ≥ id`).  For the level-`k` convergence, the auxiliary composite `E k n` (the `n`-th iterate
of the steps from `k` on) satisfies `W n = W k ∘ E k n` for `k ≤ n`, and `n ↦ E (k+1) n n → ∞`; the
convergence along `W (k+1)` therefore passes to the diagonal up to finitely many terms — which is
what `ConvLocUnifH6.congr_ae` absorbs.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsConv
import Submission.Work.FTS.StrongEps.EpsConvSubseq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false
open Work.FTS.Galerkin (Fn Fam slice)

/-- Uniform convergence survives reindexing by a map tending to infinity. -/
theorem tendstoUniformlyOn_comp_index {X β : Type*} [UniformSpace β] {F : ℕ → X → β}
    {f : X → β} {s : Set X} (h : TendstoUniformlyOn F f atTop s) {A : ℕ → ℕ}
    (hA : Tendsto A atTop atTop) : TendstoUniformlyOn (F ∘ A) f atTop s :=
  fun u hu => hA.eventually (h u hu)

/-- Uniform convergence survives eventual reindexing. -/
theorem tendstoUniformlyOn_congr_index {X β : Type*} [UniformSpace β] {F : ℕ → X → β}
    {f : X → β} {s : Set X} (h : TendstoUniformlyOn F f atTop s) {A φ : ℕ → ℕ}
    (hA : Tendsto A atTop atTop) (hφ : A =ᶠ[atTop] φ) :
    TendstoUniformlyOn (F ∘ φ) f atTop s :=
  (tendstoUniformlyOn_comp_index h hA).congr
    (hφ.mono (fun n hn => by intro x hx; simp only [Function.comp_apply, hn]))

/-- The convergence package `ConvLocUnifH6` survives reindexing by a map tending to infinity. -/
theorem ConvLocUnifH6.comp_index {α B : ℝ} {G : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f)
    {A : ℕ → ℕ} (hA : Tendsto A atTop atTop) : ConvLocUnifH6 α B (G ∘ A) f :=
  ⟨fun K hK hKQ j i hji => tendstoUniformlyOn_comp_index (h.1 K hK hKQ j i hji) hA, h.2⟩

/-- The convergence package `ConvLocUnifH6` survives an eventual change of the sequence of
profiles. -/
theorem ConvLocUnifH6.congr_ae {α B : ℝ} {G G' : ℕ → Fn} {f : Fn} (h : ConvLocUnifH6 α B G f)
    (hGG : G =ᶠ[atTop] G') : ConvLocUnifH6 α B G' f :=
  ⟨fun K hK hKQ j i hji => (h.1 K hK hKQ j i hji).congr
      (hGG.mono (fun n hn => by intro p hp; simp only [hn])), h.2⟩

/-- **The diagonal extraction over the fake times.**  From a sequence of families `G n` with a
uniform `ℋ⁶`-bound at every `τ ∈ [0,T]` (and `C^∞`-regularity of every slice on the open quadrant)
there is a single strictly increasing `φ` and, at every *rational* `τ ∈ [0,T]`, a limit `f τ`
carrying the convergence package `ConvLocUnifH6` along `φ`. -/
theorem EpsConvRat {α B T : ℝ} (hα : 0 < α) {G : ℕ → Work.FTS.Galerkin.Fam}
    (hsm : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice (G n) τ))
    (hb : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice (G n) τ) ≤ B) :
    ∃ (φ : ℕ → ℕ) (f : ℝ → Work.FTS.Galerkin.Fn), StrictMono φ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T ∩ Set.range (fun q : ℚ => (q : ℝ)),
        Work.FTS.StrongEps.ConvLocUnifH6 α B
          (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ) (f τ) := by
  classical
  -- an enumeration of the rationals
  obtain ⟨e, he⟩ := exists_surjective_nat ℚ
  -- the extraction at level `k`, with its two components bundled
  let hw : ∀ (k : ℕ) (ψ : ℕ → ℕ), ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T →
      ∃ (p : (ℕ → ℕ) × Fn), StrictMono p.1 ∧
        ConvLocUnifH6 α B (fun n => slice (G (ψ (p.1 n))) ((e k : ℚ) : ℝ)) p.2 := by
    intro k ψ h
    obtain ⟨φ0, f0, hφ0, hc0⟩ := EpsConvSubseq (α := α) (B := B) hα
      (G := fun n => slice (G (ψ n)) ((e k : ℚ) : ℝ))
      (fun n l => hsm (ψ n) ((e k : ℚ) : ℝ) h l)
      (fun n => hmem (ψ n) ((e k : ℚ) : ℝ) h)
      (fun n => hb (ψ n) ((e k : ℚ) : ℝ) h)
    exact ⟨(φ0, f0), hφ0, hc0⟩
  let step : ℕ → (ℕ → ℕ) → (ℕ → ℕ) × Fn := fun k ψ =>
    if h : ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T then Classical.choose (hw k ψ h) else (id, 0)
  let S : ℕ → (ℕ → ℕ) → (ℕ → ℕ) := fun k ψ => (step k ψ).1
  let L : ℕ → (ℕ → ℕ) → Fn := fun k ψ => (step k ψ).2
  have hStep : ∀ k ψ (h : ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T),
      StrictMono (S k ψ) ∧
      ConvLocUnifH6 α B (fun n => slice (G (ψ (S k ψ n))) ((e k : ℚ) : ℝ)) (L k ψ) := by
    intro k ψ h
    have heq : step k ψ = Classical.choose (hw k ψ h) := by
      simp only [step]; rw [dite_eq_left h]
    simp only [show S k ψ = (step k ψ).1 from rfl, show L k ψ = (step k ψ).2 from rfl, heq]
    exact Classical.choose_spec (hw k ψ h)
  have hSmono : ∀ k ψ, StrictMono (S k ψ) := by
    intro k ψ
    by_cases h : ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T
    · exact (hStep k ψ h).1
    · have heq : step k ψ = (id, (0 : Fn)) := by simp only [step]; rw [dite_eq_right h]
      rw [show S k ψ = (step k ψ).1 from rfl, heq]
      exact strictMono_id
  -- the composite subsequence at level `k` and the diagonal
  let W : ℕ → (ℕ → ℕ) := Nat.rec id (fun k Wk => Wk ∘ S k Wk)
  have hWsucc : ∀ k, W (k + 1) = W k ∘ S k (W k) := fun k => rfl
  have hWapply : ∀ k n, W (k + 1) n = W k (S k (W k) n) := fun k n => congrFun (hWsucc k) n
  have hWmono : ∀ k, StrictMono (W k) := by
    intro k
    induction k with
    | zero => exact strictMono_id
    | succ k ih => rw [hWsucc k]; exact ih.comp (hSmono k (W k))
  -- the `n`-th iterate of the steps from level `k` on
  let E : ℕ → ℕ → (ℕ → ℕ) := fun k =>
    Nat.rec id (fun n En => if n + 1 ≤ k then id else En ∘ S n (W n))
  have hEsucc : ∀ k n, E k (n + 1) = if n + 1 ≤ k then id else E k n ∘ S n (W n) :=
    fun k n => rfl
  have hEself : ∀ k, E k k = id := by
    intro k
    cases k with
    | zero => rfl
    | succ m => rw [hEsucc (m + 1) m, ite_eq_left (le_refl (m + 1))]
  have hWmult : ∀ k n, k ≤ n → W n = W k ∘ E k n := by
    intro k
    refine Nat.le_induction ?_ ?_
    · rw [hEself k, Function.comp_id]
    · intro n hkn ih
      rw [hWsucc n, hEsucc k n, ite_eq_right (by omega), ← Function.comp_assoc, ih]
  have hEge : ∀ k n m, m ≤ E k n m := by
    intro k n
    induction n with
    | zero => intro m; rw [show E k 0 = id from rfl]; exact le_rfl
    | succ n ih =>
      intro m
      rw [hEsucc]
      by_cases h : n + 1 ≤ k
      · rw [ite_eq_left h]; exact le_rfl
      · rw [ite_eq_right h, Function.comp_apply]
        exact le_trans ((hSmono n (W n)).id_le m) (ih (S n (W n) m))
  have hdiag : ∀ k n, k + 1 ≤ n → W n n = W (k + 1) (E (k + 1) n n) := by
    intro k n hn
    exact congrFun (hWmult (k + 1) n hn) n
  let φ : ℕ → ℕ := fun n => W n n
  have hφmono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ (fun n => ?_)
    show W (n + 1) (n + 1) > W n n
    rw [hWapply n (n + 1)]
    exact (hWmono n).lt_iff_lt.mpr
      (lt_of_lt_of_le (Nat.lt_succ_self n) ((hSmono n (W n)).id_le (n + 1)))
  -- the level-`k` convergence, re-indexed to `W (k+1)`
  have hconvW : ∀ k, ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T →
      ConvLocUnifH6 α B (fun m => slice (G (W (k + 1) m)) ((e k : ℚ) : ℝ)) (L k (W k)) := by
    intro k hk
    have h := (hStep k (W k) hk).2
    refine ⟨fun K hK hKQ j i hji => ?_, h.2.1, h.2.2⟩
    exact (h.1 K hK hKQ j i hji).congr (Filter.Eventually.of_forall (fun n => by
      intro p hp
      show Work.Spaces.mixed j i (slice (G (W k (S k (W k) n))) ((e k : ℚ) : ℝ)) p.1 p.2
        = Work.Spaces.mixed j i (slice (G (W (k + 1) n)) ((e k : ℚ) : ℝ)) p.1 p.2
      rw [hWapply k n]))
  -- the diagonal step: the tail of `φ` is a subsequence of the level-`k` extraction
  have hfinal : ∀ k, ((e k : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T →
      ConvLocUnifH6 α B (fun n => slice (G (W n n)) ((e k : ℚ) : ℝ)) (L k (W k)) := by
    intro k hk
    have hlevel := hconvW k hk
    have hA : Tendsto (fun n => E (k + 1) n n) atTop atTop :=
      tendsto_atTop_mono (fun n => hEge (k + 1) n n) tendsto_id
    have hcomp := hlevel.comp_index hA
    refine hcomp.congr_ae ?_
    filter_upwards [Filter.eventually_ge_atTop (k + 1)] with n hn
    simp only [Function.comp_apply]
    show slice (G (W (k + 1) (E (k + 1) n n))) ((e k : ℚ) : ℝ)
      = slice (G (W n n)) ((e k : ℚ) : ℝ)
    rw [hdiag k n hn]
  -- the limit at a real time: pick the rational `τ` and its index in the enumeration
  let kIdx : ℝ → ℕ := fun τ =>
    if h : ∃ k : ℕ, ((e k : ℚ) : ℝ) = τ then Classical.choose h else 0
  have hkIdx : ∀ τ, τ ∈ Set.range (fun q : ℚ => (q : ℝ)) → ((e (kIdx τ) : ℚ) : ℝ) = τ := by
    intro τ hτ
    obtain ⟨q, hq⟩ := hτ
    have hex : ∃ k : ℕ, ((e k : ℚ) : ℝ) = τ :=
      ⟨Classical.choose (he q), by rw [Classical.choose_spec (he q)]; exact hq⟩
    simp only [kIdx]
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  refine ⟨φ, fun τ => L (kIdx τ) (W (kIdx τ)), hφmono, ?_⟩
  intro τ hτ
  obtain ⟨hτI, hτQ⟩ := hτ
  have hk := hkIdx τ hτQ
  have hk' : ((e (kIdx τ) : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) T := by rw [hk]; exact hτI
  have hres := hfinal (kIdx τ) hk'
  convert hres using 2
  rw [hk]

end Work.FTS.StrongEps
