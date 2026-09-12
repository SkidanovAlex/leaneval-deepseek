/-
Centered compress-side bound (`compress` machinery for the shift `s = −p`,
i.e. the matrix `B ω − p·11ᵀ` with zero-mean entries), completing the
compress side of Theorem A for EVERY `s ∈ [−1,0]`:

  * `centered_reduce`          — deterministic: on the centered spectral event
    `∀x, actSq A x ≤ L²·n·sqNorm x`, a `(γ/2)·√n` small ball of `x` propagates
    to scale `γ·√n` at any `y` with `‖y−x‖₂ ≤ γ/(8L)` (no slice window needed,
    because the matrix is already centered: `‖A(y−x)‖ ≤ L√n·‖y−x‖`);
  * `compress_centered_main_bound` — the full per-point/net assembly for the
    centered `(n−1)×n` family (net availability passed as hypothesis);
  * `compress_theorem_centered`    — the paper-form theorem (instantiates the
    net from the Commons `compressible_net` result).
-/
import Mathlib
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Bernoulli
import Submission.CompressProp
import Submission.GeoBridge
import Submission.Commons.LinearAlgebra.Net.compress_slice_net
import Submission.Commons.LinearAlgebra.Net.compressible_net
import Submission.Commons.Probability.RandomMatrix.rect_spectral_measurable
import Submission.Commons.Probability.Compress.layer0_choose
import ChallengeDeps

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Submission.CompressCentered

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

noncomputable section

universe u

open Submission.Compress
open Submission.CompressProp
open Submission.GeoBridge

/-! ## 1. Deterministic centered event-reduction -/

/-- On the centered spectral event `∀v, actSq A v ≤ L²·n·sqNorm v`, a
`(γ/2)²·n`-small ball of `x` propagates to a `γ²·n`-small ball of `y` at
squared distance `sqNorm (y−x) ≤ (γ/(8L))²`.  (Window-free analogue of
`Submission.Compress.event_reduction` for the centered matrix `A`.) -/
lemma centered_reduce {n : ℕ} (A : Fin (n - 1) → Fin n → ℝ) (L γ : ℝ)
    (hL : 0 < L) (hγ : 0 < γ)
    (hE : ∀ v : Fin n → ℝ, actSq A v ≤ L ^ 2 * (n : ℝ) * sqNorm v)
    {x y : Fin n → ℝ}
    (hball : actSq A x ≤ (γ / 2) ^ 2 * (n : ℝ))
    (hd : sqNorm (y - x) ≤ (γ / (8 * L))^2) :
    actSq A y ≤ γ ^ 2 * (n : ℝ) := by
  have hnn : 0 ≤ (n : ℝ) := by positivity
  have hhalf : ((γ / 2) * Real.sqrt (n : ℝ)) ^ 2 = (γ / 2) ^ 2 * (n : ℝ) := by
    rw [mul_pow]
    congr 1
    rw [Real.sq_sqrt hnn]
  have hx' : sqrtAct A x ≤ (γ / 2) * Real.sqrt (n : ℝ) := by
    refine sqrtAct_le_of_actSq_le_sq A (by positivity : 0 ≤ (γ / 2) * Real.sqrt (n : ℝ)) x ?_
    rw [hhalf]
    exact hball
  have htri := sqrtAct_triangle A x (y - x)
  have hy : x + (y - x) = y := by
    funext i
    simp
  rw [hy] at htri
  have hyx' : sqrtAct A (y - x) ≤ γ * Real.sqrt (n : ℝ) / 8 := by
    calc
      sqrtAct A (y - x) ≤ L * Real.sqrt (n : ℝ) * Real.sqrt (sqNorm (y - x)) := by
        exact sqrtAct_le_of_spectral A L (le_of_lt hL) hE (y - x)
      _ ≤ L * Real.sqrt (n : ℝ) * (γ / (8 * L)) := by
        exact mul_le_mul_of_nonneg_left (sqrt_sqNorm_le_of_sq_le hL hγ hd)
          (mul_nonneg (le_of_lt hL) (Real.sqrt_nonneg _))
      _ = γ * Real.sqrt (n : ℝ) / 8 := by
        field_simp [hL.ne']
  have hsum : sqrtAct A y ≤ (γ / 2) * Real.sqrt (n : ℝ) + γ * Real.sqrt (n : ℝ) / 8 := by
    exact le_trans htri (add_le_add hx' hyx')
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hle : (γ / 2) * Real.sqrt (n : ℝ) + γ * Real.sqrt (n : ℝ) / 8 ≤ γ * Real.sqrt (n : ℝ) := by
    calc
      (γ / 2) * Real.sqrt (n : ℝ) + γ * Real.sqrt (n : ℝ) / 8
          = (γ / 2 + γ / 8) * Real.sqrt (n : ℝ) := by ring
      _ ≤ γ * Real.sqrt (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by linarith : γ / 2 + γ / 8 ≤ γ) hs0
  have hf : sqrtAct A y ≤ γ * Real.sqrt (n : ℝ) := le_trans hsum hle
  exact actSq_le_sq_nat_of_sqrtAct_le A (le_of_lt hγ) y hf

/-! ## 2. Main centered assembly bound -/

/-- Centered analogue of `Submission.CompressProp.compress_main_bound`: with a
single net over the whole `(ε̃, γ/(32L))`-compressible set (hypothesis `hnet`),
the probability that a compressible vector has centered small ball `(γ/2)·√n`
is at most `2^{-n} + Bnet·auxb`.  No slice windows are needed because the
matrix `B·ω − p` is centered. -/
theorem compress_centered_main_bound {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {n : ℕ} (hn₂ : 2 ≤ n)
    (L γ : ℝ) (hL₁ : 1 ≤ L) (hγ : 0 < γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (B : Fin (n - 1) → Fin n → Ω → ℝ)
    (hBmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (B k j))
    (hBind : ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => B kj.1 kj.2) P)
    (hBlaw : ∀ k : Fin (n - 1), ∀ j : Fin n, HasLaw (B k j) (bernoulliMeasure 1 0 p) P)
    (Sspec : Set Ω) (hSpecM : MeasurableSet Sspec)
    (hSpecP : P.real Sspec ≥ 1 - (1 / 2 : ℝ) ^ n)
    (hSpecOn : ∀ ⦃ω : Ω⦄, ω ∈ Sspec → ∀ x : Fin n → ℝ,
        actSq (fun k j => B k j ω - (p : ℝ)) x ≤ L ^ 2 * (n : ℝ) * sqNorm x)
    (Bnet : ℝ) (hBnet0 : 0 ≤ Bnet)
    (hnet : ∃ Net : Finset (Fin n → ℝ),
        (∀ x : Fin n → ℝ,
            Commons.LinearAlgebra.Net.compressible eps (γ / (32 * L)) x →
            ∃ y ∈ Net, Commons.LinearAlgebra.Net.compressible eps (γ / (32 * L)) y ∧
              Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ (γ / (8 * L)) ^ 2) ∧
        ((Net.card : ℝ) ≤ Bnet))
    (hauxb : ℝ) (hauxb0 : 0 ≤ hauxb)
    (hpt : ∀ y : Fin n → ℝ, (∑ j : Fin n, (y j) ^ 2) = 1 →
        P.real {ω : Ω | actSq (fun k j => B k j ω - (p : ℝ)) y ≤ γ ^ 2 * (n : ℝ)} ≤ hauxb) :
    P.real {ω : Ω | ∃ x : Fin n → ℝ,
        Commons.LinearAlgebra.Net.compressible eps (γ / (32 * L)) x ∧
        actSq (fun k j => B k j ω - (p : ℝ)) x ≤ (γ / 2) ^ 2 * (n : ℝ)}
      ≤ (1 / 2 : ℝ) ^ n + Bnet * hauxb := by
  classical
  let δ : ℝ := eps
  let ν : ℝ := γ / (32 * L)
  let Cω : Ω → Fin (n - 1) → Fin n → ℝ := fun ω k j => B k j ω - (p : ℝ)
  let S : Set Ω := {ω : Ω | ∀ x : Fin n → ℝ, actSq (Cω ω) x ≤ L ^ 2 * (n : ℝ) * sqNorm x}
  let T : Set Ω := {ω : Ω | ∃ x : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible δ ν x ∧
      actSq (Cω ω) x ≤ (γ / 2) ^ 2 * (n : ℝ)}
  let E : (Fin n → ℝ) → Set Ω := fun y => {ω : Ω | actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)}
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL₁
  -- Sspec ⊆ S
  have hSSpec : Sspec ⊆ S := by
    intro ω hω x
    have hh := hSpecOn (ω := ω) hω x
    change actSq (fun k j => B k j ω - (p : ℝ)) x ≤ L ^ 2 * (n : ℝ) * sqNorm x
    exact hh
  -- complement bound
  have hSpecComp : P.real Sᶜ ≤ (1 / 2 : ℝ) ^ n := by
    have hSspecC : Sᶜ ⊆ Sspecᶜ := by
      intro ω hω
      exact fun hωs => hω (hSSpec hωs)
    calc
      P.real Sᶜ ≤ P.real Sspecᶜ := by
        exact MeasureTheory.measureReal_mono (s₁ := Sᶜ) (s₂ := Sspecᶜ) hSspecC
          (measure_ne_top P Sspecᶜ)
      _ = 1 - P.real Sspec := measureReal_compl_eq P hSpecM
      _ ≤ (1 / 2 : ℝ) ^ n := by linarith [hSpecP]
  rcases hnet with ⟨Net, hcover, hcard⟩
  let G : Finset (Fin n → ℝ) := Net.filter (fun y => Commons.LinearAlgebra.Net.compressible δ ν y)
  -- T ∩ S ⊆ ⋃_{y ∈ G} E y
  have hB : T ∩ S ⊆ {ω : Ω | ∃ y : Fin n → ℝ, y ∈ G ∧ actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)} := by
    intro ω hω
    rcases hω with ⟨hTω, hSω⟩
    rcases hTω with ⟨x, hxc, hxball⟩
    rcases hcover x hxc with ⟨y, hyNet, hyc, hyx⟩
    have hd : sqNorm (y - x) ≤ (γ / (8 * L)) ^ 2 := by
      change Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ (γ / (8 * L)) ^ 2
      simpa [sqNorm, Commons.LinearAlgebra.Net.sqNorm] using hyx
    have hyE : actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ) := by
      exact centered_reduce (A := Cω ω) (L := L) (γ := γ) hL0 hγ hSω hxball hd
    exact ⟨y, Finset.mem_filter.mpr ⟨hyNet, hyc⟩, hyE⟩
  have hseteq : {ω : Ω | ∃ y : Fin n → ℝ, y ∈ G ∧ actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)}
      = (⋃ y ∈ (G : Finset (Fin n → ℝ)), {ω : Ω | actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)}) := by
    ext ω
    constructor
    · rintro ⟨y, hyG, hyE⟩
      exact Set.mem_iUnion₂.mpr ⟨y, hyG, hyE⟩
    · intro h
      rcases Set.mem_iUnion₂.mp h with ⟨y, hyG, hyE⟩
      exact ⟨y, hyG, hyE⟩
  have hpartA : P.real (T ∩ S) ≤ P.real {ω : Ω | ∃ y : Fin n → ℝ, y ∈ G ∧ actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)} := by
    exact MeasureTheory.measureReal_mono (s₁ := T ∩ S)
      (s₂ := {ω : Ω | ∃ y : Fin n → ℝ, y ∈ G ∧ actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)}) hB
      (measure_ne_top P {ω : Ω | ∃ y : Fin n → ℝ, y ∈ G ∧ actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)})
  have hpartB : P.real {ω : Ω | ∃ y : Fin n → ℝ, y ∈ G ∧ actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)}
      ≤ ∑ y ∈ G, P.real {ω : Ω | actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)} := by
    rw [hseteq]
    exact MeasureTheory.measureReal_biUnion_finset_le (G)
      (fun y => {ω : Ω | actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)})
  have hpartC : (∑ y ∈ G, P.real {ω : Ω | actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)})
      ≤ (G.card) • hauxb := by
    apply Finset.sum_le_card_nsmul (G)
      (fun y => P.real {ω : Ω | actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)}) hauxb
    intro y hyG
    have hyc : Commons.LinearAlgebra.Net.compressible δ ν y := (Finset.mem_filter.mp hyG).2
    have hyunit : (∑ j : Fin n, (y j) ^ 2) = 1 := by
      have hc1 : Commons.LinearAlgebra.Net.sqNorm y = 1 := hyc.1
      simpa [Commons.LinearAlgebra.Net.sqNorm] using hc1
    have hsub : {ω : Ω | actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)}
        = {ω : Ω | actSq (fun k j => B k j ω - (p : ℝ)) y ≤ γ ^ 2 * (n : ℝ)} := by
      dsimp [Cω]
    rw [hsub]
    exact hpt y hyunit
  have hcardG : ((G.card : ℝ) ≤ Bnet) := by
    have h1 : G.card ≤ Net.card := Finset.card_filter_le _ _
    calc
      (G.card : ℝ) ≤ (Net.card : ℝ) := by exact_mod_cast h1
      _ ≤ Bnet := hcard
  have hpartD : (G.card) • hauxb ≤ Bnet * hauxb := by
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcardG hauxb0
  have hper : P.real (T ∩ S) ≤ Bnet * hauxb := by
    calc
      P.real (T ∩ S) ≤ P.real {ω : Ω | ∃ y : Fin n → ℝ, y ∈ G ∧ actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)} := hpartA
      _ ≤ ∑ y ∈ G, P.real {ω : Ω | actSq (Cω ω) y ≤ γ ^ 2 * (n : ℝ)} := hpartB
      _ ≤ (G.card) • hauxb := hpartC
      _ ≤ Bnet * hauxb := hpartD
  -- T ⊆ (T ∩ S) ∪ Sᶜ
  have hTsub : T ⊆ (T ∩ S) ∪ Sᶜ := by
    intro ω hω
    by_cases hSω : ω ∈ S
    · exact Or.inl ⟨hω, hSω⟩
    · exact Or.inr hSω
  have hmeasure : P.real T ≤ P.real (T ∩ S) + P.real Sᶜ := by
    calc
      P.real T ≤ P.real ((T ∩ S) ∪ Sᶜ) := by
        exact MeasureTheory.measureReal_mono (s₁ := T) (s₂ := (T ∩ S) ∪ Sᶜ) hTsub
          (measure_ne_top P ((T ∩ S) ∪ Sᶜ))
      _ ≤ P.real (T ∩ S) + P.real Sᶜ := by
        exact MeasureTheory.measureReal_union_le (T ∩ S) Sᶜ
  have hfinal : P.real T ≤ (1 / 2 : ℝ) ^ n + Bnet * hauxb := by
    nlinarith [hmeasure, hper, hSpecComp]
  have hTdef : T = {ω : Ω | ∃ x : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible eps (γ / (32 * L)) x ∧
      actSq (fun k j => B k j ω - (p : ℝ)) x ≤ (γ / 2) ^ 2 * (n : ℝ)} := by
    dsimp [T, Cω, δ, ν]
  rw [← hTdef]
  exact hfinal


/-! ## 3. Paper-form theorem (net provided by the caller) -/

/-- Proposition `l:compress` for the CENTERED matrix `B·ω − p·11ᵀ` (the shift
`s = −p`, so that `s + p = 0`): with the compressible net supplied by
`hNet` (in practice `Commons.LinearAlgebra.Net.compressible_net`),

    P{ ∃x compressible(δ,ν), actSq (B·ω − p) x ≤ γ₀²·n } ≤ (1−p+ε)ⁿ . -/
theorem compress_theorem_centered_of_net {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε)
    (hNet : ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ {δ ν R : ℝ}, 0 < δ → δ ≤ 1 → 0 < ν → ν ≤ R / 4 → 0 < R → R ≤ 1 →
        ∃ Net : Finset (Fin n → ℝ),
          (∀ x : Fin n → ℝ, Commons.LinearAlgebra.Net.compressible δ ν x →
              ∃ y ∈ Net, Commons.LinearAlgebra.Net.compressible δ ν y ∧
                Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ R^2) ∧
          (Net.card : ℝ) ≤ (n.choose ⌊δ * (n : ℝ)⌋₊ : ℝ) * (C₁ / R) ^ ⌊δ * (n : ℝ)⌋₊) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Fin (n - 1) → Fin n → Ω → ℝ)
        (hBmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (B k j))
        (hBind : ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => B kj.1 kj.2) P)
        (hBlaw : ∀ k : Fin (n - 1), ∀ j : Fin n, HasLaw (B k j) (bernoulliMeasure 1 0 p) P)
        (hBpt : ∀ k : Fin (n - 1), ∀ j : Fin n, ∀ ω : Ω, |B k j ω - (p : ℝ)| ≤ 1),
          P.real {ω : Ω | ∃ x : Fin n → ℝ,
            Commons.LinearAlgebra.Net.compressible δ ν x ∧
            actSq (fun k j => B k j ω - (p : ℝ)) x ≤ γ₀ ^ 2 * (n : ℝ)} ≤ (1 - (p : ℝ) + ε) ^ n := by
  classical
  rcases Commons.Probability.RandomMatrix.rect_spectral_measurable (L := 1) (K := 1)
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) with ⟨Csp, hCsp1, hRect⟩
  rcases Submission.AuxOfLKR.aux_single_vector hp₀ hp₁ with ⟨γa, hγa, hAux⟩
  rcases hNet with ⟨C₁, hC₁₁, hNetAvail⟩
  let L : ℝ := max Csp (γa / 8)
  have hLgeC : Csp ≤ L := by dsimp [L]; exact le_max_left _ _
  have hLgeg : γa / 8 ≤ L := by dsimp [L]; exact le_max_right _ _
  have hL1 : 1 ≤ L := le_trans hCsp1 hLgeC
  rcases Commons.Probability.Compress.layer0_choose hp₀ hp₁ hε₀ hγa hL1 hC₁₁
    (by norm_num : (1 : ℝ) ≤ 1) with ⟨ee, n₀, hee0, hee1, hn₀2, hL0⟩
  let γ : ℝ := γa * Real.sqrt ee
  have hγ0 : 0 < γ := mul_pos hγa (Real.sqrt_pos.2 hee0)
  let γ₀ : ℝ := γ / 2
  have hγ₀0 : 0 < γ₀ := by dsimp [γ₀]; positivity
  refine ⟨n₀, hn₀2, γ₀, hγ₀0, ee, hee0, hee1, γ / (32 * L), ?_, ?_⟩
  · -- 0 < ν
    dsimp [γ]
    positivity
  · -- ν < 1 ∧ main body
    constructor
    · -- ν < 1
      have hγle : γ ≤ γa := by
        dsimp [γ]
        have hs : Real.sqrt ee ≤ 1 := by
          have h1sq : Real.sqrt ee ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (le_of_lt hee1)
          simpa using h1sq
        nlinarith
      have hle : γ / (32 * L) ≤ 1 / 4 := by
        have hLpos : 0 < L := by linarith
        have hnum : γ ≤ 8 * L := by
          calc
            γ ≤ γa := hγle
            _ = 8 * (γa / 8) := by ring
            _ ≤ 8 * L := mul_le_mul_of_nonneg_left hLgeg (by norm_num)
        have hstep : γ / (32 * L) ≤ (8 * L) / (32 * L) := by
          exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 32 * L)
        have hsim : (8 * L) / (32 * L) = 1 / 4 := by
          have hLne : L ≠ 0 := ne_of_gt (by linarith : 0 < L)
          field_simp [hLne]
          ring
        rwa [hsim] at hstep
      nlinarith
    · -- main body: ∀ n ≥ n₀
      intro n hn Ω mΩ P hP B hBmeas hBind hBlaw hBpt
      have hn2n : 2 ≤ n := le_trans hn₀2 hn
      have hn1 : 1 ≤ n := by omega
      let Aω : Ω → Fin (n - 1) → Fin n → ℝ := fun ω k j => B k j ω - (p : ℝ)
      have hAmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (fun ω => Aω ω k j) := by
        intro k j
        dsimp [Aω]
        exact (hBmeas k j).sub measurable_const
      have hAind : ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => (Aω · kj.1 kj.2)) P := by
        have hg : ∀ i : Fin (n - 1) × Fin n, Measurable (fun t : ℝ => t - (p : ℝ)) := fun i =>
          measurable_id.sub measurable_const
        have hc := ProbabilityTheory.iIndepFun.comp hBind
          (fun _ : Fin (n - 1) × Fin n => fun t : ℝ => t - (p : ℝ)) hg
        convert hc using 1
        funext i ω
        dsimp [Aω]
      have hAb : ∀ (k : Fin (n - 1)) (j : Fin n) (ω : Ω), |Aω ω k j| ≤ 1 := by
        intro k j ω
        dsimp [Aω]
        exact hBpt k j ω
      have hAm : ∀ k : Fin (n - 1), ∀ j : Fin n, ∫ ω, Aω ω k j ∂P = 0 := by
        intro k j
        dsimp [Aω]
        exact centered_integral_zero P (hBlaw k j)
      rcases hRect n hn1 (Ω := Ω) P Aω hAmeas hAind hAb hAm with ⟨G, hGm, hGP, hGsub⟩
      have hGP2 : P.real G ≥ 1 - (1 / 2 : ℝ) ^ n := by
        have he := exp_neg_nat_le_two_pow_neg n
        have hle : Real.exp (-1 * (n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
          simpa using he
        linarith
      have hGon : ∀ ⦃ω : Ω⦄, ω ∈ G → ∀ x : Fin n → ℝ,
          actSq (fun k j => B k j ω - (p : ℝ)) x ≤ L ^ 2 * (n : ℝ) * sqNorm x := by
        intro ω hω x
        have hh := hGsub hω x
        change actSq (Aω ω) x ≤ L ^ 2 * (n : ℝ) * sqNorm x
        have hA : actSq (Aω ω) x = (∑ k : Fin (n - 1), ((∑ j : Fin n, Aω ω k j * x j))^2) := rfl
        rw [hA]
        change (∑ k : Fin (n - 1), ((∑ j : Fin n, Aω ω k j * x j))^2)
            ≤ L ^ 2 * (n : ℝ) * (∑ i : Fin n, (x i) ^ 2)
        have hC2 : (Csp * Real.sqrt (n : ℝ)) ^ 2 ≤ L ^ 2 * (n : ℝ) := by
          have hC0 : 0 ≤ Csp := by positivity
          have hL0' : 0 ≤ L := by positivity
          have hcl : Csp * Real.sqrt (n : ℝ) ≤ L * Real.sqrt (n : ℝ) := by
            exact mul_le_mul_of_nonneg_right hLgeC (Real.sqrt_nonneg _)
          have hsqb : (Csp * Real.sqrt (n : ℝ)) ^ 2 ≤ (L * Real.sqrt (n : ℝ)) ^ 2 := by
            exact sq_le_sq.mpr (by
              rw [abs_of_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _)),
                  abs_of_nonneg (mul_nonneg hL0' (Real.sqrt_nonneg _))]
              exact hcl)
          calc
            (Csp * Real.sqrt (n : ℝ)) ^ 2 ≤ (L * Real.sqrt (n : ℝ)) ^ 2 := hsqb
            _ = L ^ 2 * (n : ℝ) := by
              rw [mul_pow]
              have hsqn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
              rw [hsqn]
        have hsqx : 0 ≤ (∑ i : Fin n, (x i) ^ 2) := by positivity
        have hhh : (∑ k : Fin (n - 1), ((∑ j : Fin n, Aω ω k j * x j))^2)
            ≤ (Csp * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (x i) ^ 2) := by
          simpa using hh
        have hC2s : (Csp * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (x i) ^ 2)
            ≤ L ^ 2 * (n : ℝ) * (∑ i : Fin n, (x i) ^ 2) := by
          exact mul_le_mul_of_nonneg_right hC2 hsqx
        exact le_trans hhh hC2s
      -- net over the whole compressible set
      have hγle2 : γ ≤ γa := by
        dsimp [γ]
        have hs : Real.sqrt ee ≤ 1 := by
          have h1sq : Real.sqrt ee ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (le_of_lt hee1)
          simpa using h1sq
        nlinarith
      have hRle1 : γ / (8 * L) ≤ 1 := by
        have hLpos : 0 < L := by linarith
        have hnum : γ ≤ 8 * L := by
          calc
            γ ≤ γa := hγle2
            _ = 8 * (γa / 8) := by ring
            _ ≤ 8 * L := mul_le_mul_of_nonneg_left hLgeg (by norm_num)
        have hstep : γ / (8 * L) ≤ (8 * L) / (8 * L) := by
          exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 8 * L)
        have hsim : (8 * L) / (8 * L) = 1 := by
          have hLne : L ≠ 0 := ne_of_gt (by linarith : 0 < L)
          field_simp [hLne]
        rwa [hsim] at hstep
      have hνpos : 0 < γ / (32 * L) := by positivity
      have hR0 : 0 < γ / (8 * L) := by positivity
      have hνR : γ / (32 * L) ≤ (γ / (8 * L)) / 4 := by
        have hLpos : 0 < L := by linarith
        have hLne : L ≠ 0 := ne_of_gt hLpos
        have hsim : γ / (32 * L) = (γ / (8 * L)) / 4 := by
          field_simp [hLne]
          ring
        rw [hsim]
      rcases hNetAvail n hn1 (δ := ee) (ν := γ / (32 * L)) (R := γ / (8 * L)) hee0
        (le_of_lt hee1) hνpos hνR hR0 hRle1 with ⟨Net₀, hcov, hcard0⟩
      let Bnet : ℝ := (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
          (C₁ / (γ / (8 * L))) ^ Nat.floor (ee * (n : ℝ))
      have hBnet0 : 0 ≤ Bnet := by
        dsimp [Bnet]
        positivity
      have hnet : ∃ Net : Finset (Fin n → ℝ),
          (∀ x : Fin n → ℝ,
              Commons.LinearAlgebra.Net.compressible ee (γ / (32 * L)) x →
              ∃ y ∈ Net, Commons.LinearAlgebra.Net.compressible ee (γ / (32 * L)) y ∧
                Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ (γ / (8 * L)) ^ 2) ∧
          ((Net.card : ℝ) ≤ Bnet) := by
        refine ⟨Net₀, hcov, ?_⟩
        have hc : (Net₀.card : ℝ) ≤ (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
            (C₁ / (γ / (8 * L))) ^ Nat.floor (ee * (n : ℝ)) := by
          simpa using hcard0
        simpa [Bnet] using hc
      -- per-point small ball (aux_single_vector with shift s := −p)
      let r₀ : ℕ := Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))
      let hauxb : ℝ := (Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (r₀ : ℝ)) ^ r₀ *
          (1 - (p : ℝ)) ^ ((n - 1) - r₀)
      have hAuxB0 : 0 ≤ hauxb := by
        dsimp [hauxb]
        have hr0 : 0 < (r₀ : ℝ) := by
          dsimp [r₀]
          exact_mod_cast (aux_r_pos hee0 hn2n)
        have hpart1 : 0 ≤ Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (r₀ : ℝ) := by
          exact div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos 1)) (by positivity)) (le_of_lt hr0)
        have hpp : (p : ℝ) ≤ 1 := (p.property).2
        have hpart2 : 0 ≤ (1 - (p : ℝ)) ^ ((n - 1) - r₀) := by
          exact pow_nonneg (by linarith) _
        exact mul_nonneg (pow_nonneg hpart1 _) hpart2
      have hpt : ∀ y : Fin n → ℝ, (∑ j : Fin n, (y j) ^ 2) = 1 →
          P.real {ω : Ω | actSq (fun k j => B k j ω - (p : ℝ)) y ≤ γ ^ 2 * (n : ℝ)} ≤ hauxb := by
        intro y hyunit
        have hle_e : ee * ((n - 1 : ℕ) : ℝ) ≤ (r₀ : ℝ) := by
          dsimp [r₀]
          exact Nat.le_ceil _
        have hrpos : 0 < r₀ := by
          dsimp [r₀]
          exact aux_r_pos hee0 hn2n
        have hrle : r₀ ≤ n - 1 := by
          dsimp [r₀]
          exact aux_r_le (le_of_lt hee1) hn2n
        have hmain := hAux ee hee0 n hn2n (Ω := Ω) P B hBmeas hBind hBlaw (s := -(p : ℝ)) (x := y) hyunit
          (r := r₀) hrpos hrle hle_e
        have hscale : γa ^ 2 * ee * (n : ℝ) = γ ^ 2 * (n : ℝ) := by
          dsimp [γ]
          rw [scale_sq (le_of_lt hee0)]
        have hm2 : P.real {ω : Ω |
            actSq (fun k j => B k j ω + -(p : ℝ)) y ≤ γa ^ 2 * ee * (n : ℝ)} ≤ hauxb := by
          simpa [actSq, rowAct] using hmain
        have hev : {ω : Ω |
            actSq (fun k j => B k j ω + -(p : ℝ)) y ≤ γa ^ 2 * ee * (n : ℝ)}
            = {ω : Ω |
            actSq (fun k j => B k j ω + -(p : ℝ)) y ≤ γ ^ 2 * (n : ℝ)} := by
          ext ω
          rw [hscale]
        have hm3 : P.real {ω : Ω |
            actSq (fun k j => B k j ω + -(p : ℝ)) y ≤ γ ^ 2 * (n : ℝ)} ≤ hauxb := by
          rw [hev] at hm2
          exact hm2
        have hev2 : {ω : Ω |
            actSq (fun k j => B k j ω - (p : ℝ)) y ≤ γ ^ 2 * (n : ℝ)}
            = {ω : Ω |
            actSq (fun k j => B k j ω + -(p : ℝ)) y ≤ γ ^ 2 * (n : ℝ)} := by
          ext ω
          have hfun : (fun k : Fin (n - 1) => fun j : Fin n => B k j ω - (p : ℝ)) =
              (fun k : Fin (n - 1) => fun j : Fin n => B k j ω + -(p : ℝ)) := by
            funext k j
            ring
          simp only [Set.mem_setOf_eq]
          rw [hfun]
        have hfin : P.real {ω : Ω |
            actSq (fun k j => B k j ω - (p : ℝ)) y ≤ γ ^ 2 * (n : ℝ)} ≤ hauxb := by
          rw [hev2]
          exact hm3
        exact hfin
      -- assemble via compress_centered_main_bound
      have hmainb := compress_centered_main_bound (p := p) hp₀ hp₁ (eps := ee) hee0 (le_of_lt hee1)
        (n := n) hn2n (L := L) (γ := γ) hL1 hγ0 (Ω := Ω) P B hBmeas hBind hBlaw
        (Sspec := G) hGm hGP2 hGon Bnet hBnet0 hnet hauxb hAuxB0 hpt
      have hg₀ : γ₀ ^ 2 * (n : ℝ) = (γ / 2) ^ 2 * (n : ℝ) := by
        dsimp [γ₀]
      have htarget : {ω : Ω | ∃ x : Fin n → ℝ,
          Commons.LinearAlgebra.Net.compressible ee (γ / (32 * L)) x ∧
          actSq (fun k j => B k j ω - (p : ℝ)) x ≤ γ₀ ^ 2 * (n : ℝ)}
          = {ω : Ω | ∃ x : Fin n → ℝ,
          Commons.LinearAlgebra.Net.compressible ee (γ / (32 * L)) x ∧
          actSq (fun k j => B k j ω - (p : ℝ)) x ≤ (γ / 2) ^ 2 * (n : ℝ)} := by
        ext ω
        rw [hg₀]
      have hstep2 : (1 / 2 : ℝ) ^ n + Bnet * hauxb ≤ (1 / 2 : ℝ) ^ n +
          (1 / Real.sqrt ee) * Bnet * hauxb := by
        have hone : 1 ≤ 1 / Real.sqrt ee := by
          have hs0 : 0 < Real.sqrt ee := Real.sqrt_pos.2 hee0
          have hle : Real.sqrt ee ≤ 1 := by
            have h1sq : Real.sqrt ee ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (le_of_lt hee1)
            simpa using h1sq
          rw [one_le_div hs0]
          exact hle
        have hmul : Bnet * hauxb ≤ (1 / Real.sqrt ee) * Bnet * hauxb := by
          calc
            Bnet * hauxb = 1 * (Bnet * hauxb) := by ring
            _ ≤ (1 / Real.sqrt ee) * (Bnet * hauxb) := by
              exact mul_le_mul_of_nonneg_right hone (mul_nonneg hBnet0 hAuxB0)
            _ = (1 / Real.sqrt ee) * Bnet * hauxb := by ring
        nlinarith
      have h2 := le_trans hmainb hstep2
      have hL0n := hL0 n hn
      have hb2 : C₁ / ((γa * Real.sqrt ee) / (8 * L)) = C₁ * (8 * L) / (γa * Real.sqrt ee) := by
        have hgne : γa * Real.sqrt ee ≠ 0 := by positivity
        field_simp [hgne]
      have hL0match : (1 / 2 : ℝ) ^ n + (1 / Real.sqrt ee) * Bnet * hauxb
          ≤ (1 - (p : ℝ) + ε) ^ n := by
        calc
          (1 / 2 : ℝ) ^ n + (1 / Real.sqrt ee) * Bnet * hauxb
              = (1 / 2 : ℝ) ^ n + (1 / Real.sqrt ee) *
                  (n.choose (Nat.floor (ee * (n : ℝ))) : ℝ) *
                  (C₁ * (8 * L) / (γa * Real.sqrt ee)) ^ Nat.floor (ee * (n : ℝ)) *
                  (((Real.exp 1 * ((n - 1 : ℕ) : ℝ) /
                      (Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)) : ℝ)) ^
                        Nat.ceil (ee * ((n - 1 : ℕ) : ℝ))) *
                    (1 - (p : ℝ)) ^ ((n - 1) - Nat.ceil (ee * ((n - 1 : ℕ) : ℝ)))) := by
            dsimp [Bnet, hauxb, r₀, γ]
            rw [hb2]
            ring
          _ ≤ (1 - (p : ℝ) + ε) ^ n := by
            simpa [mul_assoc] using hL0n
      exact le_trans (le_trans hmainb hstep2) hL0match


/-! ## 4. Full-`n×n`-matrix centered wrap -/

/-- `compress_side_bound` for the CENTERED matrix `B ω − p·11ᵀ` (entries
`B ω i j − p`): full-`n×n`-matrix form, `s`-free (this is the `s = −p` case of
Theorem A's compress side). -/
theorem compress_side_bound_centered_of_net {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε)
    (hNet : ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ {δ ν R : ℝ}, 0 < δ → δ ≤ 1 → 0 < ν → ν ≤ R / 4 → 0 < R → R ≤ 1 →
        ∃ Net : Finset (Fin n → ℝ),
          (∀ x : Fin n → ℝ, Commons.LinearAlgebra.Net.compressible δ ν x →
              ∃ y ∈ Net, Commons.LinearAlgebra.Net.compressible δ ν y ∧
                Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ R^2) ∧
          (Net.card : ℝ) ≤ (n.choose ⌊δ * (n : ℝ)⌋₊ : ℝ) * (C₁ / R) ^ ⌊δ * (n : ℝ)⌋₊) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
        (hBpt : ∀ i j : Fin n, ∀ ω : Ω, |B ω i j - (p : ℝ)| ≤ 1),
        ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | ∃ f : Fin n → ℝ,
            Commons.LinearAlgebra.Net.compressible δ ν f ∧
            actSqFullFn (fun i j : Fin n => B ω i j - (p : ℝ)) f ≤ u ^ 2}
            ≤ (1 - (p : ℝ) + ε) ^ n := by
  rcases compress_theorem_centered_of_net hp₀ hp₁ hε₀ hNet
    with ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, hmain⟩
  refine ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, ?_⟩
  intro n hn Ω mΩ P hP B hBmeas hBind hBlaw hBpt u hu0 hule
  let T : Fin (n - 1) → Fin n → Ω → ℝ := Submission.GeoBridge.rowFamily B
  have hTmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (T k j) := by
    intro k j
    dsimp [T, Submission.GeoBridge.rowFamily]
    exact hBmeas (Submission.GeoBridge.emb k) j
  have hTind : ProbabilityTheory.iIndepFun
      (fun kj : Fin (n - 1) × Fin n => T kj.1 kj.2) P := by
    have hg : Function.Injective (fun kj : Fin (n - 1) × Fin n => (Submission.GeoBridge.emb kj.1, kj.2)) := by
      intro a b hab
      have h1 : Submission.GeoBridge.emb a.1 = Submission.GeoBridge.emb b.1 := by simpa using congrArg Prod.fst hab
      have h2 : a.2 = b.2 := by simpa using congrArg Prod.snd hab
      apply Prod.ext
      · exact Submission.GeoBridge.emb_injective h1
      · exact h2
    have hind := ProbabilityTheory.iIndepFun.precomp hg hBind
    exact hind
  have hTlaw : ∀ k : Fin (n - 1), ∀ j : Fin n, HasLaw (T k j) (bernoulliMeasure 1 0 p) P := by
    intro k j
    dsimp [T, Submission.GeoBridge.rowFamily]
    change HasLaw (fun ω : Ω => B ω (Submission.GeoBridge.emb k) j) (bernoulliMeasure 1 0 p) P
    exact hBlaw (Submission.GeoBridge.emb k) j
  have hTpt : ∀ k : Fin (n - 1), ∀ j : Fin n, ∀ ω : Ω, |T k j ω - (p : ℝ)| ≤ 1 := by
    intro k j ω
    dsimp [T, Submission.GeoBridge.rowFamily]
    exact hBpt (Submission.GeoBridge.emb k) j ω
  have hmain' := hmain n hn (Ω := Ω) P T hTmeas hTind hTlaw hTpt
  let E : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => B ω i j - (p : ℝ)) f ≤ u ^ 2}
  let F : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSq (fun k : Fin (n - 1) => fun j : Fin n => T k j ω - (p : ℝ)) f ≤ γ₀ ^ 2 * (n : ℝ)}
  have hEF : E ⊆ F := by
    intro ω hω
    rcases hω with ⟨f, hfc, hfull⟩
    refine ⟨f, hfc, ?_⟩
    have hpart : actSq (fun k : Fin (n - 1) => fun j : Fin n => B ω (Submission.GeoBridge.emb k) j - (p : ℝ)) f ≤ u ^ 2 := by
      have hpl := Submission.GeoBridge.partial_actSqFn_le_fullFn (fun i j : Fin n => B ω i j - (p : ℝ)) f
      simpa using (le_trans hpl hfull)
    have hsame : actSq (fun k : Fin (n - 1) => fun j : Fin n => B ω (Submission.GeoBridge.emb k) j - (p : ℝ)) f =
        actSq (fun k : Fin (n - 1) => fun j : Fin n => T k j ω - (p : ℝ)) f := by
      apply congrArg (fun A => actSq A f)
      funext k j
      rfl
    have hu2 : u ^ 2 ≤ γ₀ ^ 2 * (n : ℝ) := by
      have hmul : u * u ≤ (γ₀ * Real.sqrt (n : ℝ)) * (γ₀ * Real.sqrt (n : ℝ)) := by
        exact mul_le_mul hule hule (le_of_lt hu0) (le_trans (le_of_lt hu0) hule)
      have h0 : 0 ≤ (n : ℝ) := by positivity
      have hsq : (γ₀ * Real.sqrt (n : ℝ)) ^ 2 = γ₀ ^ 2 * (n : ℝ) := by
        rw [mul_pow]
        rw [Real.sq_sqrt h0]
      calc
        u ^ 2 = u * u := by ring
        _ ≤ (γ₀ * Real.sqrt (n : ℝ)) * (γ₀ * Real.sqrt (n : ℝ)) := hmul
        _ = (γ₀ * Real.sqrt (n : ℝ)) ^ 2 := by ring
        _ = γ₀ ^ 2 * (n : ℝ) := hsq
    have hfin : actSq (fun k : Fin (n - 1) => fun j : Fin n => T k j ω - (p : ℝ)) f ≤
        γ₀ ^ 2 * (n : ℝ) := by
      rw [← hsame]
      exact le_trans hpart hu2
    exact hfin
  have hFmeas : P F ≠ ⊤ := by
    have hle : P F ≤ (1 : ℝ≥0∞) := by
      have hmono : P F ≤ P Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      simpa using hmono
    exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle
  have hPF : P.real F ≤ (1 - (p : ℝ) + ε) ^ n := hmain'
  have hmono' : P.real E ≤ P.real F := MeasureTheory.measureReal_mono hEF hFmeas
  exact le_trans hmono' hPF


/-! ## 5. The `σ_min` decomposition for EVERY shift `s` -/

/-- `sigma_min_decomp` with NO restriction on the shift `s`: the
`σ_min`-small-ball event of `B ω + s·11ᵀ` is at most `(1−p+ε)ⁿ` plus the
incompressible small-ball part, for every real `s` (including `s = −p`, where
the matrix `B ω − p·11ᵀ` is centered).  Both compress-side bounds
(`compress_side_bound` for `s+p ≠ 0`, the centered one for `s+p = 0`) are
combined by shrinking `δ, ν, γ₀`. -/
theorem sigma_min_decomp_any_s_of_net {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε)
    (hNet : ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ {δ ν R : ℝ}, 0 < δ → δ ≤ 1 → 0 < ν → ν ≤ R / 4 → 0 < R → R ≤ 1 →
        ∃ Net : Finset (Fin n → ℝ),
          (∀ x : Fin n → ℝ, Commons.LinearAlgebra.Net.compressible δ ν x →
              ∃ y ∈ Net, Commons.LinearAlgebra.Net.compressible δ ν y ∧
                Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ R^2) ∧
          (Net.card : ℝ) ≤ (n.choose ⌊δ * (n : ℝ)⌋₊ : ℝ) * (C₁ / R) ^ ⌊δ * (n : ℝ)⌋₊) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
        (hBpt : ∀ i j : Fin n, ∀ ω : Ω, |B ω i j - (p : ℝ)| ≤ 1),
        ∀ s : ℝ, ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
            ≤ (1 - (p : ℝ) + ε) ^ n
              + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
                  ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
                  actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by
  classical
  rcases compress_side_bound hp₀ hp₁ hε₀
    with ⟨n₀s, hn₀s2, γ₀s, hγ₀s, δs, hδs0, hδs1, νs, hνs0, hνs1, hcsb⟩
  rcases compress_side_bound_centered_of_net hp₀ hp₁ hε₀ hNet
    with ⟨n₀c, hn₀c2, γ₀c, hγ₀c, δc, hδc0, hδc1, νc, hνc0, hνc1, hccb⟩
  let n₀ : ℕ := max n₀s n₀c
  let γ₀ : ℝ := min γ₀s γ₀c
  let δ : ℝ := min δs δc
  let ν : ℝ := min νs νc
  have hn₀ : 2 ≤ n₀ := by
    dsimp [n₀]
    exact le_trans hn₀s2 (le_max_left n₀s n₀c)
  have hγ₀ : 0 < γ₀ := by
    dsimp [γ₀]
    rcases le_total γ₀s γ₀c with h | h
    · rw [min_eq_left h]
      exact hγ₀s
    · rw [min_eq_right h]
      exact hγ₀c
  have hδ0 : 0 < δ := by
    dsimp [δ]
    rcases le_total δs δc with h | h
    · rw [min_eq_left h]
      exact hδs0
    · rw [min_eq_right h]
      exact hδc0
  have hδ1 : δ < 1 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_left δs δc) hδs1
  have hν0 : 0 < ν := by
    dsimp [ν]
    rcases le_total νs νc with h | h
    · rw [min_eq_left h]
      exact hνs0
    · rw [min_eq_right h]
      exact hνc0
  have hν1 : ν < 1 := by
    dsimp [ν]
    exact lt_of_le_of_lt (min_le_left νs νc) hνs1
  refine ⟨n₀, hn₀, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, ?_⟩
  intro n hn Ω mΩ P hP B hBmeas hBind hBlaw hBpt s u hu0 hule
  have hn₀s_le : n₀s ≤ n := le_trans (le_max_left n₀s n₀c) hn
  have hn₀c_le : n₀c ≤ n := le_trans (le_max_right n₀s n₀c) hn
  have hγ₀s_le : γ₀ ≤ γ₀s := by dsimp [γ₀]; exact min_le_left γ₀s γ₀c
  have hγ₀c_le : γ₀ ≤ γ₀c := by dsimp [γ₀]; exact min_le_right γ₀s γ₀c
  have hule_s : u ≤ γ₀s * Real.sqrt (n : ℝ) := by
    exact le_trans hule (mul_le_mul_of_nonneg_right hγ₀s_le (Real.sqrt_nonneg _))
  have hule_c : u ≤ γ₀c * Real.sqrt (n : ℝ) := by
    exact le_trans hule (mul_le_mul_of_nonneg_right hγ₀c_le (Real.sqrt_nonneg _))
  -- shifted full matrix event (function level)
  let Es : Set Ω := {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
  let Ef : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2}
  let Ec : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2}
  let Ei : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2}
  -- Ef ⊆ Ec ∪ Ei
  have hEf : Ef ⊆ Ec ∪ Ei := by
    intro ω hω
    rcases hω with ⟨f, hf1, hfball⟩
    by_cases hc : Commons.LinearAlgebra.Net.compressible δ ν f
    · exact Or.inl ⟨f, hc, hfball⟩
    · exact Or.inr ⟨f, hf1, hc, hfball⟩
  -- Es ⊆ Ef
  have hEsEf : Es ⊆ Ef := by
    intro ω hω
    have hn1 : 1 ≤ n := by omega
    have hx := (sigma_min_le_iff hn1 (B ω + Matrix.of (fun _ _ : Fin n => s)) u).1 hω
    rcases exists_function_of_sigma_min hn1 (B ω + Matrix.of (fun _ _ : Fin n => s)) (le_of_lt hu0) hx with
      ⟨f, hf1, hfballM⟩
    refine ⟨f, hf1, ?_⟩
    have heq : actSqFull (B ω + Matrix.of (fun _ _ : Fin n => s)) f =
        actSqFullFn (fun i j : Fin n => B ω i j + s) f := by
      dsimp [actSqFull, actSqFullFn]
    rwa [heq] at hfballM
  have hEs : Es ⊆ Ec ∪ Ei := Set.Subset.trans hEsEf hEf
  -- measure bounds
  have hEi : P.real Es ≤ P.real Ec + P.real Ei := by
    have hmono : P.real Es ≤ P.real (Ec ∪ Ei) := MeasureTheory.measureReal_mono hEs (by
      have hle : P (Ec ∪ Ei) ≤ (1 : ℝ≥0∞) := by
        have hmono' : P (Ec ∪ Ei) ≤ P Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
        simpa using hmono'
      exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle)
    exact le_trans hmono (MeasureTheory.measureReal_union_le Ec Ei)
  -- compressible-part bound, branching on s + p
  have hEc : P.real Ec ≤ (1 - (p : ℝ) + ε) ^ n := by
    by_cases hss : s + (p : ℝ) ≠ 0
    · -- s + p ≠ 0 : use compress_side_bound at (δs,νs), then restrict compressibility
      have hb := hcsb n hn₀s_le (Ω := Ω) P B hBmeas hBind hBlaw hBpt s hss u hu0 hule_s
      have hmono : P.real Ec ≤ P.real {ω : Ω | ∃ f : Fin n → ℝ,
          Commons.LinearAlgebra.Net.compressible δs νs f ∧
          actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by
        apply MeasureTheory.measureReal_mono (s₁ := Ec)
        · intro ω hω
          rcases hω with ⟨f, hfc, hball⟩
          refine ⟨f, ?_, hball⟩
          have hδle : δ ≤ δs := by dsimp [δ]; exact min_le_left δs δc
          have hνle : ν ≤ νs := by dsimp [ν]; exact min_le_left νs νc
          rcases hfc with ⟨h1, z, hzsq, hzsup⟩
          refine ⟨h1, z, ?_, ?_⟩
          · have hsq : ν ^ 2 ≤ νs ^ 2 := by
              exact sq_le_sq.mpr (by
                rw [abs_of_nonneg (le_of_lt hν0), abs_of_nonneg (le_of_lt hνs0)]
                exact hνle)
            exact le_trans hzsq hsq
          · exact le_trans hzsup (mul_le_mul_of_nonneg_right hδle (by positivity : 0 ≤ (n : ℝ)))
      exact le_trans hmono hb
    · -- s + p = 0 : entries Bω + s = Bω − p; use the centered bound at (δc,νc)
      have hs0 : s = -(p : ℝ) := by
        have : s + (p : ℝ) = 0 := by simpa [not_not] using hss
        linarith
      have hb := hccb n hn₀c_le (Ω := Ω) P B hBmeas hBind hBlaw hBpt u hu0 hule_c
      have hev_eq : {ω : Ω | ∃ f : Fin n → ℝ,
            Commons.LinearAlgebra.Net.compressible δ ν f ∧
            actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2}
          ⊆ {ω : Ω | ∃ f : Fin n → ℝ,
            Commons.LinearAlgebra.Net.compressible δc νc f ∧
            actSqFullFn (fun i j : Fin n => B ω i j - (p : ℝ)) f ≤ u ^ 2} := by
        intro ω hω
        rcases hω with ⟨f, hfc, hball⟩
        have hδle : δ ≤ δc := by dsimp [δ]; exact min_le_right δs δc
        have hνle : ν ≤ νc := by dsimp [ν]; exact min_le_right νs νc
        have hfc_c : Commons.LinearAlgebra.Net.compressible δc νc f := by
          rcases hfc with ⟨h1, z, hzsq, hzsup⟩
          refine ⟨h1, z, ?_, ?_⟩
          · have hsq : ν ^ 2 ≤ νc ^ 2 := by
              exact sq_le_sq.mpr (by
                rw [abs_of_nonneg (le_of_lt hν0), abs_of_nonneg (le_of_lt hνc0)]
                exact hνle)
            exact le_trans hzsq hsq
          · exact le_trans hzsup (mul_le_mul_of_nonneg_right hδle (by positivity : 0 ≤ (n : ℝ)))
        refine ⟨f, hfc_c, ?_⟩
        have hent : actSqFullFn (fun i j : Fin n => B ω i j + s) f =
            actSqFullFn (fun i j : Fin n => B ω i j - (p : ℝ)) f := by
          apply congrArg (fun M : Fin n → Fin n → ℝ => actSqFullFn M f)
          funext i j
          rw [hs0]
          ring
        rwa [← hent]
      have hmono : P.real Ec ≤ P.real {ω : Ω | ∃ f : Fin n → ℝ,
          Commons.LinearAlgebra.Net.compressible δc νc f ∧
          actSqFullFn (fun i j : Fin n => B ω i j - (p : ℝ)) f ≤ u ^ 2} := by
        exact MeasureTheory.measureReal_mono hev_eq (measure_ne_top P {ω : Ω | ∃ f : Fin n → ℝ,
          Commons.LinearAlgebra.Net.compressible δc νc f ∧
          actSqFullFn (fun i j : Fin n => B ω i j - (p : ℝ)) f ≤ u ^ 2})
      exact le_trans hmono hb
  have hfinal : P.real Es ≤ (1 - (p : ℝ) + ε) ^ n + P.real Ei := by
    have hEc2 : P.real Ec + P.real Ei ≤ (1 - (p : ℝ) + ε) ^ n + P.real Ei := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hEc (P.real Ei)
    exact le_trans hEi hEc2
  simpa [Es, Ei] using hfinal


/-! ## 6. Law-only version (Theorem A hypothesis set) -/

/-- Law-only version of `sigma_min_decomp_any_s`: from `iIndepFun` + Bernoulli
laws only (no measurability, no pointwise bound), the `σ_min`-small-ball event
of `B ω + s·11ᵀ` is at most `(1−p+ε)ⁿ` plus the incompressible small-ball
part, for every shift `s ∈ ℝ` (including `s = −p`). -/
theorem sigma_min_decomp_law_only_any_s_of_net {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε)
    (hNet : ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ {δ ν R : ℝ}, 0 < δ → δ ≤ 1 → 0 < ν → ν ≤ R / 4 → 0 < R → R ≤ 1 →
        ∃ Net : Finset (Fin n → ℝ),
          (∀ x : Fin n → ℝ, Commons.LinearAlgebra.Net.compressible δ ν x →
              ∃ y ∈ Net, Commons.LinearAlgebra.Net.compressible δ ν y ∧
                Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ R^2) ∧
          (Net.card : ℝ) ≤ (n.choose ⌊δ * (n : ℝ)⌋₊ : ℝ) * (C₁ / R) ^ ⌊δ * (n : ℝ)⌋₊) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P),
        ∀ s : ℝ, ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
            ≤ (1 - (p : ℝ) + ε) ^ n
              + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
                  ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
                  actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by
  rcases sigma_min_decomp_any_s_of_net hp₀ hp₁ hε₀ hNet
    with ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, hdec⟩
  refine ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, ?_⟩
  intro n hn Ω mΩ P hP B hBind hBlaw s u hu0 hule
  rcases exists_measurable_clamped_matrix (P := P) B hBind hBlaw with
    ⟨Bc, hcm, hcind, hclaw, hcpt, hcae⟩
  have hdecBc := hdec n hn (Ω := Ω) P Bc hcm hcind hclaw hcpt s u hu0 hule
  -- transfer of the sigma_min event
  let Sσ : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {M | RandomBernoulliMatrices.σ_min (M + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
  have htr1 : P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u} =
      P.real {ω : Ω | RandomBernoulliMatrices.σ_min (Bc ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u} := by
    exact (measureReal_matrix_event_eq_of_ae (P := P) Bc B hcae Sσ).symm
  -- transfer of the incompressible event
  let Sin : Set (Matrix (Fin n) (Fin n) ℝ) := {M | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => M i j + s) f ≤ u ^ 2}
  have htr2 : P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => Bc ω i j + s) f ≤ u ^ 2} =
      P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by
    exact measureReal_matrix_event_eq_of_ae (P := P) Bc B hcae Sin
  have hmain : P.real {ω : Ω | RandomBernoulliMatrices.σ_min (Bc ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
      ≤ (1 - (p : ℝ) + ε) ^ n + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
        ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
        actSqFullFn (fun i j : Fin n => Bc ω i j + s) f ≤ u ^ 2} := hdecBc
  calc
    P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
        = P.real {ω : Ω | RandomBernoulliMatrices.σ_min (Bc ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u} := htr1
    _ ≤ (1 - (p : ℝ) + ε) ^ n + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
        ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
        actSqFullFn (fun i j : Fin n => Bc ω i j + s) f ≤ u ^ 2} := hmain
    _ = (1 - (p : ℝ) + ε) ^ n + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
        ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
        actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by rw [htr2]


/-! ## 7. Final glue: instantiate the Commons compressible net -/

/-- `compress_theorem_centered` (rows `Fin (n−1)`), paper form: no net
hypothesis — the net is `Commons.LinearAlgebra.Net.compressible_net`. -/
theorem compress_theorem_centered {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Fin (n - 1) → Fin n → Ω → ℝ)
        (hBmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (B k j))
        (hBind : ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => B kj.1 kj.2) P)
        (hBlaw : ∀ k : Fin (n - 1), ∀ j : Fin n, HasLaw (B k j) (bernoulliMeasure 1 0 p) P)
        (hBpt : ∀ k : Fin (n - 1), ∀ j : Fin n, ∀ ω : Ω, |B k j ω - (p : ℝ)| ≤ 1),
          P.real {ω : Ω | ∃ x : Fin n → ℝ,
            Commons.LinearAlgebra.Net.compressible δ ν x ∧
            actSq (fun k j => B k j ω - (p : ℝ)) x ≤ γ₀ ^ 2 * (n : ℝ)} ≤ (1 - (p : ℝ) + ε) ^ n := by
  rcases Commons.LinearAlgebra.Net.compressible_net with ⟨C₁, hC₁₁, hNet⟩
  exact compress_theorem_centered_of_net hp₀ hp₁ hε₀ ⟨C₁, hC₁₁, hNet⟩

/-- `compress_side_bound_centered`: full-`n×n`-matrix centered compress side,
paper form. -/
theorem compress_side_bound_centered {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
        (hBpt : ∀ i j : Fin n, ∀ ω : Ω, |B ω i j - (p : ℝ)| ≤ 1),
        ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | ∃ f : Fin n → ℝ,
            Commons.LinearAlgebra.Net.compressible δ ν f ∧
            actSqFullFn (fun i j : Fin n => B ω i j - (p : ℝ)) f ≤ u ^ 2}
            ≤ (1 - (p : ℝ) + ε) ^ n := by
  rcases Commons.LinearAlgebra.Net.compressible_net with ⟨C₁, hC₁₁, hNet⟩
  exact compress_side_bound_centered_of_net hp₀ hp₁ hε₀ ⟨C₁, hC₁₁, hNet⟩

/-- `sigma_min_decomp_any_s`: `σ_min`-decomposition for every shift `s`,
paper form. -/
theorem sigma_min_decomp_any_s {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
        (hBpt : ∀ i j : Fin n, ∀ ω : Ω, |B ω i j - (p : ℝ)| ≤ 1),
        ∀ s : ℝ, ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
            ≤ (1 - (p : ℝ) + ε) ^ n
              + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
                  ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
                  actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by
  rcases Commons.LinearAlgebra.Net.compressible_net with ⟨C₁, hC₁₁, hNet⟩
  exact sigma_min_decomp_any_s_of_net hp₀ hp₁ hε₀ ⟨C₁, hC₁₁, hNet⟩

/-- THE Theorem-A-ready compress-side decomposition, law-only, for EVERY
shift `s ∈ ℝ` (including `s = −p`): from `iIndepFun` + Bernoulli laws only,

    P{ σ_min (B ω + s·11ᵀ) ≤ u } ≤ (1−p+ε)ⁿ + P{ incompressible part },

whenever `u ≤ γ₀·√n`. -/
theorem sigma_min_decomp_law_only_any_s {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P),
        ∀ s : ℝ, ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
            ≤ (1 - (p : ℝ) + ε) ^ n
              + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
                  ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
                  actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by
  rcases Commons.LinearAlgebra.Net.compressible_net with ⟨C₁, hC₁₁, hNet⟩
  exact sigma_min_decomp_law_only_any_s_of_net hp₀ hp₁ hε₀ ⟨C₁, hC₁₁, hNet⟩

end

end Submission.CompressCentered
