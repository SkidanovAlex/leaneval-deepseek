/-
# The `g`-side bounded-height packet estimate `SliceGBound` (the `(2,2,1)` instance of `(lin-2)`)

Target: `Work.KMTPlan.A6.PieceBoundedH.sliceGBound`, i.e.
`Work.KMTPlan.A6.PieceBoundedH.SliceGBound P r C₀ ρ B`: for every height-bounded quadruple
(`lcL l₁ l₂ k₁ k₂ ≤ B`) there is `K : ℝ≥0 → ℝ≥0` with

  `‖ V^r_n (1_{core n} · T^{≤l₂}_{φ̃_{N_n,t}} G) ‖_{ℓ²(ℤ)} ≤ K(Λ) ‖g‖_{ℓ²(ℤ)}`,
  `N_n = ⌊a n⌋`, `G = Π_{l₂,≤-d·u} g`, `u = uScale ρ (lcL …)`,

uniformly in the `Λ`-lacunary scale sequence `a`, in `t ∈ [1/2,1]` and in `g`.

## The route

This is the paper's `(lin-2)` at `(p₁,p₂,p) = (2,2,1)`, at *bounded arithmetic height*, with the
loss absorbed into `K(Λ)`.  The decomposition is that of the (proved) assembly
`Work.KMTAreas.A7Hi.lacunaryBumpVarEstimate_assemblyG` and of `Work.KMTAreas.A7LoLin`, specialised
to bounded heights:

* **narrow scales** (`core ∧ Farey`):  the two *proved* narrow estimates
  `lacunaryBumpFareyPartBoundG` (`k₂ ≥ 1`, the modulated bump) and
  `lacunaryBumpFareyDiffPartBoundG` (`k₂ = 0`, the modulated *difference* `φ̃_{N,t} − φ̃_N`);
* the remaining *unmodulated* piece of the `k₂ = 0` case is the low-pass family
  `Tle ρ l₂ (varphitildeN d N 0) = kmtProj ρ l₂ (−(d·logN N))`, whose variational estimate is
  *unconditional* via the sieve route
  (`Work.KMTAreas.A7Hi2.eLpNorm_variationalNorm_lpf_le_sieveMass_uncond`, with the height-bounded
  loss absorbed) — this is the input `hLow` of `sliceGBound_of_lowpass`;
* **bad scales** (`core ∧ ¬Farey`) are *finitely many* at bounded height
  (`badScale_index_bound_g`: `¬Farey` bounds `Log N`), so they are estimated by the crude
  single-scale bound (`badPartG_Tle_single_scale_uniform`).

The pointwise decomposition `sliceG = (narrow part) + (bad part)` and the triangle inequality for
`variationalNorm` and `eLpNorm` is the assembly.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.PieceBoundedH.Defs
import Submission.Work.KMTPlan.A6.PieceBoundedH.badScalesBounded
import Submission.Work.KMTAreas.A7Hi.Gdiff
import Submission.Work.KMTAreas.A7Hi.Gbad
import Submission.Work.KMTAreas.A7Hi.summable_normSq_incFam
import Submission.Work.KMTAreas.A7Hi2.LowpassVarG2
import Submission.Work.KMTPlan.A6.PieceLocal.SieveRoute
import Submission.Work.KMTPlan.A6.variationalNorm_prefix_zero_le
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.PieceLocal

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.KMTContract Work.Analysis.EndVar
open Work.KMTAreas.A7
open Work.KMTPlan.A6.PieceBoundedH

/-! ## §1.  Basic identifications and bounds -/

/-- The model core condition is the contract core condition (definitional). -/
theorem mdlCore_iff_core (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n ↔ core ρ C₀ l₁ l₂ k₁ k₂ a n := Iff.rfl

/-- `lcL` bounds each of the four parameters. -/
theorem le_of_lcL_le {l₁ l₂ k₁ k₂ B : ℕ} (h : Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B) :
    l₁ ≤ B ∧ l₂ ≤ B ∧ k₁ ≤ B ∧ k₂ ≤ B := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [Work.KMTPlan.A6.lcL] at h
      omega

/-- The auxiliary scale `uScale` is monotone in the height. -/
theorem uScale_mono_g {ρ : ℝ} (hρ : 0 ≤ ρ) : Monotone (uScale ρ) := by
  intro L L' hLL'
  rw [uScale, uScale, scaleCount, scaleCount]
  refine Work.KMTAreas.A7.int_toNat_mono (Int.floor_mono ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h : ((L : ℕ) : ℝ) ≤ ((L' : ℕ) : ℝ) := by exact_mod_cast hLL'
  nlinarith

/-- **The `ℓ²` bound for the model input `mdlG`.**  On the rectangle `l ≤ B`, `u ≤ uScale ρ B`
the exact-height projection is `ℓ²`-bounded with a uniform constant (the maximum over the finite
box `{l ≤ B} × {−(d·uScale ρ B) ≤ κ ≤ 0}` of the single-scale IW projection bounds). -/
theorem mdlG_two_le (P : Polynomial ℤ) (ρ : ℝ) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (hl : l ≤ B) (u : ℕ) (hu : u ≤ uScale ρ B) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (Work.KMTPlan.A6.mdlG ρ P u l g) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  set Kg : ℤ := (P.natDegree : ℤ) * ((uScale ρ B : ℕ) : ℤ) with hKg
  have hex : ∀ p : ℕ × ℤ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (kmtProj ρ p.1 p.2 f) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
    fun p => Work.KMTAreas.A7Hi.eLpNorm_kmtProj_two_le ρ p.1 p.2
  set Cfun : ℕ × ℤ → ℝ := fun p => Classical.choose (hex p) with hCfun
  have hCfun0 : ∀ p, 0 ≤ Cfun p := fun p => (Classical.choose_spec (hex p)).1
  have hCfunb : ∀ p f, MeasureTheory.eLpNorm (kmtProj ρ p.1 p.2 f) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Cfun p) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
    fun p f => (Classical.choose_spec (hex p)).2 f
  set S : Finset (ℕ × ℤ) := (Finset.range (B + 1)).product (Finset.Icc (-Kg) 0) with hS
  set CC : ℝ := (∑ p ∈ S, max 0 (Cfun p)) + 1 with hCC
  have hCCpos : 0 < CC := by rw [hCC]; positivity
  have hCCle : ∀ p ∈ S, Cfun p ≤ CC := by
    intro p hp
    have h1 : max 0 (Cfun p) ≤ ∑ q ∈ S, max 0 (Cfun q) :=
      Finset.single_le_sum (fun q _ => le_max_left _ _) hp
    have h2 : Cfun p ≤ max 0 (Cfun p) := le_max_right _ _
    rw [hCC]; linarith
  refine ⟨2 * CC + 1, by positivity, ?_⟩
  intro l hl u hu g
  have hκmem : -((P.natDegree : ℤ) * (u : ℤ)) ∈ Finset.Icc (-Kg) 0 := by
    rw [Finset.mem_Icc]
    have h3 : (0 : ℤ) ≤ (P.natDegree : ℤ) := Int.natCast_nonneg _
    have h4 : (0 : ℤ) ≤ (u : ℤ) := Int.natCast_nonneg _
    constructor
    · rw [hKg]
      have h1 : (u : ℤ) ≤ ((uScale ρ B : ℕ) : ℤ) := by exact_mod_cast hu
      nlinarith
    · nlinarith
  have hmem : (l, -((P.natDegree : ℤ) * (u : ℤ))) ∈ S := by
    rw [hS]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), hκmem⟩
  have hmem0 : ((0 : ℕ), -((P.natDegree : ℤ) * (u : ℤ))) ∈ S := by
    rw [hS]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), hκmem⟩
  have hmem1 : ((l - 1 : ℕ), -((P.natDegree : ℤ) * (u : ℤ))) ∈ S := by
    rw [hS]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), hκmem⟩
  change MeasureTheory.eLpNorm (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l
      (-((P.natDegree : ℤ) * (u : ℤ))) g) 2 MeasureTheory.Measure.count
    ≤ ENNReal.ofReal (2 * CC + 1) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
  rw [Work.Analysis.EndVar.piExact]
  by_cases hl0 : l = 0
  · rw [if_pos hl0, Work.KMTContract.kmtPj_proj]
    refine (hCfunb ((0 : ℕ), -((P.natDegree : ℤ) * (u : ℤ))) g).trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have := hCCle _ hmem0; linarith
  · rw [if_neg hl0, Work.KMTContract.kmtPj_proj, Work.KMTContract.kmtPj_proj]
    refine (MeasureTheory.eLpNorm_sub_le
      (by norm_num : (1 : ENNReal) ≤ 2)).trans ?_
    refine (add_le_add (hCfunb (l, -((P.natDegree : ℤ) * (u : ℤ))) g)
      (hCfunb (l - 1, -((P.natDegree : ℤ) * (u : ℤ))) g)).trans ?_
    have h2 : Cfun (l, -((P.natDegree : ℤ) * (u : ℤ)))
        + Cfun (l - 1, -((P.natDegree : ℤ) * (u : ℤ))) ≤ 2 * CC + 1 := by
      have h1 := hCCle _ hmem
      have h2h := hCCle _ hmem1
      linarith
    calc ENNReal.ofReal (Cfun (l, -((P.natDegree : ℤ) * (u : ℤ))))
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
          + ENNReal.ofReal (Cfun (l - 1, -((P.natDegree : ℤ) * (u : ℤ))))
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
        = ENNReal.ofReal (Cfun (l, -((P.natDegree : ℤ) * (u : ℤ)))
            + Cfun (l - 1, -((P.natDegree : ℤ) * (u : ℤ))))
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
          rw [ENNReal.ofReal_add (hCfun0 _) (hCfun0 _), add_mul]
      _ ≤ ENNReal.ofReal (2 * CC + 1) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h2) bot_le

/-! ## §2.  The bad (non-narrow) scales at bounded heights -/

/-- The explicit scale cut of the bad (non-narrow) scales: `Log N < Cρc · 2^{ρ B₀} + 1 + B₀`
forces `N < badScaleCut ρ Cρc B₀`. -/
def badScaleCut (ρ : ℝ) (Cρc : ℝ) (B₀ : ℕ) : ℕ :=
  2 ^ (Nat.ceil (Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ)) + 1)

/-- **The bad scales have bounded `Log`.**  For `0 < ρ`, `3 ≤ Cρc` and a height bound `B₀`, every
core-and-not-narrow scale satisfies `Nat.floor (a n) < badScaleCut ρ Cρc B₀`.  (This is the
`g`-side (`l₂, k₂`) version of the bound used in
`Work.KMTPlan.A6.PieceBoundedH.badScales_bounded_of_height`; the smallness hypothesis
`ρ · C₀ ≤ 1/2` used by `Work.KMTAreas.A7.exists_Lnat_le_of_bad` is *not* needed here, because the
height is bounded.) -/
theorem badScale_floor_bound_g (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Cρc : ℝ)
    (hCρc : 3 ≤ Cρc) (B₀ : ℕ) :
    ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ),
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B₀ →
      ∀ n : ℕ, core ρ C₀ l₁ l₂ k₁ k₂ a n → ¬ Farey Cρc ρ l₂ k₂ a n →
        Nat.floor (a n) < badScaleCut ρ Cρc B₀ := by
  intro a l₁ l₂ k₁ k₂ hLnat n hcore hbad
  rw [badScaleCut]
  obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ := le_of_lcL_le hLnat
  have hl₂r : (l₂ : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast hl₂
  have hk₂r : (k₂ : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast hk₂
  set N : ℕ := Nat.floor (a n) with hN
  have hcut : Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N := hcore.2.1
  have h2cut := two_le_splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
  have hN3 : 3 ≤ N := by omega
  set M : ℕ := Nat.log 2 N with hM
  have hlogN : logN N = (M : ℤ) := by
    rw [logN, hM, max_eq_left (by omega : 2 ≤ N)]
  have hnotF : fareyK Cρc ρ l₂ < (k₂ : ℤ) - logN N := by
    have h : ¬ ((k₂ : ℤ) - logN N ≤ fareyK Cρc ρ l₂) := by
      simpa only [Farey] using hbad
    exact not_le.mp h
  have hfloor : -(Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) - 1 < ((fareyK Cρc ρ l₂ : ℤ) : ℝ) := by
    have h := Int.lt_floor_add_one (-(Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ))))
    simp only [fareyK]
    linarith
  have hcast : ((fareyK Cρc ρ l₂ : ℤ) : ℝ) < (k₂ : ℝ) - (M : ℝ) := by
    have h := hnotF
    rw [hlogN] at h
    exact_mod_cast h
  have hM_lt : (M : ℝ) < Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) + 1 + (k₂ : ℝ) := by linarith
  have hrpow : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (B₀ : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ, hl₂r])
  have hMT : (M : ℝ)
      < ((Nat.ceil (Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ)) + 1 : ℕ) : ℝ) := by
    have h1 : Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) + 1 + (k₂ : ℝ)
        ≤ Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ) := by
      have h2 := mul_le_mul_of_nonneg_left hrpow (by linarith : (0 : ℝ) ≤ Cρc)
      linarith
    push_cast
    have h3 := Nat.le_ceil (Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ))
    linarith
  have hMlt : M < Nat.ceil (Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ)) + 1 := by
    exact_mod_cast hMT
  have h1 : N < 2 ^ (M + 1) := by
    rw [hM]
    exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  calc N < 2 ^ (M + 1) := h1
    _ ≤ 2 ^ (Nat.ceil (Cρc * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 1 + (B₀ : ℝ)) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The bad scales are a finite initial segment.**  At bounded heights and `Λ > 1`, no index
beyond an explicit `n₀ = n₀(ρ, C₀, Cρc, Λ, B₀)` is core-and-not-narrow. -/
theorem badScale_index_bound_g (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Cρc : ℝ)
    (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ) (B₀ : ℕ) :
    ∃ n₀ : ℕ, ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ),
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B₀ →
      ∀ n : ℕ, n₀ ≤ n →
        ¬ (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n) := by
  set X : ℝ := max 1 ((badScaleCut ρ Cρc B₀ : ℕ) : ℝ) with hXdef
  have hX1 : (1 : ℝ) ≤ X := le_max_left _ _
  set n₀ : ℕ := Nat.ceil (Real.log X / Real.log ((Λ : NNReal) : ℝ) + 2) with hn₀
  refine ⟨n₀, ?_⟩
  intro a ha ha1 l₁ l₂ k₁ k₂ hLnat n hn hbad
  obtain ⟨K, hK, hKspec⟩ :=
    Work.KMTAreas.A7.lacunary_index_bound Λ hΛ a ha ha1 X hX1
  have haX : (a n : ℝ) < X := by
    have h1 : Nat.floor (a n) < badScaleCut ρ Cρc B₀ :=
      badScale_floor_bound_g ρ hρ C₀ hC₀ Cρc hCρc B₀ a l₁ l₂ k₁ k₂ hLnat n hbad.1 hbad.2
    have h2 : (a n : ℝ) < (Nat.floor (a n) : ℝ) + 1 := Nat.lt_floor_add_one (a n)
    have h3 : ((Nat.floor (a n) : ℕ) : ℝ) + 1 ≤ X := by
      have h4 : Nat.floor (a n) + 1 ≤ badScaleCut ρ Cρc B₀ := by omega
      have h5 : ((Nat.floor (a n) + 1 : ℕ) : ℝ) ≤ ((badScaleCut ρ Cρc B₀ : ℕ) : ℝ) := by
        exact_mod_cast h4
      push_cast at h5
      rw [hXdef]
      linarith [le_max_right (1 : ℝ) ((badScaleCut ρ Cρc B₀ : ℕ) : ℝ)]
    linarith
  have hnK : n < K := hKspec n haX
  have hKn₀ : K ≤ n₀ := by
    rw [hn₀]
    exact_mod_cast (le_trans hK (Nat.le_ceil _))
  omega

/-! ## §3.  Additivity of `Tle` in the symbol -/

/-- Additivity of `Tle` in the symbol, for bounded input (the `Tle` version of
`Work.KMTAreas.A7LoLin.Tle_add_of_bounded`; it needs only the admissibility of the two symbols). -/
theorem Tle_add_of_bounded {ρ : ℝ} {l : ℕ} {φ ψ : ℝ → ℂ}
    (hφ : Adm (iwArithFreqs ρ l) φ) (hψ : Adm (iwArithFreqs ρ l) ψ)
    {f : ℤ → ℂ} {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Tle ρ l (φ + ψ) f = Tle ρ l φ f + Tle ρ l ψ f := by
  have hper : periodize (φ + ψ) = periodize φ + periodize ψ := periodize_add hφ.1 hψ.1
  simp only [Tle, hper]
  exact iwConv_add_of_bounded hf hφ.2.1 hψ.2.1 hφ.2.2 hψ.2.2

/-! ## §4.  The bad (non-narrow) piece -/

/-- **The `core ∧ ¬Farey` piece is bounded** at bounded heights: the bad scales are an initial
segment of the index set, and on them the single scale `⌊a n⌋` is bounded, so the crude
single-scale bound applies to each of the (finitely many) terms. -/
theorem badPart_le (P : Polynomial ℤ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ)
    (hC₀ : 1 ≤ C₀) (Cρc : ℝ) (hCρc : 3 ≤ Cρc) (r : NNReal) (hr : 2 < r) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (hΛ : 1 < Λ)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (l₁ l₂ k₁ k₂ : ℕ), Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B →
        ∀ (t : ℝ), t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ (H : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
            then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0))
          2 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨Cs, hCspos, hCs⟩ :=
    Work.KMTAreas.A7Hi.badPartG_Tle_single_scale_uniform P ρ 2 (by norm_num) (by norm_num)
      B (badScaleCut ρ Cρc B)
  have hexAll : ∀ (Λ : NNReal), ∃ n₀ : ℕ, 1 < Λ → ∀ (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ),
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B →
      ∀ n : ℕ, n₀ ≤ n →
        ¬ (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n) := by
    intro Λ
    by_cases hΛ : 1 < Λ
    · obtain ⟨n₀, hn₀⟩ := badScale_index_bound_g ρ hρ C₀ hC₀ Cρc hCρc Λ hΛ B
      exact ⟨n₀, fun _ => hn₀⟩
    · exact ⟨0, fun hΛ' => absurd hΛ' hΛ⟩
  let Nk : NNReal → ℕ := fun Λ => Classical.choose (hexAll Λ)
  refine ⟨fun Λ => ENNReal.toNNReal (ENNReal.ofReal (4 * Cs * ((Nk Λ : ℕ) : ℝ) + 1)), ?_⟩
  intro a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ hlc t ht H
  set n₀ : ℕ := Nk Λ with hn₀def
  have hn₀c := Classical.choose_spec (hexAll Λ)
  have hn₀ : ∀ (a' : ℕ → NNReal) (ha' : PointwiseErgodicTheorems.Lacunary Λ a')
      (ha1' : ∀ n, 1 ≤ a' n) (l₁' l₂' k₁' k₂' : ℕ),
      Work.KMTPlan.A6.lcL l₁' l₂' k₁' k₂' ≤ B → ∀ n : ℕ, n₀ ≤ n →
      ¬ (core ρ C₀ l₁' l₂' k₁' k₂' a' n ∧ ¬ Farey Cρc ρ l₂' k₂' a' n) := by
    intro a' ha' ha1' l₁' l₂' k₁' k₂' hlc' n hn'
    rw [hn₀def] at hn'
    exact hn₀c hΛ a' ha' ha1' l₁' l₂' k₁' k₂' hlc' n hn'
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  set SB : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
      then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0 with hSB
  have hterm : ∀ n ∈ Finset.range n₀, MeasureTheory.eLpNorm (fun x => SB n x)
      2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Cs * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
    intro n hn
    rw [hSB]
    by_cases hmask : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
    · have hfun : (fun x : ℤ => (if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
          then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0))
          = Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H := by
        funext x
        show (if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
          then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0)
          = Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x
        rw [if_pos hmask]
      rw [hfun]
      have hfloor : Nat.floor (a n) < badScaleCut ρ Cρc B :=
        badScale_floor_bound_g ρ hρ C₀ hC₀ Cρc hCρc B a l₁ l₂ k₁ k₂ hlc n hmask.1 hmask.2
      have hl₂ : l₂ ≤ B := (le_of_lcL_le hlc).2.1
      have hk₂ : k₂ ≤ B := (le_of_lcL_le hlc).2.2.2
      exact hCs l₂ hl₂ (Nat.floor (a n)) k₂ (le_of_lt hfloor) hk₂ t ht H
    · have hfun : (fun x : ℤ => (if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
          then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0))
          = (0 : ℤ → ℂ) := by
        funext x
        show (if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
          then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0)
          = (0 : ℂ)
        rw [if_neg hmask]
      rw [hfun, MeasureTheory.eLpNorm_zero]
      exact bot_le
  have hsum : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => SB n x)) 2 MeasureTheory.Measure.count
      ≤ ∑ n ∈ Finset.range n₀, 4 * MeasureTheory.eLpNorm (fun x => SB n x)
          2 MeasureTheory.Measure.count :=
    eLpNorm_variationalNorm_le_sum (r := r) hr1 (p := 2) (by norm_num)
      (u := SB) (s := Finset.range n₀)
      (fun n hn => by
        have hn' : n₀ ≤ n := by simpa [Finset.mem_range, not_lt] using hn
        funext x
        rw [hSB]
        show (if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
          then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0)
          = (0 : ℂ)
        rw [if_neg (hn₀ a ha ha1 l₁ l₂ k₁ k₂ hlc n hn')])
      (fun n _ => (measurable_of_countable (SB n)).aestronglyMeasurable)
  have hAR : (∑ n ∈ Finset.range n₀, 4 * MeasureTheory.eLpNorm (fun x => SB n x)
        2 MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (4 * Cs * (n₀ : ℝ) + 1)
        * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
    have hstep1 : (∑ n ∈ Finset.range n₀, 4 * MeasureTheory.eLpNorm (fun x => SB n x)
          2 MeasureTheory.Measure.count)
        ≤ ∑ n ∈ Finset.range n₀, 4 * (ENNReal.ofReal Cs
            * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count) :=
      Finset.sum_le_sum (fun n hn => mul_le_mul' le_rfl (hterm n hn))
    refine hstep1.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hrew : ((n₀ : ℕ) : ENNReal) = ENNReal.ofReal ((n₀ : ℕ) : ℝ) :=
      (ENNReal.ofReal_natCast n₀).symm
    have h4 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by norm_num
    calc ((n₀ : ℕ) : ENNReal) * (4 * (ENNReal.ofReal Cs
            * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count))
        = ((n₀ : ℕ) : ENNReal) * 4 * ENNReal.ofReal Cs
            * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by ring
      _ = ENNReal.ofReal ((n₀ : ℕ) * 4 * Cs)
            * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
          rw [hrew, h4, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((n₀ : ℕ) : ℝ)),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((n₀ : ℕ) : ℝ) * 4)]
      _ = ENNReal.ofReal (4 * Cs * (n₀ : ℝ))
            * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
          rw [show ((n₀ : ℕ) : ℝ) * 4 * Cs = 4 * Cs * (n₀ : ℝ) by ring]
      _ ≤ ENNReal.ofReal (4 * Cs * (n₀ : ℝ) + 1)
            * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith [hCspos.le])) zero_le
  refine hsum.trans (hAR.trans ?_)
  show ENNReal.ofReal (4 * Cs * ((Nk Λ : ℕ) : ℝ) + 1)
        * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
      ≤ (ENNReal.toNNReal (ENNReal.ofReal (4 * Cs * ((Nk Λ : ℕ) : ℝ) + 1)) : ENNReal)
        * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
  rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]

/-! ## §5.  The narrow (`core ∧ Farey`) unmodulated low-pass piece -/

/-- The clipping set `core ∧ Farey` is a tail of the index set (the `g`-side level). -/
theorem core_farey_g_tail {ρ : ℝ} {C₀ : ℕ} {Cρc : ℝ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal}
    (hamono : Monotone a)
    (h : ∃ n, core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n) :
    ∃ n₀, ∀ n, (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n) ↔ n₀ ≤ n := by
  classical
  refine ⟨Nat.find h, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact Nat.find_min h hcon hn
  · exact ⟨Work.KMTAreas.A7.core_mono hamono hn (Nat.find_spec h).1,
      Work.KMTAreas.A7.farey_mono hamono hn (Nat.find_spec h).2⟩

/-- **The `core ∧ Farey`-clipped unmodulated low-pass family is bounded**, given the (mask-free)
low-pass variational estimate `hLow` for `l₂ ≤ B`.  The clipping set is a tail of the index set, so
the estimate is transported to the shifted lacunary sequence at the cost of the factor `3` of
`variationalNorm_prependZeros_le`. -/
theorem lowpassMasked_le (P : Polynomial ℤ) (r : NNReal) (hr : 2 < r)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) (Cρc : ℝ)
    (hLow : ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ : ℕ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → l₂ ≤ B →
        ∀ f : ℤ → ℂ, (Summable fun n : ℤ => ‖f n‖ ^ 2) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
          2 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) :
    ∃ K : NNReal → NNReal,
      ∀ (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (hΛ : 1 < Λ)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (l₁ l₂ k₁ : ℕ), l₂ ≤ B → ∀ (H : ℤ → ℂ), (Summable fun n : ℤ => ‖H n‖ ^ 2) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc ρ l₂ 0 a n
            then Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) H x else 0))
          2 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨KlowF, hKlow⟩ := hLow
  refine ⟨fun Λ => ENNReal.toNNReal (ENNReal.ofReal (3 * (KlowF Λ : ℝ) + 1)), ?_⟩
  intro C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ hl₂ H hHsumm
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hmono : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    exact le_trans h3 h1.le
  set E : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc ρ l₂ 0 a n
      then Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) H x else 0 with hE
  by_cases hex : ∃ n, core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc ρ l₂ 0 a n
  · obtain ⟨n₀, hn₀⟩ :=
      core_farey_g_tail (C₀ := C₀) (Cρc := Cρc) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := 0)
        (a := a) hmono hex
    have hEqE : ∀ n x, E n x = (if n < n₀ then 0 else Tle ρ l₂
        (varphitildeN P.natDegree (Nat.floor (a ((n - n₀) + n₀))) 0) H x) := by
      intro n x
      rw [hE]
      show (if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc ρ l₂ 0 a n
        then Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) H x else 0) = _
      by_cases hn : n < n₀
      · have hnf : ¬ (core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc ρ l₂ 0 a n) :=
          fun h => absurd ((hn₀ n).mp h) (not_le.mpr hn)
        rw [if_neg hnf, if_pos hn]
      · have hle : n₀ ≤ n := le_of_not_gt hn
        have hf : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc ρ l₂ 0 a n := (hn₀ n).mpr hle
        rw [if_pos hf, if_neg hn, Nat.sub_add_cancel hle]
    have hV : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => E n x)
        ≤ 3 * PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ =>
            Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a (m + n₀))) 0) H x) := by
      intro x
      have h1 := Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le
        (r := r) hr1 n₀
        (fun m : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a (m + n₀))) 0) H x)
      have h2 : (fun n : ℕ => E n x) = (fun n : ℕ => if n < n₀ then (0 : ℂ)
          else Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a ((n - n₀) + n₀))) 0) H x) := by
        funext n
        exact hEqE n x
      rw [h2]
      exact h1
    have ha' : PointwiseErgodicTheorems.Lacunary Λ (fun m : ℕ => a (m + n₀)) := by
      intro m
      have h := ha (m + n₀)
      simpa [Nat.add_right_comm] using h
    have ha1' : ∀ m : ℕ, 1 ≤ a (m + n₀) := fun m => ha1 (m + n₀)
    have hb := hKlow (fun m : ℕ => a (m + n₀)) Λ l₂ hΛ ha' ha1' hl₂ H hHsumm
    have hb' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a (m + n₀))) 0) H x))
        2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (KlowF Λ : ℝ) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
      rw [ENNReal.coe_nnreal_eq] at hb
      exact hb
    have hle3 : MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal)
        * PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a (m + n₀))) 0) H x))
        2 MeasureTheory.Measure.count
        ≤ (3 : ENNReal) * (ENNReal.ofReal (KlowF Λ : ℝ)
            * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count) := by
      rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
        (V := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a (m + n₀))) 0) H x))
        (c := (3 : ENNReal)) (by norm_num) (by norm_num) (by norm_num)]
      exact mul_le_mul_of_nonneg_left hb' (by norm_num)
    have hmain : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => E n x)) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (3 * (KlowF Λ : ℝ)) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
      refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
        (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => E n x))
        (g := fun x : ℤ => (3 : ENNReal) * PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a (m + n₀))) 0) H x))
        hV).trans ?_
      refine hle3.trans ?_
      rw [← mul_assoc, show (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    refine hmain.trans ?_
    rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    linarith
  · have hzero : ∀ n x, E n x = 0 := by
      intro n x
      rw [hE]
      show (if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc ρ l₂ 0 a n
        then Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) H x else 0) = 0
      rw [if_neg (fun h => hex ⟨n, h⟩)]
    have h0 : PointwiseErgodicTheorems.variationalNorm r (0 : ℕ → ℂ) = 0 := by
      have h := variationalNorm_smul (r := r) hr1 (0 : ℂ) (0 : ℕ → ℂ)
      rw [zero_smul, enorm_zero, zero_mul] at h
      exact h
    have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => E n x))
        = (0 : ℤ → ENNReal) := by
      funext x
      have hfam : (fun n : ℕ => E n x) = (0 : ℕ → ℂ) := by
        funext n
        exact hzero n x
      rw [hfam, h0]
      rfl
    rw [hfun, MeasureTheory.eLpNorm_zero]
    exact bot_le

/-! ## §6.  The bounded-height `(lin-2)` estimate, conditional on the low-pass input -/

/-- The final constant comparison: `4 * (ofReal Kt * AH) ≤ c * Ag` where
`c = toNNReal (ofReal (4 * Kt * Cg + 1))` and `AH ≤ ofReal Cg * Ag`. -/
theorem const_finish {Kt Cg : ℝ} (hKt : 0 ≤ Kt) (hCgpos : 0 < Cg) {AH Ag : ENNReal}
    (hHg : AH ≤ ENNReal.ofReal Cg * Ag) :
    4 * (ENNReal.ofReal Kt * AH)
      ≤ (ENNReal.toNNReal (ENNReal.ofReal (4 * Kt * Cg + 1)) : ENNReal) * Ag := by
  have h1 : (4 : ENNReal) * (ENNReal.ofReal Kt * AH) = ENNReal.ofReal (4 * Kt) * AH := by
    rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num, ← mul_assoc,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  calc 4 * (ENNReal.ofReal Kt * AH)
      = ENNReal.ofReal (4 * Kt) * AH := h1
    _ ≤ ENNReal.ofReal (4 * Kt) * (ENNReal.ofReal Cg * Ag) :=
        mul_le_mul_of_nonneg_left hHg zero_le
    _ = ENNReal.ofReal (4 * Kt * Cg) * Ag := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * Kt)]
    _ ≤ ENNReal.ofReal (4 * Kt * Cg + 1) * Ag :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) zero_le
    _ = (ENNReal.toNNReal (ENNReal.ofReal (4 * Kt * Cg + 1)) : ENNReal) * Ag := by
        rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]

/-- **The bounded-height `g`-side linear lacunary variational estimate** (`(lin-2)` at `(2,2,1)`),
from the mask-free unmodulated low-pass estimate `hLow`. -/
theorem sliceGBound_of_lowpass (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ)
    (hLow : ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ : ℕ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → l₂ ≤ B →
        ∀ f : ℤ → ℂ, (Summable fun n : ℤ => ‖f n‖ ^ 2) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
          2 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) :
    SliceGBound P r C₀ ρ B := by
  classical
  have key : ∀ Λ : NNReal, ∃ c : NNReal,
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1/2 : ℝ) 1 → Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n x))
          2 MeasureTheory.Measure.count
          ≤ (c : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    intro Λ
    by_cases hΛ : 1 < Λ
    swap
    · exact ⟨1, fun a l₁ l₂ k₁ k₂ t g hΛ' _ _ _ _ => absurd hΛ' hΛ⟩
    obtain ⟨CρcF, hCρcF3, KF, hKFpos, hF⟩ :=
      Work.KMTAreas.A7Hi.lacunaryBumpFareyPartBoundG P P.natDegree hd le_rfl C₀ r hr ρ hρ hρ1
        Λ hΛ 2 (by norm_num) (by norm_num)
    obtain ⟨CρcD, hCρcD3, KD, hKDpos, hD⟩ :=
      Work.KMTAreas.A7Hi.lacunaryBumpFareyDiffPartBoundG P P.natDegree hd le_rfl C₀ r hr ρ hρ
        hρ1 Λ hΛ 2 (by norm_num) (by norm_num)
    obtain ⟨KbadF, hKbadF⟩ := badPart_le P ρ hρ hρ1 C₀ hC₀ CρcF hCρcF3 r hr B
    obtain ⟨KbadD, hKbadD⟩ := badPart_le P ρ hρ hρ1 C₀ hC₀ CρcD hCρcD3 r hr B
    obtain ⟨KlowM, hKlowM⟩ := lowpassMasked_le P r hr ρ hρ hρ1 B CρcD hLow
    obtain ⟨Cg, hCgpos, hCgb⟩ := mdlG_two_le P ρ B
    set A1 : ℝ := KF * (1 + (B : ℝ)) * (1 + (B : ℝ)) with hA1def
    set A2 : ℝ := KD * (1 + (B : ℝ)) with hA2def
    set A3 : ℝ := (KlowM Λ : ℝ) with hA3def
    set A4 : ℝ := (KbadF Λ : ℝ) with hA4def
    set A5 : ℝ := (KbadD Λ : ℝ) with hA5def
    have hA1 : 0 ≤ A1 := by rw [hA1def]; exact mul_nonneg (mul_nonneg hKFpos.le (by positivity)) (by positivity)
    have hA2 : 0 ≤ A2 := by rw [hA2def]; exact mul_nonneg hKDpos.le (by positivity)
    have hA3 : 0 ≤ A3 := by rw [hA3def]; exact NNReal.coe_nonneg _
    have hA4 : 0 ≤ A4 := by rw [hA4def]; exact NNReal.coe_nonneg _
    have hA5 : 0 ≤ A5 := by rw [hA5def]; exact NNReal.coe_nonneg _
    set Kt : ℝ := 1 + (A1 + A2 + (A3 + A4 + A5)) with hKtdef
    have hKt1 : (1 : ℝ) ≤ Kt := by rw [hKtdef]; linarith [hA1, hA2, hA3, hA4, hA5]
    have hKFle : A1 ≤ Kt := by rw [hKtdef]; linarith [hA1, hA2, hA3, hA4, hA5]
    have hKDle : A2 ≤ Kt := by rw [hKtdef]; linarith [hA1, hA2, hA3, hA4, hA5]
    have hKLle : A3 ≤ Kt := by rw [hKtdef]; linarith [hA1, hA2, hA3, hA4, hA5]
    have hKBle : A4 ≤ Kt := by rw [hKtdef]; linarith [hA1, hA2, hA3, hA4, hA5]
    have hKDble : A5 ≤ Kt := by rw [hKtdef]; linarith [hA1, hA2, hA3, hA4, hA5]
    have hKtCg : (0 : ℝ) < 4 * Kt * Cg + 1 := by nlinarith [hCgpos]
    refine ⟨ENNReal.toNNReal (ENNReal.ofReal (4 * Kt * Cg + 1)), ?_⟩
    intro a l₁ l₂ k₁ k₂ t g hΛ' ha ha1 ht hlc
    set H : ℤ → ℂ := Work.KMTPlan.A6.mdlG ρ P
      (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₂ g with hHdef
    have hl₂ : l₂ ≤ B := (le_of_lcL_le hlc).2.1
    have hu : Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
        ≤ Work.KMTAreas.A7.uScale ρ B := uScale_mono_g hρ.le hlc
    have hHg : MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Cg * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
      hCgb l₂ hl₂ (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) hu g
    by_cases hgtop : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
    · rw [hgtop, ENNReal.mul_top (by
        rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        linarith)]
      exact le_top
    · have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
      have h1 : ENNReal.ofReal Cg * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
          ≠ ⊤ := by
        rw [show MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
            = ENNReal.ofReal (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal
            from (ENNReal.ofReal_toReal hgtop).symm]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      have hHne : MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count ≠ ⊤ := by
        intro h
        exact h1 (top_le_iff.mp (h ▸ hHg))
      have hHsumm : Summable (fun n : ℤ => ‖H n‖ ^ 2) := by
        refine Work.KMTAreas.A4.summable_norm_sq_of_eLpNorm_le
          (A := (MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count).toReal) ?_
        rw [ENNReal.ofReal_toReal hHne]
      have hHbdd : ∃ Bh : ℝ, ∀ m : ℤ, ‖H m‖ ≤ Bh := by
        refine ⟨(∑' n : ℤ, ‖H n‖ ^ 2) ^ (1/2 : ℝ), fun m => ?_⟩
        have h1 : ‖H m‖ ^ 2 ≤ ∑' n : ℤ, ‖H n‖ ^ 2 :=
          Summable.le_tsum hHsumm m (fun n _ => by positivity)
        calc ‖H m‖ = Real.sqrt (‖H m‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (∑' n : ℤ, ‖H n‖ ^ 2) := Real.sqrt_le_sqrt h1
          _ = (∑' n : ℤ, ‖H n‖ ^ 2) ^ (1/2 : ℝ) := Real.sqrt_eq_rpow _
      rcases Nat.eq_zero_or_pos k₂ with hk₂0 | hk₂pos
      · -- ## the case `k₂ = 0`
        subst hk₂0
        set SFD : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ 0 a n
            ∧ Farey CρcD ρ l₂ 0 a n
            then Tle ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
              - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) H x else 0 with hSFD
        set SFL : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ 0 a n
            ∧ Farey CρcD ρ l₂ 0 a n
            then Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) H x else 0 with hSFL
        set SB : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ 0 a n
            ∧ ¬ Farey CρcD ρ l₂ 0 a n
            then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) H x else 0
          with hSB
        have hs : ∀ n x, sliceG ρ P C₀ a l₁ l₂ k₁ 0 t g n x
            = (if core ρ C₀ l₁ l₂ k₁ 0 a n then Tle ρ l₂
                (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) H x else 0) := by
          intro n x
          rw [show sliceG ρ P C₀ a l₁ l₂ k₁ 0 t g n
              = (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then Tle ρ l₂
                  (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t)
                  (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ
                    (Work.KMTPlan.A6.lcL l₁ l₂ k₁ 0)) l₂ g) else 0) from rfl]
          simp only [mdlCore_iff_core, ← hHdef]
          by_cases hc : core ρ C₀ l₁ l₂ k₁ 0 a n <;> simp [hc]
        have hpt : ∀ n x, sliceG ρ P C₀ a l₁ l₂ k₁ 0 t g n x = SFD n x + SFL n x + SB n x := by
          intro n x
          rw [hs n x]
          simp only [hSFD, hSFL, hSB, Pi.add_apply]
          by_cases hm : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
          · have hΦ : ((fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                  - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ)
                  + varphitildeN P.natDegree (Nat.floor (a n)) 0)
                  = varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t := by
              funext ξ
              simp only [Pi.add_apply]
              ring
            have hadd := Tle_add_of_bounded (ρ := ρ) (l := l₂)
              (φ := fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ)
              (ψ := varphitildeN P.natDegree (Nat.floor (a n)) 0)
              (adm_of_bump ((Work.KMTAreas.A7Hi.contDiff2_varphitildeNt_g P P.natDegree
                  (Nat.floor (a n)) 0 t).sub (contDiff_varphitildeN P.natDegree
                  (Nat.floor (a n)) 0))
                ((Work.KMTAreas.A7Hi.hasCompactSupport_varphitildeNt_g P P.natDegree
                  (Nat.floor (a n)) 0 t).sub (hasCompactSupport_varphitildeN P.natDegree
                  (Nat.floor (a n)) 0)))
              (adm_of_bump (contDiff_varphitildeN P.natDegree (Nat.floor (a n)) 0)
                (hasCompactSupport_varphitildeN P.natDegree (Nat.floor (a n)) 0))
              hHbdd.choose_spec
            rw [hΦ] at hadd
            rw [if_pos hm.1, if_pos hm, if_pos hm, if_neg (fun h => h.2 hm.2)]
            simp only [add_zero]
            exact congrFun hadd x
          · by_cases hc : core ρ C₀ l₁ l₂ k₁ 0 a n
            · have hF : ¬ Farey CρcD ρ l₂ 0 a n := fun h => hm ⟨hc, h⟩
              rw [if_pos hc, if_neg hm, if_neg hm, if_pos ⟨hc, hF⟩]
              simp only [zero_add, add_zero]
            · rw [if_neg hc, if_neg hm, if_neg hm, if_neg (fun h => hc h.1)]
              simp only [zero_add, add_zero]
        have hSFD_eq : SFD = fun n : ℕ => Tle ρ l₂ (fun ξ : ℝ =>
            if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
            then varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
              - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) H := by
          rw [hSFD]
          funext n
          exact (Tle_ite ρ l₂ (core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n)
            (φ := fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
              - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) (f := H)).symm
        have hbdD : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => SFD n x)) 2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
          have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => SFD n x))
              = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Tle ρ l₂ (fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
                    then varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) H x)) := by
            simp only [hSFD_eq]
          rw [heq]
          refine (hD l₂ l₁ l₂ k₁ 0 le_rfl t ht a ha ha1 H).trans ?_
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          have hl₂r : (l₂ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hl₂
          have h1 : KD * (1 + (l₂ : ℝ)) ≤ KD * (1 + (B : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith) hKDpos.le
          linarith [hKDle]
        have hbdL : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => SFL n x)) 2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
          refine (hKlowM C₀ a Λ hΛ' ha ha1 l₁ l₂ k₁ hl₂ H hHsumm).trans ?_
          rw [ENNReal.coe_nnreal_eq]
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hKLle) zero_le
        have hbdB : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => SB n x)) 2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
          refine (hKbadD a Λ hΛ' ha ha1 l₁ l₂ k₁ 0 hlc t ht H).trans ?_
          rw [ENNReal.coe_nnreal_eq]
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hKDble) zero_le
        have hVpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ 0 t g n x)
            ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SFD n x)
              + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SFL n x)
              + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SB n x) := by
          intro x
          have h1 : (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ 0 t g n x)
              = ((fun n : ℕ => SFD n x) + (fun n : ℕ => SFL n x)) + (fun n : ℕ => SB n x) := by
            funext n
            rw [hpt n x]
            simp only [Pi.add_apply]
          rw [h1]
          exact (variationalNorm_add_le hr1 _ _).trans
            (add_le_add (variationalNorm_add_le hr1 _ _) le_rfl)
        have hsum3 : MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ 0 t g n x))
            2 MeasureTheory.Measure.count
            ≤ 4 * (ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count) := by
          refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
            (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ 0 t g n x))
            (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SFD n x)
              + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SFL n x)
              + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SB n x)) hVpt).trans ?_
          refine (MeasureTheory.eLpNorm_add_le (p := 2) (μ := MeasureTheory.Measure.count)
            (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SFD n x)
              + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SFL n x))
            (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SB n x)) (by norm_num)).trans ?_
          refine (add_le_add (MeasureTheory.eLpNorm_add_le (p := 2)
              (μ := MeasureTheory.Measure.count)
              (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SFD n x))
              (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SFL n x)) (by norm_num)) le_rfl).trans ?_
          refine (add_le_add (add_le_add hbdD hbdL) hbdB).trans ?_
          have h3 : (3 : ENNReal) * (ENNReal.ofReal Kt
              * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count)
              = (ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
                  + ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count)
                + ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
            ring
          rw [← h3]
          exact mul_le_mul_of_nonneg_right (by norm_num : (3 : ENNReal) ≤ 4) zero_le
        exact hsum3.trans (const_finish (by linarith [hKt1]) hCgpos hHg)
      · -- ## the case `k₂ ≥ 1`
        set SF : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ k₂ a n
            ∧ Farey CρcF ρ l₂ k₂ a n
            then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0
          with hSF
        set SB2 : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ k₂ a n
            ∧ ¬ Farey CρcF ρ l₂ k₂ a n
            then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0
          with hSB2
        have hs : ∀ n x, sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n x
            = (if core ρ C₀ l₁ l₂ k₁ k₂ a n then Tle ρ l₂
                (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) H x else 0) := by
          intro n x
          rw [show sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n
              = (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then Tle ρ l₂
                  (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)
                  (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ
                    (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₂ g) else 0) from rfl]
          simp only [mdlCore_iff_core, ← hHdef]
          by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n <;> simp [hc]
        have hpt : ∀ n x, sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n x = SF n x + SB2 n x := by
          intro n x
          rw [hs n x]
          simp only [hSF, hSB2, Pi.add_apply]
          by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
          · by_cases hF : Farey CρcF ρ l₂ k₂ a n
            · rw [if_pos hc, if_pos ⟨hc, hF⟩, if_neg (fun h => h.2 hF)]
              simp
            · rw [if_pos hc, if_neg (fun h => hF h.2), if_pos ⟨hc, hF⟩]
              simp
          · rw [if_neg hc, if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]
            simp
        have hSF_eq : SF = fun n : ℕ => Tle ρ l₂ (fun ξ : ℝ =>
            if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
            then varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0) H := by
          rw [hSF]
          funext n
          exact (Tle_ite ρ l₂ (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n)
            (φ := fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ)
            (f := H)).symm
        have hbdF : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => SF n x)) 2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
          have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SF n x))
              = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Tle ρ l₂ (fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
                    then varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0) H x)) := by
            simp only [hSF_eq]
          rw [heq]
          refine (hF k₂ hk₂pos l₂ l₁ l₂ k₁ le_rfl t ht a ha ha1 H).trans ?_
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          have hl₂r : (l₂ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hl₂
          have hk₂r : (k₂ : ℝ) ≤ (B : ℝ) := by exact_mod_cast (le_of_lcL_le hlc).2.2.2
          have h1 : (1 + (l₂ : ℝ)) ≤ (1 + (B : ℝ)) := by linarith
          have h2 : (1 + (k₂ : ℝ)) ≤ (1 + (B : ℝ)) := by linarith
          have h3 : (0 : ℝ) ≤ 1 + (k₂ : ℝ) := by positivity
          have h4 : (0 : ℝ) ≤ 1 + (B : ℝ) := by positivity
          calc KF * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ))
              ≤ KF * (1 + (B : ℝ)) * (1 + (B : ℝ)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left h1 hKFpos.le) h2 h3
                  (mul_nonneg hKFpos.le h4)
            _ ≤ Kt := hKFle
        have hbdB2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => SB2 n x)) 2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
          refine (hKbadF a Λ hΛ' ha ha1 l₁ l₂ k₁ k₂ hlc t ht H).trans ?_
          rw [ENNReal.coe_nnreal_eq]
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hKBle) zero_le
        have hVpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)
            ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SF n x)
              + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SB2 n x) := by
          intro x
          have h1 : (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)
              = (fun n : ℕ => SF n x) + (fun n : ℕ => SB2 n x) := by
            funext n
            rw [hpt n x]
            simp only [Pi.add_apply]
          rw [h1]
          exact variationalNorm_add_le hr1 _ _
        have hsum2 : MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n x))
            2 MeasureTheory.Measure.count
            ≤ 4 * (ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count) := by
          refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
            (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n x))
            (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SF n x)
              + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SB2 n x)) hVpt).trans ?_
          refine (MeasureTheory.eLpNorm_add_le (p := 2) (μ := MeasureTheory.Measure.count)
            (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SF n x))
            (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => SB2 n x)) (by norm_num)).trans ?_
          refine (add_le_add hbdF hbdB2).trans ?_
          have h2 : (2 : ENNReal) * (ENNReal.ofReal Kt
              * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count)
              = ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
                + ENNReal.ofReal Kt * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count := by
            ring
          rw [← h2]
          exact mul_le_mul_of_nonneg_right (by norm_num : (2 : ENNReal) ≤ 4) zero_le
        exact hsum2.trans (const_finish (by linarith [hKt1]) hCgpos hHg)
  choose c hc using key
  exact ⟨c, fun a Λ l₁ l₂ k₁ k₂ t g hΛ ha ha1 ht hlc =>
    hc Λ a l₁ l₂ k₁ k₂ t g hΛ ha ha1 ht hlc⟩

/-! ## §7.  The `k₂ = 0` unmodulated low-pass family at bounded height

The family `n ↦ Tle ρ l₂ (varphitildeN d ⌊a n⌋ 0) f = kmtProj ρ l₂ (-(d·logN ⌊a n⌋)) f` is
estimated by the *sieve* route: the dyadic walk `m ↦ lpf ρ l₂ m₀ m f = kmtProj ρ l₂ (-(m₀+m)) f`
satisfies the (unconditional, proved) sieve bound
`Work.KMTAreas.A7Hi2.eLpNorm_variationalNorm_lpf_le_sieveMass_uncond`, and the lacunary family is
the *monotone reindexing* of that walk by `n ↦ d·logN ⌊a n⌋ - m₀` on the tail where the level
`d·logN ⌊a n⌋` has passed the base level `m₀`.  The complementary initial segment (where
`d·logN ⌊a n⌋ < m₀`, so that only the finitely many levels `-(m₀-1), …, 0` occur) is controlled by
the single-scale `ℓ²` bounds.

Both pieces are uniform in the lacunary family `a`; only the *length* of the initial segment
depends on `Λ`, which is exactly the `K Λ` of the target. -/

/-- `n ≤ 2 ^ n`. -/
private lemma self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      rw [h2]
      have h3 : 0 < 2 ^ k := pow_pos (by norm_num) k
      omega

/-- **The `iwDivs` bound.**  At bounded height `l₂ ≤ B` all sieve divisors are dominated by a
single power of two depending only on `ρ` and `B`. -/
theorem iwDivs_le_pow_two_g (ρ : ℝ) (B : ℕ) :
    ∃ m₀ : ℕ, ∀ l₂ : ℕ, l₂ ≤ B → ∀ d : ℕ, d ∈ Work.A7Hi2.iwDivs ρ l₂ → d ≤ 2 ^ m₀ := by
  classical
  refine ⟨max 1 ((Finset.range (B + 1)).sup fun l₂ => (Work.A7Hi2.iwDivs ρ l₂).sup id), ?_⟩
  intro l₂ hl₂ d hd
  have h1 : d ≤ (Work.A7Hi2.iwDivs ρ l₂).sup id := Finset.le_sup (f := id) hd
  have h2 : (Work.A7Hi2.iwDivs ρ l₂).sup id
      ≤ (Finset.range (B + 1)).sup fun l₂ => (Work.A7Hi2.iwDivs ρ l₂).sup id :=
    Finset.le_sup (f := fun l₂ => (Work.A7Hi2.iwDivs ρ l₂).sup id)
      (Finset.mem_range.mpr (by omega))
  have h3 : (Finset.range (B + 1)).sup (fun l₂ => (Work.A7Hi2.iwDivs ρ l₂).sup id)
      ≤ max 1 ((Finset.range (B + 1)).sup fun l₂ => (Work.A7Hi2.iwDivs ρ l₂).sup id) :=
    le_max_right _ _
  exact (le_trans (le_trans h1 h2) h3).trans (self_le_two_pow _)

/-- **The head (initial-segment) bound.**  The indices `n < n₁` of a lacunary family whose level
`d·logN ⌊a n⌋` is still below the base level `m₀` contribute at most a constant (depending on the
finitely many levels `-(m₀-1), …, 0` and on `n₀`, an a priori bound for `n₁`) times `‖f‖₂`,
uniformly in the family. -/
theorem head_lowpass_bound (ρ : ℝ) (l₂ d m₀ n₀ : ℕ) (r : NNReal) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (n₁ : ℕ), n₁ ≤ n₀ →
      (∀ n : ℕ, n < n₁ → (d : ℤ) * logN (Nat.floor (a n)) < (m₀ : ℤ)) →
      ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if n < n₁ then Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f x else 0))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  choose c hc using fun k : ℕ => Work.KMTAreas.A7Hi.eLpNorm_kmtProj_two_le ρ l₂ (-((k : ℤ)))
  set S : ℝ := (∑ k ∈ Finset.range m₀, c k) + 1 with hS
  have hSpos : 0 < S := by
    rw [hS]
    have h0 : 0 ≤ ∑ k ∈ Finset.range m₀, c k := Finset.sum_nonneg (fun k _ => (hc k).1)
    linarith
  refine ⟨4 * ((n₀ : ℝ) + 1) * S, ?_, ?_⟩
  · have h1 : (0 : ℝ) < (n₀ : ℝ) + 1 := by positivity
    exact mul_pos (mul_pos (by norm_num) h1) hSpos
  intro a n₁ hn₁ hlev f
  set u : ℕ → ℤ → ℂ := fun n x =>
    if n < n₁ then Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f x else 0 with hu
  have hsupp : ∀ n, n ∉ Finset.range n₁ → u n = 0 := by
    intro n hn
    have hn' : n₁ ≤ n := by simpa [Finset.mem_range, not_lt] using hn
    funext x
    rw [hu]
    show (if n < n₁ then Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f x else 0) = (0 : ℂ)
    rw [if_neg (not_lt.mpr hn')]
  have hterm : ∀ n ∈ Finset.range n₁, MeasureTheory.eLpNorm (u n) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal S * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    intro n hn
    have hnlt : n < n₁ := Finset.mem_range.mp hn
    have hk0 : (0 : ℤ) ≤ (d : ℤ) * logN (Nat.floor (a n)) := by
      have hlog : (0 : ℤ) ≤ logN (Nat.floor (a n)) := by
        simp only [Work.Analysis.EndVar.logN]
        exact Int.natCast_nonneg _
      exact mul_nonneg (Int.natCast_nonneg d) hlog
    have hklt : (d : ℤ) * logN (Nat.floor (a n)) < (m₀ : ℤ) := hlev n hnlt
    have hcast : (((((d : ℤ) * logN (Nat.floor (a n))).toNat : ℕ)) : ℤ)
        = (d : ℤ) * logN (Nat.floor (a n)) := Int.toNat_of_nonneg hk0
    have hmem : (((d : ℤ) * logN (Nat.floor (a n))).toNat : ℕ) ∈ Finset.range m₀ := by
      rw [Finset.mem_range]
      have h5 : (((((d : ℤ) * logN (Nat.floor (a n))).toNat : ℕ)) : ℤ) < (m₀ : ℤ) := by
        rw [hcast]; exact hklt
      exact_mod_cast h5
    have hfun : u n = Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f := by
      funext x
      rw [hu]
      exact if_pos hnlt
    rw [hfun, Work.KMTAreas.A7Hi2.Tle_varphitildeN_zero]
    have hlev' : -((d : ℤ) * logN (Nat.floor (a n)))
        = -(((((d : ℤ) * logN (Nat.floor (a n))).toNat : ℕ)) : ℤ) := by rw [hcast]
    rw [hlev']
    refine ((hc (((d : ℤ) * logN (Nat.floor (a n))).toNat)).2 f).trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    have h1 := Finset.single_le_sum (f := c) (fun k _ => (hc k).1) hmem
    rw [hS]
    linarith
  have hsum := eLpNorm_variationalNorm_le_sum (r := r) hr (p := 2) (by norm_num)
    (μ := MeasureTheory.Measure.count) (u := u) (s := Finset.range n₁) hsupp
    (fun n _ => (measurable_of_countable (u n)).aestronglyMeasurable)
  refine hsum.trans ?_
  have hstep : (∑ n ∈ Finset.range n₁, 4 * MeasureTheory.eLpNorm (u n) 2 MeasureTheory.Measure.count)
      ≤ (n₁ : ENNReal) * (4 * (ENNReal.ofReal S
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)) := by
    refine (Finset.sum_le_sum (fun n hn => mul_le_mul' le_rfl (hterm n hn))).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn₁cast : (n₁ : ENNReal) ≤ (n₀ : ENNReal) := by exact_mod_cast hn₁
  refine hstep.trans ?_
  refine (mul_le_mul_of_nonneg_right hn₁cast zero_le).trans ?_
  calc (n₀ : ENNReal) * (4 * (ENNReal.ofReal S
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count))
      = (n₀ : ENNReal) * 4 * ENNReal.ofReal S
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by ring
    _ = ENNReal.ofReal ((n₀ : ℝ) * 4 * S)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        rw [show ((n₀ : ℕ) : ENNReal) = ENNReal.ofReal ((n₀ : ℕ) : ℝ) by
              exact (ENNReal.ofReal_natCast n₀).symm,
            show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num,
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((n₀ : ℕ) : ℝ)),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((n₀ : ℕ) : ℝ) * 4)]
    _ = ENNReal.ofReal (4 * (n₀ : ℝ) * S)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        rw [show ((n₀ : ℕ) : ℝ) * 4 * S = 4 * (n₀ : ℝ) * S by ring]
    _ ≤ ENNReal.ofReal (4 * ((n₀ : ℝ) + 1) * S)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        have hn0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
        have hSnn : 0 ≤ S := le_of_lt hSpos
        nlinarith [hn0, hSnn]

/-- **The tail bound.**  Once the level `d·logN ⌊a n⌋` has passed the base level `m₀`, the
lacunary family is the monotone reindexing of the dyadic walk `m ↦ lpf ρ l₂ m₀ m f`, whose
variational norm is bounded by the sieve constant `C · sieveMass ρ l₂`; the padding of the initial
segment costs the factor `2`. -/
theorem tail_lowpass_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (l₂ d m₀ : ℕ)
    (hlarge : ∀ d' ∈ Work.A7Hi2.iwDivs ρ l₂, Work.A7Hi2.sieveCoeff ρ l₂ d' ≠ 0 →
      d' ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (n₁ : ℕ)
      (hmono : Monotone fun n : ℕ => (d : ℤ) * logN (Nat.floor (a n)))
      (hn₁ : (m₀ : ℤ) ≤ (d : ℤ) * logN (Nat.floor (a n₁)))
      (f : ℤ → ℂ), (Summable fun n : ℤ => ‖f n‖ ^ 2) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if n < n₁ then 0 else Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f x))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨Cs, hCspos, hCs⟩ :=
    Work.KMTPlan.A6.PieceLocal.eLpNorm_variationalNorm_lpf_le_sieveMass_local
    ρ hρ hρ1 r hr 2 (by norm_num) l₂ m₀ hlarge
  have hMnn : 0 ≤ Work.A7Hi2.sieveMass ρ l₂ := Finset.sum_nonneg fun d _ => abs_nonneg _
  refine ⟨2 * Cs * (Work.A7Hi2.sieveMass ρ l₂ + 1), by positivity, ?_⟩
  intro a n₁ hmono hn₁ f hf
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hf2 : Summable fun n : ℤ => ‖f n‖ ^ (2 : ℝ) := by
    simpa [Real.rpow_two, pow_two] using hf
  set σ : ℕ → ℕ := fun n => (((d : ℤ) * logN (Nat.floor (a n))) - (m₀ : ℤ)).toNat with hσdef
  have hσcoe : ∀ n : ℕ, n₁ ≤ n → ((σ n : ℕ) : ℤ)
      = (d : ℤ) * logN (Nat.floor (a n)) - (m₀ : ℤ) := by
    intro n hn
    have h1 : (d : ℤ) * logN (Nat.floor (a n₁)) ≤ (d : ℤ) * logN (Nat.floor (a n)) :=
      hmono hn
    rw [hσdef]
    exact Int.toNat_of_nonneg (by omega)
  have hσmono : Monotone σ := by
    intro m n hmn
    have h1 : (d : ℤ) * logN (Nat.floor (a m)) ≤ (d : ℤ) * logN (Nat.floor (a n)) :=
      hmono hmn
    rw [hσdef]
    show (((d : ℤ) * logN (Nat.floor (a m))) - (m₀ : ℤ)).toNat
      ≤ (((d : ℤ) * logN (Nat.floor (a n))) - (m₀ : ℤ)).toNat
    omega
  have hmonoσ : Monotone fun k : ℕ => σ (k + n₁) :=
    fun m k hmk => hσmono (Nat.add_le_add_right hmk n₁)
  set z : ℕ → ℤ → ℂ := fun k x => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ (σ (k + n₁)) f x with hzdef
  have hpoint : ∀ n x, (if n < n₁ then (0 : ℂ)
        else Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f x)
      = (if n < n₁ then 0 else z (n - n₁) x) := by
    intro n x
    by_cases hn : n < n₁
    · rw [if_pos hn, if_pos hn]
    · have hle : n₁ ≤ n := le_of_not_gt hn
      rw [if_neg hn, if_neg hn]
      rw [hzdef]
      show Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f x
        = Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ (σ ((n - n₁) + n₁)) f x
      unfold Work.KMTAreas.A7Hi.lpf
      rw [Nat.sub_add_cancel hle, Work.KMTAreas.A7Hi2.Tle_varphitildeN_zero]
      have harg : -(((m₀ : ℤ) + ((σ n : ℕ) : ℤ))) = -((d : ℤ) * logN (Nat.floor (a n))) := by
        rw [hσcoe n hle]; ring
      rw [harg]
  have hV : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if n < n₁ then 0 else Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f x)
      ≤ 2 * PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x) := by
    intro x
    have h1 : (fun n : ℕ => if n < n₁ then (0 : ℂ)
          else Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f x)
        = (fun n : ℕ => if n < n₁ then 0 else z (n - n₁) x) := funext fun n => hpoint n x
    rw [h1]
    refine (variationalNorm_prefix_zero_le (r := r) hr1 (fun k => z k x) n₁).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have h2 : (fun k : ℕ => z k x)
        = (fun k : ℕ => (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x) (σ (k + n₁))) := by
      funext k
      rw [hzdef]
    rw [h2]
    exact Work.KMTAreas.A7.variationalNorm_comp_mono_le (r := r)
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x) hmonoσ
  have hbase : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x)) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Cs * Work.A7Hi2.sieveMass ρ l₂)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    have h := hCs f hf2
    simpa using h
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if n < n₁ then 0 else Tle ρ l₂ (varphitildeN d (Nat.floor (a n)) 0) f x))
    (g := fun x : ℤ => 2 * PointwiseErgodicTheorems.variationalNorm r
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x)) hV).trans ?_
  rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
    (V := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x))
    (c := (2 : ENNReal)) (by norm_num) (by norm_num) (by norm_num)]
  refine (mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ENNReal) ≤ 2)).trans ?_
  calc (2 : ENNReal) * (ENNReal.ofReal (Cs * Work.A7Hi2.sieveMass ρ l₂)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
      = (2 : ENNReal) * ENNReal.ofReal (Cs * Work.A7Hi2.sieveMass ρ l₂)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by ring
    _ = ENNReal.ofReal (2 * (Cs * Work.A7Hi2.sieveMass ρ l₂))
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ ENNReal.ofReal (2 * Cs * (Work.A7Hi2.sieveMass ρ l₂ + 1))
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        nlinarith [hCspos.le, hMnn]

/-- **The unmodulated low-pass `g`-side family at bounded height** — the input `hLow` of
`sliceGBound_of_lowpass`, from the eventual-domination bound `hHead` for `Λ`-lacunary families.
The head/tail split of the lacunary family at the base level `m₀` (`m₀` from
`iwDivs_le_pow_two_g`) is where the `Λ`-dependence of the constant enters, through the length
`n₁` of the head. -/
theorem lowpassBoundedHeight_of_head
    (hHead : ∀ (Λ : NNReal), 1 < Λ → ∀ (m₀ d : ℕ), 1 ≤ d →
      ∃ n₀ : ℕ, ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        ∀ n : ℕ, n₀ ≤ n → (m₀ : ℤ) ≤ (d : ℤ) * logN (Nat.floor (a n)))
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ : ℕ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → l₂ ≤ B →
        ∀ f : ℤ → ℂ, (Summable fun n : ℤ => ‖f n‖ ^ 2) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
          2 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hd1 : 1 ≤ P.natDegree := by omega
  obtain ⟨m₀, hm₀⟩ := iwDivs_le_pow_two_g ρ B
  have key : ∀ Λ : NNReal, ∃ c : NNReal,
      ∀ (a : ℕ → NNReal) (l₂ : ℕ), l₂ ≤ B → 1 < Λ →
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        ∀ f : ℤ → ℂ, (Summable fun n : ℤ => ‖f n‖ ^ 2) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
          2 MeasureTheory.Measure.count
        ≤ (c : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    intro Λ
    by_cases hΛ : 1 < Λ
    swap
    · exact ⟨1, fun a l₂ hl₂ hΛ' _ _ f _ => absurd hΛ' hΛ⟩
    obtain ⟨n₀, hn₀⟩ := hHead Λ hΛ m₀ P.natDegree hd1
    choose ch hch using fun l₂ : ℕ => head_lowpass_bound ρ l₂ P.natDegree m₀ n₀ r hr1
    have htail_ex : ∀ l₂ : ℕ, ∃ C : ℝ, 0 < C ∧ (l₂ ≤ B →
        ∀ (a : ℕ → NNReal) (n₁ : ℕ)
          (hmono : Monotone fun n : ℕ => (P.natDegree : ℤ) * logN (Nat.floor (a n)))
          (hn₁ : (m₀ : ℤ) ≤ (P.natDegree : ℤ) * logN (Nat.floor (a n₁)))
          (f : ℤ → ℂ), (Summable fun n : ℤ => ‖f n‖ ^ 2) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if n < n₁ then 0
                else Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
            2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) := by
      intro l₂
      by_cases hl₂ : l₂ ≤ B
      · obtain ⟨C, hCpos, hCb⟩ := tail_lowpass_bound ρ hρ hρ1 r hr l₂ P.natDegree m₀
          (fun d' hd' _ => by
            have h := hm₀ l₂ hl₂ d' hd'
            simpa [Work.KMTAreas.A7Hi.lpfScale] using h)
        exact ⟨C, hCpos, fun _ => hCb⟩
      · exact ⟨1, one_pos, fun h => absurd h hl₂⟩
    choose ct hct using htail_ex
    refine ⟨ENNReal.toNNReal (ENNReal.ofReal
      (∑ j ∈ Finset.range (B + 1), (ch j + ct j + 1))), ?_⟩
    intro a l₂ hl₂ _ ha ha1 f hf
    have hmono_a : Monotone a := by
      refine monotone_nat_of_le_succ (fun n => ?_)
      have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
      have h2 : Λ < a (n + 1) / a n := ha n
      have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
      have h3 : a n ≤ Λ * a n := by
        simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
      exact le_trans h3 h1.le
    have hκmono : Monotone fun n : ℕ => (P.natDegree : ℤ) * logN (Nat.floor (a n)) := by
      intro m n hmn
      have h1 : Nat.floor (a m) ≤ Nat.floor (a n) := Nat.floor_mono (hmono_a hmn)
      have h2 : logN (Nat.floor (a m)) ≤ logN (Nat.floor (a n)) :=
        Work.Analysis.EndVar.logN_mono h1
      exact mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg _)
    have hex : ∃ n : ℕ, (m₀ : ℤ) ≤ (P.natDegree : ℤ) * logN (Nat.floor (a n)) :=
      ⟨n₀, hn₀ a ha ha1 n₀ le_rfl⟩
    set n₁ : ℕ := Nat.find hex with hn₁def
    have hn₁spec : (m₀ : ℤ) ≤ (P.natDegree : ℤ) * logN (Nat.floor (a n₁)) := by
      rw [hn₁def]; exact Nat.find_spec hex
    have hn₁le : n₁ ≤ n₀ := by
      rw [hn₁def]; exact Nat.find_min' hex (hn₀ a ha ha1 n₀ le_rfl)
    have hheadlev : ∀ n : ℕ, n < n₁ →
        (P.natDegree : ℤ) * logN (Nat.floor (a n)) < (m₀ : ℤ) := by
      intro n hn
      rw [hn₁def] at hn
      exact not_le.mp (Nat.find_min hex hn)
    have hsplit : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x)
        ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if n < n₁ then
              Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0)
          + PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if n < n₁ then 0 else
              Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x) := by
      intro x
      have hsum_eq : (fun n : ℕ => if n < n₁ then
              Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0)
            + (fun n : ℕ => if n < n₁ then 0 else
              Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x)
          = fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x := by
        funext n
        simp only [Pi.add_apply]
        by_cases hn : n < n₁ <;> simp [hn]
      rw [← hsum_eq]
      exact variationalNorm_add_le hr1 _ _
    have hheadb := (hch l₂).2 a n₁ hn₁le hheadlev f
    have htailb := (hct l₂).2 hl₂ a n₁ hκmono hn₁spec f hf
    refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
      (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
      (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if n < n₁ then
            Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0)
        + PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if n < n₁ then 0 else
            Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x)) hsplit).trans ?_
    refine (MeasureTheory.eLpNorm_add_le (p := 2) (μ := MeasureTheory.Measure.count)
      (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if n < n₁ then
          Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0))
      (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if n < n₁ then 0 else
          Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x)) (by norm_num)).trans ?_
    refine (add_le_add hheadb htailb).trans ?_
    have hsum_ge : ch l₂ + ct l₂
        ≤ ∑ j ∈ Finset.range (B + 1), (ch j + ct j + 1) := by
      have h0 : ∀ j ∈ Finset.range (B + 1), (0 : ℝ) ≤ ch j + ct j + 1 := by
        intro j _
        have h1 := (hch j).1
        have h2 := (hct j).1
        linarith
      have hmem : l₂ ∈ Finset.range (B + 1) := by
        rw [Finset.mem_range]; omega
      have h := Finset.single_le_sum (f := fun j => ch j + ct j + 1) h0 hmem
      linarith
    have hconst : ENNReal.ofReal (ch l₂)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          + ENNReal.ofReal (ct l₂)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (∑ j ∈ Finset.range (B + 1), (ch j + ct j + 1))
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
      rw [← add_mul, ← ENNReal.ofReal_add (le_of_lt (hch l₂).1) (le_of_lt (hct l₂).1)]
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hsum_ge) zero_le
    refine hconst.trans ?_
    show ENNReal.ofReal (∑ j ∈ Finset.range (B + 1), (ch j + ct j + 1))
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
      ≤ (ENNReal.toNNReal (ENNReal.ofReal
          (∑ j ∈ Finset.range (B + 1), (ch j + ct j + 1))) : ENNReal)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
    rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
  choose c hc using key
  exact ⟨c, fun a Λ l₂ hΛ ha ha1 hl₂ f hf => hc Λ a l₂ hl₂ hΛ ha ha1 f hf⟩

/-- **The eventual domination of the level of a `Λ`-lacunary family** (`Λ > 1`): for `d ≥ 1` the
level `d·logN ⌊a n⌋` eventually dominates any prescribed `m₀`, uniformly in the family `a`. -/
theorem lacunaryHeadBound_g (Λ : NNReal) (hΛ : 1 < Λ) (m₀ d : ℕ) (hd : 1 ≤ d) :
    ∃ n₀ : ℕ, ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∀ n : ℕ, n₀ ≤ n → (m₀ : ℤ) ≤ (d : ℤ) * logN (Nat.floor (a n)) := by
  classical
  have hpow : ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∀ n : ℕ, Λ ^ n ≤ a n := by
    intro a ha ha1 n
    induction n with
    | zero => simpa using ha1 0
    | succ k ih =>
        have hpos : (0 : NNReal) < a k := lt_of_lt_of_le zero_lt_one (ha1 k)
        have h2 : Λ < a (k + 1) / a k := ha k
        have h1 : Λ * a k < a (k + 1) := by rwa [lt_div_iff₀ hpos] at h2
        calc Λ ^ (k + 1) = Λ * Λ ^ k := by rw [pow_succ]; ring
          _ ≤ Λ * a k := mul_le_mul_of_nonneg_left ih (by positivity : (0 : NNReal) ≤ Λ)
          _ ≤ a (k + 1) := le_of_lt h1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (2 : NNReal) ≤ Λ ^ N := by
    have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have h : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ (Λ : ℝ) ^ n :=
      (tendsto_pow_atTop_atTop_of_one_lt hΛR).eventually (eventually_ge_atTop 2)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
    refine ⟨N, ?_⟩
    rw [← NNReal.coe_le_coe]
    rw [show ((2 : NNReal) : ℝ) = 2 by norm_num, NNReal.coe_pow]
    exact hN N le_rfl
  refine ⟨N * (m₀ + 1), fun a ha ha1 n hn => ?_⟩
  have hgrow : Λ ^ (N * (m₀ + 1)) ≤ a n :=
    (pow_le_pow_right₀ (le_of_lt hΛ) hn).trans (hpow a ha ha1 n)
  have hbig : (2 : NNReal) ^ (m₀ + 1) ≤ a n := by
    refine (pow_le_pow_left₀ (by positivity : (0 : NNReal) ≤ 2) hN (m₀ + 1)).trans ?_
    rw [← pow_mul]
    exact hgrow
  have hfloor : 2 ^ (m₀ + 1) ≤ Nat.floor (a n) := by
    have h1 : ((2 ^ (m₀ + 1) : ℕ) : NNReal) ≤ a n := by
      simpa [Nat.cast_pow] using hbig
    exact Nat.le_floor h1
  have hlog : ((m₀ + 1 : ℕ) : ℤ) ≤ logN (Nat.floor (a n)) := by
    have h1 : m₀ + 1 ≤ Nat.log 2 (Nat.floor (a n)) :=
      Nat.le_log_of_pow_le (by norm_num) hfloor
    have h2 : Nat.log 2 (Nat.floor (a n)) ≤ Nat.log 2 (max (Nat.floor (a n)) 2) :=
      Nat.log_mono_right (le_max_left _ _)
    show ((m₀ + 1 : ℕ) : ℤ) ≤ ((Nat.log 2 (max (Nat.floor (a n)) 2) : ℕ) : ℤ)
    exact_mod_cast le_trans h1 h2
  have hmul : ((m₀ + 1 : ℕ) : ℤ) ≤ (d : ℤ) * logN (Nat.floor (a n)) := by
    have hLnn : (0 : ℤ) ≤ logN (Nat.floor (a n)) := le_trans (Int.natCast_nonneg _) hlog
    have hd1' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    calc ((m₀ + 1 : ℕ) : ℤ) ≤ logN (Nat.floor (a n)) := hlog
      _ = (1 : ℤ) * logN (Nat.floor (a n)) := by ring
      _ ≤ (d : ℤ) * logN (Nat.floor (a n)) := mul_le_mul_of_nonneg_right hd1' hLnn
  exact le_trans (by omega : (m₀ : ℤ) ≤ ((m₀ + 1 : ℕ) : ℤ)) hmul

/-- The unmodulated low-pass `g`-side estimate at bounded height, from the head bound
`lacunaryHeadBound_g` — the `hLow` input of `sliceGBound_of_lowpass`. -/
theorem lowpassBoundedHeightAux (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ : ℕ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → l₂ ≤ B →
        ∀ f : ℤ → ℂ, (Summable fun n : ℤ => ‖f n‖ ^ 2) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
          2 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
  lowpassBoundedHeight_of_head lacunaryHeadBound_g P hd r hr ρ hρ hρ1 B

theorem sliceGBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) : Work.KMTPlan.A6.PieceBoundedH.SliceGBound P r C₀ ρ B := by
  exact sliceGBound_of_lowpass P hd r hr C₀ hC₀ ρ hρ hρ1 B
    (lowpassBoundedHeightAux P hd r hr ρ hρ hρ1 B)

end

end Work.KMTPlan.A6.PieceLocal
