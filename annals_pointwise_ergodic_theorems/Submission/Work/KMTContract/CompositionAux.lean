/-
# Auxiliaries for the composition `exists_varEstHalfFin_Cv_of_areas`

This module contains the parts of the composition of `ROUTE_LEAD.md` §3.2 that can be developed
independently of the two deep inputs still in flight (`kmtKernel_decay`,
`kmtProj_tendsto_truncZ`, `varpCol_finsupp_bilinear`):

* the passage from `P.degree ≥ 2` to `P.natDegree ≥ 2` and the degrees of `P - X`, `X - P`;
* the `ℝ≥0∞`/`ℝ` bookkeeping for the exponents of the interpolation;
* **`varpStatementΛ_of_pieceBounds`** — the interpolation step: given the two weighted
  paraproduct bounds of the areas A6 (`(2,2,1)`, gain) and A7 (auxiliary exponents, loss) and the
  bilinear interpolation lemma `VarBilinInterp` (A8), produce Theorem `varp` with the canonical
  gain (`VarpStatementΛ`).  The bilinearity and truncation-continuity of the columns `varpCol`
  are hypotheses here, supplied later by `varpCol_finsupp_bilinear` and
  `varpCol_tendsto_truncZ`.
-/
import Submission.Work.KMTContract.Areas
import Submission.Work.KMTContract.interpWeight_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTContract

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.Analysis.InverseTheory
open Work.Analysis.Paraproduct (IWProjections)

/-! ## Degrees -/

lemma two_le_natDegree_of_degree {P : Polynomial ℤ} (hd : P.degree ≥ 2) : 2 ≤ P.natDegree := by
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.degree_zero] at hd
    exact absurd hd (by simp)
  rw [Polynomial.degree_eq_natDegree hP0] at hd
  exact_mod_cast hd

lemma natDegree_P_sub_X {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) :
    (P - X).natDegree = P.natDegree := by
  have h1 : (X : Polynomial ℤ).natDegree < P.natDegree := by
    rw [Polynomial.natDegree_X]; omega
  exact Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1

lemma natDegree_X_sub_P {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) :
    (X - P).natDegree = P.natDegree := by
  have h1 : (X : Polynomial ℤ).natDegree < P.natDegree := by
    rw [Polynomial.natDegree_X]; omega
  exact Polynomial.natDegree_sub_eq_right_of_natDegree_lt h1

/-! ## `ℝ≥0∞` bookkeeping -/

/-- `ENNReal.ofReal` is multiplicative against a coefficient. -/
lemma coe_mul_ofReal_eq (C : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) :
    (C : ℝ≥0∞) * ENNReal.ofReal r = ((C * r.toNNReal : ℝ≥0) : ℝ≥0∞) := by
  have h1 : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [ENNReal.ofReal_eq_coe_nnreal hr, Real.toNNReal_of_nonneg hr]
  rw [← h1, ENNReal.coe_mul]

/-- The coercion of `Real.toNNReal` of a non-negative real. -/
lemma coe_toNNReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ((r.toNNReal : ℝ≥0) : ℝ) = r := by
  rw [Real.coe_toNNReal', max_eq_left hr]

/-- The inverse of an infinite-free `ℝ≥0∞` is `ofReal` of the inverse of its `toReal`. -/
lemma inv_eq_ofReal_inv_toReal {p : ℝ≥0∞} (hp : p ≠ 0) :
    p⁻¹ = ENNReal.ofReal (p.toReal)⁻¹ := by
  rw [← ENNReal.toReal_inv]
  exact (ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hp)).symm

/-- For `1 < p < ∞`, the real exponent `(p.toReal)⁻¹` lies in `(0,1)`. -/
lemma toReal_inv_pos_lt_one {p : ℝ≥0∞} (h1 : 1 < p) (h2 : p < ⊤) :
    0 < (p.toReal)⁻¹ ∧ (p.toReal)⁻¹ < 1 := by
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one h1).ne'
  have hpt : 0 < p.toReal := ENNReal.toReal_pos hp0 h2.ne
  have h1' : 1 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (ENNReal.one_ne_top) h2.ne).mpr h1
    simpa using this
  exact ⟨inv_pos.mpr hpt, by
    have h := mul_lt_mul_of_pos_left h1' (inv_pos.mpr hpt)
    rwa [mul_one, inv_mul_cancel₀ hpt.ne'] at h⟩

/-- `ofReal x⁻¹` is `> 1` when `0 < x < 1`. -/
lemma one_lt_ofReal_inv {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 < ENNReal.ofReal x⁻¹ := by
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff').mpr ⟨(one_lt_inv₀ hx0).mpr hx1, inv_pos.mpr hx0⟩

/-- `(ofReal x⁻¹)⁻¹ = ofReal x`. -/
lemma inv_ofReal_inv {x : ℝ} (hx : 0 < x) : (ENNReal.ofReal x⁻¹)⁻¹ = ENNReal.ofReal x := by
  rw [inv_eq_ofReal_inv_toReal
    (by positivity : ENNReal.ofReal x⁻¹ ≠ 0)]
  rw [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hx)), inv_inv]

/-- `(p₁.toReal)⁻¹ + (p₂.toReal)⁻¹ ≤ 1` from `p₁⁻¹ + p₂⁻¹ ≤ 1`. -/
lemma toReal_inv_add_le_one {p₁ p₂ : ℝ≥0∞} (h1 : 1 < p₁) (h2p : p₁ < ⊤) (h3 : 1 < p₂)
    (h4p : p₂ < ⊤) (hH : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    (p₁.toReal)⁻¹ + (p₂.toReal)⁻¹ ≤ 1 := by
  have h1' : (p₁.toReal)⁻¹ = (p₁⁻¹).toReal := (ENNReal.toReal_inv p₁).symm
  have h2' : (p₂.toReal)⁻¹ = (p₂⁻¹).toReal := (ENNReal.toReal_inv p₂).symm
  have hf1 : p₁⁻¹ ≠ ⊤ := (ENNReal.inv_ne_top).mpr (lt_trans one_pos h1).ne'
  have hf2 : p₂⁻¹ ≠ ⊤ := (ENNReal.inv_ne_top).mpr (lt_trans one_pos h3).ne'
  rw [h1', h2', ← ENNReal.toReal_add hf1 hf2]
  calc (p₁⁻¹ + p₂⁻¹).toReal ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hH
    _ = 1 := ENNReal.toReal_one

/-- If `(p.toReal)⁻¹ = 1/2` then `p = 2`. -/
lemma inv_toReal_eq_half {p : ℝ≥0∞} (hp : p < ⊤) (h : (p.toReal)⁻¹ = 1 / 2) : p = 2 := by
  have hpt : p.toReal = 2 := by
    have := congrArg (fun t : ℝ => t⁻¹) h
    rwa [inv_inv, show (1 / 2 : ℝ)⁻¹ = 2 by norm_num] at this
  calc p = ENNReal.ofReal p.toReal := (ENNReal.ofReal_toReal hp.ne).symm
    _ = ENNReal.ofReal 2 := by rw [hpt]
    _ = 2 := by norm_num

/-- `ofReal z⁻¹ = 2` iff `z = 1/2`. -/
lemma ofReal_inv_eq_two_iff {z : ℝ} (hz : 0 < z) : ENNReal.ofReal z⁻¹ = 2 ↔ z = 1 / 2 := by
  constructor
  · intro h
    have h1 : (z⁻¹ : ℝ) = 2 := by
      have := congrArg ENNReal.toReal h
      rw [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hz))] at this
      simpa using this
    have h2 : z = (2 : ℝ)⁻¹ := inv_eq_iff_eq_inv.mp h1
    rwa [show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num] at h2
  · intro h
    rw [h, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num]
    norm_num

/-- The perturbation `z ↦ z + ε(z - 1/2)` preserves the value `1/2` (`ε > 0`). -/
lemma perturb_eq_half_iff {z ε : ℝ} (hε : 0 < ε) : z + ε * (z - 1 / 2) = 1 / 2 ↔ z = 1 / 2 := by
  constructor
  · intro h
    have h' : (z - 1 / 2) * (1 + ε) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp h' with h'' | h''
    · linarith
    · exact absurd h'' (by linarith)
  · intro h
    rw [h]; ring

/-! ## The interpolation step -/

/-- **The interpolation step of the composition.**  Given

* the bilinear interpolation lemma `VarBilinInterp` (area A8),
* the bilinearity and truncation-continuity of the §5 columns `varpCol` (the technical
  hypotheses, supplied later by `varpCol_finsupp_bilinear` / `varpCol_tendsto_truncZ`),
* the two weighted paraproduct bounds of areas A6 (`(2,2,1)`, gain `2^{-cL}`) and A7
  (`(a₁,b₁,q₁)`, loss `2^{AρL}`), with `q₁ = (a₁⁻¹+b₁⁻¹)⁻¹`,
* the exponent data of the interpolation: `p₁, p₂` in `(1,∞)`, `p₁⁻¹+p₂⁻¹ ≤ 1`,
  `θ ∈ (0,1)`, `ρ ≤ (1-θ)c/(2θ(A+1))`, and the three interpolation relations
  `p₁⁻¹ = (1-θ)/2 + θ a₁⁻¹`, `p₂⁻¹ = (1-θ)/2 + θ b₁⁻¹`, `p₁⁻¹+p₂⁻¹ = (1-θ)·1 + θ q₁⁻¹`,

produce Theorem `varp` with the *canonical* gain `2^{-c'L}`, `c' = (1-θ)c/2`, and a constant
`C Λ = max (Cθ · max (C₆ Λ) (C₇ Λ)) 1` (the `max … 1` is only there to make the constant
positive, which is what lets the `ℓ^p`-infinite cases be vacuous).

The two displayed relations are exactly the hypothesis list of `VarBilinInterp` at
`(a₀,b₀,q₀) = (2,2,1)`, `(a₁,b₁,q₁)` and `(a,b,q) = (p₁,p₂,(p₁⁻¹+p₂⁻¹)⁻¹)`. -/
theorem varpStatementΛ_of_pieceBounds
    (h8 : VarBilinInterp) {P : Polynomial ℤ} {C₀ : ℕ} {p₁ p₂ a₁ b₁ q₁ : ℝ≥0∞} {r : ℝ≥0}
    {ρ θ c A : ℝ}
    (hbil : ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f f' g : ℤ → ℂ) (c' : ℂ),
      FinSupp f → FinSupp f' → FinSupp g →
      (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a (f + c' • f') g l₁ l₂ k₁ k₂ n x)
        = (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
            + c' • (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f' g l₁ l₂ k₁ k₂ n x))
    (hbil' : ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g g' : ℤ → ℂ) (c' : ℂ),
      FinSupp f → FinSupp g → FinSupp g' →
      (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f (g + c' • g') l₁ l₂ k₁ k₂ n x)
        = (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
            + c' • (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f g' l₁ l₂ k₁ k₂ n x))
    (hconv : ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) {f g : ℤ → ℂ},
      MemLp f p₁ Measure.count → MemLp g p₂ Measure.count → ∀ (n : ℕ) (x : ℤ),
      Tendsto (fun K : ℕ => varpCol (kmtPj ρ) P P.natDegree C₀ a (truncZ K f) (truncZ K g)
          l₁ l₂ k₁ k₂ n x)
        atTop (𝓝 (varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)))
    (hzR : ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f : ℤ → ℂ),
      varpCol (kmtPj ρ) P P.natDegree C₀ a f 0 l₁ l₂ k₁ k₂ = 0)
    (hzL : ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (g : ℤ → ℂ),
      varpCol (kmtPj ρ) P P.natDegree C₀ a 0 g l₁ l₂ k₁ k₂ = 0)
    (hr : (1 : ℝ≥0) ≤ r) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hc : 0 < c) (hA : 0 ≤ A) (hρ0 : 0 < ρ)
    (hρsmall : ρ ≤ (1 - θ) * c / (2 * θ * (A + 1)))
    (h1p₁ : 1 < p₁) (h2p₁ : p₁ < ⊤) (h1p₂ : 1 < p₂) (h2p₂ : p₂ < ⊤)
    (h1a₁ : 1 < a₁) (h2a₁ : a₁ < ⊤) (h1b₁ : 1 < b₁) (h2b₁ : b₁ < ⊤)
    (h1q₁ : 1 ≤ q₁) (h2q₁ : q₁ < ⊤)
    (hqa : q₁ = (a₁⁻¹ + b₁⁻¹)⁻¹)
    (hrel1 : p₁⁻¹ = ENNReal.ofReal (1 - θ) * (2 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * a₁⁻¹)
    (hrel2 : p₂⁻¹ = ENNReal.ofReal (1 - θ) * (2 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * b₁⁻¹)
    (hrel3 : p₁⁻¹ + p₂⁻¹ =
      ENNReal.ofReal (1 - θ) * (1 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (h6 : PieceBound ρ P C₀ 2 2 1 r
      (fun l₁ l₂ s₁ s₂ => (2 : ℝ) ^ (-(c * (lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) : ℝ)))))
    (h7 : PieceBound ρ P C₀ a₁ b₁ q₁ r
      (fun l₁ l₂ s₁ s₂ => (2 : ℝ) ^ (A * ρ * (lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) : ℝ)))) :
    VarpStatementΛ (kmtPj ρ) P P.natDegree C₀ p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r := by
  obtain ⟨C₆, hC₆⟩ := h6
  obtain ⟨C₇, hC₇⟩ := h7
  obtain ⟨Cθ, hCθpos, hCθ⟩ := h8 r 2 2 1 a₁ b₁ q₁ p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ θ hr hθ0 hθ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1a₁ h2a₁ h1b₁ h2b₁
    (by norm_num) (by norm_num) h1q₁ h2q₁ hrel1 hrel2 (by rw [inv_inv]; exact hrel3)
  refine ⟨(1 - θ) * c / 2, fun Λ => max (Cθ * max (C₆ Λ) (C₇ Λ)) 1, ?_, ?_⟩
  · have : 0 < (1 - θ) * c := mul_pos (by linarith) hc
    positivity
  · intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
    set L : ℝ := ((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℤ) : ℝ) with hLdef
    have hL : 0 ≤ L := by
      rw [hLdef]
      have h : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
        simp only [lmax]; omega
      exact_mod_cast h
    set w₂ : ℝ := (2 : ℝ) ^ (-(c * L)) with hw₂def
    set w₇ : ℝ := (2 : ℝ) ^ (A * ρ * L) with hw₇def
    have hw₂pos : 0 < w₂ := by rw [hw₂def]; positivity
    have hw₇pos : 0 < w₇ := by rw [hw₇def]; positivity
    have hw₂ : ((fun l₁ l₂ s₁ s₂ => (2 : ℝ) ^ (-(c * (lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) : ℝ))))
        l₁ l₂ k₁ k₂) = w₂ := by
      rw [hw₂def, hLdef]
    have hw₇ : ((fun l₁ l₂ s₁ s₂ => (2 : ℝ) ^ (A * ρ * (lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) : ℝ)))
        l₁ l₂ k₁ k₂) = w₇ := by
      rw [hw₇def, hLdef]
    have hCcpos : 0 < max (Cθ * max (C₆ Λ) (C₇ Λ)) 1 := lt_max_of_lt_right one_pos
    have hexp : 0 ≤ (2 : ℝ) ^ (-(((1 - θ) * c / 2) * L)) := by positivity
    have hCwne : ((max (Cθ * max (C₆ Λ) (C₇ Λ)) 1 : ℝ≥0) : ℝ≥0∞) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(((1 - θ) * c / 2) * L))) ≠ 0 :=
      mul_ne_zero (ENNReal.coe_pos.mpr hCcpos).ne'
        (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hgoal : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x))
          (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count ≤
        ((max (Cθ * max (C₆ Λ) (C₇ Λ)) 1 : ℝ≥0) : ℝ≥0∞) *
          ENNReal.ofReal ((2 : ℝ) ^ (-(((1 - θ) * c / 2) * L))) *
          eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
      by_cases hg0 : eLpNorm g p₂ Measure.count = 0
      · have hgz : g = 0 := funext (eq_zero_of_eLpNorm_count_eq_zero (lt_trans one_pos h1p₂).ne' hg0)
        have hseq : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)) = fun _ => 0 := by
          funext x
          have hzero : (fun n : ℕ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g
              l₁ l₂ k₁ k₂ n x) = 0 := by
            funext n
            rw [hgz]
            exact congrFun (congrFun (hzR a l₁ l₂ k₁ k₂ f) n) x
          rw [hzero, variationalNorm_zero_of_one_le hr]
        rw [hseq, hg0]
        simp
      · by_cases hf0 : eLpNorm f p₁ Measure.count = 0
        · have hfz : f = 0 := funext (eq_zero_of_eLpNorm_count_eq_zero (lt_trans one_pos h1p₁).ne' hf0)
          have hseq : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)) = fun _ => 0 := by
            funext x
            have hzero : (fun n : ℕ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g
                l₁ l₂ k₁ k₂ n x) = 0 := by
              funext n
              rw [hfz]
              exact congrFun (congrFun (hzL a l₁ l₂ k₁ k₂ g) n) x
            rw [hzero, variationalNorm_zero_of_one_le hr]
          rw [hseq, hf0]
          simp
        · by_cases hft : eLpNorm f p₁ Measure.count = ⊤
          · rw [hft, ENNReal.mul_top hCwne, ENNReal.top_mul hg0]
            exact le_top
          · by_cases hgt : eLpNorm g p₂ Measure.count = ⊤
            · rw [hgt, ENNReal.mul_top (mul_ne_zero hCwne hf0)]
              exact le_top
            · have hfm : MemLp f p₁ Measure.count :=
                (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hft))
              have hgm : MemLp g p₂ Measure.count :=
                (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hgt))
              have hb₀ : ∀ f g : ℤ → ℂ, FinSupp f → FinSupp g →
                  eLpNorm (fun x => variationalNorm r (fun n => varpCol (kmtPj ρ) P P.natDegree C₀ a
                      f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
                    ≤ (C₆ Λ * w₂.toNNReal : ℝ≥0) * eLpNorm f 2 Measure.count *
                        eLpNorm g 2 Measure.count := by
                intro f g hf hg
                refine (hC₆ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1).trans (le_of_eq ?_)
                rw [hw₂, coe_mul_ofReal_eq _ (le_of_lt hw₂pos)]
              have hb₁ : ∀ f g : ℤ → ℂ, FinSupp f → FinSupp g →
                  eLpNorm (fun x => variationalNorm r (fun n => varpCol (kmtPj ρ) P P.natDegree C₀ a
                      f g l₁ l₂ k₁ k₂ n x)) q₁ Measure.count
                    ≤ (C₇ Λ * w₇.toNNReal : ℝ≥0) * eLpNorm f a₁ Measure.count *
                        eLpNorm g b₁ Measure.count := by
                intro f g hf hg
                refine (hC₇ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1).trans (le_of_eq ?_)
                rw [hw₇, coe_mul_ofReal_eq _ (le_of_lt hw₇pos)]
              have hconv' : ∀ f g : ℤ → ℂ, MemLp f p₁ Measure.count → MemLp g p₂ Measure.count →
                  ∀ (n : ℕ) (x : ℤ),
                  Tendsto (fun K : ℕ => varpCol (kmtPj ρ) P P.natDegree C₀ a (truncZ K f)
                      (truncZ K g) l₁ l₂ k₁ k₂ n x)
                    atTop (𝓝 (varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)) :=
                fun f g hf hg n x => hconv a l₁ l₂ k₁ k₂ hf hg n x
              have hmain := hCθ (fun f g n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f g
                  l₁ l₂ k₁ k₂ n x) (C₆ Λ * w₂.toNNReal) (C₇ Λ * w₇.toNNReal)
                (hbil a l₁ l₂ k₁ k₂) (hbil' a l₁ l₂ k₁ k₂) hb₀ hb₁ hconv' f g hfm hgm
              have hM₀ : ((C₆ Λ * w₂.toNNReal : ℝ≥0) : ℝ) = (C₆ Λ : ℝ) * w₂ := by
                rw [NNReal.coe_mul, coe_toNNReal_of_nonneg (le_of_lt hw₂pos)]
              have hM₁ : ((C₇ Λ * w₇.toNNReal : ℝ≥0) : ℝ) = (C₇ Λ : ℝ) * w₇ := by
                rw [NNReal.coe_mul, coe_toNNReal_of_nonneg (le_of_lt hw₇pos)]
              have hineq : (Cθ : ℝ) * ((C₆ Λ * w₂.toNNReal : ℝ≥0) : ℝ) ^ (1 - θ) *
                    ((C₇ Λ * w₇.toNNReal : ℝ≥0) : ℝ) ^ θ
                  ≤ (max (Cθ * max (C₆ Λ) (C₇ Λ)) 1 : ℝ≥0) *
                      (2 : ℝ) ^ (-(((1 - θ) * c / 2) * L)) := by
                rw [hM₀, hM₁, hw₂def, hw₇def]
                refine (interpWeight_le (C₆ := (C₆ Λ : ℝ)) (C₇ := (C₇ Λ : ℝ))
                  (Cθ := (Cθ : ℝ)) hc hθ0 hθ1 hA hρ0 hρsmall hL
                  (by positivity) (by positivity) (le_of_lt hCθpos)).trans ?_
                push_cast
                exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
              have hconst : ((Cθ : ℝ) * ((C₆ Λ * w₂.toNNReal : ℝ≥0) : ℝ) ^ (1 - θ) *
                    ((C₇ Λ * w₇.toNNReal : ℝ≥0) : ℝ) ^ θ).toNNReal
                  ≤ max (Cθ * max (C₆ Λ) (C₇ Λ)) 1 *
                      ((2 : ℝ) ^ (-(((1 - θ) * c / 2) * L))).toNNReal := by
                refine (Real.toNNReal_le_toNNReal hineq).trans (le_of_eq ?_)
                rw [Real.toNNReal_mul (le_of_lt (by exact_mod_cast hCcpos : (0 : ℝ) < _)),
                  Real.toNNReal_coe]
              refine hmain.trans ?_
              refine mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right ?_ (bot_le : (0 : ℝ≥0∞) ≤ _)) bot_le
              rw [coe_mul_ofReal_eq _ hexp]
              exact ENNReal.coe_le_coe.mpr hconst
    exact hgoal
end

end Work.KMTContract
