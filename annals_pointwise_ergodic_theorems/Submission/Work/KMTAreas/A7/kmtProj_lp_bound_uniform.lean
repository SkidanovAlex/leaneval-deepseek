/-
# The uniform (in `l`) `ℓ^p` bound for the KMT Ionescu--Wainger projections

The paper's Lemma `iw-prop`(i) (Krause--Mirek--Tao, Appendix `iw-app`) bounds the Ionescu--Wainger
projection `T^{≤l,≤k} = Π_{≤l,≤k}` on good major arcs by `⟨l⟩` times the multiplier norm:

  `GoodMajorArcs ρ Cρ l k → ‖T^{≤l,≤k} f‖_{ℓ^p} ≲_{ρ,p} ⟨l⟩ ‖f‖_{ℓ^p}`,  `1 < p < ∞`

(`Work.KMTAreas.A7.kmtProj_lp_bound`, proved in this directory from area `A1`).  This file proves
the *stronger* statement in which the factor `⟨l⟩` is absent:

  `∃ Cρ > 0, ∃ C > 0, ∀ l k, GoodMajorArcs ρ Cρ l k → ∀ f, ‖T^{≤l,≤k} f‖_{ℓ^p} ≤ C ‖f‖_{ℓ^p}`.

The mathematics is the uniform form of Tao's *main* theorem (`Work.BourgainPlan.Maximal` /
`Work.IonescuWainger`), used in `Submission/Work/KMTAreas/iwGap.lean` to close area `A1`.  The
`⟨l⟩` of the paper's statement is *not* a genuine loss: it is inserted there only to flatten the
two regimes of the proof, and the constant of the deep (large `l`) regime is independent of `l`
and `k` (Tao's theorem has no loss in the size of the denominator set), while the small-`l`
regime is finite by the elementary single-arc Magyar--Stein--Wainger bound.  The removal of `⟨l⟩`
is therefore the statement `Work.KMTAreas.iwEvenMultiplierGapUniform`.

## The route to an arbitrary real exponent

* the uniform bound is available at the *even* exponents `2k₀`, `k₀ ≥ 2`
  (`Work.KMTAreas.iwEvenMultiplierGapUniform`);
* duality (`Work.Analysis.IWMultiplier.IWLqBound_of_dual`, with the real-valuedness
  `star_periodize_etaCut` of the KMT symbol) transfers it to the dual exponent `(2k₀)'`;
* Riesz--Thorin interpolation (`Work.Analysis.IWMultiplier.IWLqBound_interpolation`) between
  `(2k₀)'` and `2k₀` gives every real exponent `1 < p < 2k₀` with the *same* constant;
* the passage from finitely supported data to arbitrary `f ∈ ℓ^p` is
  `Work.KMTAreas.A7.eLpNorm_kmtProj_le_of_IWLqBound` (Fatou along the truncations).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ProjLq
import Submission.Work.KMTAreas.iwEvenMultiplierGapUniform

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier (IWLqBound IWLqBound_of_dual IWLqBound_interpolation
  IsLqMultiplierBound)

/-- **Solving `p⁻¹ = (1 - θ) q₀⁻¹ + θ q₁⁻¹` for `θ ∈ [0,1]`** when `0 < q₀ < p < q₁`: the
exponent `p` lies between the Hölder duals `q₀, q₁`, so `1/p` is an affine combination of `1/q₀`
and `1/q₁` with parameter in the unit interval. -/
lemma exists_theta_interp {q₀ q₁ p : ℝ} (h0 : 0 < q₀) (h01 : q₀ < p) (h1 : p < q₁) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ p⁻¹ = (1 - θ) * q₀⁻¹ + θ * q₁⁻¹ := by
  have hp0 : 0 < p := lt_trans h0 h01
  have h10 : q₀ < q₁ := lt_trans h01 h1
  have hq1pos : 0 < q₁ := lt_trans hp0 h1
  have hlt : q₁⁻¹ < q₀⁻¹ := (inv_lt_inv₀ hq1pos h0).mpr h10
  have hden : q₁⁻¹ - q₀⁻¹ < 0 := by linarith
  have hnum : p⁻¹ - q₀⁻¹ < 0 := by
    have := (inv_lt_inv₀ hp0 h0).mpr h01
    linarith
  set θ : ℝ := (p⁻¹ - q₀⁻¹) / (q₁⁻¹ - q₀⁻¹) with hθdef
  have hden_ne : q₁⁻¹ - q₀⁻¹ ≠ 0 := ne_of_lt hden
  refine ⟨θ, ?_, ?_, ?_⟩
  · rw [hθdef]
    exact div_nonneg_of_nonpos hnum.le hden.le
  · rw [hθdef]
    rw [div_le_one_of_neg hden]
    have : q₁⁻¹ ≤ p⁻¹ := (inv_le_inv₀ hq1pos hp0).mpr h1.le
    linarith
  · have hkey : θ * (q₁⁻¹ - q₀⁻¹) = p⁻¹ - q₀⁻¹ := by
      rw [hθdef]; exact div_mul_cancel₀ _ hden_ne
    calc p⁻¹ = q₀⁻¹ + (p⁻¹ - q₀⁻¹) := by ring
      _ = q₀⁻¹ + θ * (q₁⁻¹ - q₀⁻¹) := by rw [hkey]
      _ = (1 - θ) * q₀⁻¹ + θ * q₁⁻¹ := by ring

/-- **Duality plus Riesz--Thorin interpolation of the uniform even-exponent bound.**  If the KMT
projection is bounded on `ℓ^{2r}` with a constant `C` independent of `(l,k)`, then it is bounded on
`ℓ^p` with the *same* constant for every real `p` strictly between the dual exponent `(2r)'` and
`2r`. -/
lemma iwLqBound_interp_uniform {ρ : ℝ} {l : ℕ} {k : ℤ} {r : ℕ} {C : NNReal} (hC : 0 < C)
    (hr : 2 ≤ r) {p : ℝ} (hp : 1 < p) (hp_lt : p < 2 * (r : ℝ))
    (hp_gt : 2 * (r : ℝ) / (2 * (r : ℝ) - 1) < p)
    (h : IWLqBound (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))
      (ENNReal.ofReal (2 * (r : ℝ))) C) :
    IWLqBound (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))
      (ENNReal.ofReal p) C := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have h2r0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  have hden0 : (0 : ℝ) < 2 * (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    linarith
  have hq0pos : (0 : ℝ) < 2 * (r : ℝ) / (2 * (r : ℝ) - 1) := div_pos h2r0 hden0
  -- ### duality: the bound at the dual exponent `(2r)'`
  have hdual := IWLqBound_of_dual (iwArithFreqs ρ l)
    (periodize (etaCut Work.KMTContract.kmtEta k)) h
    (by rw [ENNReal.toReal_ofReal h2r0.le]; linarith)
  have hsym : (fun ξ => star (periodize (etaCut Work.KMTContract.kmtEta k) ξ))
      = periodize (etaCut Work.KMTContract.kmtEta k) :=
    funext (fun ξ => star_periodize_etaCut k ξ)
  rw [hsym] at hdual
  rw [ENNReal.toReal_ofReal h2r0.le] at hdual
  -- ### interpolation between `(2r)'` and `2r`
  obtain ⟨θ, hθ0, hθ1, hθeq⟩ :=
    exists_theta_interp (q₀ := 2 * (r : ℝ) / (2 * (r : ℝ) - 1)) (q₁ := 2 * (r : ℝ))
      hq0pos hp_gt hp_lt
  have hqeq : ((ENNReal.ofReal p).toReal)⁻¹
      = (1 - θ) * ((ENNReal.ofReal (2 * (r : ℝ) / (2 * (r : ℝ) - 1))).toReal)⁻¹
        + θ * ((ENNReal.ofReal (2 * (r : ℝ))).toReal)⁻¹ := by
    rw [ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal hq0pos.le,
      ENNReal.toReal_ofReal h2r0.le]
    exact hθeq
  have hle_q0 : 1 ≤ (ENNReal.ofReal (2 * (r : ℝ) / (2 * (r : ℝ) - 1))).toReal := by
    rw [ENNReal.toReal_ofReal hq0pos.le]
    rw [le_div_iff₀ hden0]
    linarith
  have hle_q1 : 1 ≤ (ENNReal.ofReal (2 * (r : ℝ))).toReal := by
    rw [ENNReal.toReal_ofReal h2r0.le]
    linarith
  have hinterp := IWLqBound_interpolation (iwArithFreqs ρ l)
    (periodize (etaCut Work.KMTContract.kmtEta k)) hdual h hθ0 hθ1 hle_q0 hle_q1 hqeq
  have hCe : C ^ (1 - θ) * C ^ θ = C := by
    rw [← NNReal.rpow_add (ne_of_gt hC)]
    rw [show 1 - θ + θ = 1 by ring, NNReal.rpow_one]
  rwa [hCe] at hinterp

/-- **The uniform `ℓ^p` bound for the KMT projections, from the uniform even-exponent bound
`heven` (the `⟨l⟩`-free form of area `A1`, i.e. `Work.KMTAreas.iwEvenMultiplierGapUniform`).**

For `1 < p < ∞` there are `Cρ > 0` and `C > 0` such that for every good major arc pair `(l,k)` and
every `f : ℤ → ℂ` the projection `kmtProj ρ l k f` obeys `‖·‖_{ℓ^p} ≤ C ‖f‖_{ℓ^p}` — with a
constant `C` *independent of `l` and `k`*. -/
lemma kmtProj_lp_bound_uniform_of_even
    (heven : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (k₀ : ℕ), 2 ≤ k₀ → ∃ C : NNReal, 0 < C ∧
        ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
        ∀ (φ : SchwartzMap ℝ ℂ), (∀ x, φ x ≠ 0 → x ∈ realArc k) →
        ∀ (M : NNReal),
          IsLqMultiplierBound ((2 * k₀ : ℕ) : ENNReal) (φ : ℝ → ℂ) M →
          IWLqBound (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ))
            ((2 * k₀ : ℕ) : ENNReal) (C * M))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ℝ) (hp : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k f) (ENNReal.ofReal p)
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, heven'⟩ := heven ρ hρ hρ1
  obtain ⟨M, hMpos, hM⟩ := EtaMult
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hden_pos : (0 : ℝ) < p - 1 := by linarith
  -- the even exponent `r` chosen so that both `(2r)' < p` and `p < 2r`
  set r : ℕ := ⌈p / (p - 1)⌉₊ + ⌈p / 2⌉₊ + 2 with hrdef
  have hrc : ((r : ℕ) : ℝ) = ((⌈p / (p - 1)⌉₊ : ℕ) : ℝ) + ((⌈p / 2⌉₊ : ℕ) : ℝ) + 2 := by
    rw [hrdef]; push_cast; ring
  have hr2 : 2 ≤ r := by rw [hrdef]; omega
  have hr_gt : p / (p - 1) < (r : ℝ) := by
    have hceil : p / (p - 1) ≤ ((⌈p / (p - 1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    rw [hrc]; linarith
  have hr_gt2 : p / 2 < (r : ℝ) := by
    have hceil : p / 2 ≤ ((⌈p / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    rw [hrc]; linarith
  have hp_lt : p < 2 * (r : ℝ) := by linarith
  have hp_gt : 2 * (r : ℝ) / (2 * (r : ℝ) - 1) < p := by
    have h2r : p / (p - 1) < 2 * (r : ℝ) := by linarith
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (r : ℝ) - 1)]
    rw [div_lt_iff₀ hden_pos] at h2r
    linarith
  obtain ⟨C₀, hC₀, hbound⟩ := heven' r hr2
  refine ⟨Cρ, hCρ, (((C₀ * M : NNReal) : ℝ)), by positivity, ?_⟩
  intro l k hgood f
  have hcast : ENNReal.ofReal (2 * (r : ℝ)) = ((2 * r : ℕ) : ENNReal) := by
    rw [show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  have hq1 : 1 ≤ ((2 * r : ℕ) : ENNReal) := by
    rw [← hcast, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsup : ∀ x : ℝ, (etaCutSchwartz k) x ≠ 0 → x ∈ realArc k := by
    intro x hx
    rw [etaCutSchwartz_coe] at hx
    exact etaCut_ne_zero_mem_realArc k hx
  have hMk : IsLqMultiplierBound ((2 * r : ℕ) : ENNReal)
      ((etaCutSchwartz k : SchwartzMap ℝ ℂ) : ℝ → ℂ) M := by
    simpa [etaCutSchwartz_coe] using hM k ((2 * r : ℕ) : ENNReal) hq1
  have hevenr : IWLqBound (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))
      (ENNReal.ofReal (2 * (r : ℝ))) (C₀ * M) := by
    have hb := hbound l k hgood (etaCutSchwartz k) hsup M hMk
    rw [etaCutSchwartz_coe] at hb
    rwa [← hcast] at hb
  exact eLpNorm_kmtProj_le_of_IWLqBound l k hp (by positivity)
    (iwLqBound_interp_uniform (C := C₀ * M) (by positivity) hr2 hp hp_lt hp_gt hevenr) f

/-- **The uniform `ℓ^p` bound for the KMT Ionescu--Wainger projections** (the `⟨l⟩`-free form of
Lemma `iw-prop`(i) of Krause--Mirek--Tao): for every `ρ ∈ (0,1]` and every real exponent `p > 1`
there are constants `Cρ > 0` and `C > 0` such that, whenever `(l,k)` has good major arcs, the
projection `kmtProj ρ l k = Π_{≤l,≤k}` is bounded on `ℓ^p(ℤ)` by `C` — uniformly in `l` and `k`.

The even exponents come from `Work.KMTAreas.iwEvenMultiplierGapUniform` (the `⟨l⟩`-free form of
area `A1`), and the general real exponent from duality plus Riesz--Thorin interpolation; see
`iwLqBound_interp_uniform` and `kmtProj_lp_bound_uniform_of_even`. -/
theorem kmtProj_lp_bound_uniform (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ℝ) (hp : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k f) (ENNReal.ofReal p)
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count :=
  kmtProj_lp_bound_uniform_of_even
    (fun ρ hρ hρ1 => Work.KMTAreas.iwEvenMultiplierGapUniform ρ hρ hρ1) ρ hρ hρ1 p hp

end Work.KMTAreas.A7
