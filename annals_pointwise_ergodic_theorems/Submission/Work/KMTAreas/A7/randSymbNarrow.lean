/-
# The Ionescu–Wainger wiring for *narrow* symbols

Turns a continuous multiplier bound at an even exponent `2k₀` for a symbol supported in the narrow
arc `ℝ_{≤k}` into the discrete Ionescu–Wainger `ℓ^p` bound, by

1. the `ℓ²` endpoint (`IWMultiplierBound_q2_vector`),
2. area `A1` at `2k₀`,
3. Riesz–Thorin interpolation between `2` and `2k₀` (`IWLqBound_interpolate_two`) for `p ≥ 2`,
4. duality (`IWLqBound_of_dual`) for `1 < p < 2`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.exists_interp_theta
import Submission.Work.KMTAreas.A7.randSymb_coeff_data
import Submission.Work.KMTAreas.A7.lacunaryBump_mult_bound_k1pos
import Submission.Work.KMTAreas.A7.lacunaryBumpExponent
import Submission.Work.KMTAreas.A7.IwLqGeneral
import Submission.Work.KMTAreas.IsLqMultiplierBound_supNorm
import Submission.Work.KMTAreas.A7.IsLqMultiplierBound_star
import Submission.Work.KMTAreas.schwartz_shift_summable

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract Work.Analysis.EndVar

/-- **The weighted geometric mean is at most the maximum**: `x^{1-θ} y^θ ≤ max x y` for
`θ ∈ [0,1]`. -/
theorem nnreal_rpow_interp_le_max (x y : NNReal) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ^ (1 - θ) * y ^ θ ≤ max x y := by
  have h1θ : (0 : ℝ) ≤ 1 - θ := by linarith
  rcases le_total y x with h | h
  · have hyx : y ^ θ ≤ x ^ θ := NNReal.rpow_le_rpow h hθ0
    have h0 : (0 : NNReal) ≤ x ^ (1 - θ) := zero_le
    refine (mul_le_mul_of_nonneg_left hyx h0).trans ?_
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      have hy0 : y = 0 := le_antisymm (by simpa using h) zero_le
      subst hy0
      have hne : (1 - θ) ≠ 0 ∨ θ ≠ 0 := by
        by_contra hc
        simp only [not_or, not_not] at hc
        have h0 : (1 : ℝ) = 0 := by
          calc (1 : ℝ) = (1 - θ) + θ := by ring
            _ = 0 := by rw [hc.1, hc.2]; ring
        norm_num at h0
      rcases hne with h' | h'
      · rw [NNReal.zero_rpow h', zero_mul]; simp
      · rw [NNReal.zero_rpow h', mul_zero]; simp
    · rw [← NNReal.rpow_add hx, show 1 - θ + θ = 1 by ring, NNReal.rpow_one]
      exact le_max_left _ _
  · have hxy : x ^ (1 - θ) ≤ y ^ (1 - θ) := NNReal.rpow_le_rpow h h1θ
    have h0 : (0 : NNReal) ≤ y ^ θ := zero_le
    refine (mul_le_mul_of_nonneg_right hxy h0).trans ?_
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      have hx0 : x = 0 := le_antisymm (by simpa using h) zero_le
      subst hx0
      have hne : (1 - θ) ≠ 0 ∨ θ ≠ 0 := by
        by_contra hc
        simp only [not_or, not_not] at hc
        have h0 : (1 : ℝ) = 0 := by
          calc (1 : ℝ) = (1 - θ) + θ := by ring
            _ = 0 := by rw [hc.1, hc.2]; ring
        norm_num at h0
      rcases hne with h' | h'
      · rw [NNReal.zero_rpow h', zero_mul]; simp
      · rw [NNReal.zero_rpow h', mul_zero]; simp
    · rw [← NNReal.rpow_add hy, show (1 - θ) + θ = 1 by ring, NNReal.rpow_one]
      exact le_max_right _ _

/-- **The narrow-case wiring.**  Given the area-`A1` bound at the even exponent `2k₀`, the `ℓ²`
endpoint, and a continuous multiplier bound `IsLqMultiplierBound (2k₀) Ψ M` for a symbol supported
in the arc `ℝ_{≤k}`, the discrete Ionescu–Wainger operator `T^{≤l}_Ψ` is bounded on `ℓ^p(ℤ)` for
every `1 < p ≤ 2k₀`, with the explicit constant `max (⟨l⟩ M) (Cₑ ⟨l⟩ M)`. -/
theorem narrow_IWLqBound (hA1 : Work.KMTContract.AreaA1) {p : ℝ} (hp : 1 < p)
    {ρ : ℝ} (hρ : 0 < ρ) {Cρ : ℝ} (hCρ2 : 2 ≤ Cρ)
    (hNA : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l))
    {k₀ : ℕ} (hk₀ : 2 ≤ k₀) (hpk : p ≤ 2 * (k₀ : ℝ)) (hpk' : p / (p - 1) ≤ 2 * (k₀ : ℝ))
    {Cev : NNReal}
    (heven : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ (φ : SchwartzMap ℝ ℂ),
      (∀ x, φ x ≠ 0 → x ∈ realArc k) → ∀ (Mv : NNReal),
        IsLqMultiplierBound ((2 * k₀ : ℕ) : ENNReal) (⇑φ) Mv →
        IWLqBound (iwArithFreqs ρ l) (periodize (⇑φ)) ((2 * k₀ : ℕ) : ENNReal)
          (Cev * angleBracket l * Mv))
    {l : ℕ} {k : ℤ} (hgood : GoodMajorArcs ρ Cρ l k)
    {Φ : SchwartzMap ℝ ℂ} (hΦsupp : ∀ x, Φ x ≠ 0 → x ∈ realArc k)
    {Mv : NNReal} (hMv : 0 < Mv)
    (hM : IsLqMultiplierBound ((2 * k₀ : ℕ) : ENNReal) (⇑Φ) Mv)
    (hMst : IsLqMultiplierBound ((2 * k₀ : ℕ) : ENNReal) (fun x => star (Φ x)) Mv) :
    IWLqBound (iwArithFreqs ρ l) (periodize (⇑Φ)) (ENNReal.ofReal p)
      (max (angleBracket l * Mv) (Cev * angleBracket l * Mv)) := by
  have h2k : ((2 * k₀ : ℕ) : ENNReal) = ENNReal.ofReal (2 * (k₀ : ℝ)) := by
    rw [← ENNReal.ofReal_natCast (2 * k₀)]
    congr 1
    push_cast
    ring
  have hk0R : (2 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
  have hq1 : (1 : ENNReal) ≤ ((2 * k₀ : ℕ) : ENNReal) := by
    rw [h2k, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    linarith
  have hqt : ((2 * k₀ : ℕ) : ENNReal) < ⊤ := h2k ▸ ENNReal.ofReal_lt_top
  have hsup : ∀ x : ℝ, ‖(⇑Φ : ℝ → ℂ) x‖ ≤ (Mv : ℝ) :=
    Work.KMTAreas.IsLqMultiplierBound_supNorm (p := ((2 * k₀ : ℕ) : ENNReal)) hq1 hqt
      Φ.continuous hM
  have hsupst : ∀ x : ℝ, ‖(fun x : ℝ => star ((⇑Φ : ℝ → ℂ) x)) x‖ ≤ (Mv : ℝ) := by
    intro x; simpa using hsup x
  have hsum : ∀ x : ℝ, Summable (fun j : ℤ => (⇑Φ : ℝ → ℂ) (x + j)) := by
    intro x; exact (Work.KMTAreas.schwartz_shift_summable Φ x).of_norm
  have hsumst : ∀ x : ℝ, Summable (fun j : ℤ => (fun x : ℝ => star ((⇑Φ : ℝ → ℂ) x)) (x + j)) := by
    intro x
    refine Summable.of_norm ?_
    simpa only [norm_star] using Work.KMTAreas.schwartz_shift_summable Φ x
  have h2 : IWLqBound (iwArithFreqs ρ l) (periodize (⇑Φ)) 2 (angleBracket l * Mv) :=
    IWMultiplierBound_q2_vector hρ hCρ2 hNA hgood Φ.continuous.measurable hΦsupp hsum hsup
  have h2st : IWLqBound (iwArithFreqs ρ l) (periodize (fun x : ℝ => star ((⇑Φ : ℝ → ℂ) x))) 2
      (angleBracket l * Mv) :=
    IWMultiplierBound_q2_vector hρ hCρ2 hNA hgood
      ((starSchwartz Φ).continuous.measurable)
      (fun x hx => hΦsupp x (by simpa using hx)) hsumst hsupst
  have hev : IWLqBound (iwArithFreqs ρ l) (periodize (⇑Φ)) ((2 * k₀ : ℕ) : ENNReal)
      (Cev * angleBracket l * Mv) := heven l k hgood Φ hΦsupp Mv hM
  have hevst : IWLqBound (iwArithFreqs ρ l) (periodize (fun x : ℝ => star ((⇑Φ : ℝ → ℂ) x)))
      ((2 * k₀ : ℕ) : ENNReal) (Cev * angleBracket l * Mv) := by
    have h := heven l k hgood (starSchwartz Φ)
      (fun x hx => hΦsupp x (starSchwartz_ne_zero hx)) Mv hMst
    rwa [starSchwartz_coe] at h
  by_cases hp2 : 2 ≤ p
  · obtain ⟨θ, hθ0, hθ1, hθeq⟩ := exists_interp_theta hp2 hk₀ hpk
    have hqeq : ((ENNReal.ofReal p)).toReal⁻¹ = (1 - θ) * (2 : ℝ)⁻¹ + θ * (2 * (k₀ : ℝ))⁻¹ := by
      rw [ENNReal.toReal_ofReal (le_of_lt (lt_trans zero_lt_one hp))]
      exact hθeq
    have hb := IWLqBound_interpolate_two hk₀ (Φ := periodize (⇑Φ)) (q := ENNReal.ofReal p)
      (C₂ := angleBracket l * Mv) (C₁ := Cev * angleBracket l * Mv) h2 (by rw [← h2k]; exact hev)
      hθ0 hθ1 hqeq
    exact hb.mono (nnreal_rpow_interp_le_max _ _ hθ0 hθ1)
  · have hp2' : p < 2 := lt_of_not_ge hp2
    have hppos : 0 < p := lt_trans zero_lt_one hp
    have hp1pos : 0 < p - 1 := by linarith
    have hppos' : 0 < p / (p - 1) := div_pos hppos hp1pos
    have hp2q : 2 ≤ p / (p - 1) := by
      rw [le_div_iff₀ hp1pos]; linarith
    obtain ⟨θ, hθ0, hθ1, hθeq⟩ := exists_interp_theta hp2q hk₀ hpk'
    have hqeq : ((ENNReal.ofReal (p / (p - 1)))).toReal⁻¹
        = (1 - θ) * (2 : ℝ)⁻¹ + θ * (2 * (k₀ : ℝ))⁻¹ := by
      rw [ENNReal.toReal_ofReal (le_of_lt hppos')]
      exact hθeq
    have hb := IWLqBound_interpolate_two hk₀
      (Φ := periodize (fun x : ℝ => star ((⇑Φ : ℝ → ℂ) x)))
      (q := ENNReal.ofReal (p / (p - 1)))
      (C₂ := angleBracket l * Mv) (C₁ := Cev * angleBracket l * Mv) h2st
      (by rw [← h2k]; exact hevst) hθ0 hθ1 hqeq
    have hmono := hb.mono (nnreal_rpow_interp_le_max _ _ hθ0 hθ1)
    have hq1' : 1 < (ENNReal.ofReal (p / (p - 1))).toReal := by
      rw [ENNReal.toReal_ofReal (le_of_lt hppos')]
      rw [lt_div_iff₀ hp1pos]
      linarith
    have hdual := IWLqBound_of_dual (iwArithFreqs ρ l)
      (periodize (fun x : ℝ => star ((⇑Φ : ℝ → ℂ) x))) hmono hq1'
    have hexp : ((ENNReal.ofReal (p / (p - 1))).toReal
          / ((ENNReal.ofReal (p / (p - 1))).toReal - 1)) = p := by
      rw [ENNReal.toReal_ofReal (le_of_lt hppos')]
      have h1 : p - 1 ≠ 0 := ne_of_gt hp1pos
      field_simp
      ring
    have hsym : (fun ξ => star (periodize (fun x : ℝ => star ((⇑Φ : ℝ → ℂ) x)) ξ))
        = periodize (⇑Φ : ℝ → ℂ) := by
      funext ξ
      exact periodize_star (⇑Φ : ℝ → ℂ) ξ
    rw [hexp, hsym] at hdual
    exact hdual

/-- **`IsLqMultiplierBound` is monotone in the constant.** -/
theorem IsLqMultiplierBound.mono {q : ENNReal} {φ : ℝ → ℂ} {M M' : NNReal}
    (h : IsLqMultiplierBound q φ M) (hMM : M ≤ M') : IsLqMultiplierBound q φ M' := by
  intro G
  refine (h G).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ zero_le
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hMM)


end

end Work.KMTAreas.A7
