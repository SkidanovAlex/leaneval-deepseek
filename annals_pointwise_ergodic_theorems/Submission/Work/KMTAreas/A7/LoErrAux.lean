/-
# Auxiliary lemmas for the level-`0` single-scale model approximation (`LoErrSingleScale00`)

This module collects the small, self-contained inputs of the proof of
`Work.KMTAreas.A7.LoErrStatement` at `l₁ = l₂ = 0`:

* `iwArithFreqs_zero` — the Ionescu--Wainger arithmetic frequency set of height `≤ 0` is the
  singleton `{0}` (so that `Tle ρ 0` is the plain height-`0` convolution multiplier and
  `diffFreqs ρ 0 = {0}`);
* `nonAliasing_iwArithFreqs_zero` — the corresponding non-aliasing statement at the arc radius
  `-(2u)`, `u ≥ 1`;
and `diffFreqs ρ 0 = {0}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoDefs
import Submission.Work.KMTPlan.A6.LowSmallSymDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger


/-- **The height-`≤ 0` arithmetic frequency set is `{0}`.**  Indeed
`iwP ρ 0 = Finset.Icc 1 (2 ^ 0) = {1}` (since `iwC0 ρ ≥ 0`), and the only `1`-torsion element of
`ℝ/ℤ` is `0`. -/
theorem iwArithFreqs_zero (ρ : ℝ) : iwArithFreqs ρ 0 = {0} := by
  unfold iwArithFreqs iwP
  rw [if_pos (Nat.zero_le _)]
  rw [show (2 : ℕ) ^ 0 = 1 from rfl]
  ext γ
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · rintro ⟨q, ⟨h1, h2⟩, a, ha, rfl⟩
    have hq : q = 1 := by omega
    subst hq
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    simp
  · rintro rfl
    exact ⟨1, by norm_num, 0, by simp, by simp⟩

/-- The `realArc` radius `2^{-2u}` is at most `1/4` when `u ≥ 1`. -/
lemma two_zpow_neg_two_mul_le_quarter {u : ℕ} (hu : 1 ≤ u) :
    (2 : ℝ) ^ (-(2 * (u : ℤ))) ≤ 1 / 4 := by
  have hpow2 : ((2 : ℝ) ^ (2 * u))⁻¹ = (2 : ℝ) ^ (-(2 * (u : ℤ))) := by
    rw [show (-(2 * (u : ℤ))) = -((2 * u : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [← hpow2]
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * u) := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ (2 * u) :=
        pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ 2 * u)
  have h := (inv_le_inv₀ (show (0 : ℝ) < (2 : ℝ) ^ (2 * u) by positivity)
    (by norm_num : (0 : ℝ) < 4)).mpr h4
  simpa using h

/-- The set of arithmetic frequencies of height `≤ 0` and its double are non-aliasing at the arc
radius `-(2u)` with `u ≥ 1` (in fact at every radius `k` with `2^k ≤ 1/2`). -/
theorem nonAliasing_iwArithFreqs_zero (ρ : ℝ) {u : ℕ} (hu : 1 ≤ u) :
    NonAliasing (-(2 * (u : ℤ))) (iwArithFreqs ρ 0 ∪ iwArithFreqs ρ 0) := by
  rw [iwArithFreqs_zero, Finset.union_self]
  intro α hα β hβ θ hθ θ' hθ' hEq
  rw [Finset.mem_singleton] at hα hβ
  subst hα; subst hβ
  refine ⟨rfl, ?_⟩
  have hEq' : ((θ : ℝ) : Work.Analysis.IonescuWainger.Circle)
      = ((θ' : ℝ) : Work.Analysis.IonescuWainger.Circle) := by simpa using hEq
  have hq := two_zpow_neg_two_mul_le_quarter hu
  have hb : ∀ ξ : ℝ, ξ ∈ realArc (-(2 * (u : ℤ))) → |ξ| ≤ 1 / 4 := by
    intro ξ hξ
    rw [realArc, Set.mem_Icc] at hξ
    exact abs_le.mpr ⟨by linarith [hξ.1, hq], by linarith [hξ.2, hq]⟩
  have hmem : θ - θ' ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    (QuotientAddGroup.eq_iff_sub_mem (N := AddSubgroup.zmultiples (1 : ℝ))).mp hEq'
  obtain ⟨n, hn⟩ := (AddSubgroup.mem_zmultiples_iff).mp hmem
  have hcast : ((n : ℝ)) = θ - θ' := by simpa using hn
  have hsmall : |θ - θ'| < 1 := by
    have h1 := hb θ hθ
    have h2 := hb θ' hθ'
    have h3 : |θ - θ'| ≤ |θ| + |θ'| := by
      calc |θ - θ'| = |θ + (-θ')| := by ring_nf
        _ ≤ |θ| + |-θ'| := abs_add_le θ (-θ')
        _ = |θ| + |θ'| := by rw [abs_neg]
    linarith
  have hn1 : |(n : ℝ)| < 1 := by rw [hcast]; exact hsmall
  have hn0 : n = 0 := by
    have h1 : (n : ℝ) < 1 := (abs_lt.mp hn1).2
    have h2 : (-1 : ℝ) < (n : ℝ) := (abs_lt.mp hn1).1
    have h3 : n < 1 := by exact_mod_cast h1
    have h4 : (-1 : ℤ) < n := by exact_mod_cast h2
    omega
  simp [hn0] at hcast
  linarith [hcast]

/-- The auxiliary scale `uScale ρ L = scaleCount 1 ρ L` is at least `1`. -/
lemma uScale_pos {ρ : ℝ} (hρ : 0 ≤ ρ) (L : ℕ) : 1 ≤ Work.KMTAreas.A7.uScale ρ L := by
  rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
  have hpow : ((1 : ℤ) : ℝ) ≤ ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    rw [Nat.cast_one, Int.cast_one, one_mul]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hfl : (1 : ℤ) ≤ ⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    Int.le_floor.mpr hpow
  have h0 : (0 : ℤ) ≤ ⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    le_trans (by norm_num) hfl
  have h3 : (1 : ℤ) ≤ ((⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h0]
    exact hfl
  exact_mod_cast h3

end

end Work.KMTAreas.A7
