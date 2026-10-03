import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc

namespace Work.KMTAreas.A7

open scoped BigOperators

/-!
# The periodisation of the §6 symbol `m_* = η_{≤ -2u}`

The symbol `mStarF u = η_{≤-2u} = etaCut kmtEta (-(2u))` of Krause–Mirek–Tao is a bump which
equals `1` on `[-2^{-2u-1}, 2^{-2u-1}]` and vanishes off `(-2^{-2u}, 2^{-2u})`.  Consequently

* its periodisation equals `1` on the arc of radius `2^{-2u-1}` around `0` of the frequency
  circle `ℝ/ℤ`;
* more generally, the periodisation of `mStarF u` equals `1` at every point of the circle which
  is the image of a real number `θ₀` with `|θ₀| ≤ 2^{-2u-1}`; thus if `periodize φ` does not
  vanish at `θ` for a `φ` supported in that arc, then `periodize (mStarF u) θ = 1` as well.

The two statements below are the (easy, but load-bearing) plateau properties of the §6 symbol.
-/

/-- **The periodisation of a plateau function is `1`.**  Let `φ` be `1` on `[-δ,δ]` and `0` off
`(-Δ,Δ)`, with `Δ + δ ≤ 1`.  Then for every `x` which is within `δ` of an integer, the orbit sum
`∑' k, φ (x + k)` consists of the single term at that integer, hence equals `1`.

The hypothesis `Δ + δ ≤ 1` is what makes the contributing integer unique: if two distinct
integers `k ≠ k₀` had `|x + k| < Δ` and `|x + k₀| ≤ δ`, then `|k - k₀| < Δ + δ ≤ 1`, impossible
for distinct integers. -/
private lemma tsum_plateau {φ : ℝ → ℂ} {δ Δ : ℝ} (hΔδ : Δ + δ ≤ 1)
    (hφ1 : ∀ y : ℝ, |y| ≤ δ → φ y = 1) (hφ0 : ∀ y : ℝ, Δ ≤ |y| → φ y = 0)
    {x : ℝ} {k₀ : ℤ} (hk₀ : |x + (k₀ : ℝ)| ≤ δ) :
    (∑' k : ℤ, φ (x + (k : ℝ))) = 1 := by
  have hside : ∀ k : ℤ, k ≠ k₀ → φ (x + (k : ℝ)) = 0 := by
    intro k hk
    refine hφ0 _ ?_
    by_contra hlt
    rw [not_le] at hlt
    have hsub : |(k : ℝ) - (k₀ : ℝ)| ≤ |x + (k : ℝ)| + |x + (k₀ : ℝ)| := by
      have h := abs_sub (x + (k : ℝ)) (x + (k₀ : ℝ))
      have heq : x + (k : ℝ) - (x + (k₀ : ℝ)) = (k : ℝ) - (k₀ : ℝ) := by ring
      rwa [heq] at h
    have hge : (1 : ℝ) ≤ |(k : ℝ) - (k₀ : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |k - k₀| := Int.one_le_abs (sub_ne_zero.mpr hk)
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|k - k₀| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |((k - k₀ : ℤ) : ℝ)| := by rw [Int.cast_abs]
        _ = |(k : ℝ) - (k₀ : ℝ)| := by rw [Int.cast_sub]
    linarith
  rw [tsum_eq_single k₀ hside]
  exact hφ1 _ hk₀

/-- **The periodisation of a plateau function at a real point.**  If `φ` is `1` on `[-δ,δ]` and
`0` off `(-Δ,Δ)` with `Δ + δ ≤ 1`, then `periodize φ` is `1` on the image in `ℝ/ℤ` of `[-δ,δ]`. -/
private lemma periodize_plateau {φ : ℝ → ℂ} {δ Δ : ℝ} (hΔδ : Δ + δ ≤ 1)
    (hφ1 : ∀ y : ℝ, |y| ≤ δ → φ y = 1) (hφ0 : ∀ y : ℝ, Δ ≤ |y| → φ y = 0)
    (θ₀ : ℝ) (hθ₀ : |θ₀| ≤ δ) :
    Work.Analysis.IonescuWainger.periodize φ
      (θ₀ : Work.Analysis.IonescuWainger.Circle) = 1 := by
  rw [Work.KMTContract.periodizeCoeEqTsum]
  simpa using tsum_plateau (φ := φ) hΔδ hφ1 hφ0 (x := θ₀) (k₀ := 0) (by simpa using hθ₀)

/-- **A nonvanishing periodisation detects a real representative in the support.**  If `φ`
vanishes off `[-δ,δ]` and `periodize φ θ ≠ 0`, then `θ` is the image of some `θ₀` with
`|θ₀| ≤ δ`.  Indeed some translate `x + k` of the canonical representative `x ∈ [0,1)` of `θ`
carries a nonzero value of `φ`. -/
private lemma exists_coe_abs_le_of_periodize_ne_zero {φ : ℝ → ℂ} {δ : ℝ}
    (hsupp : ∀ y : ℝ, φ y ≠ 0 → |y| ≤ δ)
    {θ : Work.Analysis.IonescuWainger.Circle}
    (h : Work.Analysis.IonescuWainger.periodize φ θ ≠ 0) :
    ∃ θ₀ : ℝ, (θ₀ : Work.Analysis.IonescuWainger.Circle) = θ ∧ |θ₀| ≤ δ := by
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 θ).val with hxdef
  have hxθ : (x : Work.Analysis.IonescuWainger.Circle) = θ := by
    rw [hxdef]; exact AddCircle.coe_equivIco
  have hper : Work.Analysis.IonescuWainger.periodize φ θ
      = ∑' k : ℤ, φ (x + (k : ℝ)) := by
    rw [← hxθ, Work.KMTContract.periodizeCoeEqTsum]
  have hne : ∃ k : ℤ, φ (x + (k : ℝ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine h ?_
    rw [hper]
    have h0 : (fun k : ℤ => φ (x + (k : ℝ))) = fun _ => (0 : ℂ) := funext hcon
    rw [h0, tsum_zero]
  obtain ⟨k, hk⟩ := hne
  refine ⟨x + (k : ℝ), ?_, hsupp _ hk⟩
  have hkc : (((k : ℝ)) : Work.Analysis.IonescuWainger.Circle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [AddCircle.coe_add, hxθ, hkc, add_zero]

/-- `mStarF u` equals `1` on `[-2^{-2u-1}, 2^{-2u-1}]`. -/
private lemma mStarF_eq_one {U : ℕ} {x : ℝ}
    (hx : |x| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) : mStarF U x = 1 := by
  have hpow : (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)
      = (1 / 2) * (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
    rw [show (-(2 * (U : ℤ)) - 1) = -(2 * (U : ℤ)) + (-1) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg_one]
    norm_num
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
  unfold mStarF Work.Analysis.IonescuWainger.etaCut
  refine Work.KMTContract.kmtEta_one ?_
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, ← hpow]
  exact hx

/-- `mStarF u` vanishes off `(-2^{-2u}, 2^{-2u})`. -/
private lemma mStarF_eq_zero {U : ℕ} {x : ℝ}
    (hx : (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ |x|) : mStarF U x = 0 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
  unfold mStarF Work.Analysis.IonescuWainger.etaCut
  refine Work.KMTContract.kmtEta_zero ?_
  rw [abs_div, abs_of_pos hpos, one_le_div hpos]
  exact hx

/-- The two scales of `mStarF` add up to at most `1`: `2^{-2u} + 2^{-2u-1} ≤ 1` for `u ≥ 1`. -/
private lemma mStarF_scales_sum_le_one {U : ℕ} (hU : 1 ≤ U) :
    (2 : ℝ) ^ (-(2 * (U : ℤ))) + (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) ≤ 1 := by
  have hUZ : (1 : ℤ) ≤ (U : ℤ) := by exact_mod_cast hU
  have h1 : (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ 1 / 4 := by
    calc (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = 1 / 4 := by norm_num
  have h2 : (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) ≤ 1 / 8 := by
    calc (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) ≤ (2 : ℝ) ^ (-3 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      _ = 1 / 8 := by norm_num
  linarith

theorem periodize_mStarF_one (U : ℕ) (hU : 1 ≤ U) :
    (∀ θ : Work.Analysis.IonescuWainger.Circle,
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) →
      Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.mStarF U) θ = 1) ∧
    (∀ (φ : ℝ → ℂ) (θ : Work.Analysis.IonescuWainger.Circle),
      Work.Analysis.IonescuWainger.periodize φ θ ≠ 0 →
      (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) →
      Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.mStarF U) θ = 1) := by
  have hsum := mStarF_scales_sum_le_one hU
  have h1 : ∀ y : ℝ, |y| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) → mStarF U y = 1 :=
    fun y hy => mStarF_eq_one hy
  have h0 : ∀ y : ℝ, (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ |y| → mStarF U y = 0 :=
    fun y hy => mStarF_eq_zero hy
  constructor
  · intro θ hθ
    simp only [Work.BourgainPlan.IonescuWainger.arcSet, Set.mem_setOf_eq] at hθ
    obtain ⟨θ₀, hθ₀le, hθ₀eq⟩ := hθ
    rw [hθ₀eq]
    simpa using periodize_plateau (φ := mStarF U) hsum h1 h0 θ₀ hθ₀le
  · intro φ θ hper hsupp
    obtain ⟨θ₀, hθ₀eq, hθ₀le⟩ := exists_coe_abs_le_of_periodize_ne_zero hsupp hper
    rw [← hθ₀eq]
    exact periodize_plateau (φ := mStarF U) hsum h1 h0 θ₀ hθ₀le

end Work.KMTAreas.A7
