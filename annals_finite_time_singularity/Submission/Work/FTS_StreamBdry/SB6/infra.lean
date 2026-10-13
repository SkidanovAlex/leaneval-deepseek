import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.infra` — elementary helpers for the SB6 rates

`sin 2θ ≤ 2(π/2 - θ)`, the `|·|`-combination lemmas, `M ≥ 0` from `SlotBd`, and the two
one-sided squeezes.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- `s2 θ = sin 2θ ≤ 2(π/2 - θ)` for `θ ≤ π/2`. -/
lemma s2_le_two_mul_sub {θ : ℝ} (hθ : θ ≤ Real.pi / 2) :
    Work.Construction.s2 θ ≤ 2 * (Real.pi / 2 - θ) := by
  rw [Work.Construction.s2_eq]
  have h : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  rw [h]
  exact Real.sin_le (by linarith)

/-- `|a| ≤ A`, `|b| ≤ B`, `|c| ≤ C`, `|d| ≤ D` give `|a + b + c + d| ≤ A + B + C + D`. -/
lemma abs_four_le {a b c d A B C D : ℝ} (h1 : |a| ≤ A) (h2 : |b| ≤ B) (h3 : |c| ≤ C)
    (h4 : |d| ≤ D) : |a + b + c + d| ≤ A + B + C + D := by
  have h12 : |a + b| ≤ A + B := (abs_add_le a b).trans (add_le_add h1 h2)
  have h123 : |a + b + c| ≤ A + B + C := (abs_add_le (a + b) c).trans (add_le_add h12 h3)
  exact (abs_add_le (a + b + c) d).trans (add_le_add h123 h4)

/-- The same for the shape `|a + b - c - d|` in which the identity `pthIter2_eq` is stated. -/
lemma abs_four_sub_le {a b c d A B C D : ℝ} (h1 : |a| ≤ A) (h2 : |b| ≤ B) (h3 : |c| ≤ C)
    (h4 : |d| ≤ D) : |a + b - c - d| ≤ A + B + C + D := by
  have he : a + b - c - d = a + b + (-c) + (-d) := by ring
  rw [he]
  exact abs_four_le h1 h2 (by simpa using h3) (by simpa using h4)

/-- `|a + b + c| ≤ |a| + |b| + |c|`. -/
lemma abs_three_le {a b c : ℝ} : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b| ≤ |a| + |b| := abs_add_le a b
  calc |a + b + c| ≤ |a + b| + |c| := abs_add_le (a + b) c
    _ ≤ |a| + |b| + |c| := by linarith [h1]

/-- `M ≥ 0`, forced by `SlotBd` at any point of the (nonempty) quadrant. -/
lemma M_nonneg {αG M : ℝ} {Ψ : ℝ → ℝ → ℝ} (hslot : SlotBd αG Ψ M) : 0 ≤ M := by
  have h1 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr
      ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact le_trans (abs_nonneg _) (Work.FTS_StreamBdry.SlotBd.Uprime_le hslot h1)

/-- Squeeze at the left endpoint: `|Q θ| ≤ M·s2 θ` near `0` gives `Q θ → 0` as `θ → 0⁺`. -/
lemma tendsto_zero_of_abs_le_s2_left {Q : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Q θ| ≤ M * Work.Construction.s2 θ) :
    Filter.Tendsto Q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hs : Filter.Tendsto (fun θ : ℝ => Work.Construction.s2 θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcont : Continuous (fun θ : ℝ => Work.Construction.s2 θ) := by
      change Continuous fun θ : ℝ => Real.sin (2 * θ)
      fun_prop
    have h0 : Work.Construction.s2 0 = 0 := by
      rw [Work.Construction.s2_eq]; simp
    simpa only [h0] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun θ : ℝ => |Q θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hs.const_mul M)
    · filter_upwards with θ using abs_nonneg _
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))]
        with θ hθ hθ2
      exact h θ ⟨hθ, hθ2⟩
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using h2)

/-- Squeeze at the right endpoint: `|Q θ| ≤ M·s2 θ` near `π/2` gives `Q θ → 0` as `θ → π/2⁻`. -/
lemma tendsto_zero_of_abs_le_s2_right {Q : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Q θ| ≤ M * Work.Construction.s2 θ) :
    Filter.Tendsto Q (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hs : Filter.Tendsto (fun θ : ℝ => Work.Construction.s2 θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hcont : Continuous (fun θ : ℝ => Work.Construction.s2 θ) := by
      change Continuous fun θ : ℝ => Real.sin (2 * θ)
      fun_prop
    have h0 : Work.Construction.s2 (Real.pi / 2) = 0 := by
      rw [Work.Construction.s2_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    simpa only [h0] using (hcont.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun θ : ℝ => |Q θ|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hs.const_mul M)
    · filter_upwards with θ using abs_nonneg _
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))]
        with θ hθ hθ2
      exact h θ ⟨hθ2, hθ⟩
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using h2)


end Work.FTS_StreamBdry.SB6
