import Submission.NBody.Dominated
import Submission.Commons.Topology.Metric.exists_subseq_tendstoUniformlyOn_compacts_of_equicontinuous
import Submission.Commons.Topology.Metric.exists_bound_of_equicontinuous_compacts
import Mathlib

/-!
# Horofunctions of the `h`-action potential

First step of the "ideal boundary" construction of the paper (Section 3).  Assuming the Hölder
estimate for the `h`-action potential (`thm-phih.estim`),

  `φ_h(x,y) ≤ (α ‖x-y‖ + h β ‖x-y‖²)^{1/2}`,

the functions `u_n(x) = φ_h(x, n·a) - φ_h(0, n·a)` are uniformly bounded on compact sets and
uniformly equicontinuous, hence admit a subsequence converging uniformly on compact sets to a
function `𝔲` which is still dominated by `L + h` and satisfies `𝔲 0 = 0`.

Everything here is fully proved (the Hölder estimate enters as an explicit hypothesis).
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Horofunction extraction.**  Under the Hölder estimate for `φ_h`, the normalised action
potentials `x ↦ φ_h(x, n·a) - φ_h(0, n·a)` have a subsequence converging uniformly on compact
sets, and the limit is still dominated by `L + h` and vanishes at the origin. -/
theorem exists_horofunction {m : Fin N → ℝ} {h : ℝ} (hh : 0 ≤ h) {a : EN E N}
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x y : EN E N, actionPot m h x y ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ 𝔲 : EN E N → ℝ,
      (∀ K : Set (EN E N), IsCompact K → TendstoUniformlyOn
        (fun k x => (actionPot m h x ((φ k : ℝ) • a)).toReal
          - (actionPot m h 0 ((φ k : ℝ) • a)).toReal) 𝔲 atTop K) ∧
      Dominated m h 𝔲 ∧ 𝔲 0 = 0 := by
  classical
  -- finiteness of `φ_h`
  have hfin : ∀ x y : EN E N, actionPot m h x y < ⊤ := fun x y =>
    lt_of_le_of_lt (hest x y) ENNReal.ofReal_lt_top
  -- the pointwise bound `|φ(x,p) - φ(y,p)| ≤ ξ(‖x-y‖)`
  have hmod : ∀ (p x y : EN E N),
      |(actionPot m h x p).toReal - (actionPot m h y p).toReal|
        ≤ Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2) := by
    intro p x y
    have hle1 : (actionPot m h x p).toReal
        ≤ (actionPot m h x y).toReal + (actionPot m h y p).toReal := by
      have hmono := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨(hfin x y).ne, (hfin y p).ne⟩)
        (actionPot_triangle m h x y p)
      rwa [ENNReal.toReal_add (hfin x y).ne (hfin y p).ne] at hmono
    have hle2 : (actionPot m h y p).toReal
        ≤ (actionPot m h y x).toReal + (actionPot m h x p).toReal := by
      have hmono := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨(hfin y x).ne, (hfin x p).ne⟩)
        (actionPot_triangle m h y x p)
      rwa [ENNReal.toReal_add (hfin y x).ne (hfin x p).ne] at hmono
    have hxy : (actionPot m h x y).toReal
        ≤ Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hest x y)
      rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
    have hyx : (actionPot m h y x).toReal
        ≤ Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hest y x)
      rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), norm_sub_rev] at h
      exact h
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  -- a uniform modulus of continuity for `ξ`
  have hmodulus : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : ℝ, 0 ≤ ρ → ρ < δ → Real.sqrt (α * ρ + h * β * ρ ^ 2) < ε := by
    intro ε hε
    have hαβ : 0 ≤ α + h * β := by nlinarith
    have hpos : 0 < 2 * (α + h * β + 1) := by positivity
    refine ⟨min 1 (ε ^ 2 / (2 * (α + h * β + 1))), lt_min one_pos (by positivity), ?_⟩
    intro ρ hρ0 hρ
    have hδ2 : min 1 (ε ^ 2 / (2 * (α + h * β + 1)))
        ≤ ε ^ 2 / (2 * (α + h * β + 1)) := min_le_right _ _
    have hρ1 : ρ ≤ 1 := hρ.le.trans (min_le_left _ _)
    have hρ3 : ρ ≤ ε ^ 2 / (2 * (α + h * β + 1)) := hρ.le.trans hδ2
    have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith [hρ0, hρ1]
    have hmain : α * ρ + h * β * ρ ^ 2 ≤ (α + h * β) * ρ := by
      have := mul_le_mul_of_nonneg_left hρ2 (mul_nonneg hh hβ.le)
      linarith
    have hbound : (α + h * β) * ρ ≤ ε ^ 2 / 2 := by
      refine (mul_le_mul_of_nonneg_left hρ3 hαβ).trans ?_
      rw [mul_div_assoc', div_le_iff₀ hpos]
      nlinarith [sq_nonneg ε, hαβ]
    have hfinal : α * ρ + h * β * ρ ^ 2 ≤ ε ^ 2 / 2 := hmain.trans hbound
    refine lt_of_le_of_lt (Real.sqrt_le_sqrt hfinal) ?_
    rw [Real.sqrt_lt' hε]
    nlinarith [hfinal, hε]
  -- equicontinuity of the sequence
  have heq : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x y : EN E N),
      dist x y < δ → |((actionPot m h x ((n : ℝ) • a)).toReal
        - (actionPot m h 0 ((n : ℝ) • a)).toReal)
        - ((actionPot m h y ((n : ℝ) • a)).toReal
          - (actionPot m h 0 ((n : ℝ) • a)).toReal)| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := hmodulus ε hε
    refine ⟨δ, hδ, fun n x y hxy => ?_⟩
    rw [sub_sub_sub_cancel_right]
    rw [dist_eq_norm] at hxy
    exact lt_of_le_of_lt (hmod _ x y) (hδprop _ (norm_nonneg _) hxy)
  -- Arzelà–Ascoli
  obtain ⟨φ, hφ, 𝔲, h𝔲⟩ :=
    Commons.Topology.Metric.exists_strictMono_tendstoUniformlyOn_compacts_of_equicontinuous_separable
      (u := fun n x => (actionPot m h x ((n : ℝ) • a)).toReal
        - (actionPot m h 0 ((n : ℝ) • a)).toReal)
      (fun K hK => Commons.Topology.Metric.exists_bound_of_equicontinuous_compacts
        (x₀ := 0) (fun n => sub_self _) heq K hK) heq
  refine ⟨φ, hφ, 𝔲, h𝔲, ?_, ?_⟩
  · refine Dominated.of_tendsto (u := fun k x => (actionPot m h x ((φ k : ℝ) • a)).toReal
        - (actionPot m h 0 ((φ k : ℝ) • a)).toReal) (fun k => ?_) (fun x => ?_)
    · exact (dominated_actionPot_toReal (p := (φ k : ℝ) • a) (fun y => (hfin y _).ne)).add_const _
    · refine Metric.tendsto_nhds.mpr fun ε hε => ?_
      have h := (Metric.tendstoUniformlyOn_iff.mp (h𝔲 {x} isCompact_singleton)) ε hε
      filter_upwards [h] with k hk
      simpa only [dist_comm] using hk x (Set.mem_singleton x)
  · have hpt : Tendsto (fun k : ℕ => (actionPot m h 0 ((φ k : ℝ) • a)).toReal
        - (actionPot m h 0 ((φ k : ℝ) • a)).toReal) atTop (𝓝 (𝔲 0)) :=
      Metric.tendsto_nhds.mpr fun ε hε => by
        have h' := (Metric.tendstoUniformlyOn_iff.mp (h𝔲 {0} isCompact_singleton)) ε hε
        filter_upwards [h'] with k hk
        simpa only [dist_comm] using hk 0 (Set.mem_singleton 0)
    have hc : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (𝔲 0)) := by
      simpa only [sub_self] using hpt
    exact tendsto_nhds_unique hc tendsto_const_nhds

end Submission.NBody
