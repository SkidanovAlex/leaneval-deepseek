import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.ClassC.HonestCut.EDL.Step.lzCauchyBound
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

theorem TraceOfOsc {u : ℝ → ℝ} {γ K : ℝ} (hγ : 0 < γ - 1) (hK : 0 ≤ K)
    (hbound : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 4 →
      |u b - u a| ≤ K * (Real.sin (2 * b)) ^ ((γ - 1) / 2)) :
    ∃ mu : ℝ, Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 4),
        (u θ - mu) ^ 2 ≤ K ^ 2 * (Real.sin (2 * θ)) ^ (γ - 1) := by
  have hp : 0 < (γ - 1) / 2 := by linarith
  -- `x ↦ x ^ ((γ-1)/2)` tends to `0` at `0⁺`
  have hxpow : Filter.Tendsto (fun x : ℝ => x ^ ((γ - 1) / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-((γ - 1) / 2)))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith)
    have h2 : Filter.Tendsto (fun x : ℝ => (x ^ (-((γ - 1) / 2)))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      h1.inv_tendsto_atTop
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.rpow_neg (le_of_lt hx), inv_inv]
  have hle1 : (0 : ℝ) < Real.pi / 2 := by positivity
  -- hence `sin (2x) ^ ((γ-1)/2) → 0` at `0⁺`
  have hsinlim : Filter.Tendsto (fun x : ℝ => Real.sin (2 * x) ^ ((γ - 1) / 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero' (f := fun x : ℝ => Real.sin (2 * x) ^ ((γ - 1) / 2))
      (g := fun x : ℝ => 2 ^ ((γ - 1) / 2) * x ^ ((γ - 1) / 2)) ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hle1)]
        with x hx1 hx2
      have hx1' : (0 : ℝ) < x := hx1
      have hx2' : x < Real.pi / 2 := hx2
      exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_pos])) _
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hle1)]
        with x hx1 hx2
      have hx1' : (0 : ℝ) < x := hx1
      have hx2' : x < Real.pi / 2 := hx2
      have hs0 : 0 ≤ Real.sin (2 * x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
      have hle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith)
      calc Real.sin (2 * x) ^ ((γ - 1) / 2) ≤ (2 * x) ^ ((γ - 1) / 2) :=
            Real.rpow_le_rpow hs0 hle (le_of_lt hp)
        _ = 2 ^ ((γ - 1) / 2) * x ^ ((γ - 1) / 2) :=
            Real.mul_rpow (by norm_num) (le_of_lt hx1')
    · simpa using hxpow.const_mul (2 ^ ((γ - 1) / 2))
  -- the `ε`-`δ` form of the same limit
  have hdelta : ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.pi / 4 ∧
      ∀ t : ℝ, 0 < t → t < δ → K * Real.sin (2 * t) ^ ((γ - 1) / 2) < ε := by
    intro ε hε
    have hg : Filter.Tendsto (fun t : ℝ => K * Real.sin (2 * t) ^ ((γ - 1) / 2))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using hsinlim.const_mul K
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hg) ε hε
    refine ⟨min δ (Real.pi / 4), lt_min hδpos (by positivity), min_le_right _ _,
      fun t ht hlt => ?_⟩
    have htδ : t < δ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hd : dist t 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact htδ
    have h1 := hδ ht hd
    rw [Real.dist_eq, sub_zero] at h1
    have hsin_nonneg : 0 ≤ Real.sin (2 * t) ^ ((γ - 1) / 2) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [hlt, min_le_right δ (Real.pi / 4), Real.pi_pos])) _
    rwa [abs_of_nonneg (mul_nonneg hK hsin_nonneg)] at h1
  have hne : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := nhdsWithin_Ioi_neBot le_rfl
  -- `u` is Cauchy along `𝓝[>] 0`
  have hCauchy : Cauchy (Filter.map u (nhdsWithin 0 (Set.Ioi 0))) := by
    rw [Metric.cauchy_iff]
    refine ⟨hne.map u, ?_⟩
    intro ε hε
    obtain ⟨δ, hδpos, hδle, hδ⟩ := hdelta ε hε
    refine ⟨u '' (Set.Ioo 0 δ), ?_, ?_⟩
    · rw [Filter.mem_map]
      refine Filter.mem_of_superset ?_ (fun x hx => ⟨x, hx, rfl⟩)
      exact Filter.inter_mem self_mem_nhdsWithin
        (nhdsWithin_le_nhds (Iio_mem_nhds hδpos))
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have ha' : (0 : ℝ) < a := ha.1
      have hb' : (0 : ℝ) < b := hb.1
      have haπ : a < Real.pi / 4 := lt_of_lt_of_le ha.2 hδle
      have hbπ : b < Real.pi / 4 := lt_of_lt_of_le hb.2 hδle
      rcases le_total a b with hab | hba
      · rw [Real.dist_eq, abs_sub_comm]
        exact lt_of_le_of_lt (hbound a b ha' hab hbπ) (hδ b hb' hb.2)
      · rw [Real.dist_eq]
        exact lt_of_le_of_lt (hbound b a hb' hba haπ) (hδ a ha' ha.2)
  obtain ⟨mu, hmu⟩ := cauchy_map_iff_exists_tendsto.mp hCauchy
  refine ⟨mu, hmu, ?_⟩
  intro θ hθ
  obtain ⟨hθ0, hθlt⟩ := hθ
  -- pass the pointwise bound to the limit
  have hmem : Set.Ioo (0 : ℝ) θ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hθ0))
  have hev : ∀ᶠ a in (nhdsWithin (0 : ℝ) (Set.Ioi 0)),
      |u θ - u a| ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) := by
    filter_upwards [hmem] with a ha
    exact hbound a θ ha.1 (le_of_lt ha.2) hθlt
  have htend : Filter.Tendsto (fun a : ℝ => |u θ - u a|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds |u θ - mu|) :=
    (tendsto_const_nhds.sub hmu).abs
  have hleval : |u θ - mu| ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) :=
    le_of_tendsto htend hev
  have hsinθ_nonneg : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθlt, Real.pi_pos])
  have hc_nonneg : 0 ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) :=
    mul_nonneg hK (Real.rpow_nonneg hsinθ_nonneg _)
  have hsq : (u θ - mu) ^ 2 ≤ (K * Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2 := by
    rw [sq_le_sq]
    rwa [abs_of_nonneg hc_nonneg]
  have hkey : (K * Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2
      = K ^ 2 * Real.sin (2 * θ) ^ (γ - 1) := by
    have hsθ_pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθlt, Real.pi_pos])
    have hsqp : (Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2
        = Real.sin (2 * θ) ^ (γ - 1) := by
      rw [pow_two, ← Real.rpow_add hsθ_pos ((γ - 1) / 2) ((γ - 1) / 2),
        show (γ - 1) / 2 + (γ - 1) / 2 = γ - 1 by ring]
    rw [mul_pow, hsqp]
  rw [hkey] at hsq
  exact hsq

end Work.FTS.StrongEps.EpsLocalPStar
