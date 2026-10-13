/-
Copyright: work module for the Elgindi finite-time singularity project.

# The assembly of `Work.Blocks.interp_truncation`

This file carries out the *main argument* of the reduction-to-compact-support for the mixed
weighted interpolation estimate, taking as hypotheses the two remaining analytic inputs
(`fourInt_cut`, `cut_functional_le`) together with the three already-proved pieces
(`sliceL2_le`, `zF_abs_le`, `mixInt_Icc_le_cut`).

Route.  Let `ζ_k = zc φ k` be the logarithmic cut-off.  For every `0 < δ < R` and every
`k` with `1/k < δ`, `R < k`:

* `∫_{[δ,R]} w²∫_θ (D_z∂_θ G)²σ ≤ mixInt (ζ_k G)` (`mixInt_Icc_le_cut`), because `ζ_k ≡ 1`
  and `D_zζ_k ≡ 0` on `(1/k, k) ⊇ [δ,R]`;
* `α² mixInt (ζ_k G) ≤ C (α⁴ ddInt (ζ_k G) + ttInt (ζ_k G) + α² dInt (ζ_k G))` by the
  hypothesis, applied to the compactly supported function `ζ_k G` (supported in
  `[1/k², k²]`);
* the functionals of `ζ_k G` are bounded by those of `G` up to an error
  `Ke (ddInt G + dInt G + ttInt G)/log k` (`cut_functional_le`).

Letting `k → ∞` gives `α² ∫_{[δ,R]} ... ≤ C (α⁴ ddInt G + ttInt G + α² dInt G)` for every
`δ < R`, and letting `[δ,R] ↑ (0,∞)` gives the claim.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.interpol_defs
import Submission.Work.Blocks.InterpTruncDefs
import Submission.Work.Blocks.InterpTrunc.sliceL2_le
import Submission.Work.Blocks.InterpTrunc.zF_abs_le
import Submission.Work.Blocks.InterpTrunc.mixInt_Icc_le_cut
import Submission.Work.FTS.EllipticEst.Alpha4.Cut
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_exists
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_props

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

/-- The truncated function `ζ_k G` is smooth on the half-strip. -/
theorem smoothOpenθ_cut {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) :
    Work.FTS.EllipticEst.ThetaU.SmoothOpenθ (cut φ k G) := by
  intro n
  have hζ : ContDiffOn ℝ n (zeta φ k) (Set.Ioi 0) :=
    (zeta_contDiffOn_of_isZCut hφ hk).of_le
      (by simp [Work.FTS.EllipticEst.smoothOrder])
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => zeta φ k p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    simpa [Function.comp_def] using
      ContDiffOn.comp hζ contDiffOn_fst (fun p hp => hp.1)
  have h2 : ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi 0 ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hG n
  refine (h1.mul h2).congr (fun p hp => ?_)
  show zeta φ k p.1 * Function.uncurry G p = Function.uncurry (cut φ k G) p
  rfl

/-- The truncated function vanishes on the angular boundary lines. -/
theorem cut_zero_left {φ : ℝ → ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ} (h0 : ∀ z, G z 0 = 0) (z : ℝ) :
    cut φ k G z 0 = 0 := by
  simp [cut, h0 z]

theorem cut_zero_right {φ : ℝ → ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ}
    (hπ : ∀ z, G z (Real.pi / 2) = 0) (z : ℝ) : cut φ k G z (Real.pi / 2) = 0 := by
  simp [cut, hπ z]

/-- The truncated function is supported in `[1/k², k²]`. -/
theorem cut_support {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) (G : ℝ → ℝ → ℝ) {z : ℝ}
    (hz : z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2)) (θ : ℝ) :
    cut φ k G z θ = 0 := by
  simp [cut, zeta_eq_zero_of_notMem hφ hk hz]

/-- **The assembly of `interp_truncation`.** -/
theorem interp_truncation_aux
    (hfour : ∀ {φ : ℝ → ℝ} {K : ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.IsZCut φ K → 2 ≤ k →
      Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G → Work.FTS.EllipticEst.FourInt (cut φ k G))
    (hcomp : ∀ {φ : ℝ → ℝ} {K : ℝ} {G : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.IsZCut φ K → Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G →
      Work.FTS.EllipticEst.FourInt G → ∀ {Ks Kf : ℝ}, 0 ≤ Ks → 0 ≤ Kf →
      (∀ z : ℝ, 0 < z → inn G z ≤ Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z) →
      ∃ Ke : ℝ, 0 ≤ Ke ∧ ∀ (k : ℕ), 2 ≤ k →
        (∀ z : ℝ, |zF φ k z| ≤ Kf / Real.log k) →
        (Work.FTS.EllipticEst.ttInt (cut φ k G) ≤ Work.FTS.EllipticEst.ttInt G ∧
        Work.FTS.EllipticEst.dInt (cut φ k G) ≤ Work.FTS.EllipticEst.dInt G
          + (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.dInt G
              + Work.FTS.EllipticEst.ttInt G) ∧
        Work.FTS.EllipticEst.ddInt (cut φ k G) ≤ Work.FTS.EllipticEst.ddInt G
          + (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.dInt G
              + Work.FTS.EllipticEst.ttInt G))) :
    ∀ C : ℝ, 0 < C → (∀ (δ R : ℝ), 0 < δ → δ < R → ∀ (α : ℝ) (G : ℝ → ℝ → ℝ),
        0 < α → α ≤ 1 / 4 →
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
          (Set.Ioi 0 ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) →
        (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
        (∀ z : ℝ, z ∉ Set.Icc δ R → ∀ θ : ℝ, G z θ = 0) →
        Work.FTS.EllipticEst.FourInt G →
        α ^ 2 * Work.FTS.EllipticEst.mixInt G
          ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
              + α ^ 2 * Work.FTS.EllipticEst.dInt G)) →
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
        (Set.Ioi 0 ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.FTS.EllipticEst.FourInt G →
      α ^ 2 * Work.FTS.EllipticEst.mixInt G
        ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G) := by
  intro C hCpos hC α G hα hα14 hsmooth h0 hπ hF
  have hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G := hsmooth
  obtain ⟨φ, K, hφK⟩ := Work.FTS.EllipticEst.ZCuts.zCut_exists
  obtain ⟨Ks, hKspos, hKs⟩ := sliceL2_le
  -- the slicewise bound for `G`
  have hSl : ∀ z : ℝ, 0 < z →
      inn G z ≤ Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z := by
    intro z hz
    have hsm : Work.FTS.EllipticEst.ThetaU.SliceSmoothO (fun θ => G z θ) := hG.sliceSmoothO hz
    have h1 := (hKs (fun θ => G z θ) hsm (h0 z) (hπ z)).2
    simpa [inn, Work.Spaces.pth] using h1
  obtain ⟨Kf, hKf0, hKf⟩ := zF_bound_uniform hφK
  obtain ⟨Ke, hKe0, hKe⟩ := hcomp (Kf := Kf) hφK hG hF (le_of_lt hKspos) hKf0 hSl
  -- the per-`k` estimate (for an admissible `k`)
  have step : ∀ (δ R : ℝ), 0 < δ → δ < R → ∀ (k : ℕ), 3 ≤ k →
      1 / (k : ℝ) < δ → R < k →
      α ^ 2 * (∫ z in Set.Icc δ R, sl (Work.Spaces.Dz (Work.Spaces.pth G)) z)
        ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G)
          + C * (2 * ((Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
              + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G))) := by
    intro δ R hδ hR k hk3 hk1 hk2
    have hk2' : 2 ≤ k := by omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have hlog1 : (1 : ℝ) ≤ Real.log k := by
      have h3 : (1 : ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        exact le_of_lt Real.exp_one_lt_three
      exact le_trans h3 (Real.log_le_log (by norm_num) (by exact_mod_cast hk3))
    have hFz : ∀ z : ℝ, |zF φ k z| ≤ Kf / Real.log k := by
      intro z
      have hLpos : 0 < Real.log k := lt_of_lt_of_le one_pos hlog1
      calc |zF φ k z| ≤ Kf / (Real.log k) ^ 2 := hKf k hk2' z
        _ ≤ Kf / Real.log k :=
            div_le_div_of_nonneg_left hKf0 hLpos
              (by simpa using pow_le_pow_right₀ (a := Real.log k) hlog1 (by norm_num : 1 ≤ 2))
    have hcutint : Work.FTS.EllipticEst.FourInt (cut φ k G) := hfour hφK hk2' hG
    have hlow := mixInt_Icc_le_cut hφK hG hF hδ hR hk2' hk1 hk2 hcutint
    have hhC := hC (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2 + 1) (by positivity)
      (by
        have h1 : 1 / (k : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ k))
        have h2 : (1 : ℝ) < (k : ℝ) ^ 2 + 1 := by
          have : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
          linarith
        linarith)
      α (cut φ k G) hα hα14 (smoothOpenθ_cut hφK hk2' hG)
      (cut_zero_left h0) (cut_zero_right hπ)
      (fun z hz θ => cut_support hφK hk2' G
        (fun hc => hz ⟨hc.1, by linarith [hc.2]⟩) θ) hcutint
    obtain ⟨ht1, hd1, hdd1⟩ := hKe k hk2' hFz
    -- combine the three comparison bounds
    have hcomb : α ^ 4 * Work.FTS.EllipticEst.ddInt (cut φ k G)
        + Work.FTS.EllipticEst.ttInt (cut φ k G)
        + α ^ 2 * Work.FTS.EllipticEst.dInt (cut φ k G)
        ≤ (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G)
          + 2 * ((Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
              + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G)) := by
      have hα1 : α ≤ 1 := by linarith
      have hα41 : α ^ 4 ≤ 1 := pow_le_one₀ (n := 4) hα.le hα1
      have hα21 : α ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hα.le hα1
      have he0 : 0 ≤ (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
          + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G) := by
        refine mul_nonneg (div_nonneg hKe0 (le_of_lt (lt_of_lt_of_le one_pos hlog1))) ?_
        linarith [Work.Blocks.InterpTrunc.ddInt_nonneg G,
          Work.Blocks.InterpTrunc.dInt_nonneg G, Work.Blocks.InterpTrunc.ttInt_nonneg G]
      have e1 : α ^ 4 * Work.FTS.EllipticEst.ddInt (cut φ k G)
          ≤ α ^ 4 * (Work.FTS.EllipticEst.ddInt G + (Ke / Real.log k)
              * (Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.dInt G
                + Work.FTS.EllipticEst.ttInt G)) :=
        mul_le_mul_of_nonneg_left hdd1 (by positivity)
      have e2 : α ^ 2 * Work.FTS.EllipticEst.dInt (cut φ k G)
          ≤ α ^ 2 * (Work.FTS.EllipticEst.dInt G + (Ke / Real.log k)
              * (Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.dInt G
                + Work.FTS.EllipticEst.ttInt G)) :=
        mul_le_mul_of_nonneg_left hd1 (by positivity)
      nlinarith [e1, e2, ht1, hα41, hα21, he0]
    calc α ^ 2 * (∫ z in Set.Icc δ R, sl (Work.Spaces.Dz (Work.Spaces.pth G)) z)
        ≤ α ^ 2 * Work.FTS.EllipticEst.mixInt (cut φ k G) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt (cut φ k G)
            + Work.FTS.EllipticEst.ttInt (cut φ k G)
            + α ^ 2 * Work.FTS.EllipticEst.dInt (cut φ k G)) := hhC
      _ ≤ C * ((α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G)
          + 2 * ((Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
              + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G))) :=
          mul_le_mul_of_nonneg_left hcomb hCpos.le
      _ = C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G)
          + C * (2 * ((Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
              + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G))) := by ring
  -- the `δ,R`-limit
  have main : ∀ δ R : ℝ, 0 < δ → δ < R →
      α ^ 2 * (∫ z in Set.Icc δ R, sl (Work.Spaces.Dz (Work.Spaces.pth G)) z)
        ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G) := by
    intro δ R hδ hR
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max (1 / δ) R)
    have hk₀1 : (1 : ℝ) / δ < (k₀ : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk₀
    have hk₀R : R < (k₀ : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk₀
    have hk₀pos : (0 : ℝ) < (k₀ : ℝ) := by
      have : (0 : ℝ) < 1 / δ := by positivity
      linarith
    have h1k₀ : (1 : ℝ) / (k₀ : ℝ) < δ := by
      rw [div_lt_iff₀ hk₀pos]
      rw [div_lt_iff₀ hδ] at hk₀1
      linarith
    have htendlog : Filter.Tendsto (fun k : ℕ => Real.log k) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have htend : Filter.Tendsto
        (fun k : ℕ => C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G
              + Work.FTS.EllipticEst.ttInt G + α ^ 2 * Work.FTS.EllipticEst.dInt G)
            + C * (2 * ((Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
                + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G))))
        Filter.atTop
        (nhds (C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G))) := by
      have h1 : Filter.Tendsto (fun k : ℕ => Ke / Real.log k) Filter.atTop (nhds 0) :=
        htendlog.const_div_atTop Ke
      have h2 : Filter.Tendsto (fun k : ℕ => (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
            + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G))
          Filter.atTop (nhds 0) := by
        simpa using h1.mul_const (Work.FTS.EllipticEst.ddInt G
          + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G)
      have h4 : Filter.Tendsto (fun k : ℕ => C * (2 * ((Ke / Real.log k)
            * (Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.dInt G
              + Work.FTS.EllipticEst.ttInt G))))
          Filter.atTop (nhds 0) := by
        have h3 := h2.const_mul (2 : ℝ)
        simpa using h3.const_mul C
      have h5 : Filter.Tendsto
          (fun k : ℕ => C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G
                + Work.FTS.EllipticEst.ttInt G + α ^ 2 * Work.FTS.EllipticEst.dInt G)
              + C * (2 * ((Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
                  + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G))))
          Filter.atTop
          (nhds (C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
              + α ^ 2 * Work.FTS.EllipticEst.dInt G) + 0)) :=
        tendsto_const_nhds.add h4
      simpa using h5
    refine ge_of_tendsto htend ?_
    filter_upwards [Filter.eventually_ge_atTop (max 3 (k₀ + 1))] with k hk
    have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
    have hkn : k₀ + 1 ≤ k := le_trans (le_max_right _ _) hk
    have h1k : (1 : ℝ) / (k : ℝ) < δ := by
      have hle : (1 : ℝ) / (k : ℝ) ≤ 1 / (k₀ : ℝ) := by
        refine one_div_le_one_div_of_le hk₀pos ?_
        have hlt : k₀ < k := by omega
        exact_mod_cast hlt.le
      linarith
    have hRk : R < (k : ℝ) := by
      have hlt : k₀ < k := by omega
      have : (k₀ : ℝ) < (k : ℝ) := by exact_mod_cast hlt
      linarith
    exact step δ R hδ hR k hk3 h1k hRk
  -- the final limit over the inner regions
  have hfin : α ^ 2 * (∫ z in Work.Spaces.Iz, sl (Work.Spaces.Dz (Work.Spaces.pth G)) z)
      ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
          + α ^ 2 * Work.FTS.EllipticEst.dInt G) := by
    have hmono : Monotone (fun n : ℕ => Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
      intro a b hab z hz
      simp only [Set.mem_Icc] at hz ⊢
      have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        linarith
      exact ⟨le_trans (one_div_le_one_div_of_le (by positivity) hab') hz.1,
        le_trans hz.2 hab'⟩
    have hUnion : (⋃ n : ℕ, Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) = Set.Ioi 0 := by
      apply Set.Subset.antisymm
      · intro z hz
        simp only [Set.mem_iUnion, Set.mem_Icc] at hz
        obtain ⟨n, hn1, -⟩ := hz
        exact lt_of_lt_of_le (by positivity) hn1
      · intro z hz
        simp only [Set.mem_iUnion, Set.mem_Icc]
        obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / z) z)
        have hn1 : 1 / z < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
        have hn2 : z < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
        refine ⟨n, ?_, ?_⟩
        · rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
          rw [div_lt_iff₀ hz] at hn1
          nlinarith
        · linarith
    have hintU : MeasureTheory.IntegrableOn (sl (Work.Spaces.Dz (Work.Spaces.pth G)))
        (⋃ n : ℕ, Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) MeasureTheory.volume := by
      rw [hUnion]
      change MeasureTheory.Integrable (sl (Work.Spaces.Dz (Work.Spaces.pth G)))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      have h1 : MeasureTheory.Integrable (sl (Work.Spaces.Dz (Work.Spaces.pth G)))
          (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) := ((fourInt_iff G).mp hF).1
      rwa [show MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
          = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
        (MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm] at h1
    have htend := MeasureTheory.tendsto_setIntegral_of_monotone
      (f := sl (Work.Spaces.Dz (Work.Spaces.pth G)))
      (s := fun n : ℕ => Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1))
      (fun n => measurableSet_Icc) hmono hintU
    rw [hUnion] at htend
    have hlim2 : Filter.Tendsto (fun n : ℕ =>
        ∫ z in Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1),
          sl (Work.Spaces.Dz (Work.Spaces.pth G)) z)
        Filter.atTop (nhds (∫ z in Work.Spaces.Iz,
          sl (Work.Spaces.Dz (Work.Spaces.pth G)) z)) := by
      rw [show (∫ z in Work.Spaces.Iz, sl (Work.Spaces.Dz (Work.Spaces.pth G)) z)
          = ∫ z in Set.Ioi (0 : ℝ), sl (Work.Spaces.Dz (Work.Spaces.pth G)) z from
        MeasureTheory.setIntegral_congr_set
          (show Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) from by
            rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
            exact (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume)
              (a := (0 : ℝ))).symm)]
      exact htend
    refine le_of_tendsto (hlim2.const_mul (α ^ 2)) ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hδ' : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hR' : 1 / ((n : ℝ) + 1) < (n : ℝ) + 1 := by
      rw [div_lt_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith
    exact main (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) hδ' hR'
  rwa [mixInt_eq_int_sl]

end Work.Blocks.InterpTrunc
