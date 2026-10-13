/-
# `L12_tendsto_locUnif` — from the box-uniform bound to the convergence

If a sequence of `ℋ⁰`-data `D n` with a uniform `HkSq α 0`-bound has weighted data `Gaz (D n)`
tending to `0` uniformly on every box `[δ,R] × [ε,π/2-ε]`, then the `L₁₂`-functional at any
`z ≥ 0` tends to `0`.  The proof is the final `ε`-argument on top of `L12_master_bound`: `δ → 0`
kills the near-zero term, `R → ∞` the far term, `ε → 0` the angular end-terms, and the
box-uniform smallness the middle term.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.L12.LocUnifMaster
import Submission.Work.FTS.StrongEps.L12.EndsBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## From the box-uniform bound to the convergence of the functional -/

theorem L12_tendsto_zero_of_GazBox {α : ℝ} {D : ℕ → ℝ → ℝ → ℝ} {C : ℝ}
    (hmem : ∀ n, Work.Spaces.HkMem α 0 (D n))
    (hbd : ∀ n, Work.Spaces.HkSq α 0 (D n) ≤ C) (hC : 0 ≤ C)
    (hGazBox : ∀ δ R ε : ℝ, 0 < δ → δ ≤ R → 0 < ε → ε ≤ Real.pi / 4 → ∀ η > 0,
      ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Set.Icc δ R, ∀ θ ∈ Set.Icc ε (Real.pi / 2 - ε),
        |Work.FTS.GalBasis.cc.Gaz (D n) s θ| ≤ η)
    {z : ℝ} (hz : 0 ≤ z) :
    Filter.Tendsto (fun n => Work.Construction.L12 (D n) z) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro η₀ hη₀
  obtain ⟨K2, hK2nn, hK2⟩ := EndsBound
  obtain ⟨δ, hδpos, hδ1, hδsmall⟩ :=
    exists_delta_small (K := Work.FTS.GalBasis.cc.BK * Real.sqrt C) (η := η₀ / 4)
      (mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg (Real.sqrt_nonneg C)) (by positivity)
  obtain ⟨R, hR1, hRsmall⟩ :=
    exists_R_large (K := Work.FTS.GalBasis.cc.BK * Real.sqrt C) (η := η₀ / 4)
      (mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg (Real.sqrt_nonneg C)) (by positivity)
  have hδR : δ ≤ R := le_trans hδ1 hR1
  obtain ⟨ε, hεpos, hεlt, hεsmall⟩ :=
    exists_eps_small (K := Real.sqrt K2 * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C)
      (η := η₀ / 4) (by positivity) (by positivity)
  have hε4 : ε ≤ Real.pi / 4 := le_of_lt hεlt
  set T4c : ℝ := angKSw * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s) with hT4c
  have hT4cnn : 0 ≤ T4c := by
    rw [hT4c]
    exact mul_nonneg angKSw_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun s hs => Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_of_lt_of_le hδpos hs.1))))
  obtain ⟨N, hN⟩ := hGazBox δ R ε hδpos hδR hεpos hε4
    (η₀ / (4 * (T4c + 1))) (div_pos hη₀ (by linarith))
  refine ⟨N, fun n hn => ?_⟩
  have hbox := hN n hn
  have hmaster := L12_master_bound (α := α) (D := D n) (C := C) (δ := δ) (R := R) (ε := ε)
    (η := η₀ / (4 * (T4c + 1))) (hmem n) (hbd n) hC hδpos hδR hεpos hε4
    (le_of_lt (div_pos hη₀ (by linarith))) hbox hz
  have hT1 : Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (δ ^ 3) < η₀ / 4 := by
    have h3 : δ ^ 3 ≤ δ := by
      have h2 : δ ^ 2 ≤ 1 := by nlinarith [hδpos, hδ1]
      calc δ ^ 3 = δ * δ ^ 2 := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h2 hδpos.le
        _ = δ := mul_one δ
    have h1 : Real.sqrt (δ ^ 3) ≤ Real.sqrt δ := Real.sqrt_le_sqrt h3
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left h1
        (mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg (Real.sqrt_nonneg C))) hδsmall
  have hT2 : Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (1 / (1 + R)) < η₀ / 4 :=
    hRsmall
  have hT3 : Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C < η₀ / 4 := by
    have h1 : angEnd ε ≤ K2 * ε := hK2 ε ⟨hεpos, hεlt⟩
    have h2 : Real.sqrt (angEnd ε) ≤ Real.sqrt K2 * Real.sqrt ε := by
      rw [← Real.sqrt_mul hK2nn]
      exact Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C
        ≤ Real.sqrt K2 * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C * Real.sqrt ε := by
      calc Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C
          ≤ (Real.sqrt K2 * Real.sqrt ε) * Real.sqrt Work.FTS.GalBasis.cc.W2
              * Real.sqrt C :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        _ = Real.sqrt K2 * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C
              * Real.sqrt ε := by ring
    exact lt_of_le_of_lt h3 hεsmall
  have hT4 : η₀ / (4 * (T4c + 1)) * angKSw
      * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s) < η₀ / 4 := by
    have hprod : η₀ / (4 * (T4c + 1))
        * (angKSw * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s))
        = η₀ * T4c / (4 * (T4c + 1)) := by
      rw [← hT4c]
      ring
    calc η₀ / (4 * (T4c + 1)) * angKSw
          * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s)
        = η₀ / (4 * (T4c + 1))
            * (angKSw * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s)) := by ring
      _ = η₀ * T4c / (4 * (T4c + 1)) := hprod
      _ < η₀ / 4 := by
          have hb : (0 : ℝ) < 4 * (T4c + 1) := by linarith
          rw [div_lt_iff₀ hb]
          nlinarith [hT4cnn, hη₀]
  have hm' : |Work.Construction.L12 (D n) z| ≤
      Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (δ ^ 3)
        + Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (1 / (1 + R))
        + Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C
        + η₀ / (4 * (T4c + 1)) * angKSw
          * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s) := by
    simpa only [Real.norm_eq_abs] using hmaster
  rw [Real.dist_eq, sub_zero]
  linarith [hm', hT1, hT2, hT3, hT4]

end Work.FTS.StrongEps.L12
