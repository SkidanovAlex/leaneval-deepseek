import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue.exists_refCoord
import Submission.Work.FlowerGlue.Model

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.exists_refData_rootParabolic`

The reference attracting Fatou coordinate of a root-parabolic parameter, bundled with its germ
data and its asymptotic `φ = approxCoord (1 - a_f) (chart) + O(1/Re chart)`.

This is the bundling requested as item (FG-a) of `NOTES_LEAD_mandelbar_implosion.md` §3.2: the
*construction* of `Work.FlowerGlue.exists_refCoord` (the germ normal form `u ↦ z₁ + lam · u`,
the half-plane petal of the parabolic chart, the chart Fatou coordinate `fatouCoordW f (1 - a)`)
together with the quantitative estimate `Work.FatouCoord.Exist.fatouCoordW_tsum_bound`.  The two
extra requirements of `RefData` — the half-plane containment `mem_P` and the asymptotic `asymp` —
are proved here for the *explicit* witness, by re-running the construction and recording the
level `max M N_tsum` at which the half-plane petal has both properties.
-/

open scoped Topology
open Set Filter Function Metric

namespace Work.FlowerGlue2

open Work.FatouCoord (chart wMap ParabolicBounds fatouCoordW Petal)
open Work.FatouCoordFix (HPlanePetal HPlanePetalAt)

noncomputable section

theorem exists_refData_rootParabolic {c : ℂ} (d : Work.EL.RootParabolic c) :
    Nonempty (Work.FlowerGlue2.RefData d) := by
  open LeanEval.ComplexAnalysis in
  -- ### 0. the fixed point data of `F c = (T_c)^{10}`
  have hTsq : Work.Landing.Tsq c = (LeanEval.ComplexAnalysis.Tantibar c)^[2] := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add (LeanEval.ComplexAnalysis.Tantibar c) 1 1,
      Function.iterate_one]
    funext z
    simp [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow]
  have hfix : Work.EL.F c d.z₁ = d.z₁ := by
    show (Work.Landing.Tsq c)^[5] d.z₁ = d.z₁
    rw [hTsq, ← Function.iterate_mul, show (2 : ℕ) * 5 = 10 from rfl,
      show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply, d.per_half, d.per_half]
  have hFdiff : Differentiable ℂ (Work.EL.F c) := by
    show Differentiable ℂ (Work.Landing.Tsq c)^[5]
    have h : Differentiable ℂ (Work.Landing.Tsq c) := by
      have he : Work.Landing.Tsq c = fun z : ℂ => (z ^ 2 + star c) ^ 2 + c := rfl
      rw [he]; fun_prop
    exact h.iterate 5
  have hderiv1 : deriv (Work.EL.F c) d.z₁ = 1 := d.mult
  have hsimple : iteratedDeriv 2 (Work.EL.F c) d.z₁ ≠ 0 := d.simple
  -- ### 1. the parabolic germ of `F c` at `z₁`
  obtain ⟨f, h, a, r, A, A', lam, hlam, hb, hfeq⟩ :=
    Work.FatouCoord.Flower.germ_bounds (F := Work.EL.F c) (z₀ := d.z₁)
      hFdiff hfix hderiv1 hsimple
  obtain ⟨Nt, Kt, hNtpos, _hrNt, hKtnn, hbnd⟩ :=
    Work.FatouCoord.Exist.fatouCoordW_tsum_bound hb
  -- ### 2. the thresholds of the `fatouCoordW` theory
  obtain ⟨N_d, hNdpos, hNdr, hdiff⟩ := Work.FatouCoord.Exist.fatouCoordW_differentiable hb
  obtain ⟨N_c, hNcpos, hNcr, hder⟩ := Work.FatouCoord.Exist.fatouCoordW_deriv_close hb
  obtain ⟨N_i, hNipos, hNir, hinj⟩ := Work.FatouCoord.Exist.fatouCoordW_injOn hb
  obtain ⟨N_a, hNapos, hNar, habel⟩ := Work.FatouCoord.Exist.fatouCoordW_abel hb
  obtain ⟨Mg, hMg⟩ := Work.FlowerGlue.exists_mapsTo_HPlanePetal hb
  obtain ⟨Mt, hMt⟩ := Work.FlowerGlue.exists_tendsto_HPlanePetal hb
  obtain ⟨Me, hMe⟩ := Work.FlowerGlue.exists_enters_HPlanePetal hb
  -- ### 3. the level `M` of the half-plane petal
  set X1 : ℝ := max (N_d + 1) (N_c + 1) with hX1def
  set X2 : ℝ := max (N_i + 1) (N_a + 1) with hX2def
  set Y1 : ℝ := max (Mg + 1) (Mt + 1) with hY1def
  set Y2 : ℝ := max (Me + 1) (1 / r + 1) with hY2def
  set M : ℝ := max (max X1 X2) (max Y1 Y2) with hMdef
  have hNd1 : N_d + 1 ≤ M :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hNc1 : N_c + 1 ≤ M :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hNi1 : N_i + 1 ≤ M :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hNa1 : N_a + 1 ≤ M :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hMg1 : Mg + 1 ≤ M :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hMt1 : Mt + 1 ≤ M :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hMe1 : Me + 1 ≤ M :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hMr1 : 1 / r + 1 ≤ M :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hMNd : N_d < M := by linarith
  have hMNc : N_c < M := by linarith
  have hMNi : N_i < M := by linarith
  have hMNa : N_a < M := by linarith
  have hMMg : Mg ≤ M := by linarith
  have hMMt : Mt ≤ M := by linarith
  have hMMe : Me ≤ M := by linarith
  have hMr : 1 / r < M := by linarith
  have hMpos : 0 < M := lt_trans (one_div_pos.mpr hb.hr) hMr
  have hMnn : 0 ≤ M := le_of_lt hMpos
  -- ### 4. the conjugacy on the ball
  have hconjfun : ∀ u : ℂ, ‖u‖ < r →
      Work.EL.F c (d.z₁ + lam * u) = d.z₁ + lam * f u := by
    intro u hu
    have hu' : u ∈ Metric.ball 0 r := by rwa [Metric.mem_ball, dist_zero_right]
    have h1 := hfeq u hu'
    have hkey : lam * ((Work.EL.F c (d.z₁ + lam * u) - d.z₁) / lam)
        = Work.EL.F c (d.z₁ + lam * u) - d.z₁ := by
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm lam (Work.EL.F c (d.z₁ + lam * u) - d.z₁),
        mul_assoc, mul_inv_cancel₀ hlam, mul_one]
    rw [h1, hkey]
    ring
  have hHPball : ∀ u : ℂ, u ∈ HPlanePetal M → ‖u‖ < r := by
    intro u hu
    have h1 : M * ‖u‖ < 1 := Work.FatouCoordFix.HPetal.HPlanePetal_mul_norm_lt hu
    have h2 : ‖u‖ < 1 / M := by
      rw [lt_div_iff₀ hMpos, mul_comm]; exact h1
    have h3 : 1 / M < r := by
      rw [div_lt_iff₀ hMpos, mul_comm r M]
      exact (div_lt_iff₀ hb.hr).mp hMr
    exact h2.trans h3
  -- ### 5. the reference petal and coordinate
  set P : Set ℂ := Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam '' HPlanePetal M with hPdef
  set φ : ℂ → ℂ :=
    fun z => fatouCoordW f (1 - a) (chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z))
      with hφdef
  have hMmap : MapsTo f (HPlanePetal M) (HPlanePetal M) := hMg M hMMg
  have hMtend : ∀ u ∈ HPlanePetal M, Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) := hMt M hMMt
  have hMent : ∀ u : ℂ, Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) →
      (∀ n : ℕ, f^[n] u ≠ 0) → ∃ n : ℕ, f^[n] u ∈ HPlanePetal M := hMe M hMMe

  -- ### 6. the two extra requirements of `RefData`
  have hconj : ∀ u ∈ Metric.ball 0 r,
      Work.EL.F c (d.z₁ + lam * u) = d.z₁ + lam * f u :=
    fun u hu => hconjfun u (by simpa [Metric.mem_ball, dist_zero_right] using hu)
  have hmemP : ∀ z : ℂ, z ≠ d.z₁ → max M Nt < (-lam / (z - d.z₁)).re → z ∈ P := by
    intro z hz hN
    have hw : M < (-lam / (z - d.z₁)).re := lt_of_le_of_lt (le_max_left _ _) hN
    have hPeq : P = Work.FatouCoordFix.HPlanePetalAt d.z₁ lam M := by
      rw [hPdef]
      exact (Work.FatouCoordFix.HPlanePetalAt_eq_image hlam).symm
    rw [hPeq, Work.FatouCoordFix.mem_HPlanePetalAt]
    exact ⟨hz, by simpa only [neg_div] using hw⟩
  have hasymp : ∀ z : ℂ, z ≠ d.z₁ → max M Nt < (-lam / (z - d.z₁)).re →
      ‖φ z - Work.FatouCoord.approxCoord (1 - a) (-lam / (z - d.z₁))‖
        ≤ Kt / (-lam / (z - d.z₁)).re := by
    intro z hz hN
    have hNt : Nt < (-lam / (z - d.z₁)).re := lt_of_le_of_lt (le_max_right _ _) hN
    have hchart : chart ((z - d.z₁) / lam) = -lam / (z - d.z₁) := by
      rw [show chart = fun w : ℂ => (-1 : ℂ) * w⁻¹ from by
        funext w; rw [Work.FatouCoord.chart]; ring]
      field_simp
    have hφz : φ z = fatouCoordW f (1 - a) (-lam / (z - d.z₁)) := by
      rw [hφdef]
      show fatouCoordW f (1 - a)
        (chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)) = _
      rw [Work.FatouCoordFix.FlowerFix.trChartInv_apply, hchart]
    rw [hφz]
    exact hbnd _ hNt
  refine ⟨⟨⟨P, φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    lam, a, f, h, r, A, A', hlam, hb, hconj, max M Nt, Kt,
    lt_of_lt_of_le hMpos (le_max_left _ _), hKtnn, hmemP, hasymp⟩⟩
  · -- isOpen
    rw [hPdef]
    rw [show Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam '' HPlanePetal M
        = Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam ⁻¹' HPlanePetal M from by
      ext z; exact Work.FatouCoordFix.FlowerFix.mem_trChart_image hlam]
    exact (Work.FatouCoordFix.HPetal.HPlanePetal_isOpen M).preimage
      (Work.FatouCoordFix.FlowerFix.continuous_trChartInv d.z₁ lam)
  · -- mapsTo
    rw [hPdef]
    intro z hz
    rw [Work.FatouCoordFix.FlowerFix.mem_trChart_image hlam] at hz ⊢
    set u := Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z with hudef
    have hz_eq : z = Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam u := by
      rw [hudef]; exact (Work.FatouCoordFix.FlowerFix.trChart_trChartInv hlam z).symm
    have hconj : Work.EL.F c z = Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam (f u) := by
      rw [hz_eq]
      exact hconjfun u (hHPball u hz)
    rw [hconj, Work.FatouCoordFix.FlowerFix.trChartInv_trChart hlam]
    exact hMmap hz
  · -- z₁_not_mem
    rw [hPdef]
    intro hz
    rw [Work.FatouCoordFix.FlowerFix.mem_trChart_image hlam] at hz
    have h0 : Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam d.z₁ = 0 := by
      rw [Work.FatouCoordFix.FlowerFix.trChartInv_apply]
      simp
    rw [h0] at hz
    exact hz.1 rfl
  · -- tendsto
    rw [hPdef]
    intro z hz
    rw [Work.FatouCoordFix.FlowerFix.mem_trChart_image hlam] at hz
    set u := Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z with hudef
    have hz_eq : z = d.z₁ + lam * u := (Work.FatouCoordFix.FlowerFix.trChart_trChartInv hlam z).symm
    have hlimu : Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) := hMtend u hz
    have hiter := Work.FlowerGlue.iterate_conj_of_mapsTo (F := Work.EL.F c) (f := f) (z₀ := d.z₁) (lam := lam)
      (S := HPlanePetal M) (r := r) (fun _ hv => Metric.mem_ball.mpr (by
          simpa [dist_zero_right] using hHPball _ hv))
      hMmap (fun u hu => hconjfun u (by rwa [Metric.mem_ball, dist_zero_right] at hu)) u hz
    have h1 : Tendsto (fun n : ℕ => d.z₁ + lam * (f^[n] u)) atTop (nhds (d.z₁ + lam * 0)) :=
      tendsto_const_nhds.add (hlimu.const_mul lam)
    have h1' : Tendsto (fun n : ℕ => d.z₁ + lam * (f^[n] u)) atTop (nhds d.z₁) := by
      simpa using h1
    rw [hz_eq]
    exact Filter.Tendsto.congr' (Eventually.of_forall fun n => (hiter n).symm) h1'
  · -- enters
    intro z ht hne
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp ht (‖lam‖ * r)
      (mul_pos (norm_pos_iff.mpr hlam) hb.hr)
    set u : ℕ → ℂ :=
      fun n => Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam ((Work.EL.F c)^[n] z) with hudef
    have hu_ball : ∀ n ≥ N₀, ‖u n‖ < r := by
      intro n hn
      have h1 := hN₀ n hn
      rw [dist_eq_norm] at h1
      show ‖((Work.EL.F c)^[n] z - d.z₁) / lam‖ < r
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr hlam), mul_comm r ‖lam‖]
      exact h1
    have hu_ne : ∀ n : ℕ, u n ≠ 0 := by
      intro n hn
      have h1 : ((Work.EL.F c)^[n] z - d.z₁) / lam = 0 := hn
      rw [div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · exact hne n (sub_eq_zero.mp h1)
      · exact hlam h1
    have hu_lim : Tendsto u atTop (nhds 0) := by
      have hc : ContinuousAt (fun w : ℂ => (w - d.z₁) / lam) d.z₁ :=
        ((continuous_id.sub continuous_const).div_const lam).continuousAt
      have h1 := hc.tendsto.comp ht
      have h2 : (d.z₁ - d.z₁) / lam = 0 := by simp
      rw [h2] at h1
      exact h1
    have hu_step : ∀ n ≥ N₀, u (n + 1) = f (u n) := by
      intro n hn
      have h1 : (Work.EL.F c)^[n] z = Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam (u n) :=
        (Work.FatouCoordFix.FlowerFix.trChart_trChartInv hlam ((Work.EL.F c)^[n] z)).symm
      have h2 : (Work.EL.F c)^[n + 1] z = Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam (f (u n)) := by
        rw [Function.iterate_succ_apply', h1]
        exact hconjfun (u n) (hu_ball n hn)
      show Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam ((Work.EL.F c)^[n + 1] z) = f (u n)
      rw [h2, Work.FatouCoordFix.FlowerFix.trChartInv_trChart hlam]
    have hu_iter : ∀ k : ℕ, u (N₀ + k) = f^[k] (u N₀) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show N₀ + (k + 1) = (N₀ + k) + 1 from by omega,
          hu_step (N₀ + k) (Nat.le_add_right N₀ k), ih, Function.iterate_succ_apply']
    have ht' : Tendsto (fun k : ℕ => f^[k] (u N₀)) atTop (nhds 0) := by
      have hcomp : Tendsto (fun k : ℕ => u (N₀ + k)) atTop (nhds 0) :=
        Filter.Tendsto.congr' (Eventually.of_forall fun k => congrArg u (Nat.add_comm k N₀))
          (hu_lim.comp (tendsto_add_atTop_nat N₀))
      exact Filter.Tendsto.congr' (Eventually.of_forall fun k => hu_iter k) hcomp
    have hne' : ∀ k : ℕ, f^[k] (u N₀) ≠ 0 := by
      intro k h0
      exact hu_ne (N₀ + k) (by rw [hu_iter k, h0])
    obtain ⟨k, hk⟩ := hMent (u N₀) ht' hne'
    refine ⟨N₀ + k, ?_⟩
    rw [hPdef]
    refine ⟨f^[k] (u N₀), hk, ?_⟩
    rw [← hu_iter k]
    show Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam
        (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam ((Work.EL.F c)^[N₀ + k] z))
      = (Work.EL.F c)^[N₀ + k] z
    exact Work.FatouCoordFix.FlowerFix.trChart_trChartInv hlam _
  · -- diff
    intro z hz
    rw [hPdef] at hz
    rw [Work.FatouCoordFix.FlowerFix.mem_trChart_image hlam] at hz
    set u := Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z with hudef
    have hu_ne : u ≠ 0 := hz.1
    have hW : N_d < (chart u).re := lt_trans hMNd hz.2
    have hψ : DifferentiableAt ℂ (fun w : ℂ => fatouCoordW f (1 - a) w) (chart u) :=
      hdiff.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hW)
    have hchart : DifferentiableAt ℂ chart u := by
      rw [show chart = fun w : ℂ => (-1 : ℂ) * w⁻¹ from by
        funext w; rw [Work.FatouCoord.chart]; ring]
      exact (differentiableAt_inv hu_ne).const_mul (-1)
    have hC : DifferentiableAt ℂ
        (fun z => chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)) z :=
      hchart.comp z (Work.FatouCoordFix.FlowerFix.differentiable_trChartInv d.z₁ lam).differentiableAt
    have hφd : DifferentiableAt ℂ φ z := by
      show DifferentiableAt ℂ
        (fun z => fatouCoordW f (1 - a) (chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z))) z
      exact hψ.comp z hC
    exact hφd.differentiableWithinAt
  · -- inj
    intro z hz z' hz' heq
    rw [hPdef] at hz hz'
    rw [Work.FatouCoordFix.FlowerFix.mem_trChart_image hlam] at hz hz'
    rw [show φ = fun z => fatouCoordW f (1 - a)
        (chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)) from hφdef] at heq
    have h1 : chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)
        = chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z') :=
      hinj (lt_trans hMNi hz.2) (lt_trans hMNi hz'.2) heq
    have h2 : Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z
        = Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z' :=
      Work.FatouCoord.chart_injective h1
    have h3 := congrArg (Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam) h2
    rwa [Work.FatouCoordFix.FlowerFix.trChart_trChartInv hlam z,
      Work.FatouCoordFix.FlowerFix.trChart_trChartInv hlam z'] at h3
  · -- deriv_ne
    intro z hz
    rw [hPdef] at hz
    rw [Work.FatouCoordFix.FlowerFix.mem_trChart_image hlam] at hz
    set u := Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z with hudef
    have hu_ne : u ≠ 0 := hz.1
    have hW : N_c < (chart u).re := lt_trans hMNc hz.2
    have hWd : N_d < (chart u).re := lt_trans hMNd hz.2
    have hderψ : deriv (fun w : ℂ => fatouCoordW f (1 - a) w) (chart u) ≠ 0 := by
      intro h0
      have hh := hder (chart u) hW
      rw [h0] at hh
      norm_num at hh
    have hdchart : deriv chart u = (u ^ 2)⁻¹ := by
      have he : chart = fun w : ℂ => (-1 : ℂ) * w⁻¹ := by
        funext w; rw [Work.FatouCoord.chart]; ring
      rw [he]
      have h1 : HasDerivAt (fun w : ℂ => (-1 : ℂ) * w⁻¹) ((u ^ 2)⁻¹) u := by
        have h0 := (hasDerivAt_inv hu_ne).const_mul (-1)
        rwa [show (-1 : ℂ) * (-(u ^ 2)⁻¹) = (u ^ 2)⁻¹ by ring] at h0
      exact h1.deriv
    have hdtv : deriv (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam) z = 1 / lam := by
      have he : Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam = fun w : ℂ => (w - d.z₁) / lam := by
        funext w; rw [Work.FatouCoordFix.FlowerFix.trChartInv_apply]
      rw [he]
      exact (((hasDerivAt_id z).sub_const d.z₁).div_const lam).deriv
    have hψd : DifferentiableAt ℂ (fun w : ℂ => fatouCoordW f (1 - a) w) (chart u) :=
      hdiff.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hWd)
    have hcd : DifferentiableAt ℂ chart u := by
      rw [show chart = fun w : ℂ => (-1 : ℂ) * w⁻¹ from by
        funext w; rw [Work.FatouCoord.chart]; ring]
      exact (differentiableAt_inv hu_ne).const_mul (-1)
    have hCdiff : DifferentiableAt ℂ
        (fun z => chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)) z :=
      hcd.comp z (Work.FatouCoordFix.FlowerFix.differentiable_trChartInv d.z₁ lam).differentiableAt
    have hdC : deriv (fun z => chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)) z
        = (u ^ 2)⁻¹ * (1 / lam) := by
      rw [show (fun z => chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z))
          = chart ∘ (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam) from rfl]
      rw [deriv_comp z hcd (Work.FatouCoordFix.FlowerFix.differentiable_trChartInv d.z₁ lam).differentiableAt,
        hdchart, hdtv]
    have hφd : deriv φ z = deriv (fun w : ℂ => fatouCoordW f (1 - a) w) (chart u)
        * deriv (fun z => chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)) z := by
      rw [show φ = fun z => fatouCoordW f (1 - a)
          (chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)) from hφdef]
      rw [show (fun z => fatouCoordW f (1 - a)
            (chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)))
          = (fun w : ℂ => fatouCoordW f (1 - a) w)
            ∘ (fun z => chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)) from rfl]
      exact deriv_comp z hψd hCdiff
    rw [hφd, hdC]
    exact mul_ne_zero hderψ
      (mul_ne_zero (inv_ne_zero (pow_ne_zero 2 hu_ne)) (div_ne_zero one_ne_zero hlam))
  · -- shift
    intro z hz
    rw [hPdef] at hz
    rw [Work.FatouCoordFix.FlowerFix.mem_trChart_image hlam] at hz
    set u := Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z with hudef
    have hu_ne : u ≠ 0 := hz.1
    have hW : N_a < (chart u).re := lt_trans hMNa hz.2
    have hz_eq : z = Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam u := by
      rw [hudef]; exact (Work.FatouCoordFix.FlowerFix.trChart_trChartInv hlam z).symm
    have hFz : Work.EL.F c z = Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam (f u) := by
      rw [hz_eq]; exact hconjfun u (hHPball u hz)
    have hφz : φ z = fatouCoordW f (1 - a) (chart u) := by
      show fatouCoordW f (1 - a) (chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam z)) = _
      rw [hz_eq, Work.FatouCoordFix.FlowerFix.trChartInv_trChart hlam]
    have hch : chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam (Work.EL.F c z))
        = wMap f (chart u) := by
      rw [hFz, Work.FatouCoordFix.FlowerFix.trChartInv_trChart hlam]
      rw [Work.FatouCoord.wMap, Work.FatouCoord.chart_chart hu_ne]
    have hφFz : φ (Work.EL.F c z) = fatouCoordW f (1 - a) (wMap f (chart u)) := by
      show fatouCoordW f (1 - a) (chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam (Work.EL.F c z))) = _
      rw [hch]
    rw [hφFz, hφz, habel (chart u) hW]
  · -- sat
    intro ζ
    obtain ⟨N, hN⟩ := Work.FlowerGlue.image_sat_HPlanePetal hb hMnn ζ
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨u, hu, hφu⟩ := hN n hn
    refine ⟨Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam u, ?_, ?_⟩
    · rw [hPdef]; exact ⟨u, hu, rfl⟩
    · show φ (Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam u) = ζ + (n : ℂ)
      show fatouCoordW f (1 - a)
          (chart (Work.FatouCoordFix.FlowerFix.trChartInv d.z₁ lam
            (Work.FatouCoordFix.FlowerFix.trChart d.z₁ lam u))) = ζ + (n : ℂ)
      rw [Work.FatouCoordFix.FlowerFix.trChartInv_trChart hlam]
      exact hφu

end

end Work.FlowerGlue2
