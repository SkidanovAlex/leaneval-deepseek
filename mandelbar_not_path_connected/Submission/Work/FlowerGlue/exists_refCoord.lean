import Mathlib
import Submission.Work.FlowerGlue.RefCoord
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoord.Exist.fatouCoordW_deriv_close
import Submission.Work.FatouCoord.Flower.enters_widePetal
import Submission.Work.FatouCoord.Petal.petal_orbit_tendsto_zero
import Submission.Work.FatouCoordFix.Defs
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_isOpen
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_mul_norm_lt
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_mapsTo_wMap
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_subset_WidePetal
import Submission.Work.FatouCoordFix.HPetal.exists_iterate_mem_HPlanePetal
import Submission.Work.FatouCoordFix.HPetal.Petal_subset_WidePetal
import Submission.Work.FatouCoordFix.FlowerFix.GermFix
import Submission.Work.FatouCoordFix.FlowerFix.TransferFix

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.exists_refCoord`

The reference Fatou coordinate `Work.FlowerGlue.RefCoord d` of a root-parabolic parameter `d`,
built in the chart `W = -1/u` of the parabolic germ of `F c = (T_c)^{10}` at `d.z₁`.

The construction is the honest one: `germ_bounds` normalises the germ `F c` at `z₁` to the
parabolic form `f u = u + u ^ 2 h u` on the ball of radius `r` via the affine chart
`u ↦ z₀ + lam * u`; the reference petal is the half-plane petal `HPlanePetal M` of the chart,
transported to the dynamical plane (`HPlanePetalAt`), and the coordinate is the chart Fatou
coordinate `fatouCoordW f (1 - a) ∘ chart`, for which every field of `RefCoord` is a statement
about `fatouCoordW` (`_injOn`, `_deriv_close`, `_abel`, `_image_bdd`, `_differentiable`).
-/

open scoped Topology
open Set Filter Function Metric

namespace Work.FlowerGlue

open Work.FatouCoord (chart wMap ParabolicBounds fatouCoordW Petal)
open Work.FatouCoordFix (HPlanePetal HPlanePetalAt)

noncomputable section

/-! ## 1. The half-plane petal as a petal of the germ -/

/-- For every level above a threshold the parabolic germ preserves the half-plane petal. -/
theorem exists_mapsTo_HPlanePetal {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → MapsTo f (HPlanePetal M) (HPlanePetal M) := by
  obtain ⟨M₁, hM₁⟩ := Work.FatouCoordFix.FlowerFix.gpf_widePetal_growth_mono hb
  refine ⟨max M₁ 0, fun M hM => ?_⟩
  refine Work.FatouCoordFix.HPetal.HPlanePetal_mapsTo_wMap (le_trans (le_max_right _ _) hM) ?_
  intro W hW
  have hMW : M ≤ M := le_rfl
  have h1 : M < Work.FatouCoord.Flower.sgauge W := by
    rw [Work.FatouCoord.Flower.mem_sgauge]
    linarith [abs_nonneg W.im]
  have h2 := (hM₁ M (le_trans (le_max_left _ _) hM) W h1).2
  linarith

/-- For every level above a threshold every orbit in the half-plane petal converges to `0`. -/
theorem exists_tendsto_HPlanePetal {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → ∀ u ∈ HPlanePetal M,
      Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) := by
  obtain ⟨M₁, hM₁pos, hM₁⟩ := Work.FatouCoord.Petal.petal_orbit_tendsto_zero hb
  refine ⟨max (M₁ + 1) (1 / r + 1), fun M hM u hu => ?_⟩
  have hM1le : M₁ ≤ M := by
    have := le_max_left (M₁ + 1) (1 / r + 1); linarith
  have hMr : 1 / r < M := by
    have := le_max_right (M₁ + 1) (1 / r + 1); linarith
  have hMpos : 0 < M := by
    have := le_max_right (M₁ + 1) (1 / r + 1); linarith
  obtain ⟨hu0, huM⟩ := hu
  have hP : u ∈ Petal r M :=
    Work.FatouCoord.Flower.mem_Petal_of_lt_re_chart hb.hr hMpos hMr hu0 huM
  exact hM₁ u (Work.FatouCoord.Petal_mono le_rfl hM1le hP)

/-- For every level above a threshold every orbit converging to `0` and avoiding it enters the
half-plane petal. -/
theorem exists_enters_HPlanePetal {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → ∀ u : ℂ,
      Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) → (∀ n : ℕ, f^[n] u ≠ 0) →
      ∃ n : ℕ, f^[n] u ∈ HPlanePetal M := by
  obtain ⟨M₁, hM₁⟩ := Work.FatouCoordFix.FlowerFix.gpf_widePetal_growth_mono hb
  refine ⟨max M₁ (max 1 (1 / r + 1)), fun M hM u ht hne => ?_⟩
  have hMge1 : 1 ≤ max M₁ (max 1 (1 / r + 1)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hMger : 1 / r < max M₁ (max 1 (1 / r + 1)) := by
    have h : 1 / r + 1 ≤ max M₁ (max 1 (1 / r + 1)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hgr : ∀ W : ℂ, max M₁ (max 1 (1 / r + 1)) < Work.FatouCoord.Flower.sgauge W →
      max M₁ (max 1 (1 / r + 1)) < Work.FatouCoord.Flower.sgauge (wMap f W) ∧
      (wMap f W).re ≥ W.re + 1 / 2 :=
    hM₁ _ (le_max_left _ _)
  obtain ⟨n₁, hn₁⟩ :=
    Work.FatouCoord.Flower.enters_widePetal hb hMge1 hMger hgr u ht hne
  obtain ⟨k, hk⟩ :=
    Work.FatouCoordFix.HPetal.exists_iterate_mem_HPlanePetal (f := f) (M := M)
      (M' := max M₁ (max 1 (1 / r + 1))) hgr hn₁
  refine ⟨n₁ + k, ?_⟩
  rw [show n₁ + k = k + n₁ from Nat.add_comm _ _, Function.iterate_add_apply]
  exact hk

/-- The image of the half-plane petal under the chart Fatou coordinate saturates the cylinder:
every point of `ℂ` has all its sufficiently large positive translates in the image. -/
theorem image_sat_HPlanePetal {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') {M : ℝ} (hM : 0 ≤ M) :
    ∀ ζ : ℂ, ∃ N : ℕ, ∀ n ≥ N,
      ζ + (n : ℂ) ∈ (fun u : ℂ => fatouCoordW f (1 - a) (chart u)) '' HPlanePetal M := by
  intro ζ
  obtain ⟨C, hC⟩ := Work.FatouCoord.Exist.fatouCoordW_image_bdd hb M |ζ.im|
  refine ⟨Nat.ceil (C - ζ.re) + 1, fun n hn => ?_⟩
  have hn' : C - ζ.re < (n : ℝ) := by
    have h1 : Nat.ceil (C - ζ.re) < n := by omega
    have h2 : C - ζ.re ≤ (Nat.ceil (C - ζ.re) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (C - ζ.re) : ℝ) < (n : ℝ) := by exact_mod_cast h1
    linarith
  have hre : C < (ζ + (n : ℂ)).re := by
    have h1 : ((n : ℂ)).re = (n : ℝ) := by
      rw [← Complex.ofReal_natCast]; exact Complex.ofReal_re (n : ℝ)
    rw [Complex.add_re, h1]; linarith
  have him : |(ζ + (n : ℂ)).im| ≤ |ζ.im| := by
    simp
  obtain ⟨w, hw, hψ⟩ := hC (ζ + (n : ℂ)) hre him
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0] at hw; simp at hw; linarith
  refine ⟨chart w, ?_, ?_⟩
  · rw [Work.FatouCoordFix.mem_HPlanePetal]
    refine ⟨Work.FatouCoord.chart_ne_zero hw0, ?_⟩
    rw [show (-1 : ℂ) / chart w = chart (chart w) from rfl, Work.FatouCoord.chart_chart hw0]
    exact hw
  · show fatouCoordW f (1 - a) (chart (chart w)) = ζ + (n : ℂ)
    rw [Work.FatouCoord.chart_chart hw0]
    exact hψ

/-- Openness of the transported half-plane petal `HPlanePetalAt z₀ lam M`. -/
theorem isOpen_HPlanePetalAt {z₀ lam : ℂ} (hlam : lam ≠ 0) (M : ℝ) :
    IsOpen (HPlanePetalAt z₀ lam M) := by
  rw [Work.FatouCoordFix.HPlanePetalAt_eq_image hlam,
    show (fun u : ℂ => z₀ + lam * u) '' HPlanePetal M
        = Work.FatouCoordFix.FlowerFix.trChartInv z₀ lam ⁻¹' HPlanePetal M from by
      ext z; exact Work.FatouCoordFix.FlowerFix.mem_trChart_image hlam]
  exact (Work.FatouCoordFix.HPetal.HPlanePetal_isOpen M).preimage
    (Work.FatouCoordFix.FlowerFix.continuous_trChartInv z₀ lam)

/-- Iterating a conjugacy on an invariant set. -/
theorem iterate_conj_of_mapsTo {F f : ℂ → ℂ} {z₀ lam : ℂ} {S : Set ℂ} {r : ℝ}
    (hS : S ⊆ Metric.ball 0 r) (hmap : MapsTo f S S)
    (hconj : ∀ u ∈ Metric.ball 0 r, F (z₀ + lam * u) = z₀ + lam * f u) :
    ∀ u ∈ S, ∀ n : ℕ, F^[n] (z₀ + lam * u) = z₀ + lam * (f^[n] u) := by
  intro u hu n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hconj (f^[n] u) (hS (hmap.iterate n hu)),
      Function.iterate_succ_apply']

/-- See `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §1.2 for the design (glue from `fatouCoordW_injOn`/`_deriv_close`/`_abel`/`_image_bdd` and `Work.FatouCoordFix`'s `ParabolicBounds`). -/
theorem exists_refCoord {c : ℂ} (d : Work.EL.RootParabolic c) :
    Nonempty (Work.FlowerGlue.RefCoord d) := by
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
  -- ### 2. the thresholds of the `fatouCoordW` theory
  obtain ⟨N_d, hNdpos, hNdr, hdiff⟩ := Work.FatouCoord.Exist.fatouCoordW_differentiable hb
  obtain ⟨N_c, hNcpos, hNcr, hder⟩ := Work.FatouCoord.Exist.fatouCoordW_deriv_close hb
  obtain ⟨N_i, hNipos, hNir, hinj⟩ := Work.FatouCoord.Exist.fatouCoordW_injOn hb
  obtain ⟨N_a, hNapos, hNar, habel⟩ := Work.FatouCoord.Exist.fatouCoordW_abel hb
  obtain ⟨Mg, hMg⟩ := exists_mapsTo_HPlanePetal hb
  obtain ⟨Mt, hMt⟩ := exists_tendsto_HPlanePetal hb
  obtain ⟨Me, hMe⟩ := exists_enters_HPlanePetal hb
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
  refine ⟨⟨P, φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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
    have hiter := iterate_conj_of_mapsTo (F := Work.EL.F c) (f := f) (z₀ := d.z₁) (lam := lam)
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
    obtain ⟨N, hN⟩ := image_sat_HPlanePetal hb hMnn ζ
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

end Work.FlowerGlue
