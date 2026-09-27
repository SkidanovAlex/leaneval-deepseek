import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.mem_saddleRegionBall_of_frontier
import Submission.Work.Drive.N2.saddleJourneyAvoidsBalls
import Submission.Work.Drive.N2.saddleWindow_legality

namespace Work.Drive.N2

/-- **The frontier row of the saddle window, scaled form.**  A frontier point of the scaled model
region `{y ∈ modelBall (D.φ D.j) ρ | |Im (Z y)²| < c₀}` whose value lies in the window
`(f p - lam0² η, f p + lam0² η)` lies in the model ball, provided `f = f p + lam0² Re (Z ·)²` on the
chart source and `Z = Zs/lam0` with `Zs` the complex coordinate of the chart `φ'` (same source and
same model balls as the datum's chart).

Sketch: `x ∈ frontier ⊆ closure (modelBall …)` gives `x ∈ (D.φ D.j).source` (via
`swl_closure_modelBall_subset_source`), so `Z` is continuous at `x`
(`hZsm.contMDiffAt …).continuousAt`).  Transfer `|Im (Z ·)²| < c₀` from the region to `x` by
`le_of_mem_closure_of_continuousAt` and the level law `hlev` from the model ball to `x` by the same
lemma (using `swl_continuousAt_of_mem_source` for `f`); hence `|Re (Z x)²| < η` from `hxval` and
`lam0² > 0`.  With `norm_four_eq`, `‖Z x‖⁴ = Re² + Im² < η² + c₀² < 4.01 < 8⁴`, so `‖Z x‖ < 8`, and
`‖D.φ D.j x‖ = ‖φ' x‖ = ‖Zs x‖ = lam0 ‖Z x‖ < 8 lam0 = D.ρ D.j` (using `norm_Z_eq_of_hZ`,
`swl_norm_chart_eq`, `hZs`, `hZrel`, `hlam0`). -/
theorem windowFrontierRow {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p)
    {φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {Zs Z : M → ℂ} {lam0 : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = ((φ' y 0 : ℝ) : ℂ) + ((φ' y 1 : ℝ) : ℂ) * Complex.I)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hZsm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀' : c₀ < 2)
    {x : M}
    (hx : x ∈ frontier (saddleRegion (modelBall (D.φ D.j) (D.ρ D.j)) Z c₀))
    (hxval : f x ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η)) :
    x ∈ modelBall (D.φ D.j) (D.ρ D.j) := by
  -- `x` lies in the closure of the region, hence in the closure of the ball, hence in the source
  have hxcl : x ∈ closure (saddleRegion (modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) :=
    frontier_subset_closure hx
  have hxclU : x ∈ closure (modelBall (D.φ D.j) (D.ρ D.j)) :=
    closure_mono (fun y hy => hy.1) hxcl
  have hxsrc : x ∈ (D.φ D.j).source :=
    swl_closure_modelBall_subset_source (D := D) (i := D.j) (r := D.ρ D.j) le_rfl hxclU
  -- continuity of `Z` at `x`
  have hZcont : ContinuousAt Z x :=
    (hZsm.contMDiffAt ((D.φ D.j).open_source.mem_nhds hxsrc)).continuousAt
  have hImC : ContinuousAt (fun y : M => ((Z y) ^ 2).im) x := by
    fun_prop
  -- the invariant bound at `x`
  have hIm_le : ((Z x) ^ 2).im ≤ c₀ :=
    le_of_mem_closure_of_continuousAt (u := fun y : M => ((Z y) ^ 2).im) (x := x) (a := c₀)
      hxcl hImC (fun y hy => le_of_lt (abs_lt.mp hy.2).2)
  have hIm_ge : -c₀ ≤ ((Z x) ^ 2).im := by
    have hneg : ContinuousAt (fun y : M => -((Z y) ^ 2).im) x := hImC.neg
    have h := le_of_mem_closure_of_continuousAt (u := fun y : M => -((Z y) ^ 2).im)
      (x := x) (a := c₀) hxcl hneg (fun y hy => by have hh := (abs_lt.mp hy.2).1; linarith)
    linarith [h]
  have hIm_abs : |((Z x) ^ 2).im| ≤ c₀ := abs_le.mpr ⟨hIm_ge, hIm_le⟩
  have hc₀nn : 0 ≤ c₀ := le_trans (abs_nonneg _) hIm_abs
  have him_sq : (((Z x) ^ 2).im) ^ 2 ≤ c₀ ^ 2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hc₀nn])
  -- the level law at `x` (given on the whole source)
  have hfeq : f x = f p + lam0 ^ 2 * ((Z x) ^ 2).re := hlev x hxsrc
  have hre_lt : |((Z x) ^ 2).re| < η := by
    have hpos : 0 < lam0 ^ 2 := pow_pos hlam0pos 2
    have h1 : lam0 ^ 2 * (-η) < lam0 ^ 2 * ((Z x) ^ 2).re := by linarith [hxval.1, hfeq]
    have h2 : lam0 ^ 2 * ((Z x) ^ 2).re < lam0 ^ 2 * η := by linarith [hxval.2, hfeq]
    exact abs_lt.mpr ⟨lt_of_mul_lt_mul_left h1 (le_of_lt hpos),
      lt_of_mul_lt_mul_left h2 (le_of_lt hpos)⟩
  have hre_sq : (((Z x) ^ 2).re) ^ 2 < η ^ 2 :=
    sq_lt_sq.mpr (by rwa [abs_of_pos hη])
  -- `‖Z x‖⁴ = Re² + Im² < η² + c₀² < 8⁴`
  have hpow : ‖Z x‖ ^ 4 < 8 ^ 4 := by
    rw [norm_four_eq]
    nlinarith [hre_sq, him_sq, hη', hc₀', hc₀nn, hη]
  have hZlt : ‖Z x‖ < 8 := lt_of_pow_lt_pow_left₀ 4 (by norm_num) hpow
  -- the norm identity `‖Z x‖ = ‖D.φ D.j x‖ / lam0`
  have hZnorm : ‖Z x‖ = ‖D.φ D.j x‖ / lam0 :=
    swl_norm_Z_eq (D := D) (φ' := φ') (Zs := Zs) (Z := Z) (lam0 := lam0)
      hsrc hball hZs (hZrel := hZrel) hlam0pos (by rw [hsrc]; exact hxsrc)
  have hnormφ : ‖D.φ D.j x‖ = lam0 * ‖Z x‖ := by
    rw [hZnorm]
    field_simp [ne_of_gt hlam0pos]
  refine ⟨hxsrc, ?_⟩
  rw [hnormφ]
  have h8 : lam0 * 8 = D.ρ D.j := by rw [hlam0]; ring
  rw [← h8]
  exact mul_lt_mul_of_pos_left hZlt hlam0pos


end Work.Drive.N2
