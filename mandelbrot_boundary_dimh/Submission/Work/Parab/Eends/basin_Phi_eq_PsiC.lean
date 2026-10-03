import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Basic
import Submission.Work.Parab.leftCoord.escC
import Submission.Work.Parab.leftCoord.levelData
import Submission.Work.Parab.leftCoord.exists_levelFacts
import Submission.Work.Parab.leftCoord.sector_mem_EscC
import Submission.Work.Parab.leftCoordData.orbit_ends_control
import Submission.Work.Parab.basin_basic
import Submission.Work.Parab.Setup
import Submission.Work.Parab.Eends.iterate_chart_eq
import Submission.Work.Parab.Eends.analytic_not_eventuallyConst
import Submission.Work.Parab.Eends.basin_iterate_Phi

namespace Work.Parab.Eends

open Filter Metric Set
open scoped Topology

/-- **The basin Fatou coordinate on the ends is the closed extension of the petal coordinate.**

`Φ` is a Fatou coordinate of a parabolic germ `f` (`f z = z + z^2 h z` on `ball 0 r`,
`ParabolicBounds f h a r A A'`) on the uniform parabolic basin `MandelDim.ParabolicBasin f D₀`:
it satisfies the Abel equation `Φ (f z) = Φ z + 1` there and agrees with the explicitly
constructed petal coordinate `fatouCoord f (1 - a)` on the petal `Petal r M` (which lies in the
basin).  No holomorphy of `Φ` is needed.

Claim: for every level `N` above a threshold (in particular `N ≥ M`, `N ≥ 1/r`), there is a
threshold `T` such that for `ζ` with `T < |Im ζ|` and in the wedge `-3 |Im ζ| < Re ζ` (so the
point `-1/ζ` lies in `ball 0 ρ ⊆ D₀` and its `wMap`-orbit crosses the level `N` while staying
at distance `|Im ζ|/4` from the origin), the value of `Φ` is the explicit
`Work.Parab.leftCoord.PsiC N (wMap f) (fatouCoordW f (1-a)) ζ` of
`Work.Parab.leftCoord.escC`.  (The threshold `T` necessarily depends on `N`: the orbit control
`Work.Parab.leftCoordData.orbit_ends_control` needs `|Im ζ| > 100 N + const`.)

Proof route (`ζ` in the wedge with `|Im ζ| > T`, `T` chosen large):

* `z := -1/ζ ∈ MandelDim.ParabolicBasin f D₀` by hypothesis; `|z| < ρ` for any `ρ > 0` with
  `ball 0 ρ ⊆ D₀` (openness of `D₀`), so `z` lies in the component of `0` in `D₀`, where `f`
  is not locally constant (`f'(0) = 1`);
* let `w k := (wMap f)^[k] ζ`, `n := nIdxC N (wMap f) ζ`; the orbit control of
  `Work.Parab.leftCoordData.orbit_ends_control` gives `|Im ζ|/4 ≤ ‖w k‖` and `N < Re (w n)`
  for `k ≤ n`, so `‖w k‖ > 1/ρ`, `f^[k] z = chart (w k)` and `|f^[k] z| < ρ`;
* hence `f^[k] z ∈ MandelDim.ParabolicBasin f D₀` for `k ≤ n` by induction with
  `Work.Parab.basin_forward` (analytic at `f^[k] z`, not locally constant there because
  `f' = 1 + O(z) ≠ 0` near `0`), and the Abel equation may be iterated: `Φ z = Φ (f^[n] z) - n`;
* `Re (w n) > N ≥ max (M, 1/r)` shows `f^[n] z ∈ Petal r M`
  (`Work.FatouCoord.chart_mem_Petal_iff`), so `Φ (f^[n] z) = fatouCoord f (1-a) (f^[n] z) =
  fatouCoordW f (1-a) (w n)`;
* unfolding `PsiC N (wMap f) (fatouCoordW f (1-a)) ζ = fatouCoordW f (1-a) (w n) - n`
  gives the claim. -/
theorem basin_Phi_eq_PsiC {f : ℂ → ℂ} {D₀ : Set ℂ} (hg : MandelDim.IsParabolicGerm f D₀)
    {h : ℂ → ℂ} {a : ℂ} {r A A' M : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    (hpetal : Work.FatouCoord.Petal r M ⊆ MandelDim.ParabolicBasin f D₀)
    {Φ : ℂ → ℂ}
    (hΦabel : ∀ z ∈ MandelDim.ParabolicBasin f D₀, Φ (f z) = Φ z + 1)
    (hΦpet : ∀ z ∈ Work.FatouCoord.Petal r M, Φ z = Work.FatouCoord.fatouCoord f (1 - a) z) :
    ∃ N₀ : ℝ, 0 < N₀ ∧ 1 / r ≤ N₀ ∧ M ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∃ T : ℝ, ∀ ζ : ℂ, T < |ζ.im| → -3 * |ζ.im| < ζ.re →
        (-1 / ζ) ∈ MandelDim.ParabolicBasin f D₀ →
        Φ (-1 / ζ) = Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap f)
          (Work.FatouCoord.fatouCoordW f (1 - a)) ζ := by
  -- the level at which all the analytic estimates of the chart coordinate are available
  obtain ⟨N₁, hF₁⟩ := Work.Parab.leftCoord.exists_levelFacts hb
  -- the scale at which `f` is analytic and not locally constant
  obtain ⟨ρ, hρpos, hρr, hρ⟩ := Work.Parab.Eends.analytic_not_eventuallyConst hb
  refine ⟨max N₁ (max M (1 / r)), ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hF₁.pos (le_max_left _ _)
  · exact le_trans (le_max_right M (1 / r)) (le_max_right N₁ (max M (1 / r)))
  · exact le_trans (le_max_left M (1 / r)) (le_max_right N₁ (max M (1 / r)))
  · intro N hN
    have hN₁N : N₁ ≤ N := le_trans (le_max_left _ _) hN
    have hrest : max M (1 / r) ≤ N := le_trans (le_max_right _ _) hN
    have hMN : M ≤ N := le_trans (le_max_left M (1 / r)) hrest
    have h1rN : 1 / r ≤ N := le_trans (le_max_right M (1 / r)) hrest
    have hF : Work.Parab.leftCoord.LevelFacts f h a r N := hF₁.mono hN₁N
    -- the orbit control: the `wMap`-orbit of a far point of the wedge crosses the level `N`
    obtain ⟨Mo, C, hMopos, hCnn, hctrl⟩ :=
      Work.Parab.leftCoordData.orbit_ends_control hb hF.pos
    refine ⟨max Mo (max (4 * N + 1) (4 / ρ)), ?_⟩
    intro ζ him hwedge hbasin
    have hMo : Mo < |ζ.im| := lt_of_le_of_lt (le_max_left _ _) him
    have h4N : 4 * N + 1 < |ζ.im| :=
      lt_of_le_of_lt (le_trans (le_max_left (4 * N + 1) (4 / ρ))
        (le_max_right Mo (max (4 * N + 1) (4 / ρ)))) him
    have h4ρ : 4 / ρ < |ζ.im| :=
      lt_of_le_of_lt (le_trans (le_max_right (4 * N + 1) (4 / ρ))
        (le_max_right Mo (max (4 * N + 1) (4 / ρ)))) him
    have himpos : 0 < |ζ.im| := lt_trans (div_pos (by norm_num) hρpos) h4ρ
    obtain ⟨n, hnP, hnmin, hnorm, hnim, hsum⟩ := hctrl ζ hMo hwedge
    have him4pos : 0 < |ζ.im| / 4 := by linarith
    have hNlt : N < |ζ.im| / 4 := by linarith
    have h4r : 4 / r ≤ 4 / ρ := by
      have h := one_div_le_one_div_of_le hρpos hρr
      have h' : 4 * (1 / r) ≤ 4 * (1 / ρ) := by linarith
      simpa only [mul_one_div] using h'
    have h1r4 : 1 / r < |ζ.im| / 4 := by linarith
    have hnorm4 : 4 / |ζ.im| < ρ := by
      rw [div_lt_iff₀ himpos]
      have h := (div_lt_iff₀ hρpos).mp h4ρ
      nlinarith [h]
    -- the iterates of `wMap` do not vanish, so the chart conjugation iterates
    have hNeq : ∀ k ≤ n, (Work.FatouCoord.wMap f)^[k] ζ ≠ 0 := by
      intro k hk
      have hpos : 0 < ‖(Work.FatouCoord.wMap f)^[k] ζ‖ :=
        lt_of_lt_of_le him4pos (hnorm k hk)
      exact norm_ne_zero_iff.mp (ne_of_gt hpos)
    have hchartit : ∀ k ≤ n, f^[k] (Work.FatouCoord.chart ζ)
        = Work.FatouCoord.chart ((Work.FatouCoord.wMap f)^[k] ζ) :=
      iterate_chart_eq (f := f) (w := ζ) (n := n) hNeq
    -- the iterates of `z = -1/ζ` stay in the small disc where `f` is analytic and 1-1
    have hnormsmall : ∀ k ≤ n, ‖f^[k] (Work.FatouCoord.chart ζ)‖ < ρ := by
      intro k hk
      rw [hchartit k hk, Work.FatouCoord.norm_chart (hNeq k hk)]
      have h1 : (‖(Work.FatouCoord.wMap f)^[k] ζ‖)⁻¹ ≤ (|ζ.im| / 4)⁻¹ :=
        inv_anti₀ him4pos (hnorm k hk)
      have h2 : (|ζ.im| / 4)⁻¹ = 4 / |ζ.im| := by rw [inv_div]
      linarith
    have hana : ∀ k ≤ n, AnalyticAt ℂ f (f^[k] (Work.FatouCoord.chart ζ)) :=
      fun k hk => (hρ _ (hnormsmall k hk)).1
    have hnc : ∀ k ≤ n,
        ¬ ∀ᶠ w in nhds (f^[k] (Work.FatouCoord.chart ζ)),
          f w = f (f^[k] (Work.FatouCoord.chart ζ)) :=
      fun k hk => (hρ _ (hnormsmall k hk)).2
    have hbasin' : Work.FatouCoord.chart ζ ∈ MandelDim.ParabolicBasin f D₀ := hbasin
    -- the orbit stays in the basin and the Abel equation iterates
    have hmain := basin_iterate_Phi (f := f) (D := D₀) (Φ := Φ)
      (z := Work.FatouCoord.chart ζ) (n := n) hΦabel hbasin' hana hnc
    have hPhiIter : Φ (f^[n] (Work.FatouCoord.chart ζ))
        = Φ (Work.FatouCoord.chart ζ) + (n : ℂ) := hmain.2
    -- the `n`-th iterate lies in the petal
    have hwn : (Work.FatouCoord.wMap f)^[n] ζ ≠ 0 := hNeq n le_rfl
    have hz0 : f^[n] (Work.FatouCoord.chart ζ) ≠ 0 := by
      rw [hchartit n le_rfl]
      exact Work.FatouCoord.chart_ne_zero hwn
    have hchartn : Work.FatouCoord.chart (f^[n] (Work.FatouCoord.chart ζ))
        = (Work.FatouCoord.wMap f)^[n] ζ := by
      rw [hchartit n le_rfl, Work.FatouCoord.chart_chart hwn]
    have hpetalmem : f^[n] (Work.FatouCoord.chart ζ) ∈ Work.FatouCoord.Petal r M := by
      rw [Work.FatouCoord.chart_mem_Petal_iff hb.hr hz0, hchartn]
      exact ⟨lt_of_le_of_lt hMN hnP, lt_of_lt_of_le h1r4 (hnorm n le_rfl)⟩
    have hPhiPet : Φ (f^[n] (Work.FatouCoord.chart ζ))
        = Work.FatouCoord.fatouCoordW f (1 - a) ((Work.FatouCoord.wMap f)^[n] ζ) := by
      rw [hΦpet _ hpetalmem, Work.FatouCoord.fatouCoord_eq, hchartn]
    -- the closed extension in the chart
    have hmono : ∀ x : ℂ, N < ‖x‖ → x.re ≤ (Work.FatouCoord.wMap f x).re := by
      intro x hx
      obtain ⟨K, hK, hstep⟩ := hF.step
      have h := (hstep x hx).2.2.2
      linarith
    have hgood : ζ ∈ Work.Parab.leftCoord.goodSetC N (Work.FatouCoord.wMap f) n :=
      ⟨fun k hk => lt_of_lt_of_le hNlt (hnorm k hk), hnP⟩
    have hPsi := Work.Parab.leftCoord.PsiC_eq_on_goodSetC (N := N)
      (G := Work.FatouCoord.wMap f) (ψ := Work.FatouCoord.fatouCoordW f (1 - a))
      hF.abel hmono hgood
    have hfinal : Φ (Work.FatouCoord.chart ζ)
        = Work.FatouCoord.fatouCoordW f (1 - a) ((Work.FatouCoord.wMap f)^[n] ζ)
          - (n : ℂ) := by
      calc Φ (Work.FatouCoord.chart ζ)
          = Φ (f^[n] (Work.FatouCoord.chart ζ)) - (n : ℂ) := by rw [hPhiIter]; ring
        _ = Work.FatouCoord.fatouCoordW f (1 - a) ((Work.FatouCoord.wMap f)^[n] ζ)
              - (n : ℂ) := by rw [hPhiPet]
    rw [show (-1 / ζ : ℂ) = Work.FatouCoord.chart ζ from rfl, hfinal, ← hPsi]

end Work.Parab.Eends
