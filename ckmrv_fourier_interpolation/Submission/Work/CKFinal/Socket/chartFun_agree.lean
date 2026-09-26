/-
# Well-definedness of the window chart on `W1`

The window chart `Socket.chartFun ℓ d hd s hs r` at height `s` is an arbitrary choice out of
`Work.CKFinal.windowChart_data`: a function holomorphic on the ball `B(1 + i s, chartEps s)`,
equal to the paper's layer `Socket.layerFn ℓ d r` on the `𝒟`-side of that ball, equal to
`Socket.layerFn ℓ d r + sinSqC r * resCorr r` on the far side `1 < Re τ`, and even in `r`.

This file proves the chart value does not depend on the height: **two window balls containing the
same point carry the same chart value at that point**.  The proof is the identity theorem on the
intersection `winBall s ∩ winBall s'` (preconnected, being an intersection of two hyperbolic
balls, `Work.LayerCont.Glue.isPreconnected_inter_ball`): the two charts agree on the non-empty open
subset of the intersection off the line `Re τ = 1`, where each of them is pinned to `layerFn`
(resp. to `layerFn + sinSqC r * resCorr r`) by `Socket.chartFun_Dside` (resp. `Socket.chartFun_far`)
— note that `Re τ < 1` inside a window ball lands in the fundamental domain `𝒟` by
`Socket.winBall_mem_DomainD`.

The only point needing an argument is that this subset is non-empty: the intersection is open and
non-empty, but it could conceivably hug the line `Re τ = 1` (on which neither formula applies).  It
cannot: from a point `u` of the intersection and a hyperbolic ball `B(u, ρ)` inside it, the
horizontal translate of `u` by `δ = Im u * sqrt (cosh ρ - 1) / 2 ≠ 0` is again in the ball (its
hyperbolic distance to `u` has `cosh` equal to `1 + (cosh ρ - 1)/8 < cosh ρ`) and it is off the
line whenever `u` is on it.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.WinDefs
import Submission.Work.LayerCont.Glue.All

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal.Socket

/-- **Well-definedness of the window chart on `W1`.**  If two window balls (of heights `s`, `s'`)
both contain `τ`, then the corresponding window charts take the same value at `τ`; i.e. the chart
value is a function of `τ` (and `r`) alone. -/
theorem chartFun_agree (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s s' : ℝ} {hs : 0 < s} {hs' : 0 < s'} (r : ℝ) {τ : UpperHalfPlane}
    (h : τ ∈ Work.CKFinal.Socket.winBall ℓ d hd s hs)
    (h' : τ ∈ Work.CKFinal.Socket.winBall ℓ d hd s' hs') :
    Work.CKFinal.Socket.chartFun ℓ d hd s hs r τ = Work.CKFinal.Socket.chartFun ℓ d hd s' hs' r τ := by
  -- the intersection `U` of the two window balls
  set U : Set UpperHalfPlane :=
    winBall ℓ d hd s hs ∩ winBall ℓ d hd s' hs' with hUdef
  have hUopen : IsOpen U :=
    (isOpen_winBall ℓ d hd s hs).inter (isOpen_winBall ℓ d hd s' hs')
  have hUconn : IsPreconnected U := by
    rw [hUdef]
    exact Work.LayerCont.Glue.isPreconnected_inter_ball _ _ _ _
  -- the two charts are holomorphic on `U`
  have hF : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chartFun ℓ d hd s hs r) U :=
    (chartFun_mdiff ℓ d hd s hs r).mono
      (Set.Subset.trans Set.inter_subset_left (winBall_subset_eps ℓ d hd s hs))
  have hG : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chartFun ℓ d hd s' hs' r) U :=
    (chartFun_mdiff ℓ d hd s' hs' r).mono
      (Set.Subset.trans Set.inter_subset_right (winBall_subset_eps ℓ d hd s' hs'))
  have hτU : τ ∈ U := ⟨h, h'⟩
  -- the open subset of `U` off the line `Re τ = 1`, where both charts are pinned down
  set V : Set UpperHalfPlane := U ∩ {u : UpperHalfPlane | u.re ≠ 1} with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact hUopen.inter ((isOpen_ne (x := (1 : ℝ))).preimage UpperHalfPlane.continuous_re)
  have hVne : V.Nonempty := by
    rw [hVdef]
    by_cases hre : τ.re ≠ 1
    · exact ⟨τ, hτU, hre⟩
    · -- `τ` lies on the line: shift it horizontally, inside the ball of radius `ρ` about `τ`
      push Not at hre
      obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hUopen τ hτU
      have hKpos : 0 < Real.cosh ρ - 1 := by
        have := Real.one_lt_cosh.mpr (ne_of_gt hρpos); linarith
      set δ : ℝ := τ.im * Real.sqrt (Real.cosh ρ - 1) / 2 with hδdef
      have hδpos : 0 < δ := by
        rw [hδdef]; positivity
      let w : UpperHalfPlane := ⟨(τ : ℂ) + (δ : ℂ), by simpa using τ.im_pos⟩
      have hwre : w.re = τ.re + δ := by simp [w, UpperHalfPlane.coe_re]
      have hwim : w.im = τ.im := by simp [w, UpperHalfPlane.coe_im]
      refine ⟨w, ?_, ?_⟩
      · apply hρsub
        rw [Metric.mem_ball]
        -- the hyperbolic distance from `τ` to its translate is `< ρ`
        have hcosh : Real.cosh (dist w τ) = 1 + (Real.cosh ρ - 1) / 8 := by
          rw [UpperHalfPlane.cosh_dist', hwre, hwim, hδdef]
          have hsq : Real.sqrt (Real.cosh ρ - 1) ^ 2 = Real.cosh ρ - 1 := Real.sq_sqrt hKpos.le
          field_simp
          nlinarith [hsq]
        have hlt : Real.cosh (dist w τ) < Real.cosh ρ := by rw [hcosh]; linarith
        have h2 := Real.cosh_lt_cosh.mp hlt
        rw [abs_of_nonneg dist_nonneg, abs_of_pos hρpos] at h2
        exact h2
      · show w.re ≠ 1
        rw [hwre, hre]
        intro hh
        linarith [hδpos]
  -- on `V` the two charts agree: off `Re τ = 1` each is given by `layerFn` or `layerFn + corr`
  have hVeq : Set.EqOn (chartFun ℓ d hd s hs r) (chartFun ℓ d hd s' hs' r) V := by
    intro u hu
    rw [hVdef] at hu
    obtain ⟨huU, hure⟩ := hu
    obtain ⟨hus, hus'⟩ := huU
    rcases lt_or_gt_of_ne hure with hlt | hgt
    · -- `𝒟`-side: both charts are the paper layer
      have hd1 : u ∈ Work.Asymptotics.DomainD := winBall_mem_DomainD ℓ d hd hus hlt
      have hd2 : u ∈ Work.Asymptotics.DomainD := winBall_mem_DomainD ℓ d hd hus' hlt
      have h1 : chartFun ℓ d hd s hs r u = layerFn ℓ d r u :=
        chartFun_Dside ℓ d hd s hs r (winBall_subset_eps ℓ d hd s hs hus) hd1
      have h2 : chartFun ℓ d hd s' hs' r u = layerFn ℓ d r u :=
        chartFun_Dside ℓ d hd s' hs' r (winBall_subset_eps ℓ d hd s' hs' hus') hd2
      rw [h1, h2]
    · -- far side: both charts are the layer plus the residue correction
      have h1 := chartFun_far ℓ d hd s hs r (winBall_subset_eps ℓ d hd s hs hus) hgt
      have h2 := chartFun_far ℓ d hd s' hs' r (winBall_subset_eps ℓ d hd s' hs' hus') hgt
      rw [h1, h2]
  -- the identity theorem on the preconnected open `U`
  have hEq := Work.LayerCont.Glue.eqOn_of_mdifferentiableOn_of_preconnected hUopen hUconn hF hG
    (by rw [hVdef]; exact Set.inter_subset_left) hVopen hVne hVeq
  exact hEq hτU

end Work.CKFinal.Socket
