import Mathlib
import Submission.Work.RTOwed.FillBigDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- **The horizontal box cover of the `u`-`y` slice of a cusp.**

For every cusp `v` there is a finite set `K ⊂ E3` of horizontal points such that for every perimeter
parameter `u ∈ [0,1]` and every torus parameter `y ∈ [0,1]²` the cusp coordinate
`cuspX v u y = u • σ_v + y₀ • λ₂ + y₁ • λ₃` lies within `1/2` (in every coordinate) of some element
of `K`.

This is a total boundedness statement: the set
`{cuspX v u y | u ∈ [0,1], y₀,y₁ ∈ [0,1]}` is the continuous image of the compact cube
`[0,1]³`, hence totally bounded, and `Metric.totallyBounded_iff` produces the finite `1/2`-net. -/
theorem jKx_cover (v : Work.Space.Cusp) :
    ∃ K : Finset Work.Cusp.E3, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ y : Work.Cusp.E2,
      (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
      ∃ kx ∈ K, ∀ j, |Work.Cusp.cuspX v u y j - kx j| < 1 / 2 := by
  have hcompact : IsCompact ((fun p : ℝ × (ℝ × ℝ) =>
      Work.Cusp.cuspX v p.1 (!₂[p.2.1, p.2.2] : Work.Cusp.E2)) ''
      (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1))) := by
    refine IsCompact.image ?_ ?_
    · exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    · simp only [Work.Cusp.cuspX, Work.Cusp.cuspY]; fun_prop
  obtain ⟨t, htfin, hsub⟩ :=
    Metric.totallyBounded_iff.mp hcompact.totallyBounded (1 / 2) (by norm_num)
  refine ⟨htfin.toFinset, ?_⟩
  intro u hu0 hu1 y hy
  have hmem : Work.Cusp.cuspX v u y ∈ ((fun p : ℝ × (ℝ × ℝ) =>
      Work.Cusp.cuspX v p.1 (!₂[p.2.1, p.2.2] : Work.Cusp.E2)) ''
      (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1))) := by
    refine ⟨(u, y 0, y 1), ⟨⟨hu0, hu1⟩, ⟨hy 0, hy 1⟩⟩, ?_⟩
    show Work.Cusp.cuspX v u (!₂[y 0, y 1] : Work.Cusp.E2) = Work.Cusp.cuspX v u y
    rw [show (!₂[y 0, y 1] : Work.Cusp.E2) = y from by ext i; fin_cases i <;> rfl]
  rcases Set.mem_iUnion.mp (hsub hmem) with ⟨kx, hkx⟩
  rcases Set.mem_iUnion.mp hkx with ⟨hkxt, hball⟩
  refine ⟨kx, htfin.mem_toFinset.mpr hkxt, ?_⟩
  have hd : dist (Work.Cusp.cuspX v u y) kx < 1 / 2 := by
    rwa [Metric.mem_ball] at hball
  intro j
  have := PiLp.dist_apply_le (p := 2) (x := Work.Cusp.cuspX v u y) (y := kx) j
  rw [Real.dist_eq] at this
  exact lt_of_le_of_lt this hd

end Work.RTOwed
