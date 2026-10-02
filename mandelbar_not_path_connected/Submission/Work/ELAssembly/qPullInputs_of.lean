import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELAssembly.pullQ_arc
import Submission.Work.ELAssembly.pullQ_pair
import Submission.Work.ELAssembly.pullQ_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Classical Set

/-! ## Angle data of the level-`n` pair of the `z₁`-nest

The reference angle `midNear [P₀, Qp n]` of the level-`n` polygon is the midpoint of the near arc
`[α₂, βₙ']`; it is what `pullQ_one` consumes as its target angle `m`.  Everything below is the
elementary real arithmetic on the explicit rational data. -/

/-- `Work.EL.alpha2` and `Work.ELNest.alpha2` are the same rational `404/1023`. -/
private theorem el_alpha2_eq : Work.EL.alpha2 = Work.ELNest.alpha2 := rfl

/-- `α₂ < βₙ'`: the nest angles approach `α₂` from above. -/
private theorem bAng'_gt_alpha2' (n : ℕ) : Work.EL.alpha2 < Work.ELNest.bAng' n := by
  have hd : (0 : ℝ) < Work.ELNest.beta0' - Work.EL.alpha2 := by
    rw [beta0'_sub_alpha2]; norm_num
  have h : (0 : ℝ) < (Work.ELNest.beta0' - Work.EL.alpha2) / (1024 : ℝ) ^ n :=
    div_pos hd (pow_pos (by norm_num) n)
  have heq : Work.ELNest.bAng' n
      = Work.EL.alpha2 + (Work.ELNest.beta0' - Work.EL.alpha2) / (1024 : ℝ) ^ n := by
    rw [Work.ELNest.bAng', show Work.ELNest.alpha2 = Work.EL.alpha2 from rfl]
  linarith

/-- `βₙ' - α₂ > 0`. -/
private theorem bAng'_sub_alpha2_pos (n : ℕ) : 0 < Work.ELNest.bAng' n - Work.EL.alpha2 :=
  sub_pos.mpr (bAng'_gt_alpha2' n)

/-- **The reference angle `midNear` of the level-`n` `z₁`-polygon.**  For the two-element list
`[P₀, Qp n]` it is `α₂ + (βₙ' - α₂)/2`, i.e. the midpoint of the near arc `[α₂, βₙ']` (the `+1` of
the second angle `βₙ + 1` is irrelevant, `midNear` only looks at the *first* two angles). -/
private theorem midNear_alphaPair_Qp {c : ℂ} (d : Work.EL.RootParabolic c) (N : NestPairs d)
    (n : ℕ) :
    Work.EL.midNear [alphaPairOf d, N.Qp n]
      = Work.EL.alpha2 + (Work.ELNest.bAng' n - Work.EL.alpha2) / 2 := by
  have hf : Int.fract (Work.ELNest.bAng' n - Work.EL.alpha2)
      = Work.ELNest.bAng' n - Work.EL.alpha2 :=
    Int.fract_eq_self.mpr ⟨le_of_lt (bAng'_sub_alpha2_pos n), bAng'_sub_alpha2_lt_one n⟩
  rw [Work.EL.midNear.eq_1, alphaPairOf_b, N.Qpa n, hf]

/-- **`midNear [P₀, Qp n]` lies in the closed near arc `[α₂, βₙ']` of the level-`n` polygon.** -/
private theorem midNear_mem_arc {c : ℂ} (d : Work.EL.RootParabolic c) (N : NestPairs d)
    (n : ℕ) :
    Work.EL.InClosedArc (Work.EL.midNear [alphaPairOf d, N.Qp n]) Work.ELNest.alpha2
      (Work.ELNest.bAng' n) := by
  change Work.EL.InClosedArc (Work.EL.midNear [alphaPairOf d, N.Qp n]) Work.EL.alpha2
      (Work.ELNest.bAng' n)
  have h0 := bAng'_sub_alpha2_pos n
  have h1 := bAng'_sub_alpha2_lt_one n
  have hf : Int.fract (Work.ELNest.bAng' n - Work.EL.alpha2)
      = Work.ELNest.bAng' n - Work.EL.alpha2 :=
    Int.fract_eq_self.mpr ⟨le_of_lt h0, h1⟩
  have hf2 : Int.fract ((Work.ELNest.bAng' n - Work.EL.alpha2) / 2)
      = (Work.ELNest.bAng' n - Work.EL.alpha2) / 2 :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [Work.EL.InClosedArc, Work.EL.arcLen, hf, midNear_alphaPair_Qp d N n]
  have hsub : Work.EL.alpha2 + (Work.ELNest.bAng' n - Work.EL.alpha2) / 2 - Work.EL.alpha2
      = (Work.ELNest.bAng' n - Work.EL.alpha2) / 2 := by ring
  rw [hsub, hf2]
  exact ⟨by linarith, by linarith⟩

/-- The reference angle is *strictly* inside the near arc: `midNear [P₀, Qp n] ≠ α₂`. -/
private theorem midNear_ne_alpha2 {c : ℂ} (d : Work.EL.RootParabolic c) (N : NestPairs d)
    (n : ℕ) : Work.EL.midNear [alphaPairOf d, N.Qp n] ≠ Work.ELNest.alpha2 := by
  have h0 : 0 < Work.ELNest.bAng' n - Work.ELNest.alpha2 := by
    have h := bAng'_sub_alpha2_pos n
    rwa [el_alpha2_eq] at h
  rw [midNear_alphaPair_Qp d N n, el_alpha2_eq]
  intro h
  linarith

/-- The two "far arc" conditions of the level-`(n+1)` polygon, extracted from the pair-list
form: the `α`-pair gives the `α`-arc and the level-`(n+1)` pair gives the nest arc. -/
private theorem notMem_nearArcs_alpha {c : ℂ} {d : Work.EL.RootParabolic c} {N : NestPairs d}
    {n : ℕ} {x : ℝ}
    (hx : ∀ P ∈ [alphaPairOf d, N.Qp (n + 1)], ¬ Work.EL.InClosedArc x P.a P.b) :
    ¬ Work.EL.InClosedArc x Work.EL.alpha1 Work.EL.alpha2 := by
  have h := hx (alphaPairOf d) (by simp)
  simpa [alphaPairOf_a, alphaPairOf_b] using h

/-- The level-`(n+1)` nest-arc condition, extracted from the pair-list form. -/
private theorem notMem_nearArcs_bAng {c : ℂ} {d : Work.EL.RootParabolic c} {N : NestPairs d}
    {n : ℕ} {x : ℝ}
    (hx : ∀ P ∈ [alphaPairOf d, N.Qp (n + 1)], ¬ Work.EL.InClosedArc x P.a P.b) :
    ¬ Work.EL.InClosedArc x (Work.ELNest.bAng' (n + 1)) (Work.ELNest.bAng (n + 1) + 1) := by
  have h := hx (N.Qp (n + 1)) (by simp)
  simpa [N.Qpa (n + 1), N.Qpb (n + 1)] using h

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`).
/-- **The `z₁`-nest pull-back inputs from the rational certificate.**  `QPullInputs` (the inputs of
`Work.ELAssembly.pullQ_bij`) asks for four things: the level bound `hL`, the critical-value
condition `hcv`, and the three angle facts `arc`, `pair`, `one` in the pair-list form of
`[alphaPairOf d, N.Qp n]`.  This result shows that `arc`/`pair`/`one` are *not* extra inputs: they
follow from the exact rational arithmetic `Work.ELAssembly.pullQ_arc` / `pullQ_pair` /
`pullQ_one` (phrased with the explicit angles `alpha1`, `alpha2`, `bAng`, `bAng'`) together with
the angle specifications `N.Qpa`, `N.Qpb` of `NestPairs`, so that only `hL` and `hcv` remain. -/
theorem qPullInputs_of {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {N : NestPairs d}
    (hL : 1 < L)
    (hcv : ∀ n : ℕ, ∀ k ∈ Set.Icc 1 10,
      (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0 ∉
        Work.EL.polyRegion [alphaPairOf d, N.Qp n] (Work.ELNest.Qlev L n)) :
    QPullInputs c d L (alphaPairOf d) N := by
  refine ⟨hL, hcv, ?_, ?_, ?_⟩
  · -- ## `arc`: `T^[10]` carries the near arcs of the level-`(n+1)` polygon into those of level `n`
    intro n x hx P hP
    have harc := pullQ_arc n x (notMem_nearArcs_bAng hx) (notMem_nearArcs_alpha hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · simpa [alphaPairOf_a, alphaPairOf_b] using harc.2
    · simpa [N.Qpa n, N.Qpb n] using harc.1
  · -- ## `pair`: the boundary angles of the level-`(n+1)` polygon map to boundary angles
    intro n P' hP'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP'
    rcases hP' with rfl | rfl
    · exact ⟨alphaPairOf d, by simp,
        Or.inl (by simp [alphaPairOf_a, (pullQ_pair n).2.2.1])⟩
    · exact ⟨N.Qp n, by simp,
        Or.inl (by simp [N.Qpa (n + 1), N.Qpa n, (pullQ_pair n).1])⟩
  · -- ## `one`: at most one preimage angle per fibre over the reference angle
    intro n x y hx hy hxk hyk
    exact pullQ_one n (Work.EL.midNear [alphaPairOf d, N.Qp n]) x y
      (midNear_mem_arc d N n) (midNear_ne_alpha2 d N n)
      (notMem_nearArcs_bAng hx) (notMem_nearArcs_alpha hx)
      (notMem_nearArcs_bAng hy) (notMem_nearArcs_alpha hy)
      hxk hyk

end Work.ELAssembly
