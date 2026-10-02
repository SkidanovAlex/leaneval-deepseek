import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELNest.Qlev_facts
import Submission.Work.ELNest.bAng_range
import Submission.Work.ELNest.T_iterate_bAng
import Submission.Work.ELTop.nearArc_angle_data
import Submission.Work.ELAssembly.adm_order_Qp
import Submission.Work.ELAssembly.adm_bounds_Qp
import Submission.Work.ELAssembly.mem_nearArcs_of_Ioo
import Submission.Work.ELAssembly.nearArc_length_le
import Submission.Work.ELAssembly.limit_step_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Classical Set Filter
open scoped Topology

/-- **The angle data of `QPullInputs` pins the `α`-pair `P0` down.**  Under the hypotheses of
`Work.ELAssembly.pullQ_bij` (an `I : QPullInputs c d L P0 N` and admissibility of every level
`[P0, N.Qp n]`), the pair `P0` must be the root-portrait pair: `P0.a = Work.EL.alpha1 = 371/1023`
and `P0.b = Work.EL.alpha2 = 404/1023`.

**Why this is true (the argument to formalise).**  `N.Qpa n`/`N.Qpb n` give the level-`n` angles
`βₙ' = Work.ELNest.bAng' n`, `βₙ + 1 = Work.ELNest.bAng n + 1`, and `βₙ → Work.EL.alpha1`,
`βₙ' → Work.EL.alpha2`.  From `hadm n` (the flattened list `[P0.a, P0.b, βₙ', βₙ+1]` is strictly
cyclically ordered) one gets, for every `n`,

  `P0.a < P0.b < βₙ' < βₙ + 1 < P0.a + 1`,

hence in the limit `Work.EL.alpha1 ≤ P0.a < P0.b ≤ Work.EL.alpha2`.

Let `ℓₙ' := β'_{n+1} - P0.b ≥ 0` and `ℓₙ := (βₙ' - P0.b) + (P0.a - βₙ) ≥ 0` (the total length of the
near arcs of the level-`n` polygon).  Take `x ∈ (P0.b, β'_{n+1})`: then `x` lies in no closed far
arc of `[P0, N.Qp (n+1)]` (for the pair `P0` because `x > P0.b`; for the pair `N.Qp (n+1)` because
`¬ InClosedArc x β'_{n+1} (β_{n+1}+1) ↔ x > β_{n+1}`, and `x > P0.b ≥ α₁ > β_{n+1}`), so `I.arc`
gives `¬ InClosedArc (T^[10] x) Q.a Q.b` for every `Q ∈ [P0, N.Qp n]`: the image of the whole
interval `(P0.b, β'_{n+1})` lies in the near arcs of the level-`n` polygon.  Since
`T^[10] x = Int.fract (1024 x)` maps that interval (of length `ℓₙ'`) onto a (circular) arc of
length `1024 ℓₙ'` — and an arc of length `1024 ℓₙ'` contained in the two disjoint near arcs of
total length `ℓₙ` must satisfy `1024 ℓₙ' ≤ ℓₙ` (and, if `1024 ℓₙ' ≥ 1`, the image is the whole
circle, which is not contained in the near arcs) — one obtains

  `1024 (β'_{n+1} - P0.b) ≤ (βₙ' - P0.b) + (P0.a - βₙ)`   for every `n`.

The same reasoning applied to `x ∈ (β_{n+1} + 1, P0.a + 1)` gives

  `1024 (P0.a - β_{n+1}) ≤ (βₙ' - P0.b) + (P0.a - βₙ)`   for every `n`.

Adding the two and letting `n → ∞` (so `βₙ' → α₂`, `βₙ → α₁`) yields
`1024 · S ≤ 2 · S` for `S = (α₂ - P0.b) + (P0.a - α₁) ≥ 0`, hence `S = 0`, i.e.
`P0.a = α₁` and `P0.b = α₂`. -/
theorem pullQ_P0_eq {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (I : QPullInputs c d L P0 N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [P0, N.Qp n]) :
    P0.a = Work.EL.alpha1 ∧ P0.b = Work.EL.alpha2 := by
  -- the ordering/limit bounds `α₁ ≤ P0.a < P0.b ≤ α₂`
  obtain ⟨ha1, _hab, hb2⟩ := adm_bounds_Qp (P0 := P0) (N := N) hadm
  -- the two length bounds of every level, added
  have key : ∀ n : ℕ,
      (1024 : ℝ) * ((Work.ELNest.bAng' (n + 1) - P0.b) + (P0.a - Work.ELNest.bAng (n + 1)))
        ≤ 2 * ((Work.ELNest.bAng' n - P0.b) + (P0.a - Work.ELNest.bAng n)) := by
    intro n
    -- the strict cyclic order of the level-`n` and level-`(n+1)` polygons
    obtain ⟨h1, h2, h3, h4⟩ := adm_order_Qp (P0 := P0) (N := N) (n := n) (hadm n)
    obtain ⟨_g1, g2, _g3, g4⟩ := adm_order_Qp (P0 := P0) (N := N) (n := n + 1) (hadm (n + 1))
    have hP0mem : P0 ∈ [P0, N.Qp n] := by simp
    have hQpmem : N.Qp n ∈ [P0, N.Qp n] := by simp
    -- the image of the whole near arc `(P0.b, β'_{n+1})` misses the far arcs of the level-`n` polygon
    have ineq1 : (1024 : ℝ) * (Work.ELNest.bAng' (n + 1) - P0.b)
        ≤ (Work.ELNest.bAng' n - P0.b) + (P0.a - Work.ELNest.bAng n) := by
      have h := nearArc_length_le (A := P0.a) (B := P0.b) (C := Work.ELNest.bAng' n)
        (D := Work.ELNest.bAng n + 1) (x₁ := P0.b) (x₂ := Work.ELNest.bAng' (n + 1))
        h1 h2 h3 (by linarith) g2 ?_
      · linarith
      · intro x hx
        have hnear := mem_nearArcs_of_Ioo (P0 := P0) (N := N) (n := n) hadm (Or.inl ⟨hx.1, hx.2⟩)
        have harc := I.arc n x hnear
        exact ⟨harc P0 hP0mem,
          by simpa [N.Qpa n, N.Qpb n] using harc (N.Qp n) hQpmem⟩
    -- the image of the other near arc `(β_{n+1} + 1, P0.a + 1)` misses them too
    have ineq2 : (1024 : ℝ) * (P0.a - Work.ELNest.bAng (n + 1))
        ≤ (Work.ELNest.bAng' n - P0.b) + (P0.a - Work.ELNest.bAng n) := by
      have h := nearArc_length_le (A := P0.a) (B := P0.b) (C := Work.ELNest.bAng' n)
        (D := Work.ELNest.bAng n + 1) (x₁ := Work.ELNest.bAng (n + 1) + 1) (x₂ := P0.a + 1)
        h1 h2 h3 (by linarith) (by linarith) ?_
      · linarith
      · intro x hx
        have hnear := mem_nearArcs_of_Ioo (P0 := P0) (N := N) (n := n) hadm (Or.inr ⟨hx.1, hx.2⟩)
        have harc := I.arc n x hnear
        exact ⟨harc P0 hP0mem,
          by simpa [N.Qpa n, N.Qpb n] using harc (N.Qp n) hQpmem⟩
    linarith
  exact limit_step_bAng (a := P0.a) (b := P0.b) ha1 hb2 key

end Work.ELAssembly
