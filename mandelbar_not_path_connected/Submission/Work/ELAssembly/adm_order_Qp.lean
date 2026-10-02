import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- The first three entries of a strictly increasing four-element list are strictly increasing. -/
private lemma pairwise_four_three {a b c d : ℝ} (h : ([a, b, c, d] : List ℝ).Pairwise (· < ·)) :
    a < b ∧ b < c ∧ c < d := by
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false] at h
  exact ⟨h.1 b (by simp), h.2.1 c (by simp), h.2.2.1 d (by simp)⟩

/-- **The order of the four angles of the level-`n` `z₁`-polygon.**  If `[P0, N.Qp n]` is
admissible, its flattened angle list is `[P0.a, P0.b, βₙ', βₙ + 1]` (`N.Qpa`, `N.Qpb`), so
`Work.EL.PolyAdmissible.cyc` gives them strictly increasing, and the `headD`-bound gives
`βₙ + 1 < P0.a + 1`; hence `P0.a < P0.b < βₙ' < βₙ + 1 < P0.a + 1`, i.e. the four conclusions
below. -/
theorem adm_order_Qp {c : ℂ} {d : Work.EL.RootParabolic c} {P0 : Work.EL.CoPair d.hN}
    {N : Work.ELAssembly.NestPairs d} {n : ℕ} (h : Work.EL.PolyAdmissible [P0, N.Qp n]) :
    P0.a < P0.b ∧ P0.b < Work.ELNest.bAng' n ∧
      Work.ELNest.bAng' n < Work.ELNest.bAng n + 1 ∧ Work.ELNest.bAng n < P0.a := by
  have hflat : ([P0, N.Qp n].flatMap fun P => [P.a, P.b])
      = [P0.a, P0.b, Work.ELNest.bAng' n, Work.ELNest.bAng n + 1] := by
    simp [N.Qpa n, N.Qpb n]
  have hpw : ([P0.a, P0.b, Work.ELNest.bAng' n, Work.ELNest.bAng n + 1] : List ℝ).Pairwise
      (· < ·) := by
    rw [← hflat]
    exact h.cyc.2.1
  obtain ⟨h1, h2, h3⟩ := pairwise_four_three hpw
  have hhead := h.cyc.2.2
  rw [hflat] at hhead
  have h4 : Work.ELNest.bAng n < P0.a := by
    have hh := hhead (Work.ELNest.bAng n + 1) (by simp)
    have hhd : ([P0.a, P0.b, Work.ELNest.bAng' n, Work.ELNest.bAng n + 1] : List ℝ).headD 0
        = P0.a := rfl
    rw [hhd] at hh
    linarith
  exact ⟨h1, h2, h3, h4⟩

end Work.ELAssembly
