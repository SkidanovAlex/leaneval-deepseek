import Mathlib
import Submission.Work.ELNest.Qnest_shrinks

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

/-- **The landing point of the level-`n+1` pair of the `z₁`-nest lies in the level-`n` region** (the `n`-th case of `Work.ELNest.NestData.Qp1_land_mem_Q0`).  `(Qp (n+1)).y` lies on the frontier of `Q̂_{n+1}` inside `K c`, hence in `closure Q̂_{n+1} ⊆ closure Q̂_n`; the only points of `frontier Q̂_n ∩ K c` are `z₁` and `(Qp n).y`, and `(Qp (n+1)).y` equals neither. -/
theorem landing_succ_mem {c : ℂ} (S : Work.ELNest.NestData c) (n : ℕ) :
    (S.Qp (n + 1)).y ∈ S.Q n := by
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  have hRn : (1 : ℝ) < Work.ELNest.Qlev S.L n := (Work.ELNest.Qlev_facts S.hL n).1
  have hRn1 : (1 : ℝ) < Work.ELNest.Qlev S.L (n + 1) := (Work.ELNest.Qlev_facts S.hL (n + 1)).1
  have hyK : (S.Qp (n + 1)).y ∈ Work.EL.K c :=
    Work.ELTop.landsN_mem_K S.d.hN (S.Qp (n + 1)).lands_a
  have hfr1 : frontier (S.Q (n + 1)) ∩ Work.EL.K c
      = {z : ℂ | ∃ P ∈ [S.P0, S.Qp (n + 1)], P.y = z} :=
    Work.ELTop.frontier_polyRegion_inter_K S.d.hN hJ [S.P0, S.Qp (n + 1)] (S.Q_adm (n + 1))
      hRn1 (Work.ELTop.polyCurve_isJordan S.d.hN [S.P0, S.Qp (n + 1)] (S.Q_adm (n + 1)) hRn1)
  have hfr0 : frontier (S.Q n) ∩ Work.EL.K c
      = {z : ℂ | ∃ P ∈ [S.P0, S.Qp n], P.y = z} :=
    Work.ELTop.frontier_polyRegion_inter_K S.d.hN hJ [S.P0, S.Qp n] (S.Q_adm n)
      hRn (Work.ELTop.polyCurve_isJordan S.d.hN [S.P0, S.Qp n] (S.Q_adm n) hRn)
  have hy_cl1 : (S.Qp (n + 1)).y ∈ closure (S.Q (n + 1)) := by
    apply frontier_subset_closure
    have hmem : (S.Qp (n + 1)).y ∈ frontier (S.Q (n + 1)) ∩ Work.EL.K c := by
      rw [hfr1]
      exact ⟨S.Qp (n + 1), by simp, rfl⟩
    exact hmem.1
  have hy_cl0 : (S.Qp (n + 1)).y ∈ closure (S.Q n) :=
    closure_mono (Work.ELNest.NestData.Q_succ_subset S n) hy_cl1
  rw [closure_eq_self_union_frontier] at hy_cl0
  rcases hy_cl0 with h | h
  · exact h
  · exfalso
    have hfx : (S.Qp (n + 1)).y ∈ frontier (S.Q n) ∩ Work.EL.K c := ⟨h, hyK⟩
    rw [hfr0] at hfx
    obtain ⟨P, hP, hPy⟩ := hfx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact S.Qne (n + 1) (by rw [← hPy, S.P0y])
    · have hdisj : Disjoint (Work.EL.pairCurve (S.Qp n)) (Work.EL.pairCurve (S.Qp (n + 1))) :=
        S.Qp_disj n (n + 1) (by omega)
      have h1 : (S.Qp n).y ∈ Work.EL.pairCurve (S.Qp n) := by
        rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inl rfl)
      have h2 : (S.Qp n).y ∈ Work.EL.pairCurve (S.Qp (n + 1)) := by
        rw [hPy, Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inl rfl)
      exact (Set.disjoint_left.mp hdisj h1) h2

end Work.GATE2
