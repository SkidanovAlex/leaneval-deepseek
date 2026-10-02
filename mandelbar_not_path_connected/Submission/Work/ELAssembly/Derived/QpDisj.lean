/-
# `ELAssembly.Derived.QpDisj` — the pair curves of the `z₁`-nest are pairwise disjoint

The field `CertGeometry.Qp_disj` is derived from the **two-ray portrait** of the nest: if every
level-`n` landing point `(Qp n).y` carried only the two rays of angles `βₙ`, `βₙ'` of
`Ico 0 1` (`Work.ELAssembly.Qp_portrait`, proved from the orbit-portrait count), then two
different levels cannot share their landing point: the four angles `β_m, β_m', β_n, β_n'` are
distinct modulo `1`, so a common landing point would carry at least three rays.  With the
landing points distinct and the four angles incongruent modulo `1`, the curves are disjoint by
`Work.ELAssembly.pairCurve_disjoint_of`.
-/
import Mathlib
import Submission.Work.ELAssembly.landsN_add_int
import Submission.Work.ELAssembly.pairCurve_disjoint_of
import Submission.Work.ELAssembly.Derived.Fields
import Submission.Work.ELAssembly.Derived.Bases
import Submission.Work.ELNest.bAng_nest_arc
import Submission.Work.ELNest.T_iterate_bAng

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

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-- The level-`n` lower angle `βₙ` is strictly increasing in `n`. -/
theorem bAng_strictMono : StrictMono Work.ELNest.bAng :=
  strictMono_nat_of_lt_succ Work.ELNest.bAng_mono

/-- The level-`n` upper angle `βₙ'` is strictly decreasing in `n`. -/
theorem bAng'_strictAnti : StrictAnti Work.ELNest.bAng' :=
  strictAnti_nat_of_succ_lt Work.ELNest.bAng'_anti

/-- Both angles of the level-`n` pair lie in `Ico 0 1`. -/
theorem bAng_mem_Ico (n : ℕ) :
    Work.ELNest.bAng n ∈ Set.Ico (0 : ℝ) 1 ∧ Work.ELNest.bAng' n ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨⟨le_of_lt (Work.ELNest.bAng_pos n),
      lt_of_lt_of_le (Work.ELNest.bAng_lt_alpha1 n) (le_of_lt Work.ELNest.alpha1_lt_one)⟩,
    ⟨le_of_lt (lt_trans (by norm_num [Work.ELNest.alpha2]) (Work.ELNest.bAng'_gt_alpha2 n)),
      lt_of_le_of_lt (Work.ELNest.bAng'_le_beta0' n) Work.ELNest.beta0'_lt_one⟩⟩

/-- The lower angle `βₙ` of level `m` is never the upper angle `βₙ'` of level `n`. -/
theorem bAng_lt_bAng'_levels (m n : ℕ) : Work.ELNest.bAng m < Work.ELNest.bAng' n :=
  lt_of_lt_of_le (Work.ELNest.bAng_lt_alpha1 m)
    (le_of_lt (lt_trans Work.ELNest.alpha1_lt_alpha2 (Work.ELNest.bAng'_gt_alpha2 n)))

/-- **The landing points of two different levels of the `z₁`-nest differ**, from the two-ray
portrait of each level. -/
theorem Qp_y_ne_of_portrait {d : Work.EL.RootParabolic c} (N : NestPairs d)
    (hport : ∀ (n : ℕ) (θ : ℝ), θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ (N.Qp n).y ↔ θ = Work.ELNest.bAng n ∨ θ = Work.ELNest.bAng' n))
    {m n : ℕ} (hmn : m ≠ n) : (N.Qp m).y ≠ (N.Qp n).y := by
  obtain ⟨hb, -⟩ := bAng_mem_Ico m
  intro h
  have hm : Work.EL.LandsN d.hN (Work.ELNest.bAng m) (N.Qp m).y :=
    (landsN_add_int d.hN (Work.ELNest.bAng m) 1 (N.Qp m).y).mp
      (by simpa using (N.Qpb m ▸ (N.Qp m).lands_b : Work.EL.LandsN d.hN
        (Work.ELNest.bAng m + 1) (N.Qp m).y))
  have hn : Work.EL.LandsN d.hN (Work.ELNest.bAng m) (N.Qp n).y := by rw [← h]; exact hm
  rcases (hport n (Work.ELNest.bAng m) hb).mp hn with heq | heq
  · rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
    · exact absurd heq (ne_of_lt (bAng_strictMono hlt))
    · exact absurd heq (ne_of_gt (bAng_strictMono hgt))
  · exact absurd heq (ne_of_lt (bAng_lt_bAng'_levels m n))

/-- **The level-`m` and level-`n` pair curves of the `z₁`-nest are disjoint** (the field
`CertGeometry.Qp_disj`, derived from the portraits and the angle arithmetic). -/
theorem Qp_pairCurve_disjoint_of_portrait {d : Work.EL.RootParabolic c} (N : NestPairs d)
    (hport : ∀ (n : ℕ) (θ : ℝ), θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ (N.Qp n).y ↔ θ = Work.ELNest.bAng n ∨ θ = Work.ELNest.bAng' n))
    {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (Work.EL.pairCurve (N.Qp m)) (Work.EL.pairCurve (N.Qp n)) := by
  have hmn_lt : ∀ {m n : ℕ}, m < n →
      Disjoint (Work.EL.pairCurve (N.Qp m)) (Work.EL.pairCurve (N.Qp n)) := by
    intro m n hmn
    obtain ⟨hb, hb'⟩ := bAng_mem_Ico m
    obtain ⟨hc, hc'⟩ := bAng_mem_Ico n
    have h1 : Work.ELNest.bAng m < Work.ELNest.bAng n := bAng_strictMono hmn
    have h2 : Work.ELNest.bAng' n < Work.ELNest.bAng' m := bAng'_strictAnti hmn
    have d1 : (0 : ℝ) < Work.ELNest.bAng' m - Work.ELNest.bAng' n := by linarith
    have e1 : Work.ELNest.bAng' m - Work.ELNest.bAng' n < 1 := by linarith [hb'.2, hc'.1]
    have d2 : (0 : ℝ) < Work.ELNest.bAng n + 1 - Work.ELNest.bAng' m := by
      linarith [hb'.2, Work.ELNest.bAng_pos n]
    have e2 : Work.ELNest.bAng n + 1 - Work.ELNest.bAng' m < 1 := by
      linarith [bAng_lt_bAng'_levels n m]
    have d3 : (0 : ℝ) < Work.ELNest.bAng m + 1 - Work.ELNest.bAng' n := by
      linarith [hc'.2, Work.ELNest.bAng_pos m]
    have e3 : Work.ELNest.bAng m + 1 - Work.ELNest.bAng' n < 1 := by
      linarith [bAng_lt_bAng'_levels m n]
    have d4 : (0 : ℝ) < Work.ELNest.bAng n + 1 - (Work.ELNest.bAng m + 1) := by
      have h : Work.ELNest.bAng n + 1 - (Work.ELNest.bAng m + 1)
          = Work.ELNest.bAng n - Work.ELNest.bAng m := by ring
      rw [h]; linarith
    have e4 : Work.ELNest.bAng n + 1 - (Work.ELNest.bAng m + 1) < 1 := by
      have h : Work.ELNest.bAng n + 1 - (Work.ELNest.bAng m + 1)
          = Work.ELNest.bAng n - Work.ELNest.bAng m := by ring
      rw [h]; linarith [hc.2, hb.1]
    refine pairCurve_disjoint_of d.hN (N.Qp m) (N.Qp n) ?_ ?_ ?_ ?_
      (Qp_y_ne_of_portrait N hport (ne_of_lt hmn))
    · intro k
      rw [N.Qpa m, N.Qpa n]
      exact (ne_add_int_of_sub (x := Work.ELNest.bAng' n) (y := Work.ELNest.bAng' m)
        d1 e1).2 k
    · intro k
      rw [N.Qpb n, N.Qpa m]
      exact (ne_add_int_of_sub (x := Work.ELNest.bAng' m) (y := Work.ELNest.bAng n + 1)
        d2 e2).1 k
    · intro k
      rw [N.Qpa n, N.Qpb m]
      exact (ne_add_int_of_sub (x := Work.ELNest.bAng' n) (y := Work.ELNest.bAng m + 1)
        d3 e3).2 k
    · intro k
      rw [N.Qpb n, N.Qpb m]
      exact (ne_add_int_of_sub (x := Work.ELNest.bAng m + 1) (y := Work.ELNest.bAng n + 1)
        d4 e4).1 k
  rcases Nat.lt_or_gt_of_ne hmn with h | h
  · exact hmn_lt h
  · exact (hmn_lt h).symm

end Work.ELAssembly
