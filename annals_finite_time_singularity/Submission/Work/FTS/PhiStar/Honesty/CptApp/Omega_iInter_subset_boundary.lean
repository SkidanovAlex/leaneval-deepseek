/-
# `Omega_iInter_subset_boundary`

The shrinking sets `Omega n` of `CptApp/Defs.lean` (where the radial/angular cutoffs
`chiR n`, `zetaR n` are not simultaneously equal to `1`) have

`⋂ n, (Omega (n+1) ∩ Dom) ⊆ {p.1 = 0} ∪ {p.2 = 0} ∪ {p.2 = π/2}`,

i.e. the only points that survive in every `Omega n` (inside the domain
`Dom = [0,∞) × [0,π/2]`) lie on one of the three boundary lines.

Proof: a point of `Dom` with `p.1 > 0`, `p.2 > 0` and `p.2 < π/2` is at positive
distance `c = min (min p.1 p.2) (π/2 - p.2)` from all four boundary lines, so for
`m` large enough that `2/m ≤ c` and `m > p.1` none of the four defining
disjuncts of `Omega m` can hold.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

/-- For every real `c > 0` and every `a : ℝ` there is a natural number `m ≥ 1` with
`a < m` (so that `m < a` fails) and `2 / m ≤ c` (so that `p < 2/m` fails for every
`p ≥ c`). -/
lemma exists_nat_two_div_le {a c : ℝ} (hc : 0 < c) :
    ∃ m : ℕ, 1 ≤ m ∧ a < (m : ℝ) ∧ 2 / (m : ℝ) ≤ c := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (a + 1) (2 / c))
  refine ⟨max N 1, le_max_right _ _, ?_, ?_⟩
  · have h1 : a + 1 ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
    have h2 : (N : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left N 1
    linarith
  · have h2 : 2 / c ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
    have h3 : (2 / c : ℝ) ≤ ((max N 1 : ℕ) : ℝ) :=
      le_trans h2 (by exact_mod_cast le_max_left N 1)
    have hmpos : (0 : ℝ) < ((max N 1 : ℕ) : ℝ) := by
      have h4 : (1 : ℕ) ≤ max N 1 := le_max_right _ _
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one h4
    have h5 : 2 ≤ ((max N 1 : ℕ) : ℝ) * c := (div_le_iff₀ hc).mp h3
    exact (div_le_iff₀ hmpos).mpr (by linarith)

theorem Omega_iInter_subset_boundary :
    (⋂ n : ℕ, (Work.FTS.PhiStar.Honesty.CptApp.Omega (n + 1) ∩ Work.Spaces.Dom))
      ⊆ ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
          ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) := by
  intro p hp
  rw [Set.mem_iInter] at hp
  have hDom : p ∈ Work.Spaces.Dom := (hp 0).2
  simp only [Work.Spaces.Dom, Work.Spaces.Iz, Work.Spaces.Iθ, Set.mem_prod, Set.mem_Ici,
    Set.mem_Icc] at hDom
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hnot
  obtain ⟨⟨ha, hb⟩, hc⟩ := hnot
  have h1 : 0 < p.1 := lt_of_le_of_ne hDom.1 (Ne.symm ha)
  have h2 : 0 < p.2 := lt_of_le_of_ne hDom.2.1 (Ne.symm hb)
  have h3 : p.2 < Real.pi / 2 := lt_of_le_of_ne hDom.2.2 hc
  have hcpos : 0 < min (min p.1 p.2) (Real.pi / 2 - p.2) :=
    lt_min (lt_min h1 h2) (by linarith)
  obtain ⟨m, hm1, hma, hmc⟩ := exists_nat_two_div_le (a := p.1)
    (c := min (min p.1 p.2) (Real.pi / 2 - p.2)) hcpos
  have hc_le_1 : min (min p.1 p.2) (Real.pi / 2 - p.2) ≤ p.1 :=
    le_trans (min_le_left (min p.1 p.2) (Real.pi / 2 - p.2)) (min_le_left p.1 p.2)
  have hc_le_2 : min (min p.1 p.2) (Real.pi / 2 - p.2) ≤ p.2 :=
    le_trans (min_le_left (min p.1 p.2) (Real.pi / 2 - p.2)) (min_le_right p.1 p.2)
  have hc_le_3 : min (min p.1 p.2) (Real.pi / 2 - p.2) ≤ Real.pi / 2 - p.2 :=
    min_le_right _ _
  have hle1 : 2 / (m : ℝ) ≤ p.1 := le_trans hmc hc_le_1
  have hle2 : 2 / (m : ℝ) ≤ p.2 := le_trans hmc hc_le_2
  have hle3 : 2 / (m : ℝ) ≤ Real.pi / 2 - p.2 := le_trans hmc hc_le_3
  have hmem : p ∈ Work.FTS.PhiStar.Honesty.CptApp.Omega m := by
    have h := (hp (m - 1)).1
    rwa [Nat.sub_add_cancel hm1] at h
  simp only [Work.FTS.PhiStar.Honesty.CptApp.Omega, Set.mem_ofPred_eq] at hmem
  rcases hmem with h | h | h | h
  · linarith
  · linarith
  · linarith
  · linarith

end Work.FTS.PhiStar.Honesty.CptApp
