import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pCoreSeries_mono`

The upper `p`-series `1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ O_{p',p,p'}(G) ≤ ...` of a finite group
is increasing: this is the trivial half of the defining property of a *series*.

The mathematical content is just that each step is obtained by taking the preimage of a
`π`-core of the quotient `G / O_{...}(G)`, and `O_π` always contains the trivial subgroup;
hence the preimage contains the kernel of the quotient map, which is precisely the previous
term of the series.
-/

namespace Work.Fitting

variable {G : Type*} [Group G]

/-- Each term of the upper `p`-series is contained in the next one. -/
theorem pCoreSeries_le_succ (p : ℕ) (G : Type*) [Group G] (n : ℕ) :
    pCoreSeries p G n ≤ pCoreSeries p G (n + 1) := by
  rw [pCoreSeries_succ]
  intro x hx
  rw [Subgroup.mem_comap]
  have h1 : QuotientGroup.mk' (pCoreSeries p G n) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [h1]
  exact Subgroup.one_mem _

theorem pCoreSeries_mono (p : ℕ) (G : Type*) [Group G] [Finite G] :
    Monotone (Work.Fitting.pCoreSeries p G) :=
  monotone_nat_of_le_succ fun n => pCoreSeries_le_succ p G n

end Work.Fitting
