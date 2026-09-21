import Mathlib
import Submission.Work.OddRadon.Abel

/-!
# Unique continuation for the iterated Abel reduction

`abelReduceIter α k F` is the `k`-fold exponent reduction `abelReduce β F = deriv F / (2 β c)`
of the odd-dimensional Radon inversion (`Work.OddRadon`).  This file proves that, as long as
every exponent actually used is nonzero, the reduced data determine the function: if
`abelReduceIter α k f` and `abelReduceIter α k g` agree on `(0,∞)` and `f`, `g` agree on some
interval `(0,c₀)` with `c₀ > 0`, then `f = g` on all of `(0,∞)`.

Two ingredients:

* the operator is an honest linear differential operator of order `k` with leading coefficient
  `∏_{j<k} (2(α-j)c)^{-1} ≠ 0` on `(0,∞)`, so on `(0,∞)` the equation `abelReduceIter α k u = 0`
  is *equivalent* to annihilating the underlying `k`-fold derivative chain;
* a continuous function whose derivative vanishes on the (preconnected) set `(0,∞)` is constant
  there.

Consequently, peeling one reduction at a time, the difference `f - g` is a solution of a
`k`-th order linear ODE which vanishes on the nondegenerate interval `(0,c₀)`, hence everywhere
on `(0,∞)`.

## Main result

* `eq_of_abelReduceIter_eq_of_eqOn` — unique continuation for `abelReduceIter ((n:ℝ)-3/2) (n-1)`.
-/

namespace Work.OddCurve.Inv

open Set

/-- Regularity of one exponent-reduction step: if `h` is `C^(m+1)` on `(0,∞)` and `α ≠ 0`,
then `abelReduce α h` is `C^m` on `(0,∞)` (on which `c ↦ 2αc` is invertible and smooth). -/
private lemma contDiffOn_abelReduce_succ {α : ℝ} (hα : α ≠ 0) {m : ℕ} {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ (m + 1 : ℕ) h (Set.Ioi (0:ℝ))) :
    ContDiffOn ℝ (m : ℕ) (Work.OddRadon.abelReduce α h) (Set.Ioi (0:ℝ)) := by
  have hderiv : ContDiffOn ℝ (m : ℕ) (deriv h) (Set.Ioi (0:ℝ)) :=
    hh.deriv_of_isOpen isOpen_Ioi (by simp)
  have h2 : ContDiffOn ℝ (m : ℕ) (fun c : ℝ => (2 * α * c)⁻¹) (Set.Ioi (0:ℝ)) := by
    apply ContDiffOn.inv
    · fun_prop
    · intro c hc
      exact mul_ne_zero (mul_ne_zero (by norm_num) hα) (ne_of_gt hc)
  have h : Work.OddRadon.abelReduce α h = fun c : ℝ => deriv h c * (2 * α * c)⁻¹ := by
    funext c; rfl
  rw [h]
  exact hderiv.mul h2

/-- **Unique continuation for the iterated Abel reduction, in the general form.**

If `k` exponent reductions of `f` and of `g` agree on `(0,∞)` and `f`, `g` agree on `(0,c₀)`
with `c₀ > 0`, then `f = g` on `(0,∞)` — provided every exponent `α, α-1, …, α-k+1` used is
nonzero (for `k = 0` no exponent is used and the statement is the hypothesis itself). -/
private lemma eq_of_abelReduceIter_eq_of_eqOn_aux : ∀ (k : ℕ) (α : ℝ),
    (k = 0 ∨ (k : ℝ) - 1 < α) →
    ∀ {f g : ℝ → ℝ}, ContDiffOn ℝ (k : ℕ) f (Set.Ioi (0:ℝ)) →
      ContDiffOn ℝ (k : ℕ) g (Set.Ioi (0:ℝ)) →
      Set.EqOn (Work.OddRadon.abelReduceIter α k f) (Work.OddRadon.abelReduceIter α k g)
        (Set.Ioi (0:ℝ)) →
      ∀ {c₀ : ℝ}, 0 < c₀ → Set.EqOn f g (Set.Ioo (0:ℝ) c₀) →
        Set.EqOn f g (Set.Ioi (0:ℝ)) := by
  intro k
  induction k with
  | zero =>
      -- no reduction happened: the hypothesis is the conclusion
      intro α _ f g _ _ hred c₀ _ _
      simpa using hred
  | succ k ih =>
      intro α hα f g hf hg hred c₀ hc₀ hcap
      -- the exponent `α` used by the first steps is nonzero
      have hαlt : (k : ℝ) < α := by
        rcases hα with h | h
        · exact absurd h (by simp)
        · push_cast at h; linarith
      have hαne : α ≠ 0 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      -- one step of regularity, and the recursion
      have hf1 : ContDiffOn ℝ (k : ℕ) (Work.OddRadon.abelReduce α f) (Set.Ioi 0) :=
        contDiffOn_abelReduce_succ hαne hf
      have hg1 : ContDiffOn ℝ (k : ℕ) (Work.OddRadon.abelReduce α g) (Set.Ioi 0) :=
        contDiffOn_abelReduce_succ hαne hg
      have hred1 : Set.EqOn (Work.OddRadon.abelReduceIter (α - 1) k
            (Work.OddRadon.abelReduce α f))
          (Work.OddRadon.abelReduceIter (α - 1) k (Work.OddRadon.abelReduce α g))
          (Set.Ioi 0) := by
        intro c hc
        have hc' := hred hc
        rwa [Work.OddRadon.abelReduceIter_succ, Work.OddRadon.abelReduceIter_succ] at hc'
      -- the reduced functions still agree near `0` (`deriv` is a local notion)
      have hcap1 : Set.EqOn (Work.OddRadon.abelReduce α f) (Work.OddRadon.abelReduce α g)
          (Set.Ioo 0 c₀) := by
        intro c hc
        simp only [Work.OddRadon.abelReduce]
        congr 1
        exact (hcap.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hc)).deriv_eq
      have hk0 : k = 0 ∨ (k : ℝ) - 1 < α - 1 := by
        rcases eq_or_ne k 0 with hk | hk
        · exact Or.inl hk
        · exact Or.inr (by linarith)
      -- induction
      have hxy : Set.EqOn (Work.OddRadon.abelReduce α f) (Work.OddRadon.abelReduce α g)
          (Set.Ioi 0) := ih (α - 1) hk0 hf1 hg1 hred1 hc₀ hcap1
      -- on `(0,∞)` the division is by the nonzero factor `2αc`, so the derivatives agree
      have hder : Set.EqOn (deriv f) (deriv g) (Set.Ioi 0) := by
        intro x hx
        have h := hxy hx
        simp only [Work.OddRadon.abelReduce] at h
        have hb : (2 * α * x) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) hαne) (ne_of_gt hx)
        have h2 := congrArg (fun y : ℝ => y * (2 * α * x)) h
        rwa [div_mul_cancel₀ _ hb, div_mul_cancel₀ _ hb] at h2
      -- so `f - g` has vanishing derivative on the preconnected set `(0,∞)`: it is constant,
      -- and it vanishes at `c₀/2`
      have hfd : DifferentiableOn ℝ f (Set.Ioi 0) := hf.differentiableOn (by simp)
      have hgd : DifferentiableOn ℝ g (Set.Ioi 0) := hg.differentiableOn (by simp)
      have hu : DifferentiableOn ℝ (f - g) (Set.Ioi 0) := hfd.sub hgd
      have hu' : Set.EqOn (deriv (f - g)) 0 (Set.Ioi 0) := by
        intro x hx
        have h1 : deriv (f - g) x = deriv f x - deriv g x :=
          deriv_sub (hfd.differentiableAt (isOpen_Ioi.mem_nhds hx))
            (hgd.differentiableAt (isOpen_Ioi.mem_nhds hx))
        simp [h1, hder hx]
      intro y hy
      have hm : c₀ / 2 ∈ Set.Ioi (0 : ℝ) := by
        simp only [Set.mem_Ioi]; linarith
      have hcst := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hu hu' hy hm
      have hz : (f - g) y = 0 := by
        rw [hcst, Pi.sub_apply, hcap ⟨by linarith, by linarith⟩, sub_self]
      exact sub_eq_zero.mp hz

theorem eq_of_abelReduceIter_eq_of_eqOn {n : ℕ} {f g : ℝ → ℝ} (hf : ContDiffOn ℝ (n : ℕ) f (Set.Ioi (0:ℝ))) (hg : ContDiffOn ℝ (n : ℕ) g (Set.Ioi (0:ℝ))) (hred : Set.EqOn (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) f) (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) g) (Set.Ioi (0:ℝ))) {c₀ : ℝ} (hc₀ : 0 < c₀) (hcap : Set.EqOn f g (Set.Ioo (0:ℝ) c₀)) : Set.EqOn f g (Set.Ioi (0:ℝ)) := by
  -- the exponents used are `n - 3/2, n - 5/2, …, 1/2`, all nonzero
  have hα : n - 1 = 0 ∨ (((n - 1 : ℕ) : ℝ) - 1 < (n : ℝ) - 3 / 2) := by
    by_cases hn : n ≤ 1
    · exact Or.inl (by omega)
    · refine Or.inr ?_
      have hn1 : 1 ≤ n := by omega
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn1]; norm_num
      rw [hcast]; linarith
  -- the reduction of order `n - 1` only needs `C^(n-1)` regularity
  have hf' : ContDiffOn ℝ (n - 1 : ℕ) f (Set.Ioi (0:ℝ)) :=
    hf.of_le (by exact_mod_cast Nat.sub_le n 1)
  have hg' : ContDiffOn ℝ (n - 1 : ℕ) g (Set.Ioi (0:ℝ)) :=
    hg.of_le (by exact_mod_cast Nat.sub_le n 1)
  exact eq_of_abelReduceIter_eq_of_eqOn_aux (n - 1) ((n : ℝ) - 3 / 2) hα hf' hg' hred hc₀ hcap

end Work.OddCurve.Inv
