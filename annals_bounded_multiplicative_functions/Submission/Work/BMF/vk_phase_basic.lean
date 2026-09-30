import Mathlib
import Submission.Work.BMF.logPhase_iteratedDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The logarithmic phase `y ↦ -(t·log(y+u))/(2π)` is smooth on any set on which `y + u > 0`. -/
private lemma phase_contDiffOn_of (t u : ℝ) (n : WithTop ℕ∞) (s : Set ℝ)
    (h : ∀ y ∈ s, 0 < y + u) :
    ContDiffOn ℝ n (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) s := by
  have hlog : ContDiffOn ℝ n (fun y : ℝ => Real.log (y + u)) s := by
    refine Real.contDiffOn_log.comp ?_ ?_
    · exact ((contDiff_id : ContDiff ℝ n (fun y : ℝ => y)).add
        (contDiff_const : ContDiff ℝ n (fun _ : ℝ => u))).contDiffOn
    · intro y hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (h y hy)
  have hnum : ContDiffOn ℝ n (fun y : ℝ => -(t * Real.log (y + u))) s :=
    (contDiffOn_const.mul hlog).neg
  exact ContDiffOn.div hnum contDiffOn_const (fun y _ => by positivity)

/-- All iterated derivatives of the logarithmic phase are continuous on `[0,M]` and
differentiable on `(0,M)`. -/
private lemma phase_iteratedDeriv_cntDiff (t u M : ℝ) (hu : 0 < u) (m : ℕ) :
    ContinuousOn (iteratedDeriv m (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)))
      (Set.Icc 0 M) ∧
    DifferentiableOn ℝ (iteratedDeriv m (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)))
      (Set.Ioo 0 M) := by
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · have hcd := phase_contDiffOn_of t u (⊤ : WithTop ℕ∞) (Set.Ioi (-u))
      (fun y hy => by
        have hy' : -u < y := hy
        linarith)
    refine ⟨?_, ?_⟩
    · simpa using hcd.continuousOn.mono (fun x hx => by
        have h : (0 : ℝ) ≤ x := hx.1
        show -u < x
        linarith)
    · simpa using (hcd.differentiableOn (by simp)).mono (fun x hx => by
        have h : (0 : ℝ) < x := hx.1
        show -u < x
        linarith)
  · have hm1 : 1 ≤ m := hm
    have hderiv : ∀ x : ℝ, 0 < x + u →
        iteratedDeriv m (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) x =
          (-(t / (2 * Real.pi)) * (-1 : ℝ) ^ (m - 1) * (Nat.factorial (m - 1) : ℝ))
            / (x + u) ^ m := by
      intro x hx
      exact logPhase_iteratedDeriv t u m hm1 x hx
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousOn
          (fun x : ℝ =>
            (-(t / (2 * Real.pi)) * (-1 : ℝ) ^ (m - 1) * (Nat.factorial (m - 1) : ℝ))
              / (x + u) ^ m) (Set.Icc 0 M) := by
        refine ContinuousOn.div continuousOn_const ?_ ?_
        · exact ((continuous_id.add continuous_const).pow m).continuousOn
        · intro x hx
          exact pow_ne_zero m (ne_of_gt (by linarith [hx.1, hu] : (0 : ℝ) < x + u))
      exact hcont.congr (fun x hx => hderiv x (by linarith [hx.1, hu]))
    · have hdiff : DifferentiableOn ℝ
          (fun x : ℝ =>
            (-(t / (2 * Real.pi)) * (-1 : ℝ) ^ (m - 1) * (Nat.factorial (m - 1) : ℝ))
              / (x + u) ^ m) (Set.Ioo 0 M) := by
        refine DifferentiableOn.div (differentiableOn_const _) ?_ ?_
        · exact ((differentiable_id.add_const u).pow m).differentiableOn
        · intro x hx
          exact pow_ne_zero m (ne_of_gt (by linarith [hx.1, hu] : (0 : ℝ) < x + u))
      exact hdiff.congr (fun x hx => hderiv x (by linarith [hx.1, hu]))

/-- **Basic calculus facts for the logarithmic phase** `F(y) = -(t log(y+u))/(2π)` for `y > 0` and
`u > 0`: `F` is `C^k` on `(0, M+1)`, its `(k-1)`-st iterated derivative is continuous on `[0,M]`,
and that iterated derivative is differentiable on `(0,M)`.

Route.  `Real.contDiffOn_log` is `ContDiffOn ℝ n Real.log {0}ᶜ`; composing with the affine map
`y ↦ y + u` (which sends `(0,M+1)` into `{0}ᶜ` because `y + u > 0`) and multiplying by the constant
`-t/(2π)` gives the first claim.  For the other two, `Work.BMF.logPhase_iteratedDeriv` identifies
`iteratedDeriv (k-1) F x` with `c * (x+u)^{-(k-1)}` for `c = -(t/(2π)) (-1)^{k-2} (k-2)!` when
`k ≥ 2`, and with `F x` itself when `k = 1`; both are continuous on `Icc 0 M` and differentiable on
`Ioo 0 M` because `x + u > 0` there. -/
theorem vk_phase_basic (k : ℕ) (hk : 1 ≤ k) (t u M : ℝ) (hu : 0 < u) :
    ContDiffOn ℝ k (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) (Set.Ioo 0 (M + 1)) ∧
    ContinuousOn (fun x => iteratedDeriv (k - 1)
        (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) x) (Set.Icc 0 M) ∧
    DifferentiableOn ℝ (fun x => iteratedDeriv (k - 1)
        (fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) x) (Set.Ioo 0 M) := by
  refine ⟨?_, phase_iteratedDeriv_cntDiff t u M hu (k - 1)⟩
  exact phase_contDiffOn_of t u (k : WithTop ℕ∞) (Set.Ioo 0 (M + 1))
    (fun y hy => by linarith [hy.1, hu])

end Work.BMF
