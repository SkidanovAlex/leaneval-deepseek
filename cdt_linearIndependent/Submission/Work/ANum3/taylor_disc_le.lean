import Mathlib
import Submission.Work.ANum3.norm_one_le_of_hasDerivAt_norm_le
import Submission.Work.ANum3.norm_deriv_sub_le_of_ball

/-!
# Second-order Taylor estimate on a disc (complex variable)

If `f : ℂ → ℂ` is complex differentiable on the closed disc `‖z - c‖ ≤ ρ`, with `deriv f`
differentiable there, `‖deriv f c‖ ≤ M` and `‖deriv (deriv f) z‖ ≤ C` on the disc, then for
every `w` in the disc

  `‖f w - f c‖ ≤ M * ρ + C * ρ ^ 2 / 2`.

The proof integrates the second-order Taylor remainder along the segment `c → w`: with
`γ t = c + t • (w - c)` and `A = deriv f c`, the function

  `g t = f (γ t) - f c - A * (t • (w - c))`

satisfies `g 0 = 0`, `g 1 = f w - f c - A * (w - c)` and `‖g' t‖ ≤ (C ‖w-c‖²) t`, so the
one-variable estimate `norm_one_le_of_hasDerivAt_norm_le` gives `‖g 1‖ ≤ C ‖w-c‖² / 2`.
The bound `‖deriv f (γ t) - deriv f c‖ ≤ C ‖γ t - c‖` is the mean value inequality
`norm_deriv_sub_le_of_ball` applied to `deriv f` on the closed disc, and `‖γ t - c‖ = t ‖w-c‖`.

The chain rules `HasDerivAt` for `t ↦ f (γ t)` and `t ↦ deriv f (γ t)` are
`hasDerivAt_comp_curve`, proved here for complex functions restricted to real curves.
-/

namespace Work.ANum3

/-- Chain rule for a real curve into `ℂ` composed with a complex-differentiable function:
if `f` is complex differentiable at `x + t • y`, then `s ↦ f (x + s • y)` has derivative
`deriv f (x + t • y) * y` at `t`. -/
theorem hasDerivAt_comp_curve (f : ℂ → ℂ) {x y : ℂ} {t : ℝ}
    (hf : DifferentiableAt ℂ f (x + t • y)) :
    HasDerivAt (fun s : ℝ => f (x + s • y)) ((deriv f (x + t • y)) * y) t := by
  have hγ : HasDerivAt (fun s : ℝ => x + s • y) y t := by
    have h1 : HasDerivAt (fun s : ℝ => x + s • y) ((1 : ℝ) • y) t :=
      ((hasDerivAt_id t).smul_const y).const_add x
    simpa using h1
  have hF : HasFDerivAt f (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ f (x + t • y)))
      (x + t • y) := (hf.hasFDerivAt).restrictScalars ℝ
  have h := hF.comp_hasDerivAt t hγ
  simp only [ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul] at h
  exact h

/-- **Second-order Taylor estimate on a disc.**  Under the hypotheses of the statement, for
every `w` with `‖w - c‖ ≤ ρ` we have `‖f w - f c‖ ≤ M * ρ + C * ρ ^ 2 / 2`. -/
theorem taylor_disc_le {f : ℂ → ℂ} {c : ℂ} {ρ M C : ℝ} (hρ : 0 ≤ ρ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hf : ∀ z : ℂ, ‖z - c‖ ≤ ρ → DifferentiableAt ℂ f z)
    (hf' : ∀ z : ℂ, ‖z - c‖ ≤ ρ → DifferentiableAt ℂ (deriv f) z)
    (h1 : ‖deriv f c‖ ≤ M) (h2 : ∀ z : ℂ, ‖z - c‖ ≤ ρ → ‖deriv (deriv f) z‖ ≤ C) :
    ∀ w : ℂ, ‖w - c‖ ≤ ρ → ‖f w - f c‖ ≤ M * ρ + C * ρ ^ 2 / 2 := by
  intro w hw
  set A : ℂ := deriv f c with hA
  -- the points `c + t • (w - c)`, `t ∈ [0,1]`, lie in the closed disc
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(c + t • (w - c)) - c‖ ≤ ρ := by
    intro t ht
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    calc t * ‖w - c‖ ≤ 1 * ‖w - c‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = ‖w - c‖ := one_mul _
      _ ≤ ρ := hw
  -- the Taylor remainder along the segment, and its derivative
  set g : ℝ → ℂ := fun t => f (c + t • (w - c)) - f c - A * (t • (w - c)) with hg
  set g' : ℝ → ℂ := fun t => (deriv f (c + t • (w - c)) - A) * (w - c) with hg'
  have hge : ∀ t : ℝ, g t = f (c + t • (w - c)) - f c - A * (t • (w - c)) := fun t => by rw [hg]
  have hg'e : ∀ t : ℝ, g' t = (deriv f (c + t • (w - c)) - A) * (w - c) :=
    fun t => by rw [hg']
  -- `g` has derivative `g'` on `[0,1]`
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hdiff : DifferentiableAt ℂ f (c + t • (w - c)) := hf _ (hmem t ht)
    have h1' := hasDerivAt_comp_curve (x := c) (y := w - c) f hdiff
    have h2' : HasDerivAt (fun _ : ℝ => f c) 0 t := hasDerivAt_const t (f c)
    have hbase : HasDerivAt (fun s : ℝ => s • (w - c)) (w - c) t := by
      simpa using (hasDerivAt_id t).smul_const (w - c)
    have h3' : HasDerivAt (fun s : ℝ => A * (s • (w - c))) (A * (w - c)) t := by
      have hh := (hasDerivAt_const t A).mul hbase
      have hfun : ((fun _ : ℝ => A) * fun s : ℝ => s • (w - c))
          = fun s : ℝ => A * (s • (w - c)) := by funext s; simp
      rw [hfun] at hh
      exact hh.congr_deriv (by simp)
    have hcomb : HasDerivAt (fun s : ℝ => f (c + s • (w - c)) - f c - A * (s • (w - c)))
        ((deriv f (c + t • (w - c)) * (w - c)) - 0 - A * (w - c)) t := (h1'.sub h2').sub h3'
    have hgeq : g = fun s : ℝ => f (c + s • (w - c)) - f c - A * (s • (w - c)) := funext hge
    rw [← hgeq] at hcomb
    refine hcomb.congr_deriv ?_
    rw [hg'e t]; ring
  -- `g'` is continuous on `[0,1]`
  have hcont : ContinuousOn g' (Set.uIcc (0 : ℝ) 1) := by
    have hcd : ContinuousOn (deriv f) (Metric.closedBall c ρ) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      exact (hf' z hz).continuousAt.continuousWithinAt
    have hcc : ContinuousOn (fun t : ℝ => c + t • (w - c)) (Set.uIcc (0 : ℝ) 1) := by fun_prop
    have hm : Set.MapsTo (fun t : ℝ => c + t • (w - c)) (Set.uIcc (0 : ℝ) 1)
        (Metric.closedBall c ρ) := by
      intro t ht
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hmem t (by rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht)
    have h1c : ContinuousOn (fun t : ℝ => deriv f (c + t • (w - c))) (Set.uIcc (0 : ℝ) 1) :=
      hcd.comp hcc hm
    have h2c : ContinuousOn (fun t : ℝ => (deriv f (c + t • (w - c)) - A) * (w - c))
        (Set.uIcc (0 : ℝ) 1) := (h1c.sub continuousOn_const).mul continuousOn_const
    rw [show g' = fun t : ℝ => (deriv f (c + t • (w - c)) - A) * (w - c) from funext hg'e]
    exact h2c
  have h0 : g 0 = 0 := by rw [hge 0]; simp
  -- the pointwise bound `‖g' t‖ ≤ (C ‖w-c‖²) * t`
  have hb : ∀ t ∈ Set.uIcc (0 : ℝ) 1, ‖g' t‖ ≤ (C * ‖w - c‖ ^ 2) * t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 ≤ t := ht.1
    have hbd := norm_deriv_sub_le_of_ball hρ hf' h2 (hmem t ht)
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0, ← hA] at hbd
    rw [hg'e t, norm_mul]
    calc ‖deriv f (c + t • (w - c)) - A‖ * ‖w - c‖
        ≤ (C * (t * ‖w - c‖)) * ‖w - c‖ := mul_le_mul_of_nonneg_right hbd (norm_nonneg _)
      _ = (C * ‖w - c‖ ^ 2) * t := by ring
  have hstep := norm_one_le_of_hasDerivAt_norm_le hd hcont h0 hb
  have hg1 : g 1 = f w - f c - A * (w - c) := by rw [hge 1]; simp
  -- `‖f w - f c‖ ≤ ‖g 1‖ + ‖A‖ ‖w-c‖`
  have hbnd : ‖f w - f c‖ ≤ ‖A‖ * ‖w - c‖ + (C * ‖w - c‖ ^ 2) / 2 := by
    have key : (f w - f c) = g 1 + A * (w - c) := by rw [hg1]; ring
    calc ‖f w - f c‖ = ‖g 1 + A * (w - c)‖ := by rw [key]
      _ ≤ ‖g 1‖ + ‖A * (w - c)‖ := norm_add_le _ _
      _ = ‖g 1‖ + ‖A‖ * ‖w - c‖ := by rw [norm_mul]
      _ ≤ (C * ‖w - c‖ ^ 2) / 2 + ‖A‖ * ‖w - c‖ := by linarith
      _ = ‖A‖ * ‖w - c‖ + (C * ‖w - c‖ ^ 2) / 2 := by ring
  have hA1 : ‖A‖ ≤ M := by rw [hA]; exact h1
  refine hbnd.trans ?_
  have hr0 : (0 : ℝ) ≤ ‖w - c‖ := norm_nonneg _
  have e1 : ‖A‖ * ‖w - c‖ ≤ M * ρ := mul_le_mul hA1 hw hr0 hM
  have e2 : (C * ‖w - c‖ ^ 2) / 2 ≤ C * ρ ^ 2 / 2 := by
    have hsq : ‖w - c‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr0 hw 2
    linarith [mul_le_mul_of_nonneg_left hsq hC]
  linarith

end Work.ANum3
