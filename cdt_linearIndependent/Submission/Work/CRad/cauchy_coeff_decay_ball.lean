import Mathlib

namespace Work.CRad

/-- Cauchy's estimate in the form needed for `CRad`: the "diagonal" coefficients
`c n = p n (fun _ => 1)` of a power series `p` representing an analytic function `g` around `0`
decay geometrically with any rate `1 / r` where `r` is smaller than the radius on which `g` is
holomorphic. -/
theorem cauchy_coeff_decay_ball {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {c : ℕ → ℂ} {r r' : ℝ} (hr0 : 0 < r) (hrr' : r < r')
    (hd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r'))
    (hp : HasFPowerSeriesAt g p 0)
    (hc : ∀ n : ℕ, p n (fun _ : Fin n => (1 : ℂ)) = c n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖c n‖ ≤ C * (1 / r) ^ n := by
  obtain ⟨R, hR⟩ := hp
  -- A radius strictly between `r` and `r'`, on which `g` is analytic and the circle is compact.
  set rho : ℝ := (r + r') / 2 with hrho
  have hr_lt_rho : r < rho := by rw [hrho]; linarith
  have hrho_lt_r' : rho < r' := by rw [hrho]; linarith
  have hrho0 : 0 < rho := lt_trans hr0 hr_lt_rho
  -- `g` is holomorphic on the open ball of radius `rho` and continuous on its closure.
  have hdball : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rho) :=
    hd.mono (Metric.ball_subset_ball (le_of_lt hrho_lt_r'))
  have hcont : ContinuousOn g (Metric.closedBall (0 : ℂ) rho) := by
    refine (hd.mono ?_).continuousOn
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hz hrho_lt_r'
  have hdcc : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) rho) :=
    DiffContOnCl.mk_ball hdball hcont
  -- A uniform bound for `‖g‖` on the boundary circle.
  obtain ⟨C0, hC0⟩ : ∃ C0, ∀ z ∈ Metric.sphere (0 : ℂ) rho, ‖g z‖ ≤ C0 := by
    exact (isCompact_sphere (0 : ℂ) rho).exists_bound_of_continuousOn
      (hcont.mono Metric.sphere_subset_closedBall)
  set C : ℝ := max C0 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; exact lt_max_of_lt_right zero_lt_one
  refine ⟨C, hCpos, fun n => ?_⟩
  have hsphere : ∀ z ∈ Metric.sphere (0:ℂ) rho, ‖g z‖ ≤ C :=
    fun z hz => le_trans (hC0 z hz) (le_max_left _ _)
  -- Cauchy's estimate for the `n`-th derivative at the centre.
  have hcauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := ℂ) n hrho0 hdcc hsphere
  -- The `n`-th diagonal coefficient is `iteratedDeriv n g 0 / n!`.
  have hcoeff : iteratedDeriv n g (0:ℂ) = (n.factorial : ℂ) • c n := by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    rw [hR.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin n => (1:ℂ))]
    simp [Finset.sum_const, Fintype.card_perm, hc n]
  rw [hcoeff, norm_smul, norm_natCast] at hcauchy
  have hfact : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hstep1 : (n.factorial : ℝ) * ‖c n‖ ≤ (n.factorial : ℝ) * (C / rho ^ n) := by
    rwa [mul_div_assoc] at hcauchy
  have hle : ‖c n‖ ≤ C / rho ^ n := (mul_le_mul_iff_right₀ hfact).1 hstep1
  calc ‖c n‖ ≤ C / rho ^ n := hle
    _ = C * (1 / rho) ^ n := by rw [div_eq_mul_inv, ← inv_pow, one_div]
    _ ≤ C * (1 / r) ^ n := by
        apply mul_le_mul_of_nonneg_left _ hCpos.le
        apply pow_le_pow_left₀ (by positivity)
        exact one_div_le_one_div_of_le hr0 (le_of_lt hr_lt_rho)

end Work.CRad
