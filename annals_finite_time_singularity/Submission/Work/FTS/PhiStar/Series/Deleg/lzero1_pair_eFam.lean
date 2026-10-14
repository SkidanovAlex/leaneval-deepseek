import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Series.Deleg.psiCmodeAux.Bnds
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.Gegenbauer (eFam lam)
open Work.FTS.EllipticEst (Lzero1)

namespace Work.FTS.PhiStar.Series.Deleg

set_option maxHeartbeats 1600000

/-!
# The `Lzero1` pairing identity for the Gegenbauer eigenfunctions

`Lzero1 v = ψ` on `(0, π/2)`, with `v` continuous on the closed interval and vanishing at both
endpoints, implies `∫ ψ e_n cos = λ_n ∫ v e_n cos` for every eigenfunction `e_n = eFam n`
(`Lzero1 e_n = lam n · e_n`).

**Route.**  The Wronskian `Ξ θ = cos θ (v' e - v e')` has derivative `cos θ ((λ_n v - ψ) e)`
on the open interval (`hasDerivAt_lzero_wronskian`), and tends to `0` at both endpoints.  The
endpoint limits come from the *first-order form* of the equation: with `W θ = tan θ · v θ - v' θ`
one has `W' = 6v + ψ`, bounded on `(0, π/2)` because `v`, `ψ` are continuous on the compact
`Icc 0 (π/2)`; hence `v' = tan θ · v - W` with `W` bounded, which bounds `Ξ` near the endpoints.
The fundamental theorem of calculus with limits then gives the identity.
-/

private lemma cos_ne_zero_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)

/-! ## The first-order form of the equation -/

/-- `W θ = tan θ · v θ - v' θ`; the ODE says `W' = 6v + ψ`. -/
private abbrev W (v : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.tan θ * v θ - deriv v θ

/-- The ODE in expanded form: `v'' = (1/cos²θ) v + tan θ v' - 6v - ψ`. -/
private lemma deriv_deriv_eq (v ψ : ℝ → ℝ)
    (hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Lzero1 v θ = ψ θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (deriv v) θ
      = (1 / Real.cos θ ^ 2) * v θ + Real.tan θ * deriv v θ - 6 * v θ - ψ θ := by
  have hcos : Real.cos θ ≠ 0 := cos_ne_zero_Ioo hθ
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hdv : HasDerivAt v (deriv v θ) θ :=
    ((hv2.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  have h1 : deriv (fun t : ℝ => Real.tan t * v t) θ
      = (1 / Real.cos θ ^ 2) * v θ + Real.tan θ * deriv v θ := (htan.mul hdv).deriv
  have h := heq θ hθ
  simp only [Work.FTS.EllipticEst.Lzero1] at h
  rw [show deriv (fun t : ℝ => deriv v t) θ = deriv (deriv v) θ from rfl, h1] at h
  linarith

/-- `W` has the bounded derivative `6v + ψ` on the open interval. -/
private lemma hasDerivAt_W (v ψ : ℝ → ℝ)
    (hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Lzero1 v θ = ψ θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (W v) (6 * v θ + ψ θ) θ := by
  have hcos : Real.cos θ ≠ 0 := cos_ne_zero_Ioo hθ
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hdv : HasDerivAt v (deriv v θ) θ :=
    ((hv2.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hd1 : ContDiffOn ℝ 1 (deriv v) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hv2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2v : HasDerivAt (deriv v) (deriv (deriv v) θ) θ :=
    ((hd1.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  have h1 : HasDerivAt (fun t : ℝ => Real.tan t * v t)
      ((1 / Real.cos θ ^ 2) * v θ + Real.tan θ * deriv v θ) θ := htan.mul hdv
  have hode := deriv_deriv_eq v ψ hv2 heq hθ
  have hd : (1 / Real.cos θ ^ 2) * v θ + Real.tan θ * deriv v θ - deriv (deriv v) θ
      = 6 * v θ + ψ θ := by
    rw [hode]; ring
  exact (h1.sub hd2v).congr_deriv hd

/-! ## Boundedness of `W` -/

/-- Fundamental theorem of calculus for `W` on a subinterval of `(0, π/2)`. -/
private lemma W_sub_eq (v ψ : ℝ → ℝ)
    (hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hvcont : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hψcont : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Lzero1 v θ = ψ θ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    W v b - W v a = ∫ t in a..b, (6 * v t + ψ t) := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_).symm
  · -- continuity of `W v` on `[a, b]`
    have hsub : Set.Icc a b ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      intro x hx
      exact ⟨by linarith [hx.1, ha, Real.pi_pos], lt_of_le_of_lt hx.2 hb⟩
    have htan : ContinuousOn Real.tan (Set.Icc a b) := Real.continuousOn_tan_Ioo.mono hsub
    have hv : ContinuousOn v (Set.Icc a b) := hvcont.mono (by
      intro x hx
      exact ⟨le_trans ha.le hx.1, le_of_lt (lt_of_le_of_lt hx.2 hb)⟩)
    have hdv2 : ContDiffOn ℝ 0 (deriv v) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hv2.deriv_of_isOpen isOpen_Ioo
        (by norm_num : ((0 : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((2 : ℕ∞) : WithTop ℕ∞))
    have hdv : ContinuousOn (deriv v) (Set.Icc a b) := hdv2.continuousOn.mono (by
      intro x hx
      exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩)
    exact (htan.mul hv).sub hdv
  · intro x hx
    exact hasDerivAt_W v ψ hv2 heq ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩
  · -- integrability of `6v + ψ`
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    have hsub : Set.Icc a b ⊆ Set.Icc 0 (Real.pi / 2) := by
      intro x hx
      exact ⟨le_trans ha.le hx.1, le_of_lt (lt_of_le_of_lt hx.2 hb)⟩
    exact ((continuousOn_const.mul hvcont).add hψcont).mono hsub

/-- `W` is Lipschitz on subintervals of `(0, π/2)`. -/
private lemma W_abs_sub_le (v ψ : ℝ → ℝ)
    (hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hvcont : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hψcont : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Lzero1 v θ = ψ θ)
    {M a b : ℝ} (hM : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |6 * v θ + ψ θ| ≤ M)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    |W v b - W v a| ≤ M * (b - a) := by
  rw [W_sub_eq v ψ hv2 hvcont hψcont heq ha hab hb]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => 6 * v t + ψ t) (a := a) (b := b) (C := M) (fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      exact hM x ⟨by linarith [hx.1], by linarith [hx.2, hb]⟩)
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h

/-- `|W θ|` is controlled by the value at `π/4`. -/
private lemma W_abs_le (v : ℝ → ℝ) (θ : ℝ) :
    |W v θ| ≤ |W v (Real.pi / 4)| + |W v θ - W v (Real.pi / 4)| := by
  have h4 := abs_add_le (W v θ - W v (Real.pi / 4)) (W v (Real.pi / 4))
  have h5 : W v θ - W v (Real.pi / 4) + W v (Real.pi / 4) = W v θ := by ring
  rw [h5] at h4
  calc |W v θ| ≤ |W v θ - W v (Real.pi / 4)| + |W v (Real.pi / 4)| := h4
    _ = |W v (Real.pi / 4)| + |W v θ - W v (Real.pi / 4)| := by rw [add_comm]

/-- `W` is bounded on `(0, π/2)`. -/
private lemma W_bdd (v ψ : ℝ → ℝ)
    (hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hvcont : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hψcont : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Lzero1 v θ = ψ θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |W v θ| ≤ K := by
  have hc6 : ContinuousOn (fun θ => 6 * v θ + ψ θ) (Set.Icc 0 (Real.pi / 2)) :=
    (continuousOn_const.mul hvcont).add hψcont
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc6
  have hM' : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |6 * v θ + ψ θ| ≤ M := fun θ hθ => by
    simpa [Real.norm_eq_abs] using hM θ hθ
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM' 0 ⟨le_refl 0, by linarith [Real.pi_pos]⟩)
  refine ⟨|W v (Real.pi / 4)| + M * (Real.pi / 2), ?_, fun θ hθ => ?_⟩
  · have h1 := abs_nonneg (W v (Real.pi / 4))
    have h2 : 0 ≤ M * (Real.pi / 2) := mul_nonneg hMnn (by linarith [Real.pi_pos])
    linarith
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have h4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  rcases lt_or_ge θ (Real.pi / 4) with hlt | hle
  · have h := W_abs_sub_le v ψ hv2 hvcont hψcont heq hM' hθ.1 hlt.le h4lt
    have h6 : |W v θ - W v (Real.pi / 4)| = |W v (Real.pi / 4) - W v θ| := by
      rw [← abs_neg (W v (Real.pi / 4) - W v θ), neg_sub]
    have h2 : M * (Real.pi / 4 - θ) ≤ M * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left (by linarith [hθ.1]) hMnn
    calc |W v θ| ≤ |W v (Real.pi / 4)| + |W v θ - W v (Real.pi / 4)| := W_abs_le v θ
      _ = |W v (Real.pi / 4)| + |W v (Real.pi / 4) - W v θ| := by rw [h6]
      _ ≤ |W v (Real.pi / 4)| + M * (Real.pi / 2) := by linarith
  · have h := W_abs_sub_le v ψ hv2 hvcont hψcont heq hM' hpi4 hle hθ.2
    have h2 : M * (θ - Real.pi / 4) ≤ M * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left (by linarith [hθ.2]) hMnn
    calc |W v θ| ≤ |W v (Real.pi / 4)| + |W v θ - W v (Real.pi / 4)| := W_abs_le v θ
      _ ≤ |W v (Real.pi / 4)| + M * (Real.pi / 2) := by linarith

/-! ## `v → 0` at the endpoints -/

/-- `v → v (π/2) = 0` from the left. -/
private lemma tendsto_v_left {v : ℝ → ℝ} (hvcont : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hv1 : v (Real.pi / 2) = 0) :
    Tendsto v (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hmem : Real.pi / 2 ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], le_refl _⟩
  have h1 : ∀ᶠ θ in 𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2), dist (v θ) 0 < ε := by
    have h2 := (Metric.tendsto_nhds.mp (hvcont.continuousWithinAt hmem)) ε hε
    simpa only [hv1] using h2
  rw [Filter.eventually_iff, mem_nhdsWithin_iff_exists_mem_nhds_inter] at h1
  obtain ⟨u, hu, hsub⟩ := h1
  rw [Metric.mem_nhds_iff] at hu
  obtain ⟨r, hr, hru⟩ := hu
  refine Filter.mem_of_superset
    (Ioo_mem_nhdsLT (show max (Real.pi / 2 - r / 2) 0 < Real.pi / 2 from
      max_lt (by linarith) (by linarith [Real.pi_pos]))) ?_
  intro θ hθ
  refine hsub ⟨hru ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hθ.2])]
    linarith [le_max_left (Real.pi / 2 - r / 2) (0 : ℝ), hθ.1, hr]
  · exact ⟨by linarith [le_max_right (Real.pi / 2 - r / 2) (0 : ℝ), hθ.1], le_of_lt hθ.2⟩

/-- `v → v 0 = 0` from the right. -/
private lemma tendsto_v_right {v : ℝ → ℝ} (hvcont : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hv0 : v 0 = 0) :
    Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hmem : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_refl _, by linarith [Real.pi_pos]⟩
  have h1 : ∀ᶠ θ in 𝓝[Set.Icc 0 (Real.pi / 2)] (0 : ℝ), dist (v θ) 0 < ε := by
    have h2 := (Metric.tendsto_nhds.mp (hvcont.continuousWithinAt hmem)) ε hε
    simpa only [hv0] using h2
  rw [Filter.eventually_iff, mem_nhdsWithin_iff_exists_mem_nhds_inter] at h1
  obtain ⟨u, hu, hsub⟩ := h1
  rw [Metric.mem_nhds_iff] at hu
  obtain ⟨r, hr, hru⟩ := hu
  refine Filter.mem_of_superset
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min (r / 2) (Real.pi / 2) from
      lt_min (by linarith) (by linarith [Real.pi_pos]))) ?_
  intro θ hθ
  refine hsub ⟨hru ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ.1]
    linarith [min_le_left (r / 2) (Real.pi / 2), hθ.2, hr]
  · exact ⟨le_of_lt hθ.1, le_of_lt (lt_of_lt_of_le hθ.2 (min_le_right (r / 2) (Real.pi / 2)))⟩

/-! ## The Wronskian and its endpoint limits -/

/-- `Ξ θ = cos θ · (v' e - v e')(θ)`, the antiderivative of the pairing integrand. -/
private abbrev Xi (v : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun θ => Real.cos θ * (deriv v θ * eFam n θ - v θ * deriv (eFam n) θ)

/-- The pointwise rewriting of `Ξ` through `W`. -/
private lemma Xi_pointwise (v : ℝ → ℝ) (n : ℕ) {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Xi v n θ = Real.sin θ * v θ * eFam n θ
      - Real.cos θ * W v θ * eFam n θ
      - Real.cos θ * v θ * deriv (eFam n) θ := by
  simp only [Xi, W]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- The pointwise bound on `Ξ` used in the squeeze at both endpoints. -/
private lemma Xi_norm_bound (v : ℝ → ℝ) (n : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {K Qd : ℝ}
    (hK : |W v θ| ≤ K) (hQd : |deriv (eFam n) θ| ≤ Qd) :
    ‖Xi v n θ‖ ≤ |Real.sin θ * v θ * eFam n θ|
      + K * |Real.cos θ * eFam n θ| + |Real.cos θ * v θ| * Qd := by
  rw [Real.norm_eq_abs, Xi_pointwise v n (cos_ne_zero_Ioo hθ)]
  have h1 : |Real.sin θ * v θ * eFam n θ
      - Real.cos θ * W v θ * eFam n θ - Real.cos θ * v θ * deriv (eFam n) θ|
      ≤ |Real.sin θ * v θ * eFam n θ| + |Real.cos θ * W v θ * eFam n θ|
        + |Real.cos θ * v θ * deriv (eFam n) θ| := by
    have h2 := abs_sub (Real.sin θ * v θ * eFam n θ - Real.cos θ * W v θ * eFam n θ)
      (Real.cos θ * v θ * deriv (eFam n) θ)
    have h3 := abs_sub (Real.sin θ * v θ * eFam n θ) (Real.cos θ * W v θ * eFam n θ)
    linarith
  have h4 : |Real.cos θ * W v θ * eFam n θ| ≤ K * |Real.cos θ * eFam n θ| := by
    have h6 : |Real.cos θ * W v θ * eFam n θ| = |W v θ| * |Real.cos θ * eFam n θ| := by
      rw [show Real.cos θ * W v θ * eFam n θ = W v θ * (Real.cos θ * eFam n θ) from by ring,
        abs_mul]
    rw [h6]
    exact mul_le_mul_of_nonneg_right hK (abs_nonneg _)
  have h5 : |Real.cos θ * v θ * deriv (eFam n) θ| ≤ |Real.cos θ * v θ| * Qd := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hQd (abs_nonneg _)
  linarith

/-- `Ξ → 0` at `0⁺`. -/
private lemma Xi_tendsto_left (v ψ : ℝ → ℝ) (n : ℕ)
    (hvsm : ContDiffOn ℝ Work.Stability.smoothOrder v (Set.Ioo 0 (Real.pi / 2)))
    (hvcont : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hv0 : v 0 = 0)
    (hψcont : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Lzero1 v θ = ψ θ) :
    Tendsto (Xi v n) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hvsm.of_le (by norm_num)
  obtain ⟨K, _, hK⟩ := W_bdd v ψ hv2 hvcont hψcont heq
  obtain ⟨Qd, _, hQd⟩ := eFam_deriv_abs_bound n
  have hvt : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_v_right hvcont hv0
  have he : Tendsto (eFam n) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h2 : Tendsto (eFam n) (𝓝[>] (0 : ℝ)) (𝓝 (eFam n 0)) :=
      ((contDiff_eFam n).continuous.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [eFam_zero n] using h2
  have hsin : Tendsto Real.sin (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((Real.continuous_sin.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
  have hcos : Tendsto (fun θ : ℝ => Real.cos θ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using ((Real.continuous_cos.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
  have ha1 : Tendsto (fun θ => Real.sin θ * v θ * eFam n θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hsin.mul hvt).mul he
  have ha2 : Tendsto (fun θ => |Real.cos θ * eFam n θ|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hcos.mul he).abs
  have ha3 : Tendsto (fun θ => |Real.cos θ * v θ|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hcos.mul hvt).abs
  have ha : Tendsto (fun θ => |Real.sin θ * v θ * eFam n θ|
      + K * |Real.cos θ * eFam n θ| + |Real.cos θ * v θ| * Qd)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (ha1.abs.add (ha2.const_mul K)).add (ha3.mul_const Qd)
    simpa using h
  refine squeeze_zero_norm' (a := fun θ => |Real.sin θ * v θ * eFam n θ|
      + K * |Real.cos θ * eFam n θ| + |Real.cos θ * v θ| * Qd) ?_ ha
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
    with θ hθ
  exact Xi_norm_bound v n hθ (hK θ hθ) (hQd θ ⟨hθ.1.le, hθ.2.le⟩)

/-- `Ξ → 0` at `(π/2)⁻`. -/
private lemma Xi_tendsto_right (v ψ : ℝ → ℝ) (n : ℕ)
    (hvsm : ContDiffOn ℝ Work.Stability.smoothOrder v (Set.Ioo 0 (Real.pi / 2)))
    (hvcont : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hv1 : v (Real.pi / 2) = 0)
    (hψcont : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Lzero1 v θ = ψ θ) :
    Tendsto (Xi v n) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hvsm.of_le (by norm_num)
  obtain ⟨K, _, hK⟩ := W_bdd v ψ hv2 hvcont hψcont heq
  obtain ⟨Qd, _, hQd⟩ := eFam_deriv_abs_bound n
  have hvt : Tendsto v (𝓝[<] (Real.pi / 2)) (𝓝 0) := tendsto_v_left hvcont hv1
  have he : Tendsto (eFam n) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have h2 : Tendsto (eFam n) (𝓝[<] (Real.pi / 2)) (𝓝 (eFam n (Real.pi / 2))) :=
      ((contDiff_eFam n).continuous.continuousAt (x := Real.pi / 2)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))
    simpa [eFam_pi_div_two n] using h2
  have hsin : Tendsto Real.sin (𝓝[<] (Real.pi / 2)) (𝓝 1) := by
    simpa using ((Real.continuous_sin.continuousAt (x := Real.pi / 2)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2))))
  have hcos : Tendsto (fun θ : ℝ => Real.cos θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa using ((Real.continuous_cos.continuousAt (x := Real.pi / 2)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2))))
  have ha1 : Tendsto (fun θ => Real.sin θ * v θ * eFam n θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa using (hsin.mul hvt).mul he
  have ha2 : Tendsto (fun θ => |Real.cos θ * eFam n θ|) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa using (hcos.mul he).abs
  have ha3 : Tendsto (fun θ => |Real.cos θ * v θ|) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa using (hcos.mul hvt).abs
  have ha : Tendsto (fun θ => |Real.sin θ * v θ * eFam n θ|
      + K * |Real.cos θ * eFam n θ| + |Real.cos θ * v θ| * Qd)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have h := (ha1.abs.add (ha2.const_mul K)).add (ha3.mul_const Qd)
    simpa using h
  refine squeeze_zero_norm' (a := fun θ => |Real.sin θ * v θ * eFam n θ|
      + K * |Real.cos θ * eFam n θ| + |Real.cos θ * v θ| * Qd) ?_ ha
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
    with θ hθ
  exact Xi_norm_bound v n hθ (hK θ hθ) (hQd θ ⟨hθ.1.le, hθ.2.le⟩)

/-! ## The pairing identity -/

theorem lzero1_pair_eFam (ψ v : ℝ → ℝ) (n : ℕ)
    (hvsm : ContDiffOn ℝ Work.Stability.smoothOrder v (Set.Ioo 0 (Real.pi / 2)))
    (hvcont : ContinuousOn v (Set.Icc 0 (Real.pi / 2)))
    (hv0 : v 0 = 0) (hv1 : v (Real.pi / 2) = 0)
    (hψcont : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 v θ = ψ θ) :
    (∫ θ in Work.Spaces.Iθ,
        ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam n
        * ∫ θ in Work.Spaces.Iθ,
            v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hv2 : ContDiffOn ℝ 2 v (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hvsm.of_le (by norm_num)
  -- derivative conditions for `v`
  have hvder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt v (deriv v θ) θ ∧ HasDerivAt (deriv v) (deriv (deriv v) θ) θ := by
    intro θ hθ
    have hop : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have h1 : ContDiffOn ℝ 1 v (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hv2.of_le (by norm_num)
    have h3 : ContDiffOn ℝ 1 (deriv v) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hv2.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact ⟨(h1.contDiffAt hop).differentiableAt (by norm_num) |>.hasDerivAt,
      (h3.contDiffAt hop).differentiableAt (by norm_num) |>.hasDerivAt⟩
  -- derivative conditions for `eFam n`
  have heder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (eFam n) (deriv (eFam n) θ) θ
        ∧ HasDerivAt (deriv (eFam n)) (deriv (deriv (eFam n)) θ) θ := by
    intro θ _hθ
    have h1 : ContDiffOn ℝ 1 (eFam n) Set.univ :=
      (contDiff_eFam n).contDiffOn.of_le (by norm_num)
    have h3 : ContDiffOn ℝ 1 (deriv (eFam n)) Set.univ :=
      (contDiff_eFam n).contDiffOn.deriv_of_isOpen isOpen_univ
        (by norm_num : ((1 : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((3 : ℕ∞) : WithTop ℕ∞))
    exact ⟨(h1.contDiffAt (Filter.univ_mem)).differentiableAt (by norm_num) |>.hasDerivAt,
      (h3.contDiffAt (Filter.univ_mem)).differentiableAt (by norm_num) |>.hasDerivAt⟩
  -- the derivative of the Wronskian
  have hXideriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (Xi v n) (Real.cos θ * ((lam n * v θ - ψ θ) * eFam n θ)) θ := by
    intro θ hθ
    have h := hasDerivAt_lzero_wronskian (f := v) (g := eFam n) (cos_ne_zero_Ioo hθ)
      (hvder θ hθ).1 (hvder θ hθ).2 (heder θ hθ).1 (heder θ hθ).2
    have hv : v θ * Lzero1 (eFam n) θ - Lzero1 v θ * eFam n θ
        = (lam n * v θ - ψ θ) * eFam n θ := by
      rw [eFam_Lzero1 n hθ, heq θ hθ]
      ring
    rw [hv] at h
    simpa only [Xi] using h
  -- integrability of the derivative expression
  have hint : IntervalIntegrable
      (fun θ => Real.cos θ * ((lam n * v θ - ψ θ) * eFam n θ)) volume 0 (Real.pi / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hpi2.le]
    have h1 : ContinuousOn (fun θ => lam n * v θ - ψ θ) (Set.Icc 0 (Real.pi / 2)) :=
      (continuousOn_const.mul hvcont).sub hψcont
    exact Real.continuous_cos.continuousOn.mul (h1.mul (contDiff_eFam n).continuous.continuousOn)
  have hleft := Xi_tendsto_left v ψ n hvsm hvcont hv0 hψcont heq
  have hright := Xi_tendsto_right v ψ n hvsm hvcont hv1 hψcont heq
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi2 hXideriv hint
    hleft hright
  rw [sub_self] at hFTC
  -- rewrite as the integral of `-((ψ - lam v) e cos)`
  have hneg : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      (ψ θ - lam n * v θ) * eFam n θ * Real.cos θ) = 0 := by
    have hfun : (fun θ => (ψ θ - lam n * v θ) * eFam n θ * Real.cos θ)
        = fun θ => -(Real.cos θ * ((lam n * v θ - ψ θ) * eFam n θ)) := by
      funext θ; ring
    rw [hfun, intervalIntegral.integral_neg, hFTC, neg_zero]
  have hI : (∫ θ in Work.Spaces.Iθ,
      (ψ θ - lam n * v θ) * eFam n θ * Real.cos θ) = 0 := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hpi2.le]
    exact hneg
  have hsplit : (∫ θ in Work.Spaces.Iθ,
      (ψ θ - lam n * v θ) * eFam n θ * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, ψ θ * eFam n θ * Real.cos θ)
        - lam n * (∫ θ in Work.Spaces.Iθ, v θ * eFam n θ * Real.cos θ) := by
    have hfun : (fun θ => (ψ θ - lam n * v θ) * eFam n θ * Real.cos θ)
        = fun θ => ψ θ * eFam n θ * Real.cos θ
          - lam n * (v θ * eFam n θ * Real.cos θ) := by
      funext θ; ring
    rw [hfun, MeasureTheory.integral_sub, MeasureTheory.integral_const_mul]
    · show MeasureTheory.IntegrableOn (fun θ => ψ θ * eFam n θ * Real.cos θ)
        Work.Spaces.Iθ MeasureTheory.volume
      exact ((hψcont.mul (contDiff_eFam n).continuous.continuousOn).mul
        Real.continuous_cos.continuousOn).integrableOn_Icc
    · show MeasureTheory.IntegrableOn (fun θ => lam n * (v θ * eFam n θ * Real.cos θ))
        Work.Spaces.Iθ MeasureTheory.volume
      exact (((hvcont.mul (contDiff_eFam n).continuous.continuousOn).mul
        Real.continuous_cos.continuousOn).const_mul (lam n)).integrableOn_Icc
  show (∫ θ in Work.Spaces.Iθ, ψ θ * eFam n θ * Real.cos θ)
    = lam n * (∫ θ in Work.Spaces.Iθ, v θ * eFam n θ * Real.cos θ)
  linarith [hI, hsplit]

end Work.FTS.PhiStar.Series.Deleg
