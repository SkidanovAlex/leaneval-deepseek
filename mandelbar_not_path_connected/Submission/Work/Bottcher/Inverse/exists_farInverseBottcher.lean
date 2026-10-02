import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.Bottcher.Inverse.exists_farBottcher_inverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The far inverse of the Böttcher coordinate of the tricorn

`bottcher c z = z * exp (bottcherSeries c z)` is the product formula for the Böttcher
coordinate of the holomorphic quartic `p_c = T_c ∘ T_c`, `T_c z = z̄² + c`.  On the far
region `‖z‖ ≥ escapeRadius c` it is the genuine Böttcher coordinate (analytic, tangent to the
identity at infinity), and this file constructs a **right inverse** `ψ` of it there, i.e. a
section of `bottcher c` over a neighbourhood of infinity, solving the functional equation
`p_c (ψ w) = ψ (w^4)`.

The construction is the classical fixed point of `z ↦ w * exp (-S z)`, `S = bottcherSeries c`,
on the closed ball of radius `‖w‖/8` around `w`: the map is a contraction there because
`S = O(1/‖z‖²)` with Lipschitz constant `O(1/‖u‖³)` (`norm_bottcherSeries_le_far`,
`norm_bottcherSeries_sub_le`), so Banach's theorem (`exists_farBottcher_inverse`) produces a
unique solution of `bottcher c z = w` in the ball; transfer of the functional equation uses the
same uniqueness at `w^4`.
-/

open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Inverse

noncomputable section

/-- `farInvC c = ‖c‖² + 3‖c‖ + 1`, the constant controlling the Böttcher series on the far
region (see `norm_bottcherSeries_le_far`). -/
abbrev farInvC (c : ℂ) : ℝ := ‖c‖ ^ 2 + 3 * ‖c‖ + 1

/-- `farInvR c = 1024 (1 + ‖c‖) + 1024`, the far radius of the inverse Böttcher branch
(see `exists_farBottcher_inverse`). -/
abbrev farInvR (c : ℂ) : ℝ := 1024 * (1 + ‖c‖) + 1024

theorem farInvC_pos (c : ℂ) : 0 < farInvC c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  nlinarith [sq_nonneg ‖c‖]

theorem two_le_farInvR (c : ℂ) : 2 ≤ farInvR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  nlinarith

theorem one_le_farInvR (c : ℂ) : 1 ≤ farInvR c := le_trans (by norm_num) (two_le_farInvR c)

/-- **Monotonicity of the `p_c`-orbit in the far region.**  If `2 + ‖c‖ ≤ ‖z‖` then every
iterate `(p_c)^[n] z` still has norm at least `2 + ‖c‖` and at least `‖z‖`. -/
theorem norm_le_iterate_pMap (c : ℂ) {z : ℂ} (hz : 2 + ‖c‖ ≤ ‖z‖) (n : ℕ) :
    2 + ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ ∧ ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := by
  induction n with
  | zero => exact ⟨hz, le_rfl⟩
  | succ k ih =>
      obtain ⟨h1, -, h3⟩ :=
        Work.Bottcher.Core.pMap_norm_step c ((Work.Bottcher.pMap c)^[k] z) ih.1
      rw [Function.iterate_succ_apply']
      exact ⟨h3, le_trans ih.2 h1⟩

/-- **Difference formula for the quartic.**  `p_c x - p_c y = (x-y)(x+y)(x²+y²+2c̄)`. -/
theorem pMap_sub_pMap (c x y : ℂ) :
    Work.Bottcher.pMap c x - Work.Bottcher.pMap c y
      = (x - y) * (x + y) * (x ^ 2 + y ^ 2 + 2 * conj c) := by
  rw [Work.Bottcher.pMap_apply, Work.Bottcher.pMap_apply]
  ring

/-- The inverse Böttcher branch: for `‖w‖ ≥ farInvR c`, `farInvPsi c w` is the point of
`closedBall w (‖w‖/8)` with `bottcher c (farInvPsi c w) = w`; elsewhere it is `0`. -/
noncomputable def farInvPsi (c : ℂ) (w : ℂ) : ℂ :=
  if _ : farInvR c ≤ ‖w‖ then Classical.choose (exists_farBottcher_inverse c w ‹_›) else 0

/-- The defining properties of `farInvPsi c w` for `‖w‖ ≥ farInvR c`. -/
theorem farInvPsi_reg (c w : ℂ) (hw : farInvR c ≤ ‖w‖) :
    farInvPsi c w ∈ Metric.closedBall w (‖w‖ / 8) ∧
      Work.Bottcher.bottcher c (farInvPsi c w) = w ∧
      ‖farInvPsi c w - w‖ ≤ 4 * farInvC c / ‖w‖ := by
  have hspec := Classical.choose_spec (exists_farBottcher_inverse c w hw)
  unfold farInvPsi
  rw [dite_eq_left hw]
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩

/-- **Uniqueness of the inverse branch in the ball.**  Any solution `x` of `bottcher c x = w`
within `closedBall w (‖w‖/8)` equals `farInvPsi c w`. -/
theorem farInvPsi_unique (c w : ℂ) (hw : farInvR c ≤ ‖w‖) {x : ℂ}
    (hx : x ∈ Metric.closedBall w (‖w‖ / 8)) (hb : Work.Bottcher.bottcher c x = w) :
    x = farInvPsi c w := by
  have hspec := Classical.choose_spec (exists_farBottcher_inverse c w hw)
  have hx' : x = Classical.choose (exists_farBottcher_inverse c w hw) := hspec.2.2.2 x hx hb
  unfold farInvPsi
  rw [dite_eq_left hw]
  exact hx'

/-- The elementary estimate `‖p_c z - w^4‖ ≤ ‖w‖^4/8` for the point `z = ψ w` of
`closedBall w (‖w‖/8)`; this is what puts `p_c (ψ w)` in the ball at `w^4` where the inverse
branch is unique. -/
theorem norm_pMap_farInvPsi_sub_pow4_le (c w : ℂ) (hw : farInvR c ≤ ‖w‖) :
    ‖Work.Bottcher.pMap c (farInvPsi c w) - w ^ 4‖ ≤ ‖w ^ 4‖ / 8 := by
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  obtain ⟨hzball, -, hzdist⟩ := farInvPsi_reg c w hw
  have hzclose : ‖farInvPsi c w - w‖ ≤ ‖w‖ / 8 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hzball
    exact hzball
  have hwge : 1024 * (1 + ‖c‖) + 1024 ≤ ‖w‖ := hw
  have hw1024 : (1024 : ℝ) ≤ ‖w‖ := by nlinarith
  have hw1 : (1 : ℝ) ≤ ‖w‖ := by linarith
  have hznorm : ‖farInvPsi c w‖ ≤ 2 * ‖w‖ := by
    have h := norm_add_le (farInvPsi c w - w) w
    have he : (farInvPsi c w - w) + w = farInvPsi c w := by ring
    rw [he] at h
    linarith
  -- the two terms of the difference
  have hterm1 : ‖Work.Bottcher.pMap c (farInvPsi c w) - Work.Bottcher.pMap c w‖
      ≤ (4 * farInvC c / ‖w‖) * (3 * ‖w‖) * (6 * ‖w‖ ^ 2) := by
    rw [pMap_sub_pMap]
    have h1 : ‖farInvPsi c w - w‖ ≤ 4 * farInvC c / ‖w‖ := hzdist
    have h2 : ‖farInvPsi c w + w‖ ≤ 3 * ‖w‖ := by
      have h := norm_add_le (farInvPsi c w) w
      linarith
    have h3 : ‖farInvPsi c w ^ 2 + w ^ 2 + 2 * conj c‖ ≤ 6 * ‖w‖ ^ 2 := by
      have h := norm_add_le (farInvPsi c w ^ 2 + w ^ 2) (2 * conj c)
      have h4 : ‖farInvPsi c w ^ 2 + w ^ 2‖ ≤ (2 * ‖w‖) ^ 2 + ‖w‖ ^ 2 := by
        have h' := norm_add_le (farInvPsi c w ^ 2) (w ^ 2)
        rw [norm_pow, norm_pow] at h'
        have h5 : ‖farInvPsi c w‖ ^ 2 ≤ (2 * ‖w‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hznorm 2
        linarith
      have h6 : ‖2 * conj c‖ = 2 * ‖c‖ := by
        rw [norm_mul, Complex.norm_conj, Complex.norm_ofNat]
      rw [h6] at h
      have h7 : (2 * ‖w‖) ^ 2 + ‖w‖ ^ 2 + 2 * ‖c‖ ≤ 6 * ‖w‖ ^ 2 := by
        have hW2 : 2 * ‖c‖ ≤ ‖w‖ ^ 2 := by nlinarith [hwge, hc]
        nlinarith [hW2, sq_nonneg ‖w‖]
      linarith
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _)
      (by positivity)
  have hterm2 : ‖Work.Bottcher.pMap c w - w ^ 4‖ ≤ (2 * ‖c‖ + ‖c‖ ^ 2 + ‖c‖) * ‖w‖ ^ 2 := by
    have he : Work.Bottcher.pMap c w - w ^ 4
        = 2 * conj c * w ^ 2 + (conj c) ^ 2 + c := by
      rw [Work.Bottcher.pMap_apply]; ring
    rw [he]
    have h := norm_add_le (2 * conj c * w ^ 2 + (conj c) ^ 2) c
    have h2 : ‖2 * conj c * w ^ 2 + (conj c) ^ 2‖ ≤ 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 := by
      have h' := norm_add_le (2 * conj c * w ^ 2) ((conj c) ^ 2)
      have h1 : ‖2 * conj c * w ^ 2‖ = 2 * ‖c‖ * ‖w‖ ^ 2 := by
        rw [norm_mul, norm_mul, Complex.norm_conj, norm_pow, Complex.norm_ofNat]
      have h3 : ‖(conj c) ^ 2‖ = ‖c‖ ^ 2 := by rw [norm_pow, Complex.norm_conj]
      rw [h1, h3] at h'
      exact h'
    have h4 : 2 * ‖c‖ * ‖w‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖ ≤ (2 * ‖c‖ + ‖c‖ ^ 2 + ‖c‖) * ‖w‖ ^ 2 := by
      have hW : (1 : ℝ) ≤ ‖w‖ ^ 2 := by nlinarith
      nlinarith [hW, hc, mul_nonneg (add_nonneg hc hc) (sub_nonneg.mpr hW)]
    linarith
  have htotal : ‖Work.Bottcher.pMap c (farInvPsi c w) - w ^ 4‖
      ≤ ((4 * farInvC c / ‖w‖) * (3 * ‖w‖) * (6 * ‖w‖ ^ 2))
        + (2 * ‖c‖ + ‖c‖ ^ 2 + ‖c‖) * ‖w‖ ^ 2 := by
    have h := norm_add_le (Work.Bottcher.pMap c (farInvPsi c w) - Work.Bottcher.pMap c w)
      (Work.Bottcher.pMap c w - w ^ 4)
    have he : (Work.Bottcher.pMap c (farInvPsi c w) - Work.Bottcher.pMap c w)
        + (Work.Bottcher.pMap c w - w ^ 4)
        = Work.Bottcher.pMap c (farInvPsi c w) - w ^ 4 := by ring
    rw [he] at h
    linarith
  -- the numerical core
  have hnum : (4 * farInvC c / ‖w‖) * (3 * ‖w‖) * (6 * ‖w‖ ^ 2)
      = 72 * farInvC c * ‖w‖ ^ 2 := by
    field_simp
    ring
  have harith : (72 * farInvC c + (2 * ‖c‖ + ‖c‖ ^ 2 + ‖c‖)) * ‖w‖ ^ 2 ≤ ‖w‖ ^ 4 / 8 := by
    have h1 : 72 * farInvC c + (2 * ‖c‖ + ‖c‖ ^ 2 + ‖c‖)
        = 73 * ‖c‖ ^ 2 + 219 * ‖c‖ + 72 := by rw [farInvC]; ring
    rw [h1]
    have h2 : 8 * (73 * ‖c‖ ^ 2 + 219 * ‖c‖ + 72) ≤ (1024 * (1 + ‖c‖)) ^ 2 := by
      nlinarith [sq_nonneg ‖c‖, sq_nonneg (1 + ‖c‖), hc]
    have h3 : (1024 * (1 + ‖c‖)) ^ 2 ≤ ‖w‖ ^ 2 := by
      have h0 : (0 : ℝ) ≤ 1024 * (1 + ‖c‖) := by positivity
      have h4 : 1024 * (1 + ‖c‖) ≤ ‖w‖ := by nlinarith
      exact pow_le_pow_left₀ h0 h4 2
    have h5 : 8 * (73 * ‖c‖ ^ 2 + 219 * ‖c‖ + 72) ≤ ‖w‖ ^ 2 := le_trans h2 h3
    nlinarith [h5, sq_nonneg ‖w‖]
  rw [norm_pow]
  rw [hnum] at htotal
  linarith [htotal, harith]

/-- **The functional equation of the inverse branch**: `p_c (ψ w) = ψ (w^4)` for
`‖w‖ ≥ farInvR c`. -/
theorem farInvPsi_pMap (c w : ℂ) (hw : farInvR c ≤ ‖w‖) :
    Work.Bottcher.pMap c (farInvPsi c w) = farInvPsi c (w ^ 4) := by
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hw1024 : (1024 : ℝ) ≤ ‖w‖ := by
    have := hw; nlinarith
  obtain ⟨hzball, hzbot, hzdist⟩ := farInvPsi_reg c w hw
  -- `w^4` is again in the far region
  have hw4R : farInvR c ≤ ‖w ^ 4‖ := by
    rw [norm_pow]
    have h1 : (1 : ℝ) ≤ ‖w‖ := by linarith
    calc farInvR c ≤ ‖w‖ := hw
      _ = ‖w‖ ^ 1 := (pow_one _).symm
      _ ≤ ‖w‖ ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
  obtain ⟨hz'ball, hz'bot, hz'dist⟩ := farInvPsi_reg c (w ^ 4) hw4R
  -- `ψ w` is in the far region, so the Böttcher equation of the quartic applies
  have hznorm_ge : Work.Bottcher.escapeRadius c ≤ ‖farInvPsi c w‖ := by
    have hclose : ‖farInvPsi c w - w‖ ≤ ‖w‖ / 8 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hzball
      exact hzball
    have h : ‖w‖ ≤ ‖farInvPsi c w‖ + ‖farInvPsi c w - w‖ := by
      have h' := norm_add_le (farInvPsi c w) (-(farInvPsi c w - w))
      have he : farInvPsi c w + -(farInvPsi c w - w) = w := by ring
      rw [he, norm_neg] at h'
      exact h'
    have h2 : ‖farInvPsi c w‖ ≥ 7 * ‖w‖ / 8 := by linarith
    have h3 : Work.Bottcher.escapeRadius c ≤ 7 * ‖w‖ / 8 := by
      rw [Work.Bottcher.escapeRadius]
      nlinarith [norm_nonneg c]
    linarith
  have hcomm : Work.Bottcher.bottcher c (Work.Bottcher.pMap c (farInvPsi c w)) = w ^ 4 := by
    have h1 := Work.Bottcher.Core.bottcher_comm_pMap_of_escapeRadius_le c hznorm_ge
    rw [h1, hzbot]
  have hmem : Work.Bottcher.pMap c (farInvPsi c w) ∈ Metric.closedBall (w ^ 4) (‖w ^ 4‖ / 8) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact norm_pMap_farInvPsi_sub_pow4_le c w hw
  exact (farInvPsi_unique c (w ^ 4) hw4R hmem hcomm).trans (farInvPsi_unique c (w ^ 4) hw4R hz'ball hz'bot).symm

/-- **Tangency of the inverse branch at infinity**: `ψ w / w → 1` along the cocompact
filter. -/
theorem farInvPsi_tendsto_div (c : ℂ) :
    Tendsto (fun w : ℂ => farInvPsi c w / w) (Filter.cocompact ℂ) (nhds (1 : ℂ)) := by
  have hnorm : Tendsto (fun w : ℂ => ‖w‖) (Filter.cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop
  have hboundlim : Tendsto (fun w : ℂ => 4 * farInvC c / ‖w‖ ^ 2) (Filter.cocompact ℂ)
      (nhds 0) := by
    have hsq : Tendsto (fun w : ℂ => ‖w‖ * ‖w‖) (Filter.cocompact ℂ) atTop :=
      hnorm.atTop_mul_atTop₀ hnorm
    have hinv : Tendsto (fun w : ℂ => (‖w‖ * ‖w‖)⁻¹) (Filter.cocompact ℂ) (nhds 0) :=
      hsq.inv_tendsto_atTop
    have hmul : Tendsto (fun w : ℂ => 4 * farInvC c * (‖w‖ * ‖w‖)⁻¹) (Filter.cocompact ℂ)
        (nhds (4 * farInvC c * 0)) := hinv.const_mul (4 * farInvC c)
    have hmul' : Tendsto (fun w : ℂ => 4 * farInvC c * (‖w‖ * ‖w‖)⁻¹)
        (Filter.cocompact ℂ) (nhds 0) := by simpa using hmul
    refine hmul'.congr' ?_
    filter_upwards with w
    rw [div_eq_mul_inv, sq]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεev : ∀ᶠ w : ℂ in Filter.cocompact ℂ, 4 * farInvC c / ‖w‖ ^ 2 < ε :=
    hboundlim.eventually (isOpen_Iio.mem_nhds hε)
  have hRev : ∀ᶠ w : ℂ in Filter.cocompact ℂ, max (farInvR c) 1 ≤ ‖w‖ :=
    hnorm.eventually (eventually_ge_atTop (max (farInvR c) 1))
  filter_upwards [hεev, hRev] with w hwlt hwge
  have hwR : farInvR c ≤ ‖w‖ := le_trans (le_max_left _ _) hwge
  have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans (le_max_right _ _) hwge
  have hwpos : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le zero_lt_one hw1
  have hwne : w ≠ 0 := norm_pos_iff.mp hwpos
  obtain ⟨-, -, hzdist⟩ := farInvPsi_reg c w hwR
  rw [dist_eq_norm]
  have heq : farInvPsi c w / w - 1 = (farInvPsi c w - w) / w := by field_simp
  rw [heq, norm_div]
  calc ‖farInvPsi c w - w‖ / ‖w‖ ≤ (4 * farInvC c / ‖w‖) / ‖w‖ :=
        div_le_div_of_nonneg_right hzdist (norm_nonneg w)
    _ = 4 * farInvC c / ‖w‖ ^ 2 := by rw [div_div, sq]
    _ < ε := hwlt

/-- **Existence of a far inverse Böttcher branch.**  For every parameter `c` there is a radius
`R ≥ 2`, a constant `C > 0` and a map `ψ` which is a right inverse of the product-formula
Böttcher coordinate `bottcher c` on `{‖w‖ ≥ R}`, stays within `O(1/‖w‖)` of the identity,
satisfies the functional equation `p_c (ψ w) = ψ (w^4)`, and is tangent to the identity at
infinity. -/
theorem exists_farInverseBottcher (c : ℂ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ C : ℝ, 0 < C ∧ ∃ ψ : ℂ → ℂ,
      (∀ w : ℂ, R ≤ ‖w‖ → Work.Bottcher.bottcher c (ψ w) = w) ∧
        (∀ w : ℂ, R ≤ ‖w‖ → ‖w‖ / 2 ≤ ‖ψ w‖) ∧
        (∀ w : ℂ, R ≤ ‖w‖ → ‖ψ w - w‖ ≤ C / ‖w‖) ∧
        (∀ w : ℂ, R ≤ ‖w‖ → Work.Bottcher.pMap c (ψ w) = ψ (w ^ 4)) ∧
        Filter.Tendsto (fun w : ℂ => ψ w / w) (Filter.cocompact ℂ) (nhds (1 : ℂ)) := by
  refine ⟨max 2 (farInvR c), le_max_left _ _, 4 * farInvC c, by positivity, farInvPsi c,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact (farInvPsi_reg c w (le_trans (le_max_right _ _) hw)).2.1
  · intro w hw
    have hwR : farInvR c ≤ ‖w‖ := le_trans (le_max_right _ _) hw
    obtain ⟨hzball, -, -⟩ := farInvPsi_reg c w hwR
    have hclose : ‖farInvPsi c w - w‖ ≤ ‖w‖ / 8 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hzball
      exact hzball
    have h := norm_add_le (farInvPsi c w) (-(farInvPsi c w - w))
    have he : farInvPsi c w + -(farInvPsi c w - w) = w := by ring
    rw [he, norm_neg] at h
    nlinarith [norm_nonneg w]
  · intro w hw
    have hwR : farInvR c ≤ ‖w‖ := le_trans (le_max_right _ _) hw
    exact (farInvPsi_reg c w hwR).2.2
  · intro w hw
    have hwR : farInvR c ≤ ‖w‖ := le_trans (le_max_right _ _) hw
    exact farInvPsi_pMap c w hwR
  · exact farInvPsi_tendsto_div c

end

end Work.Bottcher.Inverse
