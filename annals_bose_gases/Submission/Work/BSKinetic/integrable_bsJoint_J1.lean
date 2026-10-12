import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.bsMean_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.exists_radius_eq_zero_of_hasCompactSupport
import Submission.Work.BSKinetic.Decomp.norm_ge_of_bsWin_ne_zero
import Submission.Work.BSKinetic.integrable_uncurry_bsWin_deriv_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.integrable_bsJoint_J1`

**The `J₁`-integrand of the moving-box family is `L¹`.**  For `ℓ > 0` and a smooth compactly
supported one-body state `ψ : ℝ³ → ℝ`, the function

    `p = (x, u) ↦ (Q_{Λ(u)}ψ)(x)² · (∂_k χ_{Λ(u)}(x))²`

is `Integrable` for the product of the Lebesgue measure on `ℝ³` with itself.  Here

    `bsQ ℓ u ψ x = ψ x − bsMean ℓ u ψ`,     `bsWin ℓ u x = χ_ℓ(x − ℓu)`

are the mean-free part of `ψ` in the moving box `Λ(u) = ℓu + acube ℓ` and its window
(`Work.BSKinetic.bsQ`, `Work.BSKinetic.bsWin`).

## Proof

Both factors are handled by their *support*:

* the derivative `∂_k χ_ℓ(x − ℓu)` vanishes as soon as `‖x − ℓu‖ > ℓ/2`
  (`fderiv_chiScale_eq_zero_of_norm_gt`);
* `‖x − ℓu‖ ≤ ℓ/2` together with `ψ x ≠ 0` (resp. `bsMean ℓ u ψ ≠ 0`) forces both `x` and `u`
  into balls of radius `Rψ`-dependent size (`bs_norm_lt_of_ne_zero`,
  `bs_norm_smul_lt_of_bsMean_ne_zero`).

Hence the integrand is supported in the compact product `closedBall 0 (Rψ + ℓ + ℓ/2) ×
closedBall 0 ((Rψ + ℓ)/ℓ)`.  It is *continuous*: the state factor `ψ x − bsMean ℓ u ψ` is
continuous in `(x,u)` because the box mean `u ↦ ∫_{acube ℓ} ψ(ℓu + z) dz` is continuous by
dominated convergence on the fixed cube `acube ℓ` (the dominating constant being a bound for
`ψ`, which exists by compact support).  Continuity plus compact support gives integrability
(`Continuous.integrable_of_hasCompactSupport`), and the original integrand agrees with the
nice one pointwise, the derivative factor being a translate:
`fderiv ℝ (bsWin ℓ u) x = fderiv ℝ (chiScale ℓ) (x − ℓu)`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The derivative of the moving window -/

/-- The moving window is the translate of `chiScale ℓ`: `bsWin ℓ u = χ_ℓ(· − ℓu)`
definitionally. -/
lemma bsWin_eq_chiScale_comp_sub (ℓ : ℝ) (u : ℝ³) :
    bsWin ℓ u = fun y : ℝ³ => chiScale ℓ (y - ℓ • u) := rfl

/-- **The derivative of the moving window.**  Since `bsWin ℓ u y = χ_ℓ(y − ℓu)`, the directional
derivative of the window along `kcStdBasis k` at `x` is the derivative of `χ_ℓ` at `x − ℓu`. -/
lemma fderiv_bsWin_apply {ℓ : ℝ} (hχ : Differentiable ℝ (chiScale ℓ))
    (u x : ℝ³) (k : Fin 3) :
    fderiv ℝ (bsWin ℓ u) x (kcStdBasis k)
      = fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k) := by
  show fderiv ℝ (fun y : ℝ³ => chiScale ℓ (y - ℓ • u)) x (kcStdBasis k)
      = fderiv ℝ (chiScale ℓ) (x - ℓ • u) (kcStdBasis k)
  exact fderiv_comp_sub_const_apply (chiScale ℓ) (ℓ • u) x (kcStdBasis k) hχ.differentiableAt

/-! ## 2. Elementary norm estimates for the centred cube and translations -/

/-- A point of the centred cube `acube ℓ` has norm at most `ℓ`. -/
lemma bs_norm_le_of_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℝ³} (hz : z ∈ acube ℓ) : ‖z‖ ≤ ℓ := by
  have hcomp : ∀ m : Fin 3, ‖z m‖ ≤ ℓ / 2 := by
    intro m
    have h := (mem_acube_iff ℓ z).mp hz m
    rw [Set.mem_Icc] at h
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hsq : ‖z‖ ^ 2 ≤ ℓ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖z i‖ ^ 2 ≤ ∑ _i : Fin 3, (ℓ / 2) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2
      _ = 3 * (ℓ / 2) ^ 2 := by simp
      _ ≤ ℓ ^ 2 := by nlinarith [sq_nonneg ℓ]
  have h2 := sq_le_sq.mp hsq
  rw [abs_of_nonneg (norm_nonneg z), abs_of_nonneg (le_of_lt hℓ)] at h2
  exact h2

/-- `‖ℓ • u‖ = ℓ‖u‖` for `ℓ > 0`. -/
lemma bs_norm_smul_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) : ℓ * ‖u‖ = ‖ℓ • u‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]

/-- The reverse triangle inequality in the form used below: `‖a‖ ≤ ‖a − b‖ + ‖b‖`. -/
lemma bs_norm_le_norm_sub_add {a b : ℝ³} : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
  have h := norm_add_le (a - b) b
  rwa [sub_add_cancel] at h

/-- The reverse triangle inequality in the form used below: `‖a‖ ≤ ‖b − a‖ + ‖b‖`. -/
lemma bs_norm_le_norm_sub_add' {a b : ℝ³} : ‖a‖ ≤ ‖b - a‖ + ‖b‖ := by
  have h := norm_sub_le b (b - a)
  have hba : b - (b - a) = a := by abel
  rw [hba] at h
  linarith

/-- A non-zero value of a state vanishing outside the ball of radius `R` forces its argument into
that ball. -/
lemma bs_norm_lt_of_ne_zero {R : ℝ} {ψ : ℝ³ → ℝ} (hψ : ∀ x : ℝ³, R ≤ ‖x‖ → ψ x = 0)
    {x : ℝ³} (h : ψ x ≠ 0) : ‖x‖ < R := lt_of_not_ge fun hle => h (hψ x hle)

/-! ## 3. Non-vanishing of the box mean forces the moving box into the support -/

/-- If the box mean of `ψ` over the moving box `Λ(u) = ℓu + acube ℓ` does not vanish, then some
point `ℓu + z` (`z ∈ acube ℓ`) of that box carries a non-zero value of `ψ`. -/
lemma bs_exists_mem_acube_of_bsMean_ne_zero {ℓ : ℝ} {ψ : ℝ³ → ℝ} {u : ℝ³}
    (h : bsMean ℓ u ψ ≠ 0) : ∃ z ∈ acube ℓ, ψ (ℓ • u + z) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply h
  rw [bsMean,
    show (∫ z in acube ℓ, ψ (ℓ • u + z)) = ∫ z in acube ℓ, (0 : ℝ) from
      setIntegral_congr_fun (acube_measurable ℓ) (fun z hz => hcon z hz)]
  simp

/-- **A non-zero box mean puts the moving box in the support.**  If `ψ` vanishes outside the ball
of radius `R` and `bsMean ℓ u ψ ≠ 0`, then the moving box `ℓu + acube ℓ` meets that ball, whence
`‖ℓ • u‖ < R + ℓ`. -/
lemma bs_norm_smul_lt_of_bsMean_ne_zero {ℓ R : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ∀ x : ℝ³, R ≤ ‖x‖ → ψ x = 0) {u : ℝ³} (h : bsMean ℓ u ψ ≠ 0) :
    ‖ℓ • u‖ < R + ℓ := by
  obtain ⟨z, hzmem, hzψ⟩ := bs_exists_mem_acube_of_bsMean_ne_zero h
  have hzn : ‖z‖ ≤ ℓ := bs_norm_le_of_mem_acube hℓ hzmem
  have hzR : ‖ℓ • u + z‖ < R := lt_of_not_ge fun hle => hzψ (hψ _ hle)
  have h1 : ‖ℓ • u‖ ≤ ‖ℓ • u + z‖ + ‖z‖ := by
    have hh := norm_sub_le (ℓ • u + z) z
    simpa using hh
  linarith

/-! ## 4. Continuity of the box mean -/

/-- **The moving-box mean is continuous.**  For `ℓ > 0` and `ψ` continuous with compact support,

    `u ↦ bsMean ℓ u ψ = (ℓ³)⁻¹ ∫_{acube ℓ} ψ(ℓu + z) dz`

is continuous: the `u`-dependence sits inside a *fixed* integral over the compact cube `acube ℓ`,
so dominated convergence applies with the constant bound `max C 0`, where `C` bounds `‖ψ‖` on a
ball containing the support. -/
lemma continuous_bsMean_of_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : Continuous ψ) (hcs : HasCompactSupport ψ) :
    Continuous (fun u : ℝ³ => bsMean ℓ u ψ) := by
  obtain ⟨R, _, hzero⟩ := Decomp.exists_radius_eq_zero_of_hasCompactSupport hcs
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ³) R).exists_bound_of_continuousOn
    hψ.continuousOn
  have hC' : ∀ x : ℝ³, ‖ψ x‖ ≤ max C 0 := by
    intro x
    by_cases hx : x ∈ closedBall (0 : ℝ³) R
    · exact le_trans (hC x hx) (le_max_left _ _)
    · rw [mem_closedBall, dist_zero_right] at hx
      have hx' : R ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
      rw [hzero x hx', norm_zero]
      exact le_max_right _ _
  have hmain : Continuous (fun u : ℝ³ => ∫ z in acube ℓ, ψ (ℓ • u + z)) := by
    refine continuous_of_dominated (μ := (volume : Measure ℝ³).restrict (acube ℓ))
      (F := fun u z => ψ (ℓ • u + z)) (bound := fun _ => max C 0) ?_ ?_ ?_ ?_
    · intro u
      exact (hψ.comp (by fun_prop)).aestronglyMeasurable
    · intro u
      filter_upwards with z
      exact hC' _
    · rw [integrable_const_iff]
      right
      rw [isFiniteMeasure_restrict]
      exact ne_of_lt (acube_lt_top ℓ hℓ.le)
    · filter_upwards with z
      exact hψ.comp (by fun_prop)
  simpa only [bsMean] using hmain.const_mul ((ℓ ^ 3)⁻¹)

/-! ## 5. The main theorem -/

theorem integrable_bsJoint_J1 {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (k : Fin 3) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (Work.BSKinetic.bsQ ℓ p.2 ψ p.1) ^ 2 *
        (fderiv ℝ (Work.BSKinetic.bsWin ℓ p.2) p.1 (Submission.BoseGases.kcStdBasis k)) ^ 2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hχdiff : Differentiable ℝ (chiScale ℓ) :=
    (chiScale_contDiff hℓne).differentiable (by norm_num)
  have hψc : Continuous ψ := hψ.continuous
  have hmean : Continuous (fun u : ℝ³ => bsMean ℓ u ψ) :=
    continuous_bsMean_of_hasCompactSupport hℓ hψc hcs
  -- the derivative factor is the derivative of `chiScale ℓ` at `x − ℓu`
  have hchain : ∀ p : ℝ³ × ℝ³, fderiv ℝ (bsWin ℓ p.2) p.1 (kcStdBasis k)
      = fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k) :=
    fun p => fderiv_bsWin_apply hχdiff p.2 p.1 k
  -- continuity of the integrand in its "nice" form
  have hcontD : Continuous (fun p : ℝ³ × ℝ³ =>
      fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)) :=
    ((chiScale_contDiff hℓne).continuous_fderiv (by simp) |>.clm_apply continuous_const).comp
      (continuous_fst.sub (continuous_snd.const_smul ℓ))
  have hcontφ : Continuous (fun p : ℝ³ × ℝ³ => ψ p.1 - bsMean ℓ p.2 ψ) :=
    (hψc.comp continuous_fst).sub (hmean.comp continuous_snd)
  have hcont : Continuous (fun p : ℝ³ × ℝ³ =>
      (ψ p.1 - bsMean ℓ p.2 ψ) ^ 2 *
        (fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)) ^ 2) :=
    (hcontφ.pow 2).mul (hcontD.pow 2)
  -- the compact set containing the support of the integrand
  obtain ⟨R, _hR0, hzero⟩ := Decomp.exists_radius_eq_zero_of_hasCompactSupport hcs
  set K : Set (ℝ³ × ℝ³) :=
    closedBall (0 : ℝ³) (R + ℓ + ℓ / 2) ×ˢ closedBall (0 : ℝ³) ((R + ℓ) / ℓ) with hKdef
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKcl : IsClosed K := hKc.isClosed
  have hvan : ∀ p : ℝ³ × ℝ³, p ∉ K →
      (ψ p.1 - bsMean ℓ p.2 ψ) ^ 2 *
        (fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)) ^ 2 = 0 := by
    intro p hp
    have hp' : ¬ (‖p.1‖ ≤ R + ℓ + ℓ / 2 ∧ ‖p.2‖ ≤ (R + ℓ) / ℓ) := by
      rw [hKdef] at hp
      simpa only [Set.mem_prod, mem_closedBall, dist_zero_right] using hp
    by_contra hne
    have ha : ψ p.1 - bsMean ℓ p.2 ψ ≠ 0 := by intro h0; exact hne (by rw [h0]; ring)
    have hb : fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k) ≠ 0 := by
      intro h0; exact hne (by rw [h0]; ring)
    -- the derivative factor vanishes off `‖x − ℓu‖ ≤ ℓ/2`
    have hy : ‖p.1 - ℓ • p.2‖ ≤ ℓ / 2 := by
      by_contra hcon
      rw [not_le] at hcon
      exact hb (Work.UBBInputs9.B.fderiv_chiScale_eq_zero_of_norm_gt hℓ hcon)
    have hcases : ψ p.1 ≠ 0 ∨ bsMean ℓ p.2 ψ ≠ 0 := by
      by_contra hcon
      rw [not_or] at hcon
      exact ha (by rw [not_not.mp hcon.1, not_not.mp hcon.2]; ring)
    -- the second coordinate is bounded
    have hu : ‖p.2‖ ≤ (R + ℓ) / ℓ := by
      rw [le_div_iff₀ hℓ, mul_comm, bs_norm_smul_eq hℓ]
      rcases hcases with hψnz | hm
      · have h3 : ‖p.1‖ < R := bs_norm_lt_of_ne_zero hzero hψnz
        linarith [bs_norm_le_norm_sub_add' (a := ℓ • p.2) (b := p.1), hy, hℓ]
      · have h3 : ‖ℓ • p.2‖ < R + ℓ := bs_norm_smul_lt_of_bsMean_ne_zero hℓ hzero hm
        linarith
    refine hp' ⟨?_, hu⟩
    rcases hcases with hψnz | hm
    · have h3 : ‖p.1‖ < R := bs_norm_lt_of_ne_zero hzero hψnz
      linarith
    · have h2 : ‖p.1‖ ≤ ‖p.1 - ℓ • p.2‖ + ‖ℓ • p.2‖ :=
        bs_norm_le_norm_sub_add (a := p.1) (b := ℓ • p.2)
      have h3 : ‖ℓ • p.2‖ < R + ℓ := bs_norm_smul_lt_of_bsMean_ne_zero hℓ hzero hm
      linarith
  have hcpt : HasCompactSupport (fun p : ℝ³ × ℝ³ =>
      (ψ p.1 - bsMean ℓ p.2 ψ) ^ 2 *
        (fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)) ^ 2) :=
    HasCompactSupport.intro' hKc hKcl hvan
  have hInt : Integrable (fun p : ℝ³ × ℝ³ =>
      (ψ p.1 - bsMean ℓ p.2 ψ) ^ 2 *
        (fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)) ^ 2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    hcont.integrable_of_hasCompactSupport hcpt
  refine hInt.congr (Eventually.of_forall fun p => ?_)
  show (ψ p.1 - bsMean ℓ p.2 ψ) ^ 2 *
        (fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)) ^ 2
      = (bsQ ℓ p.2 ψ p.1) ^ 2 * (fderiv ℝ (bsWin ℓ p.2) p.1 (kcStdBasis k)) ^ 2
  rw [bsQ, hchain p]

end Work.BSKinetic

end
