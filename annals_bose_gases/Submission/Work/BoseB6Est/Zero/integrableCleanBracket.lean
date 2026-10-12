import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseB6Est.zpRiem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est / Zero — the clean Bogoliubov bracket is Lebesgue integrable

`cleanBracket K εT c1 c2 t = (τ̃+β) − √((τ̃+β)²−β²)` (at `r = ‖t‖`, FS's scaled
zero-point bracket) is a *radially symmetric* function of the radius `r = ‖t‖`
whose three relevant properties are proved in `zpRiem`:

* `0 ≤ φ(r) ≤ 8π+1` for every `r ≥ 0` (`phifun_nonneg`, `phifun_le_B0`);
* `φ(r) = 0` for `r > K.T` (`phifun_eq_zero_of_T_lt`) — the kernel's momentum
  cutoff, which is *what makes the integral finite*: without it only the bound
  `r·φ(r) ≤ 268` holds, which does not integrate in three dimensions.

Hence `cleanBracket` is bounded by the *constant* `8π+1` and supported in the
finite-measure set `{t | ‖t‖ ≤ K.T}`; integrability follows from the standard
`IntegrableOn.of_bound` + `integrableOn_iff_integrable_of_support_subset`.

The only non-elementary ingredient is the finiteness of the measure of the
`eucNorm3`-ball (`volume_eucNorm3_le_lt_top`), obtained by enclosing it in the
compact Euclidean closed ball (`eucNorm3` controls the sup-norm of the
coordinates) and using that Lebesgue measure on `Fin 3 → ℝ` is finite on
compacts.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB6Est.Zero

open Submission.BoseGases

local notation "ℝ³" => Fin 3 → ℝ

/-! ## 1. Measurability of the radial data -/

/-- The corpus norm `eucNorm3` on `Fin 3 → ℝ` is measurable (it is
`√(Σ_j x_j²)`). -/
lemma measurable_eucNorm3 : Measurable (fun t : ℝ³ => eucNorm3 t) := by
  unfold Submission.BoseGases.eucNorm3
  fun_prop

/-- `phifun` (the bracket as a function of the radius) is measurable. -/
lemma measurable_phifun (K : FsKernel) (εT c1 c2 : ℝ) :
    Measurable (fun r : ℝ => phifun K εT c1 c2 r) := by
  unfold phifun
  have hβ : Measurable K.β := K.meas
  have hτ : Measurable (fun r : ℝ => Work.BoseB6.fsTau εT c1 c2 r) := by
    unfold Work.BoseB6.fsTau; fun_prop
  have hα : Measurable (fun r : ℝ => Work.BoseB6.fsTau εT c1 c2 r + K.β r) := hτ.add hβ
  have hrad : Measurable (fun r : ℝ =>
      (Work.BoseB6.fsTau εT c1 c2 r + K.β r) ^ 2 - (K.β r) ^ 2) :=
    (hα.pow_const 2).sub (hβ.pow_const 2)
  exact hα.sub (Real.continuous_sqrt.measurable.comp hrad)

/-- `cleanBracket K εT c1 c2` is measurable. -/
lemma cleanBracket_measurable (K : FsKernel) (εT c1 c2 : ℝ) :
    Measurable (fun t : ℝ³ => cleanBracket K εT c1 c2 t) := by
  have hφ : Measurable (fun r : ℝ => phifun K εT c1 c2 r) := measurable_phifun K εT c1 c2
  have hfun : (fun t : ℝ³ => cleanBracket K εT c1 c2 t)
      = fun t => phifun K εT c1 c2 (nrm t) :=
    funext fun t => cleanBracket_eq_phifun K εT c1 c2 t
  rw [hfun]
  exact hφ.comp measurable_eucNorm3

/-! ## 2. Finiteness of the measure of the `eucNorm3`-ball -/

/-- `{t : ℝ³ | ‖t‖ ≤ T}` has finite Lebesgue measure (`eucNorm3` is controlled
by, hence its sublevel sets are contained in, the compact Euclidean closed
ball of radius `T`). -/
lemma volume_eucNorm3_le_lt_top {T : ℝ} (hT : 0 ≤ T) :
    (volume : Measure ℝ³) {t | eucNorm3 t ≤ T} < ⊤ := by
  have hsub : {t : ℝ³ | eucNorm3 t ≤ T} ⊆ Metric.closedBall (0 : ℝ³) T := by
    intro t ht
    rw [Set.mem_ofPred_eq] at ht
    rw [Metric.mem_closedBall, dist_pi_le_iff hT]
    intro i
    have h1 : (t i) ^ 2 ≤ ∑ j : Fin 3, (t j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (t j)) (Finset.mem_univ i)
    have h2 : |t i| ≤ eucNorm3 t := by
      rw [← Real.sqrt_sq_eq_abs, Submission.BoseGases.eucNorm3]
      exact Real.sqrt_le_sqrt h1
    rw [Real.dist_eq, Pi.zero_apply, sub_zero]
    linarith
  exact lt_of_le_of_lt (measure_mono hsub)
    (IsCompact.measure_lt_top (isCompact_closedBall 0 T))

/-! ## 3. The two pointwise facts in FS's regime -/

/-- `‖cleanBracket K εT c1 c2 t‖ ≤ 8π+1`: the bracket is nonnegative and
dominated by `β ≤ 8π+1` on the support of the kernel. -/
lemma cleanBracket_bound {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) (t : ℝ³) :
    ‖cleanBracket K εT c1 c2 t‖ ≤ 8 * Real.pi + 1 := by
  have hτ : 0 ≤ Work.BoseB6.fsTau εT c1 c2 (nrm t) :=
    fsTau_nonneg h.hε0 (by linarith [h.hε1]) (eucNorm3_nonneg t)
  rw [cleanBracket_eq_phifun, Real.norm_eq_abs, abs_of_nonneg (phifun_nonneg K hτ)]
  exact phifun_le_B0 h (eucNorm3_nonneg t)

/-- The bracket vanishes beyond the kernel's momentum cutoff `K.T`. -/
lemma cleanBracket_support {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    Function.support (fun t : ℝ³ => cleanBracket K εT c1 c2 t)
      ⊆ {t | nrm t ≤ K.T} := by
  intro t ht
  rw [Set.mem_ofPred_eq]
  by_contra hlt
  have hlt' : K.T < nrm t := not_le.mp hlt
  have hz : cleanBracket K εT c1 c2 t = 0 := by
    rw [cleanBracket_eq_phifun]
    exact phifun_eq_zero_of_T_lt K h.hε0 (by linarith [h.hε1]) hlt'
  exact ht hz

/-! ## 4. The requested integrability -/

theorem integrableCleanBracket {K : Work.BoseB6Est.FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : Work.BoseB6Est.FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    MeasureTheory.Integrable (fun t : Fin 3 → ℝ => Work.BoseB6Est.cleanBracket K εT c1 c2 t) := by
  have hT0 : (0 : ℝ) ≤ K.T := le_trans zero_le_one h.hT1
  have hSmeas : MeasurableSet {t : ℝ³ | nrm t ≤ K.T} :=
    measurableSet_le measurable_eucNorm3 measurable_const
  have hfin : (volume : Measure ℝ³) {t : ℝ³ | nrm t ≤ K.T} < ⊤ :=
    volume_eucNorm3_le_lt_top hT0
  rw [← integrableOn_iff_integrable_of_support_subset (cleanBracket_support h)]
  refine IntegrableOn.of_bound hfin
    (cleanBracket_measurable K εT c1 c2).aestronglyMeasurable.restrict (8 * Real.pi + 1) ?_
  rw [ae_restrict_iff' hSmeas]
  exact Filter.Eventually.of_forall fun t _ => cleanBracket_bound h t

end Work.BoseB6Est.Zero
