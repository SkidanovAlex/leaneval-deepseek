import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.LatticeModel.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `x ↦ lhyProfile c (eucNorm3 x)` on `ℝ³`

The Bogoliubov model bracket `lhyProfile c` (see
`Submission.Work.BoseBox.LatticeModel.Defs`) blows up only like `r⁻²` at the
origin and decays like `r⁻⁴` at infinity.  Since the three-dimensional measure
element is `4π r² dr`, both singularities are integrable; this module turns that
statement into the machine-checked lemma `integrable_lhyProfile`.

The proof is split into two independent ingredients:

* `integrable_eucNorm3_iff` — the radial transfer: integrability on
  `(Fin 3 → ℝ, eucNorm3)` of a function of the radius alone is equivalent to
  integrability of `r ↦ r² g r` on `(0,∞)`.  This is
  `Submission.BoseGases.integrable_radial_r3` transported along the
  measure-preserving identification `Fin 3 → ℝ ≃ EuclideanSpace ℝ (Fin 3)`.
* `integrableOn_lhyProfile_mul` — the one-dimensional statement, proved from
  the two pointwise bounds `h1` (behaviour near the origin) and `h2` (decay at
  infinity) by splitting `(0,∞)` at `r = 1`: on `(0,1]` the bracket is bounded
  by the constant `c + c²/2`, while on `(1,∞)` it is dominated by
  `(c³/2) r⁻²`, which is integrable by `integrableOn_Ioi_rpow_of_lt`.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseBox.LatticeModel

/-- `lhyProfile c` is measurable (it is built from arithmetic operations,
`r ↦ r ^ 2` and `Real.sqrt`). -/
lemma measurable_lhyProfile (c : ℝ) : Measurable (lhyProfile c) := by
  unfold lhyProfile
  measurability

/-- **Radial transfer of integrability.**  A function `g` of the radius only is
integrable on `(Fin 3 → ℝ, eucNorm3)` if and only if `r ↦ r² g r` is integrable
on `(0,∞)`; the factor `r²` is the three-dimensional Jacobian. -/
lemma integrable_eucNorm3_iff (g : ℝ → ℝ) :
    Integrable (fun x : Fin 3 → ℝ => g (Submission.BoseGases.eucNorm3 x)) volume ↔
      IntegrableOn (fun r : ℝ => r ^ 2 * g r) (Set.Ioi (0 : ℝ)) volume := by
  have hmp : MeasurePreserving
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hemb : MeasurableEmbedding
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
  have hcomp : (fun x : Fin 3 → ℝ => g (Submission.BoseGases.eucNorm3 x))
      = (fun y : EuclideanSpace ℝ (Fin 3) => g ‖y‖) ∘ (WithLp.toLp 2) := by
    funext x
    simp only [Function.comp_apply]
    rw [eucNorm3_eq_norm]
  rw [hcomp, hmp.integrable_comp_emb hemb]
  exact Submission.BoseGases.integrable_radial_r3

/-- **One-dimensional integrability.**  From the behaviour `|lhyProfile c r| ≤
c + c²/(2r²)` near the origin and the decay `|lhyProfile c r| ≤ c³/(2r⁴)` at
infinity, the radial integrand `r ↦ r² · lhyProfile c r` is integrable on
`(0,∞)`. -/
lemma integrableOn_lhyProfile_mul {c : ℝ} (hc : 0 < c)
    (h1 : ∀ r : ℝ, 0 ≤ r → |lhyProfile c r| ≤ c + c ^ 2 / (2 * r ^ 2))
    (h2 : ∀ r : ℝ, 0 < r → |lhyProfile c r| ≤ c ^ 3 / (2 * r ^ 4)) :
    IntegrableOn (fun r : ℝ => r ^ 2 * lhyProfile c r) (Set.Ioi (0 : ℝ)) volume := by
  have hmeas : AEStronglyMeasurable (fun r : ℝ => r ^ 2 * lhyProfile c r) volume :=
    ((measurable_id.pow_const 2).mul (measurable_lhyProfile c)).aestronglyMeasurable
  -- `r ↦ r⁻²` is integrable at infinity.
  have hrpow : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) volume :=
    integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
  -- Near the origin the integrand is uniformly bounded.
  have hsmall : IntegrableOn (fun r : ℝ => r ^ 2 * lhyProfile c r) (Set.Ioc (0 : ℝ) 1) volume := by
    refine IntegrableOn.of_bound ?hfin ?hmeas (c + c ^ 2 / 2) ?hbound
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact hmeas.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hr0 : (0 : ℝ) < r := hr.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r)]
      have hle2 : r ^ 2 ≤ 1 := by nlinarith [mul_self_le_mul_self (le_of_lt hr0) hr.2]
      calc r ^ 2 * |lhyProfile c r| ≤ r ^ 2 * (c + c ^ 2 / (2 * r ^ 2)) :=
            mul_le_mul_of_nonneg_left (h1 r (le_of_lt hr0)) (sq_nonneg r)
        _ = c * r ^ 2 + c ^ 2 / 2 := by field_simp
        _ ≤ c + c ^ 2 / 2 := by nlinarith [hc]
  -- At infinity the integrand is dominated by `(c³/2) r⁻²`.
  have hbig : IntegrableOn (fun r : ℝ => r ^ 2 * lhyProfile c r) (Set.Ioi (1 : ℝ)) volume := by
    have hmaj : IntegrableOn (fun r : ℝ => (c ^ 3 / 2) * r ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) volume :=
      hrpow.const_mul (c ^ 3 / 2)
    refine Integrable.mono' hmaj ?_ ?_
    · exact hmeas.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r)]
      calc r ^ 2 * |lhyProfile c r| ≤ r ^ 2 * (c ^ 3 / (2 * r ^ 4)) :=
            mul_le_mul_of_nonneg_left (h2 r hr0) (sq_nonneg r)
        _ = (c ^ 3 / 2) * r ^ (-2 : ℝ) := by
            rw [Real.rpow_neg (le_of_lt hr0), Real.rpow_two]
            field_simp
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext r
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1', _⟩ | h)
      · exact h1'
      · linarith
    · intro h
      rcases le_or_gt r 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'
  have hU := hsmall.union hbig
  rw [hset] at hU
  exact hU

theorem integrable_lhyProfile {c : ℝ} (hc : 0 < c)
    (h1 : ∀ r : ℝ, 0 ≤ r → |lhyProfile c r| ≤ c + c ^ 2 / (2 * r ^ 2))
    (h2 : ∀ r : ℝ, 0 < r → |lhyProfile c r| ≤ c ^ 3 / (2 * r ^ 4)) :
    MeasureTheory.Integrable (fun x : Fin 3 → ℝ => lhyProfile c (Submission.BoseGases.eucNorm3 x))
      MeasureTheory.volume :=
  (integrable_eucNorm3_iff (lhyProfile c)).mpr (integrableOn_lhyProfile_mul hc h1 h2)

end Work.BoseBox.LatticeModel
