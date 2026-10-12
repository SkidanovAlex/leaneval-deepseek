import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1.wSmall1Pair_fibre_abs_le
import Submission.Work.BoseFixB1S.BoxPotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-!
# Integrability of a slot of the one-body fibre of the localised kernel

The sliding localisation writes the `μ`-weight of the box as a sum of slot integrals
`∫_{𝔸(N,ℓ)} Φ² · w1Fibre ℓ w_{1,B}(xᵢ)`, where `w_{1,B} = wSmallPair M ℓ d u (g₀ v h)`.

Here we only need the *slot* integrability: the fibre `z ↦ ∫_{acube ℓ} wSmallPair … z y`
is bounded uniformly in `z` by `Work.BoseFixB1.wSmall1Pair_fibre_abs_le` (it is the `L¹`-norm of
`g₀` smeared with the two localisation cutoffs), `Φ` is continuous hence bounded on the compact
box `abox N ℓ`, and `abox N ℓ` has finite volume.  It remains to see that the integrand is
a.e. strongly measurable.

For measurability we do *not* attempt to transfer a.e. strong measurability of the fibre along
the projection `x ↦ xᵢ` (that would require absolute continuity of the pushforward).  Instead we
replace the numerator `g₀ = g₀ v h`, which is only a.e. measurable, by its measurable
representative `f' = AEMeasurable.mk (g₀ v h) ·`.  Since `g₀` and `f'` agree a.e., the two fibres
agree *everywhere*: for fixed `z`, the null set where they differ is pulled back to a null set
under the measure preserving reflection `y ↦ z - y` (`Measure.measurePreserving_sub_left`), so
`integral_congr_ae` applies.  For the measurable numerator, the fibre is measurable by the
parametric-integral lemma `StronglyMeasurable.integral_prod_right`.
-/

noncomputable section

namespace Work.BoseFixR

open MeasureTheory
open scoped Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Joint measurability of the uncurried localised kernel with a measurable numerator.**
`wSmallPair M ℓ d u g z y = χ_B(z)·(g(z−y)/(χ⋆χ)((z−y)/(ℓd)))·(χ⋆χ)⁻¹((z−y)/ℓ)·χ_B(y)`:
all factors are continuous, or are the measurable numerator composed with the continuous map
`(z,y) ↦ z − y`. -/
lemma measurable_uncurry_wSmallPair {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) {g : E3 → ℝ} (hg : Measurable g) :
    Measurable fun p : E3 × E3 => Submission.BoseGases.wSmallPair M ℓ d u g p.1 p.2 := by
  have hchi : Measurable fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x :=
    (Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).measurable
  have hcs : Measurable fun p : E3 × E3 =>
      Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2) := by
    have h : Measurable fun p : E3 × E3 =>
        Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • (p.1 - p.2)) :=
      (Submission.BoseGases.conv3Small_continuous hM).measurable.comp (by fun_prop)
    simpa only [Submission.BoseGases.convScaleSmall] using h
  have hcv : Measurable fun p : E3 × E3 => Submission.BoseGases.convScale ℓ (p.1 - p.2) :=
    (Submission.BoseGases.convScale_continuous ℓ).measurable.comp (by fun_prop)
  have hnum : Measurable fun p : E3 × E3 => g (p.1 - p.2) :=
    hg.comp (by fun_prop)
  have hmain : Measurable fun p : E3 × E3 =>
      Submission.BoseGases.chiSmallB M ℓ d u p.1 *
        ((g (p.1 - p.2) / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
          / Submission.BoseGases.convScale ℓ (p.1 - p.2)) *
        Submission.BoseGases.chiSmallB M ℓ d u p.2 :=
    ((hchi.comp measurable_fst).mul ((hnum.div hcs).div hcv)).mul (hchi.comp measurable_snd)
  simpa only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled] using hmain

/-- **MEASURABILITY OF THE FIBRE** `z ↦ ∫_{acube ℓ} wSmallPair M ℓ d u g z y` for a *measurable*
numerator `g`.  The parametric integral lemma `StronglyMeasurable.integral_prod_right` needs only
joint measurability of the integrand on `E3 × E3`. -/
lemma measurable_fibre_wSmallPair {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) {g : E3 → ℝ} (hg : Measurable g) :
    Measurable fun z : E3 =>
      ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmallPair M ℓ d u g z y := by
  have hmeas := measurable_uncurry_wSmallPair hM hℓ hd u hg
  have huncurry : (Function.uncurry fun z y : E3 => Submission.BoseGases.wSmallPair M ℓ d u g z y)
      = (fun p : E3 × E3 => Submission.BoseGases.wSmallPair M ℓ d u g p.1 p.2) := rfl
  have hsm : StronglyMeasurable (Function.uncurry fun z y : E3 =>
      Submission.BoseGases.wSmallPair M ℓ d u g z y) := by
    rw [huncurry]
    exact hmeas.stronglyMeasurable
  have h := StronglyMeasurable.integral_prod_right
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
      (Submission.BoseGases.acube ℓ))
    (f := fun (z : E3) (y : E3) => Submission.BoseGases.wSmallPair M ℓ d u g z y) hsm
  exact h.measurable

theorem w1FibreSlotIntegrableOfSupport {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3))
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  intro i
  -- the numerator `g₀` is integrable, hence a.e. measurable; let `f'` be its measurable
  -- representative.
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  set f' : E3 → ℝ := AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0.aemeasurable with hf'def
  have hf'meas : Measurable f' := by
    rw [hf'def]; exact hg0.aemeasurable.measurable_mk
  have hf'eq : Submission.BoseGases.g0 v h =ᵐ[MeasureTheory.volume] f' := by
    rw [hf'def]; exact hg0.aemeasurable.ae_eq_mk
  -- the two fibres agree everywhere
  have hFibEq : ∀ z : E3,
      (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y)
        = (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u f' z y) := by
    intro z
    refine MeasureTheory.integral_congr_ae ?_
    have hmp : MeasureTheory.MeasurePreserving (fun t : E3 => z - t)
        (MeasureTheory.volume : MeasureTheory.Measure E3)
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      MeasureTheory.Measure.measurePreserving_sub_left MeasureTheory.volume z
    have hae : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
        Submission.BoseGases.g0 v h (z - y) = f' (z - y) :=
      hmp.quasiMeasurePreserving.tendsto_ae.eventually hf'eq
    filter_upwards [MeasureTheory.ae_restrict_of_ae hae] with y hy
    simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
    rw [hy]
  -- measurability of the integrand
  have hIntMeas : Measurable fun x : Submission.BoseGases.X N =>
      (Φ x) ^ 2 * ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y := by
    have hfib : Measurable fun x : Submission.BoseGases.X N =>
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y := by
      have h' : (fun x : Submission.BoseGases.X N =>
            ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y)
          = (fun x : Submission.BoseGases.X N =>
              ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmallPair M ℓ d u f' (x i) y) := by
        funext x
        exact hFibEq (x i)
      rw [h']
      exact (measurable_fibre_wSmallPair hM hℓ hd u hf'meas).comp (measurable_pi_apply i)
    exact (hΦc.measurable.pow_const 2).mul hfib
  -- the uniform fibre bound
  set Cfib : ℝ := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          / Work.SmallBoxSliding.smallConvLower M) * (8 * π * _root_.BoseGases.a v)) with hCfibdef
  have hFibBound : ∀ z : E3,
      |∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y| ≤ Cfib := by
    intro z
    exact Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  -- `Φ` is bounded on the compact box
  obtain ⟨CΦ, hCΦ⟩ :=
    (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  have hfin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (Submission.BoseGases.abox_lt_top N ℓ hℓ.le))
  haveI := hfin
  refine MeasureTheory.Integrable.of_bound
    (by simpa only [Submission.BoseGases.w1Fibre] using hIntMeas.aestronglyMeasurable)
    ((max CΦ 0) ^ 2 * |Cfib|) ?_
  refine (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mpr
    (Filter.Eventually.of_forall (fun x hx => ?_))
  have h1 : |Φ x| ≤ max CΦ 0 :=
    le_trans (by simpa only [Real.norm_eq_abs] using hCΦ x hx) (le_max_left _ _)
  have h2 : |∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) (x i) y| ≤ |Cfib| :=
    le_trans (hFibBound (x i)) (le_abs_self Cfib)
  rw [Real.norm_eq_abs, Submission.BoseGases.w1Fibre, abs_mul, abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 2) h2 (abs_nonneg _) (sq_nonneg _)

end Work.BoseFixR
