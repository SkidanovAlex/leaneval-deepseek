import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibreSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal

namespace Work.BoseFixB1.Cube.Loc

/-! # `Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibre_integrable`

The `w`-integrability of the kinetic slot's fibre marginal, together with its per-slot core
`integrable_fibreSlot`.  Both are the **second component of the internal `hkey`** of the PROVED
`Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibreSplit` (whose proof is in
`Submission/Work/BoseFixB1/Cube/Loc/tBdiagFormInd_fibreSplit.lean`), made public here.

* `integrable_fibreSlot` — the `j`-th summand `fibreSlot k m a V A χ F Φ j` of the fibre marginal is
  integrable on `abox m a` w.r.t. `volume`.  Its proof is a verbatim transcription of the
  `hkey` sub-proof: the joint a.e.-strong measurability of the uncurried integrand
  (`fibreAmpAEMeasurable_aux`), the uniform amplitude bound on the fibre states
  (`norm_tBamp_le_of_boundedOn` + `abs_boxQInd_fibre_le`), the per-`p` box Fubini
  (`Work.BoseFixB1B.tBamp_amplitude_box_fubini`, whose `IntegrableOn` input is
  `ampSqIntegrableOn_aux`) and the `p`-integrability hypothesis `hint` at the slot
  `Fin.castAdd m j` of `Φ`, combined through `MeasureTheory.integrable_prod_iff` and
  `Integrable.integral_prod_right`.
* `tBdiagFormInd_fibre_integrable` — the frozen target: the fibre marginal of `tBdiagFormInd` is
  integrable on `abox m a`.  It is `integrable_finsetSum` over the `k` slots, using the definitional
  identity `sum_fibreSlot_eq_tBdiagFormInd`.

No new analytic input is needed: every ingredient already occurs in the proof of
`tBdiagFormInd_fibreSplit`. -/

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-- **The `j`-th fibre slot is integrable.**  This is the second component of the internal `hkey`
of `tBdiagFormInd_fibreSplit`, isolated and made public.

The proof runs the `p ↔ w` Fubini of the slot-`x` integral: the per-`p` box Fubini
`Work.BoseFixB1B.tBamp_amplitude_box_fubini` rewrites the box integral at the slot
`Fin.castAdd m j` of `Φ` as the `w`-integral of the same expression at the fibre state; the
`p`-integrability of the `w`-integrated slot is `hint`; the `w`-integrability for a.e. `p` comes
from the uniform amplitude bound on the fibre states; joint a.e.-strong measurability is
`fibreAmpAEMeasurable_aux`.  `MeasureTheory.integrable_prod_iff` combines the two, and
`Integrable.integral_prod_right` then transports integrability back to the `w`-marginal. -/
theorem integrable_fibreSlot {k m : ℕ} {a V : ℝ} (ha : 0 < a) (hk : 0 < k)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hχA : ∀ z, z ∉ A → χ z = 0)
    {F : ℝ → ℝ} (hFm : Measurable F) (hFnn : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ENat) Ψ → ∀ i : Fin N,
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖ *
        ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2)))
    {Φ : Submission.BoseGases.X (k + m) → ℝ} (hΦc : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : Work.BoseFixB1.Cube.Loc.SubsectorSupp k m a A Φ) (j : Fin k) :
    MeasureTheory.Integrable (fibreSlot k m a V A χ F Φ j)
      ((volume : Measure (X m)).restrict (abox m a)) := by
  classical
  have hΦm : Measurable Φ := hΦc.continuous.measurable
  have hχint : Integrable (fun z : E3 => |χ z|) :=
    (hχc.integrable_of_hasCompactSupport hχs).abs
  have hAfin : (volume : Measure E3) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le)
  obtain ⟨CΦ, hCΦ⟩ := (abox_compact (k + m) ha).exists_bound_of_continuousOn
    (f := Φ) hΦc.continuous.continuousOn
  have hCΦ0 : 0 ≤ CΦ := le_trans (norm_nonneg (Φ 0)) (hCΦ _ (zero_mem_abox ha.le))
  have hΦb : ∀ x ∈ abox (k + m) a, |Φ x| ≤ CΦ :=
    fun x hx => by simpa [Real.norm_eq_abs] using hCΦ x hx
  haveI hνfin : IsFiniteMeasure ((volume : Measure (X m)).restrict (abox m a)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top m a ha.le⟩
  -- (a) the per-`p` box Fubini
  have hIntOn : ∀ p : E3, IntegrableOn (fun x : X (k + m) =>
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.castAdd m j) Φ)
        (Fin.castAdd m j) x‖ ^ 2) (abox (k + m) a) := fun p =>
    ampSqIntegrableOn_aux (N := k + m) (a := a) (V := V) (A := A) ha hA hAc hχc hχs hχA
      hΦm hCΦ0 hΦb (Fin.castAdd m j) p
  have hfib : ∀ w : X m, (fun y : X k => Φ (mergeBlock k m (y, w))) = fibre k m Φ w := by
    intro w
    funext y
    simp only [fibre, mkSlot_eq_mergeBlock]
  have hboxFub : ∀ p : E3,
      (∫ x in abox (k + m) a, ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A (Fin.castAdd m j) Φ) (Fin.castAdd m j) x‖ ^ 2)
      = ∫ w in abox m a, ∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2 := by
    intro p
    have h1 := (Work.BoseFixB1B.tBamp_amplitude_box_fubini (N1 := k) (N2 := m) (a := a)
      (V := V) (A := A) (χ := χ) (Φ := Φ) p).1 j (hIntOn p)
    rw [h1]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [hfib w]
  -- (b) the uniform bound on the fibre amplitudes
  have hKq : ∀ (w : X m), w ∈ abox m a → ∀ u : X k, u ∈ abox k a →
      |Work.UBBInputs8.boxQInd V A j (fibre k m Φ w) u|
        ≤ CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A) :=
    fun w hw u hu => abs_boxQInd_fibre_le (a := a) (V := V) (A := A) hAc hCΦ0 hAfin hΦb hw j hu
  have hKq0 : 0 ≤ CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A) :=
    add_nonneg hCΦ0
      (mul_nonneg (inv_nonneg.mpr (abs_nonneg V)) (mul_nonneg hCΦ0 measureReal_nonneg))
  have hamp_bd : ∀ (p : E3) (w : X m), w ∈ abox m a → ∀ u : X k, u ∈ abox k a →
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖
        ≤ (CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z| :=
    fun p w hw u hu =>
      norm_tBamp_le_of_boundedOn (a := a) hAc hχint hχA hKq0 (hKq w hw) j p hu
  have hInnerBd : ∀ (p : E3) (w : X m), w ∈ abox m a →
      (∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2)
        ≤ (volume (abox k a)).toReal
          * ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2 := by
    intro p w hw
    haveI : IsFiniteMeasure ((volume : Measure (X k)).restrict (abox k a)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top k a ha.le⟩
    have hg : Integrable (fun _ : X k =>
        ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2)
        ((volume : Measure (X k)).restrict (abox k a)) := integrable_const _
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := (volume : Measure (X k)).restrict (abox k a))
      (f := fun u : X k => ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2)
      (g := fun _ : X k =>
        ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2)
      (Filter.Eventually.of_forall fun u => sq_nonneg _) hg
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem (abox_measurable k a)] with u hu
        exact pow_le_pow_left₀ (norm_nonneg _) (hamp_bd p w hw u hu) 2)
    have hconst : (∫ u : X k,
        ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2
        ∂((volume : Measure (X k)).restrict (abox k a)))
        = (volume (abox k a)).toReal
          * ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2 := by
      rw [MeasureTheory.integral_const, Measure.real_def, Measure.restrict_apply_univ,
        smul_eq_mul]
    rwa [hconst] at hmono
  -- (c) the joint integrand
  set φ : E3 → X m → ℝ := fun p w => F ‖p‖ * ((a ^ 3)⁻¹ *
    ∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
      (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2) with hφdef
  have haesm : AEStronglyMeasurable (Function.uncurry φ)
      ((volume : Measure E3).prod ((volume : Measure (X m)).restrict (abox m a))) := by
    have hE := fibreAmpAEMeasurable_aux (k := k) (m := m) (a := a) (V := V) (A := A) hA hχc hΦm j
    have hFaes : AEStronglyMeasurable (fun q : E3 × X m => F ‖q.1‖)
        ((volume : Measure E3).prod ((volume : Measure (X m)).restrict (abox m a))) :=
      (hFm.comp (continuous_norm.measurable.comp measurable_fst)).aestronglyMeasurable
    have h := hFaes.mul (hE.const_mul ((a ^ 3)⁻¹))
    refine h.congr ?_
    filter_upwards with q
    rw [hφdef]
    rfl
  have hIntW : ∀ᵐ p ∂(volume : Measure E3), Integrable (fun w : X m => φ p w)
      ((volume : Measure (X m)).restrict (abox m a)) := by
    filter_upwards [haesm.prodMk_left] with p hp
    refine Integrable.of_bound hp (|F ‖p‖| * (|(a ^ 3)⁻¹| * ((volume (abox k a)).toReal
      * ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2))) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (abox_measurable m a)] with w hw
    have hI0 : 0 ≤ ∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2 :=
      integral_nonneg (fun u => sq_nonneg _)
    rw [hφdef]
    calc ‖F ‖p‖ * ((a ^ 3)⁻¹ * (∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2))‖
        = |F ‖p‖| * (|(a ^ 3)⁻¹| * (∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2)) := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_of_nonneg hI0]
      _ ≤ |F ‖p‖| * (|(a ^ 3)⁻¹| * ((volume (abox k a)).toReal
            * ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hInnerBd p w hw) ?_) ?_
          · positivity
          · positivity
  have hIntP : Integrable (fun p : E3 => ∫ w, ‖φ p w‖
      ∂((volume : Measure (X m)).restrict (abox m a))) (volume : Measure E3) := by
    have heq : (fun p : E3 => ∫ w, ‖φ p w‖
          ∂((volume : Measure (X m)).restrict (abox m a)))
        = (fun p : E3 => F ‖p‖ * ((a ^ 3)⁻¹ *
            ∫ x in abox (k + m) a, ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd V A (Fin.castAdd m j) Φ)
              (Fin.castAdd m j) x‖ ^ 2)) := by
      funext p
      have hnn : ∀ w : X m, 0 ≤ φ p w := by
        intro w
        rw [hφdef]
        exact mul_nonneg (hFnn _) (mul_nonneg (by positivity)
          (integral_nonneg (fun u => sq_nonneg _)))
      rw [show (fun w : X m => ‖φ p w‖) = fun w : X m => φ p w from
        funext fun w => Real.norm_of_nonneg (hnn w)]
      simp only [hφdef]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [← hboxFub p]
    rw [heq]
    exact hint (k + m) Φ hΦc (Fin.castAdd m j)
  have hJoint : Integrable (Function.uncurry φ)
      ((volume : Measure E3).prod ((volume : Measure (X m)).restrict (abox m a))) :=
    (integrable_prod_iff haesm).mpr ⟨hIntW, hIntP⟩
  have h1 : Integrable (fun w : X m => ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, φ p w
      ∂(volume : Measure E3)) ((volume : Measure (X m)).restrict (abox m a)) :=
    hJoint.integral_prod_right.const_mul _
  refine h1.congr ?_
  filter_upwards with w
  simp only [fibreSlot, hφdef]

/-- The kinetic slot's **fibre integrability**: the `w`-marginal of the FS-faithful `p`-diagonal form
`tBdiagFormInd a A V χ F` at the fibre state `fibre k m Φ w` is integrable on the outer box `abox m a`.
Companion of the PROVED `Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibreSplit` — it is exactly the second
component of the internal `hkey` of that proof, made public; it is needed to split the sum
`bGapCoeff·cn + tBdiag + qLHSword` inside the `Dloc`-integral of the Step-Loc assembly
(`Work.BoseFixB1.Cube.Loc.sbWordCube_fibreSplit_of_integrable`).

Route (every ingredient is already proved inside `tBdiagFormInd_fibreSplit.lean`, which this file
should import; do NOT import `.../fibreAmpAEMeasurable.lean`, it no longer builds).  Fix the slot
`j : Fin k` and put `φ p w := F ‖p‖ * ((a^3)⁻¹ * ∫ u in abox k a, ‖tBamp χ p (Q_{A,j}(fibre k m Φ w)) j u‖²)`.
(i) `Integrable.of_bound` (uniform bound from the proved `abs_boxQInd_fibre_le`, `norm_tBamp_le_of_boundedOn`,
the `hInnerBd` inequality) gives, for a.e. `p`, `Integrable (fun w => φ p w)` w.r.t.
`volume.restrict (abox m a)`;
(ii) `hint` applied to `Φ` at the slot `Fin.castAdd m j`, together with the per-`p` box Fubini
`Work.BoseFixB1B.tBamp_amplitude_box_fubini` (giving the `hboxFub` identity) makes
`F ‖p‖ * ((a^3)⁻¹ * ∫ x in abox (k+m) a, ‖tBamp χ p (Q_{A,castAdd j}Φ) (castAdd j) x‖²)` the `w`-integral
of `φ p ·`, hence integrable in `p`;
(iii) joint a.e.-strong-measurability of `Function.uncurry φ` is the proved `fibreAmpAEMeasurable_aux`
(in the sibling file; continuity of `χ`, measurability of `Φ`).
Then `MeasureTheory.integrable_prod_iff` and `Integrable.integral_prod_right` give
`Integrable (fibreSlot k m a V A χ F Φ j)`, and `Integrable.finset_sum` over `j : Fin k` together with
`sum_fibreSlot_eq_tBdiagFormInd` concludes. -/
theorem tBdiagFormInd_fibre_integrable {k m : ℕ} {a V : ℝ} (ha : 0 < a) (hk : 0 < k)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hχA : ∀ z, z ∉ A → χ z = 0)
    {F : ℝ → ℝ} (hFm : Measurable F) (hFnn : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ENat) Ψ → ∀ i : Fin N,
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖ *
        ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2)))
    {Φ : Submission.BoseGases.X (k + m) → ℝ} (hΦc : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : Work.BoseFixB1.Cube.Loc.SubsectorSupp k m a A Φ) :
    MeasureTheory.IntegrableOn
      (fun y : Submission.BoseGases.X m =>
        Work.UBBInputs8.tBdiagFormInd a A V χ F (Work.BoseFixB1.Cube.Loc.fibre k m Φ y))
      (Submission.BoseGases.abox m a) MeasureTheory.volume := by
  have hsum : MeasureTheory.Integrable
      (fun w : Submission.BoseGases.X m =>
        ∑ j : Fin k, fibreSlot k m a V A χ F Φ j w)
      ((volume : Measure (X m)).restrict (abox m a)) :=
    integrable_finsetSum Finset.univ
      (fun j _ => integrable_fibreSlot ha hk hA hAc hχc hχs hχA hFm hFnn hint hΦc hsupp j)
  exact hsum.congr (Filter.Eventually.of_forall
    (fun w => sum_fibreSlot_eq_tBdiagFormInd k m a V A χ F Φ w))

end Work.BoseFixB1.Cube.Loc
