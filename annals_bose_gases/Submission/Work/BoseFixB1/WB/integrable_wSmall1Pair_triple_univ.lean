import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.WB.abs_wSmall1Pair_le_r0
import Submission.Work.BoseFixB1.WB.wbU_aemeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.integrable_wSmall1Pair_triple_univ`

Joint integrability of the localised one-body kernel

    (u, (x, y)) ↦ wSmall1Pair h M ℓ d u x y
      = χ_{B(u)}(x)·(W₁(x−y)/C_ℓ(x−y))·χ_{B(u)}(y)

on the product of the *three full* Lebesgue measures on `ℝ³ × (ℝ³ × ℝ³)` — the
unconditional companion of `Work.UBBInputs7.Finding.triple_integrable_wSmall1Pair`
(which restricts the last coordinate to the big box `acube ℓ`; the restriction is what
tames the `x`-integration there, and here the compact support of the `ℓ`-cutoff
`χ_ℓ(x) = chiScale ℓ x` plays that role).

## Structure of the argument

The two cutoffs of `wSmallPair` factor out of the modulus exactly:

    |wSmall1Pair h M ℓ d u x y| = χ_ℓ(x)·χ_M((ℓd)⁻¹x−u)·|W₁/(C_ℓ)|·χ_{B(u)}(y),

with `χ_{B(u)}(y) = χ_ℓ(y)·χ_M((ℓd)⁻¹y−u)`.  Under the regime hypotheses the *middle*
factor is bounded by `2·|g₀(x−y)|/smallConvLower M` (`abs_wSmall1Pair_le_r0`, the
`hC`-version of the pointwise domination, using `R₀ ≤ ℓd/16` for the `(ℓd)`-denominator
and the hypothesis `hC` at the explicit radius `r₀` for the `ℓ`-denominator), and the
`y`-cutoff is bounded by `chiSupAbs·chiSmallDecay M`; hence

    |wSmall1Pair| ≤ χ_ℓ(x)·χ_M((ℓd)⁻¹x−u)·(C·|g₀(x−y)|),   C := 2·χ^*·χ_M^decay/S,

and the right-hand side is *integrable*: its `(u,x)`-marginal is
`χ_ℓ(x)·(∫χ_M)·(c·‖g₀‖₁)`, integrable because `χ_ℓ` is continuous with compact support,
and the `y`-fibres are translates of `|g₀| ∈ L¹`.  The two helper lemmas below establish
exactly this (`integrable_chiScale_chiSmall_prod` for the `(u,x)`-marginal,
`integrable_dominator_wSmall1Pair_vol` for the tenzor product), and the main theorem is
then `Integrable.mono'` followed by the transport along the measure-preserving
associativity equivalence `(ℝ³ × ℝ³) × ℝ³ ≃ᵐ ℝ³ × (ℝ³ × ℝ³)`.
-/

namespace Work.BoseFixB1.WB

open MeasureTheory Metric

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `(u,x)`-marginal of the dominator is integrable.**  The sliding variable `u`
occurs only in the translate `χ_M((ℓd)⁻¹x − ·)` of the bump `χ_M`, whose `u`-integral is
the constant `∫χ_M`, so the marginal is `χ_ℓ(x)·∫χ_M`, integrable because `χ_ℓ` is a
continuous compactly supported function.  (Tonelli's theorem in the `'`-form, the fibre
variable being `u` and the marginal variable `x`.) -/
lemma integrable_chiScale_chiSmall_prod {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ p.2
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
  have hchi_int : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ x) (MeasureTheory.volume : MeasureTheory.Measure _) :=
    (Submission.BoseGases.chiScale_continuous ℓ).integrable_of_hasCompactSupport
      (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ))
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ p.2
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
  refine (integrable_prod_iff' hcont.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards with x
    exact (Work.SmallBoxSliding.integrable_chiSmall_shift (M := M) hM ((ℓ * d)⁻¹ • x)).const_mul
      (Submission.BoseGases.chiScale ℓ x)
  · have heq : (fun x : EuclideanSpace ℝ (Fin 3) => ∫ u, ‖Submission.BoseGases.chiScale ℓ x
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)‖ ∂(MeasureTheory.volume :
          MeasureTheory.Measure _))
      = fun x : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiScale ℓ x
          * (∫ z, Submission.BoseGases.chiSmall M z) := by
      funext x
      have hpt : ∀ u : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)‖
          = Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) := fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
          (Submission.BoseGases.chiSmall_nonneg M _))]
      calc (∫ u, ‖Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)‖ ∂(MeasureTheory.volume :
              MeasureTheory.Measure _))
          = ∫ u, Submission.BoseGases.chiScale ℓ x
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) ∂(MeasureTheory.volume :
                MeasureTheory.Measure _) :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ = Submission.BoseGases.chiScale ℓ x
              * (∫ u, Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
                  ∂(MeasureTheory.volume : MeasureTheory.Measure _)) := by
            rw [MeasureTheory.integral_const_mul]
        _ = Submission.BoseGases.chiScale ℓ x * (∫ z, Submission.BoseGases.chiSmall M z) := by
            rw [Submission.BoseGases.integral_comp_sub_left]
    rw [heq]
    exact (hchi_int.const_mul (∫ z, Submission.BoseGases.chiSmall M z)).congr
      (Filter.Eventually.of_forall (fun x => by ring))

/-- **Integrability of the dominating function of the localised kernel on the full
`(u,x,y)`-space.**  For any `c ≥ 0`,
`z ↦ χ_ℓ(z.1.2)·χ_M((ℓd)⁻¹z.1.2 − z.1.1)·(c·|g₀(z.1.2 − z.2)|)` is integrable for the
triple product of Lebesgue measures: apply Tonelli in the `((u,x), y)`-splitting.  The
`y`-fibres are translates of `|g₀| ∈ L¹`, and the `(u,x)`-marginal is
`χ_ℓ(x)·(∫χ_M)·(c‖g₀‖₁)`, integrable by `integrable_chiScale_chiSmall_prod`. -/
lemma integrable_dominator_wSmall1Pair_vol {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R0 : ℝ} {M : ℕ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hM : 1 ≤ M) {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hc : 0 ≤ c) :
    MeasureTheory.Integrable
      (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ z.1.2
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z.1.2 - z.1.1)
          * (c * |Submission.BoseGases.g0 v h (z.1.2 - z.2)|))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h)
      (MeasureTheory.volume : MeasureTheory.Measure _) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0abs : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      |Submission.BoseGases.g0 v h z|) (MeasureTheory.volume : MeasureTheory.Measure _) := hg0int.abs
  -- a.e.-measurability of the integrand: `g₀` enters only through the difference map
  have hmeas_g0 : AEMeasurable
      (fun q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.g0 v h (q.1.2 - q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
    ((aestronglyMeasurable_g0 (v := v) (h := h)).comp_quasiMeasurePreserving
      quasiMeasurePreserving_sub_coord₂).aemeasurable
  have hmeas_abs : AEMeasurable
      (fun q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        |Submission.BoseGases.g0 v h (q.1.2 - q.2)|)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have h1 := hmeas_g0.norm
    simpa [Real.norm_eq_abs] using h1
  have hcont1 : Continuous
      (fun q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ q.1.2
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • q.1.2 - q.1.1)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp
      (continuous_snd.comp continuous_fst)).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
  have hmeas : AEStronglyMeasurable
      (fun q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ q.1.2
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • q.1.2 - q.1.1)
          * (c * |Submission.BoseGases.g0 v h (q.1.2 - q.2)|))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
    ((hcont1.aemeasurable).mul (hmeas_abs.const_mul c)).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards with p
    have hy : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        |Submission.BoseGases.g0 v h (p.2 - y)|) (MeasureTheory.volume : MeasureTheory.Measure _) :=
      hg0abs.comp_sub_left p.2
    exact (hy.const_mul (c * (Submission.BoseGases.chiScale ℓ p.2
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)))).congr
      (Filter.Eventually.of_forall (fun y => by ring))
  · have heq : (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ∫ y, ‖Submission.BoseGases.chiScale ℓ p.2
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)
            * (c * |Submission.BoseGases.g0 v h (p.2 - y)|)‖ ∂(MeasureTheory.volume :
              MeasureTheory.Measure _))
        = fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            (Submission.BoseGases.chiScale ℓ p.2
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1))
            * (c * ∫ z, |Submission.BoseGases.g0 v h z|) := by
      funext p
      have hpt : ∀ y : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.chiScale ℓ p.2
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)
              * (c * |Submission.BoseGases.g0 v h (p.2 - y)|)‖
          = Submission.BoseGases.chiScale ℓ p.2
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)
              * (c * |Submission.BoseGases.g0 v h (p.2 - y)|) := fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
          (Submission.BoseGases.chiScale_nonneg ℓ p.2)
          (Submission.BoseGases.chiSmall_nonneg M _)) (mul_nonneg hc (abs_nonneg _)))]
      calc (∫ y, ‖Submission.BoseGases.chiScale ℓ p.2
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)
              * (c * |Submission.BoseGases.g0 v h (p.2 - y)|)‖ ∂(MeasureTheory.volume :
                MeasureTheory.Measure _))
          = ∫ y, Submission.BoseGases.chiScale ℓ p.2
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)
              * (c * |Submission.BoseGases.g0 v h (p.2 - y)|) ∂(MeasureTheory.volume :
                MeasureTheory.Measure _) := integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ = (Submission.BoseGases.chiScale ℓ p.2
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1))
              * (∫ y, c * |Submission.BoseGases.g0 v h (p.2 - y)| ∂(MeasureTheory.volume :
                  MeasureTheory.Measure _)) := by
            rw [← MeasureTheory.integral_const_mul]
        _ = (Submission.BoseGases.chiScale ℓ p.2
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1))
              * (c * ∫ y, |Submission.BoseGases.g0 v h (p.2 - y)| ∂(MeasureTheory.volume :
                  MeasureTheory.Measure _)) := by
            rw [MeasureTheory.integral_const_mul]
        _ = (Submission.BoseGases.chiScale ℓ p.2
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1))
              * (c * ∫ z, |Submission.BoseGases.g0 v h z|) := by
            refine congrArg (fun t : ℝ => (Submission.BoseGases.chiScale ℓ p.2
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) * (c * t)) ?_
            exact Submission.BoseGases.integral_comp_sub_left
              (fun z : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h z|) p.2
    rw [heq]
    exact (integrable_chiScale_chiSmall_prod hM hℓ).const_mul
      (c * ∫ z, |Submission.BoseGases.g0 v h z|) |>.congr
      (Filter.Eventually.of_forall (fun p => by ring))

/-- **Joint integrability of the localised one-body kernel** `wSmall1Pair` on the product
of the three full Lebesgue measures. -/
theorem integrable_wSmall1Pair_triple_univ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ} {M : ℕ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hM : 1 ≤ M) {ℓ d r₀ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hr₀ : 0 < r₀) (hRℓ : R0 ≤ ℓ * r₀)
    (hC : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₀ →
        1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))) := by
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hSnn : 0 ≤ Work.SmallBoxSliding.smallConvLower M := le_of_lt hSpos
  have hc0 : 0 ≤ 2 * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
      / Work.SmallBoxSliding.smallConvLower M :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Submission.BoseGases.chiSupAbs_nonneg)
      (Submission.BoseGases.chiSmallDecay_nonneg M)) hSnn
  -- ## the integrable dominating function
  have hdom : MeasureTheory.Integrable
      (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ z.1.2
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z.1.2 - z.1.1)
          * ((2 * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                / Work.SmallBoxSliding.smallConvLower M)
              * |Submission.BoseGases.g0 v h (z.1.2 - z.2)|))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
    integrable_dominator_wSmall1Pair_vol (v := v) (h := h) (R0 := R0) (M := M)
      hv_supp hR0 hM hℓ hc0
  -- ## the pointwise bound
  have hpb := abs_wSmall1Pair_le_r0 (v := v) (R0 := R0) (M := M) hv_supp hR0 h hM hℓ hd hR
    hr₀ hRℓ hC
  -- ## the `x`-factor is exactly `chiScale` times `chiSmall`
  have hfact : ∀ u x : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.chiSmallB M ℓ d u x|
        = Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) := by
    intro u x
    rw [Submission.BoseGases.chiSmallB,
      abs_of_nonneg (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
        (Submission.BoseGases.chiSmall_nonneg M _))]
  -- ## the `y`-factor is bounded by the decay constant
  have hyb : ∀ u y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.chiSmallB M ℓ d u y|
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    intro u y
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u y) ?_
    have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • y - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
    exact mul_le_mul_of_nonneg_left hb2 Submission.BoseGases.chiSupAbs_nonneg
  -- ## the a.e. domination of the kernel by the dominator
  have hbound : ∀ᵐ z ∂(((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
      ‖Submission.BoseGases.wSmall1Pair h M ℓ d z.1.1 z.1.2 z.2‖
        ≤ Submission.BoseGases.chiScale ℓ z.1.2
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z.1.2 - z.1.1)
          * ((2 * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                / Work.SmallBoxSliding.smallConvLower M)
              * |Submission.BoseGases.g0 v h (z.1.2 - z.2)|) := by
    filter_upwards with z
    rw [Real.norm_eq_abs]
    have hA0 : 0 ≤ 2 / Work.SmallBoxSliding.smallConvLower M
        * (Submission.BoseGases.chiScale ℓ z.1.2
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z.1.2 - z.1.1))
        * |Submission.BoseGases.g0 v h (z.1.2 - z.2)| :=
      mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hSnn)
        (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ z.1.2)
          (Submission.BoseGases.chiSmall_nonneg M _))) (abs_nonneg _)
    calc |Submission.BoseGases.wSmall1Pair h M ℓ d z.1.1 z.1.2 z.2|
        ≤ 2 / Work.SmallBoxSliding.smallConvLower M
            * |Submission.BoseGases.chiSmallB M ℓ d z.1.1 z.1.2|
            * |Submission.BoseGases.g0 v h (z.1.2 - z.2)|
            * |Submission.BoseGases.chiSmallB M ℓ d z.1.1 z.2| := hpb z.1.1 z.1.2 z.2
      _ ≤ 2 / Work.SmallBoxSliding.smallConvLower M
            * (Submission.BoseGases.chiScale ℓ z.1.2
                * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z.1.2 - z.1.1))
            * |Submission.BoseGases.g0 v h (z.1.2 - z.2)|
            * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) := by
          rw [hfact z.1.1 z.1.2]
          exact mul_le_mul le_rfl (hyb z.1.1 z.2) (abs_nonneg _) hA0
      _ = Submission.BoseGases.chiScale ℓ z.1.2
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z.1.2 - z.1.1)
            * ((2 * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                  / Work.SmallBoxSliding.smallConvLower M)
                * |Submission.BoseGases.g0 v h (z.1.2 - z.2)|) := by
          ring
  -- ## joint integrability in the `((u,x),y)` association
  have hmeas : AEStronglyMeasurable
      (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d z.1.1 z.1.2 z.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
    aestronglyMeasurable_wSmall1Pair_vol (v := v) (h := h) (M := M) hM ℓ d
  have hInt : MeasureTheory.Integrable
      (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d z.1.1 z.1.2 z.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
    Integrable.mono' hdom hmeas hbound
  -- ## transport along the associativity equivalence to the target association
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.prodAssoc :
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) ≃ᵐ
          EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, MeasureTheory.Measure.prodAssoc_prod⟩
  have hfun : ((fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2.1 p.2.2) ∘
        ⇑(MeasurableEquiv.prodAssoc :
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) ≃ᵐ
            EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))))
      = (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d z.1.1 z.1.2 z.2) := by
    funext z
    obtain ⟨⟨u, x⟩, y⟩ := z
    simp [MeasurableEquiv.prodAssoc]
  refine (hmp.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding
    (g := fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2.1 p.2.2)).mp ?_
  rw [hfun]
  exact hInt

end Work.BoseFixB1.WB
