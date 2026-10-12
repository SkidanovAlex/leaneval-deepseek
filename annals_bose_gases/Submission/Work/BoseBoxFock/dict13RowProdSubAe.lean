import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.dict13Aux3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13RowProdSubAe` — the additivity of the block-I row in the pair kernel

The `Q M Q` kernel `qmqKernel ℓ k` (`qmqDefs`) is **linear in `k`**:

    `qmqKernel ℓ (e₁ - e₂) = qmqKernel ℓ e₁ - qmqKernel ℓ e₂`

(the kernel is `k w y − ℓ⁻³∫_{Λ} k w · − ℓ⁻³∫_{Λ} k · y + ℓ⁻⁶∬_{Λ²} k`, and each of the three
averaging rows is additive by `integral_sub`), and `rowProd Θ A B · p` is the `ℂ`-linear
multiplication by the kernel value `K (x_{p.2}) y`, so

    `rowProd Θ A B (qmqKernel ℓ e₁) p z − rowProd Θ A B (qmqKernel ℓ e₂) p z
        = rowProd Θ A B (qmqKernel ℓ (e₁ − e₂)) p z`                                          `(†)`

holds *pointwise* whenever the three additive identities hold at the point `(x_{p.2}, y)`.

The point of the present lemma is that this holds **almost everywhere** for every pair of only
measurable pair kernels `e₁, e₂` with finite double `lintegral` over the cube — the hypotheses
under which `dict13_L1` works.  The additive identities need integrability of the *slices*
`y' ↦ e w y'` and `w' ↦ e w' y`:

* the row `w` is fixed at `x_{p.2}`; since `∫⁻ w, ∫⁻ y', ‖e w y'‖ₑ < ⊤`, the slice is integrable
  for a.e. `w`, and `x_{p.2}` lands in that full-measure set for a.e. configuration `x` (the
  projection `x ↦ x_{p.2}` of the box measure `Measure.pi (fun _ => volume ↾ acube ℓ)` is
  quasi-measure-preserving onto `volume ↾ acube ℓ`, `Measure.quasiMeasurePreserving_eval`);
* similarly for the row `y`, using the *swapped* double integral (Tonelli), transferred from
  `volume ↾ acube ℓ` to the ambient `volume` by `MeasureTheory.ae_imp_of_ae_restrict` (the
  ambient `y`-measure is unrestricted, and off the cube both sides of `(†)` vanish because
  `support Θ ⊆ abox n ℓ` forces `Θ` to vanish on every configuration whose `p.1`-coordinate is
  outside the cube);
* the constant row `∬ k` needs the two intdegrals over the *product* measure, which are finite by
  Tonelli, hence the iterated integrals are linear by `MeasureTheory.integral_sub` + Fubini.

Everything here is `sorry`-free.
-/

namespace Work.BoseBoxFock

open MeasureTheory

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X

set_option autoImplicit false

/-- The one-particle cube measure `volume ↾ acube ℓ`, as an `abbrev` so that the type-class
search sees through it. -/
abbrev cubeM (ℓ : ℝ) : Measure E3 :=
  (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)

/-! ## Fubini/integrability of the pair kernel -/

/-- The uncurried kernel is integrable on the product of two copies of the cube as soon as it is
measurable with finite iterated `lintegral`. -/
private lemma integrable_prod_uncurry {ℓ : ℝ} {e : E3 → E3 → ℝ}
    (hm : Measurable (Function.uncurry e))
    (hi : ∫⁻ a, ∫⁻ b, ‖e a b‖ₑ ∂(cubeM ℓ) ∂(cubeM ℓ) < ⊤) :
    Integrable (fun q : E3 × E3 => e q.1 q.2) ((cubeM ℓ).prod (cubeM ℓ)) := by
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  rw [MeasureTheory.lintegral_prod (fun q : E3 × E3 => ‖e q.1 q.2‖ₑ) hm.enorm.aemeasurable]
  exact hi

/-- For a.e. `w` the slice `y' ↦ e w y'` is integrable over the cube. -/
private lemma ae_slice_fst {ℓ : ℝ} {e : E3 → E3 → ℝ}
    (hm : Measurable (Function.uncurry e))
    (hi : ∫⁻ a, ∫⁻ b, ‖e a b‖ₑ ∂(cubeM ℓ) ∂(cubeM ℓ) < ⊤) :
    ∀ᵐ w ∂(cubeM ℓ), Integrable (fun y' => e w y') (cubeM ℓ) := by
  have hmeas : Measurable (fun w : E3 => ∫⁻ y', ‖e w y'‖ₑ ∂(cubeM ℓ)) :=
    hm.enorm.lintegral_prod_right
  have hlt : ∫⁻ w, (∫⁻ y', ‖e w y'‖ₑ ∂(cubeM ℓ)) ∂(cubeM ℓ) < ⊤ := hi
  filter_upwards [MeasureTheory.ae_lt_top hmeas (ne_of_lt hlt)] with w hw
  refine ⟨?_, ?_⟩
  · have h1 : Measurable (fun y' : E3 => (Function.uncurry e) (w, y')) :=
      hm.comp (by fun_prop)
    exact h1.aestronglyMeasurable
  · exact hw

/-- For a.e. `y` the slice `w' ↦ e w' y` is integrable over the cube (Tonelli swap). -/
private lemma ae_slice_snd {ℓ : ℝ} {e : E3 → E3 → ℝ}
    (hm : Measurable (Function.uncurry e))
    (hi : ∫⁻ a, ∫⁻ b, ‖e a b‖ₑ ∂(cubeM ℓ) ∂(cubeM ℓ) < ⊤) :
    ∀ᵐ y ∂(cubeM ℓ), Integrable (fun w' => e w' y) (cubeM ℓ) := by
  have hmeas : Measurable (fun y : E3 => ∫⁻ w', ‖e w' y‖ₑ ∂(cubeM ℓ)) :=
    hm.enorm.lintegral_prod_left
  have hswap : ∫⁻ y, (∫⁻ w', ‖e w' y‖ₑ ∂(cubeM ℓ)) ∂(cubeM ℓ) < ⊤ := by
    rw [← MeasureTheory.lintegral_lintegral_swap (f := fun w' y => ‖e w' y‖ₑ)
      hm.enorm.aemeasurable]
    exact hi
  filter_upwards [MeasureTheory.ae_lt_top hmeas (ne_of_lt hswap)] with y hy
  refine ⟨?_, ?_⟩
  · have h1 : Measurable (fun w' : E3 => (Function.uncurry e) (w', y)) :=
      hm.comp (by fun_prop)
    exact h1.aestronglyMeasurable
  · exact hy

/-! ## The pointwise additivity of the kernel -/

/-- **The real kernel is additive in the pair kernel**, pointwise, assuming integrability of the
two slices through `w` and `y` and of the uncurried kernels on the product of the cubes. -/
private lemma qmqKernelR_sub_eq {ℓ : ℝ} {e₁ e₂ : E3 → E3 → ℝ} {w y : E3}
    (hB₁ : Integrable (fun y' => e₁ w y') (cubeM ℓ))
    (hB₂ : Integrable (fun y' => e₂ w y') (cubeM ℓ))
    (hC₁ : Integrable (fun w' => e₁ w' y) (cubeM ℓ))
    (hC₂ : Integrable (fun w' => e₂ w' y) (cubeM ℓ))
    (hD₁ : Integrable (fun q : E3 × E3 => e₁ q.1 q.2) ((cubeM ℓ).prod (cubeM ℓ)))
    (hD₂ : Integrable (fun q : E3 × E3 => e₂ q.1 q.2) ((cubeM ℓ).prod (cubeM ℓ))) :
    qmqKernelR ℓ (fun a b => e₁ a b - e₂ a b) w y
      = qmqKernelR ℓ e₁ w y - qmqKernelR ℓ e₂ w y := by
  have hB : (∫ y' in Submission.BoseGases.acube ℓ, (e₁ w y' - e₂ w y'))
      = (∫ y' in Submission.BoseGases.acube ℓ, e₁ w y')
        - ∫ y' in Submission.BoseGases.acube ℓ, e₂ w y' := integral_sub hB₁ hB₂
  have hC : (∫ w' in Submission.BoseGases.acube ℓ, (e₁ w' y - e₂ w' y))
      = (∫ w' in Submission.BoseGases.acube ℓ, e₁ w' y)
        - ∫ w' in Submission.BoseGases.acube ℓ, e₂ w' y := integral_sub hC₁ hC₂
  have hD : (∫ w' in Submission.BoseGases.acube ℓ, ∫ y' in Submission.BoseGases.acube ℓ,
        (e₁ w' y' - e₂ w' y'))
      = (∫ w' in Submission.BoseGases.acube ℓ, ∫ y' in Submission.BoseGases.acube ℓ, e₁ w' y')
        - ∫ w' in Submission.BoseGases.acube ℓ, ∫ y' in Submission.BoseGases.acube ℓ,
            e₂ w' y' := by
    have h1 : (∫ w' in Submission.BoseGases.acube ℓ,
          ∫ y' in Submission.BoseGases.acube ℓ, e₁ w' y')
        = ∫ q : E3 × E3, e₁ q.1 q.2 ∂((cubeM ℓ).prod (cubeM ℓ)) :=
      (MeasureTheory.integral_prod (fun q : E3 × E3 => e₁ q.1 q.2) hD₁).symm
    have h2 : (∫ w' in Submission.BoseGases.acube ℓ,
          ∫ y' in Submission.BoseGases.acube ℓ, e₂ w' y')
        = ∫ q : E3 × E3, e₂ q.1 q.2 ∂((cubeM ℓ).prod (cubeM ℓ)) :=
      (MeasureTheory.integral_prod (fun q : E3 × E3 => e₂ q.1 q.2) hD₂).symm
    have h3 : (∫ w' in Submission.BoseGases.acube ℓ,
          ∫ y' in Submission.BoseGases.acube ℓ, (e₁ w' y' - e₂ w' y'))
        = ∫ q : E3 × E3, (e₁ q.1 q.2 - e₂ q.1 q.2) ∂((cubeM ℓ).prod (cubeM ℓ)) := by
      have := (MeasureTheory.integral_prod
        (fun q : E3 × E3 => e₁ q.1 q.2 - e₂ q.1 q.2) (hD₁.sub hD₂)).symm
      simpa using this
    rw [h1, h2, h3]
    exact integral_sub hD₁ hD₂
  simp only [qmqKernelR, hB, hC, hD]
  ring

/-- **The `Q M Q` kernel is additive in the pair kernel**, pointwise. -/
private lemma qmqKernel_sub_eq {ℓ : ℝ} {e₁ e₂ : E3 → E3 → ℝ} {w y : E3}
    (hB₁ : Integrable (fun y' => e₁ w y') (cubeM ℓ))
    (hB₂ : Integrable (fun y' => e₂ w y') (cubeM ℓ))
    (hC₁ : Integrable (fun w' => e₁ w' y) (cubeM ℓ))
    (hC₂ : Integrable (fun w' => e₂ w' y) (cubeM ℓ))
    (hD₁ : Integrable (fun q : E3 × E3 => e₁ q.1 q.2) ((cubeM ℓ).prod (cubeM ℓ)))
    (hD₂ : Integrable (fun q : E3 × E3 => e₂ q.1 q.2) ((cubeM ℓ).prod (cubeM ℓ))) :
    qmqKernel ℓ (fun a b => e₁ a b - e₂ a b) w y
      = qmqKernel ℓ e₁ w y - qmqKernel ℓ e₂ w y := by
  have hR := qmqKernelR_sub_eq hB₁ hB₂ hC₁ hC₂ hD₁ hD₂
  simp only [qmqKernel_eq_ofReal, hR, Complex.ofReal_sub]

/-! ## The row is additive in the kernel value -/

/-- `rowProd` is `ℂ`-linear in `K`, at the level of the *evaluated* kernel `K (x_{p.2}) y`. -/
private lemma rowProd_sub_of_eval {n : ℕ} (Θ : Xn n → ℂ) (A B : E3 → ℂ)
    (K₁ K₂ K : E3 → E3 → ℂ) (p : Fin n × Fin n) (z : Xn n × (E3 × E3))
    (h : K₁ (z.1 p.2) z.2.1 - K₂ (z.1 p.2) z.2.1 = K (z.1 p.2) z.2.1) :
    rowProd Θ A B K₁ p z - rowProd Θ A B K₂ p z = rowProd Θ A B K p z := by
  have h1 : rowProd Θ A B K₁ p z - rowProd Θ A B K₂ p z
      = star (Θ z.1) * A (z.1 p.1) * (K₁ (z.1 p.2) z.2.1 - K₂ (z.1 p.2) z.2.1)
          * star (B z.2.2)
          * Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2) := by
    simp only [rowProd, rowInt]
    ring
  have h2 : rowProd Θ A B K p z
      = star (Θ z.1) * A (z.1 p.1) * K (z.1 p.2) z.2.1 * star (B z.2.2)
          * Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2) := rfl
  rw [h1, h2, h]

/-- Off the cube in the `p.1`-slot both sides of the row identity vanish (the state is supported
in the box and the updated configuration has its `p.1`-coordinate equal to `z.2.1`). -/
private lemma rowProd_eq_zero_of_notMem {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ}
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) (A B : E3 → ℂ) (K : E3 → E3 → ℂ) (z : Xn n × (E3 × E3))
    (hy : z.2.1 ∉ Submission.BoseGases.acube ℓ) : rowProd Θ A B K p z = 0 := by
  have hcoord : (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2) p.1 = z.2.1 := by
    rw [Function.update_apply, if_neg hp, Function.update_apply, if_pos rfl]
  have hΘ0 : Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2) = 0 := by
    by_contra hne
    have hmem : Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2
        ∈ Submission.BoseGases.abox n ℓ := hΘs (Function.mem_support.mpr hne)
    exact hy (by rw [← hcoord]; exact (Submission.BoseGases.mem_abox_iff n ℓ _).mp hmem p.1)
  simp only [rowProd, rowInt, hΘ0, mul_zero]

/-! ## Almost-everywhere assembly -/

theorem dict13RowProdSubAe {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Submission.BoseGases.X n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    {e₁ e₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hm₁ : Measurable (Function.uncurry e₁)) (hm₂ : Measurable (Function.uncurry e₂))
    (hi₁ : ∫⁻ a, ∫⁻ b, ‖e₁ a b‖ₑ
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)) < ⊤)
    (hi₂ : ∫⁻ a, ∫⁻ b, ‖e₂ a b‖ₑ
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)) < ⊤) :
    (fun z : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Work.BoseBoxFock.rowProd Θ A B (Work.BoseBoxFock.qmqKernel ℓ e₁) p z
          - Work.BoseBoxFock.rowProd Θ A B (Work.BoseBoxFock.qmqKernel ℓ e₂) p z)
      =ᵐ[((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)).prod
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3))))]
    (fun z : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Work.BoseBoxFock.rowProd Θ A B
          (Work.BoseBoxFock.qmqKernel ℓ (fun a b => e₁ a b - e₂ a b)) p z) := by
  -- the a.e. slice integrability of the two kernels
  have hV₁ := ae_slice_fst hm₁ hi₁
  have hV₂ := ae_slice_fst hm₂ hi₂
  have hH₁ := ae_slice_snd hm₁ hi₁
  have hH₂ := ae_slice_snd hm₂ hi₂
  have hD₁ := integrable_prod_uncurry hm₁ hi₁
  have hD₂ := integrable_prod_uncurry hm₂ hi₂
  -- the two `Q M Q` corrections, as a conjunction of slice-integrability statements
  have hGV : ∀ᵐ w ∂(cubeM ℓ),
      Integrable (fun y' => e₁ w y') (cubeM ℓ) ∧ Integrable (fun y' => e₂ w y') (cubeM ℓ) :=
    hV₁.and hV₂
  have hGH : ∀ᵐ y ∂(cubeM ℓ),
      Integrable (fun w' => e₁ w' y) (cubeM ℓ) ∧ Integrable (fun w' => e₂ w' y) (cubeM ℓ) :=
    hH₁.and hH₂
  -- ... transferred to the ambient `y`-volume (off the cube both sides vanish)
  have hY : ∀ᵐ y ∂(volume : Measure E3),
      (y ∈ Submission.BoseGases.acube ℓ →
        (Integrable (fun w' => e₁ w' y) (cubeM ℓ)
          ∧ Integrable (fun w' => e₂ w' y) (cubeM ℓ))) :=
    MeasureTheory.ae_imp_of_ae_restrict hGH
  -- the same statements after the projections of the product measure
  have hX : ∀ᵐ z ∂((Measure.pi fun _ : Fin n => cubeM ℓ).prod
      ((volume : Measure E3).prod (volume : Measure E3))),
      Integrable (fun y' => e₁ (z.1 p.2) y') (cubeM ℓ)
        ∧ Integrable (fun y' => e₂ (z.1 p.2) y') (cubeM ℓ) :=
    MeasureTheory.Measure.quasiMeasurePreserving_fst.ae
      ((MeasureTheory.Measure.quasiMeasurePreserving_eval (μ := fun _ : Fin n => cubeM ℓ) p.2).ae
        hGV)
  have hZ : ∀ᵐ z ∂((Measure.pi fun _ : Fin n => cubeM ℓ).prod
      ((volume : Measure E3).prod (volume : Measure E3))),
      (z.2.1 ∈ Submission.BoseGases.acube ℓ →
        (Integrable (fun w' => e₁ w' z.2.1) (cubeM ℓ)
          ∧ Integrable (fun w' => e₂ w' z.2.1) (cubeM ℓ))) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst.comp
      MeasureTheory.Measure.quasiMeasurePreserving_snd).ae hY
  -- the pointwise identity, a.e.
  have hmain : (fun z : Xn n × (E3 × E3) =>
        rowProd Θ A B (qmqKernel ℓ e₁) p z - rowProd Θ A B (qmqKernel ℓ e₂) p z)
      =ᵐ[(Measure.pi fun _ : Fin n => cubeM ℓ).prod
          ((volume : Measure E3).prod (volume : Measure E3))]
      (fun z : Xn n × (E3 × E3) =>
        rowProd Θ A B (qmqKernel ℓ (fun a b => e₁ a b - e₂ a b)) p z) := by
    filter_upwards [hX, hZ] with z hzX hzZ
    by_cases hy : z.2.1 ∈ Submission.BoseGases.acube ℓ
    · -- the kernel is additive at `(z.1 p.2, z.2.1)`
      refine rowProd_sub_of_eval Θ A B (qmqKernel ℓ e₁) (qmqKernel ℓ e₂)
        (qmqKernel ℓ (fun a b => e₁ a b - e₂ a b)) p z ?_
      have hk := qmqKernel_sub_eq (e₁ := e₁) (e₂ := e₂) (ℓ := ℓ)
        (w := z.1 p.2) (y := z.2.1) hzX.1 hzX.2 (hzZ hy).1 (hzZ hy).2 hD₁ hD₂
      simpa [Pi.sub_apply] using hk.symm
    · -- off the cube both sides vanish
      rw [rowProd_eq_zero_of_notMem hΘs hp A B (qmqKernel ℓ e₁) z hy,
        rowProd_eq_zero_of_notMem hΘs hp A B (qmqKernel ℓ e₂) z hy,
        rowProd_eq_zero_of_notMem hΘs hp A B
          (qmqKernel ℓ (fun a b => e₁ a b - e₂ a b)) z hy]
      simp
  -- the box measure is the product of the per-particle cube measures
  rw [Submission.BoseGases.restrict_abox_eq_pi n ℓ]
  exact hmain

end

end Work.BoseBoxFock
