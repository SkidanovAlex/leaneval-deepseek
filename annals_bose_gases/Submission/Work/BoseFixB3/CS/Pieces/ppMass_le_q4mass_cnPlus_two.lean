import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.Pieces.CS_box_hyps_of_integrable
import Submission.Work.BoseFixB3.CS.Pieces.avgMass_case
import Submission.Work.BoseFixB3.CS.Pieces.omegaSqCoupl_eq
import Submission.Work.BoseFixB3.CS.Pieces.ppMass_two_eq
import Submission.Work.BoseFixB3.CS.Pieces.pp_sq_factor
import Submission.Work.BoseFixB3.CS.Pieces.twoSlotWeightedCS
import Submission.Work.BoseFixB3.CS.Pieces.v_w0_pos_sq
import Submission.Work.BoseFixB3.CS.Pieces.yMass_two_le_cnPlus
import Submission.Work.BoseFixR.CrudeWordLower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.ppMass_le_q4mass_cnPlus_two`

The `n = 2` instance of the `CS` congruence-step bound: for two particles the condensate pair
mass `ppMass ℓ Φ` is dominated by the `4Q`-square plus the fluctuation mass `cnPlus`.

## Mathematics (the `n = 2` collapse)

For `N = 2` the pair set is `{(0,1),(1,0)}` and `X := aP ℓ 0 (aP ℓ 1 Φ)` is *constant* on
`X 2` (`aP_pair_const_in_i/j`), with `∫_{abox 2 ℓ} X² = ℓ⁶X²`.  Hence

  `ppMass ℓ Φ = 2·X²`.                                                    (i)

Write `q4B_{(0,1)} = ω(x₀−x₁)·X + R` with `R := q4B_{(0,1)} − ω(x₀−x₁)·X`, `w := wLoc ℓ v 0`.
The pointwise algebraic identity (`Pieces.twoSlotPointwise`)

  `(ωm+g)²·w + 2λg² − 2λm²·ω²w/(w+2λ) = (w+2λ)(g + wωm/(w+2λ))² ≥ 0`

with `m := X`, `g := R`, `λ := ℓ⁻²`, integrated over the box, gives

  `2ℓ⁻²·X²·Ê ≤ D + 2ℓ⁻²·∫R²`,   `Ê := ∫_{abox} ω²w/(w+2ℓ⁻²)`,  `D := ∫_{abox} (q4B)²w ≤ q4Mass`.
                                                                            (ii)

The fluctuation part is bounded by the projection contractions, `∫R² ≤ 14·cnPlus`.

The remaining input is the *lower* bound for the coupling average `Ê`: writing `z := x₀−x₁`,
`w = χ(x₀)·(v z/(χ⋆χ)_ℓ z)·χ(x₁)` and `ω = ω₀(z)`, the exact kernel identity
(`Submission.BoseGases.kernel_double_integral`) turns `∫_{abox}ω²·χχ·φ/(c²φ+2ℓ⁻²)` into a
one-dimensional integral in `z`, and the elementary estimate

  `w/(w+2ℓ⁻²) ≥ χ(x₀)χ(x₁)·φ(z)/(c²φ(z)+2ℓ⁻²)`,   `φ := v/(χ⋆χ)_ℓ`,

with `c := (∫χ²)^{−1/2} ≥ χ` the sup of `χ`, yields

  `Ê ≥ (ℓ³/(2c²))·∫_{‖z‖≤R} ω(z)²·v(z)/(v(z) + 1/(c²ℓ²)) dz`.             (iii)

By `Pieces.avgMass_case` the last integral times `ℓ/2` is bounded below by a constant
`κ > 0` depending only on `v, R`, for every `ℓ ≥ ℓ_min := R/chiR0`; hence `Ê ≥ κℓ²/c²` and,
combining with (i)–(ii),

  `ppMass = 2X² ≤ (28c²/κ)·(q4Mass + ℓ⁻²·cnPlus)`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000

/-- The supremum of the corpus bump `χ`: `c := (∫χ²)^{−1/2}`; `χ ≤ c`. -/
private def cchi : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹

private lemma cchi_pos : 0 < cchi := by
  rw [cchi]
  exact inv_pos.mpr (Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos)

private lemma chiScale_le_cchi (ℓ : ℝ) (x : E3) :
    Submission.BoseGases.chiScale ℓ x ≤ cchi := by
  have h := Submission.BoseGases.chi_le_sqrt_inv ((ℓ⁻¹) • x)
  simpa [cchi, Submission.BoseGases.chiScale] using h

private lemma chiScale_nonneg' (ℓ : ℝ) (x : E3) :
    0 ≤ Submission.BoseGases.chiScale ℓ x := by
  simpa [Submission.BoseGases.chiScale] using Submission.BoseGases.chi_nonneg ((ℓ⁻¹) • x)

/-- **The condensate amplitude of a two-particle state is constant.**  For `N = 2` the
double projection `aP ℓ 0 (aP ℓ 1 Φ)` does not depend on the configuration. -/
private lemma aP_pair_const_two {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X 2 → ℝ}
    (hΦc : Continuous Φ) :
    ∀ x y : Submission.BoseGases.X 2,
      Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x
        = Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) y := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have h0 : ∀ (x : Submission.BoseGases.X 2) (z : E3),
      Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) (Function.update x 0 z)
        = Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x :=
    fun x z => Submission.BoseGases.aP_pair_const_in_i hℓ hne hΦc x z
  have h1 : ∀ (x : Submission.BoseGases.X 2) (z : E3),
      Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) (Function.update x 1 z)
        = Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x :=
    fun x z => Submission.BoseGases.aP_pair_const_in_j hℓ hne hΦc x z
  intro x y
  have hupd : Function.update (Function.update x 0 (y 0)) 1 (y 1) = y := by
    funext m
    fin_cases m <;> simp
  calc Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x
      = Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ)
          (Function.update x 0 (y 0)) := (h0 x (y 0)).symm
    _ = Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ)
          (Function.update (Function.update x 0 (y 0)) 1 (y 1)) :=
        (h1 (Function.update x 0 (y 0)) (y 1)).symm
    _ = Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) y := by rw [hupd]

/-- **The pointwise two-slot inequality** at a configuration `x`: with `m := aP ℓ 0 (aP ℓ 1 Φ) x`
(the condensate amplitude), `g := q4B_{(0,1)} − ω(x₀−x₁)·m` and `λ := ℓ⁻²`,

`2λ·m²·ω²w/(w+2λ) ≤ (q4B)²w + 2λ·g²`. -/
private lemma key_ptwise {ℓ : ℝ} (hℓ : 0 < ℓ) {v : E3 → ℝ} (hv : 0 ≤ v) {ω : E3 → ℝ}
    {Φ : Submission.BoseGases.X 2 → ℝ} (x : Submission.BoseGases.X 2) :
    2 * (ℓ ^ 2)⁻¹ * (Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x) ^ 2
        * (ω (x 0 - x 1)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
        / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹)
      ≤ (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (0, 1) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
        + 2 * (ℓ ^ 2)⁻¹ * (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (0, 1) x
            - ω (x 0 - x 1)
              * Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x) ^ 2 := by
  have hlam : 0 < (ℓ ^ 2)⁻¹ := by positivity
  have hw0 : 0 ≤ Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) :=
    Work.BoseFixR.wLoc_zero_nonneg hv ℓ _ _
  set W : ℝ := Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) with hW
  set m : ℝ := Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x with hm
  set D : ℝ := Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (0, 1) x with hD
  set g : ℝ := D - ω (x 0 - x 1) * m with hg
  have hident := twoSlotPointwise (ω (x 0 - x 1)) W g m ((ℓ ^ 2)⁻¹) hw0 hlam
  have homg : ω (x 0 - x 1) * m + g = D := by rw [hg]; ring
  have hsq : 0 ≤ (W + 2 * (ℓ ^ 2)⁻¹)
      * (g + W * (ω (x 0 - x 1) * m) / (W + 2 * (ℓ ^ 2)⁻¹)) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h1 : 2 * (ℓ ^ 2)⁻¹ * m ^ 2 * ((ω (x 0 - x 1)) ^ 2 * W / (W + 2 * (ℓ ^ 2)⁻¹))
      ≤ (ω (x 0 - x 1) * m + g) ^ 2 * W + 2 * (ℓ ^ 2)⁻¹ * g ^ 2 := by
    linarith [hident, hsq]
  rw [homg] at h1
  have h2 : 2 * (ℓ ^ 2)⁻¹ * m ^ 2 * ((ω (x 0 - x 1)) ^ 2 * W / (W + 2 * (ℓ ^ 2)⁻¹))
      = 2 * (ℓ ^ 2)⁻¹ * m ^ 2 * (ω (x 0 - x 1)) ^ 2 * W / (W + 2 * (ℓ ^ 2)⁻¹) := by ring
  rw [h2] at h1
  have e1 : 2 * (ℓ ^ 2)⁻¹ * (Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x) ^ 2
        * (ω (x 0 - x 1)) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
        / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹)
      = 2 * (ℓ ^ 2)⁻¹ * m ^ 2 * (ω (x 0 - x 1)) ^ 2 * W / (W + 2 * (ℓ ^ 2)⁻¹) := by
    rw [hm, hW]
  have e2 : D ^ 2 * W + 2 * (ℓ ^ 2)⁻¹ * g ^ 2
      = (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (0, 1) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
        + 2 * (ℓ ^ 2)⁻¹ * (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (0, 1) x
            - ω (x 0 - x 1)
              * Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x) ^ 2 := by
    rw [hD, hW, hg, hm]
  rw [e1, ← e2]
  exact h1

/-! ## The box-to-cube transfer for two particles -/

/-- `wLoc ℓ v 0 x y = χ(x)·W(x−y)·χ(y)` with `W := wScaled ℓ v`. -/
private lemma wLoc_eq_chi_mul (ℓ : ℝ) (v : E3 → ℝ) (x y : E3) :
    Submission.BoseGases.wLoc ℓ v 0 x y
      = Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.wScaled ℓ v (x - y)
        * Submission.BoseGases.chiScale ℓ y := by
  simp [Submission.BoseGases.wLoc, Submission.BoseGases.chiU, Submission.BoseGases.chiScale]

/-- `(χ⋆χ)_ℓ (x−y) · (v(x−y)/(χ⋆χ)_ℓ(x−y)) = v(x−y)` in the dilute régime. -/
private lemma convScale_mul_wScaled {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {v : E3 → ℝ}
    (hv_supp : ∀ z : E3, R ≤ ‖z‖ → v z = 0) (z : E3) :
    Submission.BoseGases.convScale ℓ z * Submission.BoseGases.wScaled ℓ v z = v z := by
  rw [Submission.BoseGases.wScaled]
  by_cases hz : ‖z‖ ≤ R
  · have hge := Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hz
    have hne : Submission.BoseGases.convScale ℓ z ≠ 0 := by linarith
    field_simp
  · have hz' : R ≤ ‖z‖ := le_of_lt (not_le.mp hz)
    rw [hv_supp z hz']
    simp

/-- **The two-particle box integral is a double cube integral.** -/
private lemma integral_abox_two {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {G : E3 × E3 → ℝ}
    (hG : MeasureTheory.Integrable G
      (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))) :
    ∫ x in Submission.BoseGases.abox 2 ℓ, G (x 0, x 1)
      = ∫ a in Submission.BoseGases.acube ℓ,
          ∫ b in Submission.BoseGases.acube ℓ, G (a, b) := by
  rw [Submission.BoseGases.restrict_abox_eq_pi]
  calc ∫ x : Fin 2 → E3, G (x 0, x 1)
        ∂(Measure.pi fun _ : Fin 2 => (MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      = ∫ p : E3 × E3, G p
          ∂(((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
        have hmp := MeasureTheory.measurePreserving_finTwoArrow
          ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        have hcomp := hmp.integral_comp (MeasurableEquiv.measurableEmbedding _) G
        simpa [Function.comp, MeasurableEquiv.finTwoArrow_apply] using hcomp
    _ = ∫ a : E3, ∫ b : E3, G (a, b)
          ∂((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
          ∂((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
        MeasureTheory.integral_prod G hG

/-- **The coupling average is bounded below by a one-dimensional average.**  With
`φ := v/(χ⋆χ)_ℓ` and `c := (∫χ²)^{−1/2} ≥ χ`,

`Ê ≥ (ℓ³/(2c²))·∫_{‖z‖≤R} ω(z)²·v(z)/(v(z) + 1/(c²ℓ²)) dz`. -/
private lemma crux_estimate {v ω : E3 → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hv : 0 ≤ v) (hv_int : MeasureTheory.Integrable v)
    (hv_supp : ∀ z : E3, R ≤ ‖z‖ → v z = 0)
    (hωli : MeasureTheory.LocallyIntegrable ω MeasureTheory.volume)
    (hω0 : ∀ᵐ z ∂(MeasureTheory.volume : Measure E3), 0 ≤ ω z)
    (hω1 : ∀ᵐ z ∂(MeasureTheory.volume : Measure E3), ω z ≤ 1) :
    (ℓ ^ 3 / (2 * cchi ^ 2))
        * ∫ z in Metric.ball (0 : E3) R, (ω z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2)))
      ≤ ∫ x in Submission.BoseGases.abox 2 ℓ,
          (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
            / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹)) := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have hcchi : 0 < cchi := cchi_pos
  have hωaem : AEMeasurable ω MeasureTheory.volume := hωli.aestronglyMeasurable.aemeasurable
  set lam : ℝ := (ℓ ^ 2)⁻¹ with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  set φ : E3 → ℝ := fun z => v z / Submission.BoseGases.convScale ℓ z with hφdef
  have hφnn : ∀ z, 0 ≤ φ z := fun z => by
    rw [show φ z = v z / Submission.BoseGases.convScale ℓ z from rfl]
    exact div_nonneg (hv z) (Submission.BoseGases.convScale_nonneg ℓ z)
  have hconvcont : Continuous (fun z : E3 => Submission.BoseGases.convScale ℓ z) := by
    have h1 : Continuous (fun z : E3 => (ℓ⁻¹) • z) := by fun_prop
    exact Submission.BoseGases.conv_contDiff.continuous.comp h1
  have hφaem : AEMeasurable φ MeasureTheory.volume := by
    rw [hφdef]
    exact hv_int.aestronglyMeasurable.aemeasurable.div hconvcont.aemeasurable
  have hdenpos : ∀ z, 0 < cchi ^ 2 * φ z + 2 * lam := fun z => by
    have := hφnn z
    nlinarith [sq_nonneg cchi, le_of_lt hlam]
  set h : E3 → ℝ := fun z => (ω z) ^ 2 * (v z / (cchi ^ 2 * φ z + 2 * lam)) with hhdef
  have hh_eq : ∀ z, h z = (ω z) ^ 2 * (v z / (cchi ^ 2 * φ z + 2 * lam)) := fun z => rfl
  have hhnn : ∀ z, 0 ≤ h z := fun z => by
    rw [hh_eq z]
    exact mul_nonneg (sq_nonneg _) (div_nonneg (hv z) (le_of_lt (hdenpos z)))
  have h_int : MeasureTheory.Integrable h := by
    refine MeasureTheory.Integrable.mono' (hv_int.const_mul ((2 * lam)⁻¹)) ?_ ?_
    · rw [hhdef]
      have h2 : AEMeasurable (fun z : E3 => ω z * ω z * (v z / (cchi ^ 2 * φ z + 2 * lam)))
          MeasureTheory.volume :=
        (hωaem.mul hωaem).mul
          (hv_int.aestronglyMeasurable.aemeasurable.div
            (AEMeasurable.add (hφaem.const_mul (cchi ^ 2)) aemeasurable_const))
      have h3 : (fun z : E3 => ω z ^ 2 * (v z / (cchi ^ 2 * φ z + 2 * lam)))
          = fun z : E3 => ω z * ω z * (v z / (cchi ^ 2 * φ z + 2 * lam)) := by
        funext z; ring
      rw [h3]
      exact h2.aestronglyMeasurable
    · filter_upwards [hω0, hω1] with z hz0 hz1
      have hb0 : 0 ≤ v z / (cchi ^ 2 * φ z + 2 * lam) := div_nonneg (hv z) (le_of_lt (hdenpos z))
      have hω2 : (ω z) ^ 2 ≤ 1 := by nlinarith
      have h1 : v z / (cchi ^ 2 * φ z + 2 * lam) ≤ v z / (2 * lam) :=
        div_le_div_of_nonneg_left (hv z) (by linarith)
          (by have := hφnn z; nlinarith [sq_nonneg cchi])
      rw [Real.norm_eq_abs, abs_of_nonneg (hhnn z), hh_eq z]
      calc (ω z) ^ 2 * (v z / (cchi ^ 2 * φ z + 2 * lam))
          ≤ 1 * (v z / (2 * lam)) := mul_le_mul hω2 h1 hb0 (by norm_num)
        _ = (2 * lam)⁻¹ * v z := by rw [one_mul, div_eq_inv_mul]
  have h_hsupp : ∀ z : E3, R ≤ ‖z‖ → h z = 0 := fun z hz => by
    rw [hh_eq z, hv_supp z hz]
    simp
  have hker := Submission.BoseGases.kernel_double_integral h hℓ h_int h_hsupp
    Submission.BoseGases.chiR0_pos hRℓ (fun x hx => Submission.BoseGases.chiR0_half x hx)
  have hval : ∀ z : E3, Submission.BoseGases.convScale ℓ z * φ z = v z := fun z => by
    have h0 : φ z = Submission.BoseGases.wScaled ℓ v z := rfl
    rw [h0]
    exact convScale_mul_wScaled hℓ hR hRℓ hv_supp z
  have hPsi_eq : ∀ z : E3, h z / Submission.BoseGases.convScale ℓ z
      = (ω z) ^ 2 * (φ z / (cchi ^ 2 * φ z + 2 * lam)) := by
    intro z
    rw [hh_eq z]
    by_cases hC : Submission.BoseGases.convScale ℓ z = 0
    · have hvz : v z = 0 := by rw [← hval z, hC, zero_mul]
      have hφz : φ z = 0 := by
        rw [show φ z = v z / Submission.BoseGases.convScale ℓ z from rfl, hvz]
        simp
      rw [hC, hφz]
      simp
    · rw [← hval z]
      field_simp
      try ring
  -- the pointwise comparison with `ω²·w/(w+2λ)`
  have hpt : ∀ x : Submission.BoseGases.X 2,
      (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.chiScale ℓ (x 0)
          * Submission.BoseGases.chiScale ℓ (x 1)
          * (φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam)))
        ≤ (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
            / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)) := by
    intro x
    have hχ0 := chiScale_nonneg' ℓ (x 0)
    have hχ1 := chiScale_nonneg' ℓ (x 1)
    have hχ0' := chiScale_le_cchi ℓ (x 0)
    have hχ1' := chiScale_le_cchi ℓ (x 1)
    have hwnn := Work.BoseFixR.wLoc_zero_nonneg hv ℓ (x 0) (x 1)
    have hwphi : Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
        = Submission.BoseGases.chiScale ℓ (x 0) * φ (x 0 - x 1)
          * Submission.BoseGases.chiScale ℓ (x 1) := by
      rw [wLoc_eq_chi_mul]
      rfl
    have hu : (0 : ℝ) ≤ Submission.BoseGases.chiScale ℓ (x 0)
        * Submission.BoseGases.chiScale ℓ (x 1) := mul_nonneg hχ0 hχ1
    have husq : Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1)
        ≤ cchi ^ 2 := by
      have h := mul_le_mul hχ0' hχ1' hχ1 (le_of_lt hcchi)
      simpa [pow_two] using h
    have hφ' : 0 ≤ φ (x 0 - x 1) := hφnn _
    have ht : Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
        = (Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1))
          * φ (x 0 - x 1) := by
      rw [hwphi]; ring
    have hkey : φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam)
          * Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1)
        ≤ Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
            / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam) := by
      have hnum : (0 : ℝ) ≤ (Submission.BoseGases.chiScale ℓ (x 0)
          * Submission.BoseGases.chiScale ℓ (x 1)) * φ (x 0 - x 1) := mul_nonneg hu hφ'
      have hden2 : 0 < (Submission.BoseGases.chiScale ℓ (x 0)
          * Submission.BoseGases.chiScale ℓ (x 1)) * φ (x 0 - x 1) + 2 * lam := by linarith
      have hmain : (Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1))
              * φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam)
          ≤ (Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1))
              * φ (x 0 - x 1)
            / ((Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1))
              * φ (x 0 - x 1) + 2 * lam) := by
        refine div_le_div_of_nonneg_left hnum hden2 ?_
        have h2 := mul_le_mul_of_nonneg_right husq hφ'
        linarith
      have e1 : φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam)
            * Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1)
          = (Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1))
              * φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam) := by
        field_simp
        try ring
      have e2 : Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
              / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)
          = (Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1))
              * φ (x 0 - x 1)
            / ((Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1))
              * φ (x 0 - x 1) + 2 * lam) := by
        rw [ht]
      rw [e1, e2]
      exact hmain
    calc (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.chiScale ℓ (x 0)
            * Submission.BoseGases.chiScale ℓ (x 1)
            * (φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam)))
        = (ω (x 0 - x 1)) ^ 2 * (φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam)
            * Submission.BoseGases.chiScale ℓ (x 0) * Submission.BoseGases.chiScale ℓ (x 1)) := by
          ring
      _ ≤ (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
            / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)) :=
          mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
  -- integrability facts on the box
  have hW_int : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X 2 => Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) := by
    have hw : MeasureTheory.Integrable
        (fun z : E3 × E3 => Submission.BoseGases.wLoc ℓ v 0 z.1 z.2) := by
      have h0 := Submission.BoseGases.integrable_wPairU_full hℓ hv_int hv_supp hRℓ
      have h1 : (fun z : E3 × E3 => Submission.BoseGases.wLoc ℓ v 0 z.1 z.2)
          = Submission.BoseGases.wPairU ℓ v := by
        funext z
        simp only [Submission.BoseGases.wPairU, Function.uncurry, wLoc_zero_eq_wPair']
      rw [h1]
      exact h0
    exact pair_coord_integrable hℓ hne hw
  have hωsm : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X 2 => ω (x 0 - x 1))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
    Submission.BoseGases.w0_diff_aem hℓ hne hωli
  have hωbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)),
      |ω (x 0 - x 1)| ≤ 1 := by
    have hconj : ∀ᵐ z : E3, |ω z| ≤ 1 := by
      filter_upwards [hω0, hω1] with z hz0 hz1
      rw [abs_of_nonneg hz0]; exact hz1
    exact Submission.BoseGases.ae_pair_pullback hℓ hne hconj
  have hInt_om2w : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X 2 => (ω (x 0 - x 1)) ^ 2
        * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) := by
    refine (Submission.BoseGases.integrableOn_bounded_mul_wPair_sub_abox hℓ hv_int hv_supp hRℓ
      0 1 hne (hωsm.pow 2) (B := 1) (by norm_num) ?_).congr ?_
    · filter_upwards [hωbnd] with x hx
      have hsq : (ω (x 0 - x 1)) ^ 2 ≤ 1 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (ω (x 0 - x 1)), hx]
      simpa only [Pi.pow_apply, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (ω (x 0 - x 1)))] using hsq
    · filter_upwards with x
      simp only [← wLoc_zero_eq_wPair', Pi.pow_apply]
  have hWdiv_int : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X 2 => (ω (x 0 - x 1)) ^ 2
        * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
            / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) := by
    refine MeasureTheory.Integrable.mono' (hInt_om2w.const_mul ((2 * lam)⁻¹)) ?_ ?_
    · have hratio : MeasureTheory.AEStronglyMeasurable
          (fun x : Submission.BoseGases.X 2 => Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
            / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam))
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
        (hW_int.aestronglyMeasurable.aemeasurable.div
          (AEMeasurable.add hW_int.aestronglyMeasurable.aemeasurable
            aemeasurable_const)).aestronglyMeasurable
      have h2 : MeasureTheory.AEStronglyMeasurable
          (fun x : Submission.BoseGases.X 2 => ω (x 0 - x 1) * ω (x 0 - x 1)
            * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
              / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)))
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
        (hωsm.mul hωsm).mul hratio
      have h3 : (fun x : Submission.BoseGases.X 2 => (ω (x 0 - x 1)) ^ 2
            * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
              / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)))
          = fun x : Submission.BoseGases.X 2 => ω (x 0 - x 1) * ω (x 0 - x 1)
            * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
              / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)) := by
        funext x; ring
      rw [h3]
      exact h2
    · filter_upwards with x
      have hwnn := Work.BoseFixR.wLoc_zero_nonneg hv ℓ (x 0) (x 1)
      have hω2 : 0 ≤ (ω (x 0 - x 1)) ^ 2 := sq_nonneg _
      have hden : 0 < Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam := by linarith
      have h2lam : 0 < 2 * lam := by linarith
      have hle : Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
          / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)
          ≤ (2 * lam)⁻¹ * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) := by
        rw [div_le_iff₀ hden]
        have hconv : (2 * lam)⁻¹ * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
              * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)
            = Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
              * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam) / (2 * lam) := by
          rw [div_eq_inv_mul]; ring
        rw [hconv, le_div_iff₀ h2lam]
        nlinarith [hwnn]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hω2 (div_nonneg hwnn (le_of_lt hden)))]
      calc (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
            / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam))
          ≤ (ω (x 0 - x 1)) ^ 2
              * ((2 * lam)⁻¹ * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)) :=
            mul_le_mul_of_nonneg_left hle hω2
        _ = (2 * lam)⁻¹ * ((ω (x 0 - x 1)) ^ 2
              * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)) := by ring
  -- integrability of `G (a,b) = ω²·χχ·φ/(c²φ+2λ)` on the square of cube measures
  have hbase : MeasureTheory.Integrable
      (fun p : E3 × E3 => (ω (p.1 - p.2)) ^ 2 * Submission.BoseGases.wPair ℓ v p.1 p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hsm : MeasureTheory.AEStronglyMeasurable
        (Function.uncurry fun a b : E3 => (ω (a - b)) ^ 2)
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
      have h1 : MeasureTheory.AEStronglyMeasurable (fun p : E3 × E3 => (ω (p.1 - p.2)) ^ 2)
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        (aestronglyMeasurable_sub_prod hωli).pow 2
      have heq : (Function.uncurry fun a b : E3 => (ω (a - b)) ^ 2)
          = fun p : E3 × E3 => (ω (p.1 - p.2)) ^ 2 := rfl
      rw [heq]
      exact h1
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.prod MeasureTheory.volume),
        ‖(fun a b : E3 => (ω (a - b)) ^ 2) z.1 z.2‖ ≤ 1 := by
      filter_upwards [ae_prod_sub_of_ae hω0, ae_prod_sub_of_ae hω1] with z hz0 hz1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith
    exact integrable_prod_wPair_mul_bounded hℓ hv_int hv_supp hRℓ hsm (by norm_num) hb
  have hbase' : MeasureTheory.Integrable
      (fun p : E3 × E3 => (ω (p.1 - p.2)) ^ 2 * Submission.BoseGases.wPair ℓ v p.1 p.2)
      (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    hbase.mono_measure (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  have hχcont : Continuous (fun x : E3 => Submission.BoseGases.chiScale ℓ x) :=
    Submission.BoseGases.chi_contDiff.continuous.comp (by fun_prop)
  have hG_int : MeasureTheory.Integrable
      (fun p : E3 × E3 => (ω (p.1 - p.2)) ^ 2
        * (Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2
            * (φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam))))
      (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
    refine MeasureTheory.Integrable.mono' (hbase'.const_mul ((2 * lam)⁻¹)) ?_ ?_
    · -- measurability
      have hω2' : MeasureTheory.AEStronglyMeasurable
          (fun p : E3 × E3 => (ω (p.1 - p.2)) ^ 2)
          (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
        ((aestronglyMeasurable_sub_prod hωli).pow 2).mono_measure
          (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
      have hχ1' : MeasureTheory.AEStronglyMeasurable
          (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.1)
          (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
        (hχcont.comp continuous_fst).aestronglyMeasurable
      have hχ2' : MeasureTheory.AEStronglyMeasurable
          (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.2)
          (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
        (hχcont.comp continuous_snd).aestronglyMeasurable
      have hψ' : MeasureTheory.AEStronglyMeasurable
          (fun p : E3 × E3 => φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam))
          (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
        have hφp : MeasureTheory.AEStronglyMeasurable
            (fun p : E3 × E3 => φ (p.1 - p.2))
            (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
              ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
          have hv' : AEMeasurable (fun p : E3 × E3 => v (p.1 - p.2))
              (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
                ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
            ((aestronglyMeasurable_sub_prod hv_int.locallyIntegrable).mono_measure
              (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)).aemeasurable
          have hcv' : AEMeasurable (fun p : E3 × E3 =>
              Submission.BoseGases.convScale ℓ (p.1 - p.2))
              (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
                ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
            ((hconvcont.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).aemeasurable
          have hll := hv'.div hcv'
          have hfun : (fun p : E3 × E3 => φ (p.1 - p.2)) = (fun p : E3 × E3 =>
              v (p.1 - p.2) / Submission.BoseGases.convScale ℓ (p.1 - p.2)) := by
            funext p
            rw [show φ (p.1 - p.2) = v (p.1 - p.2) / Submission.BoseGases.convScale ℓ (p.1 - p.2)
              from rfl]
          rw [hfun]
          exact hll.aestronglyMeasurable
        have hden : AEMeasurable (fun p : E3 × E3 =>
            cchi ^ 2 * φ (p.1 - p.2) + 2 * lam)
            (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
              ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
          (AEMeasurable.add (hφp.aemeasurable.const_mul (cchi ^ 2)) aemeasurable_const)
        exact (hφp.aemeasurable.div hden).aestronglyMeasurable
      have hll := hω2'.mul ((hχ1'.mul hχ2').mul hψ')
      have hshape : (fun p : E3 × E3 => (ω (p.1 - p.2)) ^ 2
            * (Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2
              * (φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam))))
          = (fun p : E3 × E3 => (ω (p.1 - p.2)) ^ 2)
            * (((fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.1)
                * (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.2))
              * (fun p : E3 × E3 => φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam))) := by
        funext p; simp only [Pi.mul_apply]; try ring
      rw [hshape]
      exact hll
    · filter_upwards with p
      have hχ0 := chiScale_nonneg' ℓ p.1
      have hχ1 := chiScale_nonneg' ℓ p.2
      have hφp : 0 ≤ φ (p.1 - p.2) := hφnn _
      have hden : 0 < cchi ^ 2 * φ (p.1 - p.2) + 2 * lam := hdenpos _
      have hwphi : Submission.BoseGases.wPair ℓ v p.1 p.2
          = Submission.BoseGases.chiScale ℓ p.1 * φ (p.1 - p.2)
            * Submission.BoseGases.chiScale ℓ p.2 := by
        rw [← wLoc_zero_eq_wPair', wLoc_eq_chi_mul]
        rfl
      have hPsnn : 0 ≤ φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam) :=
        div_nonneg hφp (le_of_lt hden)
      have hle : Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2
            * (φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam))
          ≤ (2 * lam)⁻¹ * (Submission.BoseGases.chiScale ℓ p.1 * φ (p.1 - p.2)
              * Submission.BoseGases.chiScale ℓ p.2) := by
        have hu : 0 ≤ Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2 :=
          mul_nonneg hχ0 hχ1
        have hnum : 0 ≤ (Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2)
            * φ (p.1 - p.2) := mul_nonneg hu hφp
        have h2le : 2 * lam ≤ cchi ^ 2 * φ (p.1 - p.2) + 2 * lam := by
          have := mul_nonneg (sq_nonneg cchi) hφp; linarith
        have h2lam : 0 < 2 * lam := by linarith
        have hstep : (Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2)
              * φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam)
            ≤ (Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2)
              * φ (p.1 - p.2) / (2 * lam) :=
          div_le_div_of_nonneg_left hnum h2lam h2le
        calc Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2
              * (φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam))
            = (Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2)
              * φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam) := by ring
          _ ≤ (Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2)
              * φ (p.1 - p.2) / (2 * lam) := hstep
          _ = (2 * lam)⁻¹ * (Submission.BoseGases.chiScale ℓ p.1 * φ (p.1 - p.2)
              * Submission.BoseGases.chiScale ℓ p.2) := by rw [div_eq_inv_mul]; ring
      have hGnn : 0 ≤ (ω (p.1 - p.2)) ^ 2
          * (Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2
              * (φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam))) :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hχ0 hχ1) hPsnn)
      rw [Real.norm_eq_abs, abs_of_nonneg hGnn]
      calc (ω (p.1 - p.2)) ^ 2
            * (Submission.BoseGases.chiScale ℓ p.1 * Submission.BoseGases.chiScale ℓ p.2
                * (φ (p.1 - p.2) / (cchi ^ 2 * φ (p.1 - p.2) + 2 * lam)))
          ≤ (ω (p.1 - p.2)) ^ 2
              * ((2 * lam)⁻¹ * (Submission.BoseGases.chiScale ℓ p.1 * φ (p.1 - p.2)
                  * Submission.BoseGases.chiScale ℓ p.2)) :=
            mul_le_mul_of_nonneg_left hle (sq_nonneg _)
        _ = (2 * lam)⁻¹ * ((ω (p.1 - p.2)) ^ 2 * Submission.BoseGases.wPair ℓ v p.1 p.2) := by
            rw [hwphi]; ring
  -- the box integral of `ω²χχ·φ/(c²φ+2λ)`
  have hboxG : ∫ x in Submission.BoseGases.abox 2 ℓ,
        (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.chiScale ℓ (x 0)
          * Submission.BoseGases.chiScale ℓ (x 1)
          * (φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam)))
      = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
          (ω (a - b)) ^ 2 * (Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b
            * (φ (a - b) / (cchi ^ 2 * φ (a - b) + 2 * lam))) :=
    integral_abox_two hℓ.le hG_int
  have hK : ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
        (ω (a - b)) ^ 2 * (Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b
          * (φ (a - b) / (cchi ^ 2 * φ (a - b) + 2 * lam)))
      = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b
            * (h (a - b) / Submission.BoseGases.convScale ℓ (a - b)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with a
    apply MeasureTheory.integral_congr_ae
    filter_upwards with b
    rw [hPsi_eq (a - b)]
    ring
  have hinner : ∀ a : E3, (∫ b in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b
          * (h (a - b) / Submission.BoseGases.convScale ℓ (a - b)))
      = ∫ b : E3, Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b
          * (h (a - b) / Submission.BoseGases.convScale ℓ (a - b)) := by
    intro a
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro b hb
    rw [chiScale_eq_zero_of_notMem_acube hℓ hb]
    ring
  have houter : (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b
          * (h (a - b) / Submission.BoseGases.convScale ℓ (a - b)))
      = ∫ a : E3, ∫ b : E3, Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b
          * (h (a - b) / Submission.BoseGases.convScale ℓ (a - b)) := by
    have step : (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b
          * (h (a - b) / Submission.BoseGases.convScale ℓ (a - b)))
        = ∫ a in Submission.BoseGases.acube ℓ, ∫ b : E3,
            Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b
              * (h (a - b) / Submission.BoseGases.convScale ℓ (a - b)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with a
      exact hinner a
    rw [step]
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro a ha
    have hχa : Submission.BoseGases.chiScale ℓ a = 0 := chiScale_eq_zero_of_notMem_acube hℓ ha
    simp [hχa]
  -- the pointwise comparison with the `v/(v+1/(c²ℓ²))`-integrand
  have hφle : ∀ z : E3, φ z ≤ 2 * v z := by
    intro z
    by_cases hz : ‖z‖ ≤ R
    · have hge := Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hz
      rw [show φ z = v z / Submission.BoseGases.convScale ℓ z from rfl]
      have hpos : 0 < Submission.BoseGases.convScale ℓ z := by linarith
      rw [div_le_iff₀ hpos]
      have h2 : 1 ≤ 2 * Submission.BoseGases.convScale ℓ z := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h2 (hv z)]
    · have hz' : R ≤ ‖z‖ := le_of_lt (not_le.mp hz)
      have hvz : v z = 0 := hv_supp z hz'
      have hφz : φ z = 0 := by
        rw [show φ z = v z / Submission.BoseGases.convScale ℓ z from rfl, hvz]
        simp
      rw [hφz, hvz]
      norm_num
  have hh_ge : (1 / (2 * cchi ^ 2)) * ∫ z : E3, (ω z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2)))
      ≤ ∫ z : E3, h z := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ h_int ?_
    · filter_upwards with z
      have h1 : 0 < cchi ^ 2 * ℓ ^ 2 := mul_pos (pow_pos hcchi 2) (pow_pos hℓ 2)
      have h2 : 0 < 1 / (cchi ^ 2 * ℓ ^ 2) := one_div_pos.mpr h1
      have hden : 0 ≤ v z + 1 / (cchi ^ 2 * ℓ ^ 2) :=
        add_nonneg (hv z) (le_of_lt h2)
      have h3 : 0 ≤ 1 / (2 * cchi ^ 2) := by
        have : 0 < 2 * cchi ^ 2 := by positivity
        exact le_of_lt (one_div_pos.mpr this)
      exact mul_nonneg h3
        (mul_nonneg (sq_nonneg _) (div_nonneg (hv z) hden))
    · filter_upwards with z
      have h1 : 0 < cchi ^ 2 * ℓ ^ 2 := mul_pos (pow_pos hcchi 2) (pow_pos hℓ 2)
      have h2 : 0 < 1 / (cchi ^ 2 * ℓ ^ 2) := one_div_pos.mpr h1
      have hlamc : 1 / (cchi ^ 2 * ℓ ^ 2) = lam / cchi ^ 2 := by
        rw [hlamdef]; ring
      have hmain : (1 / (2 * cchi ^ 2)) * (v z / (v z + lam / cchi ^ 2))
          ≤ v z / (cchi ^ 2 * φ z + 2 * lam) := by
        rcases eq_or_lt_of_le (hv z) with hv0 | hvpos
        · rw [← hv0]; simp
        · have h2' : cchi ^ 2 * φ z ≤ 2 * cchi ^ 2 * v z := by
            have := hφle z; nlinarith [sq_nonneg cchi]
          have h1' : (1 / (2 * cchi ^ 2)) * (v z / (v z + lam / cchi ^ 2))
              = v z / (2 * cchi ^ 2 * v z + 2 * lam) := by
            field_simp
            try ring
          rw [h1']
          have h2'' : cchi ^ 2 * φ z + 2 * lam ≤ 2 * cchi ^ 2 * v z + 2 * lam := by linarith
          exact div_le_div_of_nonneg_left (le_of_lt hvpos) (hdenpos z) h2''
      calc (1 / (2 * cchi ^ 2)) * ((ω z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2))))
          = (ω z) ^ 2 * ((1 / (2 * cchi ^ 2)) * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2)))) := by ring
        _ = (ω z) ^ 2 * ((1 / (2 * cchi ^ 2)) * (v z / (v z + lam / cchi ^ 2))) := by rw [hlamc]
        _ ≤ (ω z) ^ 2 * (v z / (cchi ^ 2 * φ z + 2 * lam)) :=
            mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
        _ = h z := by rw [hh_eq z]
  have hball : (∫ z : E3, (ω z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2))))
      = ∫ z in Metric.ball (0 : E3) R, (ω z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2))) := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball (0 : E3) R)
      (f := fun z => (ω z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2))))]
    intro z hz
    have hz' : R ≤ ‖z‖ := by
      rw [Metric.mem_ball, not_lt] at hz
      simpa [dist_eq_norm] using hz
    rw [hv_supp z hz']
    simp
  have hchain1 : ∫ x in Submission.BoseGases.abox 2 ℓ,
        (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.chiScale ℓ (x 0)
          * Submission.BoseGases.chiScale ℓ (x 1)
          * (φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam)))
      = ℓ ^ 3 * ∫ z : E3, h z := by
    rw [hboxG, hK, houter, hker]
  have hGnn' : ∀ x : Submission.BoseGases.X 2,
      0 ≤ (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.chiScale ℓ (x 0)
          * Submission.BoseGases.chiScale ℓ (x 1)
          * (φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam))) := by
    intro x
    refine mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (chiScale_nonneg' ℓ (x 0))
      (chiScale_nonneg' ℓ (x 1))) (div_nonneg (hφnn _) (le_of_lt (hdenpos _))))
  have hupper : ∫ x in Submission.BoseGases.abox 2 ℓ,
        (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.chiScale ℓ (x 0)
          * Submission.BoseGases.chiScale ℓ (x 1)
          * (φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam)))
      ≤ ∫ x in Submission.BoseGases.abox 2 ℓ,
          (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
            / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hWdiv_int ?_
    · filter_upwards with x using hGnn' x
    · filter_upwards with x using hpt x
  calc (ℓ ^ 3 / (2 * cchi ^ 2))
        * ∫ z in Metric.ball (0 : E3) R, (ω z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2)))
      = ℓ ^ 3 * ((1 / (2 * cchi ^ 2))
          * ∫ z in Metric.ball (0 : E3) R,
              (ω z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2)))) := by ring
    _ ≤ ℓ ^ 3 * ∫ z : E3, h z := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hℓ.le 3)
        rw [← hball]
        exact hh_ge
    _ = ∫ x in Submission.BoseGases.abox 2 ℓ,
          (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.chiScale ℓ (x 0)
            * Submission.BoseGases.chiScale ℓ (x 1)
            * (φ (x 0 - x 1) / (cchi ^ 2 * φ (x 0 - x 1) + 2 * lam))) := hchain1.symm
    _ ≤ ∫ x in Submission.BoseGases.abox 2 ℓ,
          (ω (x 0 - x 1)) ^ 2 * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
            / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * lam)) := hupper

theorem ppMass_le_q4mass_cnPlus_two {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ {Φ : Submission.BoseGases.X 2 → ℝ}, Continuous Φ →
      Work.BoseFixB3.CS.ppMass ℓ Φ
        ≤ C * (Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
                (Submission.BoseGases.wLoc ℓ v 0) Φ
            + (ℓ ^ 2)⁻¹ * Submission.BoseGases.cnPlus ℓ Φ) := by
  classical
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  obtain ⟨hω0, hω1⟩ := Submission.BoseGases.scattering_bounds_ae hR hv hvrad hv_supp hrad hw
  have hv_int : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hsuppv : ∀ z : E3, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
  have hωli : MeasureTheory.LocallyIntegrable (Classical.choose h) MeasureTheory.volume :=
    hw.lhs_integrable
  have hcchi : 0 < cchi := cchi_pos
  -- the coupling mass is strictly positive
  have hJ : 0 < ∫ z in Metric.ball (0 : E3) R, (Classical.choose h z) ^ 2 * v z := by
    obtain ⟨-, hJ'⟩ := v_w0_pos_sq hv hvrad hv1 R hR hv_supp hav h
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Metric.ball (0 : E3) R) (f := fun z => (Classical.choose h z) ^ 2 * v z)]
    · simpa [mul_comm] using hJ'
    · intro z hz
      have hz' : R ≤ ‖z‖ := by
        rw [Metric.mem_ball, not_lt] at hz
        simpa [dist_eq_norm] using hz
      rw [hsuppv z hz']
      simp
  obtain ⟨κ, hκpos, hκ⟩ := avgMass_case v (Classical.choose h) hR
    (div_pos hR Submission.BoseGases.chiR0_pos) hcchi hv hv_int hsuppv
    hωli.aestronglyMeasurable hω0 hω1 hJ
  refine ⟨28 * cchi ^ 2 / κ, div_nonneg (mul_nonneg (by norm_num) (sq_nonneg cchi))
    (le_of_lt hκpos), ?_⟩
  intro ℓ hℓ hRℓ Φ hΦc
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have hℓmin : R / Submission.BoseGases.chiR0 ≤ ℓ := by
    rw [div_le_iff₀ Submission.BoseGases.chiR0_pos]
    simpa [mul_comm] using hRℓ
  set X : ℝ := Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) 0 with hXdef
  have hXconst : ∀ x : Submission.BoseGases.X 2,
      Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x = X := by
    intro x
    rw [hXdef]
    exact aP_pair_const_two hℓ hΦc x 0
  set wL : Submission.BoseGases.X 2 → ℝ :=
    fun x => Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) with hwLdef
  set Rmod : Submission.BoseGases.X 2 → ℝ := fun x =>
    Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x
      - (Classical.choose h) (x 0 - x 1) * X with hRmoddef
  set F : Submission.BoseGases.X 2 → ℝ := fun x => ((Classical.choose h) (x 0 - x 1)) ^ 2
      * (wL x / (wL x + 2 * (ℓ ^ 2)⁻¹)) with hFdef
  have hF_eq : ∀ x : Submission.BoseGases.X 2, F x = ((Classical.choose h) (x 0 - x 1)) ^ 2
      * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
          / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹)) := fun x => rfl
  have hRmod_eq : ∀ x : Submission.BoseGases.X 2, Rmod x
      = Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x
        - (Classical.choose h) (x 0 - x 1) * X := fun x => rfl
  -- the pointwise two-slot inequality in the shape needed below
  have hpoint : ∀ x : Submission.BoseGases.X 2,
      2 * (ℓ ^ 2)⁻¹ * X ^ 2 * F x
        ≤ (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x) ^ 2
            * wL x + 2 * (ℓ ^ 2)⁻¹ * Rmod x ^ 2 := by
    intro x
    have h0 := key_ptwise (ℓ := ℓ) hℓ hv (ω := Classical.choose h) (Φ := Φ) x
    have h3 : (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x
            - (Classical.choose h) (x 0 - x 1)
              * Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x) ^ 2 = Rmod x ^ 2 := by
      rw [hRmod_eq x, hXconst x]
    rw [h3] at h0
    rw [hXconst x] at h0
    have h1 : 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * F x
        = 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * ((Classical.choose h) (x 0 - x 1)) ^ 2
          * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
              / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹)) := by
      rw [hF_eq x]
      ring
    have h2 : 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * ((Classical.choose h) (x 0 - x 1)) ^ 2
          * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
              / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹))
        = 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * ((Classical.choose h) (x 0 - x 1)) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
          / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹) := by
      ring
    rw [h1, h2]
    exact h0
  -- integrability
  obtain ⟨-, hq4meas, Bq, hBq0, hq4bnd⟩ :=
    ae_bounded_q4B_abox hv hvrad R hR hv_supp hav h hℓ hΦc (p := (0, 1)) (by decide)
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top 2 ℓ hℓ.le⟩
  have hInt1 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X 2 =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
    integrableOn_sq_mul_wLoc (n := 2) (ℓ := ℓ) (R := R) hℓ (v := v) hv_int hsuppv hRℓ
      (p := (0, 1)) hne
      (f := fun x : Submission.BoseGases.X 2 =>
        Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x)
      hq4meas (B := Bq) hBq0 hq4bnd
  have hωbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)),
      |(Classical.choose h) (x 0 - x 1)| ≤ 1 := by
    have hconj : ∀ᵐ z : E3, |(Classical.choose h) z| ≤ 1 := by
      filter_upwards [hω0, hω1] with z hz0 hz1
      rw [abs_of_nonneg hz0]; exact hz1
    exact Submission.BoseGases.ae_pair_pullback (N := 2) (ℓ := ℓ) (i := 0) (j := 1) hℓ hne hconj
  have hRmod_sm : MeasureTheory.AEStronglyMeasurable Rmod
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) := by
    rw [hRmoddef]
    exact hq4meas.sub ((Submission.BoseGases.w0_diff_aem hℓ hne hωli).mul aestronglyMeasurable_const)
  have hRmod_bnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)),
      ‖Rmod x‖ ≤ Bq + |X| := by
    filter_upwards [hq4bnd, hωbnd] with x hx hωx
    rw [hRmod_eq x]
    have h1 : ‖Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x‖ ≤ Bq := by
      simpa [Real.norm_eq_abs] using hx
    calc ‖Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x
            - (Classical.choose h) (x 0 - x 1) * X‖
        ≤ ‖Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x‖
          + ‖(Classical.choose h) (x 0 - x 1) * X‖ := norm_sub_le _ _
      _ ≤ Bq + 1 * |X| := by
          have h2 : ‖(Classical.choose h) (x 0 - x 1) * X‖ ≤ 1 * |X| := by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_right hωx (abs_nonneg X)
          linarith
      _ = Bq + |X| := by ring
  have hInt2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X 2 => Rmod x ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) := by
    refine MeasureTheory.Integrable.of_bound (hRmod_sm.pow 2) ((Bq + |X|) ^ 2) ?_
    filter_upwards [hRmod_bnd] with x hx
    have hB : 0 ≤ Bq + |X| := by linarith [hBq0, abs_nonneg X]
    have hx' : |Rmod x| ≤ Bq + |X| := by simpa [Real.norm_eq_abs] using hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (Rmod x)]
    nlinarith [hx', abs_nonneg (Rmod x), hB]
  -- the integrated two-slot inequality
  have h0f : 0 ≤ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)]
      (fun x : Submission.BoseGases.X 2 => 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * F x) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    show 0 ≤ 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * F x
    rw [hF_eq x]
    have hwnn := Work.BoseFixR.wLoc_zero_nonneg hv ℓ (x 0) (x 1)
    have h2pos : 0 < 2 * (ℓ ^ 2)⁻¹ := mul_pos (by norm_num) (inv_pos.mpr (pow_pos hℓ 2))
    have hden : 0 < Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹ := by linarith
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (div_nonneg hwnn (le_of_lt hden)))
  have hfg : (fun x : Submission.BoseGases.X 2 => 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * F x)
      ≤ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)]
      (fun x : Submission.BoseGases.X 2 =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹ * Rmod x ^ 2) :=
    Filter.Eventually.of_forall (fun x => hpoint x)
  have hmono := MeasureTheory.integral_mono_of_nonneg (f := fun x : Submission.BoseGases.X 2 =>
        2 * (ℓ ^ 2)⁻¹ * X ^ 2 * F x)
      (g := fun x : Submission.BoseGases.X 2 =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹ * Rmod x ^ 2)
      h0f (hInt1.add (hInt2.const_mul (2 * (ℓ ^ 2)⁻¹))) hfg
  -- abbreviations for the scalar quantities
  set D0 : ℝ := ∫ x in Submission.BoseGases.abox 2 ℓ,
      (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x) ^ 2
        * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) with hD0def
  set Y0 : ℝ := ∫ x in Submission.BoseGases.abox 2 ℓ, Rmod x ^ 2 with hY0def
  set E0 : ℝ := ∫ x in Submission.BoseGases.abox 2 ℓ, F x with hE0def
  set Ib : ℝ := ∫ z in Metric.ball (0 : E3) R,
      (Classical.choose h z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2))) with hIbdef
  set Q : ℝ := Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
      (Submission.BoseGases.wLoc ℓ v 0) Φ with hQdef
  set CN : ℝ := Submission.BoseGases.cnPlus ℓ Φ with hCNdef
  have hInt1' : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X 2 =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) := hInt1
  have hInt2' : MeasureTheory.Integrable (fun x : Submission.BoseGases.X 2 => Rmod x ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) := hInt2
  have hkey : 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * E0 ≤ D0 + 2 * (ℓ ^ 2)⁻¹ * Y0 := by
    rw [hE0def, hY0def, hD0def]
    have h1 : (∫ x in Submission.BoseGases.abox 2 ℓ, 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * F x)
        = 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * (∫ x in Submission.BoseGases.abox 2 ℓ, F x) :=
      MeasureTheory.integral_const_mul _ _
    have h2 : (∫ x in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹ * Rmod x ^ 2)
        = (∫ x in Submission.BoseGases.abox 2 ℓ,
            (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x) ^ 2
              * Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1))
          + 2 * (ℓ ^ 2)⁻¹ * (∫ x in Submission.BoseGases.abox 2 ℓ, Rmod x ^ 2) := by
      rw [MeasureTheory.integral_add hInt1' (hInt2'.const_mul _), MeasureTheory.integral_const_mul]
    rw [← h1, ← h2]
    exact hmono
  have hD_le : D0 ≤ Q := by
    rw [hD0def, hQdef]
    unfold Work.BoseFixB3.CS.q4Mass
    refine Finset.single_le_sum (f := fun p : Fin 2 × Fin 2 =>
      ∫ x in Submission.BoseGases.abox 2 ℓ,
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2)) ?_
      (by decide : (0, 1) ∈ Submission.BoseGases.pairSet 2)
    intro p hp
    exact MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (sq_nonneg _) (Work.BoseFixR.wLoc_zero_nonneg hv ℓ (x p.1) (x p.2))))
  have hY_le : Y0 ≤ 14 * CN := by
    rw [hY0def, hCNdef]
    have hyMass := yMass_two_le_cnPlus (ℓ := ℓ) hℓ (ω := Classical.choose h) hω0 hω1 hΦc
    have hcongr : (∫ x in Submission.BoseGases.abox 2 ℓ, Rmod x ^ 2)
        = ∫ x in Submission.BoseGases.abox 2 ℓ,
            (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (0, 1) x
              - (Classical.choose h) (x 0 - x 1)
                * Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x) ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [hRmod_eq x, hXconst x]
    rw [hcongr]
    exact hyMass
  -- the lower bound for the coupling average
  have hcr := crux_estimate (v := v) (ω := Classical.choose h) hR hℓ hRℓ hv hv_int hsuppv hωli hω0 hω1
  have hκℓ := hκ ℓ hℓmin
  have hI_lb : 2 * κ / ℓ ≤ Ib := by
    rw [hIbdef]
    have h2 : 2 * κ ≤ ℓ * (∫ z in Metric.ball (0 : E3) R,
        (Classical.choose h z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2)))) := by
      have h2' : (2 : ℝ) * ((ℓ / 2) * (∫ z in Metric.ball (0 : E3) R,
          (Classical.choose h z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2)))))
          = ℓ * (∫ z in Metric.ball (0 : E3) R,
              (Classical.choose h z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2)))) := by ring
      have h2'' := mul_le_mul_of_nonneg_left hκℓ (by norm_num : (0 : ℝ) ≤ 2)
      linarith [h2']
    rw [div_le_iff₀ hℓ]
    linarith [h2]
  have hE_lb : κ * ℓ ^ 2 / cchi ^ 2 ≤ E0 := by
    rw [hE0def]
    have hEint : (∫ x in Submission.BoseGases.abox 2 ℓ, F x)
        = ∫ x in Submission.BoseGases.abox 2 ℓ, ((Classical.choose h) (x 0 - x 1)) ^ 2
            * (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1)
                / (Submission.BoseGases.wLoc ℓ v 0 (x 0) (x 1) + 2 * (ℓ ^ 2)⁻¹)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact hF_eq x
    rw [hEint]
    have hpos : 0 ≤ ℓ ^ 3 / (2 * cchi ^ 2) := by positivity
    have h1 : (ℓ ^ 3 / (2 * cchi ^ 2)) * (2 * κ / ℓ)
        ≤ (ℓ ^ 3 / (2 * cchi ^ 2))
          * (∫ z in Metric.ball (0 : E3) R,
              (Classical.choose h z) ^ 2 * (v z / (v z + 1 / (cchi ^ 2 * ℓ ^ 2)))) :=
      mul_le_mul_of_nonneg_left hI_lb hpos
    have h2 : (ℓ ^ 3 / (2 * cchi ^ 2)) * (2 * κ / ℓ) = κ * ℓ ^ 2 / cchi ^ 2 := by
      field_simp
      try ring
    linarith [h1, h2, hcr]
  have hq4nn : 0 ≤ Q := by
    rw [hQdef]
    unfold Work.BoseFixB3.CS.q4Mass
    refine Finset.sum_nonneg (fun p hp => ?_)
    exact MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (sq_nonneg _) (Work.BoseFixR.wLoc_zero_nonneg hv ℓ (x p.1) (x p.2))))
  have hmain : 2 * X ^ 2 * κ / cchi ^ 2 ≤ Q + 28 * (ℓ ^ 2)⁻¹ * CN := by
    have h2 : 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * (κ * ℓ ^ 2 / cchi ^ 2)
        ≤ 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * E0 :=
      mul_le_mul_of_nonneg_left hE_lb (by positivity)
    have h3 : 2 * (ℓ ^ 2)⁻¹ * X ^ 2 * (κ * ℓ ^ 2 / cchi ^ 2) = 2 * X ^ 2 * κ / cchi ^ 2 := by
      field_simp
      try ring
    have h4 : 2 * (ℓ ^ 2)⁻¹ * Y0 ≤ 2 * (ℓ ^ 2)⁻¹ * (14 * CN) :=
      mul_le_mul_of_nonneg_left hY_le (by positivity)
    have h5 : 2 * (ℓ ^ 2)⁻¹ * (14 * CN) = 28 * (ℓ ^ 2)⁻¹ * CN := by ring
    have h6 : 2 * (ℓ ^ 2)⁻¹ * (14 * CN) ≤ 2 * (ℓ ^ 2)⁻¹ * (14 * CN) := le_rfl
    linarith [hkey, h2, h3, h4, h5, hD_le]
  have htarget : 2 * X ^ 2 ≤ (28 * cchi ^ 2 / κ) * (Q + (ℓ ^ 2)⁻¹ * CN) := by
    have hc2 : 0 < cchi ^ 2 := by positivity
    have hmain' : 2 * X ^ 2 * κ ≤ (Q + 28 * (ℓ ^ 2)⁻¹ * CN) * cchi ^ 2 := by
      rw [div_le_iff₀ hc2] at hmain
      exact hmain
    have hRHS : (28 * cchi ^ 2 / κ) * (Q + (ℓ ^ 2)⁻¹ * CN)
        = 28 * cchi ^ 2 * (Q + (ℓ ^ 2)⁻¹ * CN) / κ := by ring
    rw [hRHS, le_div_iff₀ hκpos]
    have hq : 0 ≤ cchi ^ 2 * Q := mul_nonneg (sq_nonneg cchi) hq4nn
    linarith [hmain', hq]
  rw [Work.BoseFixB3.CS.Pieces.ppMass_two_eq hℓ hΦc, ← hXdef]
  exact htarget



end Work.BoseFixB3.CS.Pieces
