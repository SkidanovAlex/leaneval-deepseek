import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TanTheta.Basic
import Submission.Work.Spaces.integrableOn_majorant_rpow
import Submission.Work.Spaces.sin_rpow_le_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Auxiliary lemmas

The auxiliary facts used by `integrable_wrho_products`: the bound `|ρ| ≤ 1/2` on `(0, π/2)`,
the integrability of the weight `sin(2θ)^{-η}` there, the pointwise bounds for the two products
(one via the bounds on `ψ` and `ψ'`, one via the algebraic identity of `halg`), and the
consequence `ψ θ = (cos θ ψ'' θ - u'' θ - 2 sin θ ψ' θ)/cos θ` of that identity. -/

/-- On `(0, π/2)` the weight `ρ θ = sin θ cos θ sin(2θ)^{-η}` is bounded by `1/2` when `η < 1`:
`ρ = (1/2)·sin(2θ)^{1-η}` and `sin(2θ) ≤ 1`. -/
theorem abs_wrho_le_half (η : ℝ) (hη1 : η < 1) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : |wrho η θ| ≤ 1 / 2 := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsng : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcosg : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have htwo : Real.sin θ * Real.cos θ = (1 / 2) * Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; ring
  have hsplit : (Real.sin (2 * θ)) ^ (1 - η)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-η) := by
    rw [show (1 : ℝ) - η = 1 + (-η) by ring, Real.rpow_add hsin, Real.rpow_one]
  have hval : (1 / 2) * Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-η)
      = (1 / 2) * ((Real.sin (2 * θ)) ^ (1 - η)) := by
    rw [hsplit]; ring
  have hnn : 0 ≤ (1 / 2) * ((Real.sin (2 * θ)) ^ (1 - η)) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hsin.le _)
  rw [wrho, htwo, hval, abs_of_nonneg hnn]
  calc (1 / 2) * (Real.sin (2 * θ)) ^ (1 - η) ≤ (1 / 2) * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_one hsin.le (Real.sin_le_one _) (by linarith)) (by norm_num)
    _ = 1 / 2 := by norm_num

/-- The weight `sin(2θ)^{-η}` is integrable on `(0, π/2)` for `η < 1`. -/
theorem integrableOn_sin_two_rpow_neg (η : ℝ) (hη1 : η < 1) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η))
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const (-η)).aestronglyMeasurable
  have hfin : (volume : Measure ℝ) (Set.Ioo 0 (Real.pi / 2)) ≠ ⊤ := by
    have hle : (volume : Measure ℝ) (Set.Ioo 0 (Real.pi / 2))
        ≤ (volume : Measure ℝ) (Set.Icc 0 (Real.pi / 2)) :=
      measure_mono Set.Ioo_subset_Icc_self
    have htop : (volume : Measure ℝ) (Set.Icc 0 (Real.pi / 2)) < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    exact ne_of_lt (lt_of_le_of_lt hle htop)
  by_cases hη : η ≤ 0
  · refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ))
      (integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ)) hfin) hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hsin.le _)]
    exact Real.rpow_le_one hsin.le (Real.sin_le_one _) (by linarith)
  · have hηpos : 0 < η := not_le.mp hη
    refine Integrable.mono'
      (g := fun θ : ℝ => (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)))
      ((Work.Spaces.integrableOn_majorant_rpow η hηpos hη1).mono_set Set.Ioo_subset_Icc_self)
      hmeas ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hsin.le _)]
    exact Work.Spaces.sin_rpow_le_majorant η θ hηpos ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- The algebraic identity of `halg` solved for `ψ`: on `(0, π/2)`,
`ψ θ = (cos θ ψ'' θ - u'' θ - 2 sin θ ψ' θ)/cos θ`. -/
theorem psi_eq_of_alg (u : ℝ → ℝ)
    (halg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * deriv (deriv (psi u)) θ
        = deriv (deriv u) θ + Real.cos θ * psi u θ + 2 * Real.sin θ * deriv (psi u) θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    psi u θ = (Real.cos θ * deriv (deriv (psi u)) θ - deriv (deriv u) θ
        - 2 * Real.sin θ * deriv (psi u) θ) / Real.cos θ := by
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  rw [eq_div_iff hc, mul_comm (psi u θ) (Real.cos θ), halg θ hθ]
  ring

/-- Pointwise bound for the first product: `|ρ ψ ψ'| ≤ (1/2) C D` when `|ψ| ≤ C` and
`|ψ'| ≤ D` on `(0, π/2)`. -/
theorem abs_wrho_mul_psi_mul_deriv_le (η C D : ℝ) (hη1 : η < 1) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hC : |psi u θ| ≤ C) (hD : |deriv (psi u) θ| ≤ D) :
    |wrho η θ * psi u θ * deriv (psi u) θ| ≤ (1 / 2) * C * D := by
  have h1 : |wrho η θ| ≤ 1 / 2 := abs_wrho_le_half η hη1 hθ
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hC
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hD
  have hstep : |wrho η θ| * |psi u θ| ≤ (1 / 2) * C :=
    le_trans (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hC (by norm_num))
  rw [abs_mul, abs_mul]
  exact le_trans (mul_le_mul_of_nonneg_right hstep (abs_nonneg _))
    (mul_le_mul_of_nonneg_left hD (mul_nonneg (by norm_num) hC0))

/-- Pointwise bound for the second product, using the algebraic identity `halg`:
`|ρ ψ' ψ''| ≤ (1/2)·sin(2θ)^{-η}·(u'')² + ((1/2)D² + D(C + 2D))·sin(2θ)^{-η}`. -/
theorem abs_wrho_mul_deriv_deriv_le (η C D : ℝ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hC : |psi u θ| ≤ C) (hD : |deriv (psi u) θ| ≤ D)
    (halg : Real.cos θ * deriv (deriv (psi u)) θ
        = deriv (deriv u) θ + Real.cos θ * psi u θ + 2 * Real.sin θ * deriv (psi u) θ) :
    |wrho η θ * deriv (psi u) θ * deriv (deriv (psi u)) θ|
      ≤ (1 / 2) * ((Real.sin (2 * θ)) ^ (-η) * (deriv (deriv u) θ) ^ 2)
        + ((1 / 2) * D ^ 2 + D * (C + 2 * D)) * (Real.sin (2 * θ)) ^ (-η) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hsng : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- abbreviate the weight
  set s : ℝ := (Real.sin (2 * θ)) ^ (-η) with hsdef
  have hsnn : 0 ≤ s := by rw [hsdef]; exact Real.rpow_nonneg hsin.le _
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hC
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hD
  have hrho : |wrho η θ| = Real.sin θ * Real.cos θ * s := by
    rw [wrho, abs_mul, abs_mul, abs_of_pos hsng, abs_of_pos hcos, ← hsdef,
      abs_of_nonneg hsnn]
  -- bound `cos θ · |ψ''|` using `halg`
  have hcosR : Real.cos θ * |deriv (deriv (psi u)) θ|
      ≤ |deriv (deriv u) θ| + C + 2 * D := by
    have hL : Real.cos θ * |deriv (deriv (psi u)) θ|
        = |Real.cos θ * deriv (deriv (psi u)) θ| := by
      rw [abs_mul, abs_of_pos hcos]
    rw [hL, halg]
    have htri : |deriv (deriv u) θ + Real.cos θ * psi u θ
          + 2 * Real.sin θ * deriv (psi u) θ|
        ≤ |deriv (deriv u) θ| + (|Real.cos θ * psi u θ|
          + |2 * Real.sin θ * deriv (psi u) θ|) := by
      refine le_trans (abs_add_le (deriv (deriv u) θ + Real.cos θ * psi u θ)
        (2 * Real.sin θ * deriv (psi u) θ)) ?_
      linarith [abs_add_le (deriv (deriv u) θ) (Real.cos θ * psi u θ)]
    have hP : |Real.cos θ * psi u θ| ≤ C := by
      rw [abs_mul, abs_of_pos hcos]
      exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (Real.cos_le_one θ)) hC
    have hQ : |2 * Real.sin θ * deriv (psi u) θ| ≤ 2 * D := by
      have hsq : |2 * Real.sin θ * deriv (psi u) θ|
          = 2 * |Real.sin θ| * |deriv (psi u) θ| := by
        rw [abs_mul, abs_mul]; norm_num
      rw [hsq]
      calc 2 * |Real.sin θ| * |deriv (psi u) θ| ≤ 2 * 1 * |deriv (psi u) θ| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (by norm_num)) (abs_nonneg _)
        _ ≤ 2 * 1 * D := mul_le_mul_of_nonneg_left hD (by norm_num)
        _ = 2 * D := by ring
    linarith
  -- peel off the bounded factors
  have hstep : |wrho η θ * deriv (psi u) θ * deriv (deriv (psi u)) θ|
      ≤ s * D * (|deriv (deriv u) θ| + C + 2 * D) := by
    rw [abs_mul, abs_mul, hrho]
    rw [show Real.sin θ * Real.cos θ * s * |deriv (psi u) θ|
          * |deriv (deriv (psi u)) θ|
        = s * |deriv (psi u) θ|
          * (Real.sin θ * (Real.cos θ * |deriv (deriv (psi u)) θ|)) by ring]
    have h1 : Real.sin θ * (Real.cos θ * |deriv (deriv (psi u)) θ|)
        ≤ |deriv (deriv u) θ| + C + 2 * D := by
      calc Real.sin θ * (Real.cos θ * |deriv (deriv (psi u)) θ|)
          ≤ 1 * (Real.cos θ * |deriv (deriv (psi u)) θ|) :=
            mul_le_mul_of_nonneg_right (Real.sin_le_one θ)
              (mul_nonneg hcos.le (abs_nonneg _))
        _ = Real.cos θ * |deriv (deriv (psi u)) θ| := by ring
        _ ≤ |deriv (deriv u) θ| + C + 2 * D := hcosR
    have h2a : s * |deriv (psi u) θ| * (Real.sin θ * (Real.cos θ * |deriv (deriv (psi u)) θ|))
        ≤ s * D * (Real.sin θ * (Real.cos θ * |deriv (deriv (psi u)) θ|)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hsnn)
        (mul_nonneg (le_of_lt hsng) (mul_nonneg hcos.le (abs_nonneg _)))
    have h2b : s * D * (Real.sin θ * (Real.cos θ * |deriv (deriv (psi u)) θ|))
        ≤ s * D * (|deriv (deriv u) θ| + C + 2 * D) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hsnn hD0)
    exact le_trans h2a h2b
  -- AM-GM on `D·|u''|` and collect
  have hAM : D * |deriv (deriv u) θ|
      ≤ (1 / 2) * (deriv (deriv u) θ) ^ 2 + (1 / 2) * D ^ 2 := by
    have h1 : 0 ≤ (|deriv (deriv u) θ| - D) ^ 2 := sq_nonneg _
    rw [sub_sq, sq_abs (deriv (deriv u) θ)] at h1
    nlinarith [h1]
  refine le_trans hstep ?_
  rw [show s * D * (|deriv (deriv u) θ| + C + 2 * D)
      = s * (D * |deriv (deriv u) θ| + D * (C + 2 * D)) by ring]
  rw [show (1 / 2) * (s * (deriv (deriv u) θ) ^ 2)
        + ((1 / 2) * D ^ 2 + D * (C + 2 * D)) * s
      = s * ((1 / 2) * (deriv (deriv u) θ) ^ 2 + (1 / 2) * D ^ 2
          + D * (C + 2 * D)) by ring]
  exact mul_le_mul_of_nonneg_left (by linarith [hAM]) hsnn

/-! ## The main theorem -/

/-- The two products appearing in the weighted integration by parts are integrable:
`ρ ψ ψ'` and `ρ ψ' ψ''`, where `ρ θ = sin θ cos θ sin(2θ)^{-η}`, `η ∈ [0,1)`.

Route.  `|ρ θ| ≤ 1/2` on `(0, π/2)` (write `ρ = (1/2) sin(2θ) · sin(2θ)^{-η}`, `sin(2θ) ≤ 1`,
`1 - η ≥ 0`).
* First product: `|ρ ψ ψ'| ≤ (1/2)|ψ ψ'| ≤ (1/4)(ψ² + ψ'²)` with `‖ψ‖ ≤ C`, `‖ψ'‖ ≤ D`
  bounded; the set has finite measure.
* Second product: multiply the algebra `halg` (i.e. `cos θ ψ'' = u'' + cos θ ψ + 2 sin θ ψ'`)
  by `sin θ ψ' sin(2θ)^{-η}` to get
  `ρ ψ' ψ'' = sin θ sin(2θ)^{-η} ψ' u'' + cos θ sin θ sin(2θ)^{-η} ψ ψ' + 2 sin²θ sin(2θ)^{-η} (ψ')²`,
  then bound the three pieces by `sin(2θ)^{-η} |ψ'| |u''|` (either by Cauchy–Schwarz — `ψ'` and
  `u''` are both in `L²` for the weight `sin(2θ)^{-η}`, from the boundedness of `ψ'` and
  `hi2` — or simply by `(1/2) sin(2θ)^{-η}(D² u''² + 1)`), by `(1/2) sin(2θ)^{-η}(ψ² + ψ'²)`,
  and by `2 sin(2θ)^{-η} (ψ')²`; all are integrable because `sin(2θ)^{-η}` is integrable on
  `(0,π/2)` for `η < 1` (e.g. `Work.FTS.H2.intervalIntegrable_sin_rpow (-η) (by linarith)` in
  `Submission/Work/FTS/H2/STBasic.lean`) and `hi2`/`hi3` hold.  For a bounded factor `h` and an
  integrable `v`, `IntegrableOn (h * v)` follows from `Integrable.mul_bdd`. -/
theorem integrable_wrho_products (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ) (C D : ℝ)
    (hC : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ‖Work.FTS.EllipticEst.TanTheta.psi u θ‖ ≤ C)
    (hD : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ‖deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ‖ ≤ D)
    (halg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.cos θ * deriv (deriv (Work.FTS.EllipticEst.TanTheta.psi u)) θ
        = deriv (deriv u) θ + Real.cos θ * Work.FTS.EllipticEst.TanTheta.psi u θ
          + 2 * Real.sin θ * deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ)
    (hi2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)))
    (hi3 : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.TanTheta.psi u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.TanTheta.wrho η θ
          * Work.FTS.EllipticEst.TanTheta.psi u θ
          * deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ) (Set.Ioo 0 (Real.pi / 2))
      ∧ MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.TanTheta.wrho η θ
          * deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ
          * deriv (deriv (Work.FTS.EllipticEst.TanTheta.psi u)) θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
  have hC0 : 0 ≤ C := by
    have h := hC (Real.pi / 4) (by constructor <;> linarith [Real.pi_pos])
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  have hD0 : 0 ≤ D := by
    have h := hD (Real.pi / 4) (by constructor <;> linarith [Real.pi_pos])
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  have hwrmeas : Measurable (wrho η) := by
    unfold wrho
    exact (Real.measurable_sin.mul Real.measurable_cos).mul
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const (-η))
  have hfin : (volume : Measure ℝ) (Set.Ioo 0 (Real.pi / 2)) ≠ ⊤ := by
    have hle : (volume : Measure ℝ) (Set.Ioo 0 (Real.pi / 2))
        ≤ (volume : Measure ℝ) (Set.Icc 0 (Real.pi / 2)) :=
      measure_mono Set.Ioo_subset_Icc_self
    have htop : (volume : Measure ℝ) (Set.Icc 0 (Real.pi / 2)) < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    exact ne_of_lt (lt_of_le_of_lt hle htop)
  refine ⟨?_, ?_⟩
  · -- the first product: bounded, on a set of finite measure
    have hFmeas : Measurable (fun θ : ℝ => wrho η θ
        * ((Real.cos θ * deriv (deriv (psi u)) θ - deriv (deriv u) θ
            - 2 * Real.sin θ * deriv (psi u) θ) / Real.cos θ)
        * deriv (psi u) θ) := by
      refine (hwrmeas.mul ?_).mul (measurable_deriv _)
      refine Measurable.div ?_ Real.measurable_cos
      refine Measurable.sub ?_ ?_
      · exact (Real.measurable_cos.mul (measurable_deriv _)).sub (measurable_deriv _)
      · exact (measurable_const.mul Real.measurable_sin).mul (measurable_deriv _)
    refine Integrable.mono' (g := fun _ : ℝ => (1 / 2) * C * D)
      (integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (C := (1 / 2) * C * D) hfin)
      ?_ ?_
    · refine hFmeas.aestronglyMeasurable.congr ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      dsimp only
      rw [psi_eq_of_alg u halg hθ]
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs]
      exact abs_wrho_mul_psi_mul_deriv_le η C D hη1 u hθ
        (by simpa [Real.norm_eq_abs] using hC θ hθ)
        (by simpa [Real.norm_eq_abs] using hD θ hθ)
  · -- the second product: dominated by integrable terms via `halg`
    have hF2meas : Measurable (fun θ : ℝ => wrho η θ
        * deriv (psi u) θ * deriv (deriv (psi u)) θ) :=
      (hwrmeas.mul (measurable_deriv _)).mul (measurable_deriv _)
    have hw : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) := integrableOn_sin_two_rpow_neg η hη1
    have hi2' : IntegrableOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η) * (deriv (deriv u) θ) ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) :=
      hi2.congr_fun_ae (ae_restrict_of_forall_mem measurableSet_Ioo (fun θ _ => by ring))
    have hA : IntegrableOn
        (fun θ : ℝ => (1 / 2) * ((Real.sin (2 * θ)) ^ (-η) * (deriv (deriv u) θ) ^ 2))
        (Set.Ioo 0 (Real.pi / 2)) := Integrable.const_mul hi2' (1 / 2)
    have hB : IntegrableOn
        (fun θ : ℝ => ((1 / 2) * D ^ 2 + D * (C + 2 * D)) * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) :=
      Integrable.const_mul hw ((1 / 2) * D ^ 2 + D * (C + 2 * D))
    have hg : IntegrableOn
        (fun θ : ℝ => (1 / 2) * ((Real.sin (2 * θ)) ^ (-η) * (deriv (deriv u) θ) ^ 2)
          + ((1 / 2) * D ^ 2 + D * (C + 2 * D)) * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) := Integrable.add hA hB
    refine Integrable.mono' hg hF2meas.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    exact abs_wrho_mul_deriv_deriv_le η C D u hθ
      (by simpa [Real.norm_eq_abs] using hC θ hθ)
      (by simpa [Real.norm_eq_abs] using hD θ hθ) (halg θ hθ)

end Work.FTS.EllipticEst.TanTheta
