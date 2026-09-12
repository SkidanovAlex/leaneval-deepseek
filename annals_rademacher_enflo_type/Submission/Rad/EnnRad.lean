import Submission.Rad.EnfloReal
import Submission.Rad.Bridge
import Submission.Commons.Analysis.ENNReal.mul_sInf_image
import Submission.Commons.Analysis.ENNReal.mul_le_mul_left_iff
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure NNReal
open scoped ENNReal BigOperators Interval
noncomputable section
namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The `lintegral` appearing in the Rademacher-type inequality equals `ofReal` of the uniform
average over the cube. -/
lemma rad_lhs_ofReal {n : ℕ} (x : Fin n → X) {p : ℝ} (hp0 : 0 ≤ p) :
    (∫⁻ (ε : Ω n), ‖∑ j : Fin n, (((ε j : C) : ℝ) • x j)‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n))
      = ENNReal.ofReal (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) * ‖∑ j : Fin n, (((ε j : C) : ℝ) • x j)‖ ^ p) := by
  calc
    (∫⁻ (ε : Ω n), ‖∑ j : Fin n, (((ε j : C) : ℝ) • x j)‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n))
        = ENNReal.ofReal (∫ ε : Ω n, ‖∑ j : Fin n, (((ε j : C) : ℝ) • x j)‖ ^ p
            ∂rademacherProductDistribution (Fin n)) := by
            exact lintegral_enorm_rpow (F := fun ε : Ω n => ∑ j : Fin n, (((ε j : C) : ℝ) • x j)) hp0
    _ = ENNReal.ofReal (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) * ‖∑ j : Fin n, (((ε j : C) : ℝ) • x j)‖ ^ p) := by
          congr 1
          rw [integral_uniform_eq (g := fun ε : Ω n => ‖∑ j : Fin n, (((ε j : C) : ℝ) • x j)‖ ^ p)]
          simp

/-- The RHS of the Rademacher-type inequality equals `ofReal` of the real quantity, for finite `C`. -/
lemma rad_rhs_ofReal {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) {C : ℝ≥0∞} (hC : C ≠ ⊤) (x : Fin n → X) :
    C ^ p * (∑ j : Fin n, ‖x j‖ₑ ^ p)
      = ENNReal.ofReal (C.toReal ^ p * (∑ j : Fin n, ‖x j‖ ^ p)) := by
  have hsum : (∑ j : Fin n, ‖x j‖ₑ ^ p) = ENNReal.ofReal (∑ j : Fin n, ‖x j‖ ^ p) := by
    calc
      (∑ j : Fin n, ‖x j‖ₑ ^ p)
          = ∑ j : Fin n, ENNReal.ofReal (‖x j‖ ^ p) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact (ofReal_norm_rpow (x j) hp0).symm
      _ = ENNReal.ofReal (∑ j : Fin n, ‖x j‖ ^ p) := by
              exact (ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (Fin n)))
                (f := fun j : Fin n => ‖x j‖ ^ p)
                (by intro j hj; exact Real.rpow_nonneg (norm_nonneg (x j)) p)).symm
  calc
    C ^ p * (∑ j : Fin n, ‖x j‖ₑ ^ p)
        = (ENNReal.ofReal C.toReal) ^ p * ENNReal.ofReal (∑ j : Fin n, ‖x j‖ ^ p) := by
            rw [ENNReal.ofReal_toReal hC, hsum]
    _ = ENNReal.ofReal (C.toReal ^ p) * ENNReal.ofReal (∑ j : Fin n, ‖x j‖ ^ p) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (x := C.toReal) (p := p) (by exact ENNReal.toReal_nonneg) hp0]
    _ = ENNReal.ofReal (C.toReal ^ p * (∑ j : Fin n, ‖x j‖ ^ p)) := by
            exact (ENNReal.ofReal_mul (p := C.toReal ^ p) (q := ∑ j : Fin n, ‖x j‖ ^ p)
              (Real.rpow_nonneg (by exact ENNReal.toReal_nonneg : 0 ≤ C.toReal) p)).symm

/-- Real form of the Rademacher-type inequality, from the `ENNReal` form with finite constant. -/
lemma rad_real {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hR : IsRademacherType X C p) (hn : 1 ≤ n) (x : Fin n → X) :
    (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) * ‖∑ j : Fin n, (((ε j : RadType.C) : ℝ) • x j)‖ ^ p)
      ≤ C.toReal ^ p * (∑ j : Fin n, ‖x j‖ ^ p) := by
  have hle := hR n hn x
  rw [rad_lhs_ofReal (x := x) hp0] at hle
  rw [rad_rhs_ofReal (n := n) (p := p) hp0 (C := C) hC x] at hle
  exact (ENNReal.ofReal_le_ofReal_iff
    (by
      have hc : 0 ≤ C.toReal := by exact ENNReal.toReal_nonneg
      exact mul_nonneg (Real.rpow_nonneg hc p)
        (Finset.sum_nonneg (by intro j hj; exact Real.rpow_nonneg (norm_nonneg (x j)) p)))).mp hle

/-- The `lintegral` on the left of the Enflo-type inequality equals `ofReal` of the uniform
average of the symmetrized quantity. -/
lemma enflo_lhs_ofReal {n : ℕ} (f : Ω n → X) {p : ℝ} (hp0 : 0 ≤ p) :
    (∫⁻ (ε : Ω n), ‖(1 / 2 : ℝ) • (f ε - f (-ε))‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n))
      = ENNReal.ofReal (meanReal (fun ε : Ω n => ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ p)) := by
  calc
    (∫⁻ (ε : Ω n), ‖(1 / 2 : ℝ) • (f ε - f (-ε))‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n))
        = ENNReal.ofReal (∫ ε : Ω n, ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ p
            ∂rademacherProductDistribution (Fin n)) := by
            change (∫⁻ (ε : Ω n), ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ₑ ^ p
                ∂rademacherProductDistribution (Fin n))
              = ENNReal.ofReal (∫ ε : Ω n, ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ p
                  ∂rademacherProductDistribution (Fin n))
            rw [lintegral_enorm_rpow (F := fun ε : Ω n => (1 / 2 : ℝ) • (f ε - f (negΩ ε))) hp0]
    _ = ENNReal.ofReal (meanReal (fun ε : Ω n => ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ p)) := by rfl

/-- Each summand on the right of the Enflo-type inequality equals `ofReal` of the uniform
average of `‖D_j f‖^p`. -/
lemma enflo_rhs_j_ofReal {n : ℕ} (j : Fin n) (f : Ω n → X) {p : ℝ} (hp0 : 0 ≤ p) :
    (∫⁻ (ε : Ω n), ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n))
      = ENNReal.ofReal (meanReal (fun x : Ω n => ‖D j f x‖ ^ p)) := by
  calc
    (∫⁻ (ε : Ω n), ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n))
        = ENNReal.ofReal (∫ ε : Ω n, ‖D j f ε‖ ^ p
            ∂rademacherProductDistribution (Fin n)) := by
            rw [lintegral_enorm_rpow (F := fun ε : Ω n => D j f ε) hp0]
    _ = ENNReal.ofReal (meanReal (fun x : Ω n => ‖D j f x‖ ^ p)) := by rfl

/-- Identifying the Enflo constant `(π/√2)·C` with `(pi/sqrt 2 : ℝ≥0) * C`. -/
lemma rad_const_enn {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    ENNReal.ofReal ((Real.pi / Real.sqrt 2) * C.toReal)
      = ((pi / sqrt 2 : ℝ≥0) : ℝ≥0∞) * C := by
  calc
    ENNReal.ofReal ((Real.pi / Real.sqrt 2) * C.toReal)
        = ENNReal.ofReal ((Real.pi / Real.sqrt 2) : ℝ) * ENNReal.ofReal C.toReal := by
            exact ENNReal.ofReal_mul (p := (Real.pi / Real.sqrt 2 : ℝ)) (q := C.toReal)
              (by positivity : 0 ≤ (Real.pi / Real.sqrt 2 : ℝ))
    _ = ((pi / sqrt 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal C.toReal := by
          congr 1
          rw [← ENNReal.ofReal_coe_nnreal (p := (pi / sqrt 2 : ℝ≥0))]
          congr 1
          rw [NNReal.coe_div, NNReal.coe_real_pi]
          congr 1
          symm
          exact Real.coe_sqrt (x := (2 : ℝ≥0))
    _ = ((pi / sqrt 2 : ℝ≥0) : ℝ≥0∞) * C := by
          rw [ENNReal.ofReal_toReal hC]

/-- The Enflo-type inequality with constant `(π/√2)·C` follows from Rademacher type `C`
(finite `C`). -/
lemma enflo_of_rad {C : ℝ≥0∞} {p : ℝ} (h1p : 1 ≤ p) (hp2 : p ≤ 2)
    (hC : C ≠ ⊤) (hR : IsRademacherType X C p) :
    IsEnfloType X (ENNReal.ofReal ((Real.pi / Real.sqrt 2) * C.toReal)) p := by
  have hp0 : 0 ≤ p := by linarith
  intro n hn f
  let c : ℝ := C.toReal
  have hc0 : 0 ≤ c := by exact ENNReal.toReal_nonneg
  have hRad : ∀ (m : ℕ), 1 ≤ m → ∀ x : Fin m → X,
      (∑ ε : Ω m, ((1 / 2 : ℝ) ^ m) * ‖∑ j : Fin m, (((ε j : RadType.C) : ℝ) • x j)‖ ^ p)
        ≤ c ^ p * (∑ j : Fin m, ‖x j‖ ^ p) := by
    intro m hm x
    exact rad_real (n := m) (p := p) hp0 hC hR hm x
  have henfloReal : meanReal (fun ε : Ω n => ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ p)
      ≤ ((Real.pi / Real.sqrt 2) * c) ^ p *
          (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ p)) := by
    exact enflo_real_ineq (n := n) hn f h1p hp2 (c := c) hc0 hRad
  have hmj : ∀ j : Fin n, 0 ≤ meanReal (fun x : Ω n => ‖D j f x‖ ^ p) := by
    intro j
    unfold meanReal
    exact integral_nonneg (by intro x; exact Real.rpow_nonneg (norm_nonneg (D j f x)) p)
  have hprod : ENNReal.ofReal (((Real.pi / Real.sqrt 2) * c) ^ p *
          (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ p)))
      = (ENNReal.ofReal ((Real.pi / Real.sqrt 2) * c)) ^ p *
          (∑ j : Fin n, ENNReal.ofReal (meanReal (fun x : Ω n => ‖D j f x‖ ^ p))) := by
    calc
      ENNReal.ofReal ((((Real.pi / Real.sqrt 2) * c) ^ p) *
            (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ p)))
          = ENNReal.ofReal (((Real.pi / Real.sqrt 2) * c) ^ p) *
              ENNReal.ofReal (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ p)) := by
              exact ENNReal.ofReal_mul (p := ((Real.pi / Real.sqrt 2) * c) ^ p)
                (q := ∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ p))
                (Real.rpow_nonneg (x := (Real.pi / Real.sqrt 2) * c) (y := p)
                  (mul_nonneg (by positivity : 0 ≤ (Real.pi / Real.sqrt 2 : ℝ)) hc0))
      _ = (ENNReal.ofReal ((Real.pi / Real.sqrt 2) * c)) ^ p *
              ENNReal.ofReal (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ p)) := by
              rw [← ENNReal.ofReal_rpow_of_nonneg (x := (Real.pi / Real.sqrt 2) * c) (p := p)
                (mul_nonneg (by positivity : 0 ≤ (Real.pi / Real.sqrt 2 : ℝ)) hc0) hp0]
      _ = (ENNReal.ofReal ((Real.pi / Real.sqrt 2) * c)) ^ p *
              (∑ j : Fin n, ENNReal.ofReal (meanReal (fun x : Ω n => ‖D j f x‖ ^ p))) := by
              rw [ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (Fin n)))
                (f := fun j : Fin n => meanReal (fun x : Ω n => ‖D j f x‖ ^ p))
                (by intro j hj; exact hmj j)]
  have hm : ENNReal.ofReal (meanReal (fun ε : Ω n => ‖(1 / 2 : ℝ) • (f ε - f (negΩ ε))‖ ^ p))
      ≤ ENNReal.ofReal (((Real.pi / Real.sqrt 2) * c) ^ p *
          (∑ j : Fin n, meanReal (fun x : Ω n => ‖D j f x‖ ^ p))) := by
    exact ENNReal.ofReal_le_ofReal henfloReal
  rw [enflo_lhs_ofReal f hp0]
  rw [show (∑ j : Fin n, (∫⁻ (ε : Ω n), ‖D j f ε‖ₑ ^ p
      ∂rademacherProductDistribution (Fin n)))
      = ∑ j : Fin n, ENNReal.ofReal (meanReal (fun x : Ω n => ‖D j f x‖ ^ p)) by
        apply Finset.sum_congr rfl
        intro j hj
        exact enflo_rhs_j_ofReal j f hp0]
  exact le_trans hm (le_of_eq hprod)

end RadType
