import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.AliasDefs
import Submission.Work.BoseFixR.LatGreen.latticeGaussSummable
import Submission.Work.BoseRowsFS.Theta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.combHeat` — the comb/heat-lattice Poisson identity for the box modes

The target is the classical three-dimensional Gaussian Poisson (theta) identity in the exact form
in which the box-Fock kinetic row consumes it:

    `Σ_{n∈ℤ³} ℓ⁻³ e^{−t‖k_n‖²} e^{−i⟪k_n,u⟫} = Σ_{m∈ℤ³} (4πt)^{−3/2} e^{−‖u−ℓm‖²/4t}` ,

with `k_n = kmomInt ℓ n = (2π/ℓ)·n` the box modes and `heatK t` the heat kernel of mass `1`.
Because the lattice `ℤ³` is symmetric, the complex phase sum equals its real (cosine) part: the
sine companion is odd and vanishes.  Multiplying the three-dimensional theta identity
`Work.BoseRowsFS.theta3_images` (heat-kernel/image form) by the constant
`(4πt)^{−3/2}(2√(πt)/ℓ)³ = ℓ⁻³` then converts the image sum into the mode sum.

Everything is built from `Theta.lean`'s three-dimensional identity (itself the three-fold product
of the one-dimensional theta transformation `Commons.Analysis.Fourier.theta_shift_real`).
-/

namespace Work.BoseBoxFock

open scoped Real BigOperators

noncomputable section

set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `exp (−I x) = cos x − sin x · I` for real `x` (the summand's phase as a real combination). -/
lemma cexp_neg_I_mul (x : ℝ) :
    Complex.exp (-(Complex.I * (x : ℂ))) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
  rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- The box mode `kmomInt ℓ n = (2π/ℓ)·vecZ n` in the lattice normalisation of `Theta.lean`. -/
lemma kmomInt_eq_smul_vecZ (ℓ : ℝ) (n : Fin 3 → ℤ) :
    kmomInt ℓ n = (2 * Real.pi / ℓ) • Work.BoseRowsFS.vecZ n := by
  rw [show kmomInt ℓ n = ℓ⁻¹ • Work.BoseB4.vec n from rfl,
    Work.BoseRowsFS.vec_eq_smul_vecZ, smul_smul]
  congr 1
  ring

/-- Reversing a multi-index reverses the box mode. -/
lemma kmomInt_neg (ℓ : ℝ) (n : Fin 3 → ℤ) : kmomInt ℓ (-n) = -kmomInt ℓ n := by
  ext i
  simp [kmomInt, Work.BoseB4.vec]

/-- The momentum-side Gaussian weight is summable. -/
lemma summable_exp_neg_kmomInt {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : Fin 3 → ℤ => Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))) := by
  have hc : (0 : ℝ) < t / ℓ ^ 2 := by positivity
  have h := Work.BoseFixR.LatGreen.summable_exp_neg_norm_vec_sq (t := t / ℓ ^ 2) hc
  refine h.congr (fun n => ?_)
  congr 1
  rw [show kmomInt ℓ n = ℓ⁻¹ • Work.BoseB4.vec n from rfl, norm_smul,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ℓ⁻¹)]
  ring

/-- The `ℓ⁻³`-weighted Gaussian is summable. -/
lemma summable_weight {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))) :=
  (summable_exp_neg_kmomInt hℓ ht).mul_left _

/-- The Gaussian weighted by a trigonometric factor of the phase is summable. -/
lemma summable_weight_mul {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) (u : E3)
    (trig : ℝ → ℝ) (htrig : ∀ x, |trig x| ≤ 1) :
    Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) * trig (inner ℝ (kmomInt ℓ n) u)) := by
  refine Summable.of_norm_bounded (summable_weight hℓ ht) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹), abs_of_pos (Real.exp_pos _)]
  calc (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) * |trig (inner ℝ (kmomInt ℓ n) u)|
      ≤ (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left (htrig _) (by positivity)
    _ = (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) := by ring

/-- The absolute value of the Gaussian weighted by a trigonometric factor is summable. -/
lemma summable_weight_abs {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) (u : E3)
    (trig : ℝ → ℝ) (htrig : ∀ x, |trig x| ≤ 1) :
    Summable (fun n : Fin 3 → ℤ => |(ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
      * trig (inner ℝ (kmomInt ℓ n) u)|) := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) (summable_weight hℓ ht)
  rw [abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹), abs_of_pos (Real.exp_pos _)]
  calc (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) * |trig (inner ℝ (kmomInt ℓ n) u)|
      ≤ (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left (htrig _) (by positivity)
    _ = (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) := by ring

/-- The complex version of `summable_weight_abs`. -/
lemma summable_weight_mul_complex {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) (u : E3)
    (trig : ℝ → ℝ) (htrig : ∀ x, |trig x| ≤ 1) :
    Summable (fun n : Fin 3 → ℤ => (((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
      * trig (inner ℝ (kmomInt ℓ n) u) : ℝ) : ℂ)) := by
  refine Summable.of_norm_bounded (summable_weight_abs hℓ ht u trig htrig) (fun n => ?_)
  exact le_of_eq (RCLike.norm_ofReal (K := ℂ) _)

/-- **The sine companion vanishes**: the Gaussian-weighted sine of the phase is odd under
`n ↦ −n`, so its lattice sum is `0`. -/
lemma sin_sum_zero {ℓ : ℝ} (t : ℝ) (u : E3) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
      * Real.sin (inner ℝ (kmomInt ℓ n) u)) = 0 := by
  set f : (Fin 3 → ℤ) → ℝ := fun n => (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
      * Real.sin (inner ℝ (kmomInt ℓ n) u) with hf
  have h := Equiv.tsum_eq (Equiv.neg (Fin 3 → ℤ)) f
  simp only [Equiv.neg_apply] at h
  have hpt : ∀ n : Fin 3 → ℤ, f (-n) = -f n := by
    intro n
    simp only [hf, kmomInt_neg, norm_neg, inner_neg_left, Real.sin_neg]
    ring
  rw [tsum_congr hpt, tsum_neg] at h
  linarith [h]

/-- The lattice theta sum `Σ_j e^{−t‖k_j‖²}cos⟪k_j,u⟫` of the box modes. -/
def thetaSum (ℓ t : ℝ) (u : E3) : ℝ :=
  ∑' j : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ j‖ ^ 2)) * Real.cos (inner ℝ (kmomInt ℓ j) u)

/-- The constant identity `(4πt)^{−3/2}(2√(πt)/ℓ)³ = ℓ⁻³` of the theta transformation. -/
lemma const_arith {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) :
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * (2 * Real.sqrt (Real.pi * t) / ℓ) ^ 3
      = (ℓ ^ 3)⁻¹ := by
  have hs : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hsqrt : (4 * Real.pi * t) ^ (1 / 2 : ℝ) = 2 * Real.sqrt (Real.pi * t) := by
    rw [show (4 : ℝ) * Real.pi * t = 4 * (Real.pi * t) by ring,
      Real.mul_rpow (by norm_num) (by positivity : (0 : ℝ) ≤ Real.pi * t), Real.sqrt_eq_rpow]
    norm_num
  have hcube : (2 * Real.sqrt (Real.pi * t)) ^ 3 = (4 * Real.pi * t) ^ (3 / 2 : ℝ) := by
    rw [← hsqrt, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  rw [show (-(3 : ℝ) / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hs.le (3 / 2),
    ← hcube, div_pow]
  field_simp

/-- **The pointwise splitting** of the complex summand into its real (cosine) and imaginary
(sine) parts. -/
lemma lhs_summand_split {ℓ t : ℝ} (u : E3) (n : Fin 3 → ℤ) :
    ((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ)))
      = (((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
            * Real.cos (inner ℝ (kmomInt ℓ n) u) : ℝ) : ℂ)
        - (((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
            * Real.sin (inner ℝ (kmomInt ℓ n) u) : ℝ) : ℂ) * Complex.I := by
  rw [cexp_neg_I_mul]
  push_cast
  ring

theorem combHeat {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t)
    (u : EuclideanSpace ℝ (Fin 3)) :
    (∑' n : Fin 3 → ℤ, ((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) u : ℂ))))
      = ∑' m : Fin 3 → ℤ, ((Work.BoseBoxFock.heatK t (u - ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
  have hC : Summable (fun n : Fin 3 → ℤ => (((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
      * Real.cos (inner ℝ (kmomInt ℓ n) u) : ℝ) : ℂ)) :=
    summable_weight_mul_complex hℓ ht u Real.cos (fun x => Real.abs_cos_le_one x)
  have hS : Summable (fun n : Fin 3 → ℤ => (((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
      * Real.sin (inner ℝ (kmomInt ℓ n) u) : ℝ) : ℂ) * Complex.I) :=
    (summable_weight_mul_complex hℓ ht u Real.sin (fun x => Real.abs_sin_le_one x)).mul_right _
  -- the left-hand side is `ℓ⁻³·thetaSum`
  have hLHS : (∑' n : Fin 3 → ℤ, ((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ))))
      = (((ℓ ^ 3)⁻¹ * thetaSum ℓ t u : ℝ) : ℂ) := by
    calc (∑' n : Fin 3 → ℤ, ((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2)) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) u : ℂ))))
        = ∑' n : Fin 3 → ℤ, ((((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
              * Real.cos (inner ℝ (kmomInt ℓ n) u) : ℝ) : ℂ)
            - (((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
              * Real.sin (inner ℝ (kmomInt ℓ n) u) : ℝ) : ℂ) * Complex.I) :=
          tsum_congr (fun n => lhs_summand_split u n)
      _ = (∑' n : Fin 3 → ℤ, (((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
              * Real.cos (inner ℝ (kmomInt ℓ n) u) : ℝ) : ℂ))
            - (∑' n : Fin 3 → ℤ, (((ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
              * Real.sin (inner ℝ (kmomInt ℓ n) u) : ℝ) : ℂ) * Complex.I) :=
          Summable.tsum_sub hC hS
      _ = (((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
              * Real.cos (inner ℝ (kmomInt ℓ n) u)) : ℝ) : ℂ)
            - ((((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Real.exp (-(t * ‖kmomInt ℓ n‖ ^ 2))
              * Real.sin (inner ℝ (kmomInt ℓ n) u)) : ℝ) : ℂ) * Complex.I) := by
          rw [tsum_mul_right, ← Complex.ofReal_tsum, ← Complex.ofReal_tsum]
      _ = (((ℓ ^ 3)⁻¹ * thetaSum ℓ t u : ℝ) : ℂ) := by
          rw [sin_sum_zero t u, Complex.ofReal_zero, zero_mul, sub_zero]
          congr 1
          rw [thetaSum, ← tsum_mul_left]
          exact tsum_congr (fun n => by ring)
  -- the right-hand side is `ℓ⁻³·thetaSum` as well
  have hRHS : (∑' m : Fin 3 → ℤ, ((heatK t (u - ℓ • latVec m) : ℝ) : ℂ))
      = (((ℓ ^ 3)⁻¹ * thetaSum ℓ t u : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
    congr 1
    have hheat : ∀ m : Fin 3 → ℤ, heatK t (u - ℓ • latVec m)
        = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
          * Real.exp (-(‖u - ℓ • latVec m‖ ^ 2 / (4 * t))) := fun m => rfl
    rw [tsum_congr hheat, tsum_mul_left]
    have himg : (∑' m : Fin 3 → ℤ, Real.exp (-(‖u - ℓ • latVec m‖ ^ 2 / (4 * t))))
        = (2 * Real.sqrt (Real.pi * t) / ℓ) ^ 3 * thetaSum ℓ t u := by
      have h1 : (∑' m : Fin 3 → ℤ, Real.exp (-(‖u - ℓ • latVec m‖ ^ 2 / (4 * t))))
          = ∑' m : Fin 3 → ℤ,
              Real.exp (-(‖(-u) + ℓ • Work.BoseRowsFS.vecZ m‖ ^ 2 / (4 * t))) := by
        apply tsum_congr
        intro m
        have hnorm : ‖u - ℓ • latVec m‖ ^ 2 = ‖(-u) + ℓ • Work.BoseRowsFS.vecZ m‖ ^ 2 := by
          rw [show (-u) + ℓ • Work.BoseRowsFS.vecZ m
              = -(u - ℓ • Work.BoseRowsFS.vecZ m) by abel, norm_neg]
          rfl
        rw [hnorm]
      have h2 : (∑' j : Fin 3 → ℤ, Real.exp (-(t * ‖(2 * Real.pi / ℓ) • Work.BoseRowsFS.vecZ j‖ ^ 2))
            * Real.cos (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseRowsFS.vecZ j) (-u)))
          = thetaSum ℓ t u := by
        apply tsum_congr
        intro j
        rw [(kmomInt_eq_smul_vecZ ℓ j).symm, inner_neg_right, Real.cos_neg]
      rw [h1, Work.BoseRowsFS.theta3_images (ℓ := ℓ) (t := t) hℓ ht (-u), h2]
    rw [himg, ← mul_assoc, const_arith hℓ ht]
  rw [hLHS, hRHS]

end

end Work.BoseBoxFock
