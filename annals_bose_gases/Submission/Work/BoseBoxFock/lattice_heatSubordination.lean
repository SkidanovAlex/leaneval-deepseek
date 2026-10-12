import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_decay_gen
import Submission.Work.BoseBoxFock.SqrtKin.subordination_rpow
import Submission.Work.BoseBoxFock.SqrtKin.subordination_rpow_integrableOn
import Submission.Work.BoseBoxFock.frame_lattice_ball
import Submission.Work.BoseK15.sum_inv_one_add_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lattice_heatSubordination`

The **lattice heat subordination identity** for the kinetic row of the box-Fock model:

`Σ_n ℓ⁻³‖k_n‖‖kinFT g (k_n)‖²
  = (2√π)⁻¹ ∫_0^∞ t^{-3/2} ( Σ_n ℓ⁻³‖kinFT g (k_n)‖²
                              − Σ_n ℓ⁻³e^{-t‖k_n‖²}‖kinFT g (k_n)‖² ) dt`,

where `k_n = kmomInt ℓ n = ℓ⁻¹ • vec n = (2π/ℓ)n` runs over the full lattice `(2π/ℓ)ℤ³` and `g`
is smooth with `tsupport g ⊆ ball 0 (ℓ/2)`.

The bracket on the right is **purely lattice**: it is the pointwise sum `Σ_n a_n(1 − e^{-t‖k_n‖²})`
with `a_n = ℓ⁻³‖kinFT g (k_n)‖² ≥ 0`.  Hence the identity is the per-mode subordination
`∫_0^∞ t^{-3/2}(1 − e^{-ta})dt = 2√π√a` (`Work.BoseBoxFock.SqrtKin.subordination_rpow`),
summed with Tonelli (`MeasureTheory.integral_tsum` on the countably indexed nonnegative family).
No frame/Poisson identity is involved: both sides are lattice sums over the *same* momenta, so
there is no aliasing deficit to account for.

The only analytic input is the summability of `a_n` and of `‖k_n‖a_n`, obtained from
`Work.OneBodyKin.kinFT_decay_le` (polynomial decay of `kinFT g` for smooth compactly supported `g`,
via `Work.BoseBoxFock.SqrtKin.kinFT_decay_gen`) combined with the lattice decay
`Work.BoseK15.sum_inv_one_add_norm_le`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

set_option maxHeartbeats 4000000

/-! ## Auxiliary algebraic fact -/

/-- From `P ≤ C*Q` with `P, Q > 0` infer `Q⁻¹ ≤ C*P⁻¹` (multiply by `P` and divide by `Q`). -/
lemma inv_le_mul_inv_of_le_mul {P Q C : ℝ} (hP : 0 < P) (hQ : 0 < Q) (h : P ≤ C * Q) :
    Q⁻¹ ≤ C * P⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ hP]
  have h2 : P * Q⁻¹ ≤ C := by
    have h3 := (div_le_iff₀ hQ).mpr h
    rwa [div_eq_mul_inv] at h3
  have h4 : Q⁻¹ * P = P * Q⁻¹ := mul_comm _ _
  rwa [h4]

/-! ## Summability of the lattice kinetic weights -/

/-- **Summability of the lattice kinetic weights.**  For `g` smooth with compact support, the
`ℓ⁻³`-weighted lattice samples of `‖kinFT g‖²` with any polynomial weight `‖k_n‖^j` are summable.
This is the finite-mass/finite-first-moment input of the subordination identity.

Proof: `‖kinFT g p‖ ≤ K (1+‖p‖)^{-(j+4)}` (`kinFT_decay_gen`), so the general term is dominated by
`C (1+‖k_n‖)^{-(j+8)}`, and `(1+‖k_n‖)^{-(j+8)} ≲ (1+‖vec n‖²)^{-3}`, whose lattice sum converges
(`sum_inv_one_add_norm_le`). -/
theorem summable_lattice_kinFT_weight {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (j : ℕ) :
    Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ j
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := SqrtKin.kinFT_decay_gen hg hgc (j + 4)
  set M : ℝ := max 1 (ℓ^2) with hMdef
  have hM1 : (1:ℝ) ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hMl : ℓ^2 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hsum_vec : Summable (fun n : Fin 3 → ℤ => (((1:ℝ) + ‖Work.BoseB4.vec n‖^2)^3)⁻¹) :=
    summable_of_sum_le (fun n => by positivity)
      (fun u => (Work.BoseK15.sum_inv_one_add_norm_le 3 (by norm_num)).choose_spec.2 u)
  have key : ∀ n : Fin 3 → ℤ,
      (ℓ^3)⁻¹ * ‖kmomInt ℓ n‖^j * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2
        ≤ ((ℓ^3)⁻¹ * K^2 * M^3) * (((1:ℝ) + ‖Work.BoseB4.vec n‖^2)^3)⁻¹ := by
    intro n
    set u : ℝ := ‖kmomInt ℓ n‖ with hu
    set F : ℝ := ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ with hF
    have hu0 : 0 ≤ u := by rw [hu]; exact norm_nonneg _
    have hF0 : 0 ≤ F := by rw [hF]; exact norm_nonneg _
    have hw : ‖Work.BoseB4.vec n‖ = ℓ * u := by
      rw [hu]
      have h : ‖kmomInt ℓ n‖ = ℓ⁻¹ * ‖Work.BoseB4.vec n‖ := by
        rw [show kmomInt ℓ n = ℓ⁻¹ • Work.BoseB4.vec n from rfl, norm_smul,
          Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ℓ⁻¹)]
      rw [h]; field_simp
    have hb1 : F ≤ K / (1 + u)^(j+4) := by rw [hF, hu]; exact hK _
    have hb2 : F^2 ≤ K^2 / (1 + u)^(2*j+8) := by
      have h2 := pow_le_pow_left₀ hF0 hb1 2
      rw [div_pow] at h2
      have he : ((1 + u) ^ (j+4))^2 = (1+u)^(2*j+8) := by
        rw [← pow_mul]; congr 1; omega
      rwa [he] at h2
    have hb3 : u^j / (1+u)^(2*j+8) ≤ 1 / (1+u)^(j+8) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (1+u)^(2*j+8))
        (by positivity : (0:ℝ) < (1+u)^(j+8)), one_mul]
      calc u^j * (1+u)^(j+8) ≤ (1+u)^j * (1+u)^(j+8) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu0 (by linarith) j) (by positivity)
        _ = (1+u)^(2*j+8) := by rw [← pow_add]; congr 1; omega
    have hb4 : (1 + ‖Work.BoseB4.vec n‖^2) ≤ M * (1 + u)^2 := by
      rw [hw]
      have h2 : (ℓ*u)^2 = ℓ^2 * u^2 := by ring
      rw [h2]
      have h5 : ℓ^2 * u^2 ≤ M * u^2 := mul_le_mul_of_nonneg_right hMl (sq_nonneg u)
      have h6 : 1 + ℓ^2 * u^2 ≤ M + M * u^2 := by linarith
      have h3 : (1 + u^2) ≤ (1+u)^2 := by nlinarith [hu0]
      calc 1 + ℓ^2 * u^2 ≤ M + M * u^2 := h6
        _ = M * (1 + u^2) := by ring
        _ ≤ M * (1+u)^2 := mul_le_mul_of_nonneg_left h3 (le_of_lt hMpos)
    have hb5 : ((1+u)^(j+8))⁻¹ ≤ M^3 * (((1:ℝ) + ‖Work.BoseB4.vec n‖^2)^3)⁻¹ := by
      refine inv_le_mul_inv_of_le_mul (P := (1 + ‖Work.BoseB4.vec n‖^2)^3) (Q := (1+u)^(j+8))
        (C := M^3) (by positivity) (by positivity) ?_
      calc (1 + ‖Work.BoseB4.vec n‖^2)^3 ≤ (M * (1+u)^2)^3 :=
            pow_le_pow_left₀ (by positivity) hb4 3
        _ = M^3 * (1+u)^6 := by rw [mul_pow, ← pow_mul]
        _ ≤ M^3 * (1+u)^(j+8) := by
            have hle : (1+u)^6 ≤ (1+u)^(j+8) :=
              pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+u) (by omega)
            exact mul_le_mul_of_nonneg_left hle (by positivity)
    calc (ℓ^3)⁻¹ * u^j * F^2
        ≤ (ℓ^3)⁻¹ * u^j * (K^2 / (1+u)^(2*j+8)) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = (ℓ^3)⁻¹ * K^2 * (u^j / (1+u)^(2*j+8)) := by ring
      _ ≤ (ℓ^3)⁻¹ * K^2 * (1 / (1+u)^(j+8)) :=
          mul_le_mul_of_nonneg_left hb3 (by positivity)
      _ = (ℓ^3)⁻¹ * K^2 * ((1+u)^(j+8))⁻¹ := by rw [one_div]
      _ ≤ (ℓ^3)⁻¹ * K^2 * (M^3 * (((1:ℝ) + ‖Work.BoseB4.vec n‖^2)^3)⁻¹) :=
          mul_le_mul_of_nonneg_left hb5 (by positivity)
      _ = ((ℓ^3)⁻¹ * K^2 * M^3) * (((1:ℝ) + ‖Work.BoseB4.vec n‖^2)^3)⁻¹ := by ring
  exact Summable.of_nonneg_of_le (fun n => by positivity) key (Summable.mul_left _ hsum_vec)

/-! ## The `ENNReal` bridge -/

/-- For a function `u` that is integrable on `(0,∞)` and nonnegative there, the `ℝ≥0∞`-integral of
`‖u‖ₑ` is `ENNReal.ofReal` of the Bochner integral of `u`.  This converts the side condition of
`MeasureTheory.integral_tsum` into a statement about ordinary integrals. -/
lemma lintegral_enorm_eq_ofReal_integral_Ioi {u : ℝ → ℝ} (hu : IntegrableOn u (Set.Ioi 0))
    (hu0 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] u) :
    ∫⁻ t in Set.Ioi 0, ‖u t‖ₑ = ENNReal.ofReal (∫ t in Set.Ioi 0, u t) := by
  have h1 : (∫⁻ t in Set.Ioi 0, ‖u t‖ₑ) = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (u t) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hu0] with t ht
    exact Real.enorm_eq_ofReal ht
  rw [h1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hu hu0]

/-! ## The abstract lattice subordination identity -/

/-- **Lattice heat subordination, abstract form.**  For any nonnegative summable weight
`a : (Fin 3 → ℤ) → ℝ` whose first moment `‖k_n‖ a_n` is summable,

`Σ_n ‖k_n‖ a_n = (2√π)⁻¹ ∫_0^∞ t^{-3/2} ( Σ_n a_n − Σ_n e^{-t‖k_n‖²} a_n ) dt`.

Both sides are lattice sums over the *same* momenta; the bracket is the pointwise sum
`Σ_n a_n (1 − e^{-t‖k_n‖²})`, so the identity is Tonelli applied to the per-mode subordination
`∫_0^∞ t^{-3/2}(1 − e^{-ta})dt = 2√π√a`. -/
theorem heatSubordination_lattice {ℓ : ℝ} (hℓ : 0 < ℓ) {a : (Fin 3 → ℤ) → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a)
    (hm : Summable (fun n => a n * ‖kmomInt ℓ n‖)) :
    (∑' n : Fin 3 → ℤ, ‖kmomInt ℓ n‖ * a n)
      = (2 * Real.sqrt Real.pi)⁻¹ *
          ∫ t in Set.Ioi (0:ℝ), t^(-(3:ℝ)/2) *
            ((∑' n : Fin 3 → ℤ, a n)
             - (∑' n : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ n‖^2)) * a n)) := by
  -- the heat family is summable for `t ≥ 0` (dominated by `a`).
  have hbt : ∀ t, 0 ≤ t → Summable (fun n => Real.exp (-(t * ‖kmomInt ℓ n‖^2)) * a n) := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Real.exp_nonneg _) (ha0 n))
      (fun n => ?_) ha
    have h1 : Real.exp (-(t * ‖kmomInt ℓ n‖^2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [ht, sq_nonneg ‖kmomInt ℓ n‖]
    exact mul_le_of_le_one_left (ha0 n) h1
  -- nonnegativity of the per-mode integrand on `(0,∞)`.
  have hnn : ∀ n : Fin 3 → ℤ, ∀ t ∈ Set.Ioi (0:ℝ),
      0 ≤ t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n) := by
    intro n t ht
    have ht0 : (0:ℝ) < t := ht
    refine mul_nonneg (Real.rpow_nonneg ht0.le _) (mul_nonneg ?_ (ha0 n))
    have h : Real.exp (-(t * ‖kmomInt ℓ n‖^2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [ht0.le, sq_nonneg ‖kmomInt ℓ n‖]
    linarith
  -- integrability of each per-mode integrand.
  have hinte : ∀ n : Fin 3 → ℤ, IntegrableOn (fun t : ℝ =>
      t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n)) (Set.Ioi 0) := by
    intro n
    have hb := (SqrtKin.subordination_rpow_integrableOn (‖kmomInt ℓ n‖^2)
      (sq_nonneg _)).mul_const (a n)
    refine MeasureTheory.Integrable.congr hb (Filter.Eventually.of_forall (fun t => ?_))
    ring
  -- the value of each per-mode integral.
  have hval : ∀ n : Fin 3 → ℤ,
      ∫ t in Set.Ioi (0:ℝ), t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n)
        = 2 * Real.sqrt Real.pi * (a n * ‖kmomInt ℓ n‖) := by
    intro n
    have hcongr : (∫ t in Set.Ioi (0:ℝ),
          t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n))
        = ∫ t in Set.Ioi (0:ℝ),
            a n * ((1 - Real.exp (-(‖kmomInt ℓ n‖^2 * t))) * t^(-(3:ℝ)/2)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      ring
    rw [hcongr, MeasureTheory.integral_const_mul,
      SqrtKin.subordination_rpow (‖kmomInt ℓ n‖^2) (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    ring
  -- the `ENNReal` side condition of `integral_tsum`, in terms of the per-mode integrals.
  have hE : ∀ n : Fin 3 → ℤ,
      ∫⁻ t in Set.Ioi (0:ℝ),
          ‖t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n)‖ₑ
        = ENNReal.ofReal (2 * Real.sqrt Real.pi * (a n * ‖kmomInt ℓ n‖)) := by
    intro n
    rw [lintegral_enorm_eq_ofReal_integral_Ioi (hinte n) ?_, hval n]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hnn n t ht
  have hfin : (∑' n : Fin 3 → ℤ, ∫⁻ t in Set.Ioi (0:ℝ),
      ‖t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n)‖ₑ) ≠ ⊤ := by
    rw [tsum_congr hE, ← ENNReal.ofReal_tsum_of_nonneg
      (f := fun n : Fin 3 → ℤ => 2 * Real.sqrt Real.pi * (a n * ‖kmomInt ℓ n‖))
      (fun n => mul_nonneg (by positivity) (mul_nonneg (ha0 n) (norm_nonneg _)))
      (Summable.mul_left (2 * Real.sqrt Real.pi) hm)]
    exact ENNReal.ofReal_ne_top
  -- Tonelli (`integral_tsum`) on the countably indexed nonnegative family.
  have hswap : (∫ t in Set.Ioi (0:ℝ), ∑' n : Fin 3 → ℤ,
        t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n))
      = ∑' n : Fin 3 → ℤ, ∫ t in Set.Ioi (0:ℝ),
          t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n) := by
    refine MeasureTheory.integral_tsum (μ := volume.restrict (Set.Ioi (0:ℝ))) ?_ hfin
    intro n
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · exact continuous_id.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    · refine ContinuousOn.mul ?_ continuousOn_const
      refine ContinuousOn.sub continuousOn_const ?_
      exact (Real.continuous_exp.comp
        ((continuous_id.mul continuous_const).neg)).continuousOn
  -- the pointwise identification of the bracket with the per-mode sum.
  have hpoint : ∀ t ∈ Set.Ioi (0:ℝ),
      t^(-(3:ℝ)/2) * ((∑' n : Fin 3 → ℤ, a n)
          - (∑' n : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ n‖^2)) * a n))
        = ∑' n : Fin 3 → ℤ,
            t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have h1 : (∑' n : Fin 3 → ℤ, a n)
          - (∑' n : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ n‖^2)) * a n)
        = ∑' n : Fin 3 → ℤ, (a n - Real.exp (-(t * ‖kmomInt ℓ n‖^2)) * a n) := by
      rw [Summable.tsum_sub ha (hbt t ht0)]
    have h2 : (∑' n : Fin 3 → ℤ, (a n - Real.exp (-(t * ‖kmomInt ℓ n‖^2)) * a n))
        = ∑' n : Fin 3 → ℤ, (1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n :=
      tsum_congr (fun n => by ring)
    have hc : Summable (fun n : Fin 3 → ℤ =>
        (1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n) := by
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg ?_ (ha0 n)) (fun n => ?_) ha
      · rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith [ht0, sq_nonneg ‖kmomInt ℓ n‖]
      · have h3 : 1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2)) ≤ 1 := by
          have h4 : 0 < Real.exp (-(t * ‖kmomInt ℓ n‖^2)) := Real.exp_pos _
          linarith
        calc (1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n ≤ 1 * a n :=
              mul_le_mul_of_nonneg_right h3 (ha0 n)
          _ = a n := one_mul _
    rw [h1, h2, (Summable.tsum_mul_left (t^(-(3:ℝ)/2)) hc).symm]
  have hmain : (∫ t in Set.Ioi (0:ℝ), t^(-(3:ℝ)/2) * ((∑' n : Fin 3 → ℤ, a n)
        - (∑' n : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ n‖^2)) * a n)))
      = ∑' n : Fin 3 → ℤ, 2 * Real.sqrt Real.pi * (a n * ‖kmomInt ℓ n‖) := by
    have hcongr_int : (∫ t in Set.Ioi (0:ℝ), t^(-(3:ℝ)/2) * ((∑' n : Fin 3 → ℤ, a n)
          - (∑' n : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ n‖^2)) * a n)))
        = ∫ t in Set.Ioi (0:ℝ), ∑' n : Fin 3 → ℤ,
            t^(-(3:ℝ)/2) * ((1 - Real.exp (-(t * ‖kmomInt ℓ n‖^2))) * a n) :=
      setIntegral_congr_fun measurableSet_Ioi hpoint
    rw [hcongr_int, hswap, tsum_congr hval]
  rw [hmain, Summable.tsum_mul_left (2 * Real.sqrt Real.pi) hm, ← mul_assoc,
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) (Real.sqrt_pos_of_pos Real.pi_pos).ne'), one_mul]
  exact tsum_congr (fun n => mul_comm _ _)

/-! ## The target -/

/-- **Lattice heat subordination for the box kinetic row** (the statement as requested). -/
theorem lattice_heatSubordination {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ/2)) :
    (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖^2)
      = (2 * Real.sqrt Real.pi)⁻¹ *
          ∫ t in Set.Ioi 0, t^(-3/2:ℝ) *
            ((∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹
                * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖^2)
             - (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * Real.exp (-t * ‖Work.BoseBoxFock.kmomInt ℓ n‖^2)
                * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖^2)) := by
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  have ha0 : ∀ n : Fin 3 → ℤ,
      0 ≤ (ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2 :=
    fun n => by positivity
  have ha : Summable (fun n : Fin 3 → ℤ =>
      (ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2) := by
    simpa using summable_lattice_kinFT_weight hℓ hg hgc 0
  have hm : Summable (fun n : Fin 3 → ℤ =>
      ((ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2) * ‖kmomInt ℓ n‖) := by
    refine (summable_lattice_kinFT_weight hℓ hg hgc 1).congr (fun n => ?_)
    ring
  have hkey := heatSubordination_lattice hℓ ha0 ha hm
  calc (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * ‖kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2)
      = ∑' n : Fin 3 → ℤ,
          ‖kmomInt ℓ n‖ * ((ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2) :=
        tsum_congr (fun n => by ring)
    _ = (2 * Real.sqrt Real.pi)⁻¹ *
          ∫ t in Set.Ioi (0:ℝ), t^(-(3:ℝ)/2) *
            ((∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹
                * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2)
             - (∑' n : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ n‖^2))
                * ((ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2))) := hkey
    _ = (2 * Real.sqrt Real.pi)⁻¹ *
          ∫ t in Set.Ioi (0:ℝ), t^(-3/2:ℝ) *
            ((∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹
                * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2)
             - (∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * Real.exp (-t * ‖kmomInt ℓ n‖^2)
                * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2)) := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        have h1 : (∑' n : Fin 3 → ℤ, Real.exp (-(t * ‖kmomInt ℓ n‖^2))
              * ((ℓ^3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2))
            = ∑' n : Fin 3 → ℤ, (ℓ^3)⁻¹ * Real.exp (-t * ‖kmomInt ℓ n‖^2)
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖^2 := by
          refine tsum_congr (fun n => ?_)
          rw [neg_mul]
          ring
        rw [h1]

end Work.BoseBoxFock
