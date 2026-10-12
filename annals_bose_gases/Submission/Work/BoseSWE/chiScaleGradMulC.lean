import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseSWE.chiScaleGlaeser
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `χ_{B(u)}`-wedge bound for the scaled bump: `Work.BoseSWE.chiScaleGradMulC`

The statement is

    ∃ K, 0 ≤ K ∧ ∀ ℓ d > 0, ∀ u,
      ∫ x, ‖∇(chiScale ℓ) x‖² · χ_M((ℓd)⁻¹•x − u)²
        ≤ K·(ℓ⁻¹)²·√(chiMass M ℓ d u)·(ℓd)^{3/2} ,

where `chiScale ℓ = χ(ℓ⁻¹ • ·)` is the corpus bump at scale `ℓ`, `χ_M` is the FS cosine bump
(`∫χ_M² = 1`) and `chiMass M ℓ d u = ∫ χ_{B(u)}(x)² dx` is the mass of the two-factor cutoff
`χ_{B(u)} = chiScale ℓ · χ_M((ℓd)⁻¹• · − u)` (`Submission.BoseGases.chiSmallB`).

The constant is `K = 2N` with `N` the Glaeser constant of `Work.BoseSWE.chiScaleGlaeser`, and the
proof is three lines of analysis:

1. **Glaeser + monotoneity.**  `‖∇(chiScale ℓ) x‖² ≤ 2(N/ℓ²)·chiScale ℓ x` pointwise
   (`chiScaleGlaeser`), so
   `∫ ‖∇A‖² B² ≤ 2(N/ℓ²)·∫ A·B²` with `B = χ_M((ℓd)⁻¹• · − u)`.
2. **Cauchy–Schwarz** on the pair `(A·B, B)`: `∫ A·B² ≤ √(∫ (A·B)²)·√(∫ B²)`, i.e.
   `≤ √(chiMass M ℓ d u)·√((ℓd)³)`.
3. **The `χ_M`-normalisation** `∫ B² = (ℓd)³` (Haar dilation + translation invariance +
   `∫χ_M² = 1`) and `√((ℓd)³) = (ℓd)^{3/2}`.

Note that the two integrals are *exactly* the two quantities appearing in the statement, so no
support/`sup` information is used: the bound is insensitive to the relative position of `u` and
the `ℓ`-ball, and degenerates correctly when `chiMass = 0` (then `A·B ≡ 0` by continuity and the
left-hand side vanishes by step 1).
-/

open MeasureTheory Metric
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## Cauchy–Schwarz for the Bochner integral of two `L²` functions -/

/-- **Cauchy–Schwarz**, in the form used below: for `F, G ≥ 0` in `L²`,
`∫ F G ≤ √(∫ F²)·√(∫ G²)` (Hölder with `p = q = 2`). -/
lemma integral_mul_le_sqrt_mul_sqrt {F G : E3 → ℝ}
    (hFnn : ∀ x, 0 ≤ F x) (hGnn : ∀ x, 0 ≤ G x)
    (hF : MeasureTheory.MemLp F 2 (volume : Measure E3))
    (hG : MeasureTheory.MemLp G 2 (volume : Measure E3)) :
    (∫ x : E3, F x * G x) ≤ Real.sqrt (∫ x : E3, F x ^ 2) * Real.sqrt (∫ x : E3, G x ^ 2) := by
  have hH := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure E3))
    (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hFnn) (Filter.Eventually.of_forall hGnn)
    (by simpa using hF) (by simpa using hG)
  have hF2 : (∫ x : E3, F x ^ (2 : ℝ)) = ∫ x : E3, F x ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact Real.rpow_two (F x)
  have hG2 : (∫ x : E3, G x ^ (2 : ℝ)) = ∫ x : E3, G x ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact Real.rpow_two (G x)
  rw [hF2, hG2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  exact hH

/-- The square root of a cube is the `3/2`-power: `√(x³) = x^{3/2}` for `x ≥ 0`. -/
lemma sqrt_cube_eq_rpow {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x ^ 3) = x ^ (3 / 2 : ℝ) := by
  calc Real.sqrt (x ^ 3) = (x ^ 3) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    _ = x ^ (3 / 2 : ℝ) := by
      rw [show (x ^ 3) = x ^ (3 : ℝ) from (Real.rpow_ofNat x 3).symm, ← Real.rpow_mul hx]
      norm_num

/-! ## The `χ_M`-factor: continuity, compact support, dilation normalisation -/

/-- `χ_M(z) ≠ 0` forces the unnormalised bump nonzero (so the support bounds apply). -/
lemma chiSmallBase_ne_zero_of_chiSmall_ne_zero {M : ℕ} {z : E3}
    (hz : Submission.BoseGases.chiSmall M z ≠ 0) :
    Submission.BoseGases.chiSmallBase M z ≠ 0 := by
  intro h0
  exact hz (by simp [Submission.BoseGases.chiSmall, h0])

/-- Continuity of the dilated-translated `χ_M`-factor `x ↦ χ_M(R⁻¹•x − u)`. -/
lemma continuous_chiSmall_comp_inv_smul_sub {M : ℕ} (hM : 1 ≤ M) (R : ℝ) (u : E3) :
    Continuous (fun x : E3 => Submission.BoseGases.chiSmall M (R⁻¹ • x - u)) :=
  (Submission.BoseGases.chiSmall_continuous hM).comp
    ((continuous_id.const_smul R⁻¹).sub continuous_const)

/-- Compact support of the dilated-translated `χ_M`-factor: a nonzero value forces
`‖R⁻¹•x − u‖ ≤ 1`, hence `‖x‖ ≤ R(1 + ‖u‖)`. -/
lemma hasCompactSupport_chiSmall_comp_inv_smul_sub {M : ℕ} (hM : 1 ≤ M) {R : ℝ} (hR : 0 < R)
    (u : E3) :
    HasCompactSupport (fun x : E3 => Submission.BoseGases.chiSmall M (R⁻¹ • x - u)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall (0 : E3) (R * (1 + ‖u‖))) (isCompact_closedBall _ _) ?_
  intro x hx
  rw [Function.mem_support] at hx
  have hb : Submission.BoseGases.chiSmallBase M (R⁻¹ • x - u) ≠ 0 :=
    chiSmallBase_ne_zero_of_chiSmall_ne_zero hx
  have h1 : ‖R⁻¹ • x - u‖ ≤ 1 := Submission.BoseGases.chiSmallBase_support_norm_le hM hb
  have h2 : ‖R⁻¹ • x‖ ≤ 1 + ‖u‖ := by
    calc ‖R⁻¹ • x‖ = ‖(R⁻¹ • x - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖R⁻¹ • x - u‖ + ‖u‖ := norm_add_le _ _
      _ ≤ 1 + ‖u‖ := by linarith
  have h3 : R⁻¹ * ‖x‖ ≤ 1 + ‖u‖ := by
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)] at h2
  have h4 : ‖x‖ ≤ R * (1 + ‖u‖) := by
    have := mul_le_mul_of_nonneg_left h3 (le_of_lt hR)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hR), one_mul] at this
  simpa [Metric.mem_closedBall, dist_eq_norm] using h4

/-- **The dilation-translation normalisation of the `χ_M`-factor**:
`∫ x, χ_M(R⁻¹•x − u)² dx = R³` for `R > 0` (Haar dilation, translation invariance, `∫χ_M² = 1`). -/
lemma integral_chiSmall_comp_inv_smul_sub_sq {M : ℕ} (hM : 1 ≤ M) {R : ℝ} (hR : 0 < R)
    (u : E3) :
    (∫ x : E3, (Submission.BoseGases.chiSmall M (R⁻¹ • x - u)) ^ 2) = R ^ 3 := by
  have hcomp := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure E3)
    (fun y : E3 => (Submission.BoseGases.chiSmall M (y - u)) ^ 2) (R := R) (le_of_lt hR)
  have hfr : Module.finrank ℝ E3 = 3 := by rw [finrank_euclideanSpace, Fintype.card_fin]
  rw [hfr, smul_eq_mul] at hcomp
  rw [MeasureTheory.integral_sub_right_eq_self
      (fun z : E3 => (Submission.BoseGases.chiSmall M z) ^ 2) u,
    Submission.BoseGases.chiSmall_L2 hM, mul_one] at hcomp
  exact hcomp

/-! ## The two-factor cutoff `χ_{B(u)}` -/

/-- Continuity of the two-factor cutoff. -/
lemma continuous_chiSmallB' {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3) :
    Continuous (Submission.BoseGases.chiSmallB M ℓ d u) := by
  refine Continuous.mul ?_ ?_
  · exact Submission.BoseGases.chiScale_continuous ℓ
  · exact continuous_chiSmall_comp_inv_smul_sub hM (ℓ * d) u

/-- Compact support of the two-factor cutoff (contained in the support of `chiScale ℓ`). -/
lemma hasCompactSupport_chiSmallB' {M : ℕ} (_hM : 1 ≤ M) {ℓ : ℝ} (hℓ : 0 < ℓ) (d : ℝ)
    (u : E3) : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) := by
  unfold Submission.BoseGases.chiSmallB
  exact (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).mul_right
    (f' := fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))

/-! ## Step 1: Glaeser plus monotoneity -/

/-- **Glaeser + monotoneity**: the pointwise Glaeser bound for `chiScale ℓ` turns the
`‖∇chiScale ℓ‖²·χ_M²`-integral into `2(N/ℓ²)` times the `chiScale ℓ · χ_M²`-integral. -/
lemma glaeser_integrand_le {M : ℕ} (hM : 1 ≤ M) {N ℓ d : ℝ} (hℓ : 0 < ℓ) {u : E3}
    (hgl : ∀ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
      ≤ 2 * (N / ℓ ^ 2) * Submission.BoseGases.chiScale ℓ x) :
    (∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2)
      ≤ 2 * (N / ℓ ^ 2) * ∫ x : E3, Submission.BoseGases.chiScale ℓ x
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 := by
  set B : E3 → ℝ := fun x => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) with hB
  have hcont : Continuous (fun x : E3 => Submission.BoseGases.chiScale ℓ x * (B x) ^ 2) :=
    (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((continuous_chiSmall_comp_inv_smul_sub hM (ℓ * d) u).pow 2)
  have hcs : HasCompactSupport (fun x : E3 => Submission.BoseGases.chiScale ℓ x * (B x) ^ 2) :=
    (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).mul_right
      (f' := fun x : E3 => (B x) ^ 2)
  have hpt : ∀ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2 * (B x) ^ 2
      ≤ (2 * (N / ℓ ^ 2)) * (Submission.BoseGases.chiScale ℓ x * (B x) ^ 2) := by
    intro x
    have h := mul_le_mul_of_nonneg_right (hgl x) (sq_nonneg (B x))
    calc ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2 * (B x) ^ 2
        ≤ (2 * (N / ℓ ^ 2) * Submission.BoseGases.chiScale ℓ x) * (B x) ^ 2 := h
      _ = (2 * (N / ℓ ^ 2)) * (Submission.BoseGases.chiScale ℓ x * (B x) ^ 2) := by ring
  calc (∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2 * (B x) ^ 2)
      ≤ ∫ x : E3, (2 * (N / ℓ ^ 2)) * (Submission.BoseGases.chiScale ℓ x * (B x) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
          ((hcont.integrable_of_hasCompactSupport hcs).const_mul _)
          (Filter.Eventually.of_forall hpt)
    _ = 2 * (N / ℓ ^ 2) * ∫ x : E3, Submission.BoseGases.chiScale ℓ x * (B x) ^ 2 :=
        MeasureTheory.integral_const_mul _ _

/-! ## Step 2: Cauchy–Schwarz against the `chiMass` -/

/-- **The `chiScale ℓ·χ_M²`-integral against `√chiMass·√(ℓd)³`**, by Cauchy–Schwarz on the pair
`(chiSmallB, χ_M)` together with the two exact normalisations `∫chiSmallB² = chiMass` and
`∫χ_M² = (ℓd)³`. -/
lemma int_chiScale_mul_sq_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) :
    (∫ x : E3, Submission.BoseGases.chiScale ℓ x
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2)
      ≤ Real.sqrt (Work.SmallBoxSliding.chiMass M ℓ d u) * Real.sqrt ((ℓ * d) ^ 3) := by
  have hRpos : 0 < ℓ * d := mul_pos hℓ hd
  set B : E3 → ℝ := fun x => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) with hB
  have hBmem : MeasureTheory.MemLp B 2 (volume : Measure E3) :=
    (continuous_chiSmall_comp_inv_smul_sub hM (ℓ * d) u).memLp_of_hasCompactSupport
      (hasCompactSupport_chiSmall_comp_inv_smul_sub hM hRpos u)
  have hABmem : MeasureTheory.MemLp (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) 2
      (volume : Measure E3) :=
    (continuous_chiSmallB' hM ℓ d u).memLp_of_hasCompactSupport
      (hasCompactSupport_chiSmallB' hM hℓ d u)
  have hnonneg : ∀ x : E3, 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x := fun x =>
    mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x) (Submission.BoseGases.chiSmall_nonneg M _)
  have hcs := integral_mul_le_sqrt_mul_sqrt
    (F := fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) (G := B)
    hnonneg (fun x => Submission.BoseGases.chiSmall_nonneg M _) hABmem hBmem
  have h1 : (∫ x : E3, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
      = Work.SmallBoxSliding.chiMass M ℓ d u := by
    rw [Work.SmallBoxSliding.chiMass_def]
  have h2 : (∫ x : E3, (B x) ^ 2) = (ℓ * d) ^ 3 :=
    integral_chiSmall_comp_inv_smul_sub_sq hM hRpos u
  rw [h1, h2] at hcs
  have hpt : ∀ x : E3, Submission.BoseGases.chiScale ℓ x * (B x) ^ 2
      = Submission.BoseGases.chiSmallB M ℓ d u x * B x := by
    intro x
    simp only [Submission.BoseGases.chiSmallB, hB, pow_two]
    ring
  calc (∫ x : E3, Submission.BoseGases.chiScale ℓ x * (B x) ^ 2)
      = ∫ x : E3, Submission.BoseGases.chiSmallB M ℓ d u x * B x :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ ≤ Real.sqrt (Work.SmallBoxSliding.chiMass M ℓ d u) * Real.sqrt ((ℓ * d) ^ 3) := hcs

/-! ## The target -/

theorem chiScaleGradMulC {M : ℕ} (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        (∫ x : EuclideanSpace ℝ (Fin 3),
            ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
              * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2)
          ≤ K * (ℓ⁻¹) ^ 2 * Real.sqrt (Work.SmallBoxSliding.chiMass M ℓ d u)
              * (ℓ * d) ^ (3 / 2 : ℝ) := by
  obtain ⟨N, hNnn, hgl⟩ := chiScaleGlaeser
  refine ⟨2 * N, mul_nonneg (by norm_num) hNnn, ?_⟩
  intro ℓ d hℓ hd u
  have hRpos : 0 < ℓ * d := mul_pos hℓ hd
  have h2N : 0 ≤ 2 * (N / ℓ ^ 2) := by
    have : 0 ≤ N / ℓ ^ 2 := div_nonneg hNnn (sq_nonneg ℓ)
    linarith
  have hkey : 2 * (N / ℓ ^ 2) = 2 * N * (ℓ⁻¹) ^ 2 := by
    rw [div_eq_mul_inv, inv_pow]
    ring
  have hsqrt : Real.sqrt ((ℓ * d) ^ 3) = (ℓ * d) ^ (3 / 2 : ℝ) :=
    sqrt_cube_eq_rpow (le_of_lt hRpos)
  calc (∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2)
      ≤ 2 * (N / ℓ ^ 2) * ∫ x : E3, Submission.BoseGases.chiScale ℓ x
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 :=
        glaeser_integrand_le hM hℓ (hgl ℓ hℓ)
    _ ≤ 2 * (N / ℓ ^ 2) * (Real.sqrt (Work.SmallBoxSliding.chiMass M ℓ d u)
          * Real.sqrt ((ℓ * d) ^ 3)) :=
        mul_le_mul_of_nonneg_left (int_chiScale_mul_sq_le hM hℓ hd u) h2N
    _ = 2 * N * (ℓ⁻¹) ^ 2 * Real.sqrt (Work.SmallBoxSliding.chiMass M ℓ d u)
          * (ℓ * d) ^ (3 / 2 : ℝ) := by
        rw [hkey, hsqrt]
        ring

end Work.BoseSWE
