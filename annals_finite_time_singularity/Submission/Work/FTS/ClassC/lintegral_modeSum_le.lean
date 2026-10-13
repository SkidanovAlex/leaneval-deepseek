/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/lintegral_modeSum_le` — the level-`0` mode-sum bound, `lintegral` form

The level-`0` `HkSq` of a finite angular mode sum `g = Σ_{m≤N} a_m(z)·e_m(θ)` satisfies

  `HkSq α 0 g ≤ 9·(∫_θ σ)·(Σ_{m≤N} (m+1)·‖a_m w‖)²`,   `σ = sEta`, `‖a_m w‖ ² = ∫_z a_m² w²`

(`ModeSumZ.HkSq_zero_modeSum_le`).  Here we record the same estimate directly in the
`ℝ≥0∞`/`lintegral` shape in which it is consumed downstream:

  `∫⁻_z ∫⁻_θ ofReal ((Σ_{m≤N} a_m(z) e_m(θ))² · w(z)² · σ(θ))
      ≤ ofReal (9·(∫_θ σ)·(Σ_{m≤N} (m+1)·‖a_m w‖)²)`,

with no `HkMem`-type hypothesis: only the integrability of the weighted radial squares
`a_m² w²` is needed (and it is needed only to make the two `lintegral`/integral collapses
`ofReal_integral_eq_lintegral_ofReal` available).

The proof is short because the pointwise sup bound of the eigenfamily
(`ModeSumZ.abs_sum_eFam_le`, `|Σ_m b_m e_m θ| ≤ 3Σ_m (m+1)|b_m|` on `Iθ`) is already
*sharp with respect to the constant `9`*: it gives

  `(Σ_{m≤N} a_m(z) e_m(θ))² ≤ 9·(Σ_{m≤N} (m+1)|a_m(z)|)²   (θ ∈ Iθ)`,

so no angular Gram/Parseval input is required.  The remaining steps are
`ofReal_mul`/`lintegral_const_mul'` to pull the constants out of the two integrals, and
`weighted_l2_modeSum` (finite-sum Minkowski in `L²(w²dz)`) for the radial part.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.ModeSumZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "eFam" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- The radial weight `w z = (1+z)²/z²` is nonnegative. -/
theorem lms_w_nonneg (z : ℝ) : 0 ≤ w z := by
  rw [Work.Spaces.w]; positivity

/-- **Integrability of the dominating radial function of the mode-sum bound.**  If every
weighted square `z ↦ a_m(z)² w(z)²` (`m ≤ N`) is integrable on `Iz`, and `0 ≤ c`, then

  `z ↦ c · (Σ_{m≤N} (m+1)|a_m(z)|)² · w(z)²`

is integrable on `Iz`.  The majorant is the `m`-Cauchy–Schwarz bound
`(Σ_m (m+1)|a_m|)² ≤ (N+1)·Σ_m (m+1)²·(a_m² w²)`, divided by `w²`. -/
theorem integrableOn_modeSum_maj (a : ℕ → ℝ → ℝ) (N : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hint : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (a m z) ^ 2 * (w z) ^ 2) Iz) :
    MeasureTheory.IntegrableOn
      (fun z => c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2
        * (w z) ^ 2) Iz := by
  classical
  have hw_nn : ∀ z : ℝ, 0 ≤ w z := lms_w_nonneg
  have hmaj_int : MeasureTheory.IntegrableOn (fun z =>
      c * ((N : ℝ) + 1) * (∑ m ∈ Finset.range (N + 1),
        ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2))) Iz :=
    (MeasureTheory.integrable_finsetSum _ fun m hm =>
      (hint m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))).const_mul _).const_mul _
  have hP_asm : AEStronglyMeasurable (fun z => ∑ m ∈ Finset.range (N + 1),
      ((m : ℝ) + 1) * Real.sqrt ((a m z) ^ 2 * (w z) ^ 2)) (volume.restrict Iz) := by
    have h := Finset.aestronglyMeasurable_sum (Finset.range (N + 1))
      (f := fun (m : ℕ) => fun (z : ℝ) => ((m : ℝ) + 1) * Real.sqrt ((a m z) ^ 2 * (w z) ^ 2))
      (fun m hm => aestronglyMeasurable_const.mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          (hint m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))).aestronglyMeasurable))
    have h2 : (∑ i ∈ Finset.range (N + 1),
          (fun z : ℝ => ((i : ℝ) + 1) * Real.sqrt ((a i z) ^ 2 * (w z) ^ 2)))
        = (fun z : ℝ => ∑ i ∈ Finset.range (N + 1),
            ((i : ℝ) + 1) * Real.sqrt ((a i z) ^ 2 * (w z) ^ 2)) := by
      funext z
      rw [Finset.sum_apply]
    rwa [h2] at h
  have hasm : AEStronglyMeasurable (fun z => c * (∑ m ∈ Finset.range (N + 1),
      ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2) (volume.restrict Iz) :=
    (aestronglyMeasurable_const.mul (hP_asm.pow 2)).congr (by
      filter_upwards with z
      show c * (∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) * Real.sqrt ((a m z) ^ 2 * (w z) ^ 2)) ^ 2
          = c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2
      have hsq : ∀ m : ℕ, Real.sqrt ((a m z) ^ 2 * (w z) ^ 2) = |a m z| * w z := by
        intro m
        rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (hw_nn z)]
      have hsum : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * (|a m z| * w z))
          = (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) * w z := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring
      rw [Finset.sum_congr rfl (fun m _ => by rw [hsq m]), hsum]
      ring)
  have hae : ∀ z : ℝ, ‖c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2
        * (w z) ^ 2‖ ≤ c * ((N : ℝ) + 1)
        * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) ^ 2
            * ((a m z) ^ 2 * (w z) ^ 2)) := by
    intro z
    have hCS : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2
        ≤ ((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) * |a m z|) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq
        (s := Finset.range (N + 1)) (f := fun m => ((m : ℝ) + 1) * |a m z|)
      simpa [Finset.card_range, Nat.cast_add, Nat.cast_one] using h
    have hnonneg : 0 ≤ c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2
        * (w z) ^ 2 :=
      mul_nonneg (mul_nonneg hc (sq_nonneg _)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have hstep : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2
        ≤ ((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1),
            ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_right hCS (sq_nonneg (w z))
      have h2 : ((N : ℝ) + 1) * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) * |a m z|) ^ 2)
            * (w z) ^ 2
          = ((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2) := by
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun m _ => by rw [mul_pow, sq_abs]; ring
      exact h2 ▸ h1
    calc c * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2
        = c * ((∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2) := by
          ring
      _ ≤ c * (((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep hc
      _ = c * ((N : ℝ) + 1) * (∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2)) := by ring
  exact hmaj_int.mono' hasm (Filter.Eventually.of_forall fun z => hae z)

/-- **The level-`0` mode-sum bound in `lintegral` form.**

  `∫⁻_z ∫⁻_θ ofReal ((Σ_{m≤N} a_m(z) e_m(θ))² · w(z)² · σ(θ))
     ≤ ofReal (9·(∫_θ σ)·(Σ_{m≤N} (m+1)·√(∫_z a_m² w²))²)`,

where `e_m = Gegenbauer.eFam m` is the Dirichlet eigenfamily and `σ = sEta`. -/
theorem lintegral_modeSum_le (a : ℕ → ℝ → ℝ) (N : ℕ)
    (hint : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1),
            a m z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ENNReal.ofReal (9 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
              * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2) := by
  classical
  set K : ℝ := ∫ θ in Iθ, sEta θ with hK
  set P : ℝ → ℝ := fun z => ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z| with hP
  set Q : ℝ → ℝ := fun z => 9 * (P z) ^ 2 * (w z) ^ 2 with hQ
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact setIntegral_nonneg measurableSet_Icc fun θ hθ => Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
  have hPnn : ∀ z, 0 ≤ P z := by
    intro z
    rw [hP]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (abs_nonneg _)
  have hQnn : ∀ z, 0 ≤ Q z := by
    intro z
    rw [hQ]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  -- the `θ`-integral of `ofReal σ`
  have hσ : ∫⁻ θ in Iθ, ENNReal.ofReal (sEta θ) = ENNReal.ofReal K := by
    rw [hK]
    refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal Work.FTS.EllipticEst.Honest.sEta_integrableOn ?_).symm
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun θ hθ => Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
  -- the pointwise angular bound `(Σ a_m e_m)² ≤ 9 P²` on `Iθ`
  have hpt : ∀ z θ, θ ∈ Iθ →
      (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ
        ≤ Q z * sEta θ := by
    intro z θ hθ
    have hsup := abs_sum_eFam_le (N := N) (b := fun m => a m z) hθ
    have hPz : P z = ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z| := by rw [hP]
    have hsq : (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 ≤ 9 * (P z) ^ 2 := by
      rw [hPz]
      calc (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2
          = |∑ m ∈ Finset.range (N + 1), a m z * eFam m θ| ^ 2 := (sq_abs _).symm
        _ ≤ (3 * ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hsup 2
        _ = 9 * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 := by ring
    have h1 : (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2
        ≤ (9 * (P z) ^ 2) * (w z) ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have h2 : (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ
        ≤ (9 * (P z) ^ 2 * (w z) ^ 2) * sEta θ := by
      calc (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ
          = ((∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2) * sEta θ := by
            ring
        _ ≤ ((9 * (P z) ^ 2) * (w z) ^ 2) * sEta θ :=
            mul_le_mul_of_nonneg_right h1 (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
        _ = (9 * (P z) ^ 2 * (w z) ^ 2) * sEta θ := by ring
    rw [hQ]
    exact h2
  -- the inner `θ`-bound, for `z ∈ Iz`
  have hinner : ∀ z ∈ Iz, (∫⁻ θ in Iθ,
      ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2
        * (w z) ^ 2 * sEta θ))
      ≤ ENNReal.ofReal (Q z) * ENNReal.ofReal K := by
    intro z hz
    have h1 : (∫⁻ θ in Iθ,
        ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2
          * (w z) ^ 2 * sEta θ))
        ≤ ∫⁻ θ in Iθ, ENNReal.ofReal (Q z * sEta θ) :=
      MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ hθ =>
        ENNReal.ofReal_le_ofReal (hpt z θ hθ)
    have h2 : (∫⁻ θ in Iθ, ENNReal.ofReal (Q z * sEta θ))
        = ∫⁻ θ in Iθ, ENNReal.ofReal (Q z) * ENNReal.ofReal (sEta θ) :=
      MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun θ hθ =>
        ENNReal.ofReal_mul (hQnn z)
    have h3 : (∫⁻ θ in Iθ, ENNReal.ofReal (Q z) * ENNReal.ofReal (sEta θ))
        = ENNReal.ofReal (Q z) * ∫⁻ θ in Iθ, ENNReal.ofReal (sEta θ) :=
      MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Q z))
        (fun θ => ENNReal.ofReal (sEta θ)) ENNReal.ofReal_ne_top
    rw [h2] at h1
    rw [h3, hσ] at h1
    exact h1
  -- integrability of the dominating radial function
  have hQint : MeasureTheory.IntegrableOn Q Iz := by
    have h := integrableOn_modeSum_maj a N (c := 9) (by norm_num) hint
    simpa only [hQ, hP] using h
  have hQae : 0 ≤ᵐ[volume.restrict Iz] Q :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).2
      (Filter.Eventually.of_forall fun z hz => hQnn z)
  have hQlin : (∫⁻ z in Iz, ENNReal.ofReal (Q z)) = ENNReal.ofReal (∫ z in Iz, Q z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hQint hQae).symm
  -- the radial part, by finite-sum Minkowski
  have hM_le : (∫ z in Iz, Q z) ≤ 9 * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
      * Real.sqrt (∫ z in Iz, (a m z) ^ 2 * (w z) ^ 2)) ^ 2 := by
    have hweighted := weighted_l2_modeSum (N := N) (a := a) (c := fun m => ((m : ℝ) + 1))
      (fun m => by positivity) hint
    have hfunext : Q = fun z => 9 * ((w z) ^ 2 * (P z) ^ 2) := by
      funext z
      rw [hQ]
      ring
    rw [hfunext, MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    simpa only [hP] using hweighted
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1),
            a m z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ∫⁻ z in Iz, ENNReal.ofReal (Q z) * ENNReal.ofReal K :=
        MeasureTheory.setLIntegral_mono' measurableSet_Ici hinner
    _ = ENNReal.ofReal K * ∫⁻ z in Iz, ENNReal.ofReal (Q z) := by
        rw [show (fun z => ENNReal.ofReal (Q z) * ENNReal.ofReal K)
            = fun z => ENNReal.ofReal K * ENNReal.ofReal (Q z) from by
          funext z; rw [mul_comm]]
        exact MeasureTheory.lintegral_const_mul' (ENNReal.ofReal K)
          (fun z => ENNReal.ofReal (Q z)) ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal K * ENNReal.ofReal (∫ z in Iz, Q z) := by rw [hQlin]
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (9 * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
          * Real.sqrt (∫ z in Iz, (a m z) ^ 2 * (w z) ^ 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hM_le)
          (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal K)
    _ = ENNReal.ofReal (9 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
              * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2) := by
        rw [← ENNReal.ofReal_mul hKnn]
        congr 1
        rw [hK]
        ring

end Work.FTS.ClassC
