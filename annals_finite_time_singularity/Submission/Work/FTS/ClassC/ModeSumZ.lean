/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/ModeSumZ` — the level-`0` `HkSq` of a finite angular mode sum

The level-`0` `ℋ`-integrand of the paper carries no derivative, so (`HkSq_zero_eq_w`)

  `HkSq α 0 g = ∫_z ∫_θ (g z θ)² · w(z)² · sEta θ`,   `sEta θ = sin(2θ)^{-η}`.

For a *finite angular mode sum* `g = Σ_{m≤N} a_m(z)·e_m(θ)` of the Dirichlet eigenfamily
`e_m = Gegenbauer.eFam m`, this file bounds that quantity in terms of the weighted `L²` norms
`‖a_m w‖ = √(∫_z a_m² w²)` of the radial coefficients:

  `HkSq α 0 (Σ_{m≤N} a_m e_m) ≤ K · (Σ_{m≤N} (m+1)·‖a_m w‖)²`,   `K = 9·∫_θ sin(2θ)^{-η}`
  (`HkSq_zero_modeSum_le`).

The proof is completely elementary and splits into the two dispatched steps:

* `angGram_modeSum` (angular): `∫_θ (Σ_m b_m e_m θ)² σ ≤ 9(∫_θ σ)(Σ_m (m+1)|b_m|)²`, which rests
  on the linear sup bound `|eFam m θ| ≤ 3(m+1)` of `Series/eFam_energy_bound` (also recorded here
  as `abs_eFam_le`/`abs_sum_eFam_le`);
* `weighted_l2_modeSum` (radial): finite-sum Minkowski in `L²(w²dz)`,
  `∫_z w²(Σ_m c_m|a_m|)² ≤ (Σ_m c_m ‖a_m w‖)²`.

The one piece of bookkeeping that is not purely elementary is the *integrability* of the
dominating `z`-function `9(∫_θ σ)(Σ_{m≤N}(m+1)|a_m z|)²w(z)²`, which is bounded by
`9(∫_θ σ)(N+1)Σ_{m≤N}(m+1)²a_m(z)²w(z)²` (Cauchy–Schwarz in `m`).

Consumed by the modal route to the level-`0` honesty of `Ψ = Σ_m a_m e_m`: combining
`HkSq_zero_modeSum_le` with the per-mode bound `μ_m‖a_m w‖ ≤ ‖c_m w‖` (`ModeEnergyCS.lean`) and
the Bessel/Plancherel bound `Σ_{m≤N} n_m‖c_m w‖² ≤ HkSq α 0 F` (the source's own honesty) gives
`HkSq α 0 Ψ_N ≤ C·HkSq α 0 F`, uniformly in `N`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Series.eFam_energy_bound
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.ClassC.angGram_modeSum
import Submission.Work.FTS.ClassC.weighted_l2_modeSum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "eFam" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-! ## The sharp linear sup bound for the eigenfamily -/

/-- **`|eFam m θ| ≤ 3(m+1)` on `Iθ`.**  The interior is `EB.eFam_abs_le_sqrt_N`; at `θ = 0`
the Gegenbauer polynomial `gC (2m+1)` is odd hence vanishes, and at `θ = π/2` the factor
`cos θ` vanishes. -/
theorem abs_eFam_le (m : ℕ) {θ : ℝ} (hθ : θ ∈ Iθ) : |eFam m θ| ≤ 3 * ((m : ℝ) + 1) := by
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · have h := Work.FTS.PhiStar.Series.EB.eFam_abs_le_sqrt_N m ⟨h0, h1⟩
      have hN : Work.FTS.PhiStar.Series.EB.Npsi m ≤ (3 * ((m : ℝ) + 1)) ^ 2 := by
        rw [Work.FTS.PhiStar.Series.EB.Npsi]
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith
      calc |eFam m θ| ≤ Real.sqrt (Work.FTS.PhiStar.Series.EB.Npsi m) := h
        _ ≤ Real.sqrt ((3 * ((m : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt hN
        _ = 3 * ((m : ℝ) + 1) := Real.sqrt_sq (by positivity)
    · subst h1
      have hz : eFam m (Real.pi / 2) = 0 := by
        simp [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two]
      rw [hz, abs_zero]
      positivity
  · subst h0
    have hz : eFam m 0 = 0 := by
      simp [Work.FTS.PhiStar.Gegenbauer.eFam,
        Work.FTS.PhiStar.Gegenbauer.gC_odd_zero m]
    rw [hz, abs_zero]
    positivity

/-- **The sup bound for a finite mode sum**: `|Σ_{m≤N} b_m e_m θ| ≤ 3·Σ_{m≤N}(m+1)|b_m|`. -/
theorem abs_sum_eFam_le {N : ℕ} (b : ℕ → ℝ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    |∑ m ∈ Finset.range (N + 1), b m * eFam m θ|
      ≤ 3 * ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |b m| := by
  calc |∑ m ∈ Finset.range (N + 1), b m * eFam m θ|
      ≤ ∑ m ∈ Finset.range (N + 1), |b m * eFam m θ| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ Finset.range (N + 1), |b m| * |eFam m θ| :=
        Finset.sum_congr rfl fun m _ => abs_mul _ _
    _ ≤ ∑ m ∈ Finset.range (N + 1), |b m| * (3 * ((m : ℝ) + 1)) :=
        Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_left (abs_eFam_le m hθ) (abs_nonneg _)
    _ = 3 * ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |b m| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring

/-! ## `HkSq α 0` as an explicit weighted double integral -/

/-- **`HkSq α 0` in terms of `w²` and `sEta`.** -/
theorem HkSq_zero_eq_w (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Iz, ∫ θ in Iθ, (g z θ) ^ 2 * (w z) ^ 2 * sEta θ := by
  rw [Work.FTS.EllipticEst.Honest.HkSq_zero_eq]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
    (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ)]
  rfl

/-! ## The assembly -/

/-- **The level-`0` `HkSq` of a finite mode sum.**  With `‖a_m w‖ = √(∫_z a_m² w²)`,

  `HkSq α 0 (Σ_{m≤N} a_m e_m) ≤ 9·(∫_θ σ)·(Σ_{m≤N} (m+1)·‖a_m w‖)²`. -/
theorem HkSq_zero_modeSum_le (α : ℝ) (a : ℕ → ℝ → ℝ) (N : ℕ)
    (hint : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (a m z) ^ 2 * (w z) ^ 2) Iz) :
    Work.Spaces.HkSq α 0 (fun z θ => ∑ m ∈ Finset.range (N + 1), a m z * eFam m θ)
      ≤ 9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
              * Real.sqrt (∫ z in Iz, (a m z) ^ 2 * (w z) ^ 2)) ^ 2 := by
  rw [HkSq_zero_eq_w]
  have hK0 : 0 ≤ ∫ θ in Iθ, sEta θ :=
    setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
  -- the inner (angular) bound, for every `z`
  have hinner : ∀ z, (∫ θ in Iθ,
        (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ)
      ≤ (9 * (∫ θ in Iθ, sEta θ))
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2 := by
    intro z
    have hAG := angGram_modeSum (N := N) (b := fun m => a m z)
    have hswap : (∫ θ in Iθ,
          (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ)
        = (w z) ^ 2 * (∫ θ in Iθ,
            (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * sEta θ) := by
      rw [← MeasureTheory.integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring
    rw [hswap]
    calc (w z) ^ 2 * (∫ θ in Iθ,
            (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * sEta θ)
        ≤ (w z) ^ 2 * (9 * (∫ θ in Iθ, sEta θ)
            * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2) :=
          mul_le_mul_of_nonneg_left hAG (sq_nonneg _)
      _ = (9 * (∫ θ in Iθ, sEta θ))
            * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2 := by ring
  -- the pointwise domination of the dominating `z`-function
  have hw_nn : ∀ z : ℝ, 0 ≤ w z := fun z => by rw [Work.Spaces.w]; positivity
  have hmaj_int : MeasureTheory.IntegrableOn (fun z =>
      (9 * (∫ θ in Iθ, sEta θ)) * ((N : ℝ) + 1)
        * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2))) Iz :=
    (MeasureTheory.integrable_finset_sum _ fun m hm =>
      (hint m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))).const_mul _).const_mul _
  have hae : ∀ z : ℝ,
      ‖(9 * (∫ θ in Iθ, sEta θ))
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2‖
        ≤ (9 * (∫ θ in Iθ, sEta θ)) * ((N : ℝ) + 1)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2)) := by
    intro z
    have hCS : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2
        ≤ ((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) * |a m z|) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq
        (s := Finset.range (N + 1)) (f := fun m => ((m : ℝ) + 1) * |a m z|)
      simpa [Finset.card_range, Nat.cast_add, Nat.cast_one] using h
    have hC0 : 0 ≤ 9 * (∫ θ in Iθ, sEta θ) := by linarith [hK0]
    have hnonneg : 0 ≤ (9 * (∫ θ in Iθ, sEta θ))
        * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2 := by positivity
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
    calc (9 * (∫ θ in Iθ, sEta θ))
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2
        = (9 * (∫ θ in Iθ, sEta θ))
            * ((∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2) := by
          ring
      _ ≤ (9 * (∫ θ in Iθ, sEta θ)) * (((N : ℝ) + 1) * ∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep hC0
      _ = (9 * (∫ θ in Iθ, sEta θ)) * ((N : ℝ) + 1)
            * (∑ m ∈ Finset.range (N + 1),
                ((m : ℝ) + 1) ^ 2 * ((a m z) ^ 2 * (w z) ^ 2)) := by ring
  -- a.e. strong measurability, through `|a m z| w z = √(a m z² · w z²)`
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
  have hasm : AEStronglyMeasurable (fun z => (9 * (∫ θ in Iθ, sEta θ))
      * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2)
      (volume.restrict Iz) :=
    (aestronglyMeasurable_const.mul (hP_asm.pow 2)).congr (by
      filter_upwards with z
      show (9 * (∫ θ in Iθ, sEta θ))
          * (∑ m ∈ Finset.range (N + 1),
              ((m : ℝ) + 1) * Real.sqrt ((a m z) ^ 2 * (w z) ^ 2)) ^ 2
        = (9 * (∫ θ in Iθ, sEta θ))
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2
      have hsq : ∀ m : ℕ, Real.sqrt ((a m z) ^ 2 * (w z) ^ 2) = |a m z| * w z := by
        intro m
        rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (hw_nn z)]
      have hsum : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * (|a m z| * w z))
          = (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) * w z := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring
      rw [Finset.sum_congr rfl (fun m _ => by rw [hsq m]), hsum]
      ring)
  have hdom_int : MeasureTheory.IntegrableOn
      (fun z => (9 * (∫ θ in Iθ, sEta θ))
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2) Iz :=
    hmaj_int.mono' hasm (Filter.Eventually.of_forall fun z => hae z)
  -- the outer monotonicity
  have houter : (∫ z in Iz, ∫ θ in Iθ,
        (∑ m ∈ Finset.range (N + 1), a m z * eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ)
      ≤ ∫ z in Iz, (9 * (∫ θ in Iθ, sEta θ))
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2 := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_)
      hdom_int (Filter.Eventually.of_forall fun z => ?_)
    · exact setIntegral_nonneg measurableSet_Icc fun θ hθ => by
        have := Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
        positivity
    · exact hinner z
  refine le_trans houter ?_
  have hpull : (∫ z in Iz, (9 * (∫ θ in Iθ, sEta θ))
        * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2)
      = 9 * (∫ θ in Iθ, sEta θ)
        * (∫ z in Iz, (w z) ^ 2
            * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2) := by
    have hfunext : (fun z => (9 * (∫ θ in Iθ, sEta θ))
        * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2 * (w z) ^ 2)
        = fun z => (9 * (∫ θ in Iθ, sEta θ))
            * ((w z) ^ 2 * (∑ m ∈ Finset.range (N + 1),
                ((m : ℝ) + 1) * |a m z|) ^ 2) := by
      funext z; ring
    rw [hfunext]
    exact MeasureTheory.integral_const_mul (9 * (∫ θ in Iθ, sEta θ))
      (fun z => (w z) ^ 2 * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |a m z|) ^ 2)
  rw [hpull]
  exact mul_le_mul_of_nonneg_left
    (weighted_l2_modeSum (N := N) (a := a) (c := fun m => ((m : ℝ) + 1))
      (fun m => by positivity) hint)
    (by positivity)

end Work.FTS.ClassC
