/-
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`0` assembly of the elliptic estimate: `‖α² z²∂_zzΨ‖_ρ ≤ C·(RHS)`

This module proves `Work.FTS.EllipticEst.Honest.HkSqAssembly`: for every honest pair
`(F,Ψ)` (in the sense of `Honest.Basic`) whose `Ψ`, `z∂_zΨ` are honest, the level-`0`
`H^k`-square of `α² z²∂_zzΨ` is bounded by a universal constant times the sum of the
level-`0` squares of

`F`, `z∂_zΨ`, `∂_θθΨ`, `∂_θ(tan θ · Ψ)`, `Ψ`.

The mathematics is the pointwise rearrangement of `(PolarBSL)`
(`Hon.eq_solve`)

  `α² z²∂_zzΨ = -F - α(5+α)·z∂_zΨ - ∂_θθΨ + ∂_θ(tan θ·Ψ) - 6Ψ`   on the open quadrant

together with the five-term Cauchy–Schwarz inequality `(Σ aᵢ)² ≤ 5 Σ aᵢ²` and the fact
that the level-`0` `HkIntegrand` is the square of the weighted profile
(`HkIntegrand_zero_eq`).  The only non-trivial side condition is the angular weight
vanishing on the boundary `z = 0`, `sin 2θ = 0` of the closed quadrant; there the
integrand is `0` on both sides.

The two reusable ingredients are stated separately below:
* `HkIntegrand_zero_le_five` — the pointwise five-term domination;
* `HkSq_zero_le_sum_five` — the integration of a pointwise five-term domination.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonMemU.honMemPthTan
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option maxHeartbeats 1000000

/-! ## Elementary algebra -/

/-- **Five-term Cauchy–Schwarz**: `(a+b+c+d+e)² ≤ 5(a²+b²+c²+d²+e²)`. -/
lemma sq_sum_five_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (d - e)]

/-- Linearity of the integral over five summands. -/
lemma integral_add_five {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f1 f2 f3 f4 f5 : α → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) :
    (∫ a, f1 a + f2 a + f3 a + f4 a + f5 a ∂μ)
      = (∫ a, f1 a ∂μ) + (∫ a, f2 a ∂μ) + (∫ a, f3 a ∂μ) + (∫ a, f4 a ∂μ)
        + (∫ a, f5 a ∂μ) := by
  rw [MeasureTheory.integral_add (f := fun a => f1 a + f2 a + f3 a + f4 a) (g := f5)
        (((h1.add h2).add h3).add h4) h5,
      MeasureTheory.integral_add (f := fun a => f1 a + f2 a + f3 a) (g := f4)
        ((h1.add h2).add h3) h4,
      MeasureTheory.integral_add (f := fun a => f1 a + f2 a) (g := f3) (h1.add h2) h3,
      MeasureTheory.integral_add (f := f1) (g := f2) h1 h2]

/-! ## The level-`0` integrand -/

/-- The level-`0` `HkIntegrand` is the square of `|g|` times the level-`0` weight
`w z / sin(2θ)^{η/2}`. -/
lemma HkIntegrand_zero_eq_abs (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (|g z θ| * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [HkIntegrand_zero_eq, mul_pow, mul_pow, sq_abs]

/-- The level-`0` `HkIntegrand` vanishes on the angular boundary `sin(2θ) = 0`. -/
lemma HkIntegrand_zero_of_sin_eq_zero (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [HkIntegrand_zero_eq]
  have hsin : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  rw [hsin, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-! ## The pointwise five-term domination -/

/-- **The pointwise five-term Cauchy–Schwarz for the level-`0` integrand.**  If
`|u| ≤ |g₁| + ⋯ + |g₅|` on the *open* quadrant, then on the *closed* quadrant the level-`0`
`HkIntegrand` of `u` is dominated by `5` times the sum of the `HkIntegrand`s of the `gᵢ`.

On the open quadrant this is `sq_sum_five_le` applied after multiplying by the nonnegative
weight `w z / sin(2θ)^{η/2}`; on the boundary `z = 0` or `sin 2θ = 0` the integrand is `0`
on both sides. -/
theorem HkIntegrand_zero_le_five {α : ℝ} {u g1 g2 g3 g4 g5 : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |u z θ| ≤ |g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ + Work.Spaces.HkIntegrand α 0 g2 z θ
              + Work.Spaces.HkIntegrand α 0 g3 z θ + Work.Spaces.HkIntegrand α 0 g4 z θ
              + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
  have hnn : ∀ z θ, 0 ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ
      + Work.Spaces.HkIntegrand α 0 g2 z θ + Work.Spaces.HkIntegrand α 0 g3 z θ
      + Work.Spaces.HkIntegrand α 0 g4 z θ + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
    intro z θ
    have h1 := Work.Spaces.HkIntegrand_nonneg α 0 g1 z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α 0 g2 z θ
    have h3 := Work.Spaces.HkIntegrand_nonneg α 0 g3 z θ
    have h4 := Work.Spaces.HkIntegrand_nonneg α 0 g4 z θ
    have h5 := Work.Spaces.HkIntegrand_nonneg α 0 g5 z θ
    linarith
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0, Work.Spaces.HkIntegrand_zero_z]
    exact hnn 0 θ
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [HkIntegrand_zero_of_sin_eq_zero α u hs]
      exact hnn z θ
    · -- the open quadrant
      have hθb : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
      have hθ0 : 0 < θ := by
        rcases eq_or_lt_of_le hθb.1 with h' | h'
        · exact absurd (by rw [← h']; simp) hs
        · exact h'
      have hθ1 : θ < Real.pi / 2 := by
        rcases lt_or_eq_of_le hθb.2 with h' | h'
        · exact h'
        · exact absurd (by rw [h', show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring,
            Real.sin_pi]) hs
      have hwt : 0 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
        have hw : 0 ≤ Work.Spaces.w z := by
          rw [Work.Spaces.w]
          exact div_nonneg (sq_nonneg _) (sq_nonneg _)
        have hsden : 0 ≤ Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
          (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
            _).le
        exact div_nonneg hw hsden
      set wt : ℝ := Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) with hwtdef
      have hbase : |u z θ| * wt ≤ (|g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) * wt :=
        mul_le_mul_of_nonneg_right (h z hzpos θ hθ0 hθ1) hwt
      have hsq : (|u z θ| * wt) ^ 2
          ≤ ((|g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) * wt) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hwt) hbase 2
      have hexp : (|g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) * wt
          = |g1 z θ| * wt + |g2 z θ| * wt + |g3 z θ| * wt + |g4 z θ| * wt + |g5 z θ| * wt := by
        ring
      have hfive : (|g1 z θ| * wt + |g2 z θ| * wt + |g3 z θ| * wt + |g4 z θ| * wt
            + |g5 z θ| * wt) ^ 2
          ≤ 5 * ((|g1 z θ| * wt) ^ 2 + (|g2 z θ| * wt) ^ 2 + (|g3 z θ| * wt) ^ 2
              + (|g4 z θ| * wt) ^ 2 + (|g5 z θ| * wt) ^ 2) :=
        sq_sum_five_le _ _ _ _ _
      calc Work.Spaces.HkIntegrand α 0 u z θ
          = (|u z θ| * wt) ^ 2 := by rw [HkIntegrand_zero_eq_abs]
        _ ≤ ((|g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) * wt) ^ 2 := hsq
        _ = (|g1 z θ| * wt + |g2 z θ| * wt + |g3 z θ| * wt + |g4 z θ| * wt
              + |g5 z θ| * wt) ^ 2 := by rw [hexp]
        _ ≤ 5 * ((|g1 z θ| * wt) ^ 2 + (|g2 z θ| * wt) ^ 2 + (|g3 z θ| * wt) ^ 2
              + (|g4 z θ| * wt) ^ 2 + (|g5 z θ| * wt) ^ 2) := hfive
        _ = 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ + Work.Spaces.HkIntegrand α 0 g2 z θ
              + Work.Spaces.HkIntegrand α 0 g3 z θ + Work.Spaces.HkIntegrand α 0 g4 z θ
              + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
            rw [HkIntegrand_zero_eq_abs, HkIntegrand_zero_eq_abs, HkIntegrand_zero_eq_abs,
              HkIntegrand_zero_eq_abs, HkIntegrand_zero_eq_abs]

/-! ## Integrating a pointwise five-term domination -/

/-- **A pointwise five-term domination integrates to a `HkSq`-domination.**  Only the
*honesty* (`HkMem`) of the five majorants is needed, not of `f` itself: this is
`integral_mono_of_nonneg` twice, together with the linearity of the integral over the five
summands. -/
theorem HkSq_zero_le_sum_five {α : ℝ} {f g1 g2 g3 g4 g5 : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hm1 : Work.Spaces.HkMem α 0 g1) (hm2 : Work.Spaces.HkMem α 0 g2)
    (hm3 : Work.Spaces.HkMem α 0 g3) (hm4 : Work.Spaces.HkMem α 0 g4)
    (hm5 : Work.Spaces.HkMem α 0 g5)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 f z θ
        ≤ C * (Work.Spaces.HkIntegrand α 0 g1 z θ + Work.Spaces.HkIntegrand α 0 g2 z θ
              + Work.Spaces.HkIntegrand α 0 g3 z θ + Work.Spaces.HkIntegrand α 0 g4 z θ
              + Work.Spaces.HkIntegrand α 0 g5 z θ)) :
    Work.Spaces.HkSq α 0 f
      ≤ C * (Work.Spaces.HkSq α 0 g1 + Work.Spaces.HkSq α 0 g2 + Work.Spaces.HkSq α 0 g3
            + Work.Spaces.HkSq α 0 g4 + Work.Spaces.HkSq α 0 g5) := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g1 z θ)
              + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g2 z θ)
              + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g3 z θ)
              + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g4 z θ)
              + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g5 z θ)) := by
    intro z hz
    have hInt : Integrable (fun θ => C * (Work.Spaces.HkIntegrand α 0 g1 z θ
        + Work.Spaces.HkIntegrand α 0 g2 z θ + Work.Spaces.HkIntegrand α 0 g3 z θ
        + Work.Spaces.HkIntegrand α 0 g4 z θ + Work.Spaces.HkIntegrand α 0 g5 z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      ((((hm1.1 z hz).add (hm2.1 z hz)).add (hm3.1 z hz)).add (hm4.1 z hz)).add
        (hm5.1 z hz) |>.const_mul C
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α 0 f z θ)
      (g := fun θ => C * (Work.Spaces.HkIntegrand α 0 g1 z θ
        + Work.Spaces.HkIntegrand α 0 g2 z θ + Work.Spaces.HkIntegrand α 0 g3 z θ
        + Work.Spaces.HkIntegrand α 0 g4 z θ + Work.Spaces.HkIntegrand α 0 g5 z θ))
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 f z θ)
      hInt
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact integral_add_five (hm1.1 z hz) (hm2.1 z hz) (hm3.1 z hz) (hm4.1 z hz) (hm5.1 z hz)
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq,
    Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine (MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
    (g := fun z => C * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g1 z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g2 z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g3 z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g4 z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g5 z θ)))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 f z θ)
    (((((hm1.2.add hm2.2).add hm3.2).add hm4.2).add hm5.2).const_mul C)
    (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)).trans_eq ?_
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact integral_add_five hm1.2 hm2.2 hm3.2 hm4.2 hm5.2

/-! ## The assembly -/

theorem HkSqAssembly : ∃ C : ℝ, 0 < C ∧
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
    Work.Spaces.HkMem α 0 Ψ →
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) →
    Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ≤ C * (Work.Spaces.HkSq α 0 F
          + Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
          + Work.Spaces.HkSq α 0
              (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          + Work.Spaces.HkSq α 0 Ψ) := by
  refine ⟨216, by norm_num, ?_⟩
  intro α F Ψ h hΨ hG
  -- honesty of the five summands
  have hu : Work.Spaces.HkMem α 0
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) :=
    HonMemU.honMemPthTan α F Ψ h hΨ hG
  have hcG : Work.Spaces.HkMem α 0
      (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α * (5 + α)) hG
  have h6P : Work.Spaces.HkMem α 0 (fun z θ => 6 * Ψ z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 6 hΨ
  -- the coefficient bound `(α(5+α))² ≤ 4` (from `0 < α ≤ 1/4`)
  have hc : (α * (5 + α)) ^ 2 ≤ 4 := by
    have h1 : α * (5 + α) ≤ 21 / 16 := by nlinarith [h.hα, h.hα4]
    have h2 : 0 ≤ α * (5 + α) := by nlinarith [h.hα]
    nlinarith [h1, h2, sq_nonneg (α * (5 + α) - 21 / 16)]
  -- the pointwise domination
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 F z θ
              + Work.Spaces.HkIntegrand α 0
                  (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ
              + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
              + Work.Spaces.HkIntegrand α 0
                  (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) z θ
              + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ) :=
    HkIntegrand_zero_le_five (α := α)
      (u := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (g1 := F) (g2 := fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ))
      (g3 := Work.Spaces.pthIter 2 Ψ)
      (g4 := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (g5 := fun z θ => 6 * Ψ z θ) (fun z hz θ h0 h1 => by
        have heq := h.eq_solve hz h0 h1
        rw [heq]
        refine abs_le.mpr ⟨?_, ?_⟩ <;>
          linarith [le_abs_self (F z θ), neg_le_abs (F z θ),
            le_abs_self ((α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)),
            neg_le_abs ((α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)),
            le_abs_self (Work.Spaces.pthIter 2 Ψ z θ),
            neg_le_abs (Work.Spaces.pthIter 2 Ψ z θ),
            le_abs_self (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ),
            neg_le_abs (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ),
            le_abs_self (6 * Ψ z θ), neg_le_abs (6 * Ψ z θ)])
  -- integrate the pointwise domination
  have hmain : Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ≤ 5 * (Work.Spaces.HkSq α 0 F
          + Work.Spaces.HkSq α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
          + Work.Spaces.HkSq α 0
              (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          + Work.Spaces.HkSq α 0 (fun z θ => 6 * Ψ z θ)) :=
    HkSq_zero_le_sum_five (α := α) (C := 5) (by norm_num) h.memF hcG h.memB hu h6P hpt
  -- the two coefficient reductions
  have h2 : Work.Spaces.HkSq α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ))
      ≤ 4 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) := by
    rw [HkSq_zero_const_mul]
    nlinarith [hc, HkSq_zero_nonneg α (fun z θ => z * Work.Spaces.pz Ψ z θ)]
  have h6 : Work.Spaces.HkSq α 0 (fun z θ => 6 * Ψ z θ) = 36 * Work.Spaces.HkSq α 0 Ψ := by
    rw [HkSq_zero_const_mul]
    norm_num
  rw [h6] at hmain
  have hF0 := HkSq_zero_nonneg α F
  have hG0 := HkSq_zero_nonneg α (fun z θ => z * Work.Spaces.pz Ψ z θ)
  have hB0 := HkSq_zero_nonneg α (Work.Spaces.pthIter 2 Ψ)
  have hu0 := HkSq_zero_nonneg α
    (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
  have hP0 := HkSq_zero_nonneg α Ψ
  nlinarith [hmain, h2, hF0, hG0, hB0, hu0, hP0]

end Work.FTS.EllipticEst.Honest
