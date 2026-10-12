import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.integral_abox_comp_apply
import Submission.Work.UBBInputs8.A.pairSet_card_cast_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

open MeasureTheory
open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## Helper lemmas -/

/-- The two-factor cutoff is bounded (continuous with compact support). -/
lemma chiSmallB_norm_bound {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : ℝ³) : ∃ C, ∀ y : ℝ³, ‖chiSmallB M ℓ d u y‖ ≤ C := by
  have hc := chiSmallB_continuous hM hℓ hd u
  have hcs := chiSmallB_hasCompactSupport (d := d) hM hℓ u
  have hcomp : IsCompact (Set.range (fun y : ℝ³ => chiSmallB M ℓ d u y)) :=
    hcs.isCompact_range hc
  obtain ⟨C, hC⟩ := hcomp.isBounded.exists_norm_le
  exact ⟨C, fun y => hC _ (Set.mem_range_self y)⟩

/-- A continuous function bounded by `C` is integrable on the box `abox N L`. -/
lemma integrableOn_abox_of_bound {N : ℕ} {L : ℝ} (hL : 0 < L) {g : X N → ℝ}
    (hg : Continuous g) {C : ℝ} (hC : ∀ x : X N, ‖g x‖ ≤ C) :
    IntegrableOn g (abox N L) := by
  refine MeasureTheory.IntegrableOn.of_bound (μ := volume) ?_ hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
  rw [abox_volume N L hL.le]
  exact ENNReal.ofReal_lt_top

/-- Integrability on the box of a single-coordinate pullback. -/
lemma integrableOn_eval_abox {N : ℕ} {L : ℝ} (hL : 0 < L) {M : ℕ} (hM : 1 ≤ M)
    {d : ℝ} (hd : 0 < d) (u : ℝ³) (i : Fin N) :
    IntegrableOn (fun x : X N => chiSmallB M L d u (x i)) (abox N L) := by
  obtain ⟨C, hC⟩ := chiSmallB_norm_bound hM hL hd u
  exact integrableOn_abox_of_bound hL ((chiSmallB_continuous hM hL hd u).comp (continuous_apply i))
    (fun x => hC (x i))

/-- Integrability on the box of a squared single-coordinate pullback. -/
lemma integrableOn_eval_sq_abox {N : ℕ} {L : ℝ} (hL : 0 < L) {M : ℕ} (hM : 1 ≤ M)
    {d : ℝ} (hd : 0 < d) (u : ℝ³) (i : Fin N) :
    IntegrableOn (fun x : X N => (chiSmallB M L d u (x i)) ^ 2) (abox N L) := by
  obtain ⟨C, hC⟩ := chiSmallB_norm_bound hM hL hd u
  refine integrableOn_abox_of_bound hL
    (((chiSmallB_continuous hM hL hd u).comp (continuous_apply i)).pow 2) (C := C ^ 2) ?_
  intro x
  calc ‖(chiSmallB M L d u (x i)) ^ 2‖ = (chiSmallB M L d u (x i)) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ = |chiSmallB M L d u (x i)| ^ 2 := (sq_abs _).symm
    _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC (x i)) 2

/-- Integrability on the box of a pair of single-coordinate pullbacks. -/
lemma integrableOn_eval_mul_abox {N : ℕ} {L : ℝ} (hL : 0 < L) {M : ℕ} (hM : 1 ≤ M)
    {d : ℝ} (hd : 0 < d) (u : ℝ³) (i j : Fin N) :
    IntegrableOn (fun x : X N => chiSmallB M L d u (x i) * chiSmallB M L d u (x j))
      (abox N L) := by
  obtain ⟨C, hC⟩ := chiSmallB_norm_bound hM hL hd u
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine integrableOn_abox_of_bound hL
    (((chiSmallB_continuous hM hL hd u).comp (continuous_apply i)).mul
      ((chiSmallB_continuous hM hL hd u).comp (continuous_apply j))) (C := C * C) ?_
  intro x
  rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact mul_le_mul (hC (x i)) (hC (x j)) (norm_nonneg _) hC0

/-- **The integral of the dominating function over the analysis box.**

With `χ := chiSmallB M L dd u ≥ 0` and `T := ∫_{ℝ³} χ` (`T ≥ 0`), `T ^ 2 ≤ chiMass·(L dd)^3`,
`μ ≥ 0`, the integral over `abox N L` of the dominating function
`S·(μ·KL·T·Σᵢχ(xᵢ) + ½·KP·Σ_{p ∈ pairSet N} χ(x_p1)χ(x_p2))` is at most
`S·(L³)^{N-1}·(μ·N·KL·(L dd)³ + ½·KP·N²)·chiMass`.

Route: pull `S`, `μKL T` and `½KP` out of the integral (`integral_const_mul`, `integral_add`,
`integral_finsetSum`), use `Work.UBBInputs8.A.integral_abox_comp_apply` for the one-slot
integrals `∫_{abox N L} χ(xᵢ) = (L³)^{N-1}∫_{acube L}χ ≤ (L³)^{N-1}T` and for
`∫_{abox N L} χ(xᵢ)² = (L³)^{N-1}∫_{acube L}χ² ≤ (L³)^{N-1}chiMass`, and AM–GM
`χ(x_p1)χ(x_p2) ≤ ½(χ(x_p1)² + χ(x_p2)²)` for the pair terms.  Then `Σᵢ 1 = N`,
`Σ_{p ∈ pairSet N} 1 = #(pairSet N) ≤ N²` (`pairSet_card_cast_le`), and finally
`T ^ 2 ≤ chiMass·(L dd)³`. -/
theorem integral_hlowDom_le {N : ℕ} {M : ℕ} (hM : 1 ≤ M) {L dd μ S KL KP T : ℝ}
    (hL : 0 < L) (hd : 0 < dd) (hμ : 0 ≤ μ) (u : EuclideanSpace ℝ (Fin 3))
    (hS : 0 ≤ S) (hKL : 0 ≤ KL) (hKP : 0 ≤ KP) (hT : 0 ≤ T)
    (hTdef : T = ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M L dd u x)
    (hT2 : T ^ 2 ≤ Work.SmallBoxSliding.chiMass M L dd u * (L * dd) ^ 3) :
    (∫ x in Submission.BoseGases.abox N L,
        S * (μ * (KL * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L dd u (x i))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
              KP * Submission.BoseGases.chiSmallB M L dd u (x p.1)
                * Submission.BoseGases.chiSmallB M L dd u (x p.2))))
      ≤ S * ((L ^ 3) ^ (N - 1)
          * (μ * (N : ℝ) * KL * (L * dd) ^ 3 + (1 / 2) * KP * (N : ℝ) ^ 2)
          * Work.SmallBoxSliding.chiMass M L dd u) := by
  -- ## basic nonnegativity / integrability
  have hVnn : 0 ≤ (L ^ 3) ^ (N - 1) := pow_nonneg (pow_nonneg hL.le 3) _
  have hcmnn : 0 ≤ Work.SmallBoxSliding.chiMass M L dd u :=
    Work.SmallBoxSliding.chiMass_nonneg M L dd u
  have hμKLT : 0 ≤ μ * KL * T := mul_nonneg (mul_nonneg hμ hKL) hT
  have hχint : Integrable (fun y : ℝ³ => chiSmallB M L dd u y) volume :=
    (chiSmallB_continuous hM hL hd u).integrable_of_hasCompactSupport
      (chiSmallB_hasCompactSupport (d := dd) hM hL u)
  have hχsqint : Integrable (fun y : ℝ³ => (chiSmallB M L dd u y) ^ 2) volume :=
    Work.SmallBoxSliding.integrable_chiSmallB_sq_slice hM hL u
  have hχnn : ∀ y : ℝ³, 0 ≤ chiSmallB M L dd u y := chiSmallB_nonneg M L dd u
  -- ## the two `acube` bounds
  have hAcubeχ : ∫ y in acube L, chiSmallB M L dd u y ≤ T := by
    have h := MeasureTheory.setIntegral_le_integral (s := acube L) hχint
      (Filter.Eventually.of_forall hχnn)
    rw [hTdef]
    exact h
  have hAcubeχsq : ∫ y in acube L, (chiSmallB M L dd u y) ^ 2
      ≤ Work.SmallBoxSliding.chiMass M L dd u := by
    have h := MeasureTheory.setIntegral_le_integral (s := acube L) hχsqint
      (Filter.Eventually.of_forall (fun y => sq_nonneg _))
    rw [Work.SmallBoxSliding.chiMass_def]
    exact h
  -- ## integrability on the box
  have hI1 : ∀ i : Fin N, Integrable (fun x : X N => chiSmallB M L dd u (x i))
      (volume.restrict (abox N L)) := fun i => integrableOn_eval_abox hL hM hd u i
  have hI2 : ∀ i : Fin N, Integrable (fun x : X N => (chiSmallB M L dd u (x i)) ^ 2)
      (volume.restrict (abox N L)) := fun i => integrableOn_eval_sq_abox hL hM hd u i
  have hI3 : ∀ p ∈ pairSet N, Integrable
      (fun x : X N => chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))
      (volume.restrict (abox N L)) := fun p _ => integrableOn_eval_mul_abox hL hM hd u p.1 p.2
  have hI4 : ∀ p ∈ pairSet N, Integrable
      (fun x : X N => KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))
      (volume.restrict (abox N L)) := by
    intro p _
    obtain ⟨C, hC⟩ := chiSmallB_norm_bound hM hL hd u
    refine integrableOn_abox_of_bound hL ?_ (C := KP * C * C) ?_
    · exact (((chiSmallB_continuous hM hL hd u).comp (continuous_apply p.1)).const_mul KP).mul
        ((chiSmallB_continuous hM hL hd u).comp (continuous_apply p.2))
    · intro x
      have h1 : |chiSmallB M L dd u (x p.1)| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC (x p.1)
      have h2 : |chiSmallB M L dd u (x p.2)| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC (x p.2)
      have hC0 : 0 ≤ C := le_trans (abs_nonneg _) h1
      calc ‖KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2)‖
          = |KP| * |chiSmallB M L dd u (x p.1)| * |chiSmallB M L dd u (x p.2)| := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul]
        _ = KP * |chiSmallB M L dd u (x p.1)| * |chiSmallB M L dd u (x p.2)| := by
            rw [abs_of_nonneg hKP]
        _ ≤ KP * C * C := by
            calc KP * |chiSmallB M L dd u (x p.1)| * |chiSmallB M L dd u (x p.2)|
                = KP * (|chiSmallB M L dd u (x p.1)| * |chiSmallB M L dd u (x p.2)|) := by
                  ring
              _ ≤ KP * (C * C) := mul_le_mul_of_nonneg_left
                  (mul_le_mul h1 h2 (abs_nonneg _) hC0) hKP
              _ = KP * C * C := by ring
  -- ## the pair bound (AM–GM)
  have hpair : ∀ p ∈ pairSet N,
      (∫ x in abox N L, chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))
        ≤ (L ^ 3) ^ (N - 1) * Work.SmallBoxSliding.chiMass M L dd u := by
    intro p hp
    have hpt : ∀ x : X N, chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2)
        ≤ (1 / 2) * ((chiSmallB M L dd u (x p.1)) ^ 2 + (chiSmallB M L dd u (x p.2)) ^ 2) := by
      intro x
      nlinarith [sq_nonneg (chiSmallB M L dd u (x p.1) - chiSmallB M L dd u (x p.2))]
    have hInt2 : Integrable
        (fun x : X N => (1 / 2) * ((chiSmallB M L dd u (x p.1)) ^ 2
          + (chiSmallB M L dd u (x p.2)) ^ 2)) (volume.restrict (abox N L)) :=
      ((hI2 p.1).add (hI2 p.2)).const_mul (1 / 2)
    calc (∫ x in abox N L, chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))
        ≤ ∫ x in abox N L, (1 / 2) * ((chiSmallB M L dd u (x p.1)) ^ 2
            + (chiSmallB M L dd u (x p.2)) ^ 2) :=
          MeasureTheory.integral_mono (hI3 p hp) hInt2 hpt
      _ = (1 / 2) * ((∫ x in abox N L, (chiSmallB M L dd u (x p.1)) ^ 2)
            + (∫ x in abox N L, (chiSmallB M L dd u (x p.2)) ^ 2)) := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add (hI2 p.1) (hI2 p.2)]
      _ = (1 / 2) * (((L ^ 3) ^ (N - 1) * ∫ y in acube L, (chiSmallB M L dd u y) ^ 2)
            + ((L ^ 3) ^ (N - 1) * ∫ y in acube L, (chiSmallB M L dd u y) ^ 2)) := by
          rw [integral_abox_comp_apply hL.le p.1 hχsqint.integrableOn,
              integral_abox_comp_apply hL.le p.2 hχsqint.integrableOn]
      _ = (L ^ 3) ^ (N - 1) * ∫ y in acube L, (chiSmallB M L dd u y) ^ 2 := by ring
      _ ≤ (L ^ 3) ^ (N - 1) * Work.SmallBoxSliding.chiMass M L dd u :=
          mul_le_mul_of_nonneg_left hAcubeχsq hVnn
  -- ## part 1: the one-slot sum
  have hAb : (∫ x in abox N L, μ * (KL * T * ∑ i : Fin N, chiSmallB M L dd u (x i)))
      ≤ (L ^ 3) ^ (N - 1) * (μ * (N : ℝ) * KL * (L * dd) ^ 3)
          * Work.SmallBoxSliding.chiMass M L dd u := by
    have hsum : (∑ i : Fin N, (∫ x in abox N L, chiSmallB M L dd u (x i)))
        = (N : ℝ) * ((L ^ 3) ^ (N - 1) * ∫ y in acube L, chiSmallB M L dd u y) := by
      rw [show (∑ i : Fin N, (∫ x in abox N L, chiSmallB M L dd u (x i)))
            = ∑ i : Fin N, ((L ^ 3) ^ (N - 1) * ∫ y in acube L, chiSmallB M L dd u y)
          from Finset.sum_congr rfl
            (fun i _ => integral_abox_comp_apply hL.le i hχint.integrableOn)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hstep : (∫ x in abox N L, μ * (KL * T * ∑ i : Fin N, chiSmallB M L dd u (x i)))
        = μ * KL * T * ((N : ℝ) * ((L ^ 3) ^ (N - 1)
            * ∫ y in acube L, chiSmallB M L dd u y)) := by
      rw [show (fun x : X N => μ * (KL * T * ∑ i : Fin N, chiSmallB M L dd u (x i)))
            = (fun x : X N => (μ * KL * T) * (∑ i : Fin N, chiSmallB M L dd u (x i)))
          from funext (fun x => by ring)]
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x in abox N L, (∑ i : Fin N, chiSmallB M L dd u (x i)))
            = ∑ i : Fin N, ∫ x in abox N L, chiSmallB M L dd u (x i)
          from MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin N))
            (fun i _ => hI1 i)]
      rw [hsum]
    rw [hstep]
    calc μ * KL * T * ((N : ℝ) * ((L ^ 3) ^ (N - 1)
            * ∫ y in acube L, chiSmallB M L dd u y))
        ≤ μ * KL * T * ((N : ℝ) * ((L ^ 3) ^ (N - 1) * T)) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hAcubeχ hVnn
            · exact Nat.cast_nonneg N
          · exact hμKLT
      _ = (L ^ 3) ^ (N - 1) * (μ * (N : ℝ) * KL * T ^ 2) := by ring
      _ ≤ (L ^ 3) ^ (N - 1) * (μ * (N : ℝ) * KL
            * (Work.SmallBoxSliding.chiMass M L dd u * (L * dd) ^ 3)) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left hT2
            exact mul_nonneg (mul_nonneg hμ (Nat.cast_nonneg N)) hKL
          · exact hVnn
      _ = (L ^ 3) ^ (N - 1) * (μ * (N : ℝ) * KL * (L * dd) ^ 3)
            * Work.SmallBoxSliding.chiMass M L dd u := by ring
  -- ## part 2: the pair sum
  have hBb : (∫ x in abox N L, (1 / 2) * (∑ p ∈ pairSet N,
        KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2)))
      ≤ (L ^ 3) ^ (N - 1) * ((1 / 2) * KP * (N : ℝ) ^ 2)
          * Work.SmallBoxSliding.chiMass M L dd u := by
    have hinner : ∀ x : X N, (∑ p ∈ pairSet N,
          KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))
        = (∑ p ∈ pairSet N,
          KP * (chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))) :=
      fun x => Finset.sum_congr rfl (fun p _ => by ring)
    have hstep : (∫ x in abox N L, (1 / 2) * (∑ p ∈ pairSet N,
          KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2)))
        = (1 / 2) * ∑ p ∈ pairSet N, KP * (∫ x in abox N L,
            chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2)) := by
      rw [show (fun x : X N => (1 / 2) * (∑ p ∈ pairSet N,
              KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2)))
            = (fun x : X N => (1 / 2) * (∑ p ∈ pairSet N,
              KP * (chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))))
          from funext (fun x => by rw [hinner x])]
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x in abox N L, (∑ p ∈ pairSet N,
              KP * (chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))))
            = ∑ p ∈ pairSet N, ∫ x in abox N L,
              KP * (chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))
          from MeasureTheory.integral_finsetSum (pairSet N)
            (fun p hp => (hI3 p hp).const_mul KP)]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      exact MeasureTheory.integral_const_mul KP
        (fun x : X N => chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))
    rw [hstep]
    calc (1 / 2) * ∑ p ∈ pairSet N, KP * (∫ x in abox N L,
            chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))
        ≤ (1 / 2) * ∑ p ∈ pairSet N, KP * ((L ^ 3) ^ (N - 1)
            * Work.SmallBoxSliding.chiMass M L dd u) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_left (hpair p hp) hKP
      _ = (1 / 2) * (((pairSet N).card : ℝ) * (KP * ((L ^ 3) ^ (N - 1)
            * Work.SmallBoxSliding.chiMass M L dd u))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 / 2) * (((N : ℝ) ^ 2) * (KP * ((L ^ 3) ^ (N - 1)
            * Work.SmallBoxSliding.chiMass M L dd u))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right (pairSet_card_cast_le N)
            (mul_nonneg hKP (mul_nonneg hVnn hcmnn))
      _ = (L ^ 3) ^ (N - 1) * ((1 / 2) * KP * (N : ℝ) ^ 2)
            * Work.SmallBoxSliding.chiMass M L dd u := by ring
  -- ## assembly
  have hIA : Integrable (fun x : X N => μ * (KL * T * ∑ i : Fin N, chiSmallB M L dd u (x i)))
      (volume.restrict (abox N L)) := by
    have hsum : Integrable (fun x : X N => ∑ i : Fin N, chiSmallB M L dd u (x i))
        (volume.restrict (abox N L)) := by
      simpa using MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin N))
        (fun i _ => hI1 i)
    simpa only [mul_assoc] using ((hsum.const_mul T).const_mul KL).const_mul μ
  have hIB : Integrable (fun x : X N => (1 / 2) * (∑ p ∈ pairSet N,
      KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2)))
      (volume.restrict (abox N L)) := by
    have hsum2 : Integrable (fun x : X N => ∑ p ∈ pairSet N,
        KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))
        (volume.restrict (abox N L)) :=
      MeasureTheory.integrable_finsetSum (pairSet N) (fun p hp => hI4 p hp)
    exact hsum2.const_mul (1 / 2)
  have hFsplit : (∫ x in abox N L,
        (μ * (KL * T * ∑ i : Fin N, chiSmallB M L dd u (x i))
          + (1 / 2) * (∑ p ∈ pairSet N,
              KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))))
      = (∫ x in abox N L, μ * (KL * T * ∑ i : Fin N, chiSmallB M L dd u (x i)))
        + (∫ x in abox N L, (1 / 2) * (∑ p ∈ pairSet N,
              KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))) := by
    simpa using MeasureTheory.integral_add hIA hIB
  have key : (∫ x in abox N L,
        (μ * (KL * T * ∑ i : Fin N, chiSmallB M L dd u (x i))
          + (1 / 2) * (∑ p ∈ pairSet N,
              KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2))))
      ≤ (L ^ 3) ^ (N - 1) * (μ * (N : ℝ) * KL * (L * dd) ^ 3
          + (1 / 2) * KP * (N : ℝ) ^ 2) * Work.SmallBoxSliding.chiMass M L dd u := by
    rw [hFsplit]
    refine le_trans (add_le_add hAb hBb) (le_of_eq ?_)
    ring
  rw [MeasureTheory.integral_const_mul S (fun x : X N =>
    μ * (KL * T * ∑ i : Fin N, chiSmallB M L dd u (x i))
      + (1 / 2) * (∑ p ∈ pairSet N,
          KP * chiSmallB M L dd u (x p.1) * chiSmallB M L dd u (x p.2)))]
  exact mul_le_mul_of_nonneg_left key hS

end

end Work.UBBInputs8.A
