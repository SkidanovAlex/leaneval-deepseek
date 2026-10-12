import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.CrossKern
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.bsKern_eq_conv` — `bsKern` as a convolution

The cross-term kernel `bsKern ℓ F d` (`OneBodyKin/CrossKern.lean`) is by construction the
sliding-box-kernel

  `bsKern ℓ F d = ∫_{s ∈ acube 1} ∫_p F‖p‖·profHat(ℓ•p)·χ(s+ℓ⁻¹•d)·cos⟪ℓ•p, s+ℓ⁻¹•d⟫ dp ds`.

This module identifies it with the convolution

  `bsKern ℓ F d = (G ⋆ 1_{acube 1})(ℓ⁻¹•d)`,
  `G t = ∫_p F‖p‖·profHat(ℓ•p)·χ t·cos⟪ℓ•p, t⟫ dp`

(with the Lebesgue convolution `(f ⋆ g)(x) = ∫_t f t · g (x − t) dt`, i.e.
`MeasureTheory.convolution _ _ (ContinuousLinearMap.lsmul ℝ ℝ) volume`).  This is the identity
that lets the kernel be analysed by Fourier methods: it exhibits `bsKern` as a convolution, hence
its Fourier transform as a product (`kinFT_bsKern`).

The proof is purely a change of variables for the Lebesgue integral: unfolding the convolution and
substituting `t = ℓ⁻¹•d − s` turns it into `∫_{s ∈ acube 1} G(ℓ⁻¹•d − s) ds`, and the reflection
`s ↦ −s` of the symmetric cube turns this into `∫_{s ∈ acube 1} G(s + ℓ⁻¹•d) ds = bsKern ℓ F d`.
-/

namespace Work.OneBodyKin

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-- The convolution partner of the box indicator: `G t = ∫_p F‖p‖·profHat(ℓ•p)·χ t·cos⟪ℓ•p,t⟫ dp`.
Its convolution with `1_{acube 1}` is `bsKern` (evaluated at `ℓ⁻¹•d`). -/
private noncomputable def bsG (ℓ : ℝ) (F : ℝ → ℝ) : ℝ³ → ℝ :=
  fun t => ∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * chi t * Real.cos (inner ℝ (ℓ • p) t)

/-- The unit cube is invariant under negation. -/
private lemma neg_mem_acube_one (s : ℝ³) : -s ∈ acube 1 ↔ s ∈ acube 1 := by
  simp only [mem_acube_iff]
  constructor
  · intro h m
    have hm := h m
    simp only [PiLp.neg_apply] at hm
    exact ⟨by linarith [hm.2], by linarith [hm.1]⟩
  · intro h m
    have hm := h m
    simp only [PiLp.neg_apply]
    exact ⟨by linarith [hm.2], by linarith [hm.1]⟩

/-- Negation is a measure-preserving substitution for the set integral over the symmetric cube
`acube 1`. -/
private lemma setIntegral_neg_acube (H : ℝ³ → ℝ) :
    (∫ s in acube 1, H (-s)) = ∫ s in acube 1, H s := by
  rw [← integral_indicator (acube_measurable 1), ← integral_indicator (acube_measurable 1)]
  rw [← integral_comp_neg (fun u : ℝ³ => (acube 1).indicator (fun s : ℝ³ => H (-s)) u)]
  have h : (fun u : ℝ³ => (acube 1).indicator (fun s : ℝ³ => H (-s)) (-u))
      = (acube 1).indicator H := by
    funext u
    by_cases hu : u ∈ acube 1
    · have hnu : -u ∈ acube 1 := (neg_mem_acube_one u).mpr hu
      rw [Set.indicator_of_mem hnu, Set.indicator_of_mem hu]
      simp
    · have hnu : -u ∉ acube 1 := fun hc => hu ((neg_mem_acube_one u).mp hc)
      rw [Set.indicator_of_notMem hnu, Set.indicator_of_notMem hu]
  rw [h, integral_indicator (acube_measurable 1)]

/-- On the symmetric cube, integrating `s ↦ H (x − s)` is the same as integrating
`s ↦ H (s + x)`. -/
private lemma setIntegral_sub_eq_add (H : ℝ³ → ℝ) (x : ℝ³) :
    (∫ s in acube 1, H (x - s)) = ∫ s in acube 1, H (s + x) := by
  rw [show (fun s : ℝ³ => H (x - s)) = fun s : ℝ³ => (fun u : ℝ³ => H (x + u)) (-s) from by
    funext s; rw [sub_eq_add_neg]]
  rw [setIntegral_neg_acube (fun u : ℝ³ => H (x + u))]
  refine setIntegral_congr_fun (acube_measurable 1) (fun s _ => ?_)
  show H (x + s) = H (s + x)
  rw [add_comm]

/-- The convolution with the indicator of `acube 1` is the set integral of the reflected argument:
`(H ⋆ 1_{acube 1})(x) = ∫_{s ∈ acube 1} H (x − s) ds`. -/
private lemma conv_eq_setIntegral (H : ℝ³ → ℝ) (x : ℝ³) :
    MeasureTheory.convolution H ((acube 1).indicator (fun _ => (1 : ℝ)))
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
      = ∫ s in acube 1, H (x - s) := by
  rw [MeasureTheory.convolution]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← Submission.BoseGases.integral_comp_sub_left
      (fun t : ℝ³ => H t * (acube 1).indicator (fun _ => (1 : ℝ)) (x - t)) x]
  have h1 : (fun s : ℝ³ => H (x - s) * (acube 1).indicator (fun _ => (1 : ℝ)) (x - (x - s)))
      = (acube 1).indicator (fun s : ℝ³ => H (x - s)) := by
    funext s
    rw [sub_sub_cancel]
    by_cases hs : s ∈ acube 1
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]; ring
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]; ring
  rw [h1, integral_indicator (acube_measurable 1)]

theorem bsKern_eq_conv {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) (d : EuclideanSpace ℝ (Fin 3)) :
    Work.OneBodyKin.bsKern ℓ F d =
      MeasureTheory.convolution
        (fun t : EuclideanSpace ℝ (Fin 3) =>
          ∫ p : EuclideanSpace ℝ (Fin 3),
            F ‖p‖ * Work.OneBodyKin.profHat (ℓ • p) * Submission.BoseGases.chi t *
              Real.cos (inner ℝ (ℓ • p) t))
        ((Submission.BoseGases.acube 1).indicator (fun _ => (1 : ℝ)))
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume (ℓ⁻¹ • d) := by
  set x : ℝ³ := ℓ⁻¹ • d with hx
  have hbs : bsKern ℓ F d = ∫ s in acube 1, bsG ℓ F (s + x) := by
    rw [bsKern_def]
    rw [← hx]
    refine setIntegral_congr_fun (acube_measurable 1) (fun s _ => ?_)
    simp only [bsG]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => by ring)
  have key : bsKern ℓ F d
      = MeasureTheory.convolution (bsG ℓ F) ((acube 1).indicator (fun _ => (1 : ℝ)))
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x := by
    rw [hbs, conv_eq_setIntegral (bsG ℓ F) x]
    exact (setIntegral_sub_eq_add (bsG ℓ F) x).symm
  exact key

end Work.OneBodyKin
