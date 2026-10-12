import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Quant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.omegaSqCoupl_eq`

The coupling identity `A_w = ℓ³∫ω²v` of the CS step (the Fubini factorisation of a
slot-constant weight, FS §9):

`∫_{Λ×Λ} ω(x−y)²·w(x,y) dx dy = ℓ³ ∫_{ℝ³} ω(z)² v(z) dz`

for the `v`-weight `w = wLoc ℓ v 0 = χ_ℓ(x)·(v(x−y)/(χ⋆χ)_ℓ(x−y))·χ_ℓ(y)` and
`ω = omC w₀` (here `w` denotes the *scattering solution* of the statement, i.e. the `ω`
of the paper; the statement's `v` is the potential).

Proof route (essentially the corpus's `kernel_double_integral` with a general
`L¹`-numerator):

* `χ_ℓ ≠ 0` forces `‖·‖ ≤ ℓ/2`, hence the support of `χ_ℓ` lies in the centred cube
  `acube ℓ`; therefore both box integrals may be extended to `ℝ³`/`ℝ³×ℝ³`
  (`setIntegral_eq_integral_of_forall_compl_eq_zero`).
* Pointwise the two integrands agree, because `χ_u = χ_ℓ` at `u = 0` and
  `wScaled ℓ v z · convScale ℓ z = v z` on the support of the numerator, and
  `w²·v` is assumed to vanish off `ball 0 R` with `R ≤ ℓ·chiR0`.
* The resulting full-space double integral is `kernel_double_integral` applied to the
  integrable numerator `z ↦ w z²·v z`.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Work.BoseFixB3.CS.Pieces

open Submission.BoseGases

set_option autoImplicit false

/-- `χ_ℓ` vanishes off the centred cube `acube ℓ` (`supp χ ⊆ ball 0 (1/2)`). -/
lemma chiScale_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {x : ℝ³}
    (hx : x ∉ acube ℓ) : chiScale ℓ x = 0 := by
  by_contra h
  exact hx (mem_acube_of_norm_le (le_of_lt hℓ) (chiScale_support_le hℓ h))

/-- The two forms of the `omegaSqCoupl` integrand agree:
`ω(x−y)²·χ(x)·W(x−y)·χ(y) = χ(x)·χ(y)·(ω(x−y)²·v(x−y))/(χ⋆χ)_ℓ(x−y)`. -/
lemma omegaSqCoupl_integrand_eq (v w : ℝ³ → ℝ) (ℓ : ℝ) (a b : ℝ³) :
    w (a - b) ^ 2 * (chiU ℓ 0 a * wScaled ℓ v (a - b) * chiU ℓ 0 b)
      = chiScale ℓ a * chiScale ℓ b * ((w (a - b) ^ 2 * v (a - b)) / convScale ℓ (a - b)) := by
  simp only [chiU, chiScale, wScaled, sub_zero, div_eq_mul_inv]
  ring

theorem omegaSqCoupl_eq {v w : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hhi : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => w z ^ 2 * v z))
    (hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → w z ^ 2 * v z = 0) :
    Work.BoseFixB3.CS.omegaSqCoupl ℓ (Submission.BoseGases.omC w) (Submission.BoseGases.wLoc ℓ v 0)
      = ℓ ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), w z ^ 2 * v z := by
  have hzero : ∀ a : ℝ³, a ∉ acube ℓ → chiScale ℓ a = 0 :=
    fun a ha => chiScale_eq_zero_of_notMem_acube hℓ ha
  have hfh : ∀ a b : ℝ³,
      w (a - b) ^ 2 * (chiU ℓ 0 a * wScaled ℓ v (a - b) * chiU ℓ 0 b)
        = chiScale ℓ a * chiScale ℓ b *
            ((w (a - b) ^ 2 * v (a - b)) / convScale ℓ (a - b)) :=
    fun a b => omegaSqCoupl_integrand_eq v w ℓ a b
  -- the inner box integral is the full integral (the `b`-integrand vanishes off `acube ℓ`)
  have hinner : ∀ a : ℝ³,
      (∫ b in acube ℓ, w (a - b) ^ 2 * (chiU ℓ 0 a * wScaled ℓ v (a - b) * chiU ℓ 0 b))
        = ∫ b : ℝ³, chiScale ℓ a * chiScale ℓ b *
            ((w (a - b) ^ 2 * v (a - b)) / convScale ℓ (a - b)) := by
    intro a
    refine Eq.trans (MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
      (fun b _ => hfh a b)) ?_
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun b hb => by rw [hzero b hb]; ring)
  -- and the outer box integral likewise
  have houter : (∫ a in acube ℓ, ∫ b in acube ℓ,
        w (a - b) ^ 2 * (chiU ℓ 0 a * wScaled ℓ v (a - b) * chiU ℓ 0 b))
      = ∫ a : ℝ³, ∫ b : ℝ³, chiScale ℓ a * chiScale ℓ b *
          ((w (a - b) ^ 2 * v (a - b)) / convScale ℓ (a - b)) := by
    refine Eq.trans (MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
      (fun a _ => hinner a)) ?_
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun a ha => ?_)
    have h0 : (fun b : ℝ³ => chiScale ℓ a * chiScale ℓ b *
          ((w (a - b) ^ 2 * v (a - b)) / convScale ℓ (a - b))) = fun _ => (0 : ℝ) := by
      funext b
      rw [hzero a ha]
      ring
    rw [h0]
    simp
  have hmain := kernel_double_integral (fun z : ℝ³ => w z ^ 2 * v z) hℓ hhi hsupp
    chiR0_pos hRℓ chiR0_half
  have hL : Work.BoseFixB3.CS.omegaSqCoupl ℓ (omC w) (wLoc ℓ v 0)
      = (∫ a in acube ℓ, ∫ b in acube ℓ,
          w (a - b) ^ 2 * (chiU ℓ 0 a * wScaled ℓ v (a - b) * chiU ℓ 0 b)) := rfl
  rw [hL, houter, hmain]

end Work.BoseFixB3.CS.Pieces
