/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/SdelGamHon`: the `Sdel` summand at the exponent `γ` in the honest class

The honest copy of `TransportS.T2Sup.sdel_integral_le_of_gam`: the delicate `Sdel` summand
`canonW γ · Sdel f g 1 3 · mixed 3 1 g` is bounded by `Cd·α^{-1/2}(|f|_{ℋ⁴}+CoefTh 1 f)|g|²_{ℋ⁴}`
using `delicateMargInt_hon` and `integrableOnSliceDelicate` (both honest).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.DelicateMargIntHon
import Submission.Work.FTS.TransportS.T2Sup.integrableOnSliceDelicate
import Submission.Work.FTS.TransportS.T2Sup.delicateBound
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.Main
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false

open Work.FTS.TransportS
open Work.FTS.TransportS.SlotT2
open Work.FTS.TransportS.T2Sup

/-- The `Sdel` summand at the exponent `γ` in the honest class (the delicate case). -/
theorem sdel_integral_le_of_gam_hon {α Cd : ℝ} {f g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsf : HonF α f)
    (hSmoG : Work.FTS.EllipticEst.SmoothOpen g) (hHk4g : Work.Spaces.HkMem α 4 g)
    (hDelb : ∀ q : ℝ, 0 ≤ q → q ≤ Work.Spaces.gam α →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ Cd * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.Spaces.HkSq α 4 g) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|
      ≤ Cd * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.Spaces.HkSq α 4 g := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hgam : 0 ≤ Work.Spaces.gam α := le_of_lt hγpos
  have hHd_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|) Work.Spaces.Iz :=
    delicateMargInt_hon α (Work.Spaces.gam α) f g hα hα1 hgam le_rfl hsf hSmoG hHk4g
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 3 f z θ|
        * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW (Work.Spaces.gam α) 0 θ * |Work.Spaces.DzIter 3 f 0 θ|
            * |Work.Spaces.mixed 1 1 g 0 θ| * |Work.Spaces.mixed 3 1 g 0 θ|)
          = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact MeasureTheory.integrableOn_zero
    · exact integrableOnSliceDelicate hα hα1 hsf.1 hsf.2.1
        hSmoG hHk4g hz0
  have hpoint : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ
            * |Work.Spaces.DzIter 3 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ| := by
    intro z hz
    have hnorm : |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
            * Work.Spaces.mixed 3 1 g z θ))
    refine le_trans hnorm ?_
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall
      (fun θ => abs_nonneg _)) (hslice z hz) ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      filter_upwards with θ
      rw [canonW_zero_z, zero_mul, zero_mul, abs_zero]
      simp
    · refine ae_of_forall_Ioo (fun θ hθ => ?_)
      dsimp only
      have hsdel : Sdel f g 1 3 z θ
          = Work.Spaces.mixed 3 0 f z θ * Work.Spaces.mixed 1 1 g z θ := by
        simp only [Sdel, Nat.choose_self, Nat.cast_one, one_mul, Nat.reduceSub]
      rw [hsdel, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (canonW_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
      simp only [Work.Spaces.mixed_zero_right]
      exact le_of_eq (by ring)
  have hstep1 : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ * Work.Spaces.mixed 3 1 g z θ|
      ≤ ∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (f := fun z => ∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ))
  have hstep2 : (∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ * Sdel f g 1 3 z θ
          * Work.Spaces.mixed 3 1 g z θ|)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 3 f z θ|
            * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ| :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => abs_nonneg _))
      hHd_int (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z hz => hpoint z hz))
  refine le_trans (le_trans hstep1 hstep2) ?_
  simpa only [Work.FTS.TransportS.SlotT2.canonW, Work.Spaces.mixed_zero_right] using
    hDelb (Work.Spaces.gam α) hgam le_rfl

end Work.FTS.StrongPersist.N6Trans.Hon
