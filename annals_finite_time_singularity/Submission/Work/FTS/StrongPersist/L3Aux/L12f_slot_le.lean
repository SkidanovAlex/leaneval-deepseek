import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.H2.L12k0Q
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Aux

open MeasureTheory Set Filter
open scoped Real Topology

/-- The target: the `q`-th pure `D_z`-slot of the radial function `L₁₂(g)` is in
`L²(w² dz)` and dominated by the weighted `ℋ⁴`-norm of `g`.

Route: `L₁₂(g)(z) = -∫_z^∞ Qang g 0 (s)/s ds` is radial, so `D_z^q L₁₂(g) = DzdIter q L₁₂(g)`
(`Work.Elliptic.DzIter_rad`) and the open-quadrant `L₁₂`-bundle
(`Work.FTS.OpenPkg.l12_open_bundle`) gives

* `DzdIter (k+1) L₁₂(g) = -Qang g k` on `z > 0` for `k ≤ 3`;
* the `k = 0` slot with the weighted Hardy estimate `∫ L₁₂(g)² w² ≤ 107 ∫ (Qang g 0)² w²`;

while `Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open` bounds every angular moment
`∫ (Qang g i)² w² ≤ (∫_θ Kθ²) · HkSq α 4 g` for `i ≤ 4`.  The constant is
`107·(1 + ∫_θ Kθ²)`. -/
theorem L12f_slot_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Construction.L12 g 0 = 0 →
      ∀ q ≤ 4, MeasureTheory.IntegrableOn
          (fun z => (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 g z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 g z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 4 g := by
  refine ⟨107 * (1 + ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2), ?_, ?_⟩
  · have h : (0:ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
      integral_nonneg (fun θ => sq_nonneg _)
    nlinarith
  · intro α hα hα1 g hO hmem h0 q hq
    obtain ⟨hgen, hInt0, hbnd0⟩ :=
      Work.FTS.OpenPkg.l12_open_bundle α g hα hα1 hO hmem h0
    have hK2nn : (0:ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
      integral_nonneg (fun θ => sq_nonneg _)
    have hHnn : (0:ℝ) ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
    cases q with
    | zero =>
      have hfun : (fun z => (Work.Spaces.DzIter 0
            (fun z _ => Work.Construction.L12 g z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
          = fun z => (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        funext z
        simp only [Work.Spaces.DzIter_zero]
        rfl
      rw [hfun]
      obtain ⟨-, hQbnd⟩ := Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open
        (α := α) (g := g) hα hα1 hO hmem (i := 0) (by norm_num)
      exact ⟨hInt0, by nlinarith [hbnd0, hQbnd, hK2nn, hHnn]⟩
    | succ k =>
      have hk3 : k ≤ 3 := by omega
      obtain ⟨hQint, hQbnd⟩ := Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open
        (α := α) (g := g) hα hα1 hO hmem (i := k) (by omega)
      have haeeq : (fun z => (Work.Spaces.DzIter (k+1)
            (fun z _ => Work.Construction.L12 g z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
          =ᵐ[volume.restrict Work.Spaces.Iz]
          (fun z => (Work.Elliptic.Qang g k z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        rw [← Work.Elliptic.restrict_Ioi_eq_restrict_Iz]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
        show Work.Spaces.DzIter (k+1) (fun z _ => Work.Construction.L12 g z) z 0 ^ 2
              * (Work.Spaces.w z) ^ 2
            = (Work.Elliptic.Qang g k z) ^ 2 * (Work.Spaces.w z) ^ 2
        have h1 : Work.Spaces.DzIter (k+1) (fun z _ => Work.Construction.L12 g z) z 0
            = Work.Elliptic.DzdIter (k+1) (fun z => Work.Construction.L12 g z) z :=
          Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 g z) (k+1) z 0
        have h2 : Work.Elliptic.DzdIter (k+1) (fun z => Work.Construction.L12 g z) z
            = - Work.Elliptic.Qang g k z := hgen k hk3 z hz
        rw [h1, h2]
        ring
      refine ⟨hQint.congr haeeq.symm, ?_⟩
      rw [MeasureTheory.integral_congr_ae (μ := volume.restrict Work.Spaces.Iz) haeeq]
      nlinarith [hQbnd, hK2nn, hHnn]

end Work.FTS.StrongPersist.L3Aux
