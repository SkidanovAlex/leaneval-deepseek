/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): integrability of the transported unknown
and source against compactly supported cut-offs.

The unknown `Vc α Ψ` of the strip problem is generally *not* locally integrable on the whole
plane, even when `Ψ` is locally integrable on the open quadrant: the strip `stripE` has the
boundaries `θ = 0` and `θ = π/2` and `Ψ` may blow up there (e.g. `Ψ = 1/θ`).  It is, however,
locally integrable when multiplied by a cut-off whose support is a *compact* subset of the
strip; that is what this file proves, by pulling back along `coords` and applying
`VT.pullbackIntegrable`.

The source `Gc α F` is actually `C^∞` on the strip when `F` is, so the corresponding statement
is immediate.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Work.EllipticEst.InteriorRegularity.VT.Basic
import Submission.Work.EllipticEst.InteriorRegularity.VT.Td
import Submission.Work.EllipticEst.InteriorRegularity.VT.Smooth
import Submission.Work.EllipticEst.InteriorRegularity.VT.pullbackIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- An integrable function on a set, multiplied by a compactly supported smooth function, is
still integrable on that set. -/
theorem integrableOn_mul_of_cc {f : E2 → ℂ} {s : Set E2} (hf : IntegrableOn f s)
    {g : E2 → ℂ} (hc : HasCompactSupport g) (hs : ∀ n : ℕ, ContDiff ℝ n g) :
    IntegrableOn (fun x => g x * f x) s := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_cc hc hs
  refine Integrable.mono' (hf.norm.const_mul C) ?_ ?_
  · exact ((hs 0).continuous.aestronglyMeasurable).mul hf.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem mul_Vc_eq_mul_Ws {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {χ : E2 → ℂ}
    (hχsub : tsupport χ ⊆ stripE) :
    (fun x => χ x * Vc α Ψ x) = fun x => χ x * Ws α Ψ x := by
  funext x
  by_cases hx : x ∈ stripE
  · rw [Vc_of_mem hx]
  · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχsub h))
    rw [Vc_of_notMem hx, mul_zero, hz, zero_mul]

/-- The un-indicated unknown `Ws α Ψ` is integrable on the (compact) support of any cut-off
supported in the strip. -/
theorem integrableOn_Ws {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {χ : E2 → ℂ} (hχc : HasCompactSupport χ) (hχsub : tsupport χ ⊆ stripE) :
    IntegrableOn (Ws α Ψ) (tsupport χ) := by
  have hcoord : Continuous (fun x : E2 => (x 0, x 1)) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)).prodMk
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2))
  have hpre : (fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹' tsupport χ
      = (fun x : E2 => (x 0, x 1)) '' tsupport χ := by
    ext p
    constructor
    · intro hp
      cases p with
      | mk a b =>
        exact ⟨coords a b, hp, by simp [coords_zero, coords_one]⟩
    · rintro ⟨y, hy, hpy⟩
      have hyy : coords (y 0) (y 1) = y := by
        ext i
        fin_cases i <;> simp [coords]
      rw [← hpy]
      change coords (y 0) (y 1) ∈ tsupport χ
      rw [hyy]
      exact hy
  have hK : IsCompact ((fun x : E2 => (x 0, x 1)) '' tsupport χ) :=
    (show IsCompact (tsupport χ) from hχc).image hcoord
  have hKs : (fun x : E2 => (x 0, x 1)) '' tsupport χ
      ⊆ Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rintro p ⟨x, hx, rfl⟩
    have h := hχsub hx
    rw [mem_stripE] at h
    exact ⟨trivial, h.1, h.2⟩
  have hpb := pullbackIntegrable hα hΨ hK hKs
  have hcomp : IntegrableOn ((Ws α Ψ) ∘ (fun p : ℝ × ℝ => coords p.1 p.2))
      ((fun x : E2 => (x 0, x 1)) '' tsupport χ) := by
    refine hpb.congr_fun (fun p _ => ?_) hK.measurableSet
    simp only [Function.comp_apply, Ws_apply, wt_coords hα.ne', coords_zero, coords_one]
  have key := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
    coords_measurePreserving coords_measurableEmbedding (f := Ws α Ψ) (s := tsupport χ)
  rw [hpre] at key
  exact key.mp hcomp

/-- A smooth cut-off supported in the strip, times the unknown of the strip problem, is
integrable. -/
theorem integrable_mul_Vc {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {χ : E2 → ℂ} (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hχc : HasCompactSupport χ)
    (hχsub : tsupport χ ⊆ stripE) :
    Integrable (fun x => χ x * Vc α Ψ x) := by
  have hWs : IntegrableOn (Ws α Ψ) (tsupport χ) := integrableOn_Ws hα hΨ hχc hχsub
  have hmul : IntegrableOn (fun x => χ x * Ws α Ψ x) (tsupport χ) :=
    integrableOn_mul_of_cc hWs hχc hχs
  have hsupp : Function.support (fun x => χ x * Ws α Ψ x) ⊆ tsupport χ := by
    intro x hx
    by_contra hxn
    rw [Function.mem_support] at hx
    rw [image_eq_zero_of_notMem_tsupport hxn, zero_mul] at hx
    exact hx rfl
  have hind : Integrable ((tsupport χ).indicator (fun x => χ x * Ws α Ψ x)) :=
    (integrable_indicator_iff (show IsCompact (tsupport χ) from hχc).measurableSet).mpr hmul
  rw [indicator_eq_self.mpr hsupp] at hind
  exact hind.congr (Filter.Eventually.of_forall fun x =>
    (congrFun (mul_Vc_eq_mul_Ws hχsub) x).symm)

/-- A smooth cut-off supported in the strip, times the transported source, is integrable. -/
theorem integrable_mul_Gc {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hα : α ≠ 0) {χ : E2 → ℂ}
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ) (hχc : HasCompactSupport χ)
    (hχsub : tsupport χ ⊆ stripE) :
    Integrable (fun x => χ x * Gc α F x) :=
  integrable_of_smooth_compact (hχc.mul_right) (contDiff_mul_Gc hF hα hχs hχsub)

end Work.EllipticEst.InteriorRegularity.VT
