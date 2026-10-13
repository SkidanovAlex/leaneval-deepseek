/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/mixedTrunc/QuadBasic`

Smoothness/continuity facts on the **open quadrant** `Q = (0,∞) × (0,π/2)` for a datum `u` that
is `C^n` on the open quadrant for every `n` (the smoothness field of
`Work.FTS.EllipticEst.H2W.Ae.AeData`), together with the resulting a.e. strong measurability of
`θ`-integrals of functions continuous on `Q`.

The declarations here are the shared input of the pieces
`Deleg/mixedTrunc/{sliceCollarLe,sliceMemAe,outerIntegrable}` and of the target
`Work.FTS.EllipticEst.Deleg.mixedTruncPairLe`.

`∀ n, ContDiffOn ℝ n F Q` is *not* `ContDiffOn ℝ ⊤ F Q` in this Mathlib (the order `⊤` is the
analytic order `ω`); it *is* `C^∞` (`ContDiffOn ℝ Work.Stability.smoothOrder F Q`, with
`Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)`), by `contDiffOn_infty`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.RadCutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The open quadrant -/

/-- The open quadrant `Q = (0,∞) × (0,π/2)`. -/
abbrev quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_quad : IsOpen quad := isOpen_Ioi.prod isOpen_Ioo

theorem mem_quad_iff {p : ℝ × ℝ} : p ∈ quad ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 :=
  Iff.rfl

theorem mem_quad {z θ : ℝ} : (z, θ) ∈ quad ↔ 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 :=
  Iff.rfl

/-! ## The smoothness ladder -/

/-- `C^n` on `Q` for every `n` is `C^∞` on `Q`. -/
theorem contDiffOn_smoothOrder_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) quad :=
  contDiffOn_infty.mpr hu

/-- `∂_z^k` preserves `C^∞` on the open quadrant. -/
theorem contDiffOn_pzIter_quad' {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quad) (k : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pzIter k g)) quad := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.Spaces.pz (Work.Spaces.pzIter k g))) quad
      exact Work.FTS.LocData.contDiffOn_pz isOpen_quad ih

/-- `∂_θ^k` preserves `C^∞` on the open quadrant. -/
theorem contDiffOn_pthIter_quad' {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quad) (k : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pthIter k g)) quad := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pthIter k g))) quad
      exact Work.FTS.LocData.contDiffOn_pth isOpen_quad ih

theorem contDiffOn_pzIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pzIter k u)) quad :=
  contDiffOn_pzIter_quad' (contDiffOn_smoothOrder_quad hu) k

theorem contDiffOn_pthIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pthIter k u)) quad :=
  contDiffOn_pthIter_quad' (contDiffOn_smoothOrder_quad hu) k

/-- Any `∂_z^k ∂_θ^i u` is `C^∞` on the open quadrant. -/
theorem contDiffOn_pzIter_pthIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k i : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pzIter k (Work.Spaces.pthIter i u))) quad :=
  contDiffOn_pzIter_quad' (contDiffOn_pthIter_quad hu i) k

theorem continuousOn_pzIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter k u p.1 p.2) quad :=
  (contDiffOn_pzIter_quad hu k).continuousOn

theorem continuousOn_pthIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter k u p.1 p.2) quad :=
  (contDiffOn_pthIter_quad hu k).continuousOn

theorem continuousOn_pzIter_pthIter_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter k (Work.Spaces.pthIter i u) p.1 p.2)
      quad :=
  (contDiffOn_pzIter_pthIter_quad hu k i).continuousOn

/-- `U z = z ∂_z u` is a continuous function of `(z,θ)` on the open quadrant. -/
theorem continuousOn_Uz_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2) quad :=
  (continuousOn_fst.mul (continuousOn_pzIter_quad hu 1)).congr (fun p _ => rfl)

/-- `V z = z ∂_z∂_θ u` is a continuous function of `(z,θ)` on the open quadrant. -/
theorem continuousOn_Vz_quad {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2) quad :=
  (continuousOn_fst.mul (continuousOn_pzIter_pthIter_quad hu 1 1)).congr (fun p _ => rfl)

/-! ## The `θ`-slices -/

/-- The `θ`-slice of `∂_z^k u` is `C^∞` on `(0,π/2)` for `z > 0`. -/
theorem contDiffOn_slice_pzIter {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) (k : ℕ)
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.pzIter k u z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.LocData.contDiffOn_slice_θ (G := Work.Spaces.pzIter k u) (s := Set.Ioi 0)
    (t := Set.Ioo 0 (Real.pi / 2)) (contDiffOn_pzIter_quad hu k) hz

/-- The `θ`-slice of `∂_z∂_θ u` is `C^∞` on `(0,π/2)` for `z > 0`. -/
theorem contDiffOn_slice_pz_pth {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad)
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.pz (Work.Spaces.pth u) z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.LocData.contDiffOn_slice_θ (G := Work.Spaces.pz (Work.Spaces.pth u)) (s := Set.Ioi 0)
    (t := Set.Ioo 0 (Real.pi / 2)) (contDiffOn_pzIter_pthIter_quad hu 1 1) hz

/-- `U z = z ∂_z u` is `C¹` in `θ` on `(0,π/2)` for `z > 0`. -/
theorem contDiffOn_Uz_slice {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 1 (fun θ => Work.FTS.EllipticEst.AeColl.Uz u z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
  ((contDiffOn_slice_pzIter hu 1 hz).const_smul (z : ℝ)).of_le (by norm_num)

/-- Clairaut on the slice: `∂_θ (z ∂_z u) = z ∂_z∂_θ u` on the open quadrant. -/
theorem deriv_Uz_eq_Vz {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Work.FTS.EllipticEst.AeColl.Uz u z θ') θ
      = Work.FTS.EllipticEst.AeColl.Vz u z θ := by
  have hp : (z, θ) ∈ quad := ⟨hz, hθ⟩
  have h2 : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
    (hu 2).contDiffAt (isOpen_quad.mem_nhds hp)
  have hcomm : Work.Spaces.pz (Work.Spaces.pth u) z θ
      = Work.Spaces.pth (Work.Spaces.pz u) z θ := Work.Spaces.pz_pth_comm h2
  show deriv (fun θ' => z * Work.Spaces.pz u z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
  rw [deriv_const_mul_field]
  show z * Work.Spaces.pth (Work.Spaces.pz u) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth u) z θ
  rw [hcomm]

/-! ## A.e. strong measurability of `θ`-integrals on the quadrant -/

/-- The `θ`-integral over a measurable set `S ⊆ [0,π/2]` of a function continuous on the open
quadrant is a.e. strongly measurable as a function of `z` (Fubini). -/
theorem aesm_thetaIntegral_Ioi {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) quad) {S : Set ℝ}
    (hS : MeasurableSet S) (hSI : S ⊆ Work.Spaces.Iθ) :
    MeasureTheory.AEStronglyMeasurable (fun z => ∫ θ in S, F z θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hG : MeasureTheory.AEStronglyMeasurable
      ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => F p.1 p.2) hcont).indicator
      (MeasurableSet.univ.prod hS)
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2)) (z, θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hG.integral_prod_right'
  have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
        ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2)) (z, θ))
      = fun z => ∫ θ in S, F z θ := by
    funext z
    have hpt : (fun θ => ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2)) (z, θ))
        = (S.indicator (fun θ => F z θ)) := by
      funext θ
      by_cases h : θ ∈ S
      · rw [Set.indicator_of_mem (show (z, θ) ∈ (Set.univ ×ˢ S : Set (ℝ × ℝ)) from
            ⟨Set.mem_univ z, h⟩), Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem (show ¬((z, θ) ∈ (Set.univ ×ˢ S : Set (ℝ × ℝ))) from
            fun hh => h hh.2), Set.indicator_of_notMem h]
    calc (∫ θ in Work.Spaces.Iθ,
            ((Set.univ ×ˢ S).indicator (fun q : ℝ × ℝ => F q.1 q.2)) (z, θ))
        = ∫ θ in Work.Spaces.Iθ, (S.indicator (fun θ => F z θ)) θ := by rw [hpt]
      _ = ∫ θ in S, F z θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
            MeasureTheory.integral_indicator hS
      _ = ∫ θ in S, F z θ := by
            rw [MeasureTheory.Measure.restrict_restrict_of_subset hSI]
  rw [hfun] at h1
  exact h1.mono_measure (le_of_eq (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))))

end Work.FTS.EllipticEst.Deleg
