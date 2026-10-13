/-
Copyright: work module for the Elgindi finite-time singularity project.

# `OpenPkg/ScoefOpen` — the Stirling expansion of `D_z^n` on the open half-line `(0,∞)`

The interior estimates of the open-quadrant package (`Work.FTS.VocabO.WDp`) need the bound
`|D_z^b f| ≤ 15 |f|_{𝒲^{4,∞}}` *inside the open quadrant*, from the hypothesis
`Work.FTS.EllipticEst.SmoothOpen f` (`C^∞` on `(0,∞) × (0,π/2)` only).  The available
statements of the Stirling expansion

* `Work.Spaces.DzIter_eq_sum_scoef` (analytic order `⊤`, slices on `(-1,∞)`), and
* `Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth` (genuine smooth order, slices on `(-1,∞)`)

both require the `z`-slices at *every* `θ ∈ [0,π/2]`, which `SmoothOpen` does not supply: the
`z`-slices of a `SmoothOpen` function need not even be differentiable at the two boundary
angles.  This module redoes the expansion with the half-line `(0,∞)` and the genuine smooth
order `Work.Stability.smoothOrder = ∞`, which is exactly the data available inside the
quadrant, together with the elementary consequence that all the slices of a `SmoothOpen`
function (and of its `D_θ`-iterates) are smooth on `(0,∞)`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The slices of a `SmoothOpen` function -/

/-- The `z`-slice of a `SmoothOpen` function at an interior angle is `C^∞` on the open
half-line `(0,∞)` (in the genuine smooth order). -/
theorem smoothOpen_slice_z {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z hf hθ

/-- `D_θ` preserves the open-quadrant smooth class. -/
theorem smoothOpen_DthIter {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (a : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DthIter a f) :=
  Work.FTS.LocData.contDiffOn_DthIter Work.FTS.EllipticEst.isOpen_Q0 hf a

/-- The `z`-slice of `D_θ^a f` at an interior angle is `C^∞` on `(0,∞)`. -/
theorem smoothOpen_DthIter_slice_z {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (a : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => Work.Spaces.DthIter a f z θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z (smoothOpen_DthIter hf a) hθ

/-! ## The Stirling expansion in the genuine smooth order on `(0,∞)` -/

private theorem deriv_zpow_open (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  rw [h, deriv_id'']
  ring

private theorem z_mul_term_open (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- In the genuine smooth order, the `z`-slices of the iterated `z`-derivatives are again
smooth on the open half-line `(0,∞)`. -/
theorem pzIter_slice_contDiff_open {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0)) :
    ∀ k : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.pzIter k h z' θ) (Set.Ioi 0) := by
  intro k
  induction k with
  | zero => simpa using hsmooth
  | succ n ih =>
    have h := ih.deriv_of_isOpen isOpen_Ioi
      (le_of_eq (rfl : Work.Stability.smoothOrder + 1 = Work.Stability.smoothOrder))
    simpa [Work.Spaces.pzIter_succ, Work.Spaces.pz] using h

private theorem differentiableAt_pzIter_slice_open {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0)) (k : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z :=
  ((pzIter_slice_contDiff_open hsmooth k).contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt
    (by simp)

private theorem deriv_pzIter_slice_open (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => Work.Spaces.pzIter k h z' θ) z = Work.Spaces.pzIter (k + 1) h z θ := rfl

/-- **The Stirling expansion of `D_z^n` in the genuine smooth order, on the open half-line.**
For a function whose `z`-slice at the fixed angle `θ` is `C^∞` on `(0,∞)`,
`D_z^n h = ∑_{k≤n} S(n,k) z^k ∂_z^k h` on `(0,∞)`. -/
theorem DzIter_eq_sum_scoef_open {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0)) :
    ∀ n : ℕ, ∀ z ∈ Set.Ioi 0,
      Work.Spaces.DzIter n h z θ
        = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z ^ k * Work.Spaces.pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
    intro z hz
    simp [Work.Spaces.DzIter, Work.Spaces.scoef]
  | succ n ih =>
    intro z hz
    have hdiff : ∀ k : ℕ, DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z := fun k =>
      differentiableAt_pzIter_slice_open hsmooth k hz
    have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
      differentiableAt_pow k
    have hd3 : ∀ k : ℕ,
        DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z :=
      fun k => (hd1 k).mul (hdiff k)
    have hev : (fun z' => Work.Spaces.DzIter n h z' θ)
        =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih z' hz'
    have hterm : ∀ k : ℕ,
        deriv (fun z' : ℝ => (Work.Spaces.scoef n k : ℝ)
            * (z' ^ k * Work.Spaces.pzIter k h z' θ)) z
        = (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
            + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
      intro k
      rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
        (Work.Spaces.scoef n k : ℝ) (hd3 k)]
      congr 1
      have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
        (d := fun z' : ℝ => Work.Spaces.pzIter k h z' θ) (hd1 k) (hdiff k)
      have hmul' : deriv (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z
          = deriv (fun z' : ℝ => z' ^ k) z * Work.Spaces.pzIter k h z θ
            + z ^ k * deriv (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) z := hmul
      rw [hmul', deriv_zpow_open, deriv_pzIter_slice_open]
    have hderiv : deriv (fun z' => Work.Spaces.DzIter n h z' θ) z
        = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
              + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ))
          = (∑ k ∈ Finset.range (n + 1),
              fun z' => (Work.Spaces.scoef n k : ℝ)
                * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
        funext z'
        simp [Finset.sum_apply]
      rw [hsumfun, deriv_sum (fun k hk => (hd3 k).const_mul (Work.Spaces.scoef n k : ℝ))]
      exact Finset.sum_congr rfl fun k hk => hterm k
    calc Work.Spaces.DzIter (n + 1) h z θ
        = z * deriv (fun z' => Work.Spaces.DzIter n h z' θ) z := by
          simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      _ = z * (∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
              + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by rw [hderiv]
      _ = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ k * Work.Spaces.pzIter k h z θ
              + z ^ (k + 1) * Work.Spaces.pzIter (k + 1) h z θ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have h1 : z * ((Work.Spaces.scoef n k : ℝ)
                * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ))
              = (Work.Spaces.scoef n k : ℝ)
                * (z * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by ring
          rw [h1, z_mul_term_open]
      _ = ∑ j ∈ Finset.range (n + 2),
            (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * Work.Spaces.pzIter j h z θ) :=
          Work.Spaces.scoef_sum_shift n (fun k => Work.Spaces.pzIter k h z θ) z

end Work.FTS.OpenPkg
