/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `f`-side pointwise bounds in the interior class `SmoothQuad`

For a function `f` which is `C^∞` on the open quadrant (`Work.FTS.LocData.SmoothQuad`) and of
class `𝒲^{4,∞}` (`Work.Spaces.WlInfMem α 4 f`) we need, inside the quadrant,

* `|D_z^b f| ≤ 15 |f|_𝒲` for `b ≤ 4`, and
* `|D_z^b D_θ^a f| ≤ 15 |f|_𝒲 · (α + sin 2θ) sin(2θ)^{α/5}` for `1 ≤ a`, `a + b ≤ 4`.

These are the interior counterparts of `Work.Spaces.DzIter_le_WlInf` /
`Work.Spaces.mixed_le_WlInf`, whose hypothesis is `SmoothInt`: smoothness of the `z`-slices on
`(-1,∞)` at *every* `θ ∈ Iθ`, including the two boundary angles `θ = 0, π/2`.  In the interior
class only `θ ∈ (0,π/2)` is available, and indeed the corresponding statement at `θ = 0, π/2`
is in general false (the `z`-slices of a `SmoothQuad` function need not even be differentiable
at `z = 0`).

The engine is the Stirling expansion `D_z^n = ∑_{k≤n} S(n,k) z^k ∂_z^k`
(`Work.Spaces.scoef`, `Work.Spaces.scoef_sum_shift`), which
`Work.Spaces.DzIter_eq_sum_scoef` proves in the *analytic* order `⊤`; here it is redone in the
genuine `C^∞` order `Work.Stability.smoothOrder`, the order in which `SmoothQuad` is stated.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces

/-! ## The Stirling expansion in the genuine `C^∞` order -/

private theorem deriv_zpow' (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  rw [h, deriv_id'']; ring

private theorem z_mul_term' (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- In the genuine smooth order, the `z`-slices of the iterated `z`-derivatives are again
smooth.  (`Work.Spaces.pzIter_slice_contDiff` is the analytic-order version.) -/
theorem pzIter_slice_contDiff_smooth {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1))) :
    ∀ k : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.pzIter k h z' θ) (Set.Ioi (-1)) := by
  intro k
  induction k with
  | zero => simpa using hsmooth
  | succ n ih =>
    have h := ih.deriv_of_isOpen isOpen_Ioi (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    simpa [Work.Spaces.pzIter_succ, Work.Spaces.pz] using h

private theorem differentiableAt_pzIter_slice_smooth {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1))) (k : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z :=
  ((pzIter_slice_contDiff_smooth hsmooth k).contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt
    (by simp)

private theorem deriv_pzIter_slice' (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => Work.Spaces.pzIter k h z' θ) z = Work.Spaces.pzIter (k + 1) h z θ := rfl

/-- **The Stirling expansion of `D_z^n` in the genuine smooth order.**  For a function whose
`θ`-slice at the fixed angle `θ` is `C^∞` in the genuine `C^∞` order on `(-1,∞)`,
`D_z^n h = ∑_{k≤n} S(n,k) z^k ∂_z^k h` on that half-line.  (The analytic-order counterpart is
`Work.Spaces.DzIter_eq_sum_scoef`.) -/
theorem DzIter_eq_sum_scoef_smooth {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1))) :
    ∀ n : ℕ, ∀ z ∈ Set.Ioi (-1),
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
      differentiableAt_pzIter_slice_smooth hsmooth k hz
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
      rw [hmul', deriv_zpow', deriv_pzIter_slice']
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
          rw [h1, z_mul_term']
      _ = ∑ j ∈ Finset.range (n + 2),
            (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * Work.Spaces.pzIter j h z θ) :=
          Work.Spaces.scoef_sum_shift n (fun k => Work.Spaces.pzIter k h z θ) z

/-- The Bell numbers of the rows `0 ≤ n ≤ 4` are `1, 1, 2, 5, 15`. -/
theorem bell_le_15 (n : ℕ) (hn : n ≤ 4) : Work.Spaces.bell n ≤ 15 := by
  interval_cases n <;> decide

/-- `WlInf` is nonnegative when the finitely many suprema occurring in it are finite.
(The `Work.Spaces.WProductRule` version is a private helper of that module.) -/
theorem WlInf_nonneg' {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 4 f) :
    0 ≤ Work.Spaces.WlInf α 4 f :=
  add_nonneg (Work.Spaces.wlZSum_nonneg α 4 f hmem) (Work.Spaces.wlThSum_nonneg α 4 f hmem)

/-! ## The two pointwise bounds -/

/-- **The `f`-side `D_z`-bound in the interior class `SmoothQuad`.** -/
theorem DzIter_le_WlInf {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hfm : Work.Spaces.WlInfMem α 4 f)
    {b : ℕ} (hb : b ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.DzIter b f z θ| ≤ 15 * Work.Spaces.WlInf α 4 f := by
  have hz' : z ∈ Set.Ioi (-1) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    exact Set.mem_Ioi.mpr (by linarith)
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi (-1)) :=
    hf.curry_z hθ
  rw [DzIter_eq_sum_scoef_smooth hslice b z hz']
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (Work.Spaces.WlInf α 4 f)
    (fun k => z ^ k * Work.Spaces.pzIter k f z θ)
    (fun k hk => Work.Spaces.zpz_le_WlInf hfm (le_trans hk hb) hz hθI)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 15 := by
    exact_mod_cast bell_le_15 b hb
  calc |∑ k ∈ Finset.range (b + 1),
        (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * Work.Spaces.WlInf α 4 f := hsum
    _ ≤ 15 * Work.Spaces.WlInf α 4 f := by
        have hW : 0 ≤ Work.Spaces.WlInf α 4 f := WlInf_nonneg' hfm
        exact mul_le_mul_of_nonneg_right hbell hW

/-- **The `f`-side bound for mixed derivatives in the interior class `SmoothQuad`.** -/
theorem Mixed_le_WlInf {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hfm : Work.Spaces.WlInfMem α 4 f)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 15 * (Work.Spaces.WlInf α 4 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  have hz' : z ∈ Set.Ioi (-1) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    exact Set.mem_Ioi.mpr (by linarith)
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hW := WlInf_nonneg' hfm
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter a f z' θ) (Set.Ioi (-1)) :=
    (hf.DthIter a).curry_z hθ
  have hmixed : Work.Spaces.mixed b a f z θ
      = ∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ) :=
    DzIter_eq_sum_scoef_smooth hslice b z hz'
  rw [hmixed]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b
    (Work.Spaces.WlInf α 4 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
    (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ)
    (fun k hk => Work.Spaces.zpz_Dth_le_WlInf hα hfm ha (by omega) hz hθI)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 15 := by
    exact_mod_cast bell_le_15 b (by omega)
  have hfac : 0 ≤ Work.Spaces.WlInf α 4 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    mul_nonneg hW (mul_nonneg (by linarith [Work.Spaces.sin_two_nonneg' hθI])
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg' hθI) _))
  calc |∑ k ∈ Finset.range (b + 1),
        (Work.Spaces.scoef b k : ℝ)
          * (z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ)|
      ≤ (Work.Spaces.bell b : ℝ)
          * (Work.Spaces.WlInf α 4 f * ((α + Real.sin (2 * θ))
              * (Real.sin (2 * θ)) ^ (α / 5))) := hsum
    _ ≤ 15 * (Work.Spaces.WlInf α 4 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right hbell hfac

end Work.FTS.H2.WPQ
