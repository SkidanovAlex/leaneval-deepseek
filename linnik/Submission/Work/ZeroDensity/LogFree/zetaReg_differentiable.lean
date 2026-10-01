import Mathlib
import Submission.Work.ZeroDensity.LogFree.GramResidueDefs

/-!
# `Work.ZeroDensity.LogFree.zetaReg_differentiable`

`zetaReg w = w · ζ(w+1)` redefined to be `1` at `w = 0`.  Since `ζ` has a simple pole of
residue `1` at `s = 1`, the function `w ↦ w · ζ(w+1) = (s-1)·ζ(s)` (with `s = w+1`) extends
to an entire function, the value at `w = 0` being `1`.  Hence `zetaReg` is differentiable on
all of `ℂ`.

The proof proceeds by the (weak) removable singularity theorem:
* away from `0`, `zetaReg` agrees locally with `w ↦ w · ζ(w+1)`, which is differentiable there
  because `ζ` is differentiable away from `1`;
* at `0`, `zetaReg = Function.update (fun w => w·ζ(w+1)) 0 1` is continuous, because
  `riemannZeta_residue_one` gives `(s-1)·ζ(s) → 1` as `s → 1`, and `s = w+1 → 1` as `w → 0`.
-/

open Complex Filter
open scoped Topology

noncomputable section

namespace Work.ZeroDensity.LogFree

/-- Away from `0`, `zetaReg` agrees with the function `w ↦ w·ζ(w+1)`, hence is differentiable
there: `ζ` is differentiable away from its pole `1`. -/
lemma differentiableAt_zetaReg_of_ne {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ zetaReg z := by
  have hev : zetaReg =ᶠ[𝓝 z] (fun w : ℂ => w * riemannZeta (w + 1)) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact zetaReg_of_ne hw
  rw [hev.differentiableAt_iff]
  have hz1 : z + 1 ≠ 1 := fun h => hz (by simpa using h)
  exact differentiableAt_id.mul
    ((differentiableAt_riemannZeta hz1).comp z (differentiableAt_id.add_const 1))

/-- The residue of `ζ` at `1`, transported to `w = 0`: `w·ζ(w+1) → 1` as `w → 0` through
nonzero values. -/
lemma tendsto_mul_riemannZeta_add_one :
    Tendsto (fun w : ℂ => w * riemannZeta (w + 1)) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  have hshift : Tendsto (fun w : ℂ => w + 1) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun w : ℂ => w + 1) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
        have h := ((continuousAt_id (x := (0 : ℂ))).add
          (continuousAt_const (y := (1 : ℂ)))).tendsto
        have hfun : (id + fun _ => (1 : ℂ)) = fun w : ℂ => w + 1 := by
          funext w; simp
        rw [hfun] at h
        simpa using h
      exact h.mono_left nhdsWithin_le_nhds
    · rw [eventually_nhdsWithin_iff]
      exact Eventually.of_forall fun w hw => by
        intro hcon
        exact hw (by simpa using hcon)
  have hcomp := riemannZeta_residue_one.comp hshift
  simpa [Function.comp_def] using hcomp

/-- `zetaReg` is continuous at `0`. -/
lemma continuousAt_zetaReg_zero : ContinuousAt zetaReg (0 : ℂ) := by
  rw [zetaReg, continuousAt_update_same]
  exact tendsto_mul_riemannZeta_add_one

/-- `zetaReg` is differentiable at `0`: it is differentiable on a punctured neighbourhood of `0`
and continuous at `0`, so the removable singularity theorem applies. -/
lemma differentiableAt_zetaReg_zero : DifferentiableAt ℂ zetaReg (0 : ℂ) := by
  have hd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ zetaReg z := by
    filter_upwards [(self_mem_nhdsWithin : ({0}ᶜ : Set ℂ) ∈ 𝓝[≠] (0 : ℂ))] with z hz
    exact differentiableAt_zetaReg_of_ne hz
  exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd
    continuousAt_zetaReg_zero).differentiableAt

theorem zetaReg_differentiable : Differentiable ℂ Work.ZeroDensity.LogFree.zetaReg := by
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact differentiableAt_zetaReg_zero
  · exact differentiableAt_zetaReg_of_ne hz

end Work.ZeroDensity.LogFree
