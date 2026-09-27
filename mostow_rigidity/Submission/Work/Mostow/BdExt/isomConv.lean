import Mathlib
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.poBdAlg
import Submission.Work.Mostow.BdExt.actODirv
import Submission.Work.Mostow.BdExt.spatTheta
import Submission.Work.Mostow.BdExt.nullDir

/-!
# `isomConv`: continuity of the action on the visual compactification

If a sequence `u k` in the chart of `ℍⁿ` escapes to infinity (`‖u k‖ → ∞`) with Euclidean
directions converging to `ξ ∈ Sph n`, then for every `g : PO n 1` the sequence `g • u k` escapes
with directions converging to `bd g ξ`.

The proof is explicit linear algebra on the hyperboloid.  Write `A := rep g` for the matrix
representative of `g`, let `θ ξ = (ξ, 1)` be the null vector over `ξ` (so that `bdO A ξ` is the
direction of `mat A *ᵥ θ ξ`), and for `u ≠ 0` let `ŵ u := ‖u‖⁻¹ • hlift u` be the *normalised*
lift, whose spatial part is `dirv u`.  Then

* `hlift u = ‖u‖ • ŵ u`, so the spatial part of `mat A *ᵥ hlift u` is a positive multiple of the
  spatial part of `mat A *ᵥ ŵ u`;
* consequently `dirv (actO A u) = dirv (tsign A • spat (mat A *ᵥ ŵ u))` (`actODirv`);
* `ŵ u k → θ ξ` because `dirv (u k) → ξ` and `tpart (u k)/‖u k‖ → 1` (`nullDir`);
* finally `dirv (tsign A • spat (mat A *ᵥ θ ξ)) = bdO A ξ` (`spatTheta`), the only point where the
  sign `tsign A` matters: it is the sign of the time coordinate of `mat A *ᵥ θ ξ`, which follows
  from the estimate `|∑ᵢ aᵢ ξᵢ| ≤ √(a₀² − 1) < |a₀|` for the last row `(a₀, a)` of the
  `J`-orthogonal matrix `mat A`.

Composing the continuous map `w ↦ spat (mat A *ᵥ w)` and the continuity of `dirv` at a non-zero
point gives the result.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Filter

noncomputable section

set_option linter.unusedVariables false

variable {n : ℕ}

/-- The map `w ↦ spat (mat A *ᵥ w)` is continuous: it is the spatial projection of a linear map
between finite dimensional spaces. -/
lemma continuous_spat_mulVec (A : O1 n) :
    Continuous (fun w : Fin n ⊕ Fin 1 → ℝ => Hyper.spat ((mat A).mulVec w)) := by
  have h1 : Continuous (fun w : Fin n ⊕ Fin 1 → ℝ => (mat A).mulVec w) :=
    (Matrix.mulVecLin (mat A)).continuous_of_finiteDimensional
  have h2 : Continuous (fun z : Fin n ⊕ Fin 1 → ℝ =>
      WithLp.toLp 2 (fun i : Fin n => z (Sum.inl i))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
      (continuous_pi fun i => continuous_apply (Sum.inl i))
  exact h2.comp h1

/-- `dirv` is continuous at every non-zero point. -/
lemma continuousAt_dirv {v : E n} (hv : v ≠ 0) : ContinuousAt dirv v := by
  have h : ContinuousAt (fun z : E n => (‖z‖)⁻¹) v :=
    continuous_norm.continuousAt.inv₀ (by rwa [norm_ne_zero_iff])
  have h2 := h.smul (continuousAt_id (x := v))
  convert h2 using 1
  ext z
  simp [dirv]

theorem isomConv (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (u : ℕ → Submission.Mostow.E n) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hu : Filter.Tendsto (fun k => ‖u k‖) Filter.atTop Filter.atTop)
    (hd : Filter.Tendsto (fun k => Work.Mostow.BdExt.dirv (u k)) Filter.atTop (nhds ξ)) :
    Filter.Tendsto (fun k => Work.Mostow.BdExt.dirv (g • u k)) Filter.atTop
      (nhds (Submission.Mostow.bd g ξ)) := by
  have hW : Tendsto (fun k => (‖u k‖)⁻¹ • hlift (u k)) atTop (nhds (theta ξ)) :=
    nullDir n u ξ hu hd
  have hV : Tendsto (fun k => Hyper.spat ((mat (rep g)).mulVec ((‖u k‖)⁻¹ • hlift (u k))))
      atTop (nhds (Hyper.spat ((mat (rep g)).mulVec (theta ξ)))) :=
    ((continuous_spat_mulVec (rep g)).tendsto _).comp hW
  have hV' : Tendsto (fun k => tsign (rep g) •
      Hyper.spat ((mat (rep g)).mulVec ((‖u k‖)⁻¹ • hlift (u k)))) atTop
      (nhds (tsign (rep g) • Hyper.spat ((mat (rep g)).mulVec (theta ξ)))) :=
    hV.const_smul (tsign (rep g))
  have hne : tsign (rep g) • Hyper.spat ((mat (rep g)).mulVec (theta ξ)) ≠ 0 := by
    intro h0
    have h1 := spatTheta n (rep g) ξ hξ
    rw [h0, dirv, norm_zero, inv_zero, zero_smul] at h1
    have h2 : ‖bdO (rep g) ξ‖ = 1 := (mem_Sph_iff _).1 ((poBdAlg n).1 (rep g) ξ hξ)
    rw [← h1] at h2
    simp at h2
  have hdirv : Tendsto (fun k => dirv (tsign (rep g) •
      Hyper.spat ((mat (rep g)).mulVec ((‖u k‖)⁻¹ • hlift (u k))))) atTop
      (nhds (bdO (rep g) ξ)) := by
    have hcomp := (continuousAt_dirv hne).tendsto.comp hV'
    rwa [spatTheta n (rep g) ξ hξ] at hcomp
  have hev : (fun k => dirv (tsign (rep g) •
      Hyper.spat ((mat (rep g)).mulVec ((‖u k‖)⁻¹ • hlift (u k)))))
      =ᶠ[atTop] (fun k => dirv (g • u k)) := by
    filter_upwards [hu.eventually (eventually_ge_atTop (1 : ℝ))] with k hk
    have hk0 : u k ≠ 0 := by
      intro h; rw [h, norm_zero] at hk; linarith
    exact (actODirv n (rep g) (u k) hk0).symm
  exact Filter.Tendsto.congr' hev hdirv

end

end Work.Mostow.BdExt
