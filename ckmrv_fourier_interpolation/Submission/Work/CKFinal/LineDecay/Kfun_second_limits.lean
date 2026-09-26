/-
# The residues of `K^{(d)}(τ, ·)` in the second variable, in the `ℂ`-coordinate

CKMRV Section 5.3 shifts the contour of the layer representation in the *second* variable `z`
of the kernel; the poles picked up are the poles of `z ↦ K^{(d)}(τ,z)` on the `SL(2,ℤ)`-orbit
of `τ`, namely `z = τ - 1`, `z = τ + 1` and the diagonal `z = τ`.  The residue computation
itself is the content of `Work.Residues.hasResidue_Kfun_second'` (`z = τ - 1`, residue
`1/(2π)`), of `Work.LayerCont.Right.hasResidue_Kfun_tauAddOne` (`z = τ + 1`, residue
`-1/(2π)`) and of `hasResidue_Kfun_self` below (the *diagonal*, residue `0`).

What the contour shift actually consumes, however, is the residue at a point of `ℂ`: the
rectangular contour lives in `ℂ` and the integrand is
`z ↦ K^{(d)}(τ, UpperHalfPlane.ofComplex z)`.  This file therefore provides the bridge from the
`ℍ`-valued residue notion `Work.Residues.HasResidue` to the `ℂ`-valued limit

  `(z - w) · K^{(d)}(τ, ofComplex z) → c`  as `z → w`, `z ≠ w`,

and then states the three resulting limits in the exact form
`Work.CKFinal.LineDecay.Kfun_second_limits` used by the contour-shift
(`Work.Asymptotics.rectInt_eq_residue`).

## Main results

* `Work.CKFinal.LineDecay.tendsto_of_hasResidue_ofComplex` : the `ℍ`-to-`ℂ` bridge.
* `Work.CKFinal.LineDecay.hasResidue_Kfun_self` : `Res_{ζ=τ} K^{(d)}(τ,ζ) = 0`
  (the diagonal pole is removable: the cleared kernel `AfunFun` vanishes there).
* `Work.CKFinal.LineDecay.Kfun_second_limits` : the three limits.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.LayerCont.Right.Defs
import Submission.Work.Asymptotics.kerFormAux

namespace Work.CKFinal.LineDecay

open UpperHalfPlane
open Filter
open scoped Topology Manifold

/-! ## From a residue in `ℍ` to a limit in `ℂ`

`Work.Residues.HasResidue f w c` is the statement `(ζ - w)·f ζ → c` for `ζ : ℍ`, `ζ → w`,
`ζ ≠ w`; the target statement of this file is the corresponding limit for the variable
`z : ℂ` running over a *punctured neighbourhood of `w` in `ℂ`*, the function being
`z ↦ f (UpperHalfPlane.ofComplex z)`.

The reduction is the observation that `ofComplex` is a section of the open embedding
`UpperHalfPlane.coe`: it is continuous at every point of `ℍ`
(`Topology.IsEmbedding.tendsto_nhds_iff` applied to `eventuallyEq_coe_comp_ofComplex`), and it
is *injective* on the upper half plane, so it maps `𝓝[≠] w` into `𝓝[≠] w`.  Moreover
`z ↦ (z - w)·f (ofComplex z)` and `z ↦ ((ofComplex z : ℍ) - w)·f (ofComplex z)` agree
eventually, because `ofComplex z = ⟨z, _⟩` as soon as `z.im > 0`, which is an open condition
satisfied near `w` (as `w.im > 0`). -/
lemma tendsto_of_hasResidue_ofComplex {f : ℍ → ℂ} {w : ℍ} {c : ℂ}
    (h : Work.Residues.HasResidue f w c) :
    Filter.Tendsto (fun z : ℂ => (z - (w : ℂ)) * f (UpperHalfPlane.ofComplex z))
      (nhdsWithin (w : ℂ) {(w : ℂ)}ᶜ) (nhds c) := by
  have hwim : 0 < ((w : ℂ)).im := by rw [UpperHalfPlane.coe_im]; exact w.im_pos
  have hmem : UpperHalfPlane.upperHalfPlaneSet ∈ 𝓝 (w : ℂ) :=
    IsOpen.mem_nhds UpperHalfPlane.isOpen_upperHalfPlaneSet hwim
  -- `ofComplex` pushes the punctured neighbourhood of `w : ℂ` into the punctured
  -- neighbourhood of `w : ℍ`
  have hcomp : Filter.Tendsto
      (fun z : ℂ => (((UpperHalfPlane.ofComplex z : ℍ) : ℂ) - (w : ℂ))
        * f (UpperHalfPlane.ofComplex z))
      (𝓝[≠] (w : ℂ)) (𝓝 c) := by
    have hof : Filter.Tendsto UpperHalfPlane.ofComplex (𝓝[≠] ((w : ℂ))) (𝓝[≠] w) := by
      rw [nhdsWithin, nhdsWithin, tendsto_inf, tendsto_principal]
      refine ⟨?_, ?_⟩
      · -- continuity of the section at a point of its range
        have hcont : Filter.Tendsto UpperHalfPlane.ofComplex (𝓝 ((w : ℂ))) (𝓝 w) := by
          rw [UpperHalfPlane.isEmbedding_coe.isInducing.tendsto_nhds_iff]
          exact Filter.Tendsto.congr'
            (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex (z := (w : ℂ)) hwim).symm
            tendsto_id
        exact hcont.mono_left inf_le_left
      · -- `ofComplex z ≠ w` near `w`, because `ofComplex z = ⟨z, _⟩` there
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with z hz hmemz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
        intro hzw
        have hcoe : (((UpperHalfPlane.ofComplex z : ℍ)) : ℂ) = ((w : ℍ) : ℂ) :=
          congrArg (fun t : ℍ => (t : ℂ)) hzw
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hmemz] at hcoe
        exact hz hcoe
    exact h.comp hof
  refine Filter.Tendsto.congr' ?_ hcomp
  filter_upwards [nhdsWithin_le_nhds hmem] with z hz
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-! ## The diagonal residue of the kernel -/

/-- **The residue of `ζ ↦ K^{(d)}(τ,ζ)` at the diagonal `ζ = τ` vanishes.**

Since the cleared kernel vanishes on the diagonal (`KPlusClear_diag`, `KMinusClear_diag`), so
does `AfunFun ℓ d τ τ = (AfunPlus d τ τ + AfunMinus ℓ d τ τ)/2`, and the general
`Work.Residues.hasResidue_of_cleared` computes the residue as
`AfunFun ℓ d τ τ / j'(τ) = 0`.  This is the `n = 0` case of the translate orbit
`ζ = τ + n`, cf. `Work.Asymptotics.hasResidue_Kfun_second_translate`. -/
lemma hasResidue_Kfun_self (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (hne : Work.Residues.jprime τ ≠ 0) :
    Work.Residues.HasResidue (fun ζ : ℍ => Work.Kernels.Kfun ℓ d τ ζ) τ 0 := by
  have hA0 : Work.Asymptotics.AfunFun ℓ d τ τ = 0 := by
    rw [Work.Asymptotics.AfunFun, Work.Residues.AfunPlus, Work.Residues.AfunMinus,
      Work.Residues.KPlusClear_diag d hd τ, Work.Residues.KMinusClear_diag ℓ d hd τ]
    simp
  have hA : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => - Work.Asymptotics.AfunFun ℓ d τ ζ) τ := by
    have h1 := Work.Residues.mdifferentiableAt_AfunPlus_snd d hd τ τ
    have h2 := Work.Residues.mdifferentiableAt_AfunMinus_snd ℓ d hd τ τ
    have h3 : (fun ζ : ℍ => - Work.Asymptotics.AfunFun ℓ d τ ζ)
        = fun ζ : ℍ =>
          -((Work.Residues.AfunPlus d ζ τ + Work.Residues.AfunMinus ℓ d ζ τ) / 2) := rfl
    rw [h3]
    exact ((h1.add h2).div mdifferentiableAt_const (by norm_num)).neg
  have hmain := Work.Residues.hasResidue_of_cleared
    (f := fun ζ : ℍ => Work.Kernels.Kfun ℓ d τ ζ)
    (A := fun ζ : ℍ => - Work.Asymptotics.AfunFun ℓ d τ ζ)
    (z := τ) (z₀ := τ) (c := Work.Residues.jprime τ) hA rfl
    (Work.Residues.tendsto_slope_jprime τ) hne ?_
  · have hval : (- Work.Asymptotics.AfunFun ℓ d τ τ) / Work.Residues.jprime τ = 0 := by
      rw [hA0]; simp
    rwa [hval] at hmain
  · filter_upwards [self_mem_nhdsWithin,
      (Work.Residues.tendsto_slope_jprime τ).eventually (eventually_ne_nhds hne)]
      with ζ hζ hζne
    have hslope : (Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ)
        / ((ζ : ℂ) - (τ : ℂ)) ≠ 0 := hζne
    have hjnz : Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ ≠ 0 := by
      intro h0; exact hslope (by rw [h0, zero_div])
    have h := Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd τ ζ
      (Ne.symm (sub_ne_zero.mp hjnz))
    show Work.Kernels.Kfun ℓ d τ ζ * (Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ)
      = - Work.Asymptotics.AfunFun ℓ d τ ζ
    rw [show Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ
      = -(Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) by ring, mul_neg, h]

/-! ## The three limits -/

theorem Kfun_second_limits (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hne : Work.Residues.jprime τ ≠ 0) :
    Filter.Tendsto (fun z : ℂ => (z - (((-1:ℝ)+ᵥτ : UpperHalfPlane) : ℂ))
        * Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z))
      (nhdsWithin ((((-1:ℝ)+ᵥτ : UpperHalfPlane) : ℂ)) {(((-1:ℝ)+ᵥτ : UpperHalfPlane) : ℂ)}ᶜ)
      (nhds (1/(2*Real.pi)))
  ∧ Filter.Tendsto (fun z : ℂ => (z - (((1:ℝ)+ᵥτ : UpperHalfPlane) : ℂ))
        * Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z))
      (nhdsWithin ((((1:ℝ)+ᵥτ : UpperHalfPlane) : ℂ)) {((((1:ℝ)+ᵥτ : UpperHalfPlane) : ℂ))}ᶜ)
      (nhds (-(1/(2*Real.pi))))
  ∧ Filter.Tendsto (fun z : ℂ => (z - (τ : ℂ)) * Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z))
      (nhdsWithin ((τ:ℂ)) {(τ:ℂ)}ᶜ) (nhds 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `ζ = τ - 1`: residue `1/(2π)`
    exact tendsto_of_hasResidue_ofComplex (Work.Residues.hasResidue_Kfun_second' ℓ d hd τ hne)
  · -- `ζ = τ + 1`: residue `-1/(2π)`
    exact tendsto_of_hasResidue_ofComplex
      (Work.LayerCont.Right.hasResidue_Kfun_tauAddOne ℓ d hd τ hne)
  · -- `ζ = τ`: residue `0`
    exact tendsto_of_hasResidue_ofComplex (hasResidue_Kfun_self ℓ d hd τ hne)

end Work.CKFinal.LineDecay
