/-
# The `z₀`-generic cleanliness lemmas for the left detour

`Submission/Work/Asymptotics/detourLeftC_eq_interval_of_clean.lean` proves the three "cleanliness"
lemmas that drive the residue-free contour mechanics of the left detour with the *specific*
excluded point `z₀ = poleℂ τ = τ - 1` (`Work.Asymptotics.dlcc_clean`, `dlcc_continuousOn`,
`dlcc_differentiableAt`).  Their proofs only ever use the hypothesis

  `hclean : ∀ z, z ∈ leftRectℂ c A ξ → z ≠ z₀ → j τ ≠ j (ofComplex z)`

pointwise, and the `z ≠ poleℂ τ` side condition of the excluded point.  This file restates them
for an **arbitrary** excluded point `z₀ : ℂ`, which is exactly what the *removable coincidence*
`z₀ = coincℂ τ` needs (§5.3 on the far side of `Re τ = 1`, where the rectangle contains the
coincidence instead of the pole).

The two genuinely different statements are `dlcc_continuousOn_generic` (the closed rectangle minus
`z₀`) and `dlcc_differentiableAt_generic` (the open rectangle minus `z₀`); `dlcc_clean_generic` is
the identity, recorded for uniformity, and `dlcc_clean_coinc` is the useful *derivation* of
`hclean` from the orbit-exclusion hypothesis

  `∀ γ z, leftRect c A ξ z → (z ≠ γ • τ ∨ z = S • (-1 +ᵥ τ))`

in which the only `SL(2,ℤ)`-translate of `τ` in the rectangle is the coincidence.
-/
import Mathlib
import Submission.Work.LayerCont.Coinc.Defs
import Submission.Work.Asymptotics.detourLeftC_eq_interval_of_clean

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.LayerCont.Coinc

open Work.Asymptotics

/-- **The `z₀`-generic cleanliness hypothesis** (identity, recorded so that the three lemmas below
have a common interface). -/
theorem dlcc_clean_generic (τ : UpperHalfPlane) (c A ξ : ℝ) (z₀ : ℂ)
    (hclean : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ z₀ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)) :
    ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ z₀ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) :=
  hclean

/-- **`dlcc_clean` with the removable coincidence as the excluded point.**

If the only point of the `SL(2,ℤ)`-orbit of `τ` in the closed rectangle `[-ξ,0] × [c-A,c+A]` is the
coincidence `S • (-1 +ᵥ τ)`, then every point `z` of the rectangle other than `coincℂ τ` has
`j (ofComplex z) ≠ j τ`. -/
theorem dlcc_clean_coinc (τ : UpperHalfPlane) (c A ξ : ℝ) (hcA : 0 < c - A)
    (hcl : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect c A ξ z → (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ))) :
    ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ coincℂ τ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) := by
  intro z hz hzp hjeq
  have hzim : 0 < z.im := leftRectℂ_subset_im_pos hcA hz
  have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzim, UpperHalfPlane.coe_mk]
  have hre : (UpperHalfPlane.ofComplex z).re = z.re := by
    rw [← UpperHalfPlane.coe_re, hcoe]
  have him : (UpperHalfPlane.ofComplex z).im = z.im := by
    rw [← UpperHalfPlane.coe_im, hcoe]
  have hleft : leftRect c A ξ (UpperHalfPlane.ofComplex z) := by
    simp only [leftRect, leftRectℂ, Set.mem_ofPred_eq] at hz ⊢
    rw [hre, him]
    exact hz
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq
    (τ := UpperHalfPlane.ofComplex z) (w := τ) hjeq.symm
  rcases hcl γ (UpperHalfPlane.ofComplex z) hleft with h' | h'
  · exact h' hγ.symm
  · exact hzp (by rw [hcoe.symm, h']; rfl)

/-- **`kerForm` is continuous on the closed rectangle minus an arbitrary point `z₀`**, given the
`z₀`-generic cleanliness hypothesis. -/
theorem dlcc_continuousOn_generic (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) (c A ξ : ℝ) (z₀ : ℂ) (hcA : 0 < c - A)
    (hclean : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ z₀ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)) :
    ContinuousOn (kerForm ℓ d r τ) (leftRectℂ c A ξ \ {z₀}) := by
  have hsub : (leftRectℂ c A ξ \ {z₀}) ⊆ {z : ℂ | 0 < z.im} :=
    fun z hz => leftRectℂ_subset_im_pos hcA hz.1
  have hof : ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z)
      (leftRectℂ c A ξ \ {z₀}) :=
    continuousOn_ofComplex_of_im_pos.mono hsub
  have hgc : ContinuousOn (fun z : ℂ => (τ, UpperHalfPlane.ofComplex z))
      (leftRectℂ c A ξ \ {z₀}) :=
    ContinuousOn.prodMk (f := fun _ : ℂ => τ) (g := fun z : ℂ => UpperHalfPlane.ofComplex z)
      continuousOn_const hof
  have hK := (continuousOn_Kfun_clean ℓ d hd).comp hgc (fun z hz => by
    have h := hclean z hz.1 (by simpa using hz.2)
    simpa using h)
  have hexp : ContinuousOn (fun z : ℂ => kerExp r z) (leftRectℂ c A ξ \ {z₀}) := by
    have hcont : Continuous fun z : ℂ => kerExp r z := by
      unfold kerExp; fun_prop
    exact hcont.continuousOn
  have hmain := (hK.mul hexp).div_const Complex.I
  refine hmain.congr (fun z hz => ?_)
  simp [kerForm, Function.comp]

/-- **`kerForm` is holomorphic on the open rectangle off an arbitrary point `z₀`**, given the
`z₀`-generic cleanliness hypothesis. -/
theorem dlcc_differentiableAt_generic (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) (τ : UpperHalfPlane) (c A ξ : ℝ) (z₀ : ℂ) (hcA : 0 < c - A)
    (hclean : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ z₀ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)) :
    ∀ z : ℂ, z ∈ openLeftRectℂ c A ξ → z ≠ z₀ →
      DifferentiableAt ℂ (kerForm ℓ d r τ) z := by
  intro z hz hzp
  have hleft : z ∈ leftRectℂ c A ξ := openLeftRectℂ_subset_leftRectℂ c A ξ hz
  have hzim : 0 < z.im := leftRectℂ_subset_im_pos hcA hleft
  have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzim
  have hne : Work.Kernels.jInvariantFun τ
      ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) := hclean z hleft hzp
  have hA : DifferentiableAt ℂ
      (fun w : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)) z := by
    have hhol : DifferentiableOn ℂ
        (fun w : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)) {w : ℂ | 0 < w.im} := by
      have h := (UpperHalfPlane.mdifferentiable_iff
        (f := fun w : UpperHalfPlane => AfunFun ℓ d τ w)).mp
        (mdifferentiable_AfunFun_snd ℓ d hd τ)
      simpa [Function.comp_def] using h
    exact hhol.differentiableAt hU
  have hJ : DifferentiableAt ℂ
      (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) z := by
    have hhol : DifferentiableOn ℂ
        (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w))
        {w : ℂ | 0 < w.im} := by
      have h := (UpperHalfPlane.mdifferentiable_iff
        (f := Work.Kernels.jInvariantFun)).mp mdifferentiable_jInvariantFun
      simpa [Function.comp_def] using h
    exact hhol.differentiableAt hU
  have hexp : DifferentiableAt ℂ (fun w : ℂ => kerExp r w) z := by
    simp only [kerExp]
    fun_prop
  have hΦ : DifferentiableAt ℂ (fun w : ℂ =>
      AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)
        / (Work.Kernels.jInvariantFun τ
            - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w))
        * kerExp r w / Complex.I) z :=
    (((hA.div ((differentiableAt_const (c := Work.Kernels.jInvariantFun τ)).sub hJ)
      (sub_ne_zero.mpr hne)).mul hexp)).div_const Complex.I
  refine (Filter.EventuallyEq.differentiableAt_iff ?_).mpr hΦ
  have hmem : openLeftRectℂ c A ξ \ {z₀} ∈ 𝓝 z :=
    ((isOpen_openLeftRectℂ' c A ξ).inter isOpen_compl_singleton).mem_nhds ⟨hz, hzp⟩
  filter_upwards [hmem] with w hw
  have hwl : w ∈ leftRectℂ c A ξ := openLeftRectℂ_subset_leftRectℂ c A ξ hw.1
  have hwne : Work.Kernels.jInvariantFun τ
      ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w) := hclean w hwl hw.2
  simp only [kerForm]
  rw [show Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex w)
      = AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)
        / (Work.Kernels.jInvariantFun τ
            - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) by
    rw [eq_div_iff (sub_ne_zero.mpr hwne)]
    exact Kfun_mul_slope_eq_AfunFun ℓ d hd τ (UpperHalfPlane.ofComplex w) hwne]

end Work.LayerCont.Coinc
