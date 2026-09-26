import Mathlib
import Submission.Work.HFN.BlLowTS.Main
import Submission.Work.HFN.BlLowTS.F2Paper
import Submission.Work.HFN.BlLow.window_bound
import Submission.Work.HFN.BlLow.offwindow_bound
import Submission.Work.Asymptotics.TSasm.BlLowSeminormTS3
import Submission.Work.Asymptotics.F2LayerDefs

namespace Work.Asymptotics

open UpperHalfPlane

/-- On the low bad-line region `blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}` the paper's
layer `layer (Gcusp ℓ d) ℓ d τ ·` is *pointwise* the pole-split layer `blLowF2 ℓ d τ ·` of the
`BlLowTS` assembly: at `r = 0` both vanish by definition, and for `r ≠ 0` the two puncture
branches reduce to `paperLayer (Gcusp ℓ d) ℓ d τ r = lowF2 ℓ d τ r`, which is
`Work.Asymptotics.BlLowTS.lowF2_eq_paperLayer`.

This is the identity that lets the seminorm bound proved for the translate-pole-split layer
(`Work.Asymptotics.BlLowTS.blLowF2_seminorm`) be read off for the paper's layer itself. -/
theorem layer_eq_blLowF2 {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24)
    {Cdec : ℝ} (hCdec : 0 ≤ Cdec)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ Cdec)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      Work.Asymptotics.HalfFunnel.lowRho ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cdec)
    {τ : ℍ} (hτ : Work.Asymptotics.BlLow.blLowSet τ) :
    (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
      = fun s : ℝ => Work.HFN.BlLowTS.blLowF2 ℓ d τ s := by
  funext s
  rw [Work.Asymptotics.layer, Work.HFN.BlLowTS.blLowF2]
  by_cases hs : s = 0
  · simp [hs]
  · rw [if_neg hs, if_neg hs]
    exact (Work.HFN.BlLowTS.lowF2_eq_paperLayer ℓ d hd Cdec hCdec hdec1 hdec2
      τ s hτ).symm

/-- **The `r`-seminorm bound of the CKMRV layer on the low bad-line region.**

For `τ` in `blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}` the weighted seminorms
`|r|^k ∂_r^l` of the layer `r ↦ layer (Gcusp ℓ d) ℓ d τ r` are bounded uniformly in `τ`, for
every order `(k,l)`.

The layer is the paper's `F₂` without the spike, i.e. the `low + trunc + high` decomposition of
the contour integral `4 sin²(πr²/2) ∫_0^∞ K^{(d)}(τ,it) e^{-πr²t} dt`; on `blLowSet` it agrees
pointwise with the translate-pole-split layer `blLowF2` (`layer_eq_blLowF2`), whose seminorms are
controlled by `BlLowTS.blLowF2_seminorm` from the window/off-window bounds on the kernel. -/
theorem LayerSemiBlLowTS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), Work.Asymptotics.BlLow.blLowSet τ →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖ ≤ C := by
  intro k l
  obtain ⟨Cw, hCw, hwin⟩ := Work.HFN.BlLow.window_bound ℓ d hd
  obtain ⟨Co, hCo, hoff⟩ := Work.HFN.BlLow.offwindow_bound ℓ d hd
  obtain ⟨Cdec0, hCdec0, hdec1_0⟩ :=
    Work.HFN.BlLowTS.blLow_kernel_spike ℓ d hd hCw hCo hwin hoff
  set Cdec : ℝ := max Cdec0 Co with hCdecdef
  have hCdec : 0 ≤ Cdec := le_trans hCdec0 (le_max_left _ _)
  have hdec1 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ Cdec :=
    fun τ hτ t ht htT => le_trans (hdec1_0 τ t hτ ht htT) (le_max_left _ _)
  have hdec2 : ∀ (τ : ℍ), Work.Asymptotics.BlLow.blLowSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      Work.Asymptotics.HalfFunnel.lowRho ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cdec :=
    fun τ hτ t ht htT hsep => le_trans (hoff τ t hτ ht htT hsep) (le_max_right _ _)
  obtain ⟨C, hC, hb⟩ :=
    Work.HFN.BlLowTS.blLowF2_seminorm ℓ d hd hCdec hdec1 hdec2 k l
  refine ⟨C, hC, fun τ r hτ => ?_⟩
  rw [layer_eq_blLowF2 hd hCdec hdec1 hdec2 hτ]
  exact hb τ r hτ

end Work.Asymptotics
