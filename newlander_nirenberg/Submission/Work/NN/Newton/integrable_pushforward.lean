import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.proj02_dOne_comp_inverse
import Submission.Work.NN.Assemble.proj02_integrable_local
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/NN/Newton/DESIGN.md first (Newton iteration on shrinking polydiscs; your lemma is one node of its DAG). Do NOT use Work.NN.Core.dbar_regularity (rests on sorryAx) and do not import Core/contDiffOn_of_beltrami_fixedPoint together with Core/holderNorm_fiberPot_of_vanishing (duplicate declarations).

# integrable_pushforward — guidance

Transport of the workspace-form integrability (`proj02 J (dOne (dbarCn J u)) = 0` for every globally
smooth `u`) along a smooth local diffeomorphism `Φ`, where `dΦ ∘ J = J'(Φ) ∘ dΦ`.

## Steps

1. Fix `ζ ∈ Ω'`, and choose `z ∈ Ω` with `Φ z = ζ`.
   * `dΦ z` is bijective, so `Φ` is a local diffeomorphism near `z` (inverse function theorem).
   * `Ω'` is open, so `Φ y ∈ Ω'` for `y` near `z`, and `hpush` applies there.
2. **Chain rule.** For `y` near `z`, `dbarCn J' u (Φ y) (dΦ y h) = dbarCn J (u ∘ Φ) y h`. Unfold
   `dbarCn_apply`, and use `fderiv (u ∘ Φ) = fderiv u (Φ y) ∘ fderiv Φ y` and `hpush`.
3. **`d` commutes with pull-back.** `dOne` of the pulled-back 1-form at `z` on `(V,W)` equals
   `dOne` of the 1-form at `Φ z` on `(dΦV, dΦW)`. The second-derivative terms `D²Φ[V,W]` cancel by
   symmetry (`second_derivative_symmetric` / `IsSymmSndFDerivAt` for `C²` maps).
4. **`proj02` compatibility.** `proj02 J' Ω' (Φz)(dΦV)(dΦW) = proj02 J (Φ^*Ω') z V W`, using
   `J' (Φ z) (dΦ V) = dΦ (J z V)`.
5. **Apply the hypothesis to a global smooth function equal to `u ∘ Φ` near `z`.** Copy the bump
   argument of `Work.NN.Assemble.proj02_integrable_local`
   (`Work.NN.Core.exists_contDiff_bump_of_isCompact_subset`,
   `Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport`). The value at `z` depends only on the
   germ, via `Filter.EventuallyEq.fderiv_eq` twice.
6. **Surjectivity of `dΦ z`.** Every `(V', W')` at `ζ` is `(dΦV, dΦW)`.

Useful precedent: `Work.NN.Final.proj02_integrable_flat` does the same for a *linear* `Φ`.
-/

namespace Work.NN.Newton

open scoped ContDiff
open Filter

/-- **Pointwise chain rule for `∂̄` (change of variables).**  If `Φ` is differentiable at `z`, `u`
at `Φ z`, and the differential of `Φ` intertwines `J z` with `J' (Φ z)`, then precomposing
`∂̄_{J'} u (Φ z)` with `dΦ z` gives `∂̄_J (u ∘ Φ) z`. -/
lemma dbarCn_comp_fderiv {n : ℕ}
    {J J' : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {u : Work.NN.Core.Cn n → ℂ} {Φ : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    {z : Work.NN.Core.Cn n}
    (hΦ : DifferentiableAt ℝ Φ z) (hu : DifferentiableAt ℝ u (Φ z))
    (hpush : ∀ h, fderiv ℝ Φ z (J z h) = J' (Φ z) (fderiv ℝ Φ z h)) :
    (Work.NN.Core.dbarCn J' u (Φ z)).comp (fderiv ℝ Φ z)
      = Work.NN.Core.dbarCn J (u ∘ Φ) z := by
  ext h
  have hchain : fderiv ℝ (u ∘ Φ) z = (fderiv ℝ u (Φ z)).comp (fderiv ℝ Φ z) :=
    fderiv_comp z hu hΦ
  simp only [ContinuousLinearMap.comp_apply]
  rw [Work.NN.Core.dbarCn_apply, Work.NN.Core.dbarCn_apply, hchain]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hpush h]

/-- **Local naturality of `dOne` under pullback along a `C²` map.**  The same statement as
`Work.NN.Final.dOne_comp_fderiv`, but with only *local* smoothness hypotheses at the point `y`. -/
lemma dOne_comp_fderiv_at {n : ℕ}
    (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ)
    (Φ : Work.NN.Core.Cn n → Work.NN.Core.Cn n) (y V W : Work.NN.Core.Cn n)
    (hf : ContDiffAt ℝ 1 f (Φ y)) (hΦ : ContDiffAt ℝ 2 Φ y) :
    Work.NN.Final.dOne (fun y' => (f (Φ y')).comp (fderiv ℝ Φ y')) y V W
      = Work.NN.Final.dOne f (Φ y) (fderiv ℝ Φ y V) (fderiv ℝ Φ y W) := by
  have hfd : DifferentiableAt ℝ f (Φ y) := hf.differentiableAt (by norm_num)
  have hΦd : DifferentiableAt ℝ Φ y := hΦ.differentiableAt (by norm_num)
  have hAd : DifferentiableAt ℝ (fderiv ℝ Φ) y :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcd : DifferentiableAt ℝ (fun y' => f (Φ y')) y := hfd.comp y hΦd
  have hcomp : fderiv ℝ (fun y' => f (Φ y')) y
      = (fderiv ℝ f (Φ y)).comp (fderiv ℝ Φ y) := by
    rw [show (fun y' => f (Φ y')) = f ∘ Φ from rfl, fderiv_comp y hfd hΦd]
  have hdiffW : fderiv ℝ (fun y' => fderiv ℝ Φ y' W) y = (fderiv ℝ (fderiv ℝ Φ) y).flip W := by
    rw [fderiv_clm_apply hAd (differentiableAt_const W)]
    simp
  have hX : fderiv ℝ (fun y' => (f (Φ y')) (fderiv ℝ Φ y' W)) y V
      = f (Φ y) (((fderiv ℝ (fderiv ℝ Φ) y) V) W)
        + (fderiv ℝ f (Φ y) (fderiv ℝ Φ y V)) (fderiv ℝ Φ y W) := by
    rw [fderiv_clm_apply hcd (hAd.clm_apply (differentiableAt_const W)), hdiffW, hcomp]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, add_apply]
  have hY : fderiv ℝ (fun y' => (f (Φ y')) (fderiv ℝ Φ y' V)) y W
      = f (Φ y) (((fderiv ℝ (fderiv ℝ Φ) y) W) V)
        + (fderiv ℝ f (Φ y) (fderiv ℝ Φ y W)) (fderiv ℝ Φ y V) := by
    rw [fderiv_clm_apply hcd (hAd.clm_apply (differentiableAt_const V))]
    rw [show fderiv ℝ (fun y' => fderiv ℝ Φ y' V) y = (fderiv ℝ (fderiv ℝ Φ) y).flip V from by
      rw [fderiv_clm_apply hAd (differentiableAt_const V)]; simp]
    rw [hcomp]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, add_apply]
  have hZ1 : fderiv ℝ (fun z' => f z' (fderiv ℝ Φ y W)) (Φ y) (fderiv ℝ Φ y V)
      = (fderiv ℝ f (Φ y) (fderiv ℝ Φ y V)) (fderiv ℝ Φ y W) := by
    rw [fderiv_clm_apply hfd (differentiableAt_const (fderiv ℝ Φ y W))]
    simp [ContinuousLinearMap.flip_apply]
  have hZ2 : fderiv ℝ (fun z' => f z' (fderiv ℝ Φ y V)) (Φ y) (fderiv ℝ Φ y W)
      = (fderiv ℝ f (Φ y) (fderiv ℝ Φ y W)) (fderiv ℝ Φ y V) := by
    rw [fderiv_clm_apply hfd (differentiableAt_const (fderiv ℝ Φ y V))]
    simp [ContinuousLinearMap.flip_apply]
  have hsym : ((fderiv ℝ (fderiv ℝ Φ) y) V) W = ((fderiv ℝ (fderiv ℝ Φ) y) W) V :=
    (hΦ.isSymmSndFDerivAt (by simp)).eq V W
  rw [Work.NN.Final.dOne, Work.NN.Final.dOne]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hX, hY, hZ1, hZ2, hsym]
  ring

/-- **`dOne` depends only on the germ.** -/
lemma dOne_congr_of_eventuallyEq {n : ℕ}
    {α β : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ} {z : Work.NN.Core.Cn n}
    (h : α =ᶠ[nhds z] β) : Work.NN.Final.dOne α z = Work.NN.Final.dOne β z := by
  funext V W
  simp only [Work.NN.Final.dOne]
  have hW : (fun y => α y W) =ᶠ[nhds z] (fun y => β y W) :=
    h.mono (fun y hy => congrArg (fun L : Work.NN.Core.Cn n →L[ℝ] ℂ => L W) hy)
  have hV : (fun y => α y V) =ᶠ[nhds z] (fun y => β y V) :=
    h.mono (fun y hy => congrArg (fun L : Work.NN.Core.Cn n →L[ℝ] ℂ => L V) hy)
  rw [hW.fderiv_eq, hV.fderiv_eq]

/-- **Compatibility of `proj02` with a pointwise intertwining of `J` and `J'`.**  If
`dOne β (Φ z) (dΦ A) (dΦ B) = dOne α z A B` for all `A,B` and `dΦ ∘ J z = J' (Φ z) ∘ dΦ`, then
the `(0,2)`-projection of `dOne β` at `Φ z` on the pushed-forward vectors equals the projection
of `dOne α` at `z`. -/
lemma proj02_dOne_of_fac {n : ℕ}
    {J J' : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {Φ : Work.NN.Core.Cn n → Work.NN.Core.Cn n} {z : Work.NN.Core.Cn n}
    (hpush : ∀ A, fderiv ℝ Φ z (J z A) = J' (Φ z) (fderiv ℝ Φ z A))
    {β α : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ}
    (hfac : ∀ A B, Work.NN.Final.dOne β (Φ z) (fderiv ℝ Φ z A) (fderiv ℝ Φ z B)
      = Work.NN.Final.dOne α z A B)
    (V W : Work.NN.Core.Cn n) :
    Work.NN.Final.proj02 J' (fun ζ' => Work.NN.Final.dOne β ζ') (Φ z)
        (fderiv ℝ Φ z V) (fderiv ℝ Φ z W)
      = Work.NN.Final.proj02 J (fun y' => Work.NN.Final.dOne α y') z V W := by
  simp only [Work.NN.Final.proj02]
  rw [← hpush V, ← hpush W, hfac V W, hfac (J z V) W, hfac V (J z W), hfac (J z V) (J z W)]

/-- **Integrability is invariant under smooth local diffeomorphisms.**

If `J` is smooth and integrable on the open set `Ω` (in the workspace's form: the
`J`-`(0,2)`-part of `d ∂̄_J u` vanishes on `Ω` for every smooth `u`), `Φ` is smooth on `Ω` with
invertible differential, and `J'` is smooth on the open set `Ω' ⊆ Φ '' Ω` and is the push-forward of
`J` (`dΦ ∘ J = J'(Φ) ∘ dΦ` on `Ω`), then `J'` is integrable on `Ω'`.

Proof idea: at `ζ = Φ z`, `(∂̄_{J'} u)(Φ) ∘ dΦ = ∂̄_J (u ∘ Φ)` near `z`; `d` commutes with pull-back;
`proj02` is compatible with the intertwining; apply the hypothesis to a global smooth function
equal to `u ∘ Φ` near `z` (bump-function localisation, as in
`Work.NN.Assemble.proj02_integrable_local`). -/
theorem integrable_pushforward {n : ℕ} {Ω Ω' : Set (Work.NN.Core.Cn n)} (hΩ : IsOpen Ω)
    (hΩ' : IsOpen Ω') {J J' : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {Φ : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    (hJ : ∀ m : ℕ, ContDiffOn ℝ m J Ω) (hJ' : ∀ m : ℕ, ContDiffOn ℝ m J' Ω')
    (hΦ : ∀ m : ℕ, ContDiffOn ℝ m Φ Ω)
    (hbij : ∀ z, z ∈ Ω → Function.Bijective (fderiv ℝ Φ z))
    (himg : Ω' ⊆ Φ '' Ω)
    (hpush : ∀ z, z ∈ Ω → Φ z ∈ Ω' → ∀ h : Work.NN.Core.Cn n,
      fderiv ℝ Φ z (J z h) = J' (Φ z) (fderiv ℝ Φ z h))
    (hint : ∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
      ∀ z, z ∈ Ω → ∀ V W : Work.NN.Core.Cn n,
        Work.NN.Final.proj02 J
          (fun z' => Work.NN.Final.dOne (fun z'' => Work.NN.Core.dbarCn J u z'') z') z V W = 0) :
    ∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
      ∀ ζ, ζ ∈ Ω' → ∀ V W : Work.NN.Core.Cn n,
        Work.NN.Final.proj02 J'
          (fun z' => Work.NN.Final.dOne (fun z'' => Work.NN.Core.dbarCn J' u z'') z')
          ζ V W = 0 := by
  intro u hu ζ hζ V' W'
  -- choose `z ∈ Ω` with `Φ z = ζ`
  obtain ⟨z, hzΩ, hzΦ⟩ := himg hζ
  subst hzΦ
  -- replace the target vectors by pushed-forward ones
  obtain ⟨V, hV⟩ := (hbij z hzΩ).2 V'
  obtain ⟨W, hW⟩ := (hbij z hzΩ).2 W'
  rw [← hV, ← hW]
  -- local smoothness facts
  have hΦ2 : ContDiffAt ℝ 2 Φ z := (hΦ 2).contDiffAt (hΩ.mem_nhds hzΩ)
  have hJ'1 : ContDiffAt ℝ 1 J' (Φ z) := (hJ' 1).contDiffAt (hΩ'.mem_nhds hζ)
  have hβ : ContDiffAt ℝ 1 (fun ζ' => Work.NN.Core.dbarCn J' u ζ') (Φ z) := by
    have hfdu : ContDiffAt ℝ 1 (fderiv ℝ u) (Φ z) :=
      ((hu 2).fderiv_right (m := 1) (by norm_num)).contDiffAt
    have hcomp : ContDiffAt ℝ 1 (fun ζ' => (fderiv ℝ u ζ').comp (J' ζ')) (Φ z) :=
      hfdu.clm_comp hJ'1
    simpa only [Work.NN.Core.dbarCn] using
      (hfdu.add (hcomp.const_smul Complex.I)).const_smul ((1 / 2 : ℝ) : ℝ)
  -- the change-of-variables identity holds near `z`
  have hgm : (fun y' => (Work.NN.Core.dbarCn J' u (Φ y')).comp (fderiv ℝ Φ y'))
      =ᶠ[nhds z] (fun y' => Work.NN.Core.dbarCn J (u ∘ Φ) y') := by
    have hΩ_nhds : ∀ᶠ y' in nhds z, y' ∈ Ω := hΩ.mem_nhds hzΩ
    have hcont : ContinuousAt Φ z := hΦ2.continuousAt
    have hΩ'_nhds : ∀ᶠ y' in nhds z, Φ y' ∈ Ω' := hcont.preimage_mem_nhds (hΩ'.mem_nhds hζ)
    filter_upwards [hΩ_nhds, hΩ'_nhds] with y' hyΩ hyΩ'
    exact dbarCn_comp_fderiv
      (((hΦ 1).contDiffAt (hΩ.mem_nhds hyΩ)).differentiableAt (by norm_num))
      (((hu 1).contDiffAt).differentiableAt (by norm_num))
      (hpush y' hyΩ hyΩ')
  -- the factorisation identity for `dOne`
  have hfac : ∀ A B, Work.NN.Final.dOne (fun ζ' => Work.NN.Core.dbarCn J' u ζ') (Φ z)
        (fderiv ℝ Φ z A) (fderiv ℝ Φ z B)
      = Work.NN.Final.dOne (fun y' => Work.NN.Core.dbarCn J (u ∘ Φ) y') z A B := by
    intro A B
    rw [← dOne_comp_fderiv_at (fun ζ' => Work.NN.Core.dbarCn J' u ζ') Φ z A B hβ hΦ2]
    exact congrFun (congrFun (dOne_congr_of_eventuallyEq hgm) A) B
  have key := proj02_dOne_of_fac (z := z) (fun A => hpush z hzΩ hζ A) hfac V W
  rw [key]
  -- replace `u ∘ Φ` by a globally smooth function
  obtain ⟨χ, V₀, hχsm, _hχcpt, hχts, hV₀open, hzV₀, hχone⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset (K := {z}) (U := Ω)
      isCompact_singleton hΩ (by simpa using hzΩ)
  set f : Work.NN.Core.Cn n → ℂ := fun y => χ y * (u ∘ Φ) y with hf
  have hfsm : ∀ m : ℕ, ContDiff ℝ m f := fun m => by
    rw [hf]
    exact Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport hΩ hχsm hχts
      ((hu m).comp_contDiffOn (hΦ m))
  have hev : f =ᶠ[nhds z] (u ∘ Φ) := by
    filter_upwards [hV₀open.mem_nhds (hzV₀ (Set.mem_singleton z))] with y hy
    rw [hf]
    simp [hχone y hy]
  rw [← Work.NN.Assemble.proj02_dbarCn_congr (J := J) hev V W]
  exact hint f hfsm z hzΩ V W

end Work.NN.Newton
