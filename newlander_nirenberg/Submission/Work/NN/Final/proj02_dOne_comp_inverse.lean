import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder

/-!
# `proj02_dOne_comp_inverse`

Naturality of the form-level `(0,2)`-projection of the exterior derivative under the *inverse* of
a `(Jstd + A) → Jstd` holomorphic diffeomorphism.

Let `w : ℂⁿ → ℂⁿ` be a `C²` diffeomorphism with inverse `Ψ`, intertwining the perturbed complex
structure `Jstd + A` with the standard one in the sense

  `dw_z((Jstd + A)_z V) = i · dw_z V`   for all `z, V`,

and let `f` be a `C¹` `(0,1)`-form.  Then the `(0,2)`-projection of the exterior derivative of the
pullback `Ψ^* f` at `y` (for the standard structure, on `(V,W)`) equals the `(0,2)`-projection of
the exterior derivative of `f` at `Ψ y` (for the perturbed structure, on `(dΨ_y V, dΨ_y W)`) — the
statement used to transport the flat `∂̄`-Poincaré lemma across the chart.

The proof combines

* the naturality of the exterior derivative under pullback along a `C²` map
  (`dOne_comp_fderiv`), whose proof is the symmetry of the second derivative, and
* the identity `dΨ_y(iV) = (Jstd + A)(Ψ y)(dΨ_y V)` obtained from the intertwining relation by
  applying `dΨ_y` and using `w ∘ Ψ = id`, `Ψ ∘ w = id` (`fderiv_inv_Jstd`).
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

/-- **Naturality of `dOne` under pullback along a `C²` map.**  For a `C¹` `(0,1)`-form `f` and a
`C²` map `Φ`, the exterior derivative of the pulled-back form `y ↦ (f (Φ y)) ∘ dΦ_y` is the
exterior derivative of `f` at `Φ y` on the pushed-forward vectors.  (The proof is the symmetry of
the second derivative of `Φ`.) -/
lemma dOne_comp_fderiv {n : ℕ} (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ)
    (Φ : Work.NN.Core.Cn n → Work.NN.Core.Cn n)
    (hf : ContDiff ℝ 1 f) (hΦ : ContDiff ℝ 2 Φ) (y V W : Work.NN.Core.Cn n) :
    dOne (fun y' => (f (Φ y')).comp (fderiv ℝ Φ y')) y V W
      = dOne f (Φ y) (fderiv ℝ Φ y V) (fderiv ℝ Φ y W) := by
  have hfd : DifferentiableAt ℝ f (Φ y) := (hf.differentiable (by norm_num)).differentiableAt
  have hΦd : DifferentiableAt ℝ Φ y := (hΦ.differentiable (by norm_num)).differentiableAt
  have hAd : DifferentiableAt ℝ (fderiv ℝ Φ) y :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  have hcd : DifferentiableAt ℝ (fun y' => f (Φ y')) y := hfd.comp y hΦd
  have hcomp : fderiv ℝ (fun y' => f (Φ y')) y = (fderiv ℝ f (Φ y)).comp (fderiv ℝ Φ y) := by
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
    (hΦ.contDiffAt.isSymmSndFDerivAt (by simp)).eq V W
  rw [dOne, dOne]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hX, hY, hZ1, hZ2, hsym]
  ring

/-- **The structure identity along the inverse.**  If `w` is a `C²` diffeomorphism with inverse `Ψ`
which intertwines `Jstd + A` with `Jstd` (`dw_z((Jstd+A)_z V) = i · dw_z V`), then

  `dΨ_y (Jstd_y V) = (Jstd + A)(Ψ y) (dΨ_y V)`.

It is obtained by applying `dΨ_y` to the intertwining relation at `z = Ψ y` on the vector
`dΨ_y V` and using the two chain rules `dΨ_y ∘ dw_{Ψ y} = 1`, `dw_{Ψ y} ∘ dΨ_y = 1`. -/
lemma fderiv_inv_Jstd {n : ℕ}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {w Ψ : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    (hw : ContDiff ℝ 2 w) (hΨ : ContDiff ℝ 2 Ψ)
    (hinv₁ : ∀ z, w (Ψ z) = z) (hinv₂ : ∀ y, Ψ (w y) = y)
    (hint : ∀ z V, fderiv ℝ w z (((Work.NN.Core.JstdCn n + A) z) V)
      = Complex.I • (fderiv ℝ w z V))
    (y U : Work.NN.Core.Cn n) :
    fderiv ℝ Ψ y (Work.NN.Core.JstdCn n y U)
      = ((Work.NN.Core.JstdCn n + A) (Ψ y)) (fderiv ℝ Ψ y U) := by
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hcomp1 : (fderiv ℝ Ψ y).comp (fderiv ℝ w (Ψ y)) = 1 := by
    have h := fderiv_comp (𝕜 := ℝ) (x := Ψ y) (f := w) (g := Ψ) (hΨd (w (Ψ y))) (hwd (Ψ y))
    rw [show (Ψ ∘ w) = id from funext hinv₂, fderiv_id, hinv₁ y] at h
    exact h.symm
  have hcomp2 : (fderiv ℝ w (Ψ y)).comp (fderiv ℝ Ψ y) = 1 := by
    have h := fderiv_comp (𝕜 := ℝ) (x := y) (f := Ψ) (g := w) (hwd (Ψ y)) (hΨd y)
    rw [show (w ∘ Ψ) = id from funext hinv₁, fderiv_id] at h
    exact h.symm
  have happ2 : ∀ X, fderiv ℝ w (Ψ y) (fderiv ℝ Ψ y X) = X := by
    intro X
    have := congrArg (fun (T : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) => T X) hcomp2
    simpa [ContinuousLinearMap.comp_apply] using this
  have hkey := hint (Ψ y) (fderiv ℝ Ψ y U)
  rw [happ2 U] at hkey
  have h2 := congrArg (fun X => fderiv ℝ Ψ y X) hkey
  rw [show fderiv ℝ Ψ y
        (fderiv ℝ w (Ψ y) (((Work.NN.Core.JstdCn n + A) (Ψ y)) (fderiv ℝ Ψ y U)))
      = ((Work.NN.Core.JstdCn n + A) (Ψ y)) (fderiv ℝ Ψ y U) from by
    have := congrArg (fun (T : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) =>
      T (((Work.NN.Core.JstdCn n + A) (Ψ y)) (fderiv ℝ Ψ y U))) hcomp1
    simpa [ContinuousLinearMap.comp_apply] using this] at h2
  rw [h2]
  simp [Work.NN.Core.JstdCn_apply]

theorem proj02_dOne_comp_inverse {n : ℕ}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {w Ψ : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    (hw : ContDiff ℝ 2 w) (hΨ : ContDiff ℝ 2 Ψ)
    (hinv₁ : ∀ z, w (Ψ z) = z) (hinv₂ : ∀ y, Ψ (w y) = y)
    (hint : ∀ z V, fderiv ℝ w z (((Work.NN.Core.JstdCn n + A) z) V)
      = Complex.I • (fderiv ℝ w z V))
    {f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ} (hf : ContDiff ℝ 1 f)
    (y : Work.NN.Core.Cn n) (V W : Work.NN.Core.Cn n) :
    Work.NN.Final.proj02 (Work.NN.Core.JstdCn n)
        (fun y' => Work.NN.Final.dOne
          (fun y'' => (f (Ψ y'')).comp (fderiv ℝ Ψ y'')) y') y V W
      = Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
          (fun z' => Work.NN.Final.dOne f z') (Ψ y)
          (fderiv ℝ Ψ y V) (fderiv ℝ Ψ y W) := by
  have hpull := dOne_comp_fderiv (n := n) f Ψ hf hΨ
  have hI := fun U => fderiv_inv_Jstd hw hΨ hinv₁ hinv₂ hint y U
  simp only [proj02]
  simp only [hpull]
  rw [hI V, hI W]

end Work.NN.Final
