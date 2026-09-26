import Mathlib
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Mono.Band.noTangency_data
import Submission.Work.Drive.Mono.Band.bandData_core_exists

/-!
# The analytic core of the thin-slab band data

This file proves `Work.Drive.Mono.Band.thinSlabBand_core` — the existence, at every configuration
of Pardon's box-shrink bookkeeping, of a *thin* slab carrying the tilt genericity
`Work.Drive.Final.TiltedGenericity` — from the single analytic input
`Work.Drive.Mono.Band.bandData_core_exists`, which exposes the four data conditions the genericity
is assembled from (see the long docstring there).

## The structure of the argument in this file

`TiltedGenericity ψ s c σ u v h (innerSL ℝ n) exc` consists of four clauses about the sweep height
`F := sweepHeight ψ (innerSL ℝ n)`, the slab functional `G := fun q => ⟪v, par ψ q⟫` and the wall
functional `ℓ := innerSL ℝ n`:

* (i) away from `exc`, `F` has no critical point in the box-region inside the closed slab;
* (ii) on the two slab faces, away from `exc`, the differential of `F` is not parallel to that of
  `G`;
* (iii) at every critical point of `F` in the box-region inside the closed slab, the Hessian is
  nondegenerate and the value lies in `exc`;
* (iv) two such critical points with the same value have the same image on the surface.

Three of them are immediate from the *data*: (i) and (iii) from "the critical values in the box lie
in `exc`" together with the Morse property, (iv) from the distinctness of critical values.  For (ii)
the decisive observation is the *dictionary*

  `fderiv F p = t • fderiv G p  ⟹  ⟪v × n, normal (par ψ) p⟫ = 0`

(`crossE_normal_eq_zero_of_fderiv_eq_smul`, proved below by linear algebra alone: the parallelism
says `n - t v ⊥ span(d₁, d₂)`, so `n - t v ‖ normal (par ψ) p`, and `v × n ⊥ v, n`).  Hence at a
face point whose level is *not* in `exc` it suffices that `⟪v × n, normal (par ψ) p⟫ ≠ 0`, which is
exactly the "bad face points have their levels in `exc`" condition (d).

The only non-elementary step is therefore the *existence* of `(v, n, h, exc)` together with the four
data conditions and the size / cutting conditions on `h`; that is
`Work.Drive.Mono.Band.bandData_core_exists`, and its (long) docstring contains the analysis of why
the wall normal `n` must be chosen jointly with the half-width `h` and of the residuals of the
statement.
-/

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace

noncomputable section

/-! ## The dictionary: parallelism on a face forces tangency of the wall normal -/

/-- The derivative in the parameter plane, at `p`, of the height `q ↦ ⟪a, par ψ q⟫` in the
direction `w` is `⟪a, d(par ψ)_p w⟫` (the chain rule for the composition of the parametrisation with
the linear functional `⟪a, ·⟫`). -/
private lemma fderiv_par_height_apply (ψ : Submission.Diffeo) (a : R3) (p w : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ a (Work.BoxShrink.Pinch.par ψ q)) p w
      = inner ℝ a (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w) := by
  have hd : DifferentiableAt ℝ (Work.BoxShrink.Pinch.par ψ) p :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)).differentiableAt
  have h := fderiv_inner_apply (𝕜 := ℝ) (x := p) (G := ℝ × ℝ) (E := R3)
    (f := fun _ : ℝ × ℝ => a) (g := Work.BoxShrink.Pinch.par ψ)
    (differentiableAt_const a) hd w
  rw [h]
  simp

/-- **The dictionary, in the form used below.**  If the differential at `p` of the swept height
`sweepHeight ψ (⟪n, ·⟫)` is a scalar multiple of the differential of the direction-`v` height, then
the Gauss image at `p` is tangent to the plane spanned by `v` and `n`:

  `fderiv (sweepHeight ψ (⟪n,·⟫)) p = t • fderiv (⟪v, par ψ ·⟫) p ⟹ ⟪v × n, N p⟫ = 0`.

Indeed `fderiv (⟪n,·⟫ ∘ par ψ) p = t • fderiv (⟪v,·⟫ ∘ par ψ) p` says exactly
`⟪n - t v, d(par ψ)_p w⟫ = 0` for every `w`, i.e. `n - t v ⊥ span(d1, d2)`; as
`N p = d1 × d2 ≠ 0` spans the orthogonal complement of `span(d1, d2)` (the parametrisation is an
immersion), `n - t v` is a multiple of `N p`, and then `⟪v × n, N p⟫ = 0` because `v × n` is
orthogonal to both `v` and `n`.  The hypotheses `‖v‖ = ‖n‖ = 1` and `⟪v,n⟫ = 0` are used only to
exclude the degenerate case `n = t v` (which would force `n = 0`). -/
theorem crossE_normal_eq_zero_of_fderiv_eq_smul
    (ψ : Submission.Diffeo) {v n : R3} {t : ℝ} {p : ℝ × ℝ}
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (h : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p
      = t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) :
    inner ℝ (Work.Drive.Generic.crossE v n)
      (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 := by
  set A : (ℝ × ℝ) →L[ℝ] R3 := fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p with hA
  have hF : ∀ w : ℝ × ℝ,
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p w = inner ℝ n (A w) := by
    intro w
    rw [Work.Drive.EpsForm.sweepHeight_innerSL]
    exact fderiv_par_height_apply ψ n p w
  have hG : ∀ w : ℝ × ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p w
        = inner ℝ v (A w) :=
    fun w => fderiv_par_height_apply ψ v p w
  have hm1 : inner ℝ (n - t • v) (A (1, 0)) = 0 := by
    have h1 : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p (1, 0)
        = t * fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p (1, 0) := by
      rw [h, smul_apply, smul_eq_mul]
    rw [hF (1, 0), hG (1, 0)] at h1
    rw [inner_sub_left, real_inner_smul_left, h1, sub_self]
  have hm2 : inner ℝ (n - t • v) (A (0, 1)) = 0 := by
    have h1 : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p (0, 1)
        = t * fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p (0, 1) := by
      rw [h, smul_apply, smul_eq_mul]
    rw [hF (0, 1), hG (0, 1)] at h1
    rw [inner_sub_left, real_inner_smul_left, h1, sub_self]
  have hm1c : inner ℝ (A (1, 0)) (n - t • v) = 0 := by rw [real_inner_comm]; exact hm1
  have hcross : Work.Drive.Generic.crossE (n - t • v)
      (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 := by
    rw [Work.Drive.Generic.normal, Work.Drive.Generic.d1, Work.Drive.Generic.d2, ← hA]
    rw [Work.Drive.Generic.crossE_crossE]
    rw [hm2, hm1c]
    simp
  have hAc : Function.Injective A := by
    have := Work.Smooth.Morse.Immersion.isImmersion ψ p
    simpa [A, Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param] using this
  have hNne : Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p ≠ 0 := by
    rw [Work.Drive.Generic.normal, Work.Drive.Generic.d1, Work.Drive.Generic.d2, ← hA]
    rw [Work.Drive.Generic.crossE_ne_zero_iff]
    intro c d hcd
    have h0 : A (c, d) = 0 := by
      have hdec : (c, d) = c • ((1 : ℝ), (0 : ℝ)) + d • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
      rw [hdec, map_add, map_smul, map_smul, hcd]
    have hp : (c, d) = 0 := hAc (by rw [h0, map_zero])
    exact ⟨by simpa using congrArg Prod.fst hp, by simpa using congrArg Prod.snd hp⟩
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv1]; norm_num
  have hm_ne : n - t • v ≠ 0 := by
    intro h0
    have hn_eq : n = t • v := sub_eq_zero.mp h0
    have ht : t = 0 := by
      have h1 : inner ℝ v n = t * inner ℝ v v := by rw [hn_eq, real_inner_smul_right]
      rw [hvn, hvv, mul_one] at h1
      exact h1.symm
    have hn0 : n = 0 := by rw [hn_eq, ht, zero_smul]
    rw [hn0] at hn1
    simp at hn1
  obtain ⟨c, hc⟩ := Work.Drive.Generic.exists_smul_of_crossE_eq_zero hcross hNne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hm_ne (by rw [hc]; simp)
  have hNm : Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p = c⁻¹ • (n - t • v) := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hcross2 : inner ℝ (Work.Drive.Generic.crossE v n) (n - t • v) = 0 := by
    rw [inner_sub_right, real_inner_smul_right]
    have e1 : inner ℝ (Work.Drive.Generic.crossE v n) n = 0 := by
      rw [real_inner_comm]; exact Work.Drive.Generic.inner_crossE_right v n
    have e2 : inner ℝ (Work.Drive.Generic.crossE v n) v = 0 := by
      rw [real_inner_comm]; exact Work.Drive.Generic.inner_crossE_left v n
    rw [e1, e2]; ring
  rw [hNm, inner_smul_right, hcross2, mul_zero]

/-! ## Packaging: the four data conditions give the tilt genericity -/

/-- **The structure lemma.**  Four conditions on the pair `(v, n)` and the half-width `h` imply the
tilt genericity `Work.Drive.Final.TiltedGenericity` at the wall functional `ℓ = innerSL ℝ n`:

* `hMorse` — the sweep height is Morse on the box-region;
* `hdistinct` — two critical points of the sweep height in the box-region with the same value have
  the same image on the surface;
* `hcrit` — the value at a critical point of the sweep height in the box-region lies in `exc`;
* `hface` — a point of the box-region lying on a slab face at which the wall normal is *tangent* to
  the surface (`⟪v × n, N⟫ = 0`, the dictionary above) has its height value in `exc`.

Clauses (i), (iii) and (iv) of the genericity are immediate; clause (ii) follows from `hface`
because by `crossE_normal_eq_zero_of_fderiv_eq_smul` a parallelism of the two differentials at `p`
forces `⟪v × n, N(par ψ p)⟫ = 0`. -/
theorem tiltedGenericity_of_data
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v n : R3) (h : ℝ) (exc : Finset ℝ)
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (hMorse : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p = 0 →
      Function.Injective
        (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n))) p))
    (hdistinct : ∀ p p' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p = 0 →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p' = 0 →
      (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p
        = (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p' →
      Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p')
    (hcrit : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p = 0 →
      (innerSL ℝ) n (Work.BoxShrink.Pinch.par ψ p) ∈ exc)
    (hface : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
      inner ℝ (Work.Drive.Generic.crossE v n)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 →
      (innerSL ℝ) n (Work.BoxShrink.Pinch.par ψ p) ∈ exc) :
    Work.Drive.Final.TiltedGenericity ψ s c σ u v h ((innerSL ℝ) n) exc := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (i) no critical point of the sweep height in the box-region inside the slab, away from `exc`
    intro lam hlam p hpBox _hpSlab hval hcritp
    exact hlam (by rw [← hval]; exact hcrit p hpBox hcritp)
  · -- (ii) on the slab faces the height is not parallel to the face functional, away from `exc`
    intro lam hlam p hpBox hfacept hval t ht
    exact hlam (by
      rw [← hval]
      exact hface p hpBox hfacept
        (crossE_normal_eq_zero_of_fderiv_eq_smul ψ hv1 hn1 hvn ht))
  · -- (iii) nondegeneracy of the Hessian and membership in `exc`
    intro p hpBox _hpSlab hcritp
    exact ⟨hMorse p hpBox hcritp, hcrit p hpBox hcritp⟩
  · -- (iv) distinctness of the critical values
    intro p p' hpBox hpBox' _hpSlab _hpSlab' hcritp hcritp' hval
    exact hdistinct p p' hpBox hpBox' hcritp hcritp' hval

/-! ## The analytic core (delegated), and the target -/


/-- **The thin-slab band input.**  At every configuration there are a slab direction `v`, a wall
normal `n ⊥ v`, a half-width `h` satisfying the size and cutting conditions, and a finite
exceptional set such that the tilt genericity `Work.Drive.Final.TiltedGenericity` holds. -/
theorem thinSlabBand_core
    (ψ : Submission.Diffeo) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u r : ℝ)
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r) :
    ∃ (v n : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ) (exc : Finset ℝ),
      ‖v‖ = 1 ∧ ‖n‖ = 1 ∧ inner ℝ v n = 0 ∧ 0 < h ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < h ∧
      h + |u| < boxWidth s σ v ∧
      Work.Drive.Final.TiltedGenericity ψ s c σ u v h ((innerSL ℝ) n) exc := by
  obtain ⟨v, n, h, exc, hv1, hn1, hvn, hh, hsize, hcut, hMorse, hdistinct, hcrit, hface⟩ :=
    bandData_core_exists ψ s c σ u r hr hrs hs hu
  exact ⟨v, n, h, exc, hv1, hn1, hvn, hh, hsize, hcut,
    tiltedGenericity_of_data ψ s c σ u v n h exc hv1 hn1 hvn hMorse hdistinct hcrit hface⟩

end

end Work.Drive.Mono.Band
