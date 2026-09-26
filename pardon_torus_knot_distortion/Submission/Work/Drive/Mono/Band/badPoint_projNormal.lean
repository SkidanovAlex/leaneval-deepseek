import Mathlib
import Submission.Work.Drive.Mono.Band.noTangency_data

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- The derivative in the parameter plane, at `p`, of the height `q ↦ ⟪a, par ψ q⟫` in the
direction `w` is `⟪a, d(par ψ)_p w⟫`.  Elementary form of the chain rule for the composition of the
parametrisation with the (linear) functional `⟪a, ·⟫`. -/
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

/-- **The Gauss normal at a bad point is a non-zero multiple of `n - t v`.**

If the differential at `p` of the swept height `sweepHeight ψ (⟪n, ·⟫)` is `t` times the differential
of the direction-`v` height, then `n - t v` is orthogonal to both partial derivatives of the
parametrisation, i.e. parallel to the Gauss normal `N p = ∂₁ ⨯ ∂₂`; and since the parametrisation is
an immersion `N p ≠ 0`, while `n - t v ≠ 0` (`v ⊥ n`, `‖v‖ = 1` exclude `n = t v`), the parallelism
comes with a *non-zero* factor. -/
private lemma exists_smul_normal_sub (ψ : Submission.Diffeo) {v n : R3} {t : ℝ} {p : ℝ × ℝ}
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (h : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p
      = t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ lam : ℝ, lam ≠ 0 ∧
      Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p = lam • (n - t • v) := by
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
  -- `n - t v` is orthogonal to `d1 × d2`, hence a multiple of it
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
  -- `n - t v ≠ 0`, because `n = t v` with `v ⊥ n`, `‖v‖ = 1` forces `n = 0`
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
  exact ⟨c⁻¹, inv_ne_zero hc0, by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

/-- **The normal at a bad point of the band lies in the plane `span(v, n)` with non-zero `n`-coordinate.**

At a point `p` where the differential of the swept height `sweepHeight ψ (⟪n, ·⟫)` is a scalar
multiple of the differential of the direction-`v` height, the Gauss normal `N p` is a non-zero
multiple of `n - t v` (previous lemma).  Since `v ⊥ n` and `‖v‖ = 1`, projecting that relation onto
`v` gives `⟪v, N p⟫ = -t·λ`, whence

  `N p - ⟪v, N p⟫ • v = λ • n`

with the *same* non-zero scalar `λ`.  This is the "bad point" of the band: the normal is a genuine
multiple of `n` after removing its `v`-component. -/
theorem badPoint_projNormal (ψ : Submission.Diffeo)
    {v n : LeanEval.KnotTheory.PardonDistortion.R3} {t : ℝ} {p : ℝ × ℝ}
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (h : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p
      = t • fderiv ℝ (fun q : ℝ × ℝ =>
          inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ c : ℝ, c ≠ 0 ∧
      Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p
        - inner ℝ v (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) • v
        = c • n := by
  obtain ⟨lam, hlam0, hlam⟩ := exists_smul_normal_sub ψ hv1 hn1 hvn h
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv1]; norm_num
  have hval : inner ℝ v (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = -(lam * t) := by
    rw [hlam, inner_smul_right, inner_sub_right, real_inner_smul_right, hvn, hvv]
    ring
  refine ⟨lam, hlam0, ?_⟩
  rw [hval, hlam]
  rw [smul_sub, smul_smul, neg_smul, sub_neg_eq_add, sub_add_cancel]

end

end Work.Drive.Mono.Band
