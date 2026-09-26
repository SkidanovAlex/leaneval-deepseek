import Mathlib
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Generic.ae_height_morse
import Submission.Work.Drive.Mono.ThinWidth.det_eq_zero_iff_parallel

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
private lemma inner_crossE_normal_eq_zero_of_fderiv_eq_smul
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
  -- `m := n - t v` is orthogonal to `d1 × d2`, hence a multiple of it
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

/-- The two non-tangency conclusions at a single point of the box: the swept height has non-zero
differential, and that differential is not a multiple of the direction-`v` height's differential.
Both are the contrapositive of the dictionary above, using the hypothesis that the Gauss image of
the box-region misses the plane `span(v, n)`. -/
private lemma fderiv_sweepHeight_ne_zero_and_ne_smul
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) {v n : R3}
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (hno : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      inner ℝ (Work.Drive.Generic.crossE v n)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) ≠ 0)
    {p : ℝ × ℝ} (hbox : Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ) :
    fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
  refine ⟨fun h0 => ?_, fun t ht => ?_⟩
  · exact hno p hbox
      (inner_crossE_normal_eq_zero_of_fderiv_eq_smul ψ hv1 hn1 hvn (t := 0) (by rw [h0, zero_smul]))
  · exact hno p hbox
      (inner_crossE_normal_eq_zero_of_fderiv_eq_smul ψ hv1 hn1 hvn (t := t) ht)

/-- The *avoidance* case of the thin-slab band data: if the Gauss image of the box-region misses
the plane spanned by the orthonormal pair `v, n` (equivalently `⟪v × n, N(par ψ p)⟫ ≠ 0` at every
`p` with `par ψ p ∈ PBox s c σ`), then the genericity `Work.Drive.Final.TiltedGenericity ψ s c σ u
v h (inner ℝ n) ∅` holds with the *empty* exceptional set and for *every* half-width `h` — all four
clauses are then vacuous or immediate.

The mathematical content is the dictionary

  `fderiv (sweepHeight ψ (inner ℝ n)) p = t • fderiv (fun q => ⟪v, par ψ q⟫) p`
    `⟺ n - t v ⊥ span (d1 (par ψ) p, d2 (par ψ) p)`
    `⟹ n ∈ span (v, N p)`, hence (as `v ⊥ n`, `n ≠ 0`) `N p ∈ span (v, n)`,
    i.e. `⟪v × n, N p⟫ = 0`,

where `N p = d1 × d2` is `Work.Drive.Generic.normal (par ψ) p`; and the case `t = 0` gives
`fderiv sweepHeight = 0 ⟹ ⟪v × n, N p⟫ = 0`.  The linear-algebra core of the last equivalence is
`Work.Drive.Mono.ThinWidth.det_eq_zero_iff_parallel`; the orthogonality
`⟪N p, d1⟫ = 0`, `⟪N p, d2⟫ = 0` and `N p ≠ 0` come from
`Work.Drive.Generic.normal`, `Work.Drive.Generic.normal_ne_zero` and the immersion
`Work.Smooth.Morse.Immersion.isImmersion` (equivalently, write `n - t v` in the basis
`d1, d2, N` and use that the Gram matrix of `d1, d2` is positive definite). -/
theorem noTangency_data
    (ψ : Submission.Diffeo) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v n : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ)
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (hno : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      inner ℝ (Work.Drive.Generic.crossE v n)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) ≠ 0) :
    Work.Drive.Final.TiltedGenericity ψ s c σ u v h ((innerSL ℝ) n) ∅ := by
  have hpt : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p ≠ 0 ∧
        ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p :=
    fun p hbox => fderiv_sweepHeight_ne_zero_and_ne_smul ψ s c σ hv1 hn1 hvn hno hbox
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lam _ p hbox _ _
    exact (hpt p hbox).1
  · intro lam _ p hbox _ _ t
    exact (hpt p hbox).2 t
  · intro p hbox _ hcrit
    exact absurd hcrit (hpt p hbox).1
  · intro p p' hbox _ _ _ hcrit _ _
    exact absurd hcrit (hpt p hbox).1

end

end Work.Drive.Mono.Band
