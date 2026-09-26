import Mathlib
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.Generic.inner_fderiv_normal_d1
import Submission.Work.Drive.Generic.inner_fderiv_normal_d2

/-!
# The second-derivative identity of the Gauss map on the parameter plane

For the parametrisation `par ψ : ℝ × ℝ → ℝ³` of the challenge surface and its Gauss normal
`N = ∂₁Φ ⨯ ∂₂Φ` (`Work.Drive.Generic.normal`), the derivative `dN_p` of the Gauss map is
orthogonal to the surface: for all directions `u, v` in the parameter plane,

`⟪dN_p(u), dΦ_p(v)⟫ = -⟪N(p), D²Φ(p)(u, v)⟫`   (`normal_fderiv_inner_gen`),

and in particular for the diagonal `u = v = w` the identity requested by the band chapter,
`normal_fderiv_inner_par`.

## Proof

`fderiv_normal_apply` expands `dN_p(u) = ∂₁Φ(p) ⨯ D²Φ(p)(u, ∂₂) + D²Φ(p)(u, ∂₁) ⨯ ∂₂Φ(p)` and a
continuous linear map out of `ℝ × ℝ` is determined by its values on `(1,0)` and `(0,1)`
(`Work.Drive.Mono.Band.clm_apply_basis`, i.e. `dΦ_p(v) = v.1 • ∂₁Φ(p) + v.2 • ∂₂Φ(p)` and
`(D²Φ(p)(u))(v) = v.1 • D²Φ(p)(u, ∂₁) + v.2 • D²Φ(p)(u, ∂₂)`), so it suffices to expand the inner
product and use the three elementary cross-product identities
`⟪a ⨯ c, a⟫ = 0`, `⟪a ⨯ c, b⟫ = -⟪a ⨯ b, c⟫` and `⟪b ⨯ c, a⟫ = -⟪a ⨯ b, c⟫`
(`inner_crossE_left`, `inner_crossE_swap`, `inner_crossE_swap13`) followed by linearity.

Note that no symmetry of the second derivative is used: the two "mixed" terms pair up with the
mixed terms of the expansion of `D²Φ(p)(u, v)` exactly as they arise from the two summands of
`dN_p(u)`.
-/

namespace Work.Drive.Mono.Band

open Work.Drive.Generic (crossE d1 d2 normal D2)

/-- A continuous linear map out of the parameter plane `ℝ × ℝ` is determined by its values at the
two coordinate directions: `T v = v.1 • T (1,0) + v.2 • T (0,1)`. -/
lemma clm_apply_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : (ℝ × ℝ) →L[ℝ] E) (v : ℝ × ℝ) :
    T v = v.1 • T (1, 0) + v.2 • T (0, 1) := by
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  nth_rewrite 1 [hv]
  rw [map_add, map_smul, map_smul]

/-- **The second-derivative identity of the Gauss map, off the diagonal.**  For the parametrisation
of the challenge surface and any two parameter directions `u, v`,
`⟪dN_p(u), dΦ_p(v)⟫ = -⟪N(p), D²Φ(p)(u,v)⟫`. -/
theorem normal_fderiv_inner_gen (ψ : Submission.Diffeo) (p u v : ℝ × ℝ) :
    inner ℝ (fderiv ℝ (normal (Work.BoxShrink.Pinch.par ψ)) p u)
        (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p v)
      = - inner ℝ (normal (Work.BoxShrink.Pinch.par ψ) p)
          (D2 (Work.BoxShrink.Pinch.par ψ) p u v) := by
  have hΦ : ContDiff ℝ 3 (Work.BoxShrink.Pinch.par ψ) := par_contDiff_three ψ
  set Φ := Work.BoxShrink.Pinch.par ψ with hΦdef
  have hΦ' : ContDiff ℝ 3 Φ := hΦdef ▸ hΦ
  rw [Work.Drive.Generic.fderiv_normal_apply hΦ' p u]
  rw [clm_apply_basis (fderiv ℝ Φ p) v, clm_apply_basis (D2 Φ p u) v]
  simp only [d1, d2, inner_add_left, inner_add_right, inner_smul_right]
  set a := (fderiv ℝ Φ p) (1, 0) with ha
  set b := (fderiv ℝ Φ p) (0, 1) with hb
  set A := (D2 Φ p u) (0, 1) with hA
  set B := (D2 Φ p u) (1, 0) with hB
  have hN : normal Φ p = crossE a b := rfl
  rw [hN]
  have e1 : inner ℝ (crossE a A) a = 0 := by
    rw [real_inner_comm, Work.Drive.Generic.inner_crossE_left]
  have e2 : inner ℝ (crossE a A) b = - inner ℝ (crossE a b) A :=
    Work.Drive.Generic.inner_crossE_swap a A b
  have e3 : inner ℝ (crossE B b) a = - inner ℝ (crossE a b) B :=
    Work.Drive.Generic.inner_crossE_swap13 B b a
  have e4 : inner ℝ (crossE B b) b = 0 := Work.Drive.Generic.inner_crossE_self B b
  rw [e1, e2, e3, e4]
  ring

/-- **The second-derivative identity of the Gauss map.**  For the parametrisation `par ψ` of the
challenge surface and any `p, w : ℝ × ℝ`, the derivative of the Gauss normal `N = ∂₁Φ ⨯ ∂₂Φ` in
the direction `w` is orthogonal to the tangent vector in the direction `w`:
`⟪dN_p(w), dΦ_p(w)⟫ = -⟪N(p), D²Φ(p)(w,w)⟫`.  Route: expand `w = w.1 • (1,0) + w.2 • (0,1)`, use
`Work.Drive.Generic.inner_fderiv_normal_d1` / `inner_fderiv_normal_d2` and the bilinearity of `D2`.
(Namespace `Work.Drive.Mono.Band`.) -/
theorem normal_fderiv_inner_par (ψ : Submission.Diffeo) (p w : ℝ × ℝ) :
    inner ℝ (fderiv ℝ (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ)) p w)
        (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p w)
      = - inner ℝ (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p)
          (Work.Drive.Generic.D2 (Work.BoxShrink.Pinch.par ψ) p w w) :=
  normal_fderiv_inner_gen ψ p w w

end Work.Drive.Mono.Band
