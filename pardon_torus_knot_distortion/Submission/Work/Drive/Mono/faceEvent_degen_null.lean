import Mathlib
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.Mono.Geom2Defs
import Submission.Work.Drive.Mono.Band.badPoint_chart
import Submission.Work.Drive.Mono.Band.normal_fderiv_inner_par
import Submission.Work.Drive.Mono.Band.chart_fderiv_apply

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-!
# The face-event degeneracy is null

This file proves `Work.Drive.Mono.faceEvent_degen_null`.

## The mathematics

Write `Φ = par ψ` for the parametrisation of the surface, `N = ∂₁Φ ⨯ ∂₂Φ` for the Gauss normal and
`v` for the (fixed) unit direction of the slab.  A *face event* of the tilted sweep, with level
functional `ℓ = ⟪n, ·⟫`, is a point `p` of the box at which the differential of the sweep height
`F = ⟪n, Φ·⟫` is proportional to `dG` for `G = ⟪v, Φ·⟫ - (⟪v,c⟫+u)`; the multiplier `t` is unique
because `dG ≠ 0` there, and the *nondegeneracy* clause asks that the second derivative of `H = F - tG`
be nonzero on `ker dG`.

The key computation is that this second derivative is, up to a nonzero factor, the second fundamental
form of the surface in the direction `w` spanning `ker dG = T_p ∩ v^⊥`:

* `H = ⟪n - t v, Φ·⟫ + const` and the tangency makes `U := n - t v` a nonzero multiple `λ • N` of the
  normal, so `d²H_p(w,w) = λ ⟪N, D²Φ(p)(w,w)⟫`;
* the vector identity `⟪dN_p(w), dΦ_p(w)⟫ = -⟪N, D²Φ(p)(w,w)⟫`
  (`Work.Drive.Mono.Band.normal_fderiv_inner_par`) turns the degeneracy into
  `⟪dN_p(w), dΦ_p(w)⟫ = 0`;
* finally `dΦ_p(w)` and `b₀-component • a₀ - a₀-component • b₀` are both nonzero vectors in the
  1-dimensional space `v^⊥ ∩ (projV)^⊥` (where `projV = N - ⟪v,N⟫ v` is the projected normal), so the
  degeneracy is equivalent to `d(chart)_p(w) = 0` for the projective coordinate
  `chart = alphaV/betaV` of the projected normal
  (`Work.Drive.Mono.Band.chart_fderiv_apply`).

Hence every degenerate face event is a critical point of the band-chart map
`p ↦ (heightV, chart)`, off the zero set of `betaV`.  Since `(h,τ)` is `(|heightV - c₀|, chart)`, the
failure set is the union of the images of the critical set of that map under two affine maps, which is
null by Mathlib's equal-dimension Sard lemma
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` (plus
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` for the affine maps).
-/

/-! ## Two elementary facts about an orthonormal pair in `v^⊥` -/

/-- **Expansion in an orthonormal triple.**  If `v, a₀, b₀` is an orthonormal triple and `Y ⊥ v`,
then `Y = ⟪a₀,Y⟫ • a₀ + ⟪b₀,Y⟫ • b₀`. -/
theorem onb_decomp {v a₀ b₀ Y : R3} (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (hY : inner ℝ v Y = 0) :
    Y = inner ℝ a₀ Y • a₀ + inner ℝ b₀ Y • b₀ := by
  have hba : inner ℝ b₀ a₀ = 0 := by rw [real_inner_comm]; exact hab
  have key : Y - inner ℝ a₀ Y • a₀ - inner ℝ b₀ Y • b₀ = 0 := by
    apply Work.Drive.Mono.Band.projV_coord_eq_zero hv ha hb hab hva hvb
    · simp only [inner_sub_right, real_inner_smul_right, hY, hva, hvb, mul_zero, sub_self]
    · simp only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ha, hab,
        mul_one, mul_zero, sub_self, sub_zero]
      ring
    · simp only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hb, hba,
        mul_one, mul_zero, sub_self, sub_zero]
      ring
  have key2 : Y - (inner ℝ a₀ Y • a₀ + inner ℝ b₀ Y • b₀) = 0 := by
    rw [← key]; abel
  exact sub_eq_zero.mp key2

/-- **Scalar product in terms of the components of the ONB.** -/
theorem inner_onb_decomp {v a₀ b₀ X Y : R3} (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (hX : inner ℝ v X = 0) (hY : inner ℝ v Y = 0) :
    inner ℝ X Y = inner ℝ a₀ X * inner ℝ a₀ Y + inner ℝ b₀ X * inner ℝ b₀ Y := by
  conv_lhs => rw [onb_decomp hv ha hb hab hva hvb hY]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [real_inner_comm X a₀, real_inner_comm X b₀]
  ring

/-- The Gauss normal is orthogonal to the first partial derivative (in the other argument order). -/
theorem inner_d1_normal (Φ : ℝ × ℝ → R3) (p : ℝ × ℝ) :
    inner ℝ (Work.Drive.Generic.d1 Φ p) (Work.Drive.Generic.normal Φ p) = 0 := by
  rw [real_inner_comm]
  exact Work.Drive.Mono.Band.inner_normal_d1 Φ p

/-- The Gauss normal is orthogonal to the second partial derivative (in the other argument order). -/
theorem inner_d2_normal (Φ : ℝ × ℝ → R3) (p : ℝ × ℝ) :
    inner ℝ (Work.Drive.Generic.d2 Φ p) (Work.Drive.Generic.normal Φ p) = 0 := by
  rw [real_inner_comm]
  exact Work.Drive.Mono.Band.inner_normal_d2 Φ p

/-- `crossE u v` is orthogonal to `v` (in the other argument order). -/
theorem inner_crossE_self_right (u v : R3) :
    inner ℝ (Work.Drive.Generic.crossE u v) v = 0 := by
  rw [real_inner_comm]
  exact Work.Drive.Generic.inner_crossE_right u v

/-- `crossE u v` is orthogonal to `u` (in the other argument order). -/
theorem inner_crossE_self_left (u v : R3) :
    inner ℝ (Work.Drive.Generic.crossE u v) u = 0 := by
  rw [real_inner_comm]
  exact Work.Drive.Generic.inner_crossE_left u v

/-- **The proportionality step.**  In the plane `v^⊥` with orthonormal basis `a₀, b₀`, if
`Y₂ ≠ 0` and `Y₂ ⊥ projV` while `Y₁ ⊥ Y₂`, then `Y₁` is orthogonal to the *rotation*
`⟪b₀,projV⟫ • a₀ - ⟪a₀,projV⟫ • b₀` of `projV` in `v^⊥`.  Equivalently: `Y₂` lies on the line
spanned by that rotation, and the scalar is nonzero. -/
theorem inner_eq_zero_of_inner_secondary
    {v a₀ b₀ Y₁ Y₂ PV : R3} (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (hPVne : PV ≠ 0) (hPVv : inner ℝ v PV = 0)
    (hY₁ : inner ℝ v Y₁ = 0) (hY₂ : inner ℝ v Y₂ = 0)
    (hY₂PV : inner ℝ Y₂ PV = 0) (hY₂ne : Y₂ ≠ 0)
    (h12 : inner ℝ Y₁ Y₂ = 0) :
    inner ℝ Y₁ (inner ℝ b₀ PV • a₀ - inner ℝ a₀ PV • b₀) = 0 := by
  have h1 : inner ℝ a₀ Y₂ * inner ℝ a₀ PV + inner ℝ b₀ Y₂ * inner ℝ b₀ PV = 0 := by
    have h := hY₂PV
    rw [inner_onb_decomp hv ha hb hab hva hvb hY₂ hPVv] at h
    linarith [h]
  have h2 : inner ℝ a₀ Y₁ * inner ℝ a₀ Y₂ + inner ℝ b₀ Y₁ * inner ℝ b₀ Y₂ = 0 := by
    have h := h12
    rw [inner_onb_decomp hv ha hb hab hva hvb hY₁ hY₂] at h
    linarith [h]
  have hXY : ¬(inner ℝ a₀ Y₂ = 0 ∧ inner ℝ b₀ Y₂ = 0) := by
    rintro ⟨hx, hy⟩
    exact hY₂ne (by rw [onb_decomp hv ha hb hab hva hvb hY₂, hx, hy, zero_smul, zero_smul,
      add_zero])
  have hgoal : inner ℝ Y₁ (inner ℝ b₀ PV • a₀ - inner ℝ a₀ PV • b₀)
      = inner ℝ a₀ Y₁ * inner ℝ b₀ PV - inner ℝ b₀ Y₁ * inner ℝ a₀ PV := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_comm Y₁ a₀, real_inner_comm Y₁ b₀]
    ring
  rw [hgoal]
  rcases eq_or_ne (inner ℝ a₀ Y₂) 0 with hx0 | hx0
  · have hy0 : inner ℝ b₀ Y₂ ≠ 0 := fun h => hXY ⟨hx0, h⟩
    have key : inner ℝ b₀ Y₂ * (inner ℝ a₀ Y₁ * inner ℝ b₀ PV
        - inner ℝ b₀ Y₁ * inner ℝ a₀ PV) = 0 := by
      have e : inner ℝ b₀ Y₂ * (inner ℝ a₀ Y₁ * inner ℝ b₀ PV
            - inner ℝ b₀ Y₁ * inner ℝ a₀ PV)
          = inner ℝ a₀ Y₁ * (inner ℝ a₀ Y₂ * inner ℝ a₀ PV
              + inner ℝ b₀ Y₂ * inner ℝ b₀ PV)
            - inner ℝ a₀ PV * (inner ℝ a₀ Y₁ * inner ℝ a₀ Y₂
              + inner ℝ b₀ Y₁ * inner ℝ b₀ Y₂) := by ring
      rw [e, h1, h2]; ring
    exact (mul_eq_zero.mp key).resolve_left hy0
  · have key : inner ℝ a₀ Y₂ * (inner ℝ a₀ Y₁ * inner ℝ b₀ PV
        - inner ℝ b₀ Y₁ * inner ℝ a₀ PV) = 0 := by
      have e : inner ℝ a₀ Y₂ * (inner ℝ a₀ Y₁ * inner ℝ b₀ PV
            - inner ℝ b₀ Y₁ * inner ℝ a₀ PV)
          = inner ℝ b₀ PV * (inner ℝ a₀ Y₁ * inner ℝ a₀ Y₂
              + inner ℝ b₀ Y₁ * inner ℝ b₀ Y₂)
            - inner ℝ b₀ Y₁ * (inner ℝ a₀ Y₂ * inner ℝ a₀ PV
              + inner ℝ b₀ Y₂ * inner ℝ b₀ PV) := by ring
      rw [e, h2, h1]; ring
    exact (mul_eq_zero.mp key).resolve_left hx0

/-! ## The derivatives of the chart functions -/

/-- The `a₀`-component `alphaV` of the projected Gauss normal is `⟪a₀, N⟫`. -/
theorem alphaV_eq_inner_normal (ψ : Submission.Diffeo) (v a₀ : R3) (hva : inner ℝ v a₀ = 0)
    (q : ℝ × ℝ) :
    Work.Drive.Mono.Band.alphaV ψ v a₀ q
      = inner ℝ a₀ (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) q) := by
  rw [Work.Drive.Mono.Band.alphaV, Work.Drive.Mono.Band.projVv, Work.Drive.Mono.Band.projV,
    inner_sub_right, inner_smul_right]
  rw [show inner ℝ a₀ v = 0 from by rw [real_inner_comm]; exact hva]
  ring

/-- The `b₀`-component `betaV` of the projected Gauss normal is `⟪b₀, N⟫`. -/
theorem betaV_eq_inner_normal (ψ : Submission.Diffeo) (v b₀ : R3) (hvb : inner ℝ v b₀ = 0)
    (q : ℝ × ℝ) :
    Work.Drive.Mono.Band.betaV ψ v b₀ q
      = inner ℝ b₀ (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) q) := by
  rw [Work.Drive.Mono.Band.betaV, Work.Drive.Mono.Band.projVv, Work.Drive.Mono.Band.projV,
    inner_sub_right, inner_smul_right]
  rw [show inner ℝ b₀ v = 0 from by rw [real_inner_comm]; exact hvb]
  ring

/-- The derivative of the `a₀`-component of the projected normal. -/
theorem fderiv_alphaV_apply (ψ : Submission.Diffeo) (v a₀ : R3) (hva : inner ℝ v a₀ = 0)
    (q w : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.Mono.Band.alphaV ψ v a₀) q w
      = inner ℝ a₀ (fderiv ℝ (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ)) q w) := by
  have hfun : Work.Drive.Mono.Band.alphaV ψ v a₀
      = fun p => inner ℝ a₀ (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) :=
    funext fun p => alphaV_eq_inner_normal ψ v a₀ hva p
  have hd : DifferentiableAt ℝ
      (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ)) q :=
    ((Work.Drive.Mono.Band.contDiff_normal (Work.Drive.Mono.Band.par_contDiff_three ψ)).differentiable
      (by norm_num)) q
  rw [hfun, fderiv_inner_apply ℝ (differentiableAt_const a₀) hd]
  simp

/-- The derivative of the `b₀`-component of the projected normal. -/
theorem fderiv_betaV_apply (ψ : Submission.Diffeo) (v b₀ : R3) (hvb : inner ℝ v b₀ = 0)
    (q w : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.Mono.Band.betaV ψ v b₀) q w
      = inner ℝ b₀ (fderiv ℝ (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ)) q w) := by
  have hfun : Work.Drive.Mono.Band.betaV ψ v b₀
      = fun p => inner ℝ b₀ (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) :=
    funext fun p => betaV_eq_inner_normal ψ v b₀ hvb p
  have hd : DifferentiableAt ℝ
      (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ)) q :=
    ((Work.Drive.Mono.Band.contDiff_normal (Work.Drive.Mono.Band.par_contDiff_three ψ)).differentiable
      (by norm_num)) q
  rw [hfun, fderiv_inner_apply ℝ (differentiableAt_const b₀) hd]
  simp

/-- The first partial derivatives of the parametrisation. -/
theorem fderiv_par_apply_eq (ψ : Submission.Diffeo) (q w : ℝ × ℝ) :
    fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q w
      = w.1 • Work.Drive.Generic.d1 (Work.BoxShrink.Pinch.par ψ) q
        + w.2 • Work.Drive.Generic.d2 (Work.BoxShrink.Pinch.par ψ) q := by
  have h : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul]
  rfl

/-- The derivative of the parametrisation is orthogonal to the Gauss normal. -/
theorem inner_fderiv_par_normal (ψ : Submission.Diffeo) (q w : ℝ × ℝ) :
    inner ℝ (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q w)
      (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) q) = 0 := by
  rw [fderiv_par_apply_eq ψ q w, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_d1_normal, inner_d2_normal]
  ring

/-! ## Differentiability of the two components -/

/-- The `v`-height of the surface is differentiable everywhere. -/
theorem hdiff_heightV (ψ : Submission.Diffeo) (v : R3) (q : ℝ × ℝ) :
    DifferentiableAt ℝ (Work.Drive.Mono.Band.heightV ψ v) q :=
  ((Work.Drive.Mono.Band.contDiff_heightV ψ v).differentiable (by norm_num)) q

/-- The projective chart `alphaV/betaV` of the projected normal is differentiable at every point at
which `betaV` does not vanish. -/
theorem hdiff_chart (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (q : ℝ × ℝ)
    (hβ : Work.Drive.Mono.Band.betaV ψ v b₀ q ≠ 0) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => Work.Drive.Mono.Band.alphaV ψ v a₀ q
      / Work.Drive.Mono.Band.betaV ψ v b₀ q) q := by
  have h1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => Work.Drive.Mono.Band.alphaV ψ v a₀ q
      * (Work.Drive.Mono.Band.betaV ψ v b₀ q)⁻¹) q :=
    ((Work.Drive.Mono.Band.contDiff_alphaV ψ v a₀).differentiable (by norm_num) q).mul
      (((Work.Drive.Mono.Band.contDiff_betaV ψ v b₀).differentiable (by norm_num) q).inv hβ)
  simpa only [div_eq_mul_inv] using h1

/-! ## The crux: a degenerate face event is a critical point of the band chart -/

/-- **A degenerate face event is a critical point of the band-chart map.**  Let `p` be a face event
of the tilted sweep at the level functional `ℓ = ⟪dirOf τ a₀ b₀, ·⟫` and the slab half-width `h`, and
suppose that the second-order nondegeneracy clause *fails* at `p`, i.e. that for the tangency
multiplier `t` some nonzero `w ∈ ker d(slabFnPar)` has `d²(sweepHeight - t·slabFnPar)_p(w,w) = 0`.

Then the projective coordinate `alphaV/betaV` of the projected Gauss normal at `p` is `τ`
(in particular `betaV ≠ 0`), and `p` is a critical point of the band-chart map
`q ↦ (heightV ψ v q, alphaV ψ v a₀ q / betaV ψ v b₀ q)`. -/
theorem faceEvent_degen_crux
    (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (τ h : ℝ) {p : ℝ × ℝ}
    (hface : Work.Drive.Final.IsFaceEvent ψ s c σ u v h
      ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p)
    (hfail : ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) p
        = t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p →
      ∃ w : ℝ × ℝ, w ≠ 0 ∧ fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p w = 0 ∧
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
          Work.Drive.EpsForm.sweepHeight ψ
            ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) q
            - t * Work.Drive.Final.slabFnPar ψ c u v q)) p) w w = 0) :
    Work.Drive.Mono.Band.betaV ψ v b₀ p ≠ 0 ∧
      Work.Drive.Mono.Band.alphaV ψ v a₀ p / Work.Drive.Mono.Band.betaV ψ v b₀ p = τ ∧
      (fderiv ℝ (fun q : ℝ × ℝ => (Work.Drive.Mono.Band.heightV ψ v q,
        Work.Drive.Mono.Band.alphaV ψ v a₀ q / Work.Drive.Mono.Band.betaV ψ v b₀ q)) p).det = 0 := by
  classical
  set n : R3 := Work.Drive.Mono.Band.dirOf τ a₀ b₀ with hn
  set Φ : ℝ × ℝ → R3 := Work.BoxShrink.Pinch.par ψ with hΦdef
  obtain ⟨t, ht⟩ := hface.2.2
  obtain ⟨w, hwne, hGw, h2nd⟩ := hfail t ht
  -- the derivative formulas for the two heights
  have hFw : ∀ X : ℝ × ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p X
      = inner ℝ n (fderiv ℝ Φ p X) := by
    intro X
    rw [Work.Drive.EpsForm.sweepHeight_innerSL]
    exact Work.Drive.Generic.fderiv_height_eq (Work.Drive.Mono.Band.par_contDiff_three ψ) n p X
  have hGw' : ∀ X : ℝ × ℝ, fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p X
      = inner ℝ v (fderiv ℝ Φ p X) := by
    intro X
    have hfun : Work.Drive.Final.slabFnPar ψ c u v
        = fun q => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u) := by
      funext q; rw [Work.Drive.Final.slabFnPar_apply, Work.Drive.Final.slabFn_apply]
    rw [hfun, fderiv_sub_const]
    exact Work.Drive.Generic.fderiv_height_eq (Work.Drive.Mono.Band.par_contDiff_three ψ) v p X
  -- the tangent multiplier
  set U : R3 := n - t • v with hU
  have hkey : inner ℝ n (Work.Drive.Generic.d1 Φ p)
      = t * inner ℝ v (Work.Drive.Generic.d1 Φ p) := by
    have h := congrArg (fun (L : (ℝ × ℝ) →L[ℝ] ℝ) => L (1, 0)) ht
    simp only [smul_apply, smul_eq_mul] at h
    rw [hFw (1, 0), hGw' (1, 0)] at h
    exact h
  have hkey2 : inner ℝ n (Work.Drive.Generic.d2 Φ p)
      = t * inner ℝ v (Work.Drive.Generic.d2 Φ p) := by
    have h := congrArg (fun (L : (ℝ × ℝ) →L[ℝ] ℝ) => L (0, 1)) ht
    simp only [smul_apply, smul_eq_mul] at h
    rw [hFw (0, 1), hGw' (0, 1)] at h
    exact h
  have hUd1 : inner ℝ U (Work.Drive.Generic.d1 Φ p) = 0 := by
    rw [hU, inner_sub_left, real_inner_smul_left, hkey]; ring
  have hUd2 : inner ℝ U (Work.Drive.Generic.d2 Φ p) = 0 := by
    rw [hU, inner_sub_left, real_inner_smul_left, hkey2]; ring
  have hUd1' : inner ℝ (Work.Drive.Generic.d1 Φ p) U = 0 := by
    rw [real_inner_comm]; exact hUd1
  -- `U ≠ 0`
  have hnv : inner ℝ n v = 0 := by
    have h2 := Work.Drive.Mono.Band.inner_v_dirOf hva hvb τ
    rw [← hn, real_inner_comm] at h2
    exact h2
  have hUne : U ≠ 0 := by
    intro h0
    have hn_eq : n = t • v := by
      have h1 : n - t • v = 0 := by rw [← hU]; exact h0
      exact sub_eq_zero.mp h1
    have htv : inner ℝ n v = t := by
      rw [hn_eq, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
      norm_num
    have htz : t = 0 := by rw [← htv]; exact hnv
    have hzero : n = 0 := by rw [hn_eq, htz, zero_smul]
    have hn1 : ‖n‖ = 1 := by rw [hn]; exact Work.Drive.Mono.Band.norm_dirOf ha hb hab τ
    rw [hzero, norm_zero] at hn1
    exact one_ne_zero hn1.symm
  -- `U` is a multiple of the Gauss normal
  have hcross : Work.Drive.Generic.crossE U (Work.Drive.Generic.normal Φ p) = 0 := by
    rw [Work.Drive.Generic.normal, Work.Drive.Generic.crossE_crossE, hUd2, hUd1']
    simp
  obtain ⟨lam, hlam⟩ := Work.Drive.Generic.exists_smul_of_crossE_eq_zero hcross
    (Work.Drive.Mono.Band.normal_par_ne_zero ψ p)
  have hlamne : lam ≠ 0 := by
    intro h0
    exact hUne (by rw [hlam, h0, zero_smul])
  -- the degeneracy, read as `⟪N, D²Φ(p)(w,w)⟫ = 0`
  have hHfun : (fun q : ℝ × ℝ => Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n) q
        - t * Work.Drive.Final.slabFnPar ψ c u v q)
      = fun q => inner ℝ U (Φ q) + t * (inner ℝ v c + u) := by
    funext q
    rw [Work.Drive.EpsForm.sweepHeight_innerSL, Work.Drive.Final.slabFnPar_apply,
      Work.Drive.Final.slabFn_apply, hU, inner_sub_left, real_inner_smul_left]
    ring
  have h2nd' : inner ℝ U (Work.Drive.Generic.D2 Φ p w w) = 0 := by
    have h := h2nd
    rw [hHfun] at h
    have hc : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ U (Φ q) + t * (inner ℝ v c + u))
        = fderiv ℝ (fun q : ℝ × ℝ => inner ℝ U (Φ q)) := by
      funext q; rw [fderiv_add_const]
    rw [hc] at h
    rw [Work.Drive.Generic.fderiv_fderiv_height_eq (Work.Drive.Mono.Band.par_contDiff_three ψ)
      U p w w] at h
    exact h
  have hN2nd : inner ℝ (Work.Drive.Generic.normal Φ p) (Work.Drive.Generic.D2 Φ p w w) = 0 := by
    have h := h2nd'
    rw [hlam] at h
    rw [inner_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left hlamne
  -- the projected normal does not vanish
  have hprojne : Work.Drive.Mono.Band.projV Φ v p ≠ 0 := by
    intro h0
    obtain ⟨cc, hcc⟩ := (Work.Drive.Mono.Band.projV_eq_zero_iff hv p).mp h0
    have hn_eq : n = (t + lam * cc) • v := by
      have h1 : U = (lam * cc) • v := by rw [hlam, hcc, smul_smul]
      have h2 : n - t • v = (lam * cc) • v := by rw [← hU]; exact h1
      have h3 : n = (lam * cc) • v + t • v := by
        have := congrArg (fun x : R3 => x + t • v) h2
        simpa using this
      rw [h3, ← add_smul, add_comm]
    have hnv2 : inner ℝ n v = t + lam * cc := by
      rw [hn_eq, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
      norm_num
    have hzero : n = 0 := by
      rw [hn_eq, show t + lam * cc = 0 from by rw [← hnv2]; exact hnv, zero_smul]
    have hn1 : ‖n‖ = 1 := by rw [hn]; exact Work.Drive.Mono.Band.norm_dirOf ha hb hab τ
    rw [hzero, norm_zero] at hn1
    exact one_ne_zero hn1.symm
  have hbad : inner ℝ (Work.Drive.Generic.crossE v n) (Work.Drive.Generic.normal Φ p) = 0 := by
    have hN : Work.Drive.Generic.normal Φ p = lam⁻¹ • U := by
      rw [hlam, smul_smul, inv_mul_cancel₀ hlamne, one_smul]
    rw [hN, hU, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      inner_crossE_self_right v n, inner_crossE_self_left v n]
    ring
  obtain ⟨hchart, hβne⟩ :=
    Work.Drive.Mono.Band.badPoint_chart ψ hv ha hb hab hva hvb hbad hprojne
  refine ⟨hβne, hchart, ?_⟩
  -- the tangent vector and the derivative of the Gauss normal
  have hdw_ne : fderiv ℝ Φ p w ≠ 0 := by
    intro h0
    exact hwne (Work.Drive.Mono.Band.par_immersion ψ p (h0.trans (map_zero _).symm))
  have hdw_v : inner ℝ v (fderiv ℝ Φ p w) = 0 := by
    have h := hGw
    rw [hGw' w] at h
    exact h
  have hdw_N : inner ℝ (fderiv ℝ Φ p w) (Work.Drive.Generic.normal Φ p) = 0 := by
    rw [fderiv_par_apply_eq ψ p w, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_d1_normal, inner_d2_normal]
    ring
  have hdw_PV : inner ℝ (fderiv ℝ Φ p w) (Work.Drive.Mono.Band.projVv ψ v p) = 0 := by
    have h1 : inner ℝ ((fderiv ℝ Φ p) w) v = 0 := by
      rw [real_inner_comm]; exact hdw_v
    rw [Work.Drive.Mono.Band.projVv, Work.Drive.Mono.Band.projV, inner_sub_right,
      inner_smul_right, hdw_N, h1]
    ring
  have hPVv : inner ℝ v (Work.Drive.Mono.Band.projVv ψ v p) = 0 := by
    rw [Work.Drive.Mono.Band.projVv, Work.Drive.Mono.Band.projV, inner_sub_right,
      inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hPVne : Work.Drive.Mono.Band.projVv ψ v p ≠ 0 := hprojne
  -- the two vectors of the proportionality step
  set Y₁ : R3 := fderiv ℝ (Work.Drive.Generic.normal Φ) p w
    - (inner ℝ v (fderiv ℝ (Work.Drive.Generic.normal Φ) p w)) • v with hY₁def
  have hY₁v : inner ℝ v Y₁ = 0 := by
    rw [hY₁def, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have h12 : inner ℝ Y₁ (fderiv ℝ Φ p w) = 0 := by
    rw [hY₁def, inner_sub_left, inner_smul_left, hdw_v,
      Work.Drive.Mono.Band.normal_fderiv_inner_par ψ p w, hN2nd]
    ring
  have hsec := inner_eq_zero_of_inner_secondary hv ha hb hab hva hvb hPVne hPVv hY₁v hdw_v
    hdw_PV hdw_ne h12
  -- the conclusion: the chart is critical
  have hnum : inner ℝ a₀ (fderiv ℝ (Work.Drive.Generic.normal Φ) p w)
        * inner ℝ b₀ (Work.Drive.Mono.Band.projVv ψ v p)
      - inner ℝ a₀ (Work.Drive.Mono.Band.projVv ψ v p)
        * inner ℝ b₀ (fderiv ℝ (Work.Drive.Generic.normal Φ) p w) = 0 := by
    have h := hsec
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right] at h
    have ha' : inner ℝ Y₁ a₀ = inner ℝ a₀ (fderiv ℝ (Work.Drive.Generic.normal Φ) p w) := by
      rw [hY₁def, inner_sub_left, inner_smul_left, hva, mul_zero, sub_zero, real_inner_comm]
    have hb' : inner ℝ Y₁ b₀ = inner ℝ b₀ (fderiv ℝ (Work.Drive.Generic.normal Φ) p w) := by
      rw [hY₁def, inner_sub_left, inner_smul_left, hvb, mul_zero, sub_zero, real_inner_comm]
    rw [ha', hb'] at h
    linarith [h]
  have hdchart : fderiv ℝ (fun q : ℝ × ℝ => Work.Drive.Mono.Band.alphaV ψ v a₀ q
      / Work.Drive.Mono.Band.betaV ψ v b₀ q) p w = 0 := by
    rw [Work.Drive.Mono.Band.chart_fderiv_apply ψ v a₀ b₀ hβne w]
    rw [fderiv_alphaV_apply ψ v a₀ hva p w, fderiv_betaV_apply ψ v b₀ hvb p w]
    simp only [Work.Drive.Mono.Band.alphaV, Work.Drive.Mono.Band.betaV]
    rw [hnum]
    simp
  -- the two components of the band chart map
  have hh : fderiv ℝ (Work.Drive.Mono.Band.heightV ψ v) p w = 0 := by
    have hfun : Work.Drive.Mono.Band.heightV ψ v
        = fun q => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) := rfl
    rw [hfun, Work.Drive.Generic.fderiv_height_eq (Work.Drive.Mono.Band.par_contDiff_three ψ)
      v p w, hdw_v]
  have hdband : fderiv ℝ (fun q : ℝ × ℝ => (Work.Drive.Mono.Band.heightV ψ v q,
      Work.Drive.Mono.Band.alphaV ψ v a₀ q / Work.Drive.Mono.Band.betaV ψ v b₀ q)) p w = 0 := by
    rw [DifferentiableAt.fderiv_prodMk (hdiff_heightV ψ v p) (hdiff_chart ψ v a₀ b₀ p hβne)]
    rw [ContinuousLinearMap.prod_apply, hh, hdchart]
    rfl
  rw [show (fderiv ℝ (fun q : ℝ × ℝ => (Work.Drive.Mono.Band.heightV ψ v q,
        Work.Drive.Mono.Band.alphaV ψ v a₀ q / Work.Drive.Mono.Band.betaV ψ v b₀ q)) p).det
      = LinearMap.det (fderiv ℝ (fun q : ℝ × ℝ => (Work.Drive.Mono.Band.heightV ψ v q,
        Work.Drive.Mono.Band.alphaV ψ v a₀ q / Work.Drive.Mono.Band.betaV ψ v b₀ q)) p).toLinearMap
      by simp,
    LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro hbot
  exact hwne ((Submodule.eq_bot_iff _).mp hbot w (LinearMap.mem_ker.mpr hdband))


/-! ## The main statement -/

/-- **Almost every pair `(h, τ)` has no degenerate face event: the face-event nondegeneracy holds
off a null set of `(h, τ)`.**

`Work.Drive.Final.IsFaceEvent ψ s c σ u v h ℓ p` is a point of the surface inside the box and on a
slab face at which the swept height `sweepHeight ψ ℓ` is *tangent* to the slab height
`slabFnPar ψ c u v`. The statement says: for almost every pair `(h, τ)`, with
`ℓ = innerSL ℝ (dirOf τ a₀ b₀)`, every such point `p` satisfies the *constrained second-order
nondegeneracy* of `Work.Drive.Final.GoodSweepData2` (the Cerf-type clause consumed by
`Work.Drive.Final.faceEventGates`).

Route (for the prover): two reductions suffice.

* The τ-slices of the failure set are null for every `τ` for which the *degenerate tangency locus*
  `{p : dF_τ p ∥ dG_p ∧ (the second derivative of F_τ - t G vanishes on ker dG_p)}` is a *discrete*
  subset of the compact fundamental domain `[0,2π]² ∩ par⁻¹ (closure PBox)`; indeed then the bad
  `h`-set is the image of a finite set under `p ↦ |slabFn (par p)|`.
* The set of `τ` at which the degenerate tangency locus is *not* discrete (i.e. contains an arc) is
  itself null: this is the Cerf-type genericity statement, the only hard part. It is where the
  analyticity of `Submission.Diffeo` (`ContDiff ℝ (⊤ : ℕ∞)`, i.e. analyticity in this workspace,
  cf. `Work.Drive.Mono.Band.ae_height_good` and `Work.Drive.Mono.ThinWidth.finiteBadLevels`) is
  used: the failure of discreteness is an analytic condition in `(τ, p)`.

Tonelli/Fubini then gives the nullity of the failure set, which is measurable (a projection of a
Borel set over a compact domain; the parallelism locus is the zero set of
`det (fderiv F_τ, fderiv G)`). -/
theorem faceEvent_degen_null
    (ψ : Submission.Diffeo) (s u : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (hv : ‖v‖ = 1)
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) :
    MeasureTheory.volume {(h, τ) : ℝ × ℝ |
      ¬ (∀ p : ℝ × ℝ, Work.Drive.Final.IsFaceEvent ψ s c σ u v h
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p →
          ∃ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
              ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) p
              = t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p ∧
            ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p w = 0 →
              (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
                Work.Drive.EpsForm.sweepHeight ψ
                  ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) q
                  - t * Work.Drive.Final.slabFnPar ψ c u v q)) p) w w ≠ 0)} = 0 := by
  classical
  -- the band-chart map `q ↦ (heightV, alphaV/betaV)` and its critical set
  set bandMap : ℝ × ℝ → ℝ × ℝ := fun q => (Work.Drive.Mono.Band.heightV ψ v q,
    Work.Drive.Mono.Band.alphaV ψ v a₀ q / Work.Drive.Mono.Band.betaV ψ v b₀ q) with hbandMap
  set crit : Set (ℝ × ℝ) := {q | Work.Drive.Mono.Band.betaV ψ v b₀ q ≠ 0 ∧
    (fderiv ℝ bandMap q).det = 0} with hcrit
  -- Sard: the image of the critical set of the band chart is null
  have hnull : MeasureTheory.volume (bandMap '' crit) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := MeasureTheory.volume) (s := crit) (f := bandMap)
      (f' := fun q => fderiv ℝ bandMap q) ?_ ?_
    · intro q hq
      exact ((hdiff_heightV ψ v q).prodMk (hdiff_chart ψ v a₀ b₀ q hq.1)).hasFDerivAt
        |>.hasFDerivWithinAt
    · intro q hq
      exact hq.2
  -- the two affine maps `(x,y) ↦ (x - c₀, y)` and `(x,y) ↦ (c₀ - x, y)`
  set g₁ : ℝ × ℝ → ℝ × ℝ := fun y => (y.1 - (inner ℝ v c + u), y.2) with hg₁
  set g₂ : ℝ × ℝ → ℝ × ℝ := fun y => ((inner ℝ v c + u) - y.1, y.2) with hg₂
  have hnull₁ : MeasureTheory.volume (g₁ '' (bandMap '' crit)) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := MeasureTheory.volume) (s := bandMap '' crit) (f := g₁)
      (by rw [hg₁]; fun_prop) hnull
  have hnull₂ : MeasureTheory.volume (g₂ '' (bandMap '' crit)) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := MeasureTheory.volume) (s := bandMap '' crit) (f := g₂)
      (by rw [hg₂]; fun_prop) hnull
  -- the failure set is contained in those two images
  refine MeasureTheory.measure_mono_null ?_
    (MeasureTheory.measure_union_null hnull₁ hnull₂)
  rintro ⟨h, τ⟩ hmem
  simp only [Set.mem_setOf_eq] at hmem
  push_neg at hmem
  obtain ⟨p, hface, hfail⟩ := hmem
  obtain ⟨hβne, hchart, hdet⟩ :=
    faceEvent_degen_crux ψ s u c σ v a₀ b₀ hv ha hb hab hva hvb τ h hface hfail
  have hp : p ∈ crit := by
    rw [hcrit, Set.mem_setOf_eq]
    exact ⟨hβne, by rw [hbandMap]; exact hdet⟩
  have hband : bandMap p ∈ bandMap '' crit := ⟨p, hp, rfl⟩
  -- the value of `h`
  have habs : h = |Work.Drive.Mono.Band.heightV ψ v p - (inner ℝ v c + u)| := by
    have h1 := hface.2.1
    rw [Work.Drive.Final.slabFn_apply] at h1
    rw [← h1]
    simp only [Work.Drive.Mono.Band.heightV, Work.BoxShrink.Pinch.par]
  by_cases hle : (inner ℝ v c + u) ≤ Work.Drive.Mono.Band.heightV ψ v p
  · left
    refine ⟨bandMap p, hband, ?_⟩
    rw [hg₁, hbandMap]
    refine Prod.ext ?_ ?_
    · rw [habs, abs_of_nonneg (by linarith)]
    · exact hchart
  · right
    refine ⟨bandMap p, hband, ?_⟩
    rw [hg₂, hbandMap]
    refine Prod.ext ?_ ?_
    · rw [habs, abs_of_neg (by linarith)]; ring
    · exact hchart

end

end Work.Drive.Mono
