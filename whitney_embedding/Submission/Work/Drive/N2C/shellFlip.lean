import Mathlib
import Submission.Work.Drive.N2.roundConfigDefs

/-!
# `shellFlip`: a compactly supported smooth family of diffeomorphisms of `ℝ³` reversing the round
circle

The target `Work.Drive.N2C.shellFlip` produces a family `F s : ℝ³ → ℝ³` (`s ∈ ℝ`) of diffeomorphisms
of `ℝ³` which

* is jointly `C^∞`,
* starts at the identity (`F 0 = id`),
* is the identity outside the ball of radius `3 * r` about `c`,
* and at time `1` reverses the round circle of centre `c` and radius `r`:
  `F 1 (c + r • roundPic t) = c + r • roundPic (-t)`.

The construction is the classical "rotation of shells": rotate the space about the axis through `c`
spanned by the first coordinate direction, but by an angle which is a smooth function of the point,
constant `= π * s` near the circle and `= 0` outside the ball of radius `3 * r`.  A point of the
circle therefore moves exactly under the half-turn `rotX 1`, while the map is the identity far away.

Because the angle depends only on `‖· - c‖`, the map is the time-`s` flow of the (compactly
supported) vector field `v ↦ χ (‖v - c‖) • (e₁ × (v - c))`, so it is automatically a diffeomorphism:
we use the explicit inverse `F (-s)` and the chain rule for the injectivity of the derivative.

## Main ingredients

* `spinL θ` — the rotation of `ℝ³` about the first coordinate axis by the angle `θ`, as a continuous
  linear map; `spinL_norm`, `spinL_zero`, `spinL_add` and `spinL_pi_roundPic` are its elementary
  properties (all coordinate computations).
* `shellCut` — the smooth cutoff (constant `1` on `‖v‖ ≤ 2`, constant `0` for `‖v‖ ≥ 3`).
* `Gl τ u = spinL (τ * π * shellCut u) u` — the twisted rotation of the unit problem, with the
  involution identity `Gl (-τ) (Gl τ u) = u`.
* `Fam c r τ v = c + r • Gl τ ((1 / r) • (v - c))` — the rescaled and recentred family.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology

noncomputable section

/-! ### The rotation about the first coordinate axis -/

private def toLpCLM : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap

private def coord0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0
private def coord1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1
private def coord2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2

private def spinConst : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  toLpCLM.comp (ContinuousLinearMap.pi fun i : Fin 3 => if i = 0 then coord0 else 0)
private def spinCos : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  toLpCLM.comp (ContinuousLinearMap.pi fun i : Fin 3 =>
    if i = 1 then coord1 else if i = 2 then coord2 else 0)
private def spinSin : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  toLpCLM.comp (ContinuousLinearMap.pi fun i : Fin 3 =>
    if i = 1 then -coord2 else if i = 2 then coord1 else 0)

/-- The rotation of `ℝ³` about the first coordinate axis by the angle `θ`, as a continuous linear
map. -/
def spinL (θ : ℝ) : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  toLpCLM.comp (ContinuousLinearMap.pi fun i : Fin 3 =>
    if i = 0 then coord0
    else if i = 1 then Real.cos θ • coord1 - Real.sin θ • coord2
    else Real.sin θ • coord1 + Real.cos θ • coord2)

/-- The coordinate formula for `spinL θ`. -/
lemma spinL_ofLp (θ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (spinL θ u).ofLp = fun i : Fin 3 => if i = 0 then u 0
      else if i = 1 then Real.cos θ * u 1 - Real.sin θ * u 2
      else Real.sin θ * u 1 + Real.cos θ * u 2 := by
  funext i
  fin_cases i <;> simp [spinL, toLpCLM, coord0, coord1, coord2]

/-- `spinL` is a smooth function of the angle: it is the constant first-coordinate part plus
`cos θ` times one fixed linear map plus `sin θ` times another. -/
private lemma spinL_eq_affine (θ : ℝ) :
    spinL θ = spinConst + Real.cos θ • spinCos + Real.sin θ • spinSin := by
  ext y : 1
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i <;>
    simp [spinL, spinConst, spinCos, spinSin, toLpCLM, coord0, coord1, coord2] <;> ring

/-- `θ ↦ spinL θ` is `C^∞`. -/
private lemma spinL_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (spinL : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) := by
  have h : (spinL : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) =
      fun θ => spinConst + Real.cos θ • spinCos + Real.sin θ • spinSin := by
    funext θ; exact spinL_eq_affine θ
  rw [h]
  fun_prop

/-- Every `spinL θ` is isometric. -/
lemma spinL_norm (θ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ‖spinL θ u‖ = ‖u‖ := by
  have h : ‖spinL θ u‖ ^ 2 = ‖u‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, spinL_ofLp, Fin.sum_univ_three, Fin.isValue,
      ↓reduceIte, Fin.reduceEq, one_ne_zero, Real.norm_eq_abs, sq_abs]
    nlinarith [Real.cos_sq_add_sin_sq θ, sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
  nlinarith [norm_nonneg (spinL θ u), norm_nonneg u]

/-- `spinL 0` is the identity. -/
lemma spinL_zero (u : EuclideanSpace ℝ (Fin 3)) : spinL 0 u = u := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;> simp [spinL_ofLp]

/-- The angle addition formula for `spinL`. -/
lemma spinL_add (θ φ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    spinL θ (spinL φ u) = spinL (θ + φ) u := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;> simp [spinL_ofLp, Real.cos_add, Real.sin_add] <;> ring

/-! ### The round planar picture -/

private lemma roundPic_ofLp (t : ℝ) :
    (Work.Drive.N2.roundPic t).ofLp = ![Real.cos t, Real.sin t, (0 : ℝ)] := by
  simp [Work.Drive.N2.roundPic]

/-- The round picture has norm `1`. -/
lemma roundPic_norm (t : ℝ) : ‖Work.Drive.N2.roundPic t‖ = 1 := by
  have h : ‖Work.Drive.N2.roundPic t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [roundPic_ofLp, Fin.sum_univ_three]
  nlinarith [norm_nonneg (Work.Drive.N2.roundPic t)]

/-- The half-turn `spinL π` reverses the round picture. -/
lemma spinL_pi_roundPic (t : ℝ) :
    spinL Real.pi (Work.Drive.N2.roundPic t) = Work.Drive.N2.roundPic (-t) := by
  apply WithLp.ofLp_injective 2
  funext i
  simp only [spinL_ofLp, roundPic_ofLp]
  fin_cases i <;> simp [Real.cos_pi, Real.sin_pi, Real.cos_neg, Real.sin_neg]

/-! ### The cutoff and the twisted rotation -/

/-- The smooth cutoff: `1` on the ball of radius `2`, `0` outside the ball of radius `3`. -/
def shellCut (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.smoothTransition ((9 - ‖v‖ ^ 2) / 5)

private lemma shellCutArg_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun v : EuclideanSpace ℝ (Fin 3) => (9 - ‖v‖ ^ 2) / 5) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖ ^ 2) := contDiff_norm_sq ℝ
  exact (contDiff_const.sub h1).div_const 5

/-- The cutoff is `C^∞`. -/
lemma shellCut_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) shellCut :=
  Real.smoothTransition.contDiff.comp shellCutArg_contDiff

/-- The cutoff equals `1` on the ball of radius `2`. -/
lemma shellCut_eq_one (v : EuclideanSpace ℝ (Fin 3)) (h : ‖v‖ ≤ 2) : shellCut v = 1 := by
  unfold shellCut
  rw [Real.smoothTransition.eq_one_iff_one_le]
  have h2 : ‖v‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg v]
  linarith

/-- The cutoff equals `0` outside the ball of radius `3`. -/
lemma shellCut_eq_zero (v : EuclideanSpace ℝ (Fin 3)) (h : 3 ≤ ‖v‖) : shellCut v = 0 := by
  unfold shellCut
  apply Real.smoothTransition.zero_of_nonpos
  have h2 : 9 ≤ ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  linarith

/-- The twisted rotation of the unit problem. -/
def Gl (τ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  spinL (τ * Real.pi * shellCut u) u

/-- `Gl` is jointly `C^∞`. -/
lemma Gl_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Gl) := by
  have hinner : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => p.1 * Real.pi * shellCut p.2) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => shellCut p.2) :=
      shellCut_contDiff.comp contDiff_snd
    fun_prop
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => spinL (p.1 * Real.pi * shellCut p.2)) :=
    spinL_contDiff.comp hinner
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => p.2) := contDiff_snd
  have h3 := h1.clm_apply h2
  rw [show Function.uncurry Gl = (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
      spinL (p.1 * Real.pi * shellCut p.2) p.2) from rfl]
  exact h3

/-- `Gl` preserves the norm. -/
lemma Gl_norm (τ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ‖Gl τ u‖ = ‖u‖ := spinL_norm _ _

lemma shellCut_spin (θ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    shellCut (spinL θ u) = shellCut u := by
  unfold shellCut
  rw [spinL_norm]

/-- `Gl 0` is the identity. -/
lemma Gl_zero (u : EuclideanSpace ℝ (Fin 3)) : Gl 0 u = u := by
  simp only [Gl]
  rw [show (0 : ℝ) * Real.pi * shellCut u = 0 by ring, spinL_zero]

/-- The inverse of `Gl τ` is `Gl (-τ)`. -/
lemma Gl_comp (τ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : Gl (-τ) (Gl τ u) = u := by
  simp only [Gl]
  rw [shellCut_spin, spinL_add]
  rw [show -τ * Real.pi * shellCut u + τ * Real.pi * shellCut u = 0 by ring, spinL_zero]

/-- `Gl τ` is injective. -/
lemma Gl_inj (τ : ℝ) : Function.Injective (Gl τ) :=
  Function.LeftInverse.injective (g := Gl (-τ)) (fun u => Gl_comp τ u)

/-- `Gl τ` fixes everything outside the ball of radius `3`. -/
lemma Gl_fix (τ : ℝ) {u : EuclideanSpace ℝ (Fin 3)} (h : 3 ≤ ‖u‖) : Gl τ u = u := by
  simp only [Gl]
  rw [shellCut_eq_zero u h, show τ * Real.pi * 0 = 0 by ring, spinL_zero]

/-! ### The recentred and rescaled family -/

/-- The family of diffeomorphisms of `ℝ³`: rotate about the axis through `c` in the first coordinate
direction by the angle `τ * π` on the ball of radius `2 * r`, with a smooth cutoff outside. -/
def Fam (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (τ : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) := c + r • Gl τ ((1 / r) • (v - c))

/-- The family is jointly `C^∞`. -/
lemma Fam_contDiff (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (Fam c r)) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => (1 / r) • (p.2 - c)) :=
    (contDiff_snd.sub contDiff_const).const_smul (1 / r)
  have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => (p.1, (1 / r) • (p.2 - c))) :=
    ContDiff.prodMk contDiff_fst h1
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => Gl p.1 ((1 / r) • (p.2 - c))) := by
    have h := Gl_contDiff.comp hmap
    simpa only [Function.uncurry, Function.comp_def] using h
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => c + r • Gl p.1 ((1 / r) • (p.2 - c))) :=
    contDiff_const.add (hG.const_smul r)
  rw [show Function.uncurry (Fam c r) = (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
      c + r • Gl p.1 ((1 / r) • (p.2 - c))) from rfl]
  exact h2

/-- At time `0` the family is the identity. -/
lemma Fam_zero (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : r ≠ 0)
    (v : EuclideanSpace ℝ (Fin 3)) : Fam c r 0 v = v := by
  simp only [Fam, Gl_zero]
  rw [smul_smul, one_div, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]

/-- `Fam c r (-τ)` is a left inverse of `Fam c r τ`. -/
lemma Fam_comp (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : r ≠ 0) (τ : ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) : Fam c r (-τ) (Fam c r τ v) = v := by
  simp only [Fam]
  have h1 : (1 / r) • (c + r • Gl τ ((1 / r) • (v - c)) - c) = Gl τ ((1 / r) • (v - c)) := by
    rw [add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ hr, one_smul]
  rw [h1, Gl_comp]
  rw [smul_smul, one_div, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]

/-- Every slice of the family is injective. -/
lemma Fam_inj (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : r ≠ 0) (τ : ℝ) :
    Function.Injective (Fam c r τ) :=
  Function.LeftInverse.injective (g := Fam c r (-τ)) (fun v => Fam_comp c r hr τ v)

/-- At time `1` the family reverses the round circle of centre `c` and radius `r`. -/
lemma Fam_one (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : r ≠ 0) (t : ℝ) :
    Fam c r 1 (c + r • Work.Drive.N2.roundPic t) = c + r • Work.Drive.N2.roundPic (-t) := by
  simp only [Fam]
  have h1 : (1 / r) • (c + r • Work.Drive.N2.roundPic t - c) = Work.Drive.N2.roundPic t := by
    rw [add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ hr, one_smul]
  rw [h1]
  have hχ : shellCut (Work.Drive.N2.roundPic t) = 1 :=
    shellCut_eq_one _ (by rw [roundPic_norm]; norm_num)
  rw [Gl, hχ, mul_one, one_mul, spinL_pi_roundPic]

/-- The family is the identity outside the ball of radius `3 * r` about `c`. -/
lemma Fam_fix (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 < r) (τ : ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) (h : 3 * r < ‖v - c‖) : Fam c r τ v = v := by
  simp only [Fam]
  have hpos : (0 : ℝ) < 1 / r := by positivity
  have hnorm : ‖(1 / r) • (v - c)‖ = (1 / r) * ‖v - c‖ := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt hpos)]
  have h3 : 3 ≤ ‖(1 / r) • (v - c)‖ := by
    rw [hnorm]
    have hlt : (3 : ℝ) < (1 / r) * ‖v - c‖ := by
      have hm := mul_lt_mul_of_pos_left h hpos
      have he : (1 / r) * (3 * r) = 3 := by field_simp
      linarith
    exact le_of_lt hlt
  rw [Gl_fix τ h3]
  rw [smul_smul, one_div, mul_inv_cancel₀ (ne_of_gt hr), one_smul, add_sub_cancel]

/-- Every slice of the family is an immersion: the derivative is injective everywhere. -/
lemma Fam_fderiv_injective (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : r ≠ 0) (τ : ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) : Function.Injective (fderiv ℝ (Fam c r τ) v) := by
  have hjoint := Fam_contDiff c r
  have hslice : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fam c r τ) := by
    have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin 3) => (τ, w)) := ContDiff.prodMk contDiff_const contDiff_id
    have h := hjoint.comp hpair
    rwa [show (Function.uncurry (Fam c r)) ∘
      (fun w : EuclideanSpace ℝ (Fin 3) => (τ, w)) = (Fam c r τ) from rfl] at h
  have hslice' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fam c r (-τ)) := by
    have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin 3) => (-τ, w)) := ContDiff.prodMk contDiff_const contDiff_id
    have h := hjoint.comp hpair
    rwa [show (Function.uncurry (Fam c r)) ∘
      (fun w : EuclideanSpace ℝ (Fin 3) => (-τ, w)) = (Fam c r (-τ)) from rfl] at h
  have hd1 : DifferentiableAt ℝ (Fam c r τ) v :=
    (hslice.differentiable (by simp)).differentiableAt
  have hd2 : DifferentiableAt ℝ (Fam c r (-τ)) (Fam c r τ v) :=
    (hslice'.differentiable (by simp)).differentiableAt
  have hcomp := fderiv_comp (𝕜 := ℝ) v (g := (Fam c r (-τ))) hd2 hd1
  have hid : fderiv ℝ ((Fam c r (-τ)) ∘ (Fam c r τ)) v =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := by
    have hfun : (Fam c r (-τ)) ∘ (Fam c r τ) = id := by
      funext w; exact Fam_comp c r hr τ w
    rw [hfun, fderiv_id]
  have hL : (fderiv ℝ (Fam c r (-τ)) (Fam c r τ v)) ∘SL (fderiv ℝ (Fam c r τ) v) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← hcomp, hid]
  intro x y hxy
  have key : ∀ z : EuclideanSpace ℝ (Fin 3),
      (fderiv ℝ (Fam c r (-τ)) (Fam c r τ v)) ((fderiv ℝ (Fam c r τ) v) z) = z := by
    intro z
    have hz := congrArg (fun (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) =>
      L z) hL
    simpa using hz
  rw [← key x, ← key y, hxy]

end

open scoped Manifold ContDiff Topology in
/-- **Whitney's shell flip.**  For every centre `c` and radius `r > 0` there is a family of
diffeomorphisms of `ℝ³`, jointly `C^∞` in the time, starting at the identity, equal to the identity
outside the ball of radius `3 * r` about `c`, and reversing at time `1` the round circle
`c + r • roundPic`. -/
theorem shellFlip (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 < r) :
    ∃ F : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F) ∧
      (∀ s : ℝ, Function.Injective (F s)) ∧
      (∀ (s : ℝ) (w : EuclideanSpace ℝ (Fin 3)), Function.Injective (fderiv ℝ (F s) w)) ∧
      (∀ v : EuclideanSpace ℝ (Fin 3), F 0 v = v) ∧
      (∀ t : ℝ, F 1 (c + r • Work.Drive.N2.roundPic t) = c + r • Work.Drive.N2.roundPic (-t)) ∧
      (∀ (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)), 3 * r < ‖v - c‖ → F s v = v) := by
  refine ⟨Fam c r, Fam_contDiff c r, fun s => Fam_inj c r (ne_of_gt hr) s,
    fun s w => Fam_fderiv_injective c r (ne_of_gt hr) s w,
    fun v => Fam_zero c r (ne_of_gt hr) v, fun t => Fam_one c r (ne_of_gt hr) t,
    fun s v hv => Fam_fix c r hr s v hv⟩

end Work.Drive.N2C
