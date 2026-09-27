import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.orientationFlipDefs
import Submission.Work.Drive.N2.rigidMotionPathIsotopy

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology

noncomputable section

/-!
## The round picture and the half-turn path: auxiliary facts

The file `Submission/Work/Drive/N2/orientationFlipDefs.lean` defines

* `roundPic t = (cos t, sin t, 0) ∈ ℝ³`, the round planar picture of the circle, and
* `rotX s`, the rotation about the first coordinate axis by the angle `s * π`, as a continuous
  linear map (`rotX 0 = id`, `rotX 1` the half-turn in the second and third coordinates).

Here we collect the elementary facts about them that the engine
`Work.Drive.N2.rigidMotionPathIsotopy` asks for (smoothness of the picture, its injectivity modulo
the period `2π`, the non-vanishing of its derivative) together with the statements describing the
path `s ↦ rotX s` itself (each `rotX s` is isometric, the path is `C^∞`, and the two endpoint
identities).  All the auxiliary declarations are `private` so that they cannot collide with the
helpers of the neighbouring files of the drive.
-/

/-- The continuous linear map underlying `WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)`,
i.e. the map `f ↦ (f 0, f 1, f 2)`; it is the outer map in the definition of `rotX` and it is the map
that turns a coordinate triple into a point of `ℝ³`. -/
private def toLpCLM : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap

private lemma toLpCLM_apply (f : Fin 3 → ℝ) :
    (toLpCLM f).ofLp = f := by
  simp [toLpCLM]

private lemma toLpCLM_eq_zero {f : Fin 3 → ℝ} (hf : toLpCLM f = 0) : f = 0 := by
  have h := congrArg WithLp.ofLp hf
  simpa [toLpCLM] using h

/-- The three coordinate projections of `ℝ³`. -/
private def coord0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0
private def coord1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1
private def coord2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2

/-- The constant (in `s`) part of the rotation: the first coordinate is unchanged. -/
private def rotConst : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  toLpCLM.comp (ContinuousLinearMap.pi fun i : Fin 3 => if i = 0 then coord0 else 0)

/-- The `cos (s * π)` part of the rotation. -/
private def rotCos : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  toLpCLM.comp (ContinuousLinearMap.pi fun i : Fin 3 =>
    if i = 1 then coord1 else if i = 2 then coord2 else 0)

/-- The `sin (s * π)` part of the rotation. -/
private def rotSin : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  toLpCLM.comp (ContinuousLinearMap.pi fun i : Fin 3 =>
    if i = 1 then -coord2 else if i = 2 then coord1 else 0)

/-- **The path of rotations is a linear combination with smooth coefficients**: `rotX s` is the
constant first-coordinate projection plus `cos (s * π)` times the "`cos` part" plus `sin (s * π)`
times the "`sin` part". -/
private lemma rotX_eq_affine (s : ℝ) :
    rotX s = rotConst + Real.cos (s * Real.pi) • rotCos + Real.sin (s * Real.pi) • rotSin := by
  ext y : 1
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i <;>
    simp [rotX, rotConst, rotCos, rotSin, toLpCLM, coord0, coord1, coord2] <;> ring

/-- Coordinate formula for the rotation: `rotX s y` has coordinates
`(y 0, cos (s * π) * y 1 - sin (s * π) * y 2, sin (s * π) * y 1 + cos (s * π) * y 2)`. -/
private lemma rotX_ofLp (s : ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    (rotX s y).ofLp =
      fun i : Fin 3 => if i = 0 then y 0
        else if i = 1 then Real.cos (s * Real.pi) * y 1 - Real.sin (s * Real.pi) * y 2
        else Real.sin (s * Real.pi) * y 1 + Real.cos (s * Real.pi) * y 2 := by
  funext i
  fin_cases i <;> simp [rotX]

/-- **Every `rotX s` is isometric.** -/
private lemma rotX_norm (s : ℝ) (y : EuclideanSpace ℝ (Fin 3)) : ‖rotX s y‖ = ‖y‖ := by
  have h : ‖rotX s y‖ ^ 2 = ‖y‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, rotX_ofLp, Fin.sum_univ_three, Fin.isValue,
      ↓reduceIte, Fin.reduceEq, one_ne_zero, Real.norm_eq_abs, sq_abs]
    nlinarith [Real.cos_sq_add_sin_sq (s * Real.pi), sq_nonneg (y 0), sq_nonneg (y 1),
      sq_nonneg (y 2)]
  nlinarith [norm_nonneg (rotX s y), norm_nonneg y]

/-- **The path `s ↦ rotX s` is `C^∞`.** -/
private lemma rotX_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (rotX : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) := by
  have h : (rotX : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) =
      fun s => rotConst + Real.cos (s * Real.pi) • rotCos + Real.sin (s * Real.pi) • rotSin :=
    funext rotX_eq_affine
  rw [h]
  fun_prop

/-! ### Facts about the round picture `roundPic` -/

/-- The round picture in coordinates. -/
private lemma roundPic_ofLp (t : ℝ) :
    (roundPic t).ofLp = ![Real.cos t, Real.sin t, (0 : ℝ)] := by
  simp [roundPic]

/-- **The round picture is smooth.** -/
private lemma roundPic_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ roundPic := by
  rw [contMDiff_iff_contDiff]
  have h : roundPic =
      fun t : ℝ => toLpCLM (fun i : Fin 3 => ![Real.cos t, Real.sin t, (0 : ℝ)] i) := by
    funext t
    simp [roundPic, toLpCLM]
  rw [h]
  refine toLpCLM.contDiff.comp ?_
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- **The round picture is injective modulo the period `2π`**: two parameters giving the same point
of `ℝ³` differ by an integer multiple of `2π`.  (The `cos` and `sin` equalities are promoted to an
equality of complex exponentials, and `Complex.exp_eq_exp_iff_exists_int` reads off the period.) -/
private lemma roundPic_period (x y : ℝ) (hxy : roundPic x = roundPic y) :
    ∃ k : ℤ, y = x + k * (2 * Real.pi) := by
  have h0 : (roundPic x).ofLp = (roundPic y).ofLp := by rw [hxy]
  have hcos : Real.cos x = Real.cos y := by
    simpa [roundPic_ofLp] using congrArg (fun v : Fin 3 → ℝ => v 0) h0
  have hsin : Real.sin x = Real.sin y := by
    simpa [roundPic_ofLp] using congrArg (fun v : Fin 3 → ℝ => v 1) h0
  have hexp : Complex.exp (↑x * Complex.I) = Complex.exp (↑y * Complex.I) := by
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, hcos, hsin]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨-n, ?_⟩
  have h := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im] at h
  norm_num at h
  push_cast
  linarith [h]

/-- **The round picture is immersive**: its derivative never vanishes. -/
private lemma roundPic_immersion (t : ℝ) : fderiv ℝ roundPic t ≠ 0 := by
  have hround : roundPic = fun u : ℝ => toLpCLM (![Real.cos u, Real.sin u, (0 : ℝ)]) := by
    funext u; simp [roundPic, toLpCLM]
  have hw : HasFDerivAt (fun u : ℝ => ![Real.cos u, Real.sin u, (0 : ℝ)])
      (ContinuousLinearMap.pi fun i : Fin 3 =>
        ContinuousLinearMap.toSpanSingleton ℝ (![-Real.sin t, Real.cos t, (0 : ℝ)] i)) t := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · simpa using (Real.hasDerivAt_cos t).hasFDerivAt
    · simpa using (Real.hasDerivAt_sin t).hasFDerivAt
    · exact hasFDerivAt_const (c := (0 : ℝ)) t
  have hfd : fderiv ℝ (fun u : ℝ => toLpCLM (![Real.cos u, Real.sin u, (0 : ℝ)])) t
      = toLpCLM.comp (ContinuousLinearMap.pi fun i : Fin 3 =>
          ContinuousLinearMap.toSpanSingleton ℝ (![-Real.sin t, Real.cos t, (0 : ℝ)] i)) := by
    simpa [Function.comp_def] using (toLpCLM.hasFDerivAt.comp t hw).fderiv
  rw [hround, hfd]
  intro hA
  have hA' : (ContinuousLinearMap.pi fun i : Fin 3 =>
        ContinuousLinearMap.toSpanSingleton ℝ (![-Real.sin t, Real.cos t, (0 : ℝ)] i)) = 0 := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    have h := congrArg (fun (g : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)) => g v) hA
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at h
    exact toLpCLM_eq_zero h
  have h1 : (ContinuousLinearMap.pi fun i : Fin 3 =>
        ContinuousLinearMap.toSpanSingleton ℝ (![-Real.sin t, Real.cos t, (0 : ℝ)] i)) 1
      = ![-Real.sin t, Real.cos t, (0 : ℝ)] := by
    funext i
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hA'] at h1
  have h2 : (![-Real.sin t, Real.cos t, (0 : ℝ)] : Fin 3 → ℝ) ≠ 0 := by
    intro hz
    have h0 : (-Real.sin t) = 0 := by
      have := congrArg (fun v : Fin 3 → ℝ => v 0) hz; simpa using this
    have h1c : Real.cos t = 0 := by
      have := congrArg (fun v : Fin 3 → ℝ => v 1) hz; simpa using this
    have hsin : Real.sin t = 0 := by linarith
    nlinarith [Real.cos_sq_add_sin_sq t]
  exact h2 h1.symm

/-! ### The two endpoint identities -/

/-- At `s = 0` the rotation is the identity, so it fixes the round picture. -/
private lemma rotX_zero_roundPic (t : ℝ) : rotX 0 (roundPic t) = roundPic t := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i <;> simp [rotX_ofLp, roundPic, Real.cos_zero, Real.sin_zero]

/-- At `s = 1` the rotation is the half-turn `(x, y, z) ↦ (x, -y, -z)`, which reverses the round
picture: `rotX 1 (roundPic t) = roundPic (-t)`. -/
private lemma rotX_one_roundPic (t : ℝ) : rotX 1 (roundPic t) = roundPic (-t) := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i <;>
    simp [rotX_ofLp, roundPic, Real.cos_pi, Real.sin_pi, Real.cos_neg, Real.sin_neg]

end

open scoped Manifold ContDiff Topology in
/-- **The orientation flip of the round planar picture.**

`rotX : ℝ → (ℝ³ →L[ℝ] ℝ³)` (defined in `Submission/Work/Drive/N2/orientationFlipDefs.lean`) is the
rotation about the first coordinate axis by the angle `s * π`, and `roundPic t = (cos t, sin t, 0)`.  The
claim is that this path of rigid motions is a genuine orientation reversal of the round picture:

* every `rotX s` is isometric, and `s ↦ rotX s` is `C^∞`;
* `rotX 0` fixes the picture, while `rotX 1` carries it to the *reversed* parametrisation
  `t ↦ roundPic (-t)`;
* consequently the family `(s, t) ↦ rotX s (roundPic t)` is a smooth isotopy of immersed circle
  embeddings: jointly `C^∞`, each slice injective mod the period, each slice immersive.

The last two clauses are `Work.Drive.N2.rigidMotionPathIsotopy` applied to `c = roundPic`, `v = 0`; that
statement *takes* the period and immersion clauses of `roundPic` as hypotheses, so those must be proved
here (`cos x = cos y ∧ sin x = sin y ⇒ y ≡ x mod 2π` for the period; `(-sin t, cos t, 0) ≠ 0` for the
immersion).  The two endpoint identities are pure `cos 0 / sin 0 / cos π / sin π` computations, and
`ContDiff` of the path may need a smoothness-of-`ContinuousLinearMap.pi` lemma.  Piped through
`Work.Drive.N2.goodDrawingOn_rigidMotion` and `Work.Drive.N2.collarDrawing`, this is the
orientation-reversal collar of the lead's construction. -/
theorem orientationFlipIsotopy :
    (∀ s : ℝ, ∀ y : EuclideanSpace ℝ (Fin 3), ‖Work.Drive.N2.rotX s y‖ = ‖y‖) ∧
      (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Work.Drive.N2.rotX) ∧
      (∀ t : ℝ, Work.Drive.N2.rotX 0 (Work.Drive.N2.roundPic t) = Work.Drive.N2.roundPic t) ∧
      (∀ t : ℝ, Work.Drive.N2.rotX 1 (Work.Drive.N2.roundPic t) = Work.Drive.N2.roundPic (-t)) ∧
      (ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun p : ℝ × ℝ => Work.Drive.N2.rotX p.1 (Work.Drive.N2.roundPic p.2))) ∧
      (∀ s : ℝ, ∀ x y : ℝ,
        Work.Drive.N2.rotX s (Work.Drive.N2.roundPic x)
            = Work.Drive.N2.rotX s (Work.Drive.N2.roundPic y) →
          ∃ k : ℤ, y = x + k * (2 * Real.pi)) ∧
      (∀ s : ℝ, ∀ t : ℝ,
        fderiv ℝ (fun u : ℝ => Work.Drive.N2.rotX s (Work.Drive.N2.roundPic u)) t ≠ 0) := by
  obtain ⟨hjoint, -, hper, himm⟩ :=
    rigidMotionPathIsotopy roundPic roundPic_contMDiff roundPic_period roundPic_immersion
      rotX (fun _ : ℝ => (0 : EuclideanSpace ℝ (Fin 3))) rotX_contDiff contDiff_const rotX_norm
  refine ⟨rotX_norm, rotX_contDiff, rotX_zero_roundPic, rotX_one_roundPic, ?_, ?_, ?_⟩
  · simpa using hjoint
  · exact fun s => hper s
  · intro s t
    have h := himm s t
    have he : (fun u : ℝ => rotX s (roundPic u) + (0 : EuclideanSpace ℝ (Fin 3)))
        = (fun u : ℝ => rotX s (roundPic u)) := by funext u; simp
    rwa [he] at h

end Work.Drive.N2
