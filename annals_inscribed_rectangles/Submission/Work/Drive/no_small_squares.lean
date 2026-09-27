import Mathlib
import Submission.Work.Drive.curve_eq_iff
import Submission.Work.Drive.curve_deriv_ne_zero
import Submission.Work.Drive.MidFig
import Submission.Work.Drive.exists_uniform_local_monotone

/-!
# No small inscribed squares

For a smooth Jordan curve `γ` there is `δ > 0` such that any two chords of `γ`
with a common midpoint, equal Euclidean length and perpendicular doubled directions
`dirC` (i.e. the two diagonals of an inscribed square) have length `≥ δ`.

The proof is local: on a sufficiently short parameter arc of the curve all secants are
nearly parallel (the tangent of a `C¹` curve varies little), while the two diagonals of a
square are perpendicular; and four points of the curve that are close in the plane have
parameter lifts in a short arc because `γ` is an embedding of the compact circle.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold
open Submission.Geometry (eucDot eucNorm)

section Algebra

/-- Cauchy–Schwarz for the Euclidean dot product of `ℝ × ℝ`. -/
lemma nss_eucDot_cauchy (p q : ℝ × ℝ) : |eucDot p q| ≤ eucNorm p * eucNorm q := by
  have h1 : (eucDot p q) ^ 2 ≤ (eucNorm p * eucNorm q) ^ 2 := by
    rw [mul_pow, Submission.Geometry.eucNorm_sq, Submission.Geometry.eucNorm_sq]
    simp only [eucDot]
    nlinarith [sq_nonneg (p.1 * q.2 - p.2 * q.1)]
  have h2 : 0 ≤ eucNorm p * eucNorm q :=
    mul_nonneg (Submission.Geometry.eucNorm_nonneg p) (Submission.Geometry.eucNorm_nonneg q)
  nlinarith [abs_nonneg (eucDot p q), sq_abs (eucDot p q),
    sq_nonneg (eucNorm p * eucNorm q), h1, h2]

/-- The default (sup) norm on `ℝ × ℝ` is dominated by the Euclidean norm. -/
lemma nss_norm_le_eucNorm (p : ℝ × ℝ) : ‖p‖ ≤ eucNorm p := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hp : eucNorm p = Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
    rw [eucNorm, Submission.Geometry.eucDot_self]
  rw [hp, max_le_iff]
  constructor
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg p.2])
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg p.1])

/-- A vector is orthogonal to its right-angle rotation. -/
lemma nss_eucDot_rot90_self (e : ℝ × ℝ) : eucDot e (rot90 e) = 0 := by
  simp only [eucDot, rot90]
  ring

/-- Expansion of the dot product in the orthogonal basis `e`, `rot90 e`. -/
lemma nss_eucDot_orthonormal_expand (e p q : ℝ × ℝ) :
    eucDot p q * eucDot e e
      = eucDot p e * eucDot q e + eucDot p (rot90 e) * eucDot q (rot90 e) := by
  simp only [eucDot, rot90]
  ring

lemma nss_eucDot_sub_left (p q r : ℝ × ℝ) : eucDot (p - q) r = eucDot p r - eucDot q r := by
  simp only [eucDot, Prod.fst_sub, Prod.snd_sub]
  ring

lemma nss_eucDot_sub_right (p q r : ℝ × ℝ) : eucDot p (q - r) = eucDot p q - eucDot p r := by
  simp only [eucDot, Prod.fst_sub, Prod.snd_sub]
  ring

end Algebra

section MVT

/-- Mean value inequality, lower bound form: if `deriv φ ≥ c` on `[s,t]` then the increment of `φ`
is at least `c (t - s)`. -/
lemma nss_mul_sub_le_sub_of_le_deriv {φ : ℝ → ℝ} {s t c : ℝ} (hst : s ≤ t)
    (hcont : ContinuousOn φ (Set.Icc s t))
    (hdiff : ∀ u ∈ Set.Icc s t, DifferentiableAt ℝ φ u)
    (hderiv : ∀ u ∈ Set.Ico s t, c ≤ deriv φ u) : c * (t - s) ≤ φ t - φ s := by
  have hgcont : ContinuousOn (fun u : ℝ => c * u - φ u) (Set.Icc s t) :=
    (continuousOn_const.mul continuousOn_id).sub hcont
  have hg' : ∀ u ∈ Set.Ico s t,
      HasDerivWithinAt (fun u : ℝ => c * u - φ u) (c - deriv φ u) (Set.Ici u) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => c * u) c u := by
      simpa using (hasDerivAt_id u).const_mul c
    exact (h1.sub (hdiff u (Set.Ico_subset_Icc_self hu)).hasDerivAt).hasDerivWithinAt
  have hle := image_le_of_deriv_right_le_deriv_boundary (f := fun u : ℝ => c * u - φ u)
    (f' := fun u => c - deriv φ u) (a := s) (b := t)
    (B := fun _ : ℝ => c * s - φ s) (B' := fun _ : ℝ => 0) hgcont hg' (le_refl _)
    continuousOn_const (fun u _ => (hasDerivAt_const u (c * s - φ s)).hasDerivWithinAt)
    (fun u hu => by linarith [hderiv u hu])
  have ht := hle (show t ∈ Set.Icc s t from ⟨hst, le_refl t⟩)
  linarith

/-- Mean value inequality, upper bound form: if `|deriv φ| ≤ C` on `[s,t]` then `φ` is
`C`-Lipschitz on `[s,t]`. -/
lemma nss_abs_sub_le_of_abs_deriv_le {φ : ℝ → ℝ} {s t C : ℝ} (hst : s ≤ t)
    (hdiff : ∀ u ∈ Set.Icc s t, DifferentiableAt ℝ φ u) (hC : 0 ≤ C)
    (hderiv : ∀ u ∈ Set.Ico s t, |deriv φ u| ≤ C) : |φ t - φ s| ≤ C * (t - s) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (f' := fun u => deriv φ u)
    (a := s) (b := t) (C := C)
    (fun u hu => (hdiff u hu).hasDerivAt.hasDerivWithinAt)
    (fun u hu => by simpa [Real.norm_eq_abs] using hderiv u hu)
    t ⟨hst, le_refl t⟩
  simpa [Real.norm_eq_abs] using h

end MVT

section Local

variable {γ : Circle → ℝ × ℝ}

/-- The plane curve `t ↦ γ (Circle.exp t)` of a smooth embedded closed curve is `C¹`. -/
lemma nss_contDiff_one_curve
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ 1 (curve γ) :=
  (hγ.contMDiff.comp contMDiff_circleExp).contDiff.of_le (by simp)

lemma nss_continuous_eucNorm : Continuous (fun p : ℝ × ℝ => eucNorm p) := by
  have h : (fun p : ℝ × ℝ => eucNorm p)
      = fun p : ℝ × ℝ => Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
    funext p
    rw [eucNorm, Submission.Geometry.eucDot_self]
  rw [h]
  fun_prop

/-- The coordinate function `u ↦ ⟪curve γ u, e⟫` along the curve is differentiable. -/
lemma nss_differentiableAt_eucDot_curve {c : ℝ → ℝ × ℝ} (hc : ContDiff ℝ 1 c) (e : ℝ × ℝ)
    (u : ℝ) : DifferentiableAt ℝ (fun x => eucDot (c x) e) u := by
  have hd : DifferentiableAt ℝ c u := (hc.differentiable (by simp)).differentiableAt
  have hfun : (fun x => eucDot (c x) e) = (eucLinFun e) ∘ c := by
    funext x
    exact (eucLinFun_eq_eucDot e (c x)).symm
  rw [hfun]
  exact ((eucLinFun e).differentiableAt).comp u hd

lemma nss_continuousOn_eucDot_curve {c : ℝ → ℝ × ℝ} (hc : ContDiff ℝ 1 c) (e : ℝ × ℝ) (s t : ℝ) :
    ContinuousOn (fun x => eucDot (c x) e) (Set.Icc s t) :=
  fun u _ => (nss_differentiableAt_eucDot_curve hc e u).continuousAt.continuousWithinAt

/-- **Local bounds on the derivative.**  At every parameter `a` the derivative `deriv (curve γ) a`
is nonzero, and on a neighbourhood of `a` the derivative stays close to it: with
`E = eucNorm (deriv (curve γ) a)`, its component along `deriv (curve γ) a` is `≥ (15/16) E²` and its
component along the perpendicular `rot90 (deriv (curve γ) a)` has absolute value `≤ (1/16) E²`. -/
lemma nss_exists_local_deriv_bounds
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (a : ℝ) :
    ∃ δ > 0, ∀ u : ℝ, |u - a| < δ →
      (15 / 16) * eucNorm (deriv (curve γ) a) ^ 2
          ≤ eucDot (deriv (curve γ) u) (deriv (curve γ) a) ∧
      |eucDot (deriv (curve γ) u) (rot90 (deriv (curve γ) a))|
          ≤ (1 / 16) * eucNorm (deriv (curve γ) a) ^ 2 := by
  have hC1 : ContDiff ℝ 1 (curve γ) := nss_contDiff_one_curve hγ
  have hcont : Continuous (deriv (curve γ)) := hC1.continuous_deriv (by simp)
  have hne : deriv (curve γ) a ≠ 0 := curve_deriv_ne_zero γ hγ a
  have hE : 0 < eucNorm (deriv (curve γ) a) := Submission.Geometry.eucNorm_pos hne
  set E : ℝ := eucNorm (deriv (curve γ) a) with hEdef
  have hg : ContinuousAt (fun u : ℝ => eucNorm (deriv (curve γ) u - deriv (curve γ) a)) a :=
    (nss_continuous_eucNorm.comp (hcont.sub continuous_const)).continuousAt
  have hg0 : eucNorm (deriv (curve γ) a - deriv (curve γ) a) = 0 := by
    rw [sub_self, Submission.Geometry.eucNorm_eq_zero]
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hg (E / 16) (by linarith)
  refine ⟨δ, hδpos, fun u hu => ?_⟩
  have hdu : dist u a < δ := by rw [Real.dist_eq]; exact hu
  have hsmall : eucNorm (deriv (curve γ) u - deriv (curve γ) a) < E / 16 := by
    have h := hδ (x := u) hdu
    rwa [Real.dist_eq, hg0, sub_zero, abs_of_nonneg (Submission.Geometry.eucNorm_nonneg _)] at h
  have hEe : eucDot (deriv (curve γ) a) (deriv (curve γ) a) = E ^ 2 := by
    rw [← Submission.Geometry.eucNorm_sq, hEdef]
  have hsplit : eucDot (deriv (curve γ) u) (deriv (curve γ) a)
      = eucDot (deriv (curve γ) u - deriv (curve γ) a) (deriv (curve γ) a)
        + E ^ 2 := by
    rw [nss_eucDot_sub_left, hEe]
    ring
  have hcs : |eucDot (deriv (curve γ) u - deriv (curve γ) a) (deriv (curve γ) a)|
      ≤ eucNorm (deriv (curve γ) u - deriv (curve γ) a) * E := by
    simpa [hEdef] using
      nss_eucDot_cauchy (deriv (curve γ) u - deriv (curve γ) a) (deriv (curve γ) a)
  have hcs2 : -(eucNorm (deriv (curve γ) u - deriv (curve γ) a) * E)
      ≤ eucDot (deriv (curve γ) u - deriv (curve γ) a) (deriv (curve γ) a) := by
    have := neg_le_of_abs_le hcs
    linarith
  have hcs3 : (eucNorm (deriv (curve γ) u - deriv (curve γ) a) * E) < E ^ 2 / 16 := by
    nlinarith [hsmall, hE, hEdef]
  constructor
  · rw [hsplit]
    nlinarith [hcs2, hcs3]
  · have hsplit2 : eucDot (deriv (curve γ) u) (rot90 (deriv (curve γ) a))
        = eucDot (deriv (curve γ) u - deriv (curve γ) a) (rot90 (deriv (curve γ) a))
          + eucDot (deriv (curve γ) a) (rot90 (deriv (curve γ) a)) := by
      rw [nss_eucDot_sub_left]
      ring
    have hzero : eucDot (deriv (curve γ) a) (rot90 (deriv (curve γ) a)) = 0 :=
      nss_eucDot_rot90_self _
    rw [hsplit2, hzero, add_zero]
    have hcs4 : |eucDot (deriv (curve γ) u - deriv (curve γ) a) (rot90 (deriv (curve γ) a))|
        ≤ eucNorm (deriv (curve γ) u - deriv (curve γ) a) * E := by
      have h := nss_eucDot_cauchy (deriv (curve γ) u - deriv (curve γ) a)
        (rot90 (deriv (curve γ) a))
      rw [eucNorm_rot90] at h
      simpa [hEdef] using h
    calc |eucDot (deriv (curve γ) u - deriv (curve γ) a) (rot90 (deriv (curve γ) a))|
        ≤ eucNorm (deriv (curve γ) u - deriv (curve γ) a) * E := hcs4
      _ ≤ E ^ 2 / 16 := le_of_lt hcs3
      _ = (1 / 16) * E ^ 2 := by ring

end Local

section LocalSecant

variable {γ : Circle → ℝ × ℝ}

/-- **Local secant parallelism.**  On a sufficiently short parameter arc around a point `a` any two
secants of the curve have positive inner product, so in particular no two secants of that arc are
perpendicular: the tangent of a `C¹` curve varies little on a short arc, and every secant is close to
the tangent.

The proof uses the local derivative bounds `nss_exists_local_deriv_bounds`: with `e` the tangent at `a`
and `c = eucNorm e`, on the arc the projection of the derivative on `e` is `≥ (15/16) c²` and on
`rot90 e` at most `(1/16) c²` in absolute value; integrating (the mean value inequalities
`nss_mul_sub_le_sub_of_le_deriv`, `nss_abs_sub_le_of_abs_deriv_le`) bounds the two components of every
secant, and the orthogonal-basis expansion `nss_eucDot_orthonormal_expand` then gives positivity of the
inner product of two of them. -/
lemma nss_exists_local_secant_pos
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (a : ℝ) :
    ∃ δ > 0, ∀ s t s' t' : ℝ, a - δ < s → s < t → t < a + δ →
      a - δ < s' → s' < t' → t' < a + δ →
      curve γ s ≠ curve γ t → curve γ s' ≠ curve γ t' →
      0 < eucDot (curve γ t - curve γ s) (curve γ t' - curve γ s') := by
  have hC1 : ContDiff ℝ 1 (curve γ) := nss_contDiff_one_curve hγ
  obtain ⟨δ, hδpos, hδ⟩ := nss_exists_local_deriv_bounds hγ a
  refine ⟨δ, hδpos, ?_⟩
  intro s t s' t' hs ht ht' hs' hs'' ht'' _ _
  set e : ℝ × ℝ := deriv (curve γ) a with he
  have hbnd : ∀ u : ℝ, s ≤ u → u ≤ t → |u - a| < δ := by
    intro u h1 h2
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hbnd' : ∀ u : ℝ, s' ≤ u → u ≤ t' → |u - a| < δ := by
    intro u h1 h2
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  -- derivative bounds along the two parameter intervals
  have hderA : ∀ u ∈ Set.Ico s t, (15 / 16) * eucNorm e ^ 2
      ≤ deriv (fun x => eucDot (curve γ x) e) u := by
    intro u hu
    rw [deriv_eucDot_curve_const hC1 e u, he]
    exact (hδ u (hbnd u hu.1 (le_of_lt hu.2))).1
  have hderB : ∀ u ∈ Set.Ico s t, |deriv (fun x => eucDot (curve γ x) (rot90 e)) u|
      ≤ (1 / 16) * eucNorm e ^ 2 := by
    intro u hu
    rw [deriv_eucDot_curve_const hC1 (rot90 e) u, he]
    exact (hδ u (hbnd u hu.1 (le_of_lt hu.2))).2
  have hderA' : ∀ u ∈ Set.Ico s' t', (15 / 16) * eucNorm e ^ 2
      ≤ deriv (fun x => eucDot (curve γ x) e) u := by
    intro u hu
    rw [deriv_eucDot_curve_const hC1 e u, he]
    exact (hδ u (hbnd' u hu.1 (le_of_lt hu.2))).1
  have hderB' : ∀ u ∈ Set.Ico s' t', |deriv (fun x => eucDot (curve γ x) (rot90 e)) u|
      ≤ (1 / 16) * eucNorm e ^ 2 := by
    intro u hu
    rw [deriv_eucDot_curve_const hC1 (rot90 e) u, he]
    exact (hδ u (hbnd' u hu.1 (le_of_lt hu.2))).2
  -- mean value inequalities
  have hA1 := nss_mul_sub_le_sub_of_le_deriv (le_of_lt ht)
    (nss_continuousOn_eucDot_curve hC1 e s t)
    (fun u _ => nss_differentiableAt_eucDot_curve hC1 e u) hderA
  have hB1 := nss_abs_sub_le_of_abs_deriv_le (le_of_lt ht)
    (fun u _ => nss_differentiableAt_eucDot_curve hC1 (rot90 e) u) (by positivity) hderB
  have hA2 := nss_mul_sub_le_sub_of_le_deriv (le_of_lt hs'')
    (nss_continuousOn_eucDot_curve hC1 e s' t')
    (fun u _ => nss_differentiableAt_eucDot_curve hC1 e u) hderA'
  have hB2 := nss_abs_sub_le_of_abs_deriv_le (le_of_lt hs'')
    (fun u _ => nss_differentiableAt_eucDot_curve hC1 (rot90 e) u) (by positivity) hderB'
  -- translate to the secants
  have hX1 : (15 / 16) * eucNorm e ^ 2 * (t - s) ≤ eucDot (curve γ t - curve γ s) e := by
    rw [nss_eucDot_sub_left]
    linarith
  have hU1 : |eucDot (curve γ t - curve γ s) (rot90 e)| ≤ (1 / 16) * eucNorm e ^ 2 * (t - s) := by
    rw [nss_eucDot_sub_left]
    linarith
  have hX2 : (15 / 16) * eucNorm e ^ 2 * (t' - s') ≤ eucDot (curve γ t' - curve γ s') e := by
    rw [nss_eucDot_sub_left]
    linarith
  have hU2 : |eucDot (curve γ t' - curve γ s') (rot90 e)| ≤ (1 / 16) * eucNorm e ^ 2 * (t' - s') := by
    rw [nss_eucDot_sub_left]
    linarith
  -- the norm of the tangent at `a` is positive
  have hc : 0 < eucNorm e := by
    rw [he]
    exact Submission.Geometry.eucNorm_pos (curve_deriv_ne_zero γ hγ a)
  have hts : 0 < t - s := sub_pos.mpr ht
  have hts' : 0 < t' - s' := sub_pos.mpr hs''
  set c : ℝ := eucNorm e with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact hc
  have hX1' : (15 / 16) * c ^ 2 * (t - s) ≤ eucDot (curve γ t - curve γ s) e := by
    rw [hcdef]; exact hX1
  have hU1' : |eucDot (curve γ t - curve γ s) (rot90 e)| ≤ (1 / 16) * c ^ 2 * (t - s) := by
    rw [hcdef]; exact hU1
  have hX2' : (15 / 16) * c ^ 2 * (t' - s') ≤ eucDot (curve γ t' - curve γ s') e := by
    rw [hcdef]; exact hX2
  have hU2' : |eucDot (curve γ t' - curve γ s') (rot90 e)| ≤ (1 / 16) * c ^ 2 * (t' - s') := by
    rw [hcdef]; exact hU2
  -- the key identity and the two products
  have hexp := nss_eucDot_orthonormal_expand e (curve γ t - curve γ s) (curve γ t' - curve γ s')
  have hee : eucDot e e = c ^ 2 := by
    rw [hcdef, ← Submission.Geometry.eucNorm_sq]
  rw [hee] at hexp
  have hXY : (15 / 16) * c ^ 2 * (t - s) * ((15 / 16) * c ^ 2 * (t' - s'))
      ≤ eucDot (curve γ t - curve γ s) e * eucDot (curve γ t' - curve γ s') e := by
    refine mul_le_mul hX1' hX2' ?_ ?_
    · have : 0 < (15 / 16 : ℝ) * c ^ 2 * (t' - s') := by positivity
      exact le_of_lt this
    · linarith [hX1', mul_pos (by positivity : (0:ℝ) < (15/16) * c^2) hts]
  have hUV : -((1 / 16) * c ^ 2 * (t - s) * ((1 / 16) * c ^ 2 * (t' - s')))
      ≤ eucDot (curve γ t - curve γ s) (rot90 e) * eucDot (curve γ t' - curve γ s') (rot90 e) := by
    have h1 : -(|eucDot (curve γ t - curve γ s) (rot90 e)|
        * |eucDot (curve γ t' - curve γ s') (rot90 e)|)
        ≤ eucDot (curve γ t - curve γ s) (rot90 e) * eucDot (curve γ t' - curve γ s') (rot90 e) := by
      have := neg_abs_le (eucDot (curve γ t - curve γ s) (rot90 e)
        * eucDot (curve γ t' - curve γ s') (rot90 e))
      rwa [abs_mul] at this
    have h2 : |eucDot (curve γ t - curve γ s) (rot90 e)|
        * |eucDot (curve γ t' - curve γ s') (rot90 e)|
        ≤ (1 / 16) * c ^ 2 * (t - s) * ((1 / 16) * c ^ 2 * (t' - s')) := by
      refine mul_le_mul hU1' hU2' (abs_nonneg _) ?_
      have : 0 < (1 / 16 : ℝ) * c ^ 2 * (t - s) := by positivity
      exact le_of_lt this
    linarith
  have hsum : (15 / 16) * c ^ 2 * (t - s) * ((15 / 16) * c ^ 2 * (t' - s'))
      - (1 / 16) * c ^ 2 * (t - s) * ((1 / 16) * c ^ 2 * (t' - s'))
      ≤ eucDot (curve γ t - curve γ s) (curve γ t' - curve γ s') * c ^ 2 := by
    rw [hexp]
    linarith
  have hpos : 0 < (15 / 16) * c ^ 2 * (t - s) * ((15 / 16) * c ^ 2 * (t' - s'))
      - (1 / 16) * c ^ 2 * (t - s) * ((1 / 16) * c ^ 2 * (t' - s')) := by
    have hrew : (15 / 16) * c ^ 2 * (t - s) * ((15 / 16) * c ^ 2 * (t' - s'))
        - (1 / 16) * c ^ 2 * (t - s) * ((1 / 16) * c ^ 2 * (t' - s'))
        = c ^ 4 * ((t - s) * (t' - s')) * ((15 / 16 : ℝ) ^ 2 - (1 / 16 : ℝ) ^ 2) := by
      ring
    rw [hrew]
    have h1 : 0 < c ^ 4 * ((t - s) * (t' - s')) := by positivity
    have h2 : 0 < (15 / 16 : ℝ) ^ 2 - (1 / 16 : ℝ) ^ 2 := by norm_num
    positivity
  have hfin : 0 < eucDot (curve γ t - curve γ s) (curve γ t' - curve γ s') * c ^ 2 :=
    lt_of_lt_of_le hpos hsum
  have hc2 : (0 : ℝ) < c ^ 2 := pow_pos hcpos 2
  exact pos_of_mul_pos_left hfin (le_of_lt hc2)

end LocalSecant

section UniformSecant

variable {γ : Circle → ℝ × ℝ}

/-- **Uniform secant parallelism.**  There is `η > 0` such that any two secants of the curve whose
four parameters lie in a common interval of length `≤ η` have positive inner product (hence are not
perpendicular).

This is the uniform version of `nss_exists_local_secant_pos`, obtained by the Lebesgue number of the
cover of `[0, 4π]` by the local intervals `(a - δ a, a + δ a)`; the curve is `2π`-periodic, so the
statement for `[0, 4π]` transfers to all of `ℝ`. -/
lemma nss_exists_uniform_secant_pos
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ η > 0, ∀ a s t s' t' : ℝ, a ≤ s → s < t → t ≤ a + η → a ≤ s' → s' < t' → t' ≤ a + η →
      curve γ s ≠ curve γ t → curve γ s' ≠ curve γ t' →
      0 < eucDot (curve γ t - curve γ s) (curve γ t' - curve γ s') := by
  choose δ hδ using fun a : ℝ => nss_exists_local_secant_pos hγ a
  have hδpos : ∀ a : ℝ, 0 < δ a := fun a => (hδ a).1
  have hδprop : ∀ a s t s' t' : ℝ, a - δ a < s → s < t → t < a + δ a →
      a - δ a < s' → s' < t' → t' < a + δ a →
      curve γ s ≠ curve γ t → curve γ s' ≠ curve γ t' →
      0 < eucDot (curve γ t - curve γ s) (curve γ t' - curve γ s') := fun a => (hδ a).2
  have hcover : Set.Icc (0 : ℝ) (4 * Real.pi) ⊆ ⋃ a : ℝ, Set.Ioo (a - δ a) (a + δ a) := by
    intro u _
    exact Set.mem_iUnion.mpr ⟨u, ⟨by linarith [hδpos u], by linarith [hδpos u]⟩⟩
  obtain ⟨L, hLpos, hL⟩ :=
    lebesgue_number_lemma_of_metric isCompact_Icc (fun _ : ℝ => isOpen_Ioo) hcover
  refine ⟨min (L / 2) Real.pi, lt_min (by linarith) Real.pi_pos, ?_⟩
  intro a s t s' t' has hat ht' has' hat' ht'' hne1 hne2
  have hηL : min (L / 2) Real.pi ≤ L / 2 := min_le_left _ _
  have hηπ : min L Real.pi ≤ Real.pi := min_le_right _ _
  -- shift the window into `[0, 4π]`
  set k : ℤ := ⌊a / (2 * Real.pi)⌋ with hk
  have hper : Function.Periodic (curve γ) (2 * Real.pi) := curve_periodic γ
  have hper_sub : ∀ x : ℝ, curve γ (x - (k : ℝ) * (2 * Real.pi)) = curve γ x := by
    intro x
    have h := (hper.int_mul k) (x - (k : ℝ) * (2 * Real.pi))
    have hx : x - (k : ℝ) * (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) = x := by ring
    rw [hx] at h
    exact h.symm
  have hk_le : (k : ℝ) * (2 * Real.pi) ≤ a := by
    have h1 : (k : ℝ) ≤ a / (2 * Real.pi) := by rw [hk]; exact Int.floor_le _
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
  have hk_gt : a < (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
    have h1 : a / (2 * Real.pi) < (k : ℝ) + 1 := by rw [hk]; exact Int.lt_floor_add_one _
    have h2 : a < ((k : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
    linarith
  set a₀ : ℝ := a - (k : ℝ) * (2 * Real.pi) with ha₀
  have ha₀_nonneg : 0 ≤ a₀ := by rw [ha₀]; linarith
  have ha₀_lt : a₀ < 2 * Real.pi := by rw [ha₀]; linarith
  have ha₀_le : a₀ ≤ 4 * Real.pi := by linarith [Real.pi_pos]
  obtain ⟨i, hi⟩ := hL a₀ ⟨ha₀_nonneg, ha₀_le⟩
  have hball : ∀ u : ℝ, a ≤ u → u ≤ a + min (L / 2) Real.pi →
      u - (k : ℝ) * (2 * Real.pi) ∈ Metric.ball a₀ L := by
    intro u hu1 hu2
    have h1 : u - (k : ℝ) * (2 * Real.pi) - a₀ = u - a := by rw [ha₀]; ring
    have hu : u - a ≤ min (L / 2) Real.pi := by linarith
    rw [Metric.mem_ball, Real.dist_eq, h1, abs_lt]
    constructor
    · linarith
    · linarith [hηL, hLpos]
  have hs_in : i - δ i < s - (k : ℝ) * (2 * Real.pi) :=
    (hi (hball s has (by linarith))).1
  have ht_in : t - (k : ℝ) * (2 * Real.pi) < i + δ i :=
    (hi (hball t (by linarith) (by linarith))).2
  have hs'_in : i - δ i < s' - (k : ℝ) * (2 * Real.pi) :=
    (hi (hball s' has' (by linarith))).1
  have ht'_in : t' - (k : ℝ) * (2 * Real.pi) < i + δ i :=
    (hi (hball t' (by linarith) (by linarith))).2
  have hmain := hδprop i (s - (k : ℝ) * (2 * Real.pi)) (t - (k : ℝ) * (2 * Real.pi))
    (s' - (k : ℝ) * (2 * Real.pi)) (t' - (k : ℝ) * (2 * Real.pi))
    hs_in (by linarith) ht_in hs'_in (by linarith) ht'_in
    (by simpa [hper_sub] using hne1) (by simpa [hper_sub] using hne2)
  simpa [hper_sub] using hmain

end UniformSecant

section CircleLift

set_option backward.isDefEq.respectTransparency false

/-- `|sin x| = sin |x|` for `|x| ≤ π/2`. -/
lemma nss_abs_sin_eq_sin_abs_of_abs_le_pi_div_two {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    |Real.sin x| = Real.sin |x| := by
  rcases lt_or_ge x 0 with h | h
  · have hx' : -Real.pi < x := by
      have := abs_of_neg h ▸ hx; linarith [Real.pi_pos]
    rw [abs_of_neg h, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h hx'), Real.sin_neg]
  · have hxπ : x ≤ Real.pi := by
      have := abs_of_nonneg h ▸ hx; linarith [Real.pi_pos]
    rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h hxπ)]

/-- The chord distance between `1` and `exp (θ i)` on the unit circle is `2 |sin (θ/2)|`. -/
lemma nss_norm_one_sub_exp (θ : ℝ) :
    ‖(1 : ℂ) - (Circle.exp θ : ℂ)‖ = 2 * |Real.sin (θ / 2)| := by
  have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (θ / 2)
    have h2 : 2 * (θ / 2) = θ := by ring
    rwa [h2] at this
  have hsq : ‖(1 : ℂ) - (Circle.exp θ : ℂ)‖ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [Circle.coe_exp, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [hcos, Real.sin_sq θ, Real.sin_sq (θ / 2), sq_abs (Real.sin (θ / 2))]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_sq (by positivity)]

/-- **Lifts of nearby points of the circle lie in a short window.**  If two points of the unit
circle are at chord distance `< δ = 2 sin (η/2)`, then any two parameter lifts of them differ, after
a `2π`-shift, by at most `η`. -/
lemma nss_exists_int_shift_le (η : ℝ) (hη0 : 0 < η) (hηπ : η ≤ Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x y : Circle) (s t : ℝ), Circle.exp s = x → Circle.exp t = y →
      dist x y < δ → ∃ k : ℤ, |t + 2 * Real.pi * k - s| ≤ η := by
  refine ⟨2 * Real.sin (η / 2), mul_pos (by norm_num)
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])), ?_⟩
  intro x y s t hsx hty hdist
  have hnorm : dist x y = ‖(1 : ℂ) - ((y / x : Circle) : ℂ)‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
    have hfac : (x : ℂ) - (y : ℂ) = (x : ℂ) * (1 - ((y / x : Circle) : ℂ)) := by
      rw [Circle.coe_div]
      field_simp
    rw [hfac, norm_mul, Circle.norm_coe, one_mul]
  have hexpw : Circle.exp (Complex.arg ((y / x : Circle) : ℂ)) = y / x :=
    Circle.exp_arg (y / x)
  have hexp_sum : Circle.exp (s + Complex.arg ((y / x : Circle) : ℂ)) = y := by
    rw [Circle.exp_add, hsx, hexpw, ← mul_div_assoc, mul_div_cancel_left]
  have hle : |Complex.arg ((y / x : Circle) : ℂ)| ≤ η := by
    have hwnorm : ‖(1 : ℂ) - ((y / x : Circle) : ℂ)‖
        = 2 * |Real.sin (Complex.arg ((y / x : Circle) : ℂ) / 2)| := by
      conv_lhs => rw [← hexpw]
      exact nss_norm_one_sub_exp _
    have h2 : 2 * |Real.sin (Complex.arg ((y / x : Circle) : ℂ) / 2)| <
        2 * Real.sin (η / 2) := by
      rw [← hwnorm, ← hnorm]
      exact hdist
    have h3 : |Real.sin (Complex.arg ((y / x : Circle) : ℂ) / 2)| < Real.sin (η / 2) := by
      linarith
    set ψ : ℝ := Complex.arg ((y / x : Circle) : ℂ) / 2 with hψdef
    have hψb : |ψ| ≤ Real.pi / 2 := by
      have h1 : |Complex.arg ((y / x : Circle) : ℂ)| ≤ Real.pi :=
        abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
      have h2 : |ψ| = |Complex.arg ((y / x : Circle) : ℂ)| / 2 := by
        rw [hψdef, abs_div]
        norm_num
      rw [h2]; linarith
    have habs : |Real.sin ψ| = Real.sin |ψ| := nss_abs_sin_eq_sin_abs_of_abs_le_pi_div_two hψb
    have h4 : Real.sin |ψ| < Real.sin (η / 2) := by rw [← habs]; exact h3
    have h5 : |ψ| < η / 2 :=
      (Real.strictMonoOn_sin.lt_iff_lt
        ⟨by have := abs_nonneg ψ; linarith [Real.pi_pos], hψb⟩
        ⟨by linarith [hη0, Real.pi_pos], by linarith [hηπ]⟩).mp h4
    have h7 : |Complex.arg ((y / x : Circle) : ℂ)| / 2 < η / 2 := by
      simpa [hψdef, abs_div] using h5
    linarith [abs_nonneg (Complex.arg ((y / x : Circle) : ℂ))]
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (hexp_sum.trans hty.symm)
  refine ⟨m, ?_⟩
  have hθeq : Complex.arg ((y / x : Circle) : ℂ) = t + (m : ℝ) * (2 * Real.pi) - s := by
    linarith
  have hgoal : t + 2 * Real.pi * (m : ℝ) - s = Complex.arg ((y / x : Circle) : ℂ) := by
    rw [hθeq]; ring
  rw [hgoal]
  exact hle

/-- **The inverse of `γ` is uniformly continuous on the compact circle.**  (Only continuity and
injectivity of `γ` are used.) -/
lemma nss_exists_dist_lt_of_curve_dist_lt (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : Circle, dist (γ x) (γ y) < δ → dist x y < ε := by
  by_cases h : ∃ x y : Circle, ε ≤ dist x y
  · obtain ⟨x₀, y₀, hxy₀⟩ := h
    set S : Set (Circle × Circle) := {p | ε ≤ dist p.1 p.2} with hS
    have hclosed : IsClosed S := by
      rw [hS]; exact isClosed_le continuous_const continuous_dist
    have hne : S.Nonempty := ⟨(x₀, y₀), hxy₀⟩
    have hcont : Continuous (fun p : Circle × Circle => dist (γ p.1) (γ p.2)) :=
      (hγ.contMDiff.continuous.comp continuous_fst).dist
        (hγ.contMDiff.continuous.comp continuous_snd)
    obtain ⟨p, hpS, hpmin⟩ := hclosed.isCompact.exists_isMinOn hne hcont.continuousOn
    have hpmin' : ∀ q ∈ S, dist (γ p.1) (γ p.2) ≤ dist (γ q.1) (γ q.2) :=
      (isMinOn_iff.mp hpmin)
    have hpos : 0 < dist (γ p.1) (γ p.2) := by
      have hne' : p.1 ≠ p.2 := by
        intro heq
        have h1 : ε ≤ dist p.1 p.2 := hpS
        rw [heq, dist_self] at h1
        linarith
      exact dist_pos.mpr (fun hh => hne' (hγ.isEmbedding.injective hh))
    refine ⟨dist (γ p.1) (γ p.2), hpos, fun x y hxy => ?_⟩
    by_contra hcon
    rw [not_lt] at hcon
    have hmem : (x, y) ∈ S := by rw [hS]; exact hcon
    have := hpmin' (x, y) hmem
    linarith [hxy, this]
  · push Not at h
    exact ⟨1, one_pos, fun x y _ => by linarith [h x y]⟩

end CircleLift

section Geometry2

/-- `eucNorm` is invariant under negation. -/
lemma nss_eucNorm_neg (w : ℝ × ℝ) : eucNorm (-w) = eucNorm w := by
  have h : (-w : ℝ × ℝ) = (-1 : ℝ) • w := by simp
  rw [h, Submission.Configuration.eucNorm_smul]
  norm_num

lemma nss_eucDot_neg_left (a b : ℝ × ℝ) : eucDot (-a) b = -eucDot a b := by
  simp only [eucDot, Prod.fst_neg, Prod.snd_neg]; ring

lemma nss_eucDot_neg_right (a b : ℝ × ℝ) : eucDot a (-b) = -eucDot a b := by
  simp only [eucDot, Prod.fst_neg, Prod.snd_neg]; ring

lemma nss_eucDot_neg_neg (a b : ℝ × ℝ) : eucDot (-a) (-b) = eucDot a b := by
  rw [nss_eucDot_neg_left, nss_eucDot_neg_right, neg_neg]

lemma nss_eucNorm_sub_sq (a b : ℝ × ℝ) :
    eucNorm (a - b) ^ 2 = eucNorm a ^ 2 + eucNorm b ^ 2 - 2 * eucDot a b := by
  rw [Submission.Geometry.eucNorm_sq, Submission.Geometry.eucNorm_sq, Submission.Geometry.eucNorm_sq]
  simp only [eucDot, Prod.fst_sub, Prod.snd_sub]
  ring

lemma nss_eucNorm_add_sq (a b : ℝ × ℝ) :
    eucNorm (a + b) ^ 2 = eucNorm a ^ 2 + eucNorm b ^ 2 + 2 * eucDot a b := by
  rw [Submission.Geometry.eucNorm_sq, Submission.Geometry.eucNorm_sq, Submission.Geometry.eucNorm_sq]
  simp only [eucDot, Prod.fst_add, Prod.snd_add]
  ring

/-- Two perpendicular vectors of equal length have half-difference of length at most that length. -/
lemma nss_eucNorm_half_sub_le {U V : ℝ × ℝ} (hperp : eucDot U V = 0)
    (hUV : eucNorm U = eucNorm V) :
    eucNorm ((1/2 : ℝ) • (U - V)) ≤ eucNorm U := by
  have h1 : eucNorm ((1/2 : ℝ) • (U - V)) = eucNorm (U - V) / 2 := by
    rw [Submission.Configuration.eucNorm_smul]
    norm_num
    ring
  have h2 : eucNorm (U - V) ^ 2 = 2 * eucNorm U ^ 2 := by
    rw [nss_eucNorm_sub_sq, hUV, hperp]
    ring
  have h3 : eucNorm ((1/2 : ℝ) • (U - V)) ^ 2 ≤ eucNorm U ^ 2 := by
    rw [h1, div_pow, h2]
    nlinarith [Submission.Geometry.eucNorm_nonneg U]
  have h4 := sq_le_sq.mp h3
  rwa [abs_of_nonneg (Submission.Geometry.eucNorm_nonneg _),
    abs_of_nonneg (Submission.Geometry.eucNorm_nonneg U)] at h4

/-- Two perpendicular vectors of equal length have half-sum of length at most that length. -/
lemma nss_eucNorm_half_add_le {U V : ℝ × ℝ} (hperp : eucDot U V = 0)
    (hUV : eucNorm U = eucNorm V) :
    eucNorm ((1/2 : ℝ) • (U + V)) ≤ eucNorm U := by
  have h1 : eucNorm ((1/2 : ℝ) • (U + V)) = eucNorm (U + V) / 2 := by
    rw [Submission.Configuration.eucNorm_smul]
    norm_num
    ring
  have h2 : eucNorm (U + V) ^ 2 = 2 * eucNorm U ^ 2 := by
    rw [nss_eucNorm_add_sq, hUV, hperp]
    ring
  have h3 : eucNorm ((1/2 : ℝ) • (U + V)) ^ 2 ≤ eucNorm U ^ 2 := by
    rw [h1, div_pow, h2]
    nlinarith [Submission.Geometry.eucNorm_nonneg U]
  have h4 := sq_le_sq.mp h3
  rwa [abs_of_nonneg (Submission.Geometry.eucNorm_nonneg _),
    abs_of_nonneg (Submission.Geometry.eucNorm_nonneg U)] at h4

/-- If `a + b = c + d` then `a - c` is the half-difference of the two "diagonals" `a - b`, `c - d`. -/
lemma nss_sub_eq_half_smul_sub {a b c d : ℝ × ℝ} (h : a + b = c + d) :
    a - c = (1/2 : ℝ) • ((a - b) - (c - d)) := by
  ext
  · have h1 := congrArg Prod.fst h
    simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul] at h1 ⊢
    linarith
  · have h2 := congrArg Prod.snd h
    simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul] at h2 ⊢
    linarith

/-- If `a + b = c + d` then `a - d` is the half-sum of the two "diagonals" `a - b`, `c - d`. -/
lemma nss_sub_eq_half_smul_add {a b c d : ℝ × ℝ} (h : a + b = c + d) :
    a - d = (1/2 : ℝ) • ((a - b) + (c - d)) := by
  ext
  · have h1 := congrArg Prod.fst h
    simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul] at h1 ⊢
    linarith
  · have h2 := congrArg Prod.snd h
    simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul] at h2 ⊢
    linarith

/-- If `a + b = c + d` then `b - d` is minus the half-difference of `a - b`, `c - d`. -/
lemma nss_sub_eq_neg_half_smul_sub {a b c d : ℝ × ℝ} (h : a + b = c + d) :
    b - d = -((1/2 : ℝ) • ((a - b) - (c - d))) := by
  ext
  · have h1 := congrArg Prod.fst h
    simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Prod.fst_neg] at h1 ⊢
    linarith
  · have h2 := congrArg Prod.snd h
    simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, Prod.snd_neg] at h2 ⊢
    linarith

/-- If `a + b = c + d` then `b - c` is minus the half-sum of `a - b`, `c - d`. -/
lemma nss_sub_eq_neg_half_smul_add {a b c d : ℝ × ℝ} (h : a + b = c + d) :
    b - c = -((1/2 : ℝ) • ((a - b) + (c - d))) := by
  ext
  · have h1 := congrArg Prod.fst h
    simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Prod.fst_neg] at h1 ⊢
    linarith
  · have h2 := congrArg Prod.snd h
    simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, Prod.snd_neg] at h2 ⊢
    linarith

/-- The plane curve is invariant under a shift of the parameter by an integer multiple of `2π`. -/
lemma nss_curve_add_two_pi_mul_int (γ : Circle → ℝ × ℝ) (k : ℤ) (t : ℝ) :
    curve γ (t + 2 * Real.pi * (k : ℝ)) = curve γ t := by
  have h1 : (2 * Real.pi * (k : ℝ)) = (k : ℝ) * (2 * Real.pi) := by ring
  rw [h1]
  simp only [curve]
  rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

end Geometry2

section Target

theorem no_small_squares (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y x' y' : Circle, γ x ≠ γ y → γ x' ≠ γ y' →
      γ x + γ y = γ x' + γ y' →
      Submission.Geometry.eucNorm (γ x - γ y) = Submission.Geometry.eucNorm (γ x' - γ y') →
      Submission.Collision.dirC (γ x - γ y)
        = Submission.Collision.dirC (γ x' - γ y') + ((1 / 2 : ℝ) : UnitAddCircle) →
      δ ≤ Submission.Geometry.eucNorm (γ x - γ y) := by
  obtain ⟨ηu, hηupos, hηu⟩ := nss_exists_uniform_secant_pos hγ
  set η : ℝ := min (ηu / 2) (Real.pi / 4) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact lt_min (by linarith) (by linarith [Real.pi_pos])
  have hη2 : 2 * η ≤ ηu := by
    rw [hηdef]
    have h1 : min (ηu / 2) (Real.pi / 4) ≤ ηu / 2 := min_le_left _ _
    linarith
  have hηπ : η ≤ Real.pi := by
    rw [hηdef]
    have h1 : min (ηu / 2) (Real.pi / 4) ≤ Real.pi / 4 := min_le_right _ _
    linarith [Real.pi_pos]
  obtain ⟨δl, hδlpos, hδl⟩ := nss_exists_int_shift_le η hηpos hηπ
  obtain ⟨δi, hδipos, hδi⟩ := nss_exists_dist_lt_of_curve_dist_lt γ hγ hδlpos
  refine ⟨δi, hδipos, ?_⟩
  intro x y x' y' hxy hxy' hsum hlen hdir
  set U : ℝ × ℝ := γ x - γ y with hU
  set V : ℝ × ℝ := γ x' - γ y' with hV
  have hneU : U ≠ 0 := by rw [hU]; exact sub_ne_zero.mpr hxy
  have hneV : V ≠ 0 := by rw [hV]; exact sub_ne_zero.mpr hxy'
  have hperp : eucDot U V = 0 := by
    rw [hU, hV]
    exact (dirC_half_perp (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hxy')).mp hdir
  have hlen' : eucNorm U = eucNorm V := by rw [hU, hV]; exact hlen
  set L : ℝ := eucNorm U with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact Submission.Geometry.eucNorm_pos hneU
  have hLc : Submission.Geometry.eucNorm (γ x - γ y) = L := by rw [← hU, hLdef]
  have hLc' : Submission.Geometry.eucNorm (γ x' - γ y') = L := by
    rw [← hV, ← hlen', hLdef]
  have hA : eucNorm ((1/2 : ℝ) • (U - V)) ≤ L := by
    rw [hLdef]; exact nss_eucNorm_half_sub_le hperp hlen'
  have hB : eucNorm ((1/2 : ℝ) • (U + V)) ≤ L := by
    rw [hLdef]; exact nss_eucNorm_half_add_le hperp hlen'
  -- every two of the four image points are within `L` of each other
  have hd_xy : dist (γ x) (γ y) ≤ L := by
    rw [dist_eq_norm]; exact le_trans (nss_norm_le_eucNorm _) (le_of_eq hLc)
  have hd_x'y' : dist (γ x') (γ y') ≤ L := by
    rw [dist_eq_norm]; exact le_trans (nss_norm_le_eucNorm _) (le_of_eq hLc')
  have hd_xx' : dist (γ x) (γ x') ≤ L := by
    rw [dist_eq_norm, nss_sub_eq_half_smul_sub hsum]
    exact le_trans (nss_norm_le_eucNorm _) hA
  have hd_xy' : dist (γ x) (γ y') ≤ L := by
    rw [dist_eq_norm, nss_sub_eq_half_smul_add hsum]
    exact le_trans (nss_norm_le_eucNorm _) hB
  have hd_yx' : dist (γ y) (γ x') ≤ L := by
    rw [dist_eq_norm, nss_sub_eq_neg_half_smul_add hsum]
    refine le_trans (nss_norm_le_eucNorm _) ?_
    rw [nss_eucNorm_neg]
    exact hB
  have hd_yy' : dist (γ y) (γ y') ≤ L := by
    rw [dist_eq_norm, nss_sub_eq_neg_half_smul_sub hsum]
    refine le_trans (nss_norm_le_eucNorm _) ?_
    rw [nss_eucNorm_neg]
    exact hA
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : L < δi`
  obtain ⟨s₀, hs₀⟩ := Circle.exp_surjective x
  obtain ⟨t₀, ht₀⟩ := Circle.exp_surjective y
  obtain ⟨u₀, hu₀⟩ := Circle.exp_surjective x'
  obtain ⟨v₀, hv₀⟩ := Circle.exp_surjective y'
  have hcy : dist x y < δl := hδi x y (lt_of_le_of_lt hd_xy hcon)
  have hcx' : dist x x' < δl := hδi x x' (lt_of_le_of_lt hd_xx' hcon)
  have hcy' : dist x y' < δl := hδi x y' (lt_of_le_of_lt hd_xy' hcon)
  obtain ⟨k₁, hk₁⟩ := hδl x y s₀ t₀ hs₀ ht₀ hcy
  obtain ⟨k₂, hk₂⟩ := hδl x x' s₀ u₀ hs₀ hu₀ hcx'
  obtain ⟨k₃, hk₃⟩ := hδl x y' s₀ v₀ hs₀ hv₀ hcy'
  set t₁ : ℝ := t₀ + 2 * Real.pi * (k₁ : ℝ) with ht₁def
  set s₁ : ℝ := u₀ + 2 * Real.pi * (k₂ : ℝ) with hs₁def
  set t₂ : ℝ := v₀ + 2 * Real.pi * (k₃ : ℝ) with ht₂def
  have hk₁' : |t₁ - s₀| ≤ η := by rw [ht₁def]; exact hk₁
  have hk₂' : |s₁ - s₀| ≤ η := by rw [hs₁def]; exact hk₂
  have hk₃' : |t₂ - s₀| ≤ η := by rw [ht₂def]; exact hk₃
  have hct₁ : curve γ t₁ = γ y := by
    rw [ht₁def, nss_curve_add_two_pi_mul_int, curve, ht₀]
  have hcs₁ : curve γ s₁ = γ x' := by
    rw [hs₁def, nss_curve_add_two_pi_mul_int, curve, hu₀]
  have hct₂ : curve γ t₂ = γ y' := by
    rw [ht₂def, nss_curve_add_two_pi_mul_int, curve, hv₀]
  have hcs₀ : curve γ s₀ = γ x := by rw [curve, hs₀]
  have ht₁b : s₀ - η ≤ t₁ ∧ t₁ ≤ s₀ + η := by
    have h := hk₁'; rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hs₁b : s₀ - η ≤ s₁ ∧ s₁ ≤ s₀ + η := by
    have h := hk₂'; rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have ht₂b : s₀ - η ≤ t₂ ∧ t₂ ≤ s₀ + η := by
    have h := hk₃'; rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  set a₁ : ℝ := min s₀ t₁ with ha₁def
  set b₁ : ℝ := max s₀ t₁ with hb₁def
  set a₂ : ℝ := min s₁ t₂ with ha₂def
  set b₂ : ℝ := max s₁ t₂ with hb₂def
  have hs₀_ne_t₁ : s₀ ≠ t₁ := by
    intro heq
    exact hxy (by rw [← hcs₀, ← hct₁, heq])
  have hs₁_ne_t₂ : s₁ ≠ t₂ := by
    intro heq
    exact hxy' (by rw [← hcs₁, ← hct₂, heq])
  have hab₁ : (a₁ = s₀ ∧ b₁ = t₁) ∨ (a₁ = t₁ ∧ b₁ = s₀) := by
    rw [ha₁def, hb₁def]
    by_cases h : s₀ ≤ t₁
    · exact Or.inl ⟨min_eq_left h, max_eq_right h⟩
    · push Not at h
      exact Or.inr ⟨min_eq_right h.le, max_eq_left h.le⟩
  have hab₂ : (a₂ = s₁ ∧ b₂ = t₂) ∨ (a₂ = t₂ ∧ b₂ = s₁) := by
    rw [ha₂def, hb₂def]
    by_cases h : s₁ ≤ t₂
    · exact Or.inl ⟨min_eq_left h, max_eq_right h⟩
    · push Not at h
      exact Or.inr ⟨min_eq_right h.le, max_eq_left h.le⟩
  have ha₁_lt : a₁ < b₁ := by
    rw [ha₁def, hb₁def]
    exact min_lt_max.mpr hs₀_ne_t₁
  have ha₂_lt : a₂ < b₂ := by
    rw [ha₂def, hb₂def]
    exact min_lt_max.mpr hs₁_ne_t₂
  have hne_a₁b₁ : curve γ a₁ ≠ curve γ b₁ := by
    rcases hab₁ with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [h, h', hcs₀, hct₁]; exact hxy
    · rw [h, h', hcs₀, hct₁]; exact hxy.symm
  have hne_a₂b₂ : curve γ a₂ ≠ curve γ b₂ := by
    rcases hab₂ with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [h, h', hcs₁, hct₂]; exact hxy'
    · rw [h, h', hcs₁, hct₂]; exact hxy'.symm
  have ha₁_low : s₀ - η ≤ a₁ := by
    rcases hab₁ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith
    · rw [h]; exact ht₁b.1
  have ha₂_low : s₀ - η ≤ a₂ := by
    rcases hab₂ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hs₁b.1
    · rw [h]; exact ht₂b.1
  have hb₁_up : b₁ ≤ s₀ + η := by
    rcases hab₁ with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact ht₁b.2
    · rw [h]; linarith
  have hb₂_up : b₂ ≤ s₀ + η := by
    rcases hab₂ with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact ht₂b.2
    · rw [h]; exact hs₁b.2
  have hmain := hηu (s₀ - η) a₁ b₁ a₂ b₂ ha₁_low ha₁_lt
    (by linarith [hb₁_up, hη2]) ha₂_low ha₂_lt (by linarith [hb₂_up, hη2])
    hne_a₁b₁ hne_a₂b₂
  have hsec₁ : curve γ b₁ - curve γ a₁ = U ∨ curve γ b₁ - curve γ a₁ = -U := by
    rcases hab₁ with ⟨h, h'⟩ | ⟨h, h'⟩
    · right; rw [h, h', hcs₀, hct₁, hU]; abel
    · left; rw [h, h', hcs₀, hct₁, hU]
  have hsec₂ : curve γ b₂ - curve γ a₂ = V ∨ curve γ b₂ - curve γ a₂ = -V := by
    rcases hab₂ with ⟨h, h'⟩ | ⟨h, h'⟩
    · right; rw [h, h', hcs₁, hct₂, hV]; abel
    · left; rw [h, h', hcs₁, hct₂, hV]
  have hzero : eucDot (curve γ b₁ - curve γ a₁) (curve γ b₂ - curve γ a₂) = 0 := by
    rcases hsec₁ with h | h <;> rcases hsec₂ with h' | h' <;> rw [h, h'] <;>
      simp only [nss_eucDot_neg_neg, nss_eucDot_neg_left, nss_eucDot_neg_right, hperp, neg_zero]
  linarith [hmain, hzero]

end Target

end Work.Drive
