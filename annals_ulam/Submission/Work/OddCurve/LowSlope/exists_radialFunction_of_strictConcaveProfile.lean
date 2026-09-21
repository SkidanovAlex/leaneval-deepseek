import Mathlib
import Submission.Work.OddEnvelope.Main
import Submission.Work.OddRadon.RadialDefs
import Submission.Work.Analysis.Calculus.hasDerivAt_polarMap
import Submission.Work.Analysis.Calculus.contDiffOn_invFunOn_of_strictMonoOn
import Submission.Work.Analysis.Convex.pos_sub_mul_deriv_of_concaveOn

/-!
# The radial function `ρ` of a strictly concave profile

Let `f : ℝ → ℝ` be a profile on `(-1,1)` with `f 0 = 1`, `f > 0` inside the interval and
`f (±1) = 0` (the shape of the upper boundary of a `C^∞` "cap" of a body of revolution: a hill
peaking at `(0,1)` and meeting the axis at `(±1, 0)`).

This file constructs the *radial function* `ρ` of the region under the graph, in the sense

  `ρ u * √(1 - u²) = f (ρ u * u)`   for `-1 < u < 1`,

i.e. the point `(ρ u · u, ρ u · √(1-u²))` in the direction `(u, √(1-u²))` of the unit circle is
the point where the ray of that direction meets the graph of `f`.  Equivalently, `u ↦ ρ u · u`
assigns to the *cosine* of the direction the `x`-coordinate of the intersection, so `ρ` is the
composition of the radial map `radMap f t = √(t² + f t²)` with the inverse of the polar map

  `polarMap f t = t / √(t² + f t²)`  (the cosine of the direction of `(t, f t)`).

The construction is a one-dimensional inverse-function argument.  `polarMap f` is smooth, is
strictly increasing because its derivative is
`f t (f t - t f'(t)) / (√(t²+f t²))³ > 0` (the positivity of `f t - t f'(t)` is the tangent
inequality for the concave `f` with `f 0 = 1`,
`Work.Analysis.Convex.pos_sub_mul_deriv_of_concaveOn`), and maps `(-1,1)` onto `(-1,1)`.  Hence
`Function.invFunOn` of the polar map is a strictly increasing `C^∞` function on `(-1,1)`
(`Work.Analysis.Calculus.contDiffOn_invFunOn_of_strictMonoOn`) and `ρ := radMap f ∘ invFunOn`
has all the required properties.
-/

noncomputable section

open Set

namespace Work.OddCurve.LowSlope

/-- **The polar (cosine) map of a profile** `f`: the cosine of the direction of the graph point
`(t, f t)`, namely `t / √(t² + f t²)`. -/
def polarMap (f : ℝ → ℝ) : ℝ → ℝ := fun t => t / Real.sqrt (t ^ 2 + (f t) ^ 2)

/-- **The radial map of a profile** `f`: the distance `√(t² + f t²)` from the origin to the graph
point `(t, f t)`. -/
def radMap (f : ℝ → ℝ) : ℝ → ℝ := fun t => Real.sqrt (t ^ 2 + (f t) ^ 2)

lemma radMap_pos {f : ℝ → ℝ} (hfpos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : 0 < radMap f t := by
  show 0 < Real.sqrt (t ^ 2 + (f t) ^ 2)
  rw [Real.sqrt_pos]
  have h1 : 0 < (f t) ^ 2 := pow_pos (hfpos t ht) 2
  have h2 : 0 ≤ t ^ 2 := sq_nonneg t
  linarith

lemma radMap_pos_Icc {f : ℝ → ℝ} (hf0 : f 0 = 1) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < radMap f t := by
  show 0 < Real.sqrt (t ^ 2 + (f t) ^ 2)
  rw [Real.sqrt_pos]
  rcases eq_or_ne t 0 with rfl | hne
  · rw [hf0]; norm_num
  · have h1 : 0 < t ^ 2 := by positivity
    have h2 : 0 ≤ (f t) ^ 2 := sq_nonneg _
    linarith

lemma continuousOn_radMap {f : ℝ → ℝ} (hf0 : f 0 = 1)
    (hcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) :
    ContinuousOn (radMap f) (Set.Icc (-1 : ℝ) 1) := by
  show ContinuousOn (fun t : ℝ => Real.sqrt (t ^ 2 + (f t) ^ 2)) _
  apply ContinuousOn.sqrt
  fun_prop

lemma continuousOn_polarMap {f : ℝ → ℝ} (hf0 : f 0 = 1)
    (hcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) :
    ContinuousOn (polarMap f) (Set.Icc (-1 : ℝ) 1) := by
  show ContinuousOn (fun t : ℝ => t / Real.sqrt (t ^ 2 + (f t) ^ 2)) _
  apply ContinuousOn.div
  · fun_prop
  · exact continuousOn_radMap hf0 hcont
  · intro x hx
    exact ne_of_gt (radMap_pos_Icc hf0 hx)

lemma contDiffOn_radMap {f : ℝ → ℝ}
    (hfpos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radMap f) (Set.Ioo (-1 : ℝ) 1) := by
  show ContDiffOn ℝ _ (fun t : ℝ => Real.sqrt (t ^ 2 + (f t) ^ 2)) _
  apply ContDiffOn.sqrt
  · fun_prop
  · intro x hx
    have h1 : 0 < (f x) ^ 2 := pow_pos (hfpos x hx) 2
    have h2 : 0 ≤ x ^ 2 := sq_nonneg x
    linarith

lemma contDiffOn_polarMap {f : ℝ → ℝ}
    (hfpos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polarMap f) (Set.Ioo (-1 : ℝ) 1) := by
  show ContDiffOn ℝ _ (fun t : ℝ => t / Real.sqrt (t ^ 2 + (f t) ^ 2)) _
  exact ContDiffOn.div (by fun_prop) (contDiffOn_radMap hfpos hsm)
    (fun x hx => ne_of_gt (radMap_pos hfpos hx))

/-- The derivative of the polar map, from `Work.Analysis.Calculus.hasDerivAt_polarMap`. -/
lemma deriv_polarMap {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-1 : ℝ) 1)) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (hne : t ^ 2 + (f t) ^ 2 ≠ 0) :
    deriv (polarMap f) t = f t * (f t - t * deriv f t) / (radMap f t) ^ 3 := by
  show deriv (fun x : ℝ => x / Real.sqrt (x ^ 2 + (f x) ^ 2)) t
      = f t * (f t - t * deriv f t) / (Real.sqrt (t ^ 2 + (f t) ^ 2)) ^ 3
  exact (Work.Analysis.Calculus.hasDerivAt_polarMap hsm ht hne).deriv

/-- The derivative of the polar map is positive at every interior point of the profile. -/
lemma deriv_polarMap_pos {f : ℝ → ℝ} (hf0 : f 0 = 1)
    (hfpos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hconc : StrictConcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) f)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-1 : ℝ) 1)) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : 0 < deriv (polarMap f) t := by
  have hne : t ^ 2 + (f t) ^ 2 ≠ 0 := by
    have h1 : 0 < (f t) ^ 2 := pow_pos (hfpos t ht) 2
    have h2 : 0 ≤ t ^ 2 := sq_nonneg t
    linarith
  rw [deriv_polarMap hsm ht hne]
  exact div_pos (mul_pos (hfpos t ht)
      (Work.Analysis.Convex.pos_sub_mul_deriv_of_concaveOn hf0 hconc.concaveOn
        (hsm.differentiableOn (by simp)) ht))
    (pow_pos (radMap_pos hfpos ht) 3)

lemma deriv_polarMap_ne_zero {f : ℝ → ℝ} (hf0 : f 0 = 1)
    (hfpos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hconc : StrictConcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) f)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-1 : ℝ) 1)) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : deriv (polarMap f) t ≠ 0 :=
  ne_of_gt (deriv_polarMap_pos hf0 hfpos hconc hsm ht)

lemma strictMonoOn_polarMap {f : ℝ → ℝ} (hf0 : f 0 = 1)
    (hcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hfpos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hconc : StrictConcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) f)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-1 : ℝ) 1)) :
    StrictMonoOn (polarMap f) (Set.Icc (-1 : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_polarMap hf0 hcont) ?_
  intro x hx
  rw [interior_Icc] at hx
  exact deriv_polarMap_pos hf0 hfpos hconc hsm hx

/-- The polar map maps `(-1,1)` onto `(-1,1)`: it is continuous on `[-1,1]`, strictly increasing,
and takes the values `-1` and `1` at the ends. -/
lemma surjOn_polarMap {f : ℝ → ℝ} (hf0 : f 0 = 1) (hf_neg : f (-1) = 0) (hf_one : f 1 = 0)
    (hcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hfpos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hconc : StrictConcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) f)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-1 : ℝ) 1)) :
    Set.SurjOn (polarMap f) (Set.Ioo (-1 : ℝ) 1) (Set.Ioo (-1 : ℝ) 1) := by
  have himg := (continuousOn_polarMap hf0 hcont).image_Ioo_of_strictMonoOn (a := -1) (b := 1)
    (by norm_num) (strictMonoOn_polarMap hf0 hcont hfpos hconc hsm)
  have hWm : polarMap f (-1) = -1 := by
    show (-1 : ℝ) / Real.sqrt ((-1 : ℝ) ^ 2 + (f (-1)) ^ 2) = -1
    rw [hf_neg]; norm_num
  have hWp : polarMap f 1 = 1 := by
    show (1 : ℝ) / Real.sqrt ((1 : ℝ) ^ 2 + (f 1) ^ 2) = 1
    rw [hf_one]; norm_num
  rw [hWm, hWp] at himg
  intro u hu
  rw [← himg] at hu
  rw [Set.mem_image] at hu
  exact hu

theorem exists_radialFunction_of_strictConcaveProfile (f : ℝ → ℝ) (hf0 : f 0 = 1) (hcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (hf_neg : f (-1) = 0) (hf_one : f 1 = 0) (hfpos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) (hconc : StrictConcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) f) (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-1 : ℝ) 1)) : ∃ ρ : ℝ → ℝ, (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1) ∧ StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) ∧ (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u)) ∧ ρ 0 = 1 := by
  have hmonoIcc : StrictMonoOn (polarMap f) (Set.Icc (-1 : ℝ) 1) :=
    strictMonoOn_polarMap hf0 hcont hfpos hconc hsm
  have hsurj : Set.SurjOn (polarMap f) (Set.Ioo (-1 : ℝ) 1) (Set.Ioo (-1 : ℝ) 1) :=
    surjOn_polarMap hf0 hf_neg hf_one hcont hfpos hconc hsm
  obtain ⟨hIsm, hImono⟩ := Work.Analysis.Calculus.contDiffOn_invFunOn_of_strictMonoOn
    (a := -1) (b := 1) (by norm_num) (contDiffOn_polarMap hfpos hsm)
    (hmonoIcc.mono Set.Ioo_subset_Icc_self) hsurj
    (fun t ht => deriv_polarMap_ne_zero hf0 hfpos hconc hsm ht)
  let tinv : ℝ → ℝ := Function.invFunOn (polarMap f) (Set.Ioo (-1 : ℝ) 1)
  have hmem : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, tinv u ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro u hu
    exact Function.invFunOn_mem (hsurj hu)
  have heq : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, polarMap f (tinv u) = u := by
    intro u hu
    exact Function.invFunOn_eq (hsurj hu)
  let ρ : ℝ → ℝ := fun u => radMap f (tinv u)
  have hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u := by
    intro u hu
    exact radMap_pos hfpos (hmem u hu)
  have hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1) :=
    (contDiffOn_radMap hfpos hsm).comp hIsm (fun u hu => hmem u hu)
  have huv : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u = tinv u := by
    intro u hu
    have h' : tinv u / radMap f (tinv u) = u := by
      simpa only [polarMap, radMap] using heq u hu
    have hrt : 0 < radMap f (tinv u) := radMap_pos hfpos (hmem u hu)
    have hne : radMap f (tinv u) ≠ 0 := ne_of_gt hrt
    show radMap f (tinv u) * u = tinv u
    calc radMap f (tinv u) * u
        = radMap f (tinv u) * (tinv u / radMap f (tinv u)) := by rw [h']
      _ = tinv u := by field_simp
  have hmonoρ : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) := by
    intro u1 h1 u2 h2 h12
    show ρ u1 * u1 < ρ u2 * u2
    rw [huv u1 h1, huv u2 h2]
    exact hImono h1 h2 h12
  have hid : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u) := by
    intro u hu
    have htI : tinv u ∈ Set.Ioo (-1 : ℝ) 1 := hmem u hu
    have hft : 0 < f (tinv u) := hfpos _ htI
    have hrt : 0 < radMap f (tinv u) := radMap_pos hfpos htI
    have hr2 : (radMap f (tinv u)) ^ 2 = (tinv u) ^ 2 + (f (tinv u)) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hueq : u = tinv u / radMap f (tinv u) := by
      have h := heq u hu
      simpa only [polarMap, radMap] using h.symm
    have hne : radMap f (tinv u) ≠ 0 := ne_of_gt hrt
    have h1mu : 1 - u ^ 2 = (f (tinv u) / radMap f (tinv u)) ^ 2 := by
      have hsq : u ^ 2 = (tinv u / radMap f (tinv u)) ^ 2 := by
        conv_lhs => rw [hueq]
      rw [hsq, div_pow, div_pow]
      field_simp
      nlinarith [hr2]
    have hsqrt : Real.sqrt (1 - u ^ 2) = f (tinv u) / radMap f (tinv u) := by
      rw [h1mu, Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg hft.le hrt.le)]
    rw [huv u hu]
    show radMap f (tinv u) * Real.sqrt (1 - u ^ 2) = f (tinv u)
    rw [hsqrt]
    field_simp
  have h0 : ρ 0 = 1 := by
    have h00 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
    have hW0 : polarMap f 0 = 0 := by
      show (0 : ℝ) / Real.sqrt (0 ^ 2 + (f 0) ^ 2) = 0
      simp
    have ht0 : tinv 0 = 0 :=
      (hmonoIcc.mono Set.Ioo_subset_Icc_self).injOn (hmem 0 h00) h00
        (by rw [heq 0 h00, hW0])
    show radMap f (tinv 0) = 1
    rw [ht0]
    show Real.sqrt (0 ^ 2 + (f 0) ^ 2) = 1
    rw [hf0]
    norm_num
  exact ⟨ρ, hρpos, hρsm, hmonoρ, hid, h0⟩

end Work.OddCurve.LowSlope
