import Mathlib

/-!
# Schwarz reflection and boundary uniqueness for holomorphic functions (WIP)

The `sorry`s in this file are the remaining work of the Carathéodory route's injectivity step;
see `NOTES.md`.  Proved already: the definitions and the easy pointwise lemmas.  Remaining:
the rectangle-boundary reflection identity, the conservative property, the Morera/identity-theorem
assembly, and the Möbius transport to the disc.
-/

noncomputable section

open Set Metric Filter Complex MeasureTheory

open scoped Topology

namespace Work.Smooth.SphereJordan.Caratheodory

/-- The "double" of a function `g` on the upper half-plane, obtained by reflecting across the real
axis: it equals `g` above, `u ↦ star (g (star u))` below, and `0` on the axis. -/
def reflectUp (g : ℂ → ℂ) (u : ℂ) : ℂ :=
  if 0 < u.im then g u else if u.im < 0 then star (g (star u)) else 0

@[simp] lemma reflectUp_of_pos {g : ℂ → ℂ} {u : ℂ} (h : 0 < u.im) : reflectUp g u = g u := by
  simp [reflectUp, h]

@[simp] lemma reflectUp_of_neg {g : ℂ → ℂ} {u : ℂ} (h : u.im < 0) :
    reflectUp g u = star (g (star u)) := by
  simp [reflectUp, h, not_lt.mpr h.le]

@[simp] lemma reflectUp_of_zero {g : ℂ → ℂ} {u : ℂ} (h : u.im = 0) : reflectUp g u = 0 := by
  simp [reflectUp, h]

lemma star_eq_self_of_im_eq_zero {u : ℂ} (h : u.im = 0) : star u = u := by
  refine Complex.ext ?_ ?_ <;> simp [h]

@[simp] lemma star_I : star (Complex.I) = -Complex.I := by
  refine Complex.ext ?_ ?_ <;> simp

@[simp] lemma star_ofReal (x : ℝ) : star ((x : ℂ)) = (x : ℂ) := by
  refine Complex.ext ?_ ?_ <;> simp

/-- The boundary integral of a rectangle, in the form used by
`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`. -/
def rectBoundary (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
    (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
    Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
    Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))

/-- On a point of the closed lower half-plane the reflection agrees with `star ∘ g ∘ star`
(provided `g` vanishes on the axis, so that the two definitions agree there). -/
lemma reflectUp_eq {g : ℂ → ℂ} (hax : ∀ u : ℂ, u.im = 0 → g u = 0) {u : ℂ} (hu : u.im ≤ 0) :
    reflectUp g u = star (g (star u)) := by
  rcases lt_or_eq_of_le hu with h | h
  · rw [reflectUp_of_neg h]
  · rw [reflectUp_of_zero h]
    show (0 : ℂ) = star (g (star u))
    rw [star_eq_self_of_im_eq_zero h, hax u h, star_zero]

/-- Pulling `star` out of an interval integral. -/
lemma star_intervalIntegral {F : ℝ → ℂ} {a b : ℝ} (h : IntervalIntegrable F volume a b) :
    star (∫ x in a..b, F x) = ∫ x in a..b, star (F x) := by
  have h3 : ∀ q : ℂ, (Complex.conjCLE : ℂ →L[ℝ] ℂ) q = star q := fun q =>
    (Complex.conjCLE_apply q).trans (congrFun Complex.star_def q).symm
  have h2 := ContinuousLinearMap.intervalIntegral_comp_comm
    (L := (Complex.conjCLE : ℂ →L[ℝ] ℂ)) h
  rw [h3] at h2
  exact h2.symm

/-- **Reflection of the boundary integral.**  For a rectangle lying in the closed lower
half-plane on which `g` vanishes on the axis, the boundary integral of the reflected function
`reflectUp g` equals the conjugate of the boundary integral of `g` over the reflected rectangle.

Each of the four edge integrals transforms separately: on the rectangle `reflectUp g u = star (g
(star u))`; `star` is pulled out with `star_intervalIntegral`; the two vertical edges are
substituted by `y ↦ -y` (`intervalIntegral.integral_comp_neg`, which swaps the bounds, hence the
sign); the linear terms `I * _` are handled by `star (I * q) = -I * star q`. -/
lemma rectBoundary_reflectUp {g : ℂ → ℂ} {z w : ℂ} (hz : z.im ≤ 0) (hw : w.im ≤ 0)
    (hax : ∀ u : ℂ, u.im = 0 → g u = 0)
    (hcup : ContinuousOn (fun u : ℂ => g u) {u : ℂ | 0 ≤ u.im}) :
    rectBoundary (reflectUp g) z w = star (rectBoundary g (star z) (star w)) := by
  have hzre : (star z).re = z.re := by simp
  have hwre : (star w).re = w.re := by simp
  have hzim : (star z).im = -z.im := by simp
  have hwim : (star w).im = -w.im := by simp
  -- the interval of the vertical integrals stays in the closed lower half-plane
  have hy0 : ∀ y ∈ Set.uIcc z.im w.im, y ≤ 0 := by
    intro y hy
    rcases le_total z.im w.im with h | h
    · rw [Set.uIcc_of_le h] at hy; exact le_trans hy.2 hw
    · rw [Set.uIcc_of_ge h] at hy; exact le_trans hy.2 hz
  -- integrability of the four integrands (all their arguments lie in the upper half-plane)
  have hint_h : ∀ c : ℝ, 0 ≤ c →
      IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * Complex.I)) volume z.re w.re := by
    intro c hc
    have hcont : ContinuousOn (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * Complex.I))
        (Set.uIcc z.re w.re) := by
      refine hcup.comp (by fun_prop) ?_
      intro x _
      have h1 : ((x : ℂ) + (c : ℂ) * Complex.I).im = c := by simp
      show 0 ≤ ((x : ℂ) + (c : ℂ) * Complex.I).im
      rw [h1]; exact hc
    exact hcont.intervalIntegrable
  have hint_v : ∀ c : ℝ,
      IntervalIntegrable (fun y : ℝ => g ((c : ℂ) + (-((y : ℝ) : ℂ)) * Complex.I))
        volume z.im w.im := by
    intro c
    have hcont : ContinuousOn
        (fun y : ℝ => g ((c : ℂ) + (-((y : ℝ) : ℂ)) * Complex.I)) (Set.uIcc z.im w.im) := by
      refine hcup.comp (by fun_prop) ?_
      intro y hy
      have him : ((c : ℂ) + (-((y : ℝ) : ℂ)) * Complex.I).im = -y := by simp
      show 0 ≤ ((c : ℂ) + (-((y : ℝ) : ℂ)) * Complex.I).im
      rw [him]; linarith [hy0 y hy]
    exact hcont.intervalIntegrable
  -- the four edge identities
  have key1 : (∫ x : ℝ in z.re..w.re, reflectUp g (x + z.im * Complex.I))
      = star (∫ x : ℝ in (star z).re..(star w).re, g (x + (star z).im * Complex.I)) := by
    have hpt : ∀ x : ℝ, reflectUp g (x + z.im * Complex.I)
        = star (g (x + (star z).im * Complex.I)) := by
      intro x
      have him : (x + z.im * Complex.I).im = z.im := by simp
      rw [reflectUp_eq hax (by rw [him]; exact hz)]
      refine congrArg (fun q => star (g q)) ?_
      have hs : star (((z.im : ℝ)) : ℂ) = (((z.im : ℝ)) : ℂ) := star_ofReal z.im
      rw [star_add, star_mul, star_ofReal x, hs, star_I, hzim]
      push_cast
      ring
    simp only [hpt, hzre, hwre]
    rw [star_intervalIntegral (hint_h (star z).im (by rw [hzim]; exact neg_nonneg.mpr hz))]
  have key2 : (∫ x : ℝ in z.re..w.re, reflectUp g (x + w.im * Complex.I))
      = star (∫ x : ℝ in (star z).re..(star w).re, g (x + (star w).im * Complex.I)) := by
    have hpt : ∀ x : ℝ, reflectUp g (x + w.im * Complex.I)
        = star (g (x + (star w).im * Complex.I)) := by
      intro x
      have him : (x + w.im * Complex.I).im = w.im := by simp
      rw [reflectUp_eq hax (by rw [him]; exact hw)]
      refine congrArg (fun q => star (g q)) ?_
      have hs : star (((w.im : ℝ)) : ℂ) = (((w.im : ℝ)) : ℂ) := star_ofReal w.im
      rw [star_add, star_mul, star_ofReal x, hs, star_I, hwim]
      push_cast
      ring
    simp only [hpt, hzre, hwre]
    rw [star_intervalIntegral (hint_h (star w).im (by rw [hwim]; exact neg_nonneg.mpr hw))]
  have hsub3 : (∫ y : ℝ in z.im..w.im, g (w.re + (-y) * Complex.I))
      = -(∫ y : ℝ in -z.im..-w.im, g (w.re + y * Complex.I)) := by
    rw [show (∫ y : ℝ in z.im..w.im, g (w.re + (-y) * Complex.I))
        = ∫ y : ℝ in -w.im..-z.im, g (w.re + y * Complex.I) from by
      simpa only [Complex.ofReal_neg] using
        (intervalIntegral.integral_comp_neg (a := z.im) (b := w.im)
          (f := fun y : ℝ => g (w.re + y * Complex.I)))]
    rw [intervalIntegral.integral_symm]
  have hsub4 : (∫ y : ℝ in z.im..w.im, g (z.re + (-y) * Complex.I))
      = -(∫ y : ℝ in -z.im..-w.im, g (z.re + y * Complex.I)) := by
    rw [show (∫ y : ℝ in z.im..w.im, g (z.re + (-y) * Complex.I))
        = ∫ y : ℝ in -w.im..-z.im, g (z.re + y * Complex.I) from by
      simpa only [Complex.ofReal_neg] using
        (intervalIntegral.integral_comp_neg (a := z.im) (b := w.im)
          (f := fun y : ℝ => g (z.re + y * Complex.I)))]
    rw [intervalIntegral.integral_symm]
  have key3 : (∫ y : ℝ in z.im..w.im, reflectUp g (w.re + y * Complex.I))
      = -star (∫ y : ℝ in (star z).im..(star w).im, g (w.re + y * Complex.I)) := by
    have hpt : ∀ y ∈ Set.uIcc z.im w.im, reflectUp g (w.re + y * Complex.I)
        = star (g (w.re + (-y) * Complex.I)) := by
      intro y hy
      have him : (w.re + y * Complex.I).im = y := by simp
      rw [reflectUp_eq hax (by rw [him]; exact hy0 y hy)]
      refine congrArg (fun q => star (g q)) ?_
      rw [star_add, star_mul, star_ofReal w.re, star_ofReal y, star_I]
      ring
    have hcongr : (∫ y : ℝ in z.im..w.im, reflectUp g (w.re + y * Complex.I))
        = ∫ y : ℝ in z.im..w.im, star (g (w.re + (-y) * Complex.I)) :=
      intervalIntegral.integral_congr hpt
    rw [hcongr, hzim, hwim, ← star_neg, ← hsub3, ← star_intervalIntegral (hint_v w.re)]
  have key4 : (∫ y : ℝ in z.im..w.im, reflectUp g (z.re + y * Complex.I))
      = -star (∫ y : ℝ in (star z).im..(star w).im, g (z.re + y * Complex.I)) := by
    have hpt : ∀ y ∈ Set.uIcc z.im w.im, reflectUp g (z.re + y * Complex.I)
        = star (g (z.re + (-y) * Complex.I)) := by
      intro y hy
      have him : (z.re + y * Complex.I).im = y := by simp
      rw [reflectUp_eq hax (by rw [him]; exact hy0 y hy)]
      refine congrArg (fun q => star (g q)) ?_
      rw [star_add, star_mul, star_ofReal z.re, star_ofReal y, star_I]
      ring
    have hcongr : (∫ y : ℝ in z.im..w.im, reflectUp g (z.re + y * Complex.I))
        = ∫ y : ℝ in z.im..w.im, star (g (z.re + (-y) * Complex.I)) :=
      intervalIntegral.integral_congr hpt
    rw [hcongr, hzim, hwim, ← star_neg, ← hsub4, ← star_intervalIntegral (hint_v z.re)]
  -- assemble
  have hI : ∀ q : ℂ, star (Complex.I * q) = -(Complex.I * star q) := by
    intro q
    rw [star_mul, star_I]; ring
  simp only [rectBoundary]
  rw [key1, key2, key3, key4, hzre, hwre]
  simp only [star_add, star_sub, hI]
  ring

/-- `reflectUp g` agrees with `g` on the closed upper half-plane. -/
lemma reflectUp_eqOn_upper {g : ℂ → ℂ} (hax : ∀ u : ℂ, u.im = 0 → g u = 0) :
    EqOn (reflectUp g) g {u : ℂ | 0 ≤ u.im} := by
  intro u hu
  have hu' : 0 ≤ u.im := hu
  rcases lt_or_eq_of_le hu' with h | h
  · exact reflectUp_of_pos h
  · rw [reflectUp_of_zero h.symm, hax u h.symm]

/-- On the closed lower half-plane, `reflectUp g` is the reflected branch `star ∘ g ∘ star`. -/
lemma reflectUp_eqOn_lower {g : ℂ → ℂ} (hax : ∀ u : ℂ, u.im = 0 → g u = 0) :
    EqOn (reflectUp g) (fun u : ℂ => star (g (star u))) {u : ℂ | u.im ≤ 0} := by
  intro u hu
  have hu' : u.im ≤ 0 := hu
  rcases lt_or_eq_of_le hu' with h | h
  · exact reflectUp_of_neg h
  · rw [reflectUp_of_zero h]
    show (0 : ℂ) = star (g (star u))
    rw [star_eq_self_of_im_eq_zero h, hax u h, star_zero]

/-- **Continuity of the reflected function.**  On the ball the reflection is continuous: above the
axis it agrees with `g`, below with `star ∘ g ∘ star`, and on the axis both one-sided limits are
`0` (which is the value of the reflection there, and also of `g` by `hax`). -/
lemma continuousOn_reflectUp {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hgdiff : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → DifferentiableAt ℂ g u)
    (hgcont : ContinuousOn g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}))
    (hax : ∀ u : ℂ, u.im = 0 → g u = 0) :
    ContinuousOn (reflectUp g) (Metric.ball (0 : ℂ) ρ) := by
  intro u₀ hu₀
  have hnorm₀ : ‖u₀‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hu₀
  rcases lt_trichotomy u₀.im 0 with h | h | h
  · -- strictly below the axis
    have hloc : (fun u : ℂ => star (g (star u))) =ᶠ[𝓝 u₀] reflectUp g := by
      filter_upwards [isOpen_lt continuous_im continuous_const |>.mem_nhds h] with u hu
      exact (reflectUp_of_neg hu).symm
    have hsu : ‖star u₀‖ < ρ := by
      rw [show ‖star u₀‖ = ‖u₀‖ from by simp]; exact hnorm₀
    have hsim : 0 < (star u₀).im := by
      rw [show (star u₀).im = -u₀.im from by simp]; linarith
    have h1 : ContinuousAt (fun u : ℂ => g (star u)) u₀ :=
      ContinuousAt.comp (hgdiff (star u₀) hsu hsim).continuousAt continuous_star.continuousAt
    have h2 : ContinuousAt (fun u : ℂ => star (g (star u))) u₀ :=
      ContinuousAt.comp continuous_star.continuousAt h1
    exact (h2.congr hloc).continuousWithinAt
  · -- on the axis: both one-sided limits vanish
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hmem₀ : u₀ ∈ Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im} := ⟨hu₀, le_of_eq h.symm⟩
    have hgw : ContinuousWithinAt g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}) u₀ :=
      hgcont u₀ hmem₀
    rw [Metric.continuousWithinAt_iff] at hgw
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hgw ε hε
    refine ⟨min δ₁ ((ρ - ‖u₀‖) / 2), lt_min hδ₁pos (by linarith), fun u hu hdist => ?_⟩
    have hdist₁ : dist u u₀ < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
    have hdist₂ : dist u u₀ < (ρ - ‖u₀‖) / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
    have hu_ball : u ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right]
      have h2 : ‖u‖ ≤ ‖u₀‖ + dist u u₀ := by
        have h3 := dist_triangle u u₀ 0
        rw [dist_zero_right u, dist_zero_right u₀] at h3
        linarith
      linarith
    rcases lt_or_ge u.im 0 with hneg | hpos
    · have hsu_ball : star u ∈ Metric.ball (0 : ℂ) ρ := by
        have hb : ‖u‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hu_ball
        rwa [Metric.mem_ball, dist_zero_right, show ‖star u‖ = ‖u‖ from by simp]
      have hsu_im : 0 ≤ (star u).im := by
        rw [show (star u).im = -u.im from by simp]; linarith
      have hdist' : dist (star u) u₀ < δ₁ := by
        have hstar_u₀ : star u₀ = u₀ := by
          refine Complex.ext ?_ ?_ <;> simp [h]
        rw [dist_eq_norm, ← hstar_u₀, ← star_sub, norm_star, ← dist_eq_norm]
        exact hdist₁
      have hres := hδ₁ (x := star u) ⟨hsu_ball, hsu_im⟩ hdist'
      rw [hax u₀ h, dist_zero_right] at hres
      rw [reflectUp_of_neg hneg, show reflectUp g u₀ = 0 from reflectUp_of_zero h]
      simpa [dist_zero_right, norm_star] using hres
    · have hres := hδ₁ (x := u) ⟨hu_ball, hpos⟩ hdist₁
      rw [hax u₀ h, dist_zero_right] at hres
      rw [show reflectUp g u = g u from reflectUp_eqOn_upper hax hpos,
        show reflectUp g u₀ = 0 from reflectUp_of_zero h]
      simpa [dist_zero_right] using hres
  · -- strictly above the axis
    have hloc : g =ᶠ[𝓝 u₀] reflectUp g := by
      filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds h] with u hu
      exact (reflectUp_of_pos hu).symm
    exact ((hgdiff u₀ hnorm₀ h).continuousAt.congr hloc).continuousWithinAt

/-! ## Symmetry, localised reflection, and the Morera assembly -/

/-- `rectBoundary` is symmetric in its two corners. -/
lemma rectBoundary_symm (f : ℂ → ℂ) (z w : ℂ) : rectBoundary f z w = rectBoundary f w z := by
  have h1 : (∫ x : ℝ in w.re..z.re, f (x + w.im * Complex.I))
      = -(∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) :=
    intervalIntegral.integral_symm (a := z.re) (b := w.re)
  have h2 : (∫ x : ℝ in w.re..z.re, f (x + z.im * Complex.I))
      = -(∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) :=
    intervalIntegral.integral_symm (a := z.re) (b := w.re)
  have h3 : (∫ y : ℝ in w.im..z.im, f (z.re + y * Complex.I))
      = -(∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I)) :=
    intervalIntegral.integral_symm (a := z.im) (b := w.im)
  have h4 : (∫ y : ℝ in w.im..z.im, f (w.re + y * Complex.I))
      = -(∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) :=
    intervalIntegral.integral_symm (a := z.im) (b := w.im)
  simp only [rectBoundary]
  rw [h1, h2, h3, h4]
  ring

/-- `Rectangle` is symmetric in its two corners. -/
lemma Rectangle_comm (z w : ℂ) : Rectangle w z = Rectangle z w := by
  simp only [Rectangle, Set.uIcc, min_comm, max_comm]

/-- Negation on an unordered interval. -/
lemma neg_mem_uIcc {a b y : ℝ} : -y ∈ Set.uIcc a b ↔ y ∈ Set.uIcc (-a) (-b) := by
  rcases le_total a b with h | h
  · rw [Set.uIcc_of_le h, Set.uIcc_of_ge (by linarith : -b ≤ -a), Set.mem_Icc, Set.mem_Icc]
    constructor <;> intro hh <;> exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
  · rw [Set.uIcc_of_ge h, Set.uIcc_of_le (by linarith : -a ≤ -b), Set.mem_Icc, Set.mem_Icc]
    constructor <;> intro hh <;> exact ⟨by linarith [hh.2], by linarith [hh.1]⟩

/-- `star` carries the rectangle of the reflected corners to the original one. -/
lemma star_mem_Rectangle {z w u : ℂ} :
    star u ∈ Rectangle z w ↔ u ∈ Rectangle (star z) (star w) := by
  have hzr : (star z).re = z.re := by simp
  have hzi : (star z).im = -z.im := by simp
  have hwr : (star w).re = w.re := by simp
  have hwi : (star w).im = -w.im := by simp
  have hur : (star u).re = u.re := by simp
  have hui : (star u).im = -u.im := by simp
  rw [Rectangle, Rectangle, Complex.mem_reProdIm, Complex.mem_reProdIm,
    hzr, hwr, hur, hzi, hwi, hui]
  exact and_congr_right fun _ => neg_mem_uIcc

/-- **Localised form of the reflection identity for the rectangle boundary integral.**  Only the
continuity of `g` on the ball and on the closed upper half of it is used, together with the fact
that the reflected rectangle lies in the ball. -/
lemma rectBoundary_reflectUp_of_mem_ball {g : ℂ → ℂ} {ρ : ℝ} {z w : ℂ} (hz : z.im ≤ 0)
    (hw : w.im ≤ 0) (hax : ∀ u : ℂ, u.im = 0 → g u = 0)
    (hcont : ContinuousOn g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}))
    (hball : ∀ x ∈ Set.uIcc (star z).re (star w).re, ∀ y ∈ Set.uIcc (star z).im (star w).im,
      ((x : ℂ) + (y : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) ρ) :
    rectBoundary (reflectUp g) z w = star (rectBoundary g (star z) (star w)) := by
  have hzre : (star z).re = z.re := by simp
  have hwre : (star w).re = w.re := by simp
  have hzim : (star z).im = -z.im := by simp
  have hwim : (star w).im = -w.im := by simp
  have hy0 : ∀ y ∈ Set.uIcc z.im w.im, y ≤ 0 := by
    intro y hy
    rcases le_total z.im w.im with h | h
    · rw [Set.uIcc_of_le h] at hy; exact le_trans hy.2 hw
    · rw [Set.uIcc_of_ge h] at hy; exact le_trans hy.2 hz
  have hom : ∀ c ∈ Set.uIcc (star z).im (star w).im, 0 ≤ c := by
    intro c hc
    rw [hzim, hwim] at hc
    rcases le_total (-z.im) (-w.im) with h | h
    · rw [Set.uIcc_of_le h] at hc; linarith [hc.1, hz]
    · rw [Set.uIcc_of_ge h] at hc; linarith [hc.1, hw]
  have hint_h : ∀ c ∈ Set.uIcc (star z).im (star w).im,
      IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * Complex.I)) volume z.re w.re := by
    intro c hc
    have hc0 : 0 ≤ c := hom c hc
    refine ContinuousOn.intervalIntegrable ?_
    refine hcont.comp (by fun_prop) ?_
    intro x hx
    refine ⟨hball x (by rwa [hzre, hwre]) c hc, ?_⟩
    show 0 ≤ ((x : ℂ) + (c : ℂ) * Complex.I).im
    rw [show ((x : ℂ) + (c : ℂ) * Complex.I).im = c from by simp]
    exact hc0
  have hint_v : ∀ c ∈ Set.uIcc z.re w.re,
      IntervalIntegrable (fun y : ℝ => g ((c : ℂ) + (-((y : ℝ) : ℂ)) * Complex.I))
        volume z.im w.im := by
    intro c hc
    refine ContinuousOn.intervalIntegrable ?_
    refine hcont.comp (by fun_prop) ?_
    intro y hy
    refine ⟨?_, ?_⟩
    · have hb : ((c : ℂ) + (((-y : ℝ)) : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) ρ :=
        hball c (by rwa [hzre, hwre]) (-y) (by
          rw [hzim, hwim]
          rcases le_total z.im w.im with h' | h'
          · rw [Set.uIcc_of_le h'] at hy
            rw [Set.uIcc_of_ge (by linarith)]
            exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
          · rw [Set.uIcc_of_ge h'] at hy
            rw [Set.uIcc_of_le (by linarith)]
            exact ⟨by linarith [hy.2], by linarith [hy.1]⟩)
      simpa only [Complex.ofReal_neg] using hb
    · show 0 ≤ ((c : ℂ) + (-((y : ℝ) : ℂ)) * Complex.I).im
      rw [show ((c : ℂ) + (-((y : ℝ) : ℂ)) * Complex.I).im = -y from by simp]
      linarith [hy0 y hy]
  have hsub3 : (∫ y : ℝ in z.im..w.im, g (w.re + (-y) * Complex.I))
      = -(∫ y : ℝ in -z.im..-w.im, g (w.re + y * Complex.I)) := by
    rw [show (∫ y : ℝ in z.im..w.im, g (w.re + (-y) * Complex.I))
        = ∫ y : ℝ in -w.im..-z.im, g (w.re + y * Complex.I) from by
      simpa only [Complex.ofReal_neg] using
        (intervalIntegral.integral_comp_neg (a := z.im) (b := w.im)
          (f := fun y : ℝ => g (w.re + y * Complex.I)))]
    rw [intervalIntegral.integral_symm]
  have hsub4 : (∫ y : ℝ in z.im..w.im, g (z.re + (-y) * Complex.I))
      = -(∫ y : ℝ in -z.im..-w.im, g (z.re + y * Complex.I)) := by
    rw [show (∫ y : ℝ in z.im..w.im, g (z.re + (-y) * Complex.I))
        = ∫ y : ℝ in -w.im..-z.im, g (z.re + y * Complex.I) from by
      simpa only [Complex.ofReal_neg] using
        (intervalIntegral.integral_comp_neg (a := z.im) (b := w.im)
          (f := fun y : ℝ => g (z.re + y * Complex.I)))]
    rw [intervalIntegral.integral_symm]
  have key1 : (∫ x : ℝ in z.re..w.re, reflectUp g (x + z.im * Complex.I))
      = star (∫ x : ℝ in (star z).re..(star w).re, g (x + (star z).im * Complex.I)) := by
    have hpt : ∀ x : ℝ, reflectUp g (x + z.im * Complex.I)
        = star (g (x + (star z).im * Complex.I)) := by
      intro x
      have him : (x + z.im * Complex.I).im = z.im := by simp
      rw [reflectUp_eq hax (by rw [him]; exact hz)]
      refine congrArg (fun q => star (g q)) ?_
      have hs : star (((z.im : ℝ)) : ℂ) = (((z.im : ℝ)) : ℂ) := star_ofReal z.im
      rw [star_add, star_mul, star_ofReal x, hs, star_I, hzim]
      push_cast
      ring
    simp only [hpt, hzre, hwre]
    rw [star_intervalIntegral (hint_h (star z).im (Set.left_mem_uIcc))]
  have key2 : (∫ x : ℝ in z.re..w.re, reflectUp g (x + w.im * Complex.I))
      = star (∫ x : ℝ in (star z).re..(star w).re, g (x + (star w).im * Complex.I)) := by
    have hpt : ∀ x : ℝ, reflectUp g (x + w.im * Complex.I)
        = star (g (x + (star w).im * Complex.I)) := by
      intro x
      have him : (x + w.im * Complex.I).im = w.im := by simp
      rw [reflectUp_eq hax (by rw [him]; exact hw)]
      refine congrArg (fun q => star (g q)) ?_
      have hs : star (((w.im : ℝ)) : ℂ) = (((w.im : ℝ)) : ℂ) := star_ofReal w.im
      rw [star_add, star_mul, star_ofReal x, hs, star_I, hwim]
      push_cast
      ring
    simp only [hpt, hzre, hwre]
    rw [star_intervalIntegral (hint_h (star w).im (Set.right_mem_uIcc))]
  have key3 : (∫ y : ℝ in z.im..w.im, reflectUp g (w.re + y * Complex.I))
      = -star (∫ y : ℝ in (star z).im..(star w).im, g (w.re + y * Complex.I)) := by
    have hpt : ∀ y ∈ Set.uIcc z.im w.im, reflectUp g (w.re + y * Complex.I)
        = star (g (w.re + (-y) * Complex.I)) := by
      intro y hy
      have him : (w.re + y * Complex.I).im = y := by simp
      rw [reflectUp_eq hax (by rw [him]; exact hy0 y hy)]
      refine congrArg (fun q => star (g q)) ?_
      rw [star_add, star_mul, star_ofReal w.re, star_ofReal y, star_I]
      ring
    have hcongr : (∫ y : ℝ in z.im..w.im, reflectUp g (w.re + y * Complex.I))
        = ∫ y : ℝ in z.im..w.im, star (g (w.re + (-y) * Complex.I)) :=
      intervalIntegral.integral_congr hpt
    rw [hcongr, hzim, hwim, ← star_neg, ← hsub3,
      ← star_intervalIntegral (hint_v w.re (Set.right_mem_uIcc))]
  have key4 : (∫ y : ℝ in z.im..w.im, reflectUp g (z.re + y * Complex.I))
      = -star (∫ y : ℝ in (star z).im..(star w).im, g (z.re + y * Complex.I)) := by
    have hpt : ∀ y ∈ Set.uIcc z.im w.im, reflectUp g (z.re + y * Complex.I)
        = star (g (z.re + (-y) * Complex.I)) := by
      intro y hy
      have him : (z.re + y * Complex.I).im = y := by simp
      rw [reflectUp_eq hax (by rw [him]; exact hy0 y hy)]
      refine congrArg (fun q => star (g q)) ?_
      rw [star_add, star_mul, star_ofReal z.re, star_ofReal y, star_I]
      ring
    have hcongr : (∫ y : ℝ in z.im..w.im, reflectUp g (z.re + y * Complex.I))
        = ∫ y : ℝ in z.im..w.im, star (g (z.re + (-y) * Complex.I)) :=
      intervalIntegral.integral_congr hpt
    rw [hcongr, hzim, hwim, ← star_neg, ← hsub4,
      ← star_intervalIntegral (hint_v z.re (Set.left_mem_uIcc))]
  have hI : ∀ q : ℂ, star (Complex.I * q) = -(Complex.I * star q) := by
    intro q
    rw [star_mul, star_I]; ring
  simp only [rectBoundary]
  rw [key1, key2, key3, key4, hzre, hwre]
  simp only [star_add, star_sub, hI]
  ring

/-- **Splitting a rectangle that crosses the real axis.** -/
lemma rectBoundary_split {f : ℂ → ℂ} {z w : ℂ} (hz : z.im ≤ 0) (hw : 0 ≤ w.im)
    (hzw : z.im ≤ w.im) (hcont : ContinuousOn f (Rectangle z w)) :
    rectBoundary f z w = rectBoundary f z (w.re : ℂ) + rectBoundary f (z.re : ℂ) w := by
  have hzu : ∀ a ∈ Set.uIcc z.im w.im, z.im ≤ a := by
    intro a ha; rw [Set.uIcc_of_le hzw] at ha; exact ha.1
  have hwu : ∀ a ∈ Set.uIcc z.im w.im, a ≤ w.im := by
    intro a ha; rw [Set.uIcc_of_le hzw] at ha; exact ha.2
  have hint_h : ∀ c ∈ Set.uIcc z.im w.im,
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume z.re w.re := by
    intro c hc
    refine ContinuousOn.intervalIntegrable ?_
    refine hcont.comp (by fun_prop) ?_
    intro x hx
    refine ⟨?_, ?_⟩
    · show ((x : ℂ) + (c : ℂ) * Complex.I).re ∈ Set.uIcc z.re w.re
      simpa using hx
    · show ((x : ℂ) + (c : ℂ) * Complex.I).im ∈ Set.uIcc z.im w.im
      simpa using hc
  have hint_v : ∀ c ∈ Set.uIcc z.re w.re, ∀ a ∈ Set.uIcc z.im w.im, ∀ b ∈ Set.uIcc z.im w.im,
      IntervalIntegrable (fun y : ℝ => f ((c : ℂ) + (y : ℂ) * Complex.I)) volume a b := by
    intro c hc a ha b hb
    refine ContinuousOn.intervalIntegrable ?_
    refine hcont.comp (by fun_prop) ?_
    intro y hy
    refine ⟨?_, ?_⟩
    · show ((c : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.uIcc z.re w.re
      simpa using hc
    · have hyim : ((c : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
      show ((c : ℂ) + (y : ℂ) * Complex.I).im ∈ Set.uIcc z.im w.im
      rw [hyim, Set.uIcc_of_le hzw]
      rcases le_total a b with h | h
      · rw [Set.uIcc_of_le h] at hy
        exact ⟨le_trans (hzu a ha) hy.1, le_trans hy.2 (hwu b hb)⟩
      · rw [Set.uIcc_of_ge h] at hy
        exact ⟨le_trans (hzu b hb) hy.1, le_trans hy.2 (hwu a ha)⟩
  have h0 : (0 : ℝ) ∈ Set.uIcc z.im w.im := by rw [Set.uIcc_of_le hzw]; exact ⟨hz, hw⟩
  have e1 : (∫ y : ℝ in z.im..0, f (w.re + y * Complex.I))
      + (∫ y : ℝ in 0..w.im, f (w.re + y * Complex.I))
      = ∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint_v w.re (Set.right_mem_uIcc) z.im (Set.left_mem_uIcc) 0 h0)
      (hint_v w.re (Set.right_mem_uIcc) 0 h0 w.im (Set.right_mem_uIcc))
  have e2 : (∫ y : ℝ in z.im..0, f (z.re + y * Complex.I))
      + (∫ y : ℝ in 0..w.im, f (z.re + y * Complex.I))
      = ∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint_v z.re (Set.left_mem_uIcc) z.im (Set.left_mem_uIcc) 0 h0)
      (hint_v z.re (Set.left_mem_uIcc) 0 h0 w.im (Set.right_mem_uIcc))
  simp only [rectBoundary, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_mul]
  rw [← e1, ← e2]
  ring

/-! ## The reflected function is holomorphic on the ball -/

/-- **Above the axis.**  On a rectangle in the closed upper half-plane the reflected function agrees
with `g`, so its boundary integral vanishes by Cauchy–Goursat. -/
lemma rectBoundary_reflectUp_eq_zero_of_upper {g : ℂ → ℂ} {ρ : ℝ} {z w : ℂ}
    (hcont : ContinuousOn g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}))
    (hdiff : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → DifferentiableAt ℂ g u)
    (hax : ∀ u : ℂ, u.im = 0 → g u = 0)
    (h0 : 0 ≤ z.im) (h0' : 0 ≤ w.im) (hrect : Rectangle z w ⊆ Metric.ball (0 : ℂ) ρ) :
    rectBoundary (reflectUp g) z w = 0 := by
  have hc0 : ∀ c ∈ Set.uIcc z.im w.im, 0 ≤ c := by
    intro c hc
    rw [Set.uIcc, Set.mem_Icc] at hc
    have : 0 ≤ min z.im w.im := le_min h0 h0'
    linarith [hc.1, this]
  have heq : rectBoundary (reflectUp g) z w = rectBoundary g z w := by
    have h1 : ∀ c ∈ Set.uIcc z.im w.im,
        (∫ x : ℝ in z.re..w.re, reflectUp g (x + c * Complex.I))
          = ∫ x : ℝ in z.re..w.re, g (x + c * Complex.I) := by
      intro c hc
      refine intervalIntegral.integral_congr fun x _ => ?_
      have him : ((x : ℂ) + (c : ℂ) * Complex.I).im = c := by simp
      exact reflectUp_eqOn_upper hax (show 0 ≤ ((x : ℂ) + (c : ℂ) * Complex.I).im from by
        rw [him]; exact hc0 c hc)
    have h2 : ∀ c ∈ Set.uIcc z.re w.re,
        (∫ y : ℝ in z.im..w.im, reflectUp g (c + y * Complex.I))
          = ∫ y : ℝ in z.im..w.im, g (c + y * Complex.I) := by
      intro c _
      refine intervalIntegral.integral_congr fun y hy => ?_
      have him : ((c : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
      exact reflectUp_eqOn_upper hax (show 0 ≤ ((c : ℂ) + (y : ℂ) * Complex.I).im from by
        rw [him]; exact hc0 y hy)
    simp only [rectBoundary]
    rw [h1 z.im (Set.left_mem_uIcc), h1 w.im (Set.right_mem_uIcc),
      h2 z.re (Set.left_mem_uIcc), h2 w.re (Set.right_mem_uIcc)]
  rw [heq]
  have hC : ContinuousOn g (Rectangle z w) := by
    refine hcont.mono ?_
    intro u hu
    rw [Rectangle, Complex.mem_reProdIm] at hu
    exact ⟨hrect hu, hc0 u.im hu.2⟩
  have hD : DifferentiableOn ℂ g
      (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im)) := by
    intro u hu
    rw [Complex.mem_reProdIm] at hu
    have huRect : u ∈ Rectangle z w := by
      rw [Rectangle, Complex.mem_reProdIm]
      exact ⟨⟨le_of_lt hu.1.1, le_of_lt hu.1.2⟩, ⟨le_of_lt hu.2.1, le_of_lt hu.2.2⟩⟩
    have hnorm : ‖u‖ < ρ := by
      simpa [Metric.mem_ball, dist_zero_right] using hrect huRect
    have hlt : 0 < u.im := by
      have hmin0 : 0 ≤ min z.im w.im := le_min h0 h0'
      linarith [hu.2.1, hmin0]
    exact (hdiff u hnorm hlt).differentiableWithinAt
  have := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn g z w hC hD
  simpa [rectBoundary, smul_eq_mul] using this

/-- **Below the axis.**  There the reflected function is `star ∘ g ∘ star`; its rectangle integral is
the conjugate of that of `g` over the reflected rectangle, which lies above the axis. -/
lemma rectBoundary_reflectUp_eq_zero_of_lower {g : ℂ → ℂ} {ρ : ℝ} {z w : ℂ}
    (hcont : ContinuousOn g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}))
    (hdiff : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → DifferentiableAt ℂ g u)
    (hax : ∀ u : ℂ, u.im = 0 → g u = 0)
    (hz : z.im ≤ 0) (hw : w.im ≤ 0) (hrect : Rectangle z w ⊆ Metric.ball (0 : ℂ) ρ) :
    rectBoundary (reflectUp g) z w = 0 := by
  have hball : ∀ x ∈ Set.uIcc (star z).re (star w).re, ∀ y ∈ Set.uIcc (star z).im (star w).im,
      ((x : ℂ) + (y : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) ρ := by
    intro x hx y hy
    have hmem : ((x : ℂ) + (y : ℂ) * Complex.I) ∈ Rectangle (star z) (star w) := by
      rw [Rectangle, Complex.mem_reProdIm]
      exact ⟨by simpa using hx, by simpa using hy⟩
    have hstar : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) + (-y) * Complex.I := by
      rw [star_add, star_mul, star_ofReal, star_I, star_ofReal]; ring
    have hb : ((x : ℂ) + (-y) * Complex.I) ∈ Metric.ball (0 : ℂ) ρ := by
      rw [← hstar]; exact hrect ((star_mem_Rectangle).2 hmem)
    have hnorm : ‖(x : ℂ) + (-y) * Complex.I‖ < ρ := by
      simpa [Metric.mem_ball, dist_zero_right] using hb
    have heq : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ = ‖(x : ℂ) + (-y) * Complex.I‖ := by
      rw [← norm_star ((x : ℂ) + (y : ℂ) * Complex.I), hstar]
    rw [Metric.mem_ball, dist_zero_right, heq]
    exact hnorm
  rw [rectBoundary_reflectUp_of_mem_ball hz hw hax hcont hball]
  have hC : ContinuousOn g (Rectangle (star z) (star w)) := by
    refine hcont.mono ?_
    intro u hu
    rw [Rectangle, Complex.mem_reProdIm] at hu
    have hmem : star u ∈ Rectangle z w := (star_mem_Rectangle).2 (by
      rw [Rectangle, Complex.mem_reProdIm]
      exact hu)
    have hb : star u ∈ Metric.ball (0 : ℂ) ρ := hrect hmem
    have hb' : ‖star u‖ < ρ := by rwa [Metric.mem_ball, dist_zero_right] at hb
    refine ⟨?_, ?_⟩
    · show u ∈ Metric.ball (0 : ℂ) ρ
      rw [Metric.mem_ball, dist_zero_right]
      rwa [show ‖u‖ = ‖star u‖ from by simp]
    · show 0 ≤ u.im
      have h1 := hu.2.1
      have hzi : (star z).im = -z.im := by simp
      have hwi : (star w).im = -w.im := by simp
      rw [hzi, hwi] at h1
      have h2 : 0 ≤ min (-z.im) (-w.im) := le_min (by linarith) (by linarith)
      linarith [h1, h2]
  have hD : DifferentiableOn ℂ g
      (Set.Ioo (min (star z).re (star w).re) (max (star z).re (star w).re) ×ℂ
        Set.Ioo (min (star z).im (star w).im) (max (star z).im (star w).im)) := by
    intro u hu
    rw [Complex.mem_reProdIm] at hu
    have huRect : u ∈ Rectangle (star z) (star w) := by
      rw [Rectangle, Complex.mem_reProdIm]
      exact ⟨⟨le_of_lt hu.1.1, le_of_lt hu.1.2⟩, ⟨le_of_lt hu.2.1, le_of_lt hu.2.2⟩⟩
    have hmem : star u ∈ Rectangle z w := (star_mem_Rectangle).2 huRect
    have hb : star u ∈ Metric.ball (0 : ℂ) ρ := hrect hmem
    have hnorm : ‖u‖ < ρ := by
      rw [Metric.mem_ball, dist_zero_right] at hb
      rwa [norm_star] at hb
    have hlt : 0 < u.im := by
      have h1 := hu.2.1
      have hzi : (star z).im = -z.im := by simp
      have hwi : (star w).im = -w.im := by simp
      rw [hzi, hwi] at h1
      have h2 : 0 ≤ min (-z.im) (-w.im) := le_min (by linarith) (by linarith)
      linarith [h1, h2]
    exact (hdiff u hnorm hlt).differentiableWithinAt
  have hzr : rectBoundary g (star z) (star w) = 0 := by
    have := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      g (star z) (star w) hC hD
    simpa [rectBoundary, smul_eq_mul] using this
  rw [hzr, star_zero]

/-- **The rectangle integral of the reflected function vanishes on the ball.** -/
lemma rectBoundary_reflectUp_eq_zero {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}))
    (hdiff : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → DifferentiableAt ℂ g u)
    (hax : ∀ u : ℂ, u.im = 0 → g u = 0) :
    ∀ z w : ℂ, Rectangle z w ⊆ Metric.ball (0 : ℂ) ρ → rectBoundary (reflectUp g) z w = 0 := by
  have key : ∀ z w : ℂ, z.im < 0 → 0 ≤ w.im → Rectangle z w ⊆ Metric.ball (0 : ℂ) ρ →
      rectBoundary (reflectUp g) z w = 0 := by
    intro z w hzneg hwpos hrect
    have hzneg' : z.im ≤ 0 := le_of_lt hzneg
    have hzw : z.im ≤ w.im := le_trans hzneg' hwpos
    have hCcont : ContinuousOn (reflectUp g) (Metric.ball (0 : ℂ) ρ) :=
      continuousOn_reflectUp hρ hdiff hcont hax
    rw [rectBoundary_split hzneg' hwpos hzw (hCcont.mono hrect)]
    have hsub₁ : Rectangle z ((w.re : ℂ)) ⊆ Metric.ball (0 : ℂ) ρ := by
      intro u hu
      refine hrect ?_
      rw [Rectangle, Complex.mem_reProdIm] at hu ⊢
      refine ⟨hu.1, ?_⟩
      have h1 : u.im ∈ Set.Icc z.im 0 := by simpa [Set.uIcc_of_le hzneg'] using hu.2
      rw [Set.uIcc_of_le hzw]
      exact ⟨h1.1, le_trans h1.2 hwpos⟩
    have hsub₂ : Rectangle ((z.re : ℂ)) w ⊆ Metric.ball (0 : ℂ) ρ := by
      intro u hu
      refine hrect ?_
      rw [Rectangle, Complex.mem_reProdIm] at hu ⊢
      refine ⟨hu.1, ?_⟩
      have h1 : u.im ∈ Set.Icc 0 w.im := by simpa [Set.uIcc_of_le hwpos] using hu.2
      rw [Set.uIcc_of_le hzw]
      exact ⟨le_trans hzneg' h1.1, h1.2⟩
    rw [rectBoundary_reflectUp_eq_zero_of_lower hcont hdiff hax hzneg' (by simp) hsub₁,
      rectBoundary_reflectUp_eq_zero_of_upper hcont hdiff hax (by simp) hwpos hsub₂, add_zero]
  intro z w hrect
  by_cases hz0 : 0 ≤ z.im
  · by_cases hw0 : 0 ≤ w.im
    · exact rectBoundary_reflectUp_eq_zero_of_upper hcont hdiff hax hz0 hw0 hrect
    · rw [rectBoundary_symm (reflectUp g) z w]
      refine key w z (not_le.mp hw0) hz0 ?_
      rwa [← Rectangle_comm]
  · by_cases hw0 : 0 ≤ w.im
    · exact key z w (not_le.mp hz0) hw0 hrect
    · exact rectBoundary_reflectUp_eq_zero_of_lower hcont hdiff hax
        (le_of_lt (not_le.mp hz0)) (le_of_lt (not_le.mp hw0)) hrect

/-- The reflected function is conservative on the ball. -/
lemma isConservativeOn_reflectUp {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}))
    (hdiff : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → DifferentiableAt ℂ g u)
    (hax : ∀ u : ℂ, u.im = 0 → g u = 0) :
    IsConservativeOn (reflectUp g) (Metric.ball (0 : ℂ) ρ) := by
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  have hkey := rectBoundary_reflectUp_eq_zero hρ hcont hdiff hax z w hzw
  simpa [rectBoundary, smul_eq_mul] using hkey

/-- **Boundary uniqueness, half-plane form (global vanishing on the axis).** -/
theorem half_plane_eq_zero_of_global {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hgdiff : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → DifferentiableAt ℂ g u)
    (hgcont : ContinuousOn g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}))
    (hax : ∀ u : ℂ, u.im = 0 → g u = 0) :
    ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → g u = 0 := by
  have hCcont : ContinuousOn (reflectUp g) (Metric.ball (0 : ℂ) ρ) :=
    continuousOn_reflectUp hρ hgdiff hgcont hax
  have hcons : IsConservativeOn (reflectUp g) (Metric.ball (0 : ℂ) ρ) :=
    isConservativeOn_reflectUp hρ hgcont hgdiff hax
  have hdiff : DifferentiableOn ℂ (reflectUp g) (Metric.ball (0 : ℂ) ρ) :=
    (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_ball).1 ⟨hcons, hCcont⟩
  have hana : AnalyticOnNhd ℂ (reflectUp g) (Metric.ball (0 : ℂ) ρ) :=
    hdiff.analyticOnNhd isOpen_ball
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) ρ) := (convex_ball (0 : ℂ) ρ).isPreconnected
  have hz₀ : (((ρ / 2 : ℝ)) : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]
    have h2 : ‖(((ρ / 2 : ℝ)) : ℂ)‖ ^ 2 = (ρ / 2) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    nlinarith [h2, norm_nonneg (((ρ / 2 : ℝ)) : ℂ), hρ]
  have hclos : (((ρ / 2 : ℝ)) : ℂ) ∈
      closure ({u : ℂ | reflectUp g u = 0} \ {(((ρ / 2 : ℝ)) : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(((ρ / 2 + ε / 2 : ℝ)) : ℂ), ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · show reflectUp g (((ρ / 2 + ε / 2 : ℝ)) : ℂ) = 0
        rw [reflectUp_of_zero (by simp)]
      · simp only [Set.mem_singleton_iff, Complex.ofReal_inj]
        linarith
    · rw [dist_eq_norm, ← Complex.ofReal_sub]
      have h2 : ‖(((ρ / 2 - (ρ / 2 + ε / 2) : ℝ)) : ℂ)‖ ^ 2 = (ρ / 2 - (ρ / 2 + ε / 2)) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      have h3 : ‖(((ρ / 2 - (ρ / 2 + ε / 2) : ℝ)) : ℂ)‖ = -(ρ / 2 - (ρ / 2 + ε / 2)) := by
        nlinarith [h2, norm_nonneg (((ρ / 2 - (ρ / 2 + ε / 2) : ℝ)) : ℂ), hε]
      rw [h3]
      linarith
  have hzero' : ∀ u ∈ Metric.ball (0 : ℂ) ρ, reflectUp g u = 0 :=
    hana.eqOn_zero_of_preconnected_of_mem_closure hpre hz₀ hclos
  intro u hu hui
  have h1 : reflectUp g u = 0 := hzero' u (by rwa [Metric.mem_ball, dist_zero_right])
  rwa [reflectUp_of_pos hui] at h1

/-- **Boundary uniqueness, half-plane form.**  A function holomorphic on the upper half of a ball,
continuous up to the axis, and vanishing on the axis of the ball, vanishes on the upper half of the
ball. -/
theorem half_plane_eq_zero {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hgdiff : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → DifferentiableAt ℂ g u)
    (hgcont : ContinuousOn g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}))
    (hzero : ∀ u : ℂ, ‖u‖ < ρ → u.im = 0 → g u = 0) :
    ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → g u = 0 := by
  set G : ℂ → ℂ := fun u => if ‖u‖ < ρ then g u else 0 with hG
  have hGeq : ∀ u : ℂ, ‖u‖ < ρ → G u = g u := by
    intro u hu
    simp only [hG]
    rw [if_pos hu]
  have hGax : ∀ u : ℂ, u.im = 0 → G u = 0 := by
    intro u hu
    by_cases h : ‖u‖ < ρ
    · rw [hGeq u h, hzero u h hu]
    · simp only [hG]
      rw [if_neg h]
  have hGdiff : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → DifferentiableAt ℂ G u := by
    intro u hu hui
    have hmem : u ∈ Metric.ball (0 : ℂ) ρ := by rwa [Metric.mem_ball, dist_zero_right]
    have hev : G =ᶠ[𝓝 u] g := by
      filter_upwards [isOpen_ball.mem_nhds hmem] with v hv
      exact hGeq v (by rwa [Metric.mem_ball, dist_zero_right] at hv)
    exact (hev.differentiableAt_iff).2 (hgdiff u hu hui)
  have hGcont : ContinuousOn G (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}) := by
    refine hgcont.congr ?_
    intro u hu
    exact hGeq u (by simpa [Metric.mem_ball, dist_zero_right] using hu.1)
  have hres := half_plane_eq_zero_of_global hρ hGdiff hGcont hGax
  intro u hu hui
  rw [← hGeq u hu]
  exact hres u hu hui

end Work.Smooth.SphereJordan.Caratheodory
