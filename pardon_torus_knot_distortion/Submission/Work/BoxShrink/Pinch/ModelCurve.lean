import Mathlib
import Submission.Work.CoreTopology.All

/-!
# The model curve: the circle `{x = 5/2} ∩ F` of the standard torus

This module constructs, explicitly, the simple closed curves of the standard torus of revolution
`F = standard.carrier` cut out by the plane `{x = ±5/2}`, and proves everything about them which
the model case of the pinch needs (`Work.BoxShrink.Pinch.isCircleUnion_sphereSet_model`):

* `mdPhi t = (π/3)·sin t` and `mdTheta t = ±arccos (5/(2(2 + cos (mdPhi t))))` parametrise the
  ("longitude", "meridian") parameters of the curve `F ∩ {x = 5/2}`: the key identity
  `x_coord` is `(2 + cos (mdPhi t)) · cos (mdTheta t) = 5/2`, so that `mdGamma t = psi (mdTheta t)
  (mdPhi t)` runs through the whole circle `F ∩ {x = 5/2}` (`exists_mdGamma_eq`), and the
  reflected curve `mdGammaMinus t = psi (mdTheta t + π) (mdPhi t)` runs through `F ∩ {x = -5/2}`
  (`exists_mdGammaMinus_eq`);
* `injOn_mdTheta_mdPhi`: the parameter map `(mdTheta, mdPhi)` is injective on a fundamental period,
  which (with the range bounds `|mdTheta| ≤ mdC < π` and `|mdPhi| ≤ mdB < π`) makes both curves
  simple closed curves of the torus;
* `continuous_mdTheta`: the parameter `mdTheta` is continuous, although it is defined by a
  sign-conditional `arccos`; the general principle (`continuous_ite_sign_mul`) is that a function
  `t ↦ if 0 ≤ p t then a t else -a t` with `a`, `p` continuous and `a` vanishing where `p` does is
  continuous.

The mathematical content in one line: on the standard torus `psi θ φ = ((2 + cos φ) cos θ, ...)`,
the plane `x = 5/2` meets the torus in the circle where `(2 + cos φ)·cos θ = 5/2`; since
`2 + cos φ ∈ [1,3]` this forces `cos φ ≥ 1/2`, i.e. `|φ| ≤ π/3`, and for each such `φ` the two
longitude parameters `θ = ±arccos (5/(2(2 + cos φ)))` are the two points of the circle.  The
parametrisation above runs through the four arcs of that circle, the sign of `mdTheta` switching
exactly where `arccos (5/(2(2 + cos (mdPhi t))))` vanishes (at `|sin t| = 1`), which is what makes
it continuous.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-! ## The definitions -/

/-- `π/3`: the half-width of the meridian parameter of the model curve. -/
def mdB : ℝ := Real.pi / 3

/-- `arccos (5/6)`: the half-width of the longitude parameter of the model curve. -/
def mdC : ℝ := Real.arccos (5 / 6)

/-- The meridian parameter of the model curve. -/
def mdPhi (t : ℝ) : ℝ := mdB * Real.sin t

/-- The argument of the `arccos` defining the longitude parameter. -/
def mdD (t : ℝ) : ℝ := 5 / (2 * (2 + Real.cos (mdPhi t)))

/-- The longitude parameter of the model curve. -/
def mdTheta (t : ℝ) : ℝ :=
  if 0 ≤ Real.cos t then Real.arccos (mdD t) else -Real.arccos (mdD t)

/-- The point of the standard torus with parameters `(mdTheta t, mdPhi t)`: it runs through the
circle `F ∩ {x = 5/2}`. -/
def mdGamma : ℝ → R3 :=
  (fun p : ℝ × ℝ => Work.CoreTopology.standard.psi p.1 p.2) ∘
    (fun t : ℝ => (mdTheta t, mdPhi t))

/-- The reflected curve: it runs through the circle `F ∩ {x = -5/2}`. -/
def mdGammaMinus : ℝ → R3 :=
  (fun p : ℝ × ℝ => Work.CoreTopology.standard.psi p.1 p.2) ∘
    (fun t : ℝ => (mdTheta t + Real.pi, mdPhi t))

@[simp] theorem mdGamma_apply (t : ℝ) :
    mdGamma t = Work.CoreTopology.standard.psi (mdTheta t) (mdPhi t) := rfl

@[simp] theorem mdGammaMinus_apply (t : ℝ) :
    mdGammaMinus t = Work.CoreTopology.standard.psi (mdTheta t + Real.pi) (mdPhi t) := rfl

/-! ## Elementary bounds -/

theorem mdB_pos : 0 < mdB := by unfold mdB; positivity

theorem mdB_lt_pi : mdB < Real.pi := by unfold mdB; linarith [Real.pi_pos]

theorem mdB_ne_zero : mdB ≠ 0 := ne_of_gt mdB_pos

theorem cos_mdB : Real.cos mdB = 1 / 2 := by rw [mdB, Real.cos_pi_div_three]

theorem mdC_pos : 0 < mdC := by rw [mdC, Real.arccos_pos]; norm_num

theorem mdC_lt_pi : mdC < Real.pi := by rw [mdC, Real.arccos_lt_pi]; norm_num

theorem abs_mdPhi_le (t : ℝ) : |mdPhi t| ≤ mdB := by
  rw [mdPhi, abs_mul, abs_of_pos mdB_pos]
  nlinarith [Real.abs_sin_le_one t, mdB_pos]

theorem mdPhi_mem_Icc (t : ℝ) : mdPhi t ∈ Set.Icc (-Real.pi) Real.pi := by
  have habs := abs_le.mp (abs_mdPhi_le t)
  have hb := mdB_lt_pi
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

theorem cos_mdPhi_mem (t : ℝ) : Real.cos (mdPhi t) ∈ Set.Icc (1 / 2) 1 := by
  constructor
  · have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := |mdPhi t|) (y := mdB)
      (abs_nonneg _) (le_of_lt mdB_lt_pi) (abs_mdPhi_le t)
    rw [Real.cos_abs, cos_mdB] at h
    exact h
  · exact Real.cos_le_one _

theorem mdD_mem (t : ℝ) : mdD t ∈ Set.Icc (5 / 6) 1 := by
  have h1 := (cos_mdPhi_mem t).1
  have hpos : 0 < 2 * (2 + Real.cos (mdPhi t)) := by linarith
  constructor
  · rw [mdD, le_div_iff₀ hpos]; linarith [(cos_mdPhi_mem t).2]
  · rw [mdD, div_le_iff₀ hpos]; linarith [(cos_mdPhi_mem t).1]

/-- A pure trigonometry fact: for `x` in `[-π, π]`, `cos x ≥ 1/2` forces `|x| ≤ π/3`. -/
theorem cos_half_iff (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    1 / 2 ≤ Real.cos x ↔ |x| ≤ Real.pi / 3 := by
  have hxabs : |x| ≤ Real.pi := abs_le.mpr ⟨hx.1, hx.2⟩
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h2 : Real.cos |x| < Real.cos (Real.pi / 3) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 3) (y := |x|)
        (by positivity) hxabs hc
    rw [Real.cos_abs, Real.cos_pi_div_three] at h2
    linarith
  · intro h
    have h2 : Real.cos (Real.pi / 3) ≤ Real.cos |x| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith [Real.pi_pos]) h
    rw [Real.cos_abs, Real.cos_pi_div_three] at h2
    linarith

/-- The strict version: for `x` in `[-π, π]`, `cos x > 1/2` forces `|x| < π/3`. -/
theorem half_lt_cos_iff (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    1 / 2 < Real.cos x ↔ |x| < Real.pi / 3 := by
  have hxabs : |x| ≤ Real.pi := abs_le.mpr ⟨hx.1, hx.2⟩
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h2 : Real.cos |x| ≤ Real.cos (Real.pi / 3) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 3) (y := |x|)
        (by positivity) hxabs hc
    rw [Real.cos_abs, Real.cos_pi_div_three] at h2
    linarith
  · intro h
    have h2 : Real.cos (Real.pi / 3) < Real.cos |x| :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith [Real.pi_pos]) h
    rw [Real.cos_abs, Real.cos_pi_div_three] at h2
    linarith

theorem abs_mdTheta (t : ℝ) : |mdTheta t| = Real.arccos (mdD t) := by
  rw [mdTheta]
  split_ifs with h
  · exact abs_of_nonneg (Real.arccos_nonneg _)
  · rw [abs_neg, abs_of_nonneg (Real.arccos_nonneg _)]

theorem cos_mdTheta (t : ℝ) : Real.cos (mdTheta t) = mdD t := by
  have h1 := (mdD_mem t).1
  have h2 := (mdD_mem t).2
  rw [mdTheta]
  split_ifs with h
  · exact Real.cos_arccos (by linarith) (by linarith)
  · rw [Real.cos_neg]; exact Real.cos_arccos (by linarith) (by linarith)

theorem abs_mdTheta_le (t : ℝ) : |mdTheta t| ≤ mdC := by
  have h : Real.arccos (mdD t) ≤ Real.arccos (5 / 6) :=
    Real.arccos_le_arccos (mdD_mem t).1
  rw [abs_mdTheta]
  exact h

/-- `mdD t < 1` exactly when `mdTheta` does not vanish, i.e. when `cos t ≠ 0`. -/
theorem mdD_lt_one_iff (t : ℝ) : mdD t < 1 ↔ Real.cos t ≠ 0 := by
  have hpos : 0 < 2 * (2 + Real.cos (mdPhi t)) := by
    have h1 := (cos_mdPhi_mem t).1
    linarith
  rw [mdD, div_lt_iff₀ hpos, one_mul]
  have h1 : 5 < 2 * (2 + Real.cos (mdPhi t)) ↔ 1 / 2 < Real.cos (mdPhi t) := by
    constructor <;> intro h <;> linarith
  rw [h1, half_lt_cos_iff (mdPhi t) (mdPhi_mem_Icc t),
    show Real.pi / 3 = mdB from rfl, mdPhi, abs_mul, abs_of_pos mdB_pos]
  constructor
  · intro h
    rw [mul_lt_iff_lt_one_right mdB_pos] at h
    intro hc
    have h5 : Real.sin t ^ 2 = 1 := by
      have h4 := Real.sin_sq_add_cos_sq t
      have h7 : Real.cos t ^ 2 = 0 := by rw [hc]; norm_num
      linarith
    have h6 : |Real.sin t| = 1 := by
      rw [← Real.sqrt_sq_eq_abs, h5]; norm_num
    linarith
  · intro h
    rw [mul_lt_iff_lt_one_right mdB_pos]
    by_contra hc
    push Not at hc
    have hs1 : |Real.sin t| = 1 := le_antisymm (Real.abs_sin_le_one t) hc
    have h5 : Real.sin t ^ 2 = 1 := by rw [← sq_abs, hs1]; norm_num
    have h6 : Real.cos t ^ 2 = 0 := by
      have h4 := Real.sin_sq_add_cos_sq t
      rw [h5] at h4; linarith
    exact h (sq_eq_zero_iff.mp h6)

/-- **The sign of `mdTheta` is the sign of `cos t`.** -/
theorem mdTheta_nonneg_iff (t : ℝ) : 0 ≤ mdTheta t ↔ 0 ≤ Real.cos t := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [mdTheta, if_neg (not_le.mpr hc)] at h
    have h1 : Real.arccos (mdD t) = 0 := le_antisymm (by linarith) (Real.arccos_nonneg _)
    have h2 : 1 ≤ mdD t := Real.arccos_eq_zero.mp h1
    have h3 : mdD t = 1 := le_antisymm (mdD_mem t).2 h2
    have h4 : mdD t < 1 := (mdD_lt_one_iff t).mpr (ne_of_lt hc)
    linarith
  · intro h
    rw [mdTheta, if_pos h]
    exact Real.arccos_nonneg _

/-- **The defining identity of the model curve**: the point `(mdTheta t, mdPhi t)` of the parameter
plane lies on the level set `(2 + cos φ)·cos θ = 5/2`, i.e. on the circle `F ∩ {x = 5/2}`. -/
theorem x_coord (t : ℝ) : (2 + Real.cos (mdPhi t)) * Real.cos (mdTheta t) = 5 / 2 := by
  have hpos : 0 < 2 + Real.cos (mdPhi t) := by
    have h1 := (cos_mdPhi_mem t).1
    linarith
  rw [cos_mdTheta, mdD]
  field_simp

/-! ## Continuity and periodicity -/

/-- **A general continuity principle.**  If `a` and `p` are continuous and `a` vanishes wherever
`p` does, then the sign-corrected function `t ↦ if 0 ≤ p t then a t else -a t` is continuous:
away from the zeros of `p` the sign is locally constant, and at a zero of `p` the value is `0` and
the function is squeezed by `|a|`. -/
theorem continuous_ite_sign_mul {a p : ℝ → ℝ} (ha : Continuous a) (hp : Continuous p)
    (h0 : ∀ t, p t = 0 → a t = 0) :
    Continuous fun t => if 0 ≤ p t then a t else -a t := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rcases lt_trichotomy (p t₀) 0 with hlt | heq | hgt
  · have hloc : (fun t => if 0 ≤ p t then a t else -a t) =ᶠ[nhds t₀] fun t => -a t := by
      filter_upwards [(isOpen_lt hp continuous_const).mem_nhds hlt] with t ht
      rw [if_neg (not_le.mpr ht)]
    exact (ha.neg.continuousAt).congr hloc.symm
  · have hzero : a t₀ = 0 := h0 t₀ heq
    have hf0 : (if 0 ≤ p t₀ then a t₀ else -a t₀) = 0 := by
      rw [if_pos (le_of_eq heq.symm), hzero]
    have hA : Filter.Tendsto (fun t => ‖a t - a t₀‖) (nhds t₀) (nhds 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp ha.continuousAt
    have hfun : (fun t => ‖(if 0 ≤ p t then a t else -a t) - 0‖) = fun t => ‖a t - a t₀‖ := by
      funext t
      rw [sub_zero, hzero, sub_zero]
      by_cases h : 0 ≤ p t
      · rw [if_pos h]
      · rw [if_neg h, norm_neg]
    change Filter.Tendsto (fun t => if 0 ≤ p t then a t else -a t) (nhds t₀)
      (nhds ((fun t => if 0 ≤ p t then a t else -a t) t₀))
    rw [show (fun t => if 0 ≤ p t then a t else -a t) t₀ = 0 from hf0]
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (hfun ▸ hA)
  · have hloc : (fun t => if 0 ≤ p t then a t else -a t) =ᶠ[nhds t₀] fun t => a t := by
      filter_upwards [(isOpen_lt continuous_const hp).mem_nhds hgt] with t ht
      rw [if_pos (le_of_lt ht)]
    exact ha.continuousAt.congr hloc.symm

theorem continuous_mdPhi : Continuous mdPhi := by
  rw [show mdPhi = fun t : ℝ => mdB * Real.sin t from rfl]
  fun_prop

theorem continuous_mdD : Continuous mdD := by
  rw [show mdD = fun t : ℝ => 5 / (2 * (2 + Real.cos (mdPhi t))) from rfl]
  exact continuous_const.div (continuous_const.mul (continuous_const.add
    (Real.continuous_cos.comp continuous_mdPhi))) (fun t => by
      have h1 := (cos_mdPhi_mem t).1
      positivity)

theorem continuous_mdTheta : Continuous mdTheta := by
  have ha : Continuous fun t : ℝ => Real.arccos (mdD t) :=
    Real.continuous_arccos.comp continuous_mdD
  have hp : Continuous fun t : ℝ => Real.cos t := Real.continuous_cos
  have h0 : ∀ t : ℝ, Real.cos t = 0 → Real.arccos (mdD t) = 0 := by
    intro t ht
    have h1 : mdD t = 1 := by
      rcases lt_or_ge (mdD t) 1 with h | h
      · exact absurd ht ((mdD_lt_one_iff t).mp h)
      · exact le_antisymm (mdD_mem t).2 h
    rw [h1, Real.arccos_one]
  exact continuous_ite_sign_mul ha hp h0

theorem mdPhi_periodic (t : ℝ) : mdPhi (t + 2 * Real.pi) = mdPhi t := by
  rw [mdPhi, mdPhi, show t + 2 * Real.pi = t + (1 : ℤ) * (2 * Real.pi) from by norm_num,
    Real.sin_add_int_mul_two_pi]

theorem mdD_periodic (t : ℝ) : mdD (t + 2 * Real.pi) = mdD t := by
  rw [mdD, mdD, mdPhi_periodic]

theorem mdTheta_periodic (t : ℝ) : mdTheta (t + 2 * Real.pi) = mdTheta t := by
  have h1 : Real.cos (t + 2 * Real.pi) = Real.cos t := by
    rw [show t + 2 * Real.pi = t + (1 : ℤ) * (2 * Real.pi) from by norm_num,
      Real.cos_add_int_mul_two_pi]
  rw [mdTheta, mdTheta, h1, mdD_periodic]

theorem continuous_mdGamma : Continuous mdGamma := by
  have h1 : Continuous (fun t : ℝ => (mdTheta t, mdPhi t)) :=
    continuous_mdTheta.prodMk continuous_mdPhi
  have h2 : Continuous (fun p : ℝ × ℝ => Work.CoreTopology.standard.psi p.1 p.2) :=
    Work.CoreTopology.standard.cont
  exact h2.comp h1

theorem continuous_mdGammaMinus : Continuous mdGammaMinus := by
  have h1 : Continuous (fun t : ℝ => (mdTheta t + Real.pi, mdPhi t)) :=
    (continuous_mdTheta.add continuous_const).prodMk continuous_mdPhi
  have h2 : Continuous (fun p : ℝ × ℝ => Work.CoreTopology.standard.psi p.1 p.2) :=
    Work.CoreTopology.standard.cont
  exact h2.comp h1

theorem mdGamma_periodic (t : ℝ) : mdGamma (t + 2 * Real.pi) = mdGamma t := by
  rw [mdGamma_apply, mdGamma_apply, mdTheta_periodic, mdPhi_periodic]

theorem mdGammaMinus_periodic (t : ℝ) : mdGammaMinus (t + 2 * Real.pi) = mdGammaMinus t := by
  rw [mdGammaMinus_apply, mdGammaMinus_apply, mdTheta_periodic, mdPhi_periodic]

theorem mdGamma_mem (t : ℝ) : mdGamma t ∈ Work.CoreTopology.standard.carrier := by
  rw [mdGamma_apply]
  exact Work.CoreTopology.standard.psi_mem_carrier (mdTheta t) (mdPhi t)

theorem mdGammaMinus_mem (t : ℝ) : mdGammaMinus t ∈ Work.CoreTopology.standard.carrier := by
  rw [mdGammaMinus_apply]
  exact Work.CoreTopology.standard.psi_mem_carrier (mdTheta t + Real.pi) (mdPhi t)

/-! ## Injectivity of the parameter map -/

theorem injOn_mdTheta_mdPhi :
    Set.InjOn (fun t : ℝ => (mdTheta t, mdPhi t)) (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht t' ht' h
  rw [Set.mem_Ico] at ht ht'
  have h1 : mdTheta t = mdTheta t' := congrArg Prod.fst h
  have h2 : mdPhi t = mdPhi t' := congrArg Prod.snd h
  have h3 : Real.sin t = Real.sin t' := by
    have hh := h2
    rw [mdPhi] at hh
    exact mul_left_cancel₀ mdB_ne_zero hh
  have h4 : Real.cos t ^ 2 = Real.cos t' ^ 2 := by
    have h5 : Real.sin t ^ 2 = Real.sin t' ^ 2 := by rw [h3]
    have h6 := Real.sin_sq_add_cos_sq t
    have h7 := Real.sin_sq_add_cos_sq t'
    linarith
  have h5 : Real.cos t = Real.cos t' := by
    have h6 : |Real.cos t| = |Real.cos t'| := by
      have hh : |Real.cos t| ^ 2 = |Real.cos t'| ^ 2 := by rw [sq_abs, sq_abs, h4]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with hh' | hh'
      · exact hh'
      · have h7 : |Real.cos t| = 0 := by
          linarith [abs_nonneg (Real.cos t), abs_nonneg (Real.cos t')]
        have h8 : |Real.cos t'| = 0 := by
          linarith [abs_nonneg (Real.cos t), abs_nonneg (Real.cos t')]
        rw [h7, h8]
    have h7 : (0 ≤ Real.cos t) ↔ (0 ≤ Real.cos t') := by
      rw [← mdTheta_nonneg_iff t, ← mdTheta_nonneg_iff t', h1]
    rcases lt_or_ge (Real.cos t) 0 with hh | hh
    · have h8 : Real.cos t' < 0 := by
        by_contra hc
        push Not at hc
        exact absurd (h7.mpr hc) (by linarith)
      rw [abs_of_neg hh, abs_of_neg h8] at h6; linarith
    · have h8 : 0 ≤ Real.cos t' := h7.mp hh
      rw [abs_of_nonneg hh, abs_of_nonneg h8] at h6; exact h6
  obtain ⟨k, hk⟩ := (Work.Core.cos_sin_eq_iff_exists_int t t').mp ⟨h5, h3⟩
  have h10 : t - t' = (k : ℝ) * (2 * Real.pi) := by linarith
  have h11 : |t - t'| < 2 * Real.pi := by
    rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
  have hk0 : k = 0 := by
    by_contra hkne
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hkne
    have h12 : 2 * Real.pi ≤ |t - t'| := by
      rw [h10, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    linarith
  rw [hk0] at hk
  simpa using hk

/-! ## Surjectivity: every point of the two circles is hit -/

theorem exists_mdGamma_eq (θ φ : ℝ) (h : (2 + Real.cos φ) * Real.cos θ = 5 / 2) :
    ∃ t : ℝ, mdGamma t = Work.CoreTopology.standard.psi θ φ := by
  have hcosφ : 1 / 2 ≤ Real.cos φ := by
    have h2 : (0:ℝ) < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
    nlinarith [h, Real.cos_le_one θ]
  have hcosθ : Real.cos θ = 5 / (2 * (2 + Real.cos φ)) := by
    rw [eq_div_iff (by positivity)]; linarith
  obtain ⟨ψ, m, hψmem, hψcos, hψsin, hψeq⟩ :
      ∃ (ψ : ℝ) (m : ℤ), ψ ∈ Set.Icc (-mdB) mdB ∧ Real.cos ψ = Real.cos φ ∧
        Real.sin ψ = Real.sin φ ∧ ψ = φ + (m : ℝ) * (2 * Real.pi) := by
    set m₀ : ℤ := round (φ / (2 * Real.pi)) with hm
    refine ⟨φ - (m₀ : ℝ) * (2 * Real.pi), -m₀, ?_, ?_, ?_, ?_⟩
    · have hψabs : |φ - (m₀ : ℝ) * (2 * Real.pi)| ≤ Real.pi := by
        have h1 := abs_sub_round (φ / (2 * Real.pi))
        rw [← hm] at h1
        have h3 : (φ / (2 * Real.pi) - (m₀ : ℝ)) * (2 * Real.pi) =
            φ - (m₀ : ℝ) * (2 * Real.pi) := by
          rw [sub_mul, div_mul_cancel₀ _ (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
        have h4 : |φ - (m₀ : ℝ) * (2 * Real.pi)| =
            |φ / (2 * Real.pi) - (m₀ : ℝ)| * (2 * Real.pi) := by
          rw [← h3, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        rw [h4]
        calc |φ / (2 * Real.pi) - (m₀ : ℝ)| * (2 * Real.pi) ≤ (1 / 2) * (2 * Real.pi) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = Real.pi := by ring
      have hψIcc : φ - (m₀ : ℝ) * (2 * Real.pi) ∈ Set.Icc (-Real.pi) Real.pi :=
        abs_le.mp hψabs
      have h5 : 1 / 2 ≤ Real.cos (φ - (m₀ : ℝ) * (2 * Real.pi)) := by
        rw [Real.cos_sub_int_mul_two_pi]; exact hcosφ
      have h6 : |φ - (m₀ : ℝ) * (2 * Real.pi)| ≤ Real.pi / 3 :=
        (cos_half_iff _ hψIcc).mp h5
      rw [show Real.pi / 3 = mdB from rfl] at h6
      exact abs_le.mp h6
    · rw [Real.cos_sub_int_mul_two_pi]
    · rw [Real.sin_sub_int_mul_two_pi]
    · simp only [Int.cast_neg]; ring
  have hψabs : |ψ| ≤ mdB := abs_le.mpr hψmem
  set t : ℝ := Real.arcsin (ψ / mdB) with ht
  have htmem : |ψ / mdB| ≤ 1 := by
    rw [abs_div, abs_of_pos mdB_pos, div_le_iff₀ mdB_pos]
    simpa using hψabs
  have hsin_t : Real.sin t = ψ / mdB := by
    rw [ht]
    exact Real.sin_arcsin (abs_le.mp htmem).1 (abs_le.mp htmem).2
  have hmdPhi_t : mdPhi t = ψ := by
    rw [mdPhi, hsin_t, mul_div_cancel₀ _ mdB_ne_zero]
  have hcos_t : 0 ≤ Real.cos t := by
    rw [ht]
    exact Real.cos_nonneg_of_mem_Icc
      ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have hmdTheta_t : mdTheta t = Real.arccos (mdD t) := by rw [mdTheta, if_pos hcos_t]
  have hmdD_t : mdD t = Real.cos θ := by
    rw [mdD, hmdPhi_t, hψcos]; exact hcosθ.symm
  by_cases hsinθ : 0 ≤ Real.sin θ
  · refine ⟨t, ?_⟩
    rw [mdGamma_apply]
    refine (Work.CoreTopology.standard.psi_eq_iff (mdTheta t) (mdPhi t) θ φ).mpr ⟨?_, ?_⟩
    · have hcos_eq : Real.cos (mdTheta t) = Real.cos θ := by rw [cos_mdTheta, hmdD_t]
      have hsin_eq : Real.sin (mdTheta t) = Real.sin θ := by
        rw [hmdTheta_t, Real.sin_arccos]
        have h2 : Real.sqrt (1 - (mdD t) ^ 2) = Real.sin θ := by
          rw [hmdD_t,
            show (1:ℝ) - Real.cos θ ^ 2 = Real.sin θ ^ 2 from by rw [Real.sin_sq],
            Real.sqrt_sq hsinθ]
        rw [h2]
      obtain ⟨k, hk⟩ := (Work.Core.cos_sin_eq_iff_exists_int (mdTheta t) θ).mp
        ⟨hcos_eq, hsin_eq⟩
      exact ⟨k, hk⟩
    · exact ⟨m, by rw [hmdPhi_t, hψeq]⟩
  · push Not at hsinθ
    have hcost_ne : Real.cos t ≠ 0 := by
      intro hc
      have h8 : mdD t = 1 := by
        rcases lt_or_ge (mdD t) 1 with hh | hh
        · exact absurd hc ((mdD_lt_one_iff t).mp hh)
        · exact le_antisymm (mdD_mem t).2 hh
      rw [hmdD_t] at h8
      have h9 : Real.sin θ = 0 := by
        have h10 := Real.sin_sq_add_cos_sq θ
        rw [h8] at h10; nlinarith
      linarith
    have hcost_pos : 0 < Real.cos t := lt_of_le_of_ne hcos_t (Ne.symm hcost_ne)
    have hnot : ¬ (0 ≤ Real.cos (Real.pi - t)) := by
      rw [Real.cos_pi_sub]; linarith
    have hmdPhi_ref : mdPhi (Real.pi - t) = ψ := by
      rw [mdPhi, Real.sin_pi_sub, hsin_t, mul_div_cancel₀ _ mdB_ne_zero]
    have hmdD_ref : mdD (Real.pi - t) = mdD t := by rw [mdD, mdD, hmdPhi_ref, hmdPhi_t]
    refine ⟨Real.pi - t, ?_⟩
    rw [mdGamma_apply]
    refine (Work.CoreTopology.standard.psi_eq_iff (mdTheta (Real.pi - t))
      (mdPhi (Real.pi - t)) θ φ).mpr ⟨?_, ?_⟩
    · have hcos_eq : Real.cos (mdTheta (Real.pi - t)) = Real.cos θ := by
        rw [cos_mdTheta, hmdD_ref, hmdD_t]
      have hsin_eq : Real.sin (mdTheta (Real.pi - t)) = Real.sin θ := by
        have h1 : mdTheta (Real.pi - t) = -Real.arccos (mdD (Real.pi - t)) := by
          rw [mdTheta, if_neg hnot]
        rw [h1, Real.sin_neg, Real.sin_arccos, hmdD_ref, hmdD_t]
        have h2 : Real.sqrt (1 - Real.cos θ ^ 2) = -Real.sin θ := by
          rw [show (1:ℝ) - Real.cos θ ^ 2 = Real.sin θ ^ 2 from by rw [Real.sin_sq],
            Real.sqrt_sq_eq_abs, abs_of_neg hsinθ]
        rw [h2]; ring
      obtain ⟨k, hk⟩ := (Work.Core.cos_sin_eq_iff_exists_int (mdTheta (Real.pi - t)) θ).mp
        ⟨hcos_eq, hsin_eq⟩
      exact ⟨k, hk⟩
    · exact ⟨m, by rw [hmdPhi_ref, hψeq]⟩

/-- **The reflection of the model curve**: every point of `F ∩ {x = -5/2}` is hit by
`mdGammaMinus`. -/
theorem exists_mdGammaMinus_eq (θ φ : ℝ) (h : (2 + Real.cos φ) * Real.cos θ = -(5 / 2)) :
    ∃ t : ℝ, mdGammaMinus t = Work.CoreTopology.standard.psi θ φ := by
  have hcosφ : 1 / 2 ≤ Real.cos φ := by
    have h2 : (0:ℝ) < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
    have h1 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    nlinarith [h]
  have hcosθ : Real.cos θ = -(5 / (2 * (2 + Real.cos φ))) := by
    have h1 : Real.cos θ = -5 / (2 * (2 + Real.cos φ)) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [h1]; ring
  obtain ⟨ψ, m, hψmem, hψcos, hψsin, hψeq⟩ :
      ∃ (ψ : ℝ) (m : ℤ), ψ ∈ Set.Icc (-mdB) mdB ∧ Real.cos ψ = Real.cos φ ∧
        Real.sin ψ = Real.sin φ ∧ ψ = φ + (m : ℝ) * (2 * Real.pi) := by
    set m₀ : ℤ := round (φ / (2 * Real.pi)) with hm
    refine ⟨φ - (m₀ : ℝ) * (2 * Real.pi), -m₀, ?_, ?_, ?_, ?_⟩
    · have hψabs : |φ - (m₀ : ℝ) * (2 * Real.pi)| ≤ Real.pi := by
        have h1 := abs_sub_round (φ / (2 * Real.pi))
        rw [← hm] at h1
        have h3 : (φ / (2 * Real.pi) - (m₀ : ℝ)) * (2 * Real.pi) =
            φ - (m₀ : ℝ) * (2 * Real.pi) := by
          rw [sub_mul, div_mul_cancel₀ _ (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
        have h4 : |φ - (m₀ : ℝ) * (2 * Real.pi)| =
            |φ / (2 * Real.pi) - (m₀ : ℝ)| * (2 * Real.pi) := by
          rw [← h3, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        rw [h4]
        calc |φ / (2 * Real.pi) - (m₀ : ℝ)| * (2 * Real.pi) ≤ (1 / 2) * (2 * Real.pi) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = Real.pi := by ring
      have hψIcc : φ - (m₀ : ℝ) * (2 * Real.pi) ∈ Set.Icc (-Real.pi) Real.pi :=
        abs_le.mp hψabs
      have h5 : 1 / 2 ≤ Real.cos (φ - (m₀ : ℝ) * (2 * Real.pi)) := by
        rw [Real.cos_sub_int_mul_two_pi]; exact hcosφ
      have h6 : |φ - (m₀ : ℝ) * (2 * Real.pi)| ≤ Real.pi / 3 :=
        (cos_half_iff _ hψIcc).mp h5
      rw [show Real.pi / 3 = mdB from rfl] at h6
      exact abs_le.mp h6
    · rw [Real.cos_sub_int_mul_two_pi]
    · rw [Real.sin_sub_int_mul_two_pi]
    · simp only [Int.cast_neg]; ring
  have hψabs : |ψ| ≤ mdB := abs_le.mpr hψmem
  set t : ℝ := Real.arcsin (ψ / mdB) with ht
  have htmem : |ψ / mdB| ≤ 1 := by
    rw [abs_div, abs_of_pos mdB_pos, div_le_iff₀ mdB_pos]
    simpa using hψabs
  have hsin_t : Real.sin t = ψ / mdB := by
    rw [ht]
    exact Real.sin_arcsin (abs_le.mp htmem).1 (abs_le.mp htmem).2
  have hmdPhi_t : mdPhi t = ψ := by
    rw [mdPhi, hsin_t, mul_div_cancel₀ _ mdB_ne_zero]
  have hcos_t : 0 ≤ Real.cos t := by
    rw [ht]
    exact Real.cos_nonneg_of_mem_Icc
      ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have hmdTheta_t : mdTheta t = Real.arccos (mdD t) := by rw [mdTheta, if_pos hcos_t]
  have hmdD_t : mdD t = -Real.cos θ := by
    rw [mdD, hmdPhi_t, hψcos, hcosθ]; ring
  by_cases hsinθ : Real.sin θ ≤ 0
  · -- use `t`: `mdTheta t + π ≡ θ`
    refine ⟨t, ?_⟩
    rw [mdGammaMinus_apply]
    refine (Work.CoreTopology.standard.psi_eq_iff (mdTheta t + Real.pi) (mdPhi t) θ φ).mpr
      ⟨?_, ?_⟩
    · have hcos_eq : Real.cos (mdTheta t + Real.pi) = Real.cos θ := by
        rw [Real.cos_add_pi, cos_mdTheta, hmdD_t]; ring
      have hsin_eq : Real.sin (mdTheta t + Real.pi) = Real.sin θ := by
        rw [Real.sin_add_pi, hmdTheta_t, Real.sin_arccos]
        have h2 : Real.sqrt (1 - (mdD t) ^ 2) = -Real.sin θ := by
          rw [hmdD_t,
            show (1:ℝ) - (-Real.cos θ) ^ 2 = Real.sin θ ^ 2 from by rw [Real.sin_sq]; ring,
            Real.sqrt_sq_eq_abs, abs_of_nonpos hsinθ]
        rw [h2, neg_neg]
      obtain ⟨k, hk⟩ := (Work.Core.cos_sin_eq_iff_exists_int
        (mdTheta t + Real.pi) θ).mp ⟨hcos_eq, hsin_eq⟩
      exact ⟨k, hk⟩
    · exact ⟨m, by rw [hmdPhi_t, hψeq]⟩
  · push Not at hsinθ
    -- use `π - t`: `mdTheta (π - t) + π ≡ θ`
    have hcost_ne : Real.cos t ≠ 0 := by
      intro hc
      have h8 : mdD t = 1 := by
        rcases lt_or_ge (mdD t) 1 with hh | hh
        · exact absurd hc ((mdD_lt_one_iff t).mp hh)
        · exact le_antisymm (mdD_mem t).2 hh
      rw [hmdD_t] at h8
      have h9 : Real.sin θ = 0 := by
        have h10 := Real.sin_sq_add_cos_sq θ
        nlinarith
      linarith
    have hcost_pos : 0 < Real.cos t := lt_of_le_of_ne hcos_t (Ne.symm hcost_ne)
    have hnot : ¬ (0 ≤ Real.cos (Real.pi - t)) := by
      rw [Real.cos_pi_sub]; linarith
    have hmdPhi_ref : mdPhi (Real.pi - t) = ψ := by
      rw [mdPhi, Real.sin_pi_sub, hsin_t, mul_div_cancel₀ _ mdB_ne_zero]
    have hmdD_ref : mdD (Real.pi - t) = mdD t := by rw [mdD, mdD, hmdPhi_ref, hmdPhi_t]
    refine ⟨Real.pi - t, ?_⟩
    rw [mdGammaMinus_apply]
    refine (Work.CoreTopology.standard.psi_eq_iff (mdTheta (Real.pi - t) + Real.pi)
      (mdPhi (Real.pi - t)) θ φ).mpr ⟨?_, ?_⟩
    · have hcos_eq : Real.cos (mdTheta (Real.pi - t) + Real.pi) = Real.cos θ := by
        have h1 : mdTheta (Real.pi - t) = -Real.arccos (mdD (Real.pi - t)) := by
          rw [mdTheta, if_neg hnot]
        rw [h1, Real.cos_add_pi, Real.cos_neg, Real.cos_arccos
          (by linarith [(mdD_mem (Real.pi - t)).1]) (by linarith [(mdD_mem (Real.pi - t)).2]),
          hmdD_ref, hmdD_t]
        ring
      have hsin_eq : Real.sin (mdTheta (Real.pi - t) + Real.pi) = Real.sin θ := by
        have h1 : mdTheta (Real.pi - t) = -Real.arccos (mdD (Real.pi - t)) := by
          rw [mdTheta, if_neg hnot]
        rw [h1, Real.sin_add_pi, Real.sin_neg, Real.sin_arccos, hmdD_ref, hmdD_t]
        have h2 : Real.sqrt (1 - (-Real.cos θ) ^ 2) = Real.sin θ := by
          rw [show (1:ℝ) - (-Real.cos θ) ^ 2 = Real.sin θ ^ 2 from by rw [Real.sin_sq]; ring,
            Real.sqrt_sq hsinθ.le]
        rw [h2]; ring
      obtain ⟨k, hk⟩ := (Work.Core.cos_sin_eq_iff_exists_int
        (mdTheta (Real.pi - t) + Real.pi) θ).mp ⟨hcos_eq, hsin_eq⟩
      exact ⟨k, hk⟩
    · exact ⟨m, by rw [hmdPhi_ref, hψeq]⟩


/-! ## The curves as closed curves of the standard torus, and their ranges -/

/-- **A congruence modulo `2π` of two numbers of modulus `≤ B < π` is an equality.** -/
theorem eq_of_congr_two_pi_of_abs_le {x y B : ℝ} (hB : B < Real.pi) (hx : |x| ≤ B)
    (hy : |y| ≤ B) (h : ∃ k : ℤ, x = y + (k : ℝ) * (2 * Real.pi)) : x = y := by
  obtain ⟨k, hk⟩ := h
  have hk0 : k = 0 := by
    have h1 : |(k : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
      rw [show (k : ℝ) * (2 * Real.pi) = x - y from by rw [hk]; ring]
      have hxy' : |x - y| ≤ |x| + |y| := by simpa using abs_sub_le x 0 y
      calc |x - y| ≤ B + B := le_trans hxy' (add_le_add hx hy)
        _ < 2 * Real.pi := by linarith [Real.pi_pos]
    by_contra hkne
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hkne
    have h2 : 2 * Real.pi ≤ |(k : ℝ) * (2 * Real.pi)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    linarith
  rw [hk, hk0]; ring

theorem injOn_mdGamma : Set.InjOn mdGamma (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht t' ht' h
  have h1 : ∃ k : ℤ, mdTheta t = mdTheta t' + (k : ℝ) * (2 * Real.pi) :=
    ((Work.CoreTopology.standard.psi_eq_iff (mdTheta t) (mdPhi t) (mdTheta t')
      (mdPhi t')).mp h).1
  have h2 : ∃ k : ℤ, mdPhi t = mdPhi t' + (k : ℝ) * (2 * Real.pi) :=
    ((Work.CoreTopology.standard.psi_eq_iff (mdTheta t) (mdPhi t) (mdTheta t')
      (mdPhi t')).mp h).2
  have hθ : mdTheta t = mdTheta t' :=
    eq_of_congr_two_pi_of_abs_le mdC_lt_pi (abs_mdTheta_le t) (abs_mdTheta_le t') h1
  have hφ : mdPhi t = mdPhi t' :=
    eq_of_congr_two_pi_of_abs_le mdB_lt_pi (abs_mdPhi_le t) (abs_mdPhi_le t') h2
  exact injOn_mdTheta_mdPhi ht ht' (Prod.ext hθ hφ)

theorem injOn_mdGammaMinus : Set.InjOn mdGammaMinus (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht t' ht' h
  have h1 : ∃ k : ℤ, mdTheta t + Real.pi = (mdTheta t' + Real.pi) + (k : ℝ) * (2 * Real.pi) :=
    ((Work.CoreTopology.standard.psi_eq_iff (mdTheta t + Real.pi) (mdPhi t)
      (mdTheta t' + Real.pi) (mdPhi t')).mp h).1
  have h2 : ∃ k : ℤ, mdPhi t = mdPhi t' + (k : ℝ) * (2 * Real.pi) :=
    ((Work.CoreTopology.standard.psi_eq_iff (mdTheta t + Real.pi) (mdPhi t)
      (mdTheta t' + Real.pi) (mdPhi t')).mp h).2
  obtain ⟨k, hk⟩ := h1
  have hθ : mdTheta t = mdTheta t' :=
    eq_of_congr_two_pi_of_abs_le mdC_lt_pi (abs_mdTheta_le t) (abs_mdTheta_le t')
      ⟨k, by linarith⟩
  have hφ : mdPhi t = mdPhi t' :=
    eq_of_congr_two_pi_of_abs_le mdB_lt_pi (abs_mdPhi_le t) (abs_mdPhi_le t') h2
  exact injOn_mdTheta_mdPhi ht ht' (Prod.ext hθ hφ)

theorem mdGamma_x (t : ℝ) : mdGamma t 0 = 5 / 2 := by
  rw [mdGamma_apply, Work.CoreTopology.standard_psi, Work.Core.torusMap_apply_zero]
  exact x_coord t

theorem mdGammaMinus_x (t : ℝ) : mdGammaMinus t 0 = -(5 / 2) := by
  rw [mdGammaMinus_apply, Work.CoreTopology.standard_psi, Work.Core.torusMap_apply_zero,
    Real.cos_add_pi]
  nlinarith [x_coord t]

theorem mdGamma_range :
    Set.range mdGamma =
      Work.CoreTopology.standard.carrier ∩ {y : R3 | y 0 = 5 / 2} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨mdGamma_mem t, mdGamma_x t⟩
  · rintro y ⟨hy, hy0⟩
    obtain ⟨θ, φ, hθφ⟩ := (Work.CoreTopology.ParamTorus.mem_carrier_iff _ y).mp hy
    have h : (2 + Real.cos φ) * Real.cos θ = 5 / 2 := by
      have h' := congrArg (fun z : R3 => z 0) hθφ
      rw [Work.CoreTopology.standard_psi, Work.Core.torusMap_apply_zero, hy0] at h'
      exact h'
    obtain ⟨t, ht⟩ := exists_mdGamma_eq θ φ h
    exact ⟨t, ht.trans hθφ⟩

theorem mdGammaMinus_range :
    Set.range mdGammaMinus =
      Work.CoreTopology.standard.carrier ∩ {y : R3 | y 0 = -(5 / 2)} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨mdGammaMinus_mem t, mdGammaMinus_x t⟩
  · rintro y ⟨hy, hy0⟩
    obtain ⟨θ, φ, hθφ⟩ := (Work.CoreTopology.ParamTorus.mem_carrier_iff _ y).mp hy
    have h : (2 + Real.cos φ) * Real.cos θ = -(5 / 2) := by
      have h' := congrArg (fun z : R3 => z 0) hθφ
      rw [Work.CoreTopology.standard_psi, Work.Core.torusMap_apply_zero, hy0] at h'
      exact h'
    obtain ⟨t, ht⟩ := exists_mdGammaMinus_eq θ φ h
    exact ⟨t, ht.trans hθφ⟩

end

end Work.BoxShrink.Pinch
