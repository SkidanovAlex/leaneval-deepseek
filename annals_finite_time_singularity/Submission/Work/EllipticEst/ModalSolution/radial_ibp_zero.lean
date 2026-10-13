/-
Radial integration by parts (Lagrange identity) for the modal Bessel operator.

For `α ≠ 0` put `s = (5-α)/α`.  The radial operator
`L = -(α² z² ∂_z² + α(5+α) z ∂_z)` is formally self-adjoint for the weight
`z^s = z^((5-α)/α)`: the coefficient identity is `(α² z² z^s)' = α(5+α) z z^s`, which is
exactly `α² (s+2) = α (5+α)`.  Hence, with
`P z = α² z² z^s`, `Q z = α(5+α) z z^s` and `F z = -P z (f z g'(z) - f'(z) g(z))`,

  `F' z = (f z (L g)(z) - (L f)(z) g z) z^s`   (`P' = Q`),

so the compactly supported case (`g` vanishes off `[a,b] ⊂ (0,∞)`) gives the vanishing
integral.  The boundary terms `F a`, `F b` vanish because `g` and `g'` do: `g = 0` on
`(0,a) ∪ (b,∞)` and `g'` inherits that by continuity.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution

open scoped Real Topology
open MeasureTheory Set Filter

/-- A function continuous on `[c,d]` that vanishes on `(c,d)` vanishes on `[c,d]`. -/
lemma eq_zero_of_vanish_Ioo {h : ℝ → ℝ} {c d : ℝ} (hcd : c < d)
    (hcont : ContinuousOn h (Set.Icc c d)) (heq : ∀ y ∈ Set.Ioo c d, h y = 0) :
    Set.EqOn h 0 (Set.Icc c d) :=
  Set.EqOn.of_subset_closure heq hcont continuousOn_const
    Set.Ioo_subset_Icc_self (closure_Ioo hcd.ne).ge

/-- A function of class `C¹` on `[c,d]` (derivative continuous there) that vanishes on
`(c,d)` has vanishing derivative on `[c,d]`. -/
lemma deriv_eq_zero_of_vanish_Ioo {h : ℝ → ℝ} {c d : ℝ} (hcd : c < d)
    (hcont : ContinuousOn (deriv h) (Set.Icc c d)) (heq : ∀ y ∈ Set.Ioo c d, h y = 0) :
    Set.EqOn (deriv h) 0 (Set.Icc c d) := by
  have hE : Set.EqOn (deriv h) (fun _ => (0 : ℝ)) (Set.Ioo c d) := by
    intro y hy
    have hev : h =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
      exact heq z hz
    exact ((hasDerivAt_const (x := y) (c := 0)).congr_of_eventuallyEq hev).deriv
  exact Set.EqOn.of_subset_closure hE hcont continuousOn_const
    Set.Ioo_subset_Icc_self (closure_Ioo hcd.ne).ge

/-- The derivative of the radial weight factor `α² z² z^((5-α)/α)`; the coefficient
identity `α² ((5-α)/α + 2) = α(5+α)` is precisely what makes the operator self-adjoint. -/
lemma hasDerivAt_Pweight (α : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => α ^ 2 * (z ^ 2 * z ^ ((5 - α) / α)))
      (α * (5 + α) * x * x ^ ((5 - α) / α)) x := by
  set s : ℝ := (5 - α) / α with hs
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hrpow : HasDerivAt (fun z : ℝ => z ^ s) (s * x ^ (s - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hcoef : α ^ 2 * (s + 2) = α * (5 + α) := by
    rw [hs]
    rcases eq_or_ne α 0 with h | h
    · subst h; norm_num
    · field_simp
      ring
  have hxx : x ^ 2 * x ^ (s - 1) = x * x ^ s := by
    rw [← Real.rpow_natCast (x := x) (n := 2), ← Real.rpow_add hx]
    rw [show (↑(2 : ℕ) : ℝ) + (s - 1) = 1 + s by ring, Real.rpow_add hx, Real.rpow_one]
  have hmain : α ^ 2 * (2 * x * x ^ s + x ^ 2 * (s * x ^ (s - 1)))
      = α * (5 + α) * x * x ^ s := by
    rw [show x ^ 2 * (s * x ^ (s - 1)) = s * (x * x ^ s) by
      rw [show x ^ 2 * (s * x ^ (s - 1)) = s * (x ^ 2 * x ^ (s - 1)) by ring, hxx],
      ← hcoef]
    ring
  have hh := (hasDerivAt_const (x := x) (c := α ^ 2)).mul (hpow.mul hrpow)
  rw [zero_mul, zero_add] at hh
  exact hh.congr_deriv hmain

theorem radial_ibp_zero (α : ℝ) {f g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hf : ContDiffOn ℝ 2 f (Set.Ioi 0))
    (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (hg0 : ∀ z, z ∉ Set.Icc a b → g z = 0) :
    ∫ z in Set.Icc a b, (f z * (-(α ^ 2 * z ^ 2 * deriv (deriv g) z + α * (5 + α) * z * deriv g z))
        - (-(α ^ 2 * z ^ 2 * deriv (deriv f) z + α * (5 + α) * z * deriv f z)) * g z)
        * z ^ ((5 - α) / α) = 0 := by
  set Js : ℝ → ℝ := fun z =>
    (f z * (-(α ^ 2 * z ^ 2 * deriv (deriv g) z + α * (5 + α) * z * deriv g z))
      - (-(α ^ 2 * z ^ 2 * deriv (deriv f) z + α * (5 + α) * z * deriv f z)) * g z)
      * z ^ ((5 - α) / α) with hJs_def
  set F : ℝ → ℝ :=
    fun z => -(α ^ 2 * (z ^ 2 * z ^ ((5 - α) / α)) * (f z * deriv g z - deriv f z * g z))
    with hF_def
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hbpos : 0 < b := lt_trans ha hab
  -- ### the pointwise derivative identity `F' = Js`
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (Js x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    have hxpos : 0 < x := hsub hx
    have hxmem : Set.Ioi (0 : ℝ) ∈ 𝓝 x := isOpen_Ioi.mem_nhds hxpos
    have hdf : HasDerivAt f (deriv f x) x :=
      ((hf.contDiffAt hxmem).differentiableAt (by norm_num)).hasDerivAt
    have hdg : HasDerivAt g (deriv g x) x :=
      ((hg.contDiffAt hxmem).differentiableAt (by norm_num)).hasDerivAt
    have hddf : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
      (((hf.contDiffAt hxmem).derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasDerivAt
    have hddg : HasDerivAt (deriv g) (deriv (deriv g) x) x :=
      (((hg.contDiffAt hxmem).derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasDerivAt
    have hP : HasDerivAt (fun z : ℝ => α ^ 2 * (z ^ 2 * z ^ ((5 - α) / α)))
        (α * (5 + α) * x * x ^ ((5 - α) / α)) x := hasDerivAt_Pweight α hxpos
    have hA : HasDerivAt (fun z : ℝ => f z * deriv g z - deriv f z * g z)
        (f x * deriv (deriv g) x - deriv (deriv f) x * g x) x := by
      refine ((hdf.mul hddg).sub (hddf.mul hdg)).congr_deriv ?_
      ring
    rw [hF_def, hJs_def]
    exact (hP.mul hA).neg.congr_deriv (by ring)
  -- ### continuity of the integrand
  have hJs_cont : ContinuousOn Js (Set.Icc a b) := by
    rw [hJs_def]
    have hf0 : ContinuousOn f (Set.Icc a b) := hf.continuousOn.mono hsub
    have hgc : ContinuousOn g (Set.Icc a b) := hg.continuousOn.mono hsub
    have hdfc : ContinuousOn (deriv f) (Set.Icc a b) :=
      (hf.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
    have hdgc : ContinuousOn (deriv g) (Set.Icc a b) :=
      (hg.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
    have hddfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
      ((hf.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen
        isOpen_Ioi (by norm_num)).mono hsub
    have hddgc : ContinuousOn (deriv (deriv g)) (Set.Icc a b) :=
      ((hg.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen
        isOpen_Ioi (by norm_num)).mono hsub
    have hw : ContinuousOn (fun z : ℝ => z ^ ((5 - α) / α)) (Set.Icc a b) :=
      continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt (hsub hz)))
    have hB1 : ContinuousOn (fun z : ℝ =>
        f z * (-(α ^ 2 * z ^ 2 * deriv (deriv g) z + α * (5 + α) * z * deriv g z)))
        (Set.Icc a b) :=
      hf0.mul (ContinuousOn.neg (ContinuousOn.add
        ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hddgc)
        ((continuousOn_const.mul continuousOn_id).mul hdgc)))
    have hB2 : ContinuousOn (fun z : ℝ =>
        (-(α ^ 2 * z ^ 2 * deriv (deriv f) z + α * (5 + α) * z * deriv f z)) * g z)
        (Set.Icc a b) :=
      (ContinuousOn.neg (ContinuousOn.add
        ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hddfc)
        ((continuousOn_const.mul continuousOn_id).mul hdfc))).mul hgc
    exact (hB1.sub hB2).mul hw
  have hint : IntervalIntegrable Js volume a b := hJs_cont.intervalIntegrable_of_Icc hab.le
  have hFTC : ∫ z in a..b, Js z = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- ### the boundary terms vanish: `g` and `g'` are zero at `a` and at `b`
  have hga : g a = 0 := by
    have h := eq_zero_of_vanish_Ioo (h := g) (c := a / 2) (d := a) (by linarith)
      (hg.continuousOn.mono
        (fun x hx => lt_of_lt_of_le (by linarith : (0 : ℝ) < a / 2) hx.1))
      (fun y hy => hg0 y (fun hyab => absurd hyab.1 (not_le_of_gt hy.2)))
    have ha' : a ∈ Set.Icc (a / 2) a := by constructor <;> linarith
    simpa using h ha'
  have hdga : deriv g a = 0 := by
    have h := deriv_eq_zero_of_vanish_Ioo (h := g) (c := a / 2) (d := a) (by linarith)
      ((hg.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
        (fun x hx => lt_of_lt_of_le (by linarith : (0 : ℝ) < a / 2) hx.1))
      (fun y hy => hg0 y (fun hyab => absurd hyab.1 (not_le_of_gt hy.2)))
    have ha' : a ∈ Set.Icc (a / 2) a := by constructor <;> linarith
    simpa using h ha'
  have hgb : g b = 0 := by
    have h := eq_zero_of_vanish_Ioo (h := g) (c := b) (d := b + 1) (by linarith)
      (hg.continuousOn.mono (fun x hx => lt_of_lt_of_le hbpos hx.1))
      (fun y hy => hg0 y (fun hyab => absurd hyab.2 (not_le_of_gt hy.1)))
    have hb' : b ∈ Set.Icc b (b + 1) := by constructor <;> linarith
    simpa using h hb'
  have hdgb : deriv g b = 0 := by
    have h := deriv_eq_zero_of_vanish_Ioo (h := g) (c := b) (d := b + 1) (by linarith)
      ((hg.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
        (fun x hx => lt_of_lt_of_le hbpos hx.1))
      (fun y hy => hg0 y (fun hyab => absurd hyab.2 (not_le_of_gt hy.1)))
    have hb' : b ∈ Set.Icc b (b + 1) := by constructor <;> linarith
    simpa using h hb'
  have hFb : F b = 0 := by
    simp only [hF_def]
    rw [hgb, hdgb]
    ring
  have hFa : F a = 0 := by
    simp only [hF_def]
    rw [hga, hdga]
    ring
  have h0 : ∫ z in a..b, Js z = 0 := by rw [hFTC, hFb, hFa]; ring
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  exact h0

end Work.EllipticEst.ModalSolution
