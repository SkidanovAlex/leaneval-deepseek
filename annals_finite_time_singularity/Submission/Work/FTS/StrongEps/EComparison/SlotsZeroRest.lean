import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Coercivity.not_integrableOn_of_lower_rpow
import Submission.Work.Coercivity.theta_integral_lower
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroRepr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SlotsZeroRest` — the three slots vanish along the radial Euler mode

The hypothesis

`hU : Uop α w z θ = 0` on the open quadrant, i.e. `-3 w - α z ∂_z w = 0`,

is the radial (indicial) Euler identity `z ∂_z w = -(3/α) w`: for every fixed `θ` the
`z`-slice of `w` is a multiple of `z^{-3/α}` (`SlotsZeroRepr`).  Differentiating the
representation in `θ` shows that `Vop w = ∂_θ w - tan θ · w` has exactly the same shape,
`Vop w z θ = d θ · z^{-3/α}`.  The weighted integrand of `HkIntegrand α 6 (Vop w)` contains
the level-`0` term `(Vop w · w z / sin(2θ)^{η/2})²`, which on `z ∈ (0,1)` is bounded below
by `const · d θ² sin(2θ)^{-η} z^{-2}`; a single `θ` with `d θ ≠ 0` therefore forces the
`z`-integral to diverge at `z → 0⁺` (`SlotsZeroSliceLB`), contradicting `HkMem α 6 (Vop w)`
via `Work.Coercivity.not_integrableOn_of_lower_rpow`.

Finally, on the open quadrant `Rop α w = Vop w` *identically* once `Uop α w = 0`:
the numerator of `Rop` is `2 sin θ w + sin θ · α z ∂_z w + cos θ ∂_θ w = -sin θ w + cos θ ∂_θ w`.
-/

namespace Work.FTS.StrongEps.EComparison

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The smoothness of `Vop w` -/

private theorem contDiffOn_tan_snd :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Real.tan p.2)
      = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 := by
    funext p; rw [Real.tan_eq_sin_div_cos]
  rw [hfun]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  · exact (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  · intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)

private theorem smoothOpen_tan_mul {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * w z θ) := by
  have h := contDiffOn_tan_snd.mul (show ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => w p.1 p.2) Work.FTS.EllipticEst.Q0 from hsm)
  have hgoal : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * w z θ) ↔
      ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2 * w p.1 p.2)
        Work.FTS.EllipticEst.Q0 := Iff.rfl
  exact hgoal.mpr h

private theorem smoothOpen_Vop {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop w) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth w) := hsm.pth
  have h2 := h1.sub (smoothOpen_tan_mul hsm)
  have hgoal : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop w) ↔
      ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => deriv (fun θ' => w p.1 θ') p.2 - Real.tan p.2 * w p.1 p.2)
        Work.FTS.EllipticEst.Q0 := Iff.rfl
  exact hgoal.mpr h2

/-! ## The `z`-profile of `w` and of `Vop w` -/

/-- From the radial Euler identity `Uop α w = 0` the `z`-slice of `w` is a multiple of
`z^{-3/α}`. -/
private theorem repr_w {α : ℝ} (hα : 0 < α) {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hU : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), w z θ = w 1 θ * z ^ (-(3 / α)) := by
  intro z hz θ hθ
  refine SlotsZeroRepr hα (u := w) (θ := θ)
    ((hsm.curry_z hθ).differentiableOn (by simp [Work.Stability.smoothOrder])) ?_ z hz
  intro z' hz'
  have h := hU z' hz' θ hθ
  simp only [Work.Construction.Uop, Work.Spaces.pz] at h
  have hαne : α ≠ 0 := ne_of_gt hα
  have key : z' * deriv (fun z'' => w z'' θ) z' = -3 * w z' θ / α := by
    rw [eq_div_iff hαne]
    linarith [h]
  rw [key]
  ring

/-- `∂_θ` of the representation: the `θ`-derivative of `w (·,θ)` inherits the `z^{-3/α}`-factor
(the two functions agree on a neighbourhood of the interior point `θ`). -/
private theorem pth_repr {α : ℝ} {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hrep : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), w z θ = w 1 θ * z ^ (-(3 / α)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth w z θ = Work.Spaces.pth w 1 θ * z ^ (-(3 / α)) := by
  have h1 : (fun θ' => w z θ') =ᶠ[nhds θ] (fun θ' => w 1 θ' * z ^ (-(3 / α))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact hrep z hz θ' hθ'
  have h2 := h1.deriv_eq
  have hd : DifferentiableAt ℝ (fun θ' => w 1 θ') θ :=
    ((hsm.curry_θ (z := 1) (by norm_num)).differentiableOn
      (by simp [Work.Stability.smoothOrder])).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have h3 : deriv (fun θ' => w 1 θ' * z ^ (-(3 / α))) θ
      = deriv (fun θ' => w 1 θ') θ * z ^ (-(3 / α)) := deriv_mul_const hd _
  show deriv (fun θ' => w z θ') θ = deriv (fun θ' => w 1 θ') θ * z ^ (-(3 / α))
  rw [h2, h3]

/-- `Vop w` inherits the `z^{-3/α}`-profile of `w`. -/
private theorem repr_Vop {α : ℝ} (hα : 0 < α) {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hU : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Construction.Vop w z θ = Work.Construction.Vop w 1 θ * z ^ (-(3 / α)) := by
  intro z hz θ hθ
  have hrep := repr_w hα hsm hU
  have hp := pth_repr hsm hrep hz hθ
  have hw := hrep z hz θ hθ
  simp only [Work.Construction.Vop]
  rw [hp, hw]
  ring

/-! ## The `θ`-slice lower bound for the `H^k`-integrand

The whole point of the `z^{-3/α}`-profile is that the level-`0` summand of
`HkIntegrand α 6 (Vop w)` is `(d θ · z^{-3/α} · w(z)/sin(2θ)^{η/2})²`, which near `z = 0`
behaves like `z^{-6/α}·(w z)² ≥ z^{-2}`: the `θ`-integral blows up like `z^{-2}`.  The
elementary coercivity lemma `Work.Coercivity.theta_integral_lower` extracts exactly this
from the pointwise bound `δ² z² ≤ (Vop w z θ)²` on an angular interval on which `|d| ≥ δ`. -/

private theorem slice_lower_bound {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {d : ℝ → ℝ}
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) (hdcont : ContinuousAt d θ₀)
    (hne : d θ₀ ≠ 0)
    (hrep : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), f z θ = d θ * z ^ (-(3 / α)))
    (hHk : ∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ =>
      Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iθ) :
    ∃ c : ℝ, 0 < c ∧ ∀ z, 0 < z → z < 1 →
      c / z ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
  -- the reference level `δ = |d θ₀|/2` and an angular interval on which `|d| ≥ δ`
  set δ : ℝ := |d θ₀| / 2 with hδdef
  have hδpos : 0 < δ := by
    have : 0 < |d θ₀| := abs_pos.mpr hne
    rw [hδdef]; linarith
  obtain ⟨η, hηpos, hη⟩ :=
    Metric.continuousAt_iff.mp hdcont (|d θ₀| / 2) (by
      have : 0 < |d θ₀| := abs_pos.mpr hne
      linarith)
  have hη' : ∀ θ : ℝ, |θ - θ₀| < η → δ ≤ |d θ| := by
    intro θ hθ
    have h1 : |d θ - d θ₀| < |d θ₀| / 2 := by
      have h := hη (x := θ) (by rw [Real.dist_eq]; exact hθ)
      rwa [Real.dist_eq] at h
    have h2 : |d θ₀| ≤ |d θ| + |d θ - d θ₀| := by
      have h3 : |d θ - (d θ - d θ₀)| ≤ |d θ| + |d θ - d θ₀| := abs_sub _ _
      rwa [show d θ - (d θ - d θ₀) = d θ₀ by ring] at h3
    rw [hδdef]; linarith
  -- the interval `(θ₀-ε, θ₀+ε)`, contained in `(0,π/2)` and in `{|θ-θ₀| < η}`
  set ε : ℝ := min (η / 2) (min (θ₀ / 2) ((Real.pi / 2 - θ₀) / 2)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith) (lt_min (by linarith [hθ₀.1]) (by linarith [hθ₀.2]))
  have hεη : ε ≤ η / 2 := le_trans (min_le_left _ _) le_rfl
  have hε1 : ε ≤ θ₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε2 : ε ≤ (Real.pi / 2 - θ₀) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ ^ 2 * (2 * ε), by positivity, fun z hz hz1 => ?_⟩
  -- the pointwise bound `δ² z² ≤ (f z θ)²` on the interval
  have hlow : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), (4 * δ) ^ 2 / 16 * z ^ 2 ≤ (f z θ) ^ 2 := by
    intro θ hθ
    have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨by linarith [hθ.1, hε1, hθ₀.1], by linarith [hθ.2, hε2, hθ₀.2]⟩
    have hdθ : δ ≤ |d θ| := by
      refine hη' θ ?_
      rw [abs_lt]
      constructor <;> linarith [hθ.1, hθ.2, hεη, hηpos]
    have hsq : (z ^ (-(3 / α))) ^ 2 = z ^ (-(6 / α)) := by
      rw [pow_two, ← Real.rpow_add hz (-(3 / α)) (-(3 / α))]
      congr 1
      ring
    have hfe : (f z θ) ^ 2 = (d θ) ^ 2 * z ^ (-(6 / α)) := by
      rw [hrep z hz θ hθmem, mul_pow, hsq]
    have hzp : 1 ≤ z ^ (-(6 / α)) := by
      have h6 : -(6 / α) ≤ 0 := by
        have : 0 < 6 / α := by positivity
        linarith
      have h := Real.rpow_le_rpow_of_nonpos hz (by linarith : z ≤ 1) h6
      simpa using h
    have hz2 : z ^ 2 ≤ 1 := by nlinarith
    have hd2 : δ ^ 2 ≤ (d θ) ^ 2 := by
      have h1 : δ ^ 2 ≤ |d θ| ^ 2 := by
        have := abs_nonneg (d θ)
        nlinarith [hdθ, hδpos]
      rwa [sq_abs] at h1
    rw [hfe]
    have h4 : (4 * δ) ^ 2 / 16 = δ ^ 2 := by ring
    rw [h4]
    calc δ ^ 2 * z ^ 2 ≤ δ ^ 2 * 1 := by
          exact mul_le_mul_of_nonneg_left hz2 (sq_nonneg δ)
      _ = δ ^ 2 := by ring
      _ ≤ (d θ) ^ 2 := hd2
      _ = (d θ) ^ 2 * 1 := by ring
      _ ≤ (d θ) ^ 2 * z ^ (-(6 / α)) :=
          mul_le_mul_of_nonneg_left hzp (sq_nonneg (d θ))
  have hmain := Work.Coercivity.theta_integral_lower α 6 f z hz
    (θ₁ := θ₀ - ε) (θ₂ := θ₀ + ε) (Aref := 4 * δ)
    (by linarith [hε1, hθ₀.1]) (by linarith [hεpos]) (by linarith [hε2, hθ₀.2])
    (hHk z hz) hlow
  have hA : (4 * δ) ^ 2 * ((θ₀ + ε) - (θ₀ - ε)) / 16 = δ ^ 2 * (2 * ε) := by ring
  rw [hA] at hmain
  -- the weight beats `1/z²`
  have hw2 : 1 / z ^ 2 ≤ (Work.Spaces.w z) ^ 2 * z ^ 2 := by
    have h : (Work.Spaces.w z) ^ 2 * z ^ 2 = (1 + z) ^ 4 / z ^ 2 := by
      rw [Work.Spaces.w]
      field_simp
    rw [h, div_le_div_iff_of_pos_right (pow_pos hz 2)]
    exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z)
  have hc0 : 0 ≤ δ ^ 2 * (2 * ε) := by positivity
  calc δ ^ 2 * (2 * ε) / z ^ 2
      = δ ^ 2 * (2 * ε) * (1 / z ^ 2) := by ring
    _ ≤ δ ^ 2 * (2 * ε) * ((Work.Spaces.w z) ^ 2 * z ^ 2) :=
        mul_le_mul_of_nonneg_left hw2 hc0
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := hmain

/-! ## `Rop w = Vop w` once `Uop w = 0` -/

private theorem Rop_eq_Vop {α : ℝ} {w : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hU : Work.Construction.Uop α w z θ = 0) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Construction.Rop α w z θ = Work.Construction.Vop w z θ := by
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hpz : α * z * Work.Spaces.pz w z θ = -3 * w z θ := by
    have h := hU
    simp only [Work.Construction.Uop] at h
    linarith [h]
  have hnum : 2 * Real.sin θ * w z θ + α * Real.sin θ * z * Work.Spaces.pz w z θ
      + Real.cos θ * Work.Spaces.pth w z θ
      = Real.cos θ * (Work.Spaces.pth w z θ - Real.tan θ * w z θ) := by
    rw [Real.tan_eq_sin_div_cos]
    have hx : α * Real.sin θ * z * Work.Spaces.pz w z θ
        = Real.sin θ * (α * z * Work.Spaces.pz w z θ) := by ring
    rw [hx, hpz]
    field_simp
    ring
  simp only [Work.Construction.Rop, Work.Construction.Vop]
  rw [hnum, div_eq_iff (ne_of_gt hcos)]
  ring

/-! ## The main statement -/

theorem SlotsZeroRest {α : ℝ} (hα : 0 < α) {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hU : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0)
    (hV : Work.Spaces.HkMem α 6 (Work.Construction.Vop w)) :
    (∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Rop α w z θ = 0) ∧
    (∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0) ∧
    (∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Vop w z θ = 0) := by
  have hsmV : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop w) := smoothOpen_Vop hsm
  have hrepV := repr_Vop hα hsm hU
  -- The third slot vanishes: otherwise the level-`0` term of the weighted integrand blows up.
  have hzero : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Vop w z θ = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₀, hz₀, θ₀, hθ₀, hne₀⟩ := hcon
    -- the `θ`-profile `d = Vop w 1 ·` does not vanish at `θ₀`
    have hne : Work.Construction.Vop w 1 θ₀ ≠ 0 := by
      intro h0
      have h := hrepV z₀ hz₀ θ₀ hθ₀
      rw [h, h0, zero_mul] at hne₀
      exact hne₀ rfl
    have hcont : ContinuousAt (fun θ => Work.Construction.Vop w 1 θ) θ₀ :=
      ((hsmV.curry_θ (z := 1) (by norm_num)).continuousOn).continuousAt
        (isOpen_Ioo.mem_nhds hθ₀)
    have hHk : ∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ =>
        Work.Spaces.HkIntegrand α 6 (Work.Construction.Vop w) z θ) Work.Spaces.Iθ :=
      fun z hz => hV.1 z (le_of_lt hz)
    obtain ⟨c, hc, hlb⟩ := slice_lower_bound hα hθ₀ hcont hne hrepV hHk
    have hInt : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (Work.Construction.Vop w) z θ) (Set.Ici 0) := hV.2
    exact (Work.Coercivity.not_integrableOn_of_lower_rpow hc (by norm_num : (0 : ℝ) < 1)
      (fun z hz => hlb z hz.1 hz.2)) hInt
  refine ⟨fun z hz θ hθ => ?_, hU, hzero⟩
  rw [Rop_eq_Vop (hU z hz θ hθ) hθ]
  exact hzero z hz θ hθ

end

end Work.FTS.StrongEps.EComparison
