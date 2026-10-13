import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.H2W.Slot11Src.mixed11_Wt_sq_eq
import Submission.Work.Spaces.mixed_comm
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.Mine.cs_interval_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W.slot11_src_int`: integrability of the angular derivative of the shifted source

For `0 < α ≤ 1/4`, a datum `h : TT.EllWeakPos α 2 F Ψ` of the weak elliptic class and every
`z > 0`, the function

  `θ ↦ (∂_θ (Gsrc α (D_zF) (D_zΨ)) (z,θ))² · sin(2θ)^{2-γ}`

is integrable on the angular interval `Iθ = [0,π/2]`.

Route.  On the open quadrant `Gsrc α (D_zF) (D_zΨ) = D_zF + α²·D_z(slotA Ψ) + α(5+α)·D_z²Ψ`, where
`slotA Ψ = z²∂_z²Ψ`, and `D_z²Ψ = slotA Ψ + D_zΨ` there; differentiating in `θ` splits
`∂_θ(Gsrc …)` into the four terms `∂_θ(D_zF)`, `α²∂_θ(D_z(slotA Ψ))`,
`α(5+α)∂_θ(slotA Ψ)`, `α(5+α)∂_θ(D_zΨ)`.  Each of their squares against `sin(2θ)^{2-γ}` is
integrable:

* the first two are the `(1,1)`-slots of `HkMem α 2 F` resp. `HkMem α 2 (slotA Ψ)`
  (`Slot11Src.mixed11_Wt_sq_eq`, together with `integrableOn_mixedSummand`);
* the third is the `(1,0)`-slot of `HkMem α 2 (slotA Ψ)` (`Wt_sq_eq`, `mul_sq_rpow_neg`);
* the fourth is controlled by the elementary criterion `integrableOn_deriv_sq_mul_rpow` applied
  to the `i = 1` pure slot of `HkMem α 2 (∂_θ²Ψ)` (`integrableOn_zSummand` +
  `pthIter2_DzIter_comm`).  No endpoint continuity of the slice is needed here: the second
  derivative is already weighted-`L²` with the singular weight `sEta`, and the fundamental
  theorem of calculus on the open interval plus Cauchy–Schwarz (`Mine.cs_interval_le`) bounds the
  first derivative there.
-/

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary `rpow` algebra of the angular weights -/

/-- `sin(2θ) ≥ 0` on the angular interval. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sEta θ = sin(2θ)^{-η} ≥ 0` on the angular interval. -/
theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(s·Y)²·s^{-c} = Y²·s^{2-c}` for `s ≥ 0`, `c ≠ 2`. -/
theorem mul_sq_rpow_neg {s Y c : ℝ} (hs : 0 ≤ s) (hc : c ≠ 2) :
    (s * Y) ^ 2 * s ^ (-c) = Y ^ 2 * s ^ (2 - c) := by
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · subst hs0
    by_cases hc0 : c = 0
    · subst hc0
      rw [neg_zero, Real.rpow_zero, mul_one, sub_zero, Real.rpow_two] <;> ring
    · rw [Real.zero_rpow (neg_ne_zero.mpr hc0),
        Real.zero_rpow (sub_ne_zero.mpr (Ne.symm hc))]
      ring
  · have key : s ^ ((2 : ℕ) : ℝ) * s ^ (-c) = s ^ (2 - c) := by
      rw [← Real.rpow_add hs0]
      congr 1
    calc (s * Y) ^ 2 * s ^ (-c)
        = s ^ 2 * Y ^ 2 * s ^ (-c) := by rw [mul_pow]
      _ = s ^ ((2 : ℕ) : ℝ) * Y ^ 2 * s ^ (-c) := by rw [← Real.rpow_natCast s 2]
      _ = (s ^ ((2 : ℕ) : ℝ) * s ^ (-c)) * Y ^ 2 := by ring
      _ = s ^ (2 - c) * Y ^ 2 := by rw [key]
      _ = Y ^ 2 * s ^ (2 - c) := by ring

/-- `(Wt α z θ)² = w(z)²·sin(2θ)^{-γ}` on the angular interval. -/
theorem Wt_sq_eq (α : ℝ) (z : ℝ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow,
    ← Real.rpow_natCast (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) 2,
    ← Real.rpow_mul hs]
  congr 1
  ring

/-! ## The two product rules relating `D_z Ψ` to the plain derivatives of `Ψ` -/

/-- `∂_z(D_zΨ) = ∂_zΨ + z·∂_z²Ψ` on the open quadrant. -/
theorem pz_DzIter_one_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ
      = Work.Spaces.pzIter 1 Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ := by
  have h := (hasDerivAt_id z).mul (hΨ.hasDerivAt_slice_pzIter 1 hθ hz)
  have hd : HasDerivAt (fun z' => z' * Work.Spaces.pzIter 1 Ψ z' θ)
      (1 * Work.Spaces.pzIter 1 Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ) z := h
  rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ
      = deriv (fun z' => z' * Work.Spaces.pzIter 1 Ψ z' θ) z from rfl, hd.deriv]
  ring

/-- `∂_z²(D_zΨ) = 2·∂_z²Ψ + z·∂_z³Ψ` on the open quadrant. -/
theorem pzIter2_DzIter_one_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
      = 2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pzIter 3 Ψ z θ := by
  have hev : (fun z' => Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter 1 Ψ z' θ + z' * Work.Spaces.pzIter 2 Ψ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact pz_DzIter_one_eq hΨ hz' hθ
  have h1 : HasDerivAt (fun z' => Work.Spaces.pzIter 1 Ψ z' θ)
      (Work.Spaces.pzIter 2 Ψ z θ) z := hΨ.hasDerivAt_slice_pzIter 1 hθ hz
  have h2 : HasDerivAt (fun z' => z' * Work.Spaces.pzIter 2 Ψ z' θ)
      (1 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pzIter 3 Ψ z θ) z :=
    (hasDerivAt_id z).mul (hΨ.hasDerivAt_slice_pzIter 2 hθ hz)
  rw [show Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
      = deriv (fun z' => Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z' θ) z from rfl,
    hev.deriv_eq]
  rw [show deriv (fun z' => Work.Spaces.pzIter 1 Ψ z' θ + z' * Work.Spaces.pzIter 2 Ψ z' θ) z
      = deriv (fun z' => Work.Spaces.pzIter 1 Ψ z' θ) z
        + deriv (fun z' => z' * Work.Spaces.pzIter 2 Ψ z' θ) z from
      deriv_add h1.differentiableAt h2.differentiableAt, h1.deriv, h2.deriv]
  ring

/-- `D_z²Ψ = z²∂_z²Ψ + D_zΨ` on the open quadrant. -/
theorem dziter_two_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 Ψ z θ
      = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + Work.Spaces.DzIter 1 Ψ z θ := by
  rw [show Work.Spaces.DzIter 2 Ψ z θ
      = z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ from rfl,
    pz_DzIter_one_eq hΨ hz hθ]
  show z * (Work.Spaces.pzIter 1 Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ)
      = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ + z * Work.Spaces.pzIter 1 Ψ z θ
  ring

/-- `D_z(z²∂_z²Ψ) = z²∂_z²(D_zΨ)` on the open quadrant. -/
theorem dz_zsq_pzIter2_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z * Work.Spaces.pz (fun z' θ' => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ') z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ := by
  have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter 2 Ψ z' θ) z :=
    ((hΨ.pzIter 2).curry_z hθ).differentiableOn (by simp) |>.differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hsq : deriv (fun z' : ℝ => z' ^ 2) z = 2 * z := by
    have h1 : (fun z' : ℝ => z' ^ 2) = (fun z' : ℝ => z') * (fun z' : ℝ => z') := by
      funext z'
      show z' ^ 2 = ((fun z' : ℝ => z') * fun z' : ℝ => z') z'
      simp only [Pi.mul_apply]
      ring
    rw [h1, deriv_mul differentiableAt_id differentiableAt_id]
    simp
    ring
  have hpz : Work.Spaces.pz (fun z' θ' => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ') z θ
      = (2 * z) * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ := by
    show deriv (fun z' => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) z = _
    have hfun : (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
        = (fun z' : ℝ => z' ^ 2) * (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ) := by
      funext z'
      simp only [Pi.mul_apply]
    rw [hfun, deriv_mul (differentiableAt_pow 2) hd2, hsq,
      (hΨ.hasDerivAt_slice_pzIter 2 hθ hz).deriv]
  rw [hpz, pzIter2_DzIter_one_eq hΨ hz hθ]
  ring

/-! ## An elementary integrability criterion for the first `θ`-derivative

The only positive-exponent weight `sin(2θ)^c` is bounded, so it is enough to know that the
*second* derivative is weighted-square-integrable with the singular weight `sEta`: the
fundamental theorem of calculus on the open interval, Cauchy–Schwarz (`cs_interval_le`) and the
boundedness of the weight then give a *pointwise* bound on the first derivative. -/
theorem integrableOn_deriv_sq_mul_rpow {u : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ c) Iθ := by
  have hpi4 : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hdC1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    (hC 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont_d : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    (hC 1).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont_g : ContinuousOn (fun θ => deriv (fun t => deriv u t) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hdC1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hderiv_has : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x := fun x hx =>
    ((hdC1.differentiableOn (by norm_num)).differentiableAt
      (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  -- ## the fundamental theorem of calculus on the interval between `π/4` and `θ`
  have hsub : ∀ ⦃a b : ℝ⦄, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun a b ha hb x hx => ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have hsubIoo : ∀ ⦃a b : ℝ⦄, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun a b ha hb x hx => ⟨lt_trans ha.1 hx.1, lt_trans hx.2 hb.2⟩
  have hFTC : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv u θ - deriv u (Real.pi / 4)
        = ∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x := by
    intro θ hθ
    rcases le_total (Real.pi / 4) θ with hle | hle
    · have hcs : ContinuousOn (deriv u) (Set.Icc (Real.pi / 4) θ) :=
        hcont_d.mono (hsub hpi4 hθ)
      have hder : ∀ x ∈ Set.Ioo (Real.pi / 4) θ,
          HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x :=
        fun x hx => hderiv_has x (hsubIoo hpi4 hθ hx)
      have hi : IntervalIntegrable (fun x => deriv (fun t => deriv u t) x) volume
          (Real.pi / 4) θ :=
        (hcont_g.mono (hsub hpi4 hθ)).intervalIntegrable_of_Icc hle
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcs hder hi).symm
    · have hcs : ContinuousOn (deriv u) (Set.Icc θ (Real.pi / 4)) :=
        hcont_d.mono (hsub hθ hpi4)
      have hder : ∀ x ∈ Set.Ioo θ (Real.pi / 4),
          HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x :=
        fun x hx => hderiv_has x (hsubIoo hθ hpi4 hx)
      have hi : IntervalIntegrable (fun x => deriv (fun t => deriv u t) x) volume θ (Real.pi / 4) :=
        (hcont_g.mono (hsub hθ hpi4)).intervalIntegrable_of_Icc hle
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcs hder hi
      rw [intervalIntegral.integral_symm θ (Real.pi / 4), h]
      ring
  set R : ℝ := ∫ θ in Iθ, (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    with hR
  have hRnn : 0 ≤ R := by
    rw [hR]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ)
  have hpi2 : 0 ≤ Real.pi / 2 := by positivity
  set K : ℝ := 2 * ((deriv u (Real.pi / 4)) ^ 2 + (Real.pi / 2) * R) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]; nlinarith [sq_nonneg (deriv u (Real.pi / 4)), hRnn, hpi2]
  -- ## the pointwise bound
  have hbd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ c ≤ K := by
    intro θ hθ
    have h1 := hFTC θ hθ
    have h2 : (deriv u θ) ^ 2
        = (deriv u (Real.pi / 4)
            + ∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x) ^ 2 := by
      rw [← h1]; ring
    have ha : 0 ≤ min (Real.pi / 4) θ := le_min (le_of_lt hpi4.1) (le_of_lt hθ.1)
    have hb : max (Real.pi / 4) θ ≤ Real.pi / 2 :=
      max_le (le_of_lt hpi4.2) (le_of_lt hθ.2)
    have hab : min (Real.pi / 4) θ ≤ max (Real.pi / 4) θ := min_le_max
    have hcs := Work.FTS.EllipticEst.Mine.cs_interval_le hcont_g hint ha hb hab
    have hsplit : (deriv u (Real.pi / 4)
          + ∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x) ^ 2
        ≤ 2 * ((deriv u (Real.pi / 4)) ^ 2
            + (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x) ^ 2) := by
      nlinarith [sq_nonneg (deriv u (Real.pi / 4)
        - ∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)]
    have hsq : (deriv u θ) ^ 2 ≤ K := by
      rw [h2, hK]
      rcases le_total (Real.pi / 4) θ with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at hcs
        nlinarith [hsplit, hcs, hRnn]
      · rw [min_eq_right hle, max_eq_left hle] at hcs
        rw [intervalIntegral.integral_symm (Real.pi / 4) θ, neg_sq] at hcs
        nlinarith [hsplit, hcs, hRnn]
    have hsle : (Real.sin (2 * θ)) ^ c ≤ 1 :=
      Real.rpow_le_one (sin_two_nonneg_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
        (Real.sin_le_one _) hc
    calc (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ c
        ≤ (deriv u θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hsle (sq_nonneg _)
      _ = (deriv u θ) ^ 2 := by ring
      _ ≤ K := hsq
  -- ## almost everywhere strong measurability
  have haesm : AEStronglyMeasurable
      (fun θ => (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ c) (volume.restrict Iθ) := by
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine ((hcont_d.aestronglyMeasurable measurableSet_Ioo).pow 2).mul ?_
    exact (((Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Ioo hθ)))).aestronglyMeasurable measurableSet_Ioo
  -- ## conclusion
  haveI : IsFiniteMeasure (volume.restrict Iθ) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc, sub_zero]
        exact ENNReal.ofReal_lt_top⟩
  refine Integrable.mono' (integrable_const K) haesm ?_
  filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hbd,
    MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hbdθ hmem
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (sin_two_nonneg_Iθ hmem) _))]
  exact hbdθ

/-- `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`. -/
theorem sq_add_four_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- The radial source term `A = z²∂_z²Ψ` of the shifted slice. -/
noncomputable def srcA (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- `(w z / sin(2θ)^{η/2})² = w(z)²·sEta θ` on the angular interval. -/
theorem wdivsin_sq (z : ℝ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rw [div_pow, ← Real.rpow_natCast (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) 2,
    ← Real.rpow_mul hs (Work.Spaces.eta / 2) ((2 : ℕ) : ℝ),
    show Work.Spaces.eta / 2 * ((2 : ℕ) : ℝ) = Work.Spaces.eta by ring,
    Work.FTS.EllipticEst.sEta, Real.rpow_neg hs, div_eq_mul_inv]

/-- The `θ`-slice of a function smooth on the open quadrant is differentiable at interior
angles. -/
theorem differentiableAt_slice_θ' {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => G z θ') θ :=
  ((hG.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- `∂_θ` is additive on the slices of two functions. -/
theorem pth_add_of_diff' {f h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : DifferentiableAt ℝ (fun θ' => f z θ') θ)
    (hh : DifferentiableAt ℝ (fun θ' => h z θ') θ) :
    Work.Spaces.pth (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pth f z θ + Work.Spaces.pth h z θ := by
  simp only [Work.Spaces.pth]
  rw [show (fun θ' => f z θ' + h z θ') = (fun θ' => f z θ') + (fun θ' => h z θ') from rfl,
    deriv_add hf hh]

/-- `∂_θ` commutes with multiplication by a constant on slices. -/
theorem pth_const_mul_of_diff' {f : ℝ → ℝ → ℝ} (c : ℝ) {z θ : ℝ}
    (hf : DifferentiableAt ℝ (fun θ' => f z θ') θ) :
    Work.Spaces.pth (fun z θ => c * f z θ) z θ = c * Work.Spaces.pth f z θ := by
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_field]

/-- Extraction of the `(1,1)`-slot of the `ℋ²`-integrand of a `SmoothOpen` function: the
integrand `(∂_θ(D_z f))²·sin(2θ)^{2-γ}` is integrable on the angular slice. -/
theorem integrableOn_pth_DzIter_one {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Iθ := by
  have hslot := Work.FTS.EllipticEst.integrableOn_mixedSummand α 2 hf hm 1 1
    (by norm_num) (by norm_num) (Set.mem_Ici.mpr hz.le)
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have h1 : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hwz : Work.Spaces.w z ≠ 0 := fun hh => hw2 (by rw [hh]; ring)
  refine (hslot.const_mul ((Work.Spaces.w z) ^ 2)⁻¹).congr ?_
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
  filter_upwards with θ hθ
  have hw := hwz
  rw [Work.FTS.EllipticEst.H2W.Slot11Src.mixed11_Wt_sq_eq hf z θ hz hθ.1 hθ.2]
  field_simp

theorem slot11_src_int : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ → ∀ z ∈ Work.Spaces.Iz, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
          (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h z hzIz hz
  have hgam_lt : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have hgam_ne : Work.Spaces.gam α ≠ 2 := ne_of_lt hgam_lt
  have hsig_nn : ∀ θ ∈ Iθ, 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
    fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _
  -- ### the smoothness data
  have hΨ : SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hF : SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ)
      (fun z θ hz' hθ hθ' => h.eq z hz' θ hθ hθ')
  have hA : SmoothOpen (srcA Ψ) := by
    have h1 := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hΨ.pzIter 2)
    exact h1
  have hG : SmoothOpen (Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
      (Work.Spaces.DzIter 1 Ψ)) := by
    have h1 : SmoothOpen (Work.Spaces.DzIter 1 F) := hF.DzIter 1
    have h2 := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl ((hΨ.DzIter 1).pzIter 2)
    have h3 := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl ((hΨ.DzIter 1).pz)
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl h1
          (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) h2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α)) h3)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.EllipticEst.Mine.Gsrc]
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have h1 : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hwz : Work.Spaces.w z ≠ 0 := fun hh => hw2 (by rw [hh]; ring)
  -- ### the four integrable pieces
  let F1 : ℝ → ℝ := fun θ => (Work.Spaces.pth (Work.Spaces.DzIter 1 F) z θ) ^ 2
    * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
  let F2 : ℝ → ℝ := fun θ => (Work.Spaces.pth (Work.Spaces.DzIter 1 (srcA Ψ)) z θ) ^ 2
    * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
  let F3 : ℝ → ℝ := fun θ => (Work.Spaces.pth (srcA Ψ) z θ) ^ 2
    * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
  let F4 : ℝ → ℝ := fun θ => (Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
    * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
  have hF1 : MeasureTheory.IntegrableOn F1 Iθ := integrableOn_pth_DzIter_one hF h.memF hz
  have hF2 : MeasureTheory.IntegrableOn F2 Iθ := integrableOn_pth_DzIter_one hA h.memA hz
  have hF3 : MeasureTheory.IntegrableOn F3 Iθ := by
    have hslot := Work.FTS.EllipticEst.integrableOn_mixedSummand α 2 hA h.memA 1 0
      (by norm_num) (by norm_num) (Set.mem_Ici.mpr hz.le)
    have hstep : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.DthIter 1 (srcA Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.gam α))) Iθ := by
      refine (hslot.const_mul ((Work.Spaces.w z) ^ 2)⁻¹).congr ?_
      rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
      refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
      filter_upwards with θ hθ
      have hw := hwz
      rw [show Work.Spaces.mixed 0 1 (srcA Ψ) z θ = Work.Spaces.DthIter 1 (srcA Ψ) z θ from rfl,
        mul_pow, Wt_sq_eq α z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      field_simp
      first | rfl | ring
    refine hstep.congr ?_
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
    filter_upwards with θ hθ
    rw [show Work.Spaces.DthIter 1 (srcA Ψ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (srcA Ψ) z θ from rfl]
    exact mul_sq_rpow_neg (sin_two_nonneg_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) hgam_ne
  have hint4 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ := by
    have hB : SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hΨ.pth).pth
    have hpure := Work.FTS.EllipticEst.integrableOn_zSummand α 2 hB h.memB 1 (by norm_num) hzIz
    refine (hpure.const_mul ((Work.Spaces.w z) ^ 2)⁻¹).congr ?_
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
    filter_upwards with θ hθ
    have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
    have hcomm : Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
        = Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ :=
      Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 1 hQ
    show ((Work.Spaces.w z) ^ 2)⁻¹
          * (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ ^ 2
          * Work.FTS.EllipticEst.sEta θ
    rw [mul_pow, wdivsin_sq z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩, ← hcomm]
    field_simp <;> ring
  have hF4 : MeasureTheory.IntegrableOn F4 Iθ :=
    integrableOn_deriv_sq_mul_rpow (by linarith : (0:ℝ) ≤ 2 - Work.Spaces.gam α)
      (fun n => contDiffOn_iff_forall_nat_le.mp ((hΨ.DzIter 1).curry_θ hz) n le_top) hint4
  -- ### the pointwise bound on the open interval
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.pth (Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
          (Work.Spaces.DzIter 1 Ψ)) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
      ≤ 4 * (F1 θ + α ^ 4 * F2 θ + (α * (5 + α)) ^ 2 * F3 θ
          + (α * (5 + α)) ^ 2 * F4 θ) := by
    intro θ hθ
    have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    -- the decomposition of `∂_θ G`
    have hloc : (fun θ' => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
          (Work.Spaces.DzIter 1 Ψ) z θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter 1 F z θ'
            + α ^ 2 * (Work.Spaces.DzIter 1 (srcA Ψ) z θ')
            + (α * (5 + α)) * (srcA Ψ z θ' + Work.Spaces.DzIter 1 Ψ z θ')) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      simp only [Work.FTS.EllipticEst.Mine.Gsrc]
      rw [show z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ'
            = Work.Spaces.DzIter 1 (srcA Ψ) z θ' from
          (dz_zsq_pzIter2_eq hΨ hz hθ').symm,
        show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ'
            = srcA Ψ z θ' + Work.Spaces.DzIter 1 Ψ z θ' from
          dziter_two_eq hΨ hz hθ']
    have hderiv : Work.Spaces.pth (Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
        (Work.Spaces.DzIter 1 Ψ)) z θ
        = (Work.Spaces.pth (Work.Spaces.DzIter 1 F) z θ
            + α ^ 2 * Work.Spaces.pth (Work.Spaces.DzIter 1 (srcA Ψ)) z θ)
          + (α * (5 + α)) * (Work.Spaces.pth (srcA Ψ) z θ
              + Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) z θ) := by
      show deriv (fun θ' => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
          (Work.Spaces.DzIter 1 Ψ) z θ') θ = _
      rw [hloc.deriv_eq]
      show Work.Spaces.pth (fun z θ => Work.Spaces.DzIter 1 F z θ
            + α ^ 2 * Work.Spaces.DzIter 1 (srcA Ψ) z θ
            + α * (5 + α) * (srcA Ψ z θ + Work.Spaces.DzIter 1 Ψ z θ)) z θ = _
      have hdF1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DzIter 1 F z θ') θ :=
        differentiableAt_slice_θ' (hF.DzIter 1) hz hθ
      have hdB : DifferentiableAt ℝ (fun θ' => Work.Spaces.DzIter 1 (srcA Ψ) z θ') θ :=
        differentiableAt_slice_θ' (hA.DzIter 1) hz hθ
      have hdA : DifferentiableAt ℝ (fun θ' => srcA Ψ z θ') θ :=
        differentiableAt_slice_θ' hA hz hθ
      have hdP : DifferentiableAt ℝ (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') θ :=
        differentiableAt_slice_θ' (hΨ.DzIter 1) hz hθ
      have h1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DzIter 1 F z θ'
          + α ^ 2 * Work.Spaces.DzIter 1 (srcA Ψ) z θ') θ :=
        hdF1.add (hdB.const_mul (α ^ 2))
      have h2 : DifferentiableAt ℝ
          (fun θ' => α ^ 2 * Work.Spaces.DzIter 1 (srcA Ψ) z θ') θ := hdB.const_mul (α ^ 2)
      have h3 : DifferentiableAt ℝ (fun θ' => srcA Ψ z θ' + Work.Spaces.DzIter 1 Ψ z θ') θ :=
        hdA.add hdP
      have h4 : DifferentiableAt ℝ (fun θ' => α * (5 + α)
          * (srcA Ψ z θ' + Work.Spaces.DzIter 1 Ψ z θ')) θ := h3.const_mul (α * (5 + α))
      rw [pth_add_of_diff' (f := fun z θ => Work.Spaces.DzIter 1 F z θ
            + α ^ 2 * Work.Spaces.DzIter 1 (srcA Ψ) z θ)
          (h := fun z θ => α * (5 + α) * (srcA Ψ z θ + Work.Spaces.DzIter 1 Ψ z θ)) h1 h4,
        pth_add_of_diff' (f := Work.Spaces.DzIter 1 F)
          (h := fun z θ => α ^ 2 * Work.Spaces.DzIter 1 (srcA Ψ) z θ) hdF1 h2,
        pth_const_mul_of_diff' (f := Work.Spaces.DzIter 1 (srcA Ψ)) (α ^ 2) hdB,
        pth_const_mul_of_diff' (f := fun z θ => srcA Ψ z θ + Work.Spaces.DzIter 1 Ψ z θ)
          (α * (5 + α)) h3,
        pth_add_of_diff' (f := srcA Ψ) (h := Work.Spaces.DzIter 1 Ψ) hdA hdP]
    rw [hderiv]
    have hsq := sq_add_four_le (Work.Spaces.pth (Work.Spaces.DzIter 1 F) z θ)
      (α ^ 2 * Work.Spaces.pth (Work.Spaces.DzIter 1 (srcA Ψ)) z θ)
      ((α * (5 + α)) * Work.Spaces.pth (srcA Ψ) z θ)
      ((α * (5 + α)) * Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) z θ)
    have hexp : (Work.Spaces.pth (Work.Spaces.DzIter 1 F) z θ
          + α ^ 2 * Work.Spaces.pth (Work.Spaces.DzIter 1 (srcA Ψ)) z θ
          + (α * (5 + α)) * Work.Spaces.pth (srcA Ψ) z θ
          + (α * (5 + α)) * Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        = ((Work.Spaces.pth (Work.Spaces.DzIter 1 F) z θ
            + α ^ 2 * Work.Spaces.pth (Work.Spaces.DzIter 1 (srcA Ψ)) z θ)
          + (α * (5 + α)) * (Work.Spaces.pth (srcA Ψ) z θ
              + Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) z θ)) ^ 2 := by ring
    rw [← hexp]
    refine (mul_le_mul_of_nonneg_right hsq (hsig_nn θ hθI)).trans (le_of_eq ?_)
    simp only [F1, F2, F3, F4]
    ring
  -- ### almost everywhere strong measurability
  have haesm : AEStronglyMeasurable
      (fun θ => (Work.Spaces.pth (Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
          (Work.Spaces.DzIter 1 Ψ)) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) (volume.restrict Iθ) := by
    refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
      ((Work.Spaces.pth (fun z θ => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
          (Work.Spaces.DzIter 1 Ψ) z θ)) p.1 p.2) ^ 2
        * Real.rpow (Real.sin (2 * p.2)) (2 - Work.Spaces.gam α)) ?_ hz
    exact ((hG.pth).continuousOn.pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (sin_two_pos_Ioo hp.2))))
  -- ### the dominating integrable function
  have hBnd : MeasureTheory.Integrable (fun θ => 4 * (F1 θ + α ^ 4 * F2 θ
      + (α * (5 + α)) ^ 2 * F3 θ + (α * (5 + α)) ^ 2 * F4 θ)) (volume.restrict Iθ) := by
    have h2 : MeasureTheory.Integrable (fun θ => α ^ 4 * F2 θ) (volume.restrict Iθ) :=
      hF2.const_mul _
    have h3 : MeasureTheory.Integrable (fun θ => (α * (5 + α)) ^ 2 * F3 θ)
        (volume.restrict Iθ) := hF3.const_mul _
    have h4 : MeasureTheory.Integrable (fun θ => (α * (5 + α)) ^ 2 * F4 θ)
        (volume.restrict Iθ) := hF4.const_mul _
    exact (((hF1.add h2).add h3).add h4).const_mul 4
  -- ### conclusion
  refine MeasureTheory.Integrable.mono' hBnd haesm ?_
  filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt,
    MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hptθ hmem
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hsig_nn θ hmem))]
  exact hptθ

end Work.FTS.EllipticEst.H2W
