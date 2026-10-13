/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.sliceDzMod` — the `θ`-Lipschitz modulus of `D_z^a (E g)`, `a ≤ 2`

For every linear `E` carrying the level-`8` existence class plus the two frozen packages on the
source class `ClassC α` (i.e. `Ctx α Ce E`), every `a ≤ 2`, every `0 < a₀ ≤ b₀`, there is a
constant `K > 0` with

  `|D_z^a (E g)(z,θ) − D_z^a (E g)(z,θ')| ≤ K · Xn₆ α g · |θ − θ'|`
  (`g ∈ ClassC α`, `z ∈ [a₀,b₀]`, `θ, θ' ∈ (0,π/2)`).

This is the `D_z^a`-shifted angular modulus that the "clause 2"/`PkgDecay` half of the producer
`pkgBoxH_of_ellClassOk` needs: it is *uniform in `g`* (the constant is proportional to the
`ℋ⁶`-norm `Xn₆ α g`) and it does not degrade as `θ, θ'` approach the endpoints.

## The argument

Write `f := fun t => D_z^a (E g)(z,t)` for the angular slice of `Ψ = E g` at a fixed `z > 0`.
Two *pointwise interior* bounds on `f` are available in the tree, both proportional to
`Xn₆ α g` and both uniform in `z ∈ [a₀,b₀]` and in `θ ∈ (0,π/2)`:

* the value bound `|f t| ≤ K₁·Xn₆ α g`, which is the mixed-jet bound
  `ProducerH.MixedJets.mixed_jets_le_Xn6` at `(j,i) = (a,0)` (`mixed a 0 = D_z^a`,
  `a + 0 ≤ 4`), valid on the open quadrant;
* the second angular derivative bound
  `|(deriv (deriv f)) t| ≤ K₂·Xn₆ α g`, which is
  `ProducerH.SecondDerivDz.second_theta_deriv_DzIter_le_Xn6` (`a ≤ 2`), obtained from the slice
  ODE `S'' = tan θ·S' + (cos θ)⁻²·S − 6S − G` with the sharp constant `6`.

A bounded function with a bounded *second* derivative on a bounded interval is Lipschitz: near a
point `t ∈ (0,π/2)` the mean value theorem gives an interior point `ξ` at distance ≤ `π/8` with
`|f' ξ| ≤ 2A/(π/8)`, and the mean value bound applied to `f'` moves the estimate from `ξ` to
`t` at the cost `B·(π/8)`.  So `|f'| ≤ 16A/π + Bπ/8` on all of `(0,π/2)`, and one more mean value
step gives the two-point bound with the constant `K = 2K₁/(π/8) + K₂·(π/8)`.

The two generic real-analysis facts used are `deriv_le_of_value_and_second_le` (proved below for
self-containment; an identical sibling lives in
`Submission/Work/FTS_EllLimOK/ProducerH/H2/deriv_le_of_value_and_second_le.lean`) and
`abs_sub_le_of_deriv_abs_le` (imported from the sibling module
`Submission.Work.FTS_EllLimOK.ProducerH.H2.abs_sub_le_of_deriv_abs_le`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgMid
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2Eg_modulus
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDerivDz.second_theta_deriv_DzIter_le_Xn6
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS_EllLimOK.ProducerH.H2.abs_sub_le_of_deriv_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## A Landau-type bound for the first derivative on a bounded interval -/

/-- **Landau-type bound.**  If `f : ℝ → ℝ` is `C²` on `(0,L)`, `|f| ≤ A` there and
`|f''| ≤ B` there, then `|f'| ≤ 2A/c + B·c` on `(0,L)`, for any shift `c > 0` with `2c < L`
(which guarantees that every `t ∈ (0,L)` has a point at distance `c` inside the interval in at
least one direction).

Proof: if `t ≤ c` use the mean value theorem for `f` on `[t, t+c]` (here `t + c ≤ 2c < L`) to
find `ξ ∈ (t,t+c)` with `|f' ξ| = |f(t+c) − f t| / c ≤ 2A/c`, then the mean value bound for `f'`
(convex mean value inequality on `deriv f`) to move from `ξ` to `t`, which costs `B·c`; if
`t > c` do the same with `[t−c, t]`. -/
private theorem deriv_le_of_value_and_second_le_aux {f : ℝ → ℝ} {L A B c : ℝ}
    (_hL : 0 < L) (hc : 0 < c) (h2c : 2 * c < L) (hB0 : 0 ≤ B)
    (hC : ContDiffOn ℝ 2 f (Set.Ioo 0 L))
    (hA : ∀ t ∈ Set.Ioo 0 L, |f t| ≤ A)
    (hBd : ∀ t ∈ Set.Ioo 0 L, |deriv (deriv f) t| ≤ B) :
    ∀ t ∈ Set.Ioo 0 L, |deriv f t| ≤ 2 * A / c + B * c := by
  have hs : UniqueDiffOn ℝ (Set.Ioo 0 L) := isOpen_Ioo.uniqueDiffOn
  -- `deriv f` is `C¹` on the interval
  have hder1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 L) :=
    (hC.derivWithin hs (by norm_num)).congr
      (fun x hx => by rw [derivWithin_of_isOpen isOpen_Ioo hx])
  have hcont : ContinuousOn f (Set.Ioo 0 L) := hC.continuousOn
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 L) := hC.differentiableOn (by norm_num)
  have hdiff1 : DifferentiableOn ℝ (deriv f) (Set.Ioo 0 L) := hder1.differentiableOn (by norm_num)
  -- the mean value bound for `deriv f` between two interior points
  have hcmp : ∀ p ∈ Set.Ioo 0 L, ∀ q ∈ Set.Ioo 0 L,
      |deriv f p - deriv f q| ≤ B * |p - q| := by
    intro p hp q hq
    have hd : ∀ x ∈ Set.Ioo 0 L, DifferentiableAt ℝ (deriv f) x := fun x hx =>
      hdiff1.differentiableAt (isOpen_Ioo.mem_nhds hx)
    have hb : ∀ x ∈ Set.Ioo 0 L, ‖deriv (deriv f) x‖ ≤ B := fun x hx => by
      simpa only [Real.norm_eq_abs] using hBd x hx
    have := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Ioo 0 L) hq hp
    simpa only [Real.norm_eq_abs] using this
  intro t ht
  -- a point `ξ` inside the interval, at distance at most `c` from `t`, where `deriv f` is small
  have hshallow : ∃ ξ ∈ Set.Ioo 0 L, |t - ξ| ≤ c ∧ |deriv f ξ| ≤ 2 * A / c := by
    rcases le_or_gt t c with hle | hlt
    · -- forward: the mean value theorem on `[t, t+c]`
      have hu0 : 0 < t + c := by linarith [ht.1, hc]
      have huL : t + c < L := by linarith [hle, h2c]
      have hu : t + c ∈ Set.Ioo 0 L := ⟨hu0, huL⟩
      have htu : t < t + c := by linarith
      obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope f htu
        (hcont.mono (fun x hx => ⟨by linarith [ht.1, hx.1], by linarith [hx.2, huL]⟩))
        (hdiff.mono (fun x hx => ⟨by linarith [ht.1, hx.1], by linarith [hx.2, huL]⟩))
      have hb : |f (t + c) - f t| ≤ 2 * A := by
        calc |f (t + c) - f t| ≤ |f (t + c) - 0| + |0 - f t| := abs_sub_le _ 0 _
          _ = |f (t + c)| + |f t| := by simp
          _ ≤ A + A := add_le_add (hA (t + c) hu) (hA t ht)
          _ = 2 * A := by ring
      have hden : (t + c) - t = c := by ring
      have hξeq' : deriv f ξ = (f (t + c) - f t) / c := by rw [hξeq, hden]
      refine ⟨ξ, ⟨by linarith [hξ.1, ht.1], by linarith [hξ.2, huL]⟩, ?_, ?_⟩
      · rw [abs_sub_comm]
        have : ξ - t < c := by linarith [hξ.2]
        rw [abs_of_pos (by linarith [hξ.1])]
        linarith
      · rw [hξeq', abs_div, abs_of_pos hc]
        calc |f (t + c) - f t| / c ≤ (2 * A) / c := div_le_div_of_nonneg_right hb hc.le
          _ = 2 * A / c := by ring
    · -- backward: the mean value theorem on `[t−c, t]`
      have hu0 : 0 < t - c := by linarith
      have huL : t - c < L := by linarith [ht.2]
      have hu : t - c ∈ Set.Ioo 0 L := ⟨hu0, huL⟩
      have hut : t - c < t := by linarith
      obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope f hut
        (hcont.mono (fun x hx => ⟨by linarith [hu0, hx.1], by linarith [hx.2, ht.2]⟩))
        (hdiff.mono (fun x hx => ⟨by linarith [hu0, hx.1], by linarith [hx.2, ht.2]⟩))
      have hb : |f t - f (t - c)| ≤ 2 * A := by
        calc |f t - f (t - c)| ≤ |f t - 0| + |0 - f (t - c)| := abs_sub_le _ 0 _
          _ = |f t| + |f (t - c)| := by simp
          _ ≤ A + A := add_le_add (hA t ht) (hA (t - c) hu)
          _ = 2 * A := by ring
      have hden : t - (t - c) = c := by ring
      have hξeq' : deriv f ξ = (f t - f (t - c)) / c := by rw [hξeq, hden]
      refine ⟨ξ, ⟨by linarith [hu0, hξ.1], by linarith [hξ.2, ht.2]⟩, ?_, ?_⟩
      · have : t - ξ < c := by linarith [hξ.1]
        rw [abs_of_nonneg (by linarith [hξ.2])]
        linarith
      · rw [hξeq', abs_div, abs_of_pos hc]
        calc |f t - f (t - c)| / c ≤ (2 * A) / c := div_le_div_of_nonneg_right hb hc.le
          _ = 2 * A / c := by ring
  obtain ⟨ξ, hξmem, hξc, hξbd⟩ := hshallow
  have hcmp' : |deriv f t - deriv f ξ| ≤ B * |t - ξ| := hcmp t ht ξ hξmem
  have hle : B * |t - ξ| ≤ B * c := mul_le_mul_of_nonneg_left hξc hB0
  have htri : |deriv f t| ≤ |deriv f t - deriv f ξ| + |deriv f ξ| := by
    have h : deriv f t = (deriv f t - deriv f ξ) + deriv f ξ := by ring
    calc |deriv f t| = |(deriv f t - deriv f ξ) + deriv f ξ| := congrArg abs h
      _ ≤ _ := abs_add_le _ _
  linarith [htri, hcmp', hle, hξbd]

/-! ## The angular modulus of `D_z^a (E g)` -/

theorem sliceDzMod {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    (a : ℕ) (ha : a ≤ 2) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.DzIter a (E g) z θ - Work.Spaces.DzIter a (E g) z θ'|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| := by
  -- ## the two pointwise interior bounds, both proportional to `Xn₆ α g`
  obtain ⟨K1, hK1, h1⟩ :=
    Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6 (α := α) (Ce := Ce) hα hα4 hE
  obtain ⟨K2, hK2, h2⟩ :=
    Work.FTS_EllLimOK.ProducerH.SecondDerivDz.second_theta_deriv_DzIter_le_Xn6
      (α := α) (Ce := Ce) hα hα4 hE a ha ha₀ hab
  refine ⟨2 * K1 / (π / 8) + K2 * (π / 8), by positivity, ?_⟩
  intro g hg z hz θ hθ θ' hθ'
  have hzpos : 0 < z := lt_of_lt_of_le ha₀ hz.1
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  -- ## the angular slice `f` of `Ψ = E g` at the radius `z`
  let f : ℝ → ℝ := fun t => Work.Spaces.DzIter a (E g) z t
  have hC2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (π / 2)) := by
    have hsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
    have hcur := (hsm.mixed a 0).curry_θ hzpos
    simpa only [f, Work.Spaces.mixed_zero_right] using
      hcur.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder)
  -- the value bound (`mixed_jets_le_Xn6` at `(j,i) = (a,0)`, `mixed a 0 = D_z^a`)
  have hA : ∀ t ∈ Set.Ioo 0 (π / 2), |f t| ≤ K1 * Work.FTS.StrongGlobal.Xn6 α g := by
    intro t ht
    simpa only [f, Work.Spaces.mixed_zero_right] using h1 g hg a 0 (by omega) z t ⟨hzpos, ht⟩
  -- the second angular derivative bound (`second_theta_deriv_DzIter_le_Xn6`)
  have hBd : ∀ t ∈ Set.Ioo 0 (π / 2),
      |deriv (deriv f) t| ≤ K2 * Work.FTS.StrongGlobal.Xn6 α g := by
    intro t ht
    simpa only [f] using h2 g hg z hz t ht
  -- ## the Landau step: `|f'| ≤ K·Xn₆ α g` on `(0,π/2)`
  have h2c : 2 * (π / 8) < π / 2 := by linarith [Real.pi_pos]
  have hd : ∀ t ∈ Set.Ioo 0 (π / 2),
      |deriv f t| ≤ 2 * (K1 * Work.FTS.StrongGlobal.Xn6 α g) / (π / 8)
        + (K2 * Work.FTS.StrongGlobal.Xn6 α g) * (π / 8) :=
    deriv_le_of_value_and_second_le_aux (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      h2c (mul_nonneg hK2.le hX0) hC2 hA hBd
  have hd' : ∀ t ∈ Set.Ioo 0 (π / 2),
      |deriv f t| ≤ (2 * K1 / (π / 8) + K2 * (π / 8)) * Work.FTS.StrongGlobal.Xn6 α g := by
    intro t ht
    refine le_trans (hd t ht) (le_of_eq ?_)
    ring
  -- ## the two-point bound
  have hC1 : ContDiffOn ℝ 1 f (Set.Ioo 0 (π / 2)) := hC2.of_le (by norm_num)
  have hres := abs_sub_le_of_deriv_abs_le hC1 hd' θ hθ θ' hθ'
  simpa only [f] using hres

end Work.FTS_EllLimOK.ProducerH.H2
