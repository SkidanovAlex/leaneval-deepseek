/-
Copyright: work module for the Elgindi finite-time singularity project.

# The second derivative of the slice equation `Lzero1 u = g`

With `Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` the angular operator of the elliptic section,
differentiating the equation `Lzero1 u = g` twice gives

  `u'''' + g'' = (tan θ · u)''' - 6 u''`     on `(0, π/2)`,

which is the statement of `Work.FTS.EllipticEst.remov.slice5_eqn_deriv2`.  It is the order-`1`
input to the elliptic estimate: it lets one trade two derivatives of `g` for three derivatives
of the `sin/cos`-weighted quantity `tan θ · u` plus the second derivative of `u`.

The proof is the computation `iteratedDeriv 2 (Lzero1 u) = -u^{(4)} + (tan θ u)^{(3)} - 6u^{(2)}`,
obtained by first writing `Lzero1 u = -u'' + (tan θ u)' - 6u` as a function identity (via
`deriv f = iteratedDeriv 1 f`), then using the additivity of `iteratedDeriv` on sums
(`iteratedDeriv_add`, `iteratedDeriv_sub`, `iteratedDeriv_neg`, `iteratedDeriv_const_mul`) —
which needs the `C²`-smoothness of the two pieces at the point, itself a consequence of
`hu : ContDiffOn ℝ 4 u (0, π/2)` and the helper `contDiffAt_iteratedDeriv` of `cosBarIdents`.
Finally `g` agrees with `Lzero1 u` near every interior point, so its second derivative is that
of `Lzero1 u` (`Filter.EventuallyEq.iteratedDeriv_eq`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.cosBarIdents

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- `Lzero1 u` is `-u'' + (tan θ · u)' - 6u`, written in terms of `iteratedDeriv`. -/
lemma Lzero1_eq_iteratedDeriv (u : ℝ → ℝ) :
    Work.FTS.EllipticEst.Lzero1 u
      = -(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)
        - (fun t => 6 * u t) := by
  funext t
  have hd2 : deriv (fun s => deriv u s) t = iteratedDeriv 2 u t := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hd1 : deriv (fun s => Real.tan s * u s) t
      = iteratedDeriv 1 (fun s => Real.tan s * u s) t := by rw [iteratedDeriv_one]
  unfold Work.FTS.EllipticEst.Lzero1
  rw [hd2, hd1]
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]

/-- The second iterated derivative of `Lzero1 u` at an interior point:
`(Lzero1 u)'' = -u'''' + (tan θ · u)''' - 6u''`. -/
lemma iteratedDeriv_two_Lzero1 (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv 2 (Work.FTS.EllipticEst.Lzero1 u) θ
        = -iteratedDeriv 4 u θ
          + iteratedDeriv 3 (fun t => Real.tan t * u t) θ
          - 6 * iteratedDeriv 2 u θ := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  have hcosθ : Real.cos θ ≠ 0 := hcos_ne θ hθ
  have huAt : ContDiffAt ℝ 4 u θ := hu.contDiffAt hIoo
  have huC1 : ContDiffAt ℝ 1 u θ := huAt.of_le (by norm_num)
  have huC2 : ContDiffAt ℝ 2 u θ := huAt.of_le (by norm_num)
  have huC3 : ContDiffAt ℝ 3 u θ := huAt.of_le (by norm_num)
  have htanC3 : ContDiffAt ℝ 3 Real.tan θ := Real.contDiffAt_tan.mpr hcosθ
  have htuC3 : ContDiffAt ℝ 3 (fun s => Real.tan s * u s) θ := htanC3.mul huC3
  have hu2C2 : ContDiffAt ℝ 2 (iteratedDeriv 2 u) θ :=
    contDiffAt_iteratedDeriv (f := u) (n := 4) (k := 2) huAt (by norm_num)
  have htu1C2 : ContDiffAt ℝ 2 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    contDiffAt_iteratedDeriv (f := fun s => Real.tan s * u s) (n := 3) (k := 1) htuC3
      (by norm_num)
  rw [Lzero1_eq_iteratedDeriv]
  have hA : ContDiffAt ℝ 2
      (-(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    (ContDiffAt.neg hu2C2).add htu1C2
  have hB : ContDiffAt ℝ 2 (fun t => 6 * u t) θ := contDiffAt_const.mul huC2
  rw [iteratedDeriv_sub hA hB]
  have hA1 : ContDiffAt ℝ 2 (-(iteratedDeriv 2 u)) θ := ContDiffAt.neg hu2C2
  have hA2 : ContDiffAt ℝ 2 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ := htu1C2
  rw [iteratedDeriv_add hA1 hA2, iteratedDeriv_neg, iteratedDeriv_const_mul (6 : ℝ) huC2]
  rw [itd_comp_two_val 2 u θ, itd_comp_two_val 1 (fun s => Real.tan s * u s) θ]

theorem slice5_eqn_deriv2 (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (deriv (deriv u))) θ + deriv (deriv g) θ
        = deriv (deriv (deriv (fun t => Real.tan t * u t))) θ - 6 * deriv (deriv u) θ := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  -- `g` agrees with `Lzero1 u` near every interior point
  have hcong : Work.FTS.EllipticEst.Lzero1 u =ᶠ[𝓝 θ] g := by
    filter_upwards [hIoo] with t ht
    exact hode t ht
  -- hence `g'' = (Lzero1 u)''` there
  have hg2 : deriv (deriv g) θ
      = iteratedDeriv 2 (Work.FTS.EllipticEst.Lzero1 u) θ := by
    rw [← itd_two_val g θ, ← Filter.EventuallyEq.iteratedDeriv_eq 2 hcong]
  have hL2 := iteratedDeriv_two_Lzero1 u hu θ hθ
  -- rewrite every `deriv`-tower as an `iteratedDeriv`
  rw [hg2, hL2, ← itd_four_val u θ, ← itd_three_val (fun t => Real.tan t * u t) θ,
    ← itd_two_val u θ]
  ring

end Work.FTS.EllipticEst.remov
