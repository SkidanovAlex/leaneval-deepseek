import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.EllipticEst.UopHk.L12_w_sq_integrable
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.H2.L12k0Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

/-- **The open-quadrant `L₁₂`-bundle.**  For `0 < α ≤ 1`, a source `g` which is `C^∞` on the
open quadrant (`Work.FTS.EllipticEst.SmoothOpen g`) and lies in the weighted space `ℋ⁴`
(`Work.Spaces.HkMem α 4 g`), with the associated singular term vanishing at the origin
(`Work.Elliptic.L12 g 0 = 0`), the three facts about the operator
`L₁₂(g)(z) = ∫_z^∞ ∫_θ K(θ) g(r,θ)/r dθ dr` needed by the consumer:

* the index-raising recursion `D_z^{k+1} L₁₂(g) = -Qang g k` for `k ≤ 3` (tex 1276--1290),
  where `Qang g k z = ∫_θ Kθ(θ)·(D_z^k g)(z,θ) dθ` is the `k`-th angular moment;
* `z ↦ L₁₂(g)(z)² w(z)²` is integrable on `Iz = [0,∞)`;
* the weighted Hardy estimate `∫ L₁₂(g)² w² ≤ 107 ∫ (Qang g 0)² w²`.

The three parts are supplied by already-proved results of the open-quadrant migration:
`QangDiff_open` (the divided derivative `∂_z Qang g j = Qang g (j+1)/z` on `z > 0`, the
`z`-input of the recursion, valid for `j ≤ 2`), `integrableOn_Fstar_div_of_smoothOpen_Hk` /
`contDiffOn_L12_of_smoothOpen_Hk` (integrability of the density and the derivative of `L₁₂`,
which feed `Work.Elliptic.L12_values` to give the decay at `∞` and continuity on `[0,1]`),
`Qang_sq_w_sq_integral_open` (the angular-moment denominator), and finally
`Work.FTS.H2.L12k0Q` (the two weighted Hardy inequalities on `(0,1)` and `(1,∞)`). -/
theorem l12_open_bundle (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Elliptic.L12 g 0 = 0) :
    (∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
        Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z
          = - Work.Elliptic.Qang g k z) ∧
      MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  -- ## the `L₁₂`-density is integrable on `(0,∞)` and `L₁₂` has derivative `-L12dens`
  have hFstarDiv : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk α 4 g hsm hmem
  have hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun (hFstarDiv.const_mul 3)
      (fun r _ => (Work.Elliptic.L12dens_eq_three_Fstar_div g r).symm) measurableSet_Ioi
  have h12deriv := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 g hsm hmem
    (by norm_num : 2 ≤ 4)).2
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    refine (h12deriv z hz).congr_deriv ?_
    rw [Work.Elliptic.L12dens_eq_three_Fstar_div]
    ring
  have hcontd : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := by
    have hFcont := (Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 4 g hsm hmem
      (by norm_num : 1 ≤ 4)).continuousOn
    have h : ContinuousOn (fun z => 3 * (Work.Elliptic.Fstar g z / z)) (Set.Ioi 0) :=
      continuousOn_const.mul (hFcont.div continuousOn_id (fun z hz => ne_of_gt hz))
    exact h.congr (fun z _ => Work.Elliptic.L12dens_eq_three_Fstar_div g z)
  -- ## the value formula's consequences: decay at `∞` and continuity on `[0,1]`
  obtain ⟨-, htend, hcont⟩ := Work.Elliptic.L12_values g hint h0
  -- ## the angular moment `Qang g 0`
  have hQint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open (α := α) (g := g) hα hα1 hsm hmem
      (i := 0) (by norm_num)).1
  -- ## the index-raising recursion
  have hQderiv := (Work.FTS.OpenPkg.QangOpen.QangDiff_open α g hα hα1 hsm hmem).1
  have hgen : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z
        = - Work.Elliptic.Qang g k z := by
    intro k
    induction k with
    | zero =>
        intro _ z hz
        have hd : deriv (fun z => Work.Elliptic.L12 g z) z = -(Work.Elliptic.L12dens g z) :=
          (hderiv z hz).deriv
        change z * deriv (fun z => Work.Elliptic.L12 g z) z = - Work.Elliptic.Qang g 0 z
        rw [hd, Work.Elliptic.L12dens_eq_Qang_div, mul_neg, neg_inj,
          mul_div_cancel₀ _ (ne_of_gt hz)]
    | succ n ih =>
        intro hn z hz
        have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)
            =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (by omega) z' hz'
        have hdv : deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
            = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
          rw [hev.deriv_eq]
          exact deriv.neg
        change z * deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
            = - Work.Elliptic.Qang g (n + 1) z
        rw [hdv, mul_neg, neg_inj, (hQderiv n (by omega) z hz).deriv,
          mul_div_cancel₀ _ (ne_of_gt hz)]
  -- ## the two weighted Hardy inequalities
  obtain ⟨hInt, hBound⟩ :=
    Work.FTS.H2.L12k0Q α g hmem hint hderiv hcontd hcont htend h0 hQint
  exact ⟨hgen, hInt, hBound⟩

end Work.FTS.OpenPkg
