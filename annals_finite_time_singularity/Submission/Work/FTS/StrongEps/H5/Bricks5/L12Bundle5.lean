/-
# `H5/Bricks5/L12Bundle5` — the level-`5` open-quadrant `L₁₂`-bundle

`L₁₂(g)(z) = ∫_z^∞ ∫_θ K(θ)·g(r,θ)/r dθ dr` is the radial function of Elgindi's
Prop. `L12H` (tex 1276).  For a source `g` which is `C^∞` on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen g`) and lies in the weighted space `ℋ⁵`
(`Work.Spaces.HkMem α 5 g`), with `L₁₂(g)(0) = 0`, and given

* the `z`-differentiation of the angular moments, `∂_z(Qang g j) z = Qang g (j+1) z / z` for
  `j ≤ 3` (`Work.FTS.StrongEps.H5.Atoms.QangDiff5`),
* the weighted `L²`-finiteness of the zeroth moment, `∫ (Qang g 0)² w² < ∞`
  (`Work.FTS.StrongEps.H5.Atoms.QangSq5`),

this module proves the three facts about `L₁₂` needed by the level-`5` `L12H` clause:

* the index-raising recursion `D_z^{k+1} L₁₂(g) = -Qang g k` for `k ≤ 4`;
* `z ↦ L₁₂(g)(z)² w(z)²` is integrable on `Iz = [0,∞)`;
* the weighted Hardy estimate `∫ L₁₂(g)² w² ≤ 107 ∫ (Qang g 0)² w²`.

This is the level-`5` instance of the level-4 sibling
`Work.FTS.OpenPkg.l12_open_bundle` (and of the level-6 `Work.FTS.StrongPersist.l12L6_bundle`),
re-run with one more slot.  The only change in the argument is that the induction producing the
recursion now runs up to `k = 4` and therefore consumes the divided derivative of `Qang g j` for
`j ≤ 3` (supplied here as a hypothesis, so that this file does not depend on the `Qang`
level-`5` chain).  Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.H2.L12k0Q
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-`5` `L₁₂`-bundle.**  See the module docstring. -/
theorem l12Bundle5 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 5 g)
    (h0 : Work.Elliptic.L12 g 0 = 0)
    (hqder : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w)
        (Work.Elliptic.Qang g (j + 1) z / z) z)
    (hQint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
        Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z
          = - Work.Elliptic.Qang g k z) ∧
      MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  -- the level-four membership, used only to feed the (otherwise unused) hypothesis of `L12k0Q`
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem
  -- ## the `L₁₂`-density is integrable on `(0,∞)` and `L₁₂` has derivative `-L12dens`
  have hFstarDiv : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk α 5 g hO hmem
  have hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun (hFstarDiv.const_mul 3)
      (fun r _ => (Work.Elliptic.L12dens_eq_three_Fstar_div g r).symm) measurableSet_Ioi
  have h12deriv := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 5 g hO hmem
    (by norm_num : 2 ≤ 5)).2
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    refine (h12deriv z hz).congr_deriv ?_
    rw [Work.Elliptic.L12dens_eq_three_Fstar_div]
    ring
  have hcontd : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := by
    have hFcont := (Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 5 g hO hmem
      (by norm_num : 1 ≤ 5)).continuousOn
    have h : ContinuousOn (fun z => 3 * (Work.Elliptic.Fstar g z / z)) (Set.Ioi 0) :=
      continuousOn_const.mul (hFcont.div continuousOn_id (fun z hz => ne_of_gt hz))
    exact h.congr (fun z _ => Work.Elliptic.L12dens_eq_three_Fstar_div g z)
  -- ## the value formula's consequences: decay at `∞` and continuity on `[0,1]`
  obtain ⟨-, htend, hcont⟩ := Work.Elliptic.L12_values g hint h0
  -- ## the index-raising recursion, by induction up to `k = 4`
  have hgen : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
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
        rw [hdv, mul_neg, neg_inj, (hqder n (by omega) z hz).deriv,
          mul_div_cancel₀ _ (ne_of_gt hz)]
  -- ## the two weighted Hardy inequalities
  obtain ⟨hInt, hBound⟩ :=
    Work.FTS.H2.L12k0Q α g hmem4 hint hderiv hcontd hcont htend h0 hQint
  exact ⟨hgen, hInt, hBound⟩

end Work.FTS.StrongEps.H5
