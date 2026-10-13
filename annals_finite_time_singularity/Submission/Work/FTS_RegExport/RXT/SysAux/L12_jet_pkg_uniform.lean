import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_L12_aux
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_jet_pkg_uniform
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_tail_weight
import Submission.Work.FTS_RegExport.RXT.L12Iter.Tower
import Submission.Work.Construction.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.L12_jet_pkg_uniform` — the `L₁₂` half of the weighted jet
package, uniform in the datum

Given the datum package for `𝔽K u` (`FK_jet_pkg_uniform`: `C²` of `𝔽K u` on `(0,∞)`, the three
weighted `D_z`-jet bounds, and integrability/continuity of `𝔽K u r / r`), the radial transform
`L₁₂ u` inherits the same package:

* `D_z^j L₁₂ u` obeys the standing weighted bound `≤ C·z^{3/2}/(1+z)²` for `j ≤ 2`
  (`j = 0` is the sharpened tail bound `L12_tail_weight`, using the normalisation
  `L₁₂ u 0 = 0`; `j = 1, 2` are the two identities `D_z L₁₂ u = -𝔽K u`,
  `D_z² L₁₂ u = -D_z 𝔽K u`),
* `L₁₂ u` is `C³` on `(0,∞)` (`contDiffOn_three_L12`),
* `∂_z L₁₂ u = -𝔽K u/z` (`L12Iter.Construction_L12_hasDerivAt` together with
  `Construction.mul_L12dens_eq_FK`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS_RegExport.RXT.SysAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The `L₁₂`-half of the weighted jet package, uniform in the datum.** -/
theorem L12_jet_pkg_uniform (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0 →
      (∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a u z θ| ≤ B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) →
      Work.Construction.L12 u 0 = 0 →
      (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z (_ : ℝ) => Work.Construction.L12 u z) z 0|
          ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) ∧
      ContDiffOn ℝ 3 (fun z => Work.Construction.L12 u z) (Set.Ioi 0) ∧
      (∀ z : ℝ, 0 < z → HasDerivAt (fun z' => Work.Construction.L12 u z')
        (-(Work.Construction.FK u z) / z) z) := by
  obtain ⟨CFK, hCFKpos, hFKpkg⟩ := FK_jet_pkg_uniform B
  refine ⟨8 * CFK + 1, by linarith, ?_⟩
  intro u hCd hb h0
  obtain ⟨hFKjets, hFK0, hFKcont, hgint, hgcont⟩ := hFKpkg u hCd hb
  have hBnn : 0 ≤ max B 0 := le_max_right B 0
  -- the datum bound in the shape required by `L12Iter.Construction_L12_hasDerivAt`
  have hbRwt : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k u z θ| ≤ max B 0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z := by
    intro k hk z θ hz hθ hθ2
    have h1 : |Work.Spaces.DzIter k u z θ| ≤ B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero] using
        hb k 0 (by omega) z θ hz hθ hθ2
    have h2 : B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
        ≤ max B 0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z := by
      rw [Work.FTS_RegExport.RXT.L12Iter.Rwt]
      exact mul_le_mul_of_nonneg_right (le_max_left B 0) (by positivity)
    linarith [h1, h2]
  -- the derivative of `L₁₂ u`
  have hL12deriv : ∀ z : ℝ, 0 < z → HasDerivAt (fun z' => Work.Construction.L12 u z')
      (-(Work.Construction.FK u z) / z) z := by
    intro z hz
    have h := Work.FTS_RegExport.RXT.L12Iter.Construction_L12_hasDerivAt
      (f := u) hBnn hCd hbRwt hz
    have hval : Work.Construction.L12dens u z = Work.Construction.FK u z / z := by
      have h2 := Work.Construction.mul_L12dens_eq_FK (F := u) (ne_of_gt hz)
      rw [← h2, mul_div_cancel_left₀ _ (ne_of_gt hz)]
    simpa only [hval, neg_div] using h
  have hL12c3 : ContDiffOn ℝ 3 (fun z => Work.Construction.L12 u z) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFKcont
  -- `D_z L₁₂ u = -𝔽K u`
  have hL12jet1 : ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 u z) z 0|
        ≤ CFK * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro z hz
    have hval : Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 u z) z 0
        = -(Work.Construction.FK u z) := by
      show z * deriv (fun z' => Work.Construction.L12 u z') z = -(Work.Construction.FK u z)
      rw [(hL12deriv z hz).deriv]
      field_simp
    rw [hval, abs_neg]
    exact hFK0 z hz
  -- `D_z² L₁₂ u = -D_z 𝔽K u`
  have hL12jet2 : ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter 2 (fun z _ => Work.Construction.L12 u z) z 0|
        ≤ CFK * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro z hz
    have hdiff : DifferentiableAt ℝ (fun w : ℝ => Work.Construction.FK u w) z :=
      (hFKcont.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
    have hev : (fun w => Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 u z) w 0)
        =ᶠ[𝓝 z] fun w => -(Work.Construction.FK u w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      have hwpos : 0 < w := hw
      show w * deriv (fun z' => Work.Construction.L12 u z') w = -(Work.Construction.FK u w)
      rw [(hL12deriv w hwpos).deriv]
      field_simp
    have hderiv : deriv (fun w => Work.Spaces.DzIter 1
        (fun z _ => Work.Construction.L12 u z) w 0) z
        = -(deriv (fun w : ℝ => Work.Construction.FK u w) z) := by
      rw [hev.deriv_eq]
      exact (hdiff.hasDerivAt.neg).deriv
    have hval : Work.Spaces.DzIter 2 (fun z _ => Work.Construction.L12 u z) z 0
        = -Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK u z) z 0 := by
      show z * deriv (fun w => Work.Spaces.DzIter 1
          (fun z _ => Work.Construction.L12 u z) w 0) z
        = -(z * deriv (fun w : ℝ => Work.Construction.FK u w) z)
      rw [hderiv]
      ring
    rw [hval, abs_neg]
    exact hFKjets 1 (by norm_num) z hz
  -- the sharpened level-`0` tail bound
  have hL12jet0 : ∀ z : ℝ, 0 < z →
      |Work.Construction.L12 u z| ≤ 8 * CFK * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro z hz
    rw [Work.FTS_RegExport.RXT.L12_eq_integral_FK u z]
    refine L12_tail_weight (g := fun r : ℝ => Work.Construction.FK u r / r) (B := CFK)
      hCFKpos.le hz hgint ?_ ?_
    · intro r hr
      have h1 : |Work.Construction.FK u r| ≤ CFK * (r ^ ((3 : ℝ) / 2) / (1 + r) ^ 2) :=
        hFK0 r hr
      rw [abs_div, abs_of_pos hr]
      calc |Work.Construction.FK u r| / r
          ≤ (CFK * (r ^ ((3 : ℝ) / 2) / (1 + r) ^ 2)) / r :=
            div_le_div_of_nonneg_right h1 hr.le
        _ = CFK * (Real.sqrt r / (1 + r) ^ 2) := by
            rw [mul_div_assoc,
              show (r ^ ((3 : ℝ) / 2) / (1 + r) ^ 2) / r = L12Wt r / r from rfl,
              L12Wt_div_eq hr]
    · rw [← Work.FTS_RegExport.RXT.L12_eq_integral_FK u 0]
      exact h0
  refine ⟨?_, hL12c3, hL12deriv⟩
  intro j hj z hz
  have hnn : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 := by positivity
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl
  · have h : |Work.Spaces.DzIter 0 (fun z _ => Work.Construction.L12 u z) z 0|
        ≤ 8 * CFK * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
      simpa only [Work.Spaces.DzIter_zero] using hL12jet0 z hz
    calc |Work.Spaces.DzIter 0 (fun z _ => Work.Construction.L12 u z) z 0|
        ≤ 8 * CFK * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := h
      _ ≤ (8 * CFK + 1) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
  · calc |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 u z) z 0|
        ≤ CFK * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := hL12jet1 z hz
      _ ≤ (8 * CFK + 1) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
  · calc |Work.Spaces.DzIter 2 (fun z _ => Work.Construction.L12 u z) z 0|
        ≤ CFK * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := hL12jet2 z hz
      _ ≤ (8 * CFK + 1) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn

end

end Work.FTS_RegExport.RXT.SysAux
