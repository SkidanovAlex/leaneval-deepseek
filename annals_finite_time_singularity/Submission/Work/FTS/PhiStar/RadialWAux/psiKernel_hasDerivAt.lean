import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.PhiPsiDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `psiKernel_hasDerivAt` — differentiation under the integral sign for the outer rescaled kernel

The function considered here is the kernel of the outer rescaled Green piece
`PsiP P c = fun z => ∫_{u > 1} c (z u) u^{-P-1} du` at a derivative level `j`:

  `z ↦ ∫_{u > 1} c^{(j)}(z u) u^{j-P-1} du`.

For `c` of class `C^14` on `(0,∞)` with the first `14` derivatives bounded by `B`, `j + 1 ≤ 14`
and `j + 1 < P` this function is differentiable at every `z > 0` and its derivative is the same
integral one order higher:

  `(d/dz) ∫_{u>1} c^{(j)}(zu) u^{j-P-1} du = ∫_{u>1} c^{(j+1)}(zu) u^{j+1-P-1} du`.

This is the level `j` form of `PsiP_iteratedDeriv` (equivalently of
`radPsiAux_kernel_hasDerivAt`, which is stated at order `22`); the proof is the standard
dominated-convergence argument, with dominating function `B u^{j-P}` on `(Ioi 1)` — integrable
because `j - P < -1`, i.e. precisely the hypothesis `(j : ℝ) + 1 < P`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

/-- On `(0,∞)` a function of class `C^14` has continuous `k`-th iterated derivative for `k ≤ 14`. -/
private lemma contOn_iteratedDeriv_fourteen {c : ℝ → ℝ} (hc : ContDiffOn ℝ 14 c (Set.Ioi 0))
    {k : ℕ} (hk : k ≤ 14) : ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) isOpen_Ioi.uniqueDiffOn
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- The `(k+1)`-st iterated derivative is the derivative of the `k`-th one, for a function of
class `C^14`. -/
private lemma hasDerivAt_iteratedDeriv_fourteen {c : ℝ → ℝ} {x : ℝ} {k : ℕ}
    (hc : ContDiffAt ℝ 14 c x) (hk : k < 14) :
    HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k c) x := by
    have h' := hc.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin (m := k)
      (show ((k : ℕ) : WithTop ℕ∞) < ((14 : ℕ) : WithTop ℕ∞) by exact_mod_cast hk)
      (show UniqueDiffOn ℝ (insert x (Set.univ : Set ℝ)) from by
        simpa using (uniqueDiffOn_univ (𝕜 := ℝ) (E := ℝ)))
    rw [differentiableWithinAt_univ] at h'
    simpa using h'
  have h1 : HasDerivAt (iteratedDeriv k c) (deriv (iteratedDeriv k c) x) x := hd.hasDerivAt
  simpa [iteratedDeriv_succ] using h1

theorem psiKernel_hasDerivAt {P B : ℝ} (hB : 0 ≤ B) {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ 14 h (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv 14 h B)
    {j : ℕ} (hj : j + 1 ≤ 14) (hjP : (j : ℝ) + 1 < P) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x : ℝ => ∫ u in Set.Ioi 1,
        iteratedDeriv j h (x * u) * u ^ ((j : ℝ) - P - 1))
      (∫ u in Set.Ioi 1,
        iteratedDeriv (j + 1) h (z * u) * u ^ (((j + 1 : ℕ) : ℝ) - P - 1)) z := by
  have hkle : j ≤ 14 := by omega
  have hlt : (j : ℝ) - P < -1 := by linarith
  have hlt' : (j : ℝ) - P - 1 < -1 := by linarith
  have hcont_j : ContinuousOn (iteratedDeriv j h) (Set.Ioi 0) :=
    contOn_iteratedDeriv_fourteen hh hkle
  have hcont_j1 : ContinuousOn (iteratedDeriv (j + 1) h) (Set.Ioi 0) :=
    contOn_iteratedDeriv_fourteen hh hj
  have hne : ∀ u ∈ Set.Ioi (1 : ℝ), u ≠ 0 := fun u hu => ne_of_gt (lt_trans zero_lt_one hu)
  have hrpow : ContinuousOn (fun u : ℝ => u ^ ((j : ℝ) - P - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hrpow1 : ContinuousOn (fun u : ℝ => u ^ (((j + 1 : ℕ) : ℝ) - P - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hcomp : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv j h (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_j.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hcomp1 : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv (j + 1) h (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_j1.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 1)) (s := Set.Ioi (0 : ℝ)) (x₀ := z)
    (F := fun x u : ℝ => iteratedDeriv j h (x * u) * u ^ ((j : ℝ) - P - 1))
    (F' := fun x u : ℝ => iteratedDeriv (j + 1) h (x * u)
      * u ^ (((j + 1 : ℕ) : ℝ) - P - 1))
    (bound := fun u : ℝ => B * u ^ ((j : ℝ) - P))
    (isOpen_Ioi.mem_nhds hz)
    (by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ((hcomp x hx).mul hrpow).aestronglyMeasurable measurableSet_Ioi)
    (by
      refine MeasureTheory.Integrable.mono'
        ((integrableOn_Ioi_rpow_of_lt hlt' zero_lt_one).const_mul B)
        (((hcomp z hz).mul hrpow).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : 0 < u := lt_trans zero_lt_one hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu' _)]
      exact mul_le_mul_of_nonneg_right (hb j hkle (z * u) (mul_pos hz hu'))
        (le_of_lt (Real.rpow_pos_of_pos hu' _)))
    (by exact ((hcomp1 z hz).mul hrpow1).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha' _),
        show (((j + 1 : ℕ) : ℝ) - P - 1) = (j : ℝ) - P from by push_cast; ring]
      exact mul_le_mul_of_nonneg_right (hb (j + 1) hj (x * a) (mul_pos hx ha'))
        (le_of_lt (Real.rpow_pos_of_pos ha' _)))
    (by exact (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul B)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      have hid : HasDerivAt (fun y : ℝ => y * a) a x := by
        simpa using (hasDerivAt_id x).mul_const a
      have hca : ContDiffAt ℝ 14 h (x * a) :=
        hh.contDiffAt (isOpen_Ioi.mem_nhds (mul_pos hx ha'))
      have hd := hasDerivAt_iteratedDeriv_fourteen hca (by omega : j < 14)
      have hcomp' := hd.comp x hid
      have hfun : (iteratedDeriv j h ∘ fun y : ℝ => y * a) =
          fun y : ℝ => iteratedDeriv j h (y * a) := rfl
      rw [hfun] at hcomp'
      have hres := hcomp'.mul_const (a ^ ((j : ℝ) - P - 1))
      have hval : ((iteratedDeriv (j + 1) h (x * a) * a) * a ^ ((j : ℝ) - P - 1))
          = iteratedDeriv (j + 1) h (x * a) * a ^ (((j + 1 : ℕ) : ℝ) - P - 1) := by
        rw [show (((j + 1 : ℕ) : ℝ) - P - 1) = 1 + ((j : ℝ) - P - 1) from by push_cast; ring,
          Real.rpow_add ha', Real.rpow_one]
        ring
      rw [hval] at hres
      exact hres)
  exact hmain.2

end Work.FTS.PhiStar.RadialWAux
