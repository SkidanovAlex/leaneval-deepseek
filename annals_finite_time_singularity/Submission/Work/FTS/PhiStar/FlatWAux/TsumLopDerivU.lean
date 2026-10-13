/-
The "un-summable majorant" version of `TsumLopDeriv`.

`Work.FTS.PhiStar.FlatWAux.TsumLopDeriv` proves the identity
`(Lop^[i]) (deriv (∑_m c m · q m)) θ = ∑_m c m · (Lop^[i]) (deriv (q m)) θ`
under the extra hypothesis that the majorant `B` itself is summable.  That hypothesis is
never used: every place where a domination by a summable family is needed uses only
`hcB : Summable (m ↦ |c m| * B m)`.  This file records that the identity therefore holds
without `Summable B`.

The proof is a verbatim adaptation of the proof of `TsumLopDeriv`.

The analytic input is the classical one: on an *open* interval on which the derivatives
converge and the derivatives of the summands are uniformly dominated by a summable family,
a `tsum` is differentiable with the sum of the derivatives as its derivative
(`hasDerivAt_tsum_of_isPreconnected`).  The uniform domination of the `i`-fold `Lop`
iterates by `K · B` on a compact subinterval is supplied by
`TsumLopDerivAux.Lop_iter_deriv_bound`, and the derivative of the summed family by
`TsumLopDerivAux.tsum_Lop_iter_deriv_hasDerivAt`; neither uses `Summable B`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped Real Topology
open Filter

theorem TsumLopDerivU (c : ℕ → ℝ) (q : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hB0 : ∀ m : ℕ, 0 ≤ B m)
    (hcB : Summable fun m : ℕ => |c m| * B m)
    (hq : ∀ m : ℕ, ContDiffOn ℝ 8 (q m) (Set.Ioo 0 (Real.pi / 2)))
    (hqb : ∀ (m r : ℕ), r ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |iteratedDeriv r (q m) θ| ≤ B m) :
    ∀ i : ℕ, i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.Lop^[i]) (deriv (fun θ' => ∑' m : ℕ, c m * q m θ')) θ
        = ∑' m : ℕ, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) θ := by
  set F : ℝ → ℝ := fun θ' => ∑' m : ℕ, c m * q m θ' with hFdef
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hqtr : (Real.pi / 4) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have key : ∀ i : ℕ, i ≤ 6 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i]) (deriv F) θ
        = ∑' m, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) θ := by
    intro i
    induction i with
    | zero =>
        intro _ θ hθ
        simp only [Function.iterate_zero_apply]
        have hd : HasDerivAt F (∑' m, c m * deriv (q m) θ) θ := by
          refine hasDerivAt_tsum_of_isPreconnected
            (u := fun m : ℕ => |c m| * B m)
            (g := fun m (y : ℝ) => c m * q m y)
            (g' := fun m (y : ℝ) => c m * deriv (q m) y)
            hcB hU isPreconnected_Ioo ?_ ?_ hqtr ?_ hθ
          · intro m y hy
            have hdiff : DifferentiableAt ℝ (q m) y :=
              ((hq m).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
            exact hdiff.hasDerivAt.const_mul (c m)
          · intro m y hy
            rw [Real.norm_eq_abs, abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            simpa only [iteratedDeriv_one] using hqb m 1 (by norm_num) y hy
          · refine Summable.of_norm_bounded hcB (fun m => ?_)
            rw [Real.norm_eq_abs, abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            simpa only [iteratedDeriv_zero] using hqb m 0 (by norm_num) (Real.pi / 4) hqtr
        rw [hd.deriv]
    | succ i ih =>
        intro hi6 θ hθ
        have hi5 : i ≤ 5 := by omega
        set a : ℝ := θ / 2 with hadef
        set b : ℝ := (θ + Real.pi / 2) / 2 with hbdef
        have ha : 0 < a := by rw [hadef]; linarith [hθ.1]
        have hab : a ≤ b := by rw [hadef, hbdef]; linarith [Real.pi_pos]
        have hb : b < Real.pi / 2 := by rw [hbdef]; linarith [hθ.2]
        have hθab : θ ∈ Set.Ioo a b := by
          constructor
          · rw [hadef]; linarith [hθ.1]
          · rw [hbdef]; linarith [hθ.2]
        have hsub : Set.Ioo a b ⊆ Set.Ioo 0 (Real.pi / 2) := fun y hy =>
          ⟨by linarith [hy.1], by linarith [hy.2, hb]⟩
        have hIH : ∀ y ∈ Set.Ioo a b,
            (Work.Spaces.Lop^[i]) (deriv F) y
              = ∑' m, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) y :=
          fun y hy => ih (by omega) y (hsub hy)
        obtain ⟨Kv, K', hKv0, hK'0, hbnd⟩ :=
          TsumLopDerivAux.Lop_iter_deriv_bound q B hq hqb i 1 (by omega) (by omega) ha hab hb
        have hbval : ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Set.Icc a b →
            |(Work.Spaces.Lop^[i]) (deriv (q m)) θ'| ≤ Kv * B m := by
          intro m θ' hθ'
          simpa only [iteratedDeriv_one] using (hbnd m θ' hθ').1
        have hbnd' : ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Set.Icc a b →
            |deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ'| ≤ K' * B m := by
          intro m θ' hθ'
          simpa only [iteratedDeriv_one] using (hbnd m θ' hθ').2
        have hderiv := TsumLopDerivAux.tsum_Lop_iter_deriv_hasDerivAt c q B hcB hq i (by omega)
          ha hab hb K' Kv hK'0 hKv0 hbnd' hbval θ hθab
        calc (Work.Spaces.Lop^[i + 1]) (deriv F) θ
            = Real.sin (2 * θ) * deriv ((Work.Spaces.Lop^[i]) (deriv F)) θ := by
                rw [show (Work.Spaces.Lop^[i + 1]) (deriv F)
                    = Work.Spaces.Lop ((Work.Spaces.Lop^[i]) (deriv F)) from
                      Function.iterate_succ_apply' Work.Spaces.Lop i (deriv F)]
                rfl
          _ = Real.sin (2 * θ)
                * deriv (fun y : ℝ => ∑' m, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) y) θ := by
                congr 1
                exact Filter.EventuallyEq.deriv_eq (by
                  filter_upwards [isOpen_Ioo.mem_nhds hθab] with y hy
                  exact hIH y hy)
          _ = Real.sin (2 * θ)
                * (∑' m, c m * deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ) := by
                rw [hderiv.deriv]
          _ = ∑' m, c m * (Real.sin (2 * θ)
                * deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ) := by
                rw [← tsum_mul_left]
                exact tsum_congr fun m => by ring
          _ = ∑' m, c m * (Work.Spaces.Lop^[i + 1]) (deriv (q m)) θ := by
                refine tsum_congr fun m => ?_
                congr 1
                rw [show (Work.Spaces.Lop^[i + 1]) (deriv (q m))
                    = Work.Spaces.Lop ((Work.Spaces.Lop^[i]) (deriv (q m))) from
                      Function.iterate_succ_apply' Work.Spaces.Lop i (deriv (q m))]
                rfl
  intro i hi θ hθ
  simpa only [hFdef] using key i hi θ hθ

end Work.FTS.PhiStar.FlatWAux
