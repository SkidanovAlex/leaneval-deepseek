import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.ClassCHon.Zpz.tendsto_intervalIntegral_zero_right
import Submission.Work.FTS.ClassCHon.Zpz.tendsto_limit_eq_zero_of_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter

namespace Work.FTS.ClassCHon.Zpz

/-- **Left-endpoint limit** (intended namespace `Work.FTS.ClassCHon.Zpz`, module
`Submission.Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_lower`).

If `c` is differentiable on `(0,∞)` and both `c t * t ^ (q - 1)` and its `t`-weighted derivative
`t * deriv c t * t ^ (q - 1)` are integrable on `(0,1)`, then `t ↦ c t * t ^ q` tends to `0` at
`0⁺`.  No hypothesis on the real exponent `q` is needed.

Route (tools available in Mathlib): `F t := c t * t ^ q` satisfies
`F' t = deriv c t * t ^ q + q * (c t * t ^ (q - 1))` on `(0,∞)`, which is `L¹` on `(0,1)` (because
`deriv c t * t ^ q = t * deriv c t * t ^ (q - 1)` for `t > 0`); so `t ↦ ∫ x in (0)..t, F' x` tends
to `0` at `0⁺` (`MeasureTheory.tendsto_setIntegral_of_antitone` applied to `s n = Set.Ioc 0 (1/(n+1))`,
whose intersection is empty, plus an `ε`-squeeze), and since
`F z - F t = ∫ x in t..z, F' x = ∫ x in (0)..z, F' x - ∫ x in (0)..t, F' x` for `0 < t < z`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt` plus additivity of interval integrals), `F` has
the finite limit `C := F z - ∫ x in (0)..z, F' x` at `0⁺`.  Finally `C = 0`: if `C ≠ 0` then
`|c t * t ^ (q - 1)| = |F t| / t ≥ |C| / (2 * t)` for all small `t`, contradicting `h0` because
`∫ x in a..b, 1/x = Real.log (b / a) → ∞` as `a → 0⁺` (`integral_one_div_of_pos`). -/
theorem rpow_mul_tendsto_zero_lower {q : ℝ} {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ (q - 1)) (Set.Ioo 0 1))
    (hd0 : MeasureTheory.IntegrableOn (fun t => t * deriv c t * t ^ (q - 1))
      (Set.Ioo 0 1)) :
    Filter.Tendsto (fun t => c t * t ^ q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set F : ℝ → ℝ := fun t => c t * t ^ q with hFdef
  -- `t ^ q = t ^ (q - 1) * t` for `t > 0`
  have hrpow : ∀ t : ℝ, 0 < t → t ^ q = t ^ (q - 1) * t := by
    intro t ht
    have h := Real.rpow_add ht (q - 1) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  -- the pointwise formula for `deriv F` on `(0,1)`
  have hderiv_eq : ∀ t ∈ Set.Ioo 0 1, deriv F t
      = t * deriv c t * t ^ (q - 1) + q * (c t * t ^ (q - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h2 : HasDerivAt (fun s : ℝ => s ^ q) (q * t ^ (q - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    have h : HasDerivAt F (deriv c t * t ^ q + c t * (q * t ^ (q - 1))) t := by
      rw [hFdef]
      exact (hcd t ht0).mul h2
    rw [h.deriv, hrpow t ht0]
    ring
  -- `F` is differentiable on `(0,∞)` with derivative `deriv F`
  have hder : ∀ t : ℝ, 0 < t → HasDerivAt F (deriv F t) t := by
    intro t ht
    have h2 : HasDerivAt (fun s : ℝ => s ^ q) (q * t ^ (q - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht.ne')
    have h : HasDerivAt F (deriv c t * t ^ q + c t * (q * t ^ (q - 1))) t := by
      rw [hFdef]
      exact (hcd t ht).mul h2
    rw [h.deriv]
    exact h
  -- `deriv F` is integrable on `(0,1)`
  have hint : MeasureTheory.IntegrableOn (deriv F) (Set.Ioo 0 1) := by
    have hg : MeasureTheory.IntegrableOn
        (fun t => t * deriv c t * t ^ (q - 1) + q * (c t * t ^ (q - 1))) (Set.Ioo 0 1) :=
      hd0.add (h0.const_mul q)
    refine hg.congr_fun ?_ measurableSet_Ioo
    intro t ht
    exact (hderiv_eq t ht).symm
  -- the primitive of `deriv F` tends to `0` at `0⁺`
  have hA : Filter.Tendsto (fun t => ∫ x in (0)..t, deriv F x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) :=
    tendsto_intervalIntegral_zero_right hint
  -- the fundamental theorem of calculus on `[t, 1/2]`
  have hFTC : ∀ t ∈ Set.Ioo 0 (1/2 : ℝ),
      F (1/2) - F t = (∫ x in (0)..(1/2 : ℝ), deriv F x) - ∫ x in (0)..t, deriv F x := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htz : t < 1/2 := ht.2
    have hi_t : IntervalIntegrable (deriv F) volume (0:ℝ) t := by
      rw [intervalIntegrable_iff]
      refine hint.mono_set ?_
      rw [Set.uIoc_of_le ht0.le]
      intro x hx
      exact ⟨hx.1, by linarith [hx.2]⟩
    have hi_z : IntervalIntegrable (deriv F) volume t (1/2 : ℝ) := by
      rw [intervalIntegrable_iff]
      refine hint.mono_set ?_
      rw [Set.uIoc_of_le htz.le]
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals hi_t hi_z
    have hftc : F (1/2) - F t = ∫ x in t..(1/2:ℝ), deriv F x := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (f' := deriv F) ?_ hi_z
      · linarith [h]
      · intro x hx
        rw [Set.uIcc_of_le htz.le] at hx
        exact hder x (by linarith [hx.1])
    linarith [hadd, hftc]
  -- the limit of `F` at `0⁺`
  set C : ℝ := F (1/2) - ∫ x in (0)..(1/2 : ℝ), deriv F x with hCdef
  have hev : (fun t => C + ∫ x in (0)..t, deriv F x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] F := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1/2 by norm_num)] with t ht
    have h := hFTC t ht
    rw [hCdef]
    linarith [h]
  have hlim : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds C) := by
    have hA' : Filter.Tendsto (fun t => C + ∫ x in (0)..t, deriv F x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds C) := by
      simpa using hA.const_add C
    exact Filter.Tendsto.congr' hev hA'
  -- the limit can only be `0`
  have hC0 : C = 0 :=
    tendsto_limit_eq_zero_of_rpow (F := F) (c := c) (q := q) (fun t _ => by rw [hFdef]) h0 hlim
  have hfin : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [hC0] at hlim
    exact hlim
  rw [hFdef] at hfin
  exact hfin

end Work.FTS.ClassCHon.Zpz
