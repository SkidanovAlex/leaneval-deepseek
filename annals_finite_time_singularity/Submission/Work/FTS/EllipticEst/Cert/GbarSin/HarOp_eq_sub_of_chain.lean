/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integration by parts for the weighted Hardy operator, from the chain relation

The weighted Hardy operator of `GbarSetup.lean` is

  `HarOp β g z = z^{-β} ∫_0^z s^{β-1} g(s) ds`.

Let `v` be related to a function `u` by the *chain relation*

  `u z - u s = ∫_s^z v r / r dr`   for every `s ∈ (0, z)`,

i.e. `u` is a primitive of `s ↦ v s / s` on `(0,z)`, shifted by a constant.  This module proves
the integration by parts identity

  `HarOp β v z = u z - β * HarOp β u z`   (`1 < β`, `z > 0`),

the `D_z`-conjugation form of the Hardy operator: in the application `u = F_*(D_z^j F)` and
`v = F_*(D_z^{j+1} F) = D_z u`, and the identity is exactly
`HarOp β (D_z u) z = u z - β HarOp β u z`, which converts `u - β HarOp β u` back into a Hardy
operator applied to the *derivative* (`Cert/GbarSin/OpenCore.lean`, radial identity
`D_z^j Ḡ = -(3/(4α)) HarOp (5/α) (F_*(D_z^j F))`).

## The proof

Only the interval integrability of `s ↦ v s / s` on `(0,z)` is assumed (no continuity of `v`, and
`u` is known only through the chain relation), so the argument is run through the primitive

  `F s = ∫_0^s v r / r dr`,

which is absolutely continuous on `[0,z]`
(`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`), with `F = u - c` on
`(0,z)`, where `c = u z - F z`.  Then

* `s^{β-1} v s = s^β (v s / s)` pointwise (both sides vanish at `s = 0` since `β > 1`), so
  `∫_0^z s^{β-1} v s ds = ∫_0^z s^β (v s / s) ds`;
* *integration by parts for absolutely continuous functions*
  (`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`, applied to `s ↦ s^β`, which
  is `C¹` for `β > 1`, and to `F`, with `deriv F = v s / s` a.e. by
  `IntervalIntegrable.ae_hasDerivAt_integral`) gives
  `∫_0^z s^β (v s / s) ds = z^β F z - β ∫_0^z s^{β-1} F s ds`;
* `F = u - c` on `(0,z)` (plus the vanishing weight at `0`) gives
  `∫_0^z s^{β-1} u s ds = ∫_0^z s^{β-1} F s ds + c · ∫_0^z s^{β-1} ds`
  and `∫_0^z s^{β-1} ds = z^β / β`.

Dividing the resulting identity `∫_0^z s^{β-1} v s ds = z^β u z - β ∫_0^z s^{β-1} u s ds`
by `z^β > 0` is the claim.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.GbarSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.GbarSin

open MeasureTheory Set Filter
open scoped Topology

/-- For `1 < β` and `0 ≤ x` one has `x ^ (β - 1) * x = x ^ β`. -/
theorem rpow_sub_one_mul_self_aux {β : ℝ} (hβ : 1 < β) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (β - 1) * x = x ^ β := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0, Real.zero_rpow (x := β - 1) (by linarith), zero_mul,
      Real.zero_rpow (x := β) (ne_of_gt (lt_trans zero_lt_one hβ))]
  · have h : x ^ β = x ^ (β - 1) * x ^ (1 : ℝ) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [h, Real.rpow_one]

theorem HarOp_eq_sub_of_chain (β : ℝ) (hβ : 1 < β) {u v : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn (fun r : ℝ => v r / r) (Set.Ioo 0 z))
    (hchain : ∀ s ∈ Set.Ioo (0 : ℝ) z, u z - u s = ∫ r in s..z, v r / r) :
    Work.FTS.EllipticEst.HarOp β v z = u z - β * Work.FTS.EllipticEst.HarOp β u z := by
  have hβ0 : (0 : ℝ) < β := lt_trans zero_lt_one hβ
  have hβm : (0 : ℝ) < β - 1 := by linarith
  have hzle : (0 : ℝ) ≤ z := hz.le
  set g : ℝ → ℝ := fun r => v r / r with hgdef
  have hintI : IntervalIntegrable g volume (0 : ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hzle).mpr hint
  set F : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, g r with hFdef
  have hFac : AbsolutelyContinuousOnInterval F (0 : ℝ) z :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral hintI (c := 0)
      (by simp [hzle])
  have hFcont : ContinuousOn F (Set.uIcc (0 : ℝ) z) := hFac.continuousOn
  set c : ℝ := u z - F z with hcdef
  set A : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * v s with hAdef
  set B : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * u s with hBdef
  set C : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * F s with hCdef
  -- ### the chain relation, in terms of the primitive `F`
  have hsub : ∀ s ∈ Set.Ioo (0 : ℝ) z, F s = u s - c := by
    intro s hs
    have h1 : u z - u s = ∫ r in s..z, g r := hchain s hs
    have hzi : IntervalIntegrable g volume s z := hintI.mono_set (by
      rw [uIcc_of_le hzle, uIcc_of_le hs.2.le]
      exact Icc_subset_Icc hs.1.le le_rfl)
    have h0i : IntervalIntegrable g volume (0 : ℝ) s := hintI.mono_set (by
      rw [uIcc_of_le hzle, uIcc_of_le hs.1.le]
      exact Icc_subset_Icc le_rfl hs.2.le)
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0i hzi
    have hus : u s = u z - ((∫ r in (0 : ℝ)..z, g r) - ∫ r in (0 : ℝ)..s, g r) := by
      linarith [hadd, h1]
    rw [hcdef, hFdef]
    linarith [hus]
  -- ### step 1: `s ^ (β-1) * v s = s ^ β * g s` pointwise
  have hA : A = ∫ s in (0 : ℝ)..z, s ^ β * g s := by
    rw [hAdef]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hzle] at hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, hgdef]
      simp only [Real.zero_rpow (x := β - 1) (by linarith),
        Real.zero_rpow (x := β) (ne_of_gt hβ0), zero_mul]
    · rw [hgdef]
      rw [← rpow_sub_one_mul_self_aux hβ h0.le]
      field_simp
  -- ### step 2: integration by parts
  have hpow_ac : AbsolutelyContinuousOnInterval (fun s : ℝ => s ^ β) (0 : ℝ) z :=
    ContDiffOn.absolutelyContinuousOnInterval fun x _ =>
      (Real.contDiffAt_rpow_const_of_le (x := x) (p := β) (n := 1)
        (by exact_mod_cast hβ.le : ((1 : ℕ) : ℝ) ≤ β)).contDiffWithinAt
  have hIbpRaw := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hpow_ac hFac
  have hderivF : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) z → deriv F x = g x := by
    filter_upwards [hintI.ae_hasDerivAt_integral] with x hx hxI
    exact (hx (Set.uIoc_subset_uIcc hxI) 0 (by simp [hzle])).deriv
  have hstep1 : (∫ x in (0 : ℝ)..z, x ^ β * deriv F x) = ∫ x in (0 : ℝ)..z, x ^ β * g x :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [hderivF] with x hx hxI
      rw [hx hxI])
  have hstep2 : (∫ x in (0 : ℝ)..z, deriv (fun s : ℝ => s ^ β) x * F x)
      = β * C := by
    have hp : ∀ x ∈ Set.uIcc (0 : ℝ) z,
        deriv (fun s : ℝ => s ^ β) x * F x = β * (x ^ (β - 1) * F x) := by
      intro x _
      rw [(Real.hasDerivAt_rpow_const (p := β) (Or.inr (le_of_lt hβ))).deriv]
      ring
    rw [intervalIntegral.integral_congr hp, intervalIntegral.integral_const_mul, hCdef]
  have hIbp : (∫ s in (0 : ℝ)..z, s ^ β * g s) = z ^ β * F z - β * C := by
    have hbd : ((fun s : ℝ => s ^ β) 0) * F 0 = 0 := by
      simp only [Real.zero_rpow (ne_of_gt hβ0), zero_mul]
    rw [hstep1, hstep2, hbd] at hIbpRaw
    simpa using hIbpRaw
  -- ### step 3: `∫_0^z x^{β-1} = z^β/β`
  have hrpowint : (∫ x in (0 : ℝ)..z, x ^ (β - 1)) = z ^ β / β := by
    have hInt : IntervalIntegrable (fun x : ℝ => x ^ (β - 1)) volume (0 : ℝ) z :=
      (Real.continuous_rpow_const hβm.le).continuousOn.intervalIntegrable
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) z,
        HasDerivAt (fun y : ℝ => y ^ β / β) (x ^ (β - 1)) x := by
      intro x _
      have h := (Real.hasDerivAt_rpow_const (p := β) (Or.inr (le_of_lt hβ)) (x := x)).div_const β
      convert h using 1
      field_simp
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
    rw [Real.zero_rpow (ne_of_gt hβ0), zero_div, sub_zero] at h
    exact h
  -- ### step 4: `B = C + c * (z^β/β)`
  have hBrel : B = C + c * (z ^ β / β) := by
    have hcongr1 : B = ∫ s in (0 : ℝ)..z, s ^ (β - 1) * (F s + c) := by
      rw [hBdef]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hzle] at hs
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · rw [← h0, Real.zero_rpow (x := β - 1) (by linarith), zero_mul, zero_mul]
      · rcases eq_or_lt_of_le hs.2 with hz' | hz'
        · rw [hz', hcdef, hFdef]
          ring
        · have hsI : s ∈ Set.Ioo (0 : ℝ) z := ⟨h0, hz'⟩
          rw [hsub s hsI]
          ring
    have hcongr2 : (∫ s in (0 : ℝ)..z, s ^ (β - 1) * (F s + c))
        = ∫ s in (0 : ℝ)..z, (s ^ (β - 1) * F s + c * s ^ (β - 1)) :=
      intervalIntegral.integral_congr fun s _ => by ring
    have hint1 : IntervalIntegrable (fun s : ℝ => s ^ (β - 1) * F s) volume (0 : ℝ) z :=
      (((Real.continuous_rpow_const hβm.le).continuousOn).mul hFcont).intervalIntegrable
    have hint2 : IntervalIntegrable (fun s : ℝ => c * s ^ (β - 1)) volume (0 : ℝ) z :=
      (continuous_const.mul (Real.continuous_rpow_const hβm.le)).continuousOn.intervalIntegrable
    have hadd := intervalIntegral.integral_add hint1 hint2
    have hcm : (∫ s in (0 : ℝ)..z, c * s ^ (β - 1)) = c * (z ^ β / β) := by
      rw [intervalIntegral.integral_const_mul, hrpowint]
    rw [hcongr1, hcongr2, hadd, hcm, hCdef]
  -- ### assembly
  show z ^ (-β) * A = u z - β * (z ^ (-β) * B)
  have hzpow : z ^ (-β) * z ^ β = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  rw [hA, hIbp, hBrel]
  have hL : z ^ (-β) * (z ^ β * F z - β * C) = F z - β * (z ^ (-β) * C) := by
    rw [mul_sub, ← mul_assoc, hzpow, one_mul]
    ring
  have hX : β * (z ^ (-β) * (C + c * (z ^ β / β))) = β * (z ^ (-β) * C) + c := by
    have h1 : z ^ (-β) * (c * (z ^ β / β)) = c / β := by
      rw [show c * (z ^ β / β) = z ^ β * (c / β) by ring, ← mul_assoc, hzpow, one_mul]
    rw [mul_add, h1]
    field_simp
  rw [hL, hX]
  linarith [hcdef]

end Work.FTS.EllipticEst.Cert.GbarSin
