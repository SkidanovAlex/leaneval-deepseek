/-
# `zcutFamDefs` — the explicit cut-off family `χ_n` and its two weighted derivatives

This module fixes the objects used in `Work.FTS.EllipticEst.Mine.zcutFam`: an explicit family of
smooth cut-offs `χ_n : ℝ → ℝ` which is `0` on `(-∞, 1/(n+1)]`, `1` on `[2/(n+1), n+1]` and `0`
on `[2(n+1), ∞)`, with *uniform* bounds on `z χ_n'(z)` and on `z (z χ_n')'(z)`.

The construction is the product of two rescalings of a single fixed smooth step
`Ψ t = Real.smoothTransition (t - 1)` (`0` on `(-∞,1]`, `1` on `[2,∞)`):

  `χ n z = Ψ ((n+1) z) · (1 - Ψ (z / (n+1)))`.

The first factor rises from `0` at `z = 1/(n+1)` (where `(n+1) z = 1`) to `1` at `z = 2/(n+1)`;
the second factor falls from `1` at `z = n+1` (where `z/(n+1) = 1`) to `0` at `z = 2(n+1)`.

For the derivative bounds one writes `A = zcScale n = n+1`, `B = A⁻¹`, and

  `k1 t := t · Ψ'(t)`,   `k2 t := t · k1'(t)`,

so that (with `u = A z`, `v = z B`)

  `z χ_n'(z) = k1 u · (1 - Ψ v) - Ψ u · k1 v`,
  `z (z χ_n')'(z) = k2 u · (1 - Ψ v) - 2 (k1 u)(k1 v) - Ψ u · k2 v`.

Both `k1` and `k2` are continuous and vanish for `t < 1` and for `2 < t`; hence (compactness of
`[0,3]`) they are *uniformly* bounded — this is the content of the delegated lemma
`Work.FTS.EllipticEst.Mine.zcutK12Bound`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology
open Filter

namespace Work.FTS.EllipticEst.Mine

/-- The fixed smooth step `Ψ t = Real.smoothTransition (t - 1)`: it equals `0` for `t ≤ 1` and
`1` for `2 ≤ t`. -/
noncomputable abbrev zcPsi (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

/-- The scale `n ↦ n + 1` of the `n`-th cut-off (its inverse is the "inner" threshold). -/
noncomputable abbrev zcScale (n : ℕ) : ℝ := (n : ℝ) + 1

/-- **The `n`-th cut-off**, `χ n z = Ψ ((n+1) z) · (1 - Ψ (z (n+1)⁻¹))`: it is `0` for
`z ≤ 1/(n+1)`, `1` for `2/(n+1) ≤ z ≤ n+1` and `0` for `2(n+1) ≤ z`. -/
noncomputable abbrev zcChi (n : ℕ) (z : ℝ) : ℝ :=
  zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))

/-- The weighted first derivative `t ↦ t Ψ'(t)` of the fixed step. -/
noncomputable abbrev zcK1 (t : ℝ) : ℝ := t * deriv zcPsi t

/-- The weighted second derivative `t ↦ t (t Ψ')'(t)` of the fixed step. -/
noncomputable abbrev zcK2 (t : ℝ) : ℝ := t * deriv zcK1 t

/-! ## Elementary properties of the step `Ψ` -/

theorem zcPsi_contDiff (m : ℕ) : ContDiff ℝ m zcPsi :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem zcPsi_diff : Differentiable ℝ zcPsi :=
  (zcPsi_contDiff 1).differentiable one_ne_zero

theorem zcPsi_nonneg (t : ℝ) : 0 ≤ zcPsi t := Real.smoothTransition.nonneg (t - 1)

theorem zcPsi_le_one (t : ℝ) : zcPsi t ≤ 1 := Real.smoothTransition.le_one (t - 1)

theorem zcPsi_eq_zero {t : ℝ} (ht : t ≤ 1) : zcPsi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem zcPsi_eq_one {t : ℝ} (ht : 2 ≤ t) : zcPsi t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem zcK1_contDiff_one : ContDiff ℝ (1 : WithTop ℕ∞) zcK1 := by
  have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) zcPsi := zcPsi_contDiff 2
  have hd : ContDiff ℝ (1 : WithTop ℕ∞) (deriv zcPsi) := (contDiff_succ_iff_deriv.mp h2).2.2
  exact contDiff_id.mul hd

theorem zcK1_diff : Differentiable ℝ zcK1 := zcK1_contDiff_one.differentiable one_ne_zero

theorem zcK1_continuous : Continuous zcK1 := zcK1_diff.continuous

theorem zcK2_continuous : Continuous zcK2 := by
  have hd : Continuous (deriv zcK1) := zcK1_contDiff_one.continuous_deriv le_rfl
  exact continuous_id.mul hd

/-! ## The step's derivative vanishes off `(1,2)` -/

theorem deriv_zcPsi_eq_zero_of_lt_one {t : ℝ} (ht : t < 1) : deriv zcPsi t = 0 := by
  have hmem : Set.Iio (1 : ℝ) ∈ 𝓝 t := Iio_mem_nhds ht
  have heq : zcPsi =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => by
      simp only [zcPsi]
      exact Real.smoothTransition.zero_of_nonpos (by linarith [Set.mem_Iio.mp hs])) hmem
  rw [heq.deriv_eq, deriv_const]

theorem deriv_zcPsi_eq_zero_of_gt_two {t : ℝ} (ht : 2 < t) : deriv zcPsi t = 0 := by
  have hmem : Set.Ioi (2 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
  have heq : zcPsi =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => by
      simp only [zcPsi]
      exact Real.smoothTransition.one_of_one_le (by linarith [Set.mem_Ioi.mp hs])) hmem
  rw [heq.deriv_eq, deriv_const]

/-- `k1` vanishes for `t < 1`. -/
theorem zcK1_eq_zero_of_lt_one {t : ℝ} (ht : t < 1) : zcK1 t = 0 := by
  have hmem : Set.Iio (1 : ℝ) ∈ 𝓝 t := Iio_mem_nhds ht
  have heq : zcK1 =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => by
      simp only [zcK1]
      rw [deriv_zcPsi_eq_zero_of_lt_one (Set.mem_Iio.mp hs)]; ring) hmem
  exact heq.eq_of_nhds

/-- `k1` vanishes for `2 < t`. -/
theorem zcK1_eq_zero_of_gt_two {t : ℝ} (ht : 2 < t) : zcK1 t = 0 := by
  have hmem : Set.Ioi (2 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
  have heq : zcK1 =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => by
      simp only [zcK1]
      rw [deriv_zcPsi_eq_zero_of_gt_two (Set.mem_Ioi.mp hs)]; ring) hmem
  exact heq.eq_of_nhds

/-- `k2` vanishes for `t < 1` (because `k1` does on a whole neighbourhood). -/
theorem zcK2_eq_zero_of_lt_one {t : ℝ} (ht : t < 1) : zcK2 t = 0 := by
  have hmem : Set.Iio (1 : ℝ) ∈ 𝓝 t := Iio_mem_nhds ht
  have heq : zcK1 =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => by
      simp only [zcK1]
      rw [deriv_zcPsi_eq_zero_of_lt_one (Set.mem_Iio.mp hs)]; ring) hmem
  simp only [zcK2, heq.deriv_eq, deriv_const, mul_zero]

/-- `k2` vanishes for `2 < t`. -/
theorem zcK2_eq_zero_of_gt_two {t : ℝ} (ht : 2 < t) : zcK2 t = 0 := by
  have hmem : Set.Ioi (2 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
  have heq : zcK1 =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => by
      simp only [zcK1]
      rw [deriv_zcPsi_eq_zero_of_gt_two (Set.mem_Ioi.mp hs)]; ring) hmem
  simp only [zcK2, heq.deriv_eq, deriv_const, mul_zero]

/-! ## The scale -/

theorem zcScale_pos (n : ℕ) : 0 < zcScale n := by rw [zcScale]; positivity

theorem zcScale_ne_zero (n : ℕ) : zcScale n ≠ 0 := ne_of_gt (zcScale_pos n)

theorem zcScale_mul_inv (n : ℕ) : zcScale n * (zcScale n)⁻¹ = 1 :=
  mul_inv_cancel₀ (zcScale_ne_zero n)

end Work.FTS.EllipticEst.Mine
