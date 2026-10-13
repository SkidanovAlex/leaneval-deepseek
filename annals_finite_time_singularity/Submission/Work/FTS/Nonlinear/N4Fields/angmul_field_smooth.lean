/-
# `angmul_field_smooth` — angular multiplication in `ℋ⁴`, with the smoothness hypothesis

## Why this file exists

The lemma assigned as `Work.FTS.Nonlinear.N4Fields.angmul_field`
(`Submission/Work/FTS/Nonlinear/N4Fields/angmul_field.lean`, and the field `angmul` of the
structure `Work.FTS.Nonlin.N4Norm`) is **false as written**: its hypotheses

* `∀ θ ∈ Iθ, |a θ| ≤ B` and
* `∀ i ∈ [1,4], ∀ θ ∈ Iθ, |D_θ^i a(0, θ)| ≤ B sin 2θ`

say nothing about the *regularity* of the angular profile `a`, and the conclusion demands
`Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ)`, i.e. (`Integrable` = `AEStronglyMeasurable ∧
HasFiniteIntegral`, `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`) *a.e. strong
measurability* of the `ℋ⁴`-integrand of `a·f`.  Counterexample:

* let `V ⊆ Iθ` be a non-measurable set (Vitali, using `Classical.choice`) and put
  `a := V.indicator (fun _ => 1)`, `B := 1`.  A `{0,1}`-valued function is differentiable at `x`
  only if it is locally constant there, and otherwise Mathlib's `deriv` is `0`
  (`deriv_zero_of_not_differentiableAt`); hence `deriv a ≡ 0`, and therefore
  `D_θ^i a ≡ 0` for every `i ≥ 1` — the two hypotheses above hold;
* let `f (z,θ) := χ z` be a `C^∞` function of `z` alone with `HkMem α 4 f` (e.g.
  `χ z = (z/(1+z))^4`: the mixed terms of `HkIntegrand α 4 f` vanish because `f` does not depend
  on `θ`, and `(D_z^i f)² w²` is integrable on `Iz` since `D_z^i f = O(z^4)` at `0` and `= O(z^{-1})`
  at `∞`).  Since `D_θ^i f ≡ 0` for `i ≥ 1`, all mixed terms of `HkIntegrand α 4 (a·f)` are also
  `0`, while (by `Work.FTS.EllipticEst.Blocks.DzIter_angular_mul`) its radial terms are
  `(a θ · D_z^i f z θ · w z / sin(2θ)^{η/2})^2 = a θ · (D_z^i f z θ · w z / sin(2θ)^{η/2})^2`.
  Thus, for every `z` with `χ z ≠ 0`, the `θ`-slice of the integrand is
  `a θ · P(θ)` with `P = Σ_i (D_z^i f z ·)² w z² sin(2θ)^{-η} > 0` on `(0,π/2)` (a full measure
  set), which is *not* a.e. strongly measurable because `V` is not a.e. measurable; hence the
  `θ`-slice is not `IntegrableOn Iθ` and `HkMem α 4 (a·f)` fails for every candidate constant
  `C`.  (The propagation "`1_V` not a.e. measurable and `P > 0` a.e. ⟹ `1_V·P` not a.e.
  measurable" is finite algebra: divide by `P`.)

So the statement needs one more hypothesis — *smoothness of the angular profile*, which is
exactly what the existing reference result

* `Work.FTS.EllipticEst.Blocks.HkIntegrand_mul_angular_le` (sorry-free, in
  `Submission/Work/FTS/EllipticEst/Blocks/HkIntegrand_mul_angular_le.lean`), and
* `Work.Blocks.HkMul_ang_le` / `Work.FTS.EllipticEst.Blocks.HkMul_ang_le`

use: they carry `∀ θ, ContDiffAt ℝ ⊤ a θ`, needed for the iterated Leibniz expansion
`Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand` and for the smoothness
`SmoothOpen (a·f)` that `HkMem` requires (via `HkMem_of_majorant`).

## What is proved here

`angmul_field_smooth` is the *same* statement as `angmul_field` with the missing hypothesis
`∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ` added.  It is a drop-in replacement for the field `angmul` of
`N4Norm` once that field is restated accordingly.

The proof is the rescaling `a = B · a'`, `a' θ = a θ / B` of the reference pointwise bound
`HkIntegrand α k (a'·f) ≤ C₁ HkIntegrand α k f` (with `C₁` *universal*, i.e. independent of the
profile `a`, as required by the interface), transported to the closed quadrant and integrated.
The `B = 0` case is separate (`a` vanishes on `Iθ`, whence the integrand vanishes there).

The reference lemma `HkIntegrand_angular_mul_le` returns its constant *after* the profile `a`
has been introduced, so it cannot be used directly for the uniform statement of the interface;
the two lemmas `angular_summand_sq_le_le_unit` and `HkIntegrand_ang_mul_unit_le` below are that
reference result with the constant pulled out in front of `∀ a` (the constant depends only on
`k`), the profile bound `|a| ≤ 1` being required only on the open interval `(0,π/2)` (which is
all the proof uses — and all the interface supplies).
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.EllipticEst.Blocks.HkIntegrand_mul_angular_le
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## `Lop` is linear -/

/-- `Lop` commutes with multiplication by a constant (`deriv` does so unconditionally: see
`deriv_const_mul_field`). -/
theorem Lop_const_mul (c : ℝ) (u : ℝ → ℝ) :
    Work.Spaces.Lop (fun θ => c * u θ) = fun θ => c * Work.Spaces.Lop u θ := by
  funext θ
  rw [Work.Spaces.Lop, Work.Spaces.Lop, deriv_const_mul_field c]
  ring

/-- The iterates of `Lop` commute with multiplication by a constant. -/
theorem LopIter_const_mul (c : ℝ) (n : ℕ) (u : ℝ → ℝ) :
    Work.FTS.EllipticEst.LopIter n (fun θ => c * u θ)
      = fun θ => c * Work.FTS.EllipticEst.LopIter n u θ := by
  show (Work.Spaces.Lop^[n]) (fun θ => c * u θ)
      = fun θ => c * (Work.Spaces.Lop^[n]) u θ
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        Lop_const_mul c ((Work.Spaces.Lop^[n]) u)]

/-! ## The reference pointwise bound, with a constant uniform in the profile -/

theorem angular_summand_sq_le_le_unit (k : ℕ) (a : ℝ → ℝ) (K : ℕ → ℝ)
    (ha1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a θ| ≤ 1) (hK : ∀ m : ℕ, 0 ≤ K m)
    (hKb : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ K m * (Real.sin (2 * θ)) ^ 2) :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (i j m : ℕ), α ≤ 1 → 1 ≤ i → i + j ≤ k → m ≤ i →
      ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
            * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
  intro α f i j m hα1 hi1 hij hmi z θ hθ0 hθ1
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHe : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hjk : j ≤ k := by omega
  have hmk : m ≤ k := by omega
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have ha2 : (a θ) ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha1 θ hθIoo) 2
      rwa [sq_abs, one_pow] at h
    have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi1 hij
    have h0c : ((i.choose 0 : ℝ)) = 1 := by simp
    rw [h0c, Nat.sub_zero]
    simp only [Work.FTS.EllipticEst.LopIter_zero, Nat.cast_one, one_mul]
    calc (a θ * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (a θ) ^ 2 * (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ 1 * Work.Spaces.HkIntegrand α k f z θ :=
          mul_le_mul ha2 hmix (sq_nonneg _) (by norm_num)
      _ ≤ 1 ^ 2 * (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ := by
          have h1 : (1 : ℝ) ≤ K 0 + 1 := by linarith [hK 0]
          calc (1 : ℝ) * Work.Spaces.HkIntegrand α k f z θ
              ≤ (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ :=
                mul_le_mul_of_nonneg_right h1 hHe
            _ = 1 ^ 2 * (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring
  · rcases Nat.lt_or_eq_of_le hmi with hlt | heq
    · -- 1 ≤ m < i, so 1 ≤ i - m
      have hpos' : 1 ≤ i - m := by omega
      have hd := hKb m hpos hmk θ hθIoo
      have h6 := angular_sq_mul_Wt_sq_le (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
        (u := Work.Spaces.mixed j (i - m) f z θ) (α := α) (z := z) (θ := θ)
        (hK m) hθIoo hd
      have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ (i - m) j hpos' (by omega)
      calc ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (i.choose m : ℝ) ^ 2 * ((Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * (Work.Spaces.mixed j (i - m) f z θ
              * Work.Spaces.Wt α z θ) ^ 2) := mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmix (hK m)) (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
            have h1 : K m * Work.Spaces.HkIntegrand α k f z θ
                ≤ (K m + 1) * Work.Spaces.HkIntegrand α k f z θ :=
              mul_le_mul_of_nonneg_right (by linarith) hHe
            calc (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ)
                ≤ (i.choose m : ℝ) ^ 2 * ((K m + 1) * Work.Spaces.HkIntegrand α k f z θ) :=
                  mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
              _ = (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring
    · -- m = i, so i - m = 0
      have hz0 : i - m = 0 := by omega
      have hd := hKb m hpos hmk θ hθIoo
      have h7 := angular_sq_mul_Wt_sq_le_radial (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
        (u := Work.Spaces.mixed j (i - m) f z θ) (α := α) (z := z) (θ := θ)
        hα1 (hK m) hθIoo hd
      rw [hz0, Work.Spaces.mixed_zero_right] at h7
      have hz' : (Work.Spaces.DzIter j f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hjk
      rw [hz0, Work.Spaces.mixed_zero_right]
      calc ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.DzIter j f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (i.choose m : ℝ) ^ 2 * ((Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * (Work.Spaces.DzIter j f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
            mul_le_mul_of_nonneg_left h7 (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz' (hK m)) (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
            have h1 : K m * Work.Spaces.HkIntegrand α k f z θ
                ≤ (K m + 1) * Work.Spaces.HkIntegrand α k f z θ :=
              mul_le_mul_of_nonneg_right (by linarith) hHe
            calc (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ)
                ≤ (i.choose m : ℝ) ^ 2 * ((K m + 1) * Work.Spaces.HkIntegrand α k f z θ) :=
                  mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
              _ = (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring

theorem HkIntegrand_ang_mul_unit_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℝ), (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a θ| ≤ 1) →
      (∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ) →
      (∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2) →
      ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen f →
        ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
            ≤ C * Work.Spaces.HkIntegrand α k f z θ := by
  set K : ℕ → ℝ := fun _ => 1 with hKdef
  have hK : ∀ m : ℕ, 0 ≤ K m := fun m => by rw [hKdef]; exact zero_le_one
  set KB : ℝ := ∑ m ∈ Finset.range (k + 1), (K m + 1) with hKBdef
  have hKBpos : 0 < KB := by
    rw [hKBdef]
    exact Finset.sum_pos (fun m _ => by linarith [hK m])
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
  set CB : ℝ := ((2 : ℝ) ^ k) ^ 2 with hCBdef
  have hCBnonneg : 0 ≤ CB := by rw [hCBdef]; positivity
  set Cpair : ℝ := ((k : ℝ) + 1) * CB * KB with hCpairdef
  have hCpairnonneg : 0 ≤ Cpair := by rw [hCpairdef]; positivity
  set C1 : ℝ := ((k : ℝ) + 1) ^ 2 * Cpair with hC1def
  refine ⟨((k : ℝ) + 1) + C1, by positivity, ?_⟩
  intro a ha1 ha hKb0 α f hα hα1 hf z θ hz hθ0 hθ1
  have hKb : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ K m * (Real.sin (2 * θ)) ^ 2 := by
    intro m hm1 hmk θ hθ
    rw [hKdef]
    simpa using hKb0 m hm1 hmk θ hθ
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHe : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZi : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [DzIter_angular_mul i a f]
      have ha2 : (a θ) ^ 2 ≤ 1 := by
        have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha1 θ hθIoo) 2
        rwa [sq_abs, one_pow] at h
      calc (a θ * Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (a θ) ^ 2 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
        _ ≤ 1 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
            mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)
        _ = (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := one_mul _
        _ ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hik
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (k + 1), Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hMi : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ C1 * Work.Spaces.HkIntegrand α k f z θ := by
    have hpair : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (1 ≤ i ∧ i + j ≤ k) →
        (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Cpair * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi j hj hc
      obtain ⟨hi1, hij⟩ := hc
      have hik : i ≤ k := by omega
      have hjk : j ≤ k := by omega
      have hexp : Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ
          = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ := by
        have hag : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * f z θ) := by
          have haG : ContDiff ℝ ⊤ a := contDiff_iff_contDiffAt.mpr ha
          have haC : ContDiff ℝ Work.Stability.smoothOrder a := haG.of_le le_top
          have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
              (fun p : ℝ × ℝ => a p.2) Q0 :=
            haC.contDiffOn.comp contDiffOn_snd (fun p _ => Set.mem_univ p.2)
          have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Q0 := hf
          have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
              (fun p : ℝ × ℝ => a p.2 * f p.1 p.2) Q0 := h1.mul h2
          exact h3
        rw [← Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hag j i hz hθIoo]
        rw [DzIter_angular_mul j a f]
        rw [DthIter_angular_mul_expand ha hf i j hz hθIoo]
        exact Finset.sum_congr rfl fun m _ => by
          rw [Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hf j (i - m) hz hθIoo]
      rw [hexp]
      have hstep : (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ) * Work.Spaces.Wt α z θ
          = ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) := by
        rw [Finset.sum_mul]
      rw [hstep]
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
        (f := fun m => (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
          * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ)
      have hbound : ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
            * Work.FTS.EllipticEst.LopIter m a θ
            * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ CB * KB * Work.Spaces.HkIntegrand α k f z θ := by
        have hchoose : ∀ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 ≤ CB := by
          intro m hm
          have h1 : (i.choose m : ℝ) ≤ (2 : ℝ) ^ k := by
            have h2 : i.choose m ≤ 2 ^ k := le_trans (Nat.choose_le_two_pow i m)
              (Nat.pow_le_pow_right (by norm_num) hik)
            exact_mod_cast h2
          calc (i.choose m : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
            _ = CB := by rw [hCBdef]
        have hsumKB : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
            ≤ CB * KB := by
          have hstep1 : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
              ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := by
            refine Finset.sum_le_sum fun m hm => ?_
            exact mul_le_mul_of_nonneg_right (hchoose m hm) (by linarith [hK m])
          have hstep2 : ∑ m ∈ Finset.range (i + 1), CB * (K m + 1)
              = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := by
            rw [Finset.mul_sum]
          have hstep3 : ∑ m ∈ Finset.range (i + 1), (K m + 1) ≤ KB := by
            rw [hKBdef]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro m hm
              simp only [Finset.mem_range] at hm ⊢
              omega
            · intro m _ _
              linarith [hK m]
          calc _ ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := hstep1
            _ = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := hstep2
            _ ≤ CB * KB := mul_le_mul_of_nonneg_left hstep3 hCBnonneg
        calc ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
                * Work.Spaces.HkIntegrand α k f z θ := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hmi : m ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
              exact angular_summand_sq_le_le_unit k a K ha1 hK hKb α f i j m hα1 hi1 hij hmi
                z θ hθ0 hθ1
          _ = Work.Spaces.HkIntegrand α k f z θ
                * ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun m _ => by ring
          _ ≤ Work.Spaces.HkIntegrand α k f z θ * (CB * KB) :=
              mul_le_mul_of_nonneg_left hsumKB hHe
          _ = CB * KB * Work.Spaces.HkIntegrand α k f z θ := by ring
      have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
        rw [Finset.card_range]
        push_cast
        ring
      calc (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) * ∑ m ∈ Finset.range (i + 1),
              ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
                * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2 := hcs
        _ ≤ (((i : ℝ) + 1)) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            rw [hcard]
            exact mul_le_mul_of_nonneg_left hbound (by positivity)
        _ ≤ ((k : ℝ) + 1) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
            linarith
        _ = Cpair * Work.Spaces.HkIntegrand α k f z θ := by
            rw [hCpairdef]
            ring
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
            Cpair * Work.Spaces.HkIntegrand α k f z θ := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc]
            exact hpair i hi j hj hc
          · rw [if_neg hc]
            exact mul_nonneg hCpairnonneg hHe
      _ = C1 * Work.Spaces.HkIntegrand α k f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [hC1def]
          push_cast
          ring
  rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) (le_of_eq ?_)
  ring

end Work.FTS.EllipticEst.Blocks

namespace Work.FTS.Nonlinear.N4Fields

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Auxiliary: `SmoothOpen` of an angular multiple, and the closed-quadrant transfer -/

/-- Multiplying a `SmoothOpen` function by a `C^∞` angular profile preserves `SmoothOpen`. -/
theorem smoothOpen_angMul {a : ℝ → ℝ} (ha : ∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * G z θ) := by
  have haG : ContDiff ℝ ⊤ a := contDiff_iff_contDiffAt.mpr ha
  have haC : ContDiff ℝ Work.Stability.smoothOrder a := haG.of_le le_top
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 :=
    haC.contDiffOn.comp contDiffOn_snd (fun p _ => Set.mem_univ p.2)
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => a p.2 * G p.1 p.2) Work.FTS.EllipticEst.Q0 := h1.mul hG
  exact h3

/-- A pointwise bound on the *open* quadrant extends to the *closed* quadrant `Iz ×ˢ Iθ`: on the
two boundary lines `z = 0` and `sin(2θ) = 0` both `ℋ^k`-integrands vanish
(`HkIntegrand_zero_fst`, `HkIntegrand_eq_zero_of_sin_eq_zero`). -/
theorem closed_of_interior {k : ℕ} {a : ℝ → ℝ} {C : ℝ}
    (hint : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ := by
  intro α f hα hα1 hf z hz θ hθ
  have hzge : (0 : ℝ) ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
  have hθb : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := by
    simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
  rcases eq_or_lt_of_le hzge with h0 | hpos
  · rw [← h0, Work.FTS.LocData.HkIntegrand_zero_fst α k (fun z θ => a θ * f z θ) θ,
      Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k (fun z θ => a θ * f z θ) z θ hs,
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f z θ hs, mul_zero]
    · have hθ1 : 0 < θ := by
        rcases eq_or_lt_of_le hθb.1 with h | h
        · exact absurd (by rw [← h]; simp) hs
        · exact h
      have hθ2 : θ < Real.pi / 2 := by
        rcases lt_or_eq_of_le hθb.2 with h | h
        · exact h
        · exact absurd (by rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring,
            Real.sin_pi]) hs
      exact hint α f hα hα1 hf z θ hpos hθ1 hθ2

/-! ## Auxiliary: transfer of `HkSq` along a pointwise domination -/

/-- A pointwise domination of the `ℋ^k`-integrand on the closed quadrant, with the integrand of
`f` integrable, transfers to `HkSq` (both sides being iterated integrals). -/
theorem HkSq_le_of_integrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkSq α k g ≤ C * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α k f z θ)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
        ((hmf.1 z hz).const_mul C)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    rwa [MeasureTheory.integral_const_mul] at h1
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)
      ≤ ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (g := fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ))
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (hmf.2.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rwa [MeasureTheory.integral_const_mul] at h2

/-! ## The `B = 0` case: the profile vanishes on `Iθ` -/

/-- If `a` vanishes on `Iθ`, then every `D_θ`-iterate (of order `≥ 1`) of `(z,θ) ↦ a θ · f z θ`
vanishes on `Iz ×ˢ Iθ`.  (`D_θ` carries the factor `sin(2θ)`, which is `0` at the two endpoints
of `Iθ`, and on the open interval the `θ`-slice of `a·f` is locally `0`.) -/
theorem DthIter_angmul_eq_zero (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, a θ = 0) :
    ∀ i : ℕ, 1 ≤ i → ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.DthIter i (fun z θ => a θ * f z θ) z θ = 0 := by
  -- the one-step statement: `D_θ` kills any function vanishing on `Iθ` in the angular variable
  have hstep : ∀ (G : ℝ → ℝ → ℝ), (∀ z θ, θ ∈ Work.Spaces.Iθ → G z θ = 0) →
      ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → Work.Spaces.Dth G z θ = 0 := by
    intro G hG z θ hθ
    rw [Work.Spaces.Dth, Work.Spaces.pth]
    by_cases hs : Real.sin (2 * θ) = 0
    · rw [hs, zero_mul]
    · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
        refine ⟨?_, ?_⟩
        · rcases lt_or_eq_of_le hθ.1 with h | h
          · exact h
          · exact absurd (by rw [← h]; simp) hs
        · rcases lt_or_eq_of_le hθ.2 with h | h
          · exact h
          · exact absurd (by rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring,
              Real.sin_pi]) hs
      have hnb : (fun θ' : ℝ => G z θ') =ᶠ[nhds θ] (fun _ => (0 : ℝ)) := by
        have hmem : Work.Spaces.Iθ ∈ nhds θ :=
          Filter.mem_of_superset (Ioo_mem_nhds hθ'.1 hθ'.2)
            (fun θ' (hθ'' : θ' ∈ Set.Ioo 0 (Real.pi / 2)) =>
              (⟨le_of_lt hθ''.1, le_of_lt hθ''.2⟩ : θ' ∈ Work.Spaces.Iθ))
        filter_upwards [hmem] with θ' hθ''
        exact hG z θ' hθ''
      rw [hnb.deriv_eq, deriv_const, mul_zero]
  intro i
  induction i with
  | zero => intro h; omega
  | succ m ih =>
      intro _ z θ hθ
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        exact hstep (fun z θ => a θ * f z θ)
          (fun z θ hθ => by rw [ha0 θ hθ, zero_mul]) z θ hθ
      · rw [Work.Spaces.DthIter_succ]
        exact hstep (Work.Spaces.DthIter m (fun z θ => a θ * f z θ))
          (fun z θ hθ => ih hpos z θ hθ) z θ hθ

/-! ## The corrected field lemma -/

/-- **The corrected `angmul` field.**  Same as `Work.FTS.Nonlinear.N4Fields.angmul_field` but
with the smoothness hypothesis on the angular profile that the statement is missing (and that
the reference proof uses).  The constant is universal in `α`, `a`, `B`, `f`. -/
theorem angmul_field_smooth {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (B : ℝ) (f : Work.FTS.Galerkin.Fn),
      0 ≤ B →
      (∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B * Real.sin (2 * θ)) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => a θ * f z θ) ≤ C * B * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.EllipticEst.Blocks.HkIntegrand_ang_mul_unit_le 4
  refine ⟨1 + Real.sqrt C₁, by positivity, ?_⟩
  intro α hα a B f hB haSm haB haIt hf hmem
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · -- ## `B = 0`
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, a θ = 0 := by
      intro θ hθ
      have h1 := haB θ hθ
      rw [← hB0] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hzero : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ = 0 := by
      intro z θ hθ
      rw [Work.Spaces.HkIntegrand]
      have h1 : (∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul i a f]
        simp [ha0 θ hθ]
      have h2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hc
        · rw [Work.Spaces.mixed]
          rw [Work.Coercivity.DzIter_eq_zero_of_forall_eq_zero
            (Work.Spaces.DthIter i (fun z θ => a θ * f z θ)) θ
            (fun z' => DthIter_angmul_eq_zero a f ha0 i hc.1 z' θ hθ) j z,
            zero_mul, sq, mul_zero]
        · rfl
      rw [h1, h2, add_zero]
    have hmem' : Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant (M := fun _ _ => (0 : ℝ)) α 4 ?_ ?_ ?_ ?_
      · have h0 : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0 :=
          continuousOn_const
        refine h0.congr ?_
        intro p hp
        exact hzero p.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
      · intro z hz; exact integrableOn_zero
      · have hthis : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (fun _ _ => (0 : ℝ)) z θ)
            = fun _ => (0 : ℝ) := by
          funext z; simp
        rw [hthis]
        exact integrableOn_zero
      · intro z hz θ hθ; rw [hzero z θ hθ]
    refine ⟨hmem', ?_⟩
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ) = 0 := by
      rw [Work.Spaces.HkSq]
      have hinner : ∀ z : ℝ,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ)
            = 0 := by
        intro z
        rw [MeasureTheory.integral_eq_zero_of_ae]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hzero z θ hθ)
      simp only [hinner, integral_zero]
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsq, Real.sqrt_zero, ← hB0]
    simp
  · -- ## `B > 0`: rescale to `a' = a/B` and use the uniform unit bound
    set a' : ℝ → ℝ := fun θ => a θ / B with ha'def
    have hBne : B ≠ 0 := hBpos.ne'
    have ha'1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a' θ| ≤ 1 := by
      intro θ hθ
      have h1 := haB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h2 : |a' θ| = |a θ| / B := by
        rw [ha'def, abs_div, abs_of_pos hBpos]
      rw [h2]
      exact (div_le_one hBpos).mpr h1
    have ha'Sm : ∀ θ : ℝ, ContDiffAt ℝ ⊤ a' θ := by
      intro θ
      have h := (haSm θ).div_const B
      simpa only [ha'def] using h
    have ha'It : ∀ m : ℕ, 1 ≤ m → m ≤ 4 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Work.FTS.EllipticEst.LopIter m a' θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 := by
      intro m hm1 hm4 θ hθ
      -- the `Lop`-iterate of the rescaled profile
      have hlin : ∀ θ' : ℝ,
          Work.FTS.EllipticEst.LopIter m a' θ'
            = B⁻¹ * Work.FTS.EllipticEst.LopIter m a θ' := by
        have h1 : a' = fun θ => B⁻¹ * a θ := by
          funext θ'; rw [ha'def]; field_simp
        intro θ'
        rw [h1, congrFun (Work.FTS.EllipticEst.Blocks.LopIter_const_mul B⁻¹ m a) θ']
      -- the interface hypothesis, in `Lop`-form
      have hbound : |Work.FTS.EllipticEst.LopIter m a θ| ≤ B * Real.sin (2 * θ) := by
        have h2 : Work.FTS.EllipticEst.LopIter m a θ
            = Work.Spaces.DthIter m (fun _ (θ' : ℝ) => a θ') 0 θ := by
          rw [Work.Spaces.DthIter_eq_iterate_Lop]
          rfl
        rw [h2]
        exact haIt m hm1 (by omega) θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsq : (Work.FTS.EllipticEst.LopIter m a θ) ^ 2
          ≤ (B * Real.sin (2 * θ)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
      rw [hlin θ]
      calc (B⁻¹ * Work.FTS.EllipticEst.LopIter m a θ) ^ 2
          = B⁻¹ ^ 2 * (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 := by ring
        _ ≤ B⁻¹ ^ 2 * (B * Real.sin (2 * θ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = (Real.sin (2 * θ)) ^ 2 := by
            field_simp
    -- the pointwise bound for the rescaled profile, on the open and then the closed quadrant
    have hopen : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 4 (fun z θ => a' θ * f z θ) z θ
          ≤ C₁ * Work.Spaces.HkIntegrand α 4 f z θ :=
      hC₁ a' ha'1 ha'Sm ha'It α f hα0 hα1 hf
    have hclosed := closed_of_interior (k := 4) (a := a') (C := C₁)
      (fun α' f' hα' hα'1 hf' => hC₁ a' ha'1 ha'Sm ha'It α' f' hα' hα'1 hf') α f hα0 hα1 hf
    -- transport back to `a·f = B · (a'·f)`
    have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ
          ≤ (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ := by
      intro z hz θ hθ
      have hrew : (fun z θ => a θ * f z θ) = fun z θ => B * (a' θ * f z θ) := by
        funext z' θ'
        have hBmul : B * (a θ' / B) = a θ' := by field_simp
        rw [ha'def]
        calc a θ' * f z' θ' = (B * (a θ' / B)) * f z' θ' := by rw [hBmul]
          _ = B * (a θ' / B * f z' θ') := by ring
      rw [hrew, Work.FTS.LocData.HkIntegrand_const_mul]
      calc B ^ 2 * Work.Spaces.HkIntegrand α 4 (fun z θ => a' θ * f z θ) z θ
          ≤ B ^ 2 * (C₁ * Work.Spaces.HkIntegrand α 4 f z θ) :=
            mul_le_mul_of_nonneg_left (hclosed z hz θ hθ) (sq_nonneg B)
        _ = (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ := by ring
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (smoothOpen_angMul haSm hf).continuousOn_HkIntegrand α 4
    have hmem' : Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant α 4 hcont ?_ ?_ hpt
      · intro z hz
        exact (hmem.1 z hz).const_mul (B ^ 2 * C₁)
      · have h2 := hmem.2.const_mul (B ^ 2 * C₁)
        have heq : (fun z => ∫ θ in Work.Spaces.Iθ,
              (B ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ)
            = fun z => (B ^ 2 * C₁) * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 f z θ := by
          funext z
          rw [MeasureTheory.integral_const_mul]
        rw [heq]
        exact h2
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ)
        ≤ (B ^ 2 * C₁) * Work.Spaces.HkSq α 4 f :=
      HkSq_le_of_integrand_le α 4 (B ^ 2 * C₁) hmem hpt
    refine ⟨hmem', ?_⟩
    have hsqrt : Work.Spaces.HkNorm α 4 (fun z θ => a θ * f z θ)
        ≤ (B * Real.sqrt C₁) * Work.FTS.Nonlin.Xn α f := by
      have h1 : Real.sqrt (B ^ 2 * C₁) = B * Real.sqrt C₁ := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ B ^ 2), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hB]
      have h2 : Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
      rw [Work.Spaces.HkNorm, h2]
      calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ))
          ≤ Real.sqrt ((B ^ 2 * C₁) * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (B ^ 2 * C₁) * Real.sqrt (Work.Spaces.HkSq α 4 f) :=
            Real.sqrt_mul (by positivity) (Work.Spaces.HkSq α 4 f)
        _ = (B * Real.sqrt C₁) * Real.sqrt (Work.Spaces.HkSq α 4 f) := by rw [h1]
    have hXnnn : 0 ≤ Work.FTS.Nonlin.Xn α f := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
      exact Real.sqrt_nonneg _
    calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * f z θ)
        ≤ (B * Real.sqrt C₁) * Work.FTS.Nonlin.Xn α f := hsqrt
      _ ≤ (1 + Real.sqrt C₁) * B * Work.FTS.Nonlin.Xn α f := by
          refine mul_le_mul_of_nonneg_right ?_ hXnnn
          nlinarith [hB, Real.sqrt_nonneg C₁]

end Work.FTS.Nonlinear.N4Fields
