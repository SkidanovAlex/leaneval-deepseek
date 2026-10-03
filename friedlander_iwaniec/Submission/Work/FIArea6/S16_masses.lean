/-
# `Submission.Work.FIArea6.S16_masses` — the near/far §16 mass bounds, cycle-free

`S16ErrTwo/nearMass_le.lean` and `S16ErrTwo/farMass_le.lean` cannot be imported by
`Submission.Work.FIArea6.S16_error_bound` (they import *it*, for
`Work.FIArea6.error_le_far`).  Since that lemma now lives in the cycle-free module
`Submission.Work.FIArea6.S16_far_point`, this file carries the same two mass bounds
(the near-diagonal and the far piece, *FI* (16.5)–(16.6) and (16.9)) with the far-piece
dependency re-pointed at `S16_far_point` and the one colliding helper name
(`sum_inv_Icc_le`) disambiguated.  The two lemmas below are then the `hnear` and `hfar`
slots of `Work.FIArea6.S16_assembly_final`.
-/
import Mathlib
import Submission.Work.FIArea6.S16ErrTwo.Defs
import Submission.Work.FIArea6.S16_far_point
import Submission.Work.FIArea6.card_dvd_delta_fiber_near_le
import Submission.Work.FIArea6.S16ErrTwo.card_Icc_filter_dvd_le
import Submission.Work.FIArea6.S16ErrTwo.sum_natAbs_inv_le
import Submission.Work.FIArea4.prim_of_beta6
import Submission.Work.FIArea4.GaussMoebiusCore
import Submission.Work.FIArea4.S15delta

set_option autoImplicit false

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### The near/far mass machinery (copied from `S16ErrTwo`, far-piece dependency re-pointed) -/

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The far pair sum without the coprimality/divisibility conditions and without the constant
`8N/X³`: this is what `Σ_d (φ(d)/d)·farMass X d β` reduces to. -/
def Sfar (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Mthr Pa X < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      then ‖β z1‖ * ‖β z2‖ / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) else 0)

/-- The far column weight at `z`: the sum of `1/|Δ(z,z₂)|` over the far pairs in `boxN`. -/
def Wsum (Pa : Work.FITop.Params) (X : ℕ) (z : GaussianInt) : ℝ :=
  ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Mthr Pa X < ((Work.FIPlan.absDelta z z2 : ℕ) : ℝ)
      then 1 / ((Work.FIPlan.absDelta z z2 : ℕ) : ℝ) else 0)

/-- `1/|n|` for an integer `n` (with the harmless convention `1/0 = 0`). -/
def invNatAbs (n : ℤ) : ℝ := ((n.natAbs : ℕ) : ℝ)⁻¹

lemma Sfar_nonneg (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) :
    0 ≤ Sfar Pa X β := by
  rw [Sfar]
  refine Finset.sum_nonneg (fun z1 _ => Finset.sum_nonneg (fun z2 _ => ?_))
  split_ifs
  · positivity
  · exact le_refl 0

lemma invNatAbs_nonneg (n : ℤ) : 0 ≤ invNatAbs n := by
  rw [invNatAbs]; positivity

lemma Wsum_nonneg (Pa : Work.FITop.Params) (X : ℕ) (z : GaussianInt) : 0 ≤ Wsum Pa X z := by
  rw [Wsum]
  refine Finset.sum_nonneg (fun z2 _ => ?_)
  split_ifs
  · positivity
  · exact le_refl 0

end


open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Abstract AM–GM.** For a finite `s`, weights `a` and a symmetric nonnegative kernel `k`,

`Σ_{x,y ∈ s} a x·a y·k(x,y) ≤ Σ_{x ∈ s} a x² · Σ_{y ∈ s} k(x,y)`.

Proof: `2 a x a y · k ≤ (a x² + a y²) · k` pointwise, and the two double sums
`ΣΣ a x² k` and `ΣΣ a y² k` are equal by `Finset.sum_comm` and the symmetry of `k`. -/
lemma double_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (k : ι → ι → ℝ)
    (hksym : ∀ x y, k x y = k y x) (hknn : ∀ x y, 0 ≤ k x y) :
    (∑ x ∈ s, ∑ y ∈ s, a x * a y * k x y)
      ≤ ∑ x ∈ s, a x ^ 2 * ∑ y ∈ s, k x y := by
  have hsplit : (∑ x ∈ s, ∑ y ∈ s, (a x ^ 2 + a y ^ 2) * k x y)
      = (∑ x ∈ s, ∑ y ∈ s, a x ^ 2 * k x y)
        + (∑ x ∈ s, ∑ y ∈ s, a y ^ 2 * k x y) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x hx
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro y hy
    ring
  have hD2 : (∑ x ∈ s, ∑ y ∈ s, a y ^ 2 * k x y)
      = (∑ x ∈ s, ∑ y ∈ s, a x ^ 2 * k x y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y hy
    apply Finset.sum_congr rfl; intro x hx
    rw [hksym x y]
  have hD1 : (∑ x ∈ s, ∑ y ∈ s, a x ^ 2 * k x y)
      = ∑ x ∈ s, a x ^ 2 * ∑ y ∈ s, k x y := by
    apply Finset.sum_congr rfl; intro x hx
    rw [Finset.mul_sum]
  have hstep : 2 * (∑ x ∈ s, ∑ y ∈ s, a x * a y * k x y)
      ≤ ∑ x ∈ s, ∑ y ∈ s, (a x ^ 2 + a y ^ 2) * k x y := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro y hy
    have h := mul_le_mul_of_nonneg_right (two_mul_le_add_sq (a x) (a y)) (hknn x y)
    nlinarith
  linarith [hstep, hsplit, hD1, hD2]

/-- **Abstract AM–GM, threshold form.** Specialisation of `double_sum_le` to a kernel written
as an `if`-of-`1/d` guarded by a symmetric predicate `c`, matching both `Sfar` and `Wsum`. -/
lemma double_sum_le_ite {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (c : ι → ι → Prop) (d : ι → ι → ℝ)
    (hsym : ∀ x y, c x y ↔ c y x) (hd : ∀ x y, d x y = d y x)
    (hdnn : ∀ x y, 0 ≤ d x y) :
    (∑ x ∈ s, ∑ y ∈ s, (if c x y then a x * a y / d x y else 0))
      ≤ ∑ x ∈ s, a x ^ 2 * ∑ y ∈ s, (if c x y then 1 / d x y else 0) := by
  have hksym : ∀ x y, (if c x y then (d x y)⁻¹ else 0)
      = (if c y x then (d y x)⁻¹ else 0) := by
    intro x y
    by_cases h : c x y
    · have h' : c y x := (hsym x y).mp h
      simp [h, h', hd x y]
    · have h' : ¬ c y x := fun hy => h ((hsym x y).mpr hy)
      simp [h, h']
  have hknn : ∀ x y, 0 ≤ (if c x y then (d x y)⁻¹ else 0) := by
    intro x y
    by_cases h : c x y
    · simp only [h, ↓reduceIte]; exact inv_nonneg.mpr (hdnn x y)
    · simp [h]
  have hb := double_sum_le s a (fun x y => if c x y then (d x y)⁻¹ else 0) hksym hknn
  have hA : (∑ x ∈ s, ∑ y ∈ s, (if c x y then a x * a y / d x y else 0))
      = (∑ x ∈ s, ∑ y ∈ s, a x * a y * (if c x y then (d x y)⁻¹ else 0)) := by
    apply Finset.sum_congr rfl; intro x hx
    apply Finset.sum_congr rfl; intro y hy
    by_cases h : c x y
    · simp only [h, ↓reduceIte]; rw [div_eq_mul_inv]
    · simp [h]
  have hC : (∑ x ∈ s, a x ^ 2 * ∑ y ∈ s, (if c x y then (d x y)⁻¹ else 0))
      = (∑ x ∈ s, a x ^ 2 * ∑ y ∈ s, (if c x y then 1 / d x y else 0)) := by
    apply Finset.sum_congr rfl; intro x hx
    congr 1
    apply Finset.sum_congr rfl; intro y hy
    by_cases h : c x y <;> simp [h, one_div]
  rw [hA, ← hC]
  exact hb

/-- **`Sfar ≤ Σ_z ‖βz‖² Wsum z`**: the far-pair mass is dominated by the `Wsum`-weighted
`L²` mass of the coefficient, by AM–GM plus the symmetry `|Δ(z₁,z₂)| = |Δ(z₂,z₁)|`. -/
theorem Sfar_le_Wsum (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) :
    Sfar Pa X β
      ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ‖β z1‖ ^ (2 : ℕ) * Wsum Pa X z1 := by
  unfold Sfar Wsum
  exact double_sum_le_ite (Work.FITop.boxN Pa) (fun z => ‖β z‖)
    (fun z1 z2 => Mthr Pa X < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
    (fun z1 z2 => ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
    (fun z1 z2 => by rw [absDelta_comm])
    (fun z1 z2 => by rw [absDelta_comm])
    (fun z1 z2 => by positivity)

end


open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Two elementary inputs

The harmonic-type bound `∑_{d ≤ X} φ(d)/d² ≤ 1 + log(2+X)` and the final bookkeeping of the
constants. -/

/-- `∑_{d ≤ X} 1/d ≤ 1 + log X` — the standard harmonic estimate, from Mathlib's
`harmonic_le_one_add_log`. -/
lemma sum_inv_Icc_le (X : ℕ) (hX : 1 ≤ X) :
    (∑ d ∈ Finset.Icc 1 X, ((d : ℝ))⁻¹) ≤ 1 + Real.log (X : ℝ) := by
  have h := harmonic_le_one_add_log X
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h

/-- `∑_{d ≤ X} φ(d)/d² ≤ 1 + log(2+X)`: from `φ(d) ≤ d` and the harmonic estimate. -/
lemma phi_div_sq_sum_le_aux (X : ℕ) (hX : 1 ≤ X) :
    ∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ) ^ 2
      ≤ 1 + Real.log (2 + (X : ℝ)) := by
  have h1 : ∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ) ^ 2
      ≤ ∑ d ∈ Finset.Icc 1 X, ((d : ℝ))⁻¹ := by
    refine Finset.sum_le_sum (fun d hdmem => ?_)
    obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hdmem
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hle : (Nat.totient d : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
    calc (Nat.totient d : ℝ) / (d : ℝ) ^ 2 ≤ (d : ℝ) / (d : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hle (by positivity)
      _ = ((d : ℝ))⁻¹ := by
          rw [sq, ← div_div, div_self (ne_of_gt hdpos), one_div]
  have h2 : ∑ d ∈ Finset.Icc 1 X, ((d : ℝ))⁻¹ ≤ 1 + Real.log (X : ℝ) := sum_inv_Icc_le X hX
  have h3 : Real.log (X : ℝ) ≤ Real.log (2 + (X : ℝ)) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < X)) (by linarith)
  linarith

/-- The constant bookkeeping: the four pieces `4X²`, `10θ√N·X`, `4π√N` and `10πθN(1+log)/X`
add up to at most `128` times the target shape. -/
lemma s16err_arith_bound_aux (Pa : Work.FITop.Params) (X : ℕ) (hX : 1 ≤ X) :
    4 * (X : ℝ) ^ 2
        + (10 * Pa.θ * Real.sqrt Pa.N + 2 * Mthr Pa X / Real.sqrt Pa.N) * X
        + 5 * Pa.θ * Mthr Pa X * (1 + Real.log (2 + (X : ℝ)))
      ≤ 128 * (1 + Real.log (2 + (X : ℝ)))
          * ((X : ℝ) ^ 2 + Pa.θ * Real.sqrt Pa.N * X + Real.sqrt Pa.N + Pa.θ * Pa.N / X) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hNpos : 0 < Pa.N := by linarith [Pa.hN1]
  have hNnn : (0 : ℝ) ≤ Pa.N := hNpos.le
  have hsN : 0 < Real.sqrt Pa.N := Real.sqrt_pos.mpr hNpos
  have hsN0 : Real.sqrt Pa.N ≠ 0 := ne_of_gt hsN
  have hsNnn : 0 ≤ Real.sqrt Pa.N := hsN.le
  have hsq : Real.sqrt Pa.N * Real.sqrt Pa.N = Pa.N := by
    simpa [pow_two] using Real.sq_sqrt hNnn
  have hθ : 0 ≤ Pa.θ := Pa.hθ0.le
  have hlog : (0 : ℝ) ≤ Real.log (2 + (X : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) ≤ 1 + Real.log (2 + (X : ℝ)) := by linarith
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 + (X : ℝ)) := by linarith
  have hNdiv : Pa.N / Real.sqrt Pa.N = Real.sqrt Pa.N := by
    rw [div_eq_iff hsN0]
    exact hsq.symm
  have hA : (10 * Pa.θ * Real.sqrt Pa.N + 2 * Mthr Pa X / Real.sqrt Pa.N) * X
      = 10 * Pa.θ * Real.sqrt Pa.N * X + 4 * Real.pi * Real.sqrt Pa.N := by
    have hb : 2 * Mthr Pa X / Real.sqrt Pa.N * X = 4 * Real.pi * (Pa.N / Real.sqrt Pa.N) := by
      rw [Mthr]
      field_simp <;> ring
    rw [add_mul, hb, hNdiv]
  have hB : 5 * Pa.θ * Mthr Pa X * (1 + Real.log (2 + (X : ℝ)))
      = 10 * Real.pi * (1 + Real.log (2 + (X : ℝ))) * (Pa.θ * Pa.N / X) := by
    rw [Mthr]
    field_simp <;> ring
  rw [hA, hB]
  have hX2 : (0 : ℝ) ≤ (X : ℝ) ^ 2 := sq_nonneg _
  have hA0 : 0 ≤ Pa.θ * Real.sqrt Pa.N * X := mul_nonneg (mul_nonneg hθ hsNnn) hXpos.le
  have hC0 : 0 ≤ Pa.θ * Pa.N / X := div_nonneg (mul_nonneg hθ hNnn) hXpos.le
  have e1 : 4 * (X : ℝ) ^ 2
      ≤ 128 * (1 + Real.log (2 + (X : ℝ))) * (X : ℝ) ^ 2 := by
    have h := mul_le_mul (show (4 : ℝ) ≤ 128 by norm_num) hL1 (by norm_num) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h hX2
    linarith [h2]
  have e2 : 10 * (Pa.θ * Real.sqrt Pa.N * X)
      ≤ 128 * (1 + Real.log (2 + (X : ℝ))) * (Pa.θ * Real.sqrt Pa.N * X) := by
    have h := mul_le_mul (show (10 : ℝ) ≤ 128 by norm_num) hL1 (by norm_num) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h hA0
    linarith [h2]
  have e3 : 4 * Real.pi * Real.sqrt Pa.N
      ≤ 128 * (1 + Real.log (2 + (X : ℝ))) * Real.sqrt Pa.N := by
    have hpi : (4 * Real.pi : ℝ) ≤ 128 := by nlinarith [Real.pi_lt_four]
    have h := mul_le_mul hpi hL1 (by positivity) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h hsNnn
    linarith [h2]
  have e4 : 10 * Real.pi * (1 + Real.log (2 + (X : ℝ))) * (Pa.θ * Pa.N / X)
      ≤ 128 * (1 + Real.log (2 + (X : ℝ))) * (Pa.θ * Pa.N / X) := by
    have hpi : (10 * Real.pi : ℝ) ≤ 128 := by nlinarith [Real.pi_lt_four]
    have h := mul_le_mul_of_nonneg_left hpi (mul_nonneg hL0 hC0)
    linarith [h]
  calc 4 * (X : ℝ) ^ 2 + (10 * Pa.θ * Real.sqrt Pa.N * X + 4 * Real.pi * Real.sqrt Pa.N)
        + 10 * Real.pi * (1 + Real.log (2 + (X : ℝ))) * (Pa.θ * Pa.N / X)
      = 4 * (X : ℝ) ^ 2 + 10 * (Pa.θ * Real.sqrt Pa.N * X) + 4 * Real.pi * Real.sqrt Pa.N
        + 10 * Real.pi * (1 + Real.log (2 + (X : ℝ))) * (Pa.θ * Pa.N / X) := by ring
    _ ≤ 128 * (1 + Real.log (2 + (X : ℝ))) * (X : ℝ) ^ 2
        + 128 * (1 + Real.log (2 + (X : ℝ))) * (Pa.θ * Real.sqrt Pa.N * X)
        + 128 * (1 + Real.log (2 + (X : ℝ))) * Real.sqrt Pa.N
        + 128 * (1 + Real.log (2 + (X : ℝ))) * (Pa.θ * Pa.N / X) := by linarith [e1, e2, e3, e4]
    _ = 128 * (1 + Real.log (2 + (X : ℝ)))
          * ((X : ℝ) ^ 2 + Pa.θ * Real.sqrt Pa.N * X + Real.sqrt Pa.N + Pa.θ * Pa.N / X) := by
        ring

/-- **Step 1.** The near-diagonal mass at the modulus `4d` is bounded by the `4d`-fibre counts
against the square mass. -/
lemma nearMass_le_fiber (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    {d : ℕ} (hd : 1 ≤ d) (hPz : 4 * d ≤ Pa.Pz) :
    nearMass Pa X d β
      ≤ ∑ z ∈ Work.FITop.boxN Pa,
          (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ) * ‖β z‖ ^ 2 := by
  set s : Finset GaussianInt := Work.FITop.boxN Pa with hs
  set M : ℝ := Mthr Pa X with hM
  set f : GaussianInt → ℝ := fun z => ‖β z‖ with hf
  set cond : GaussianInt → GaussianInt → Prop :=
    fun z1 z2 => 0 < Work.FIPlan.absDelta z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
      ∧ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ M with hcond
  set ind : GaussianInt → GaussianInt → ℝ :=
    fun z1 z2 => if cond z1 z2 ∧ β z1 ≠ 0 ∧ β z2 ≠ 0 then 1 else 0 with hind
  have hsym : ∀ z1 z2, cond z1 z2 ↔ cond z2 z1 := by
    intro z1 z2
    have h := Work.FIArea6.S16ErrTwo.absDelta_comm z1 z2
    simp only [hcond]
    rw [h]
  have hind_sym : ∀ z1 z2, ind z1 z2 = ind z2 z1 := by
    intro z1 z2
    rw [hind]
    by_cases h : cond z1 z2 ∧ β z1 ≠ 0 ∧ β z2 ≠ 0
    · have h2 : cond z2 z1 ∧ β z2 ≠ 0 ∧ β z1 ≠ 0 :=
        ⟨(hsym z1 z2).mp h.1, h.2.2, h.2.1⟩
      simp [h, h2]
    · have h2 : ¬(cond z2 z1 ∧ β z2 ≠ 0 ∧ β z1 ≠ 0) := fun hc =>
        h ⟨(hsym z1 z2).mpr hc.1, hc.2.2, hc.2.1⟩
      simp [h, h2]
  have hunfold : nearMass Pa X d β
      = ∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * (f z1 * f z2) := by
    rw [show nearMass Pa X d β
      = ∑ z1 ∈ s, ∑ z2 ∈ s, (if cond z1 z2 then f z1 * f z2 else 0) from by
      simp only [nearMass, hs, hM, hcond, hf]]
    refine Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => ?_))
    rw [hind]
    by_cases h : cond z1 z2
    · by_cases h1 : β z1 = 0
      · simp [h, h1, hf]
      · by_cases h2 : β z2 = 0
        · simp [h, h1, h2, hf]
        · simp [h, h1, h2]
    · simp [h]
  have hcnt : ∀ z1 ∈ s, (∑ z2 ∈ s, ind z1 z2)
      ≤ (Work.FIArea6.fibCountDvdNear Pa φ d M z1 : ℝ) := by
    intro z1 _
    have hcard : (s.filter (fun z2 => cond z1 z2 ∧ β z1 ≠ 0 ∧ β z2 ≠ 0)).card
        ≤ Work.FIArea6.fibCountDvdNear Pa φ d M z1 := by
      rw [Work.FIArea6.fibCountDvdNear, ← hs]
      refine Finset.card_le_card (fun z2 hz2 => ?_)
      obtain ⟨hz2s, hc, -, hbz2⟩ := Finset.mem_filter.mp hz2
      exact Finset.mem_filter.mpr ⟨hz2s, hβ.support hbz2,
        Work.FIArea6.coprime_gnorm_four_mul hβ hbz2 hd hPz, hc.2.1, hc.2.2⟩
    rw [show (∑ z2 ∈ s, ind z1 z2)
        = ((s.filter (fun z2 => cond z1 z2 ∧ β z1 ≠ 0 ∧ β z2 ≠ 0)).card : ℝ) from by
      rw [hind]; exact Finset.sum_boole _ _]
    exact_mod_cast hcard
  have hA : (∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * f z1 ^ 2)
      = ∑ z1 ∈ s, f z1 ^ 2 * (∑ z2 ∈ s, ind z1 z2) := by
    refine Finset.sum_congr rfl (fun z1 _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z2 _ => by ring)
  have hB : (∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * f z2 ^ 2)
      = ∑ z1 ∈ s, f z1 ^ 2 * (∑ z2 ∈ s, ind z1 z2) := by
    rw [Finset.sum_comm]
    have h1 : (∑ z2 ∈ s, ∑ z1 ∈ s, ind z1 z2 * f z2 ^ 2)
        = ∑ z2 ∈ s, f z2 ^ 2 * (∑ z1 ∈ s, ind z1 z2) := by
      refine Finset.sum_congr rfl (fun z2 _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z1 _ => by ring)
    rw [h1]
    refine Finset.sum_congr rfl (fun z2 _ => ?_)
    rw [show (∑ z1 ∈ s, ind z1 z2) = (∑ w ∈ s, ind z2 w) from
      Finset.sum_congr rfl (fun w _ => hind_sym w z2)]
  have hmid : (∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * ((f z1 ^ 2 + f z2 ^ 2) / 2))
      = ((∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * f z1 ^ 2)
          + (∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * f z2 ^ 2)) / 2 := by
    have hinner : ∀ z1, (∑ z2 ∈ s, ind z1 z2 * ((f z1 ^ 2 + f z2 ^ 2) / 2))
        = (∑ z2 ∈ s, ind z1 z2 * f z1 ^ 2) / 2
          + (∑ z2 ∈ s, ind z1 z2 * f z2 ^ 2) / 2 := by
      intro z1
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun z2 _ => by ring)
    rw [Finset.sum_congr rfl (fun z1 _ => hinner z1)]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, add_div]
  rw [hunfold]
  calc ∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * (f z1 * f z2)
      ≤ ∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * ((f z1 ^ 2 + f z2 ^ 2) / 2) := by
        refine Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => ?_))
        have hnn : 0 ≤ ind z1 z2 := by simp only [hind]; split_ifs <;> norm_num
        have hgm : f z1 * f z2 ≤ (f z1 ^ 2 + f z2 ^ 2) / 2 := by
          nlinarith [sq_nonneg (f z1 - f z2)]
        exact mul_le_mul_of_nonneg_left hgm hnn
    _ = ((∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * f z1 ^ 2)
          + (∑ z1 ∈ s, ∑ z2 ∈ s, ind z1 z2 * f z2 ^ 2)) / 2 := hmid
    _ = ∑ z1 ∈ s, f z1 ^ 2 * (∑ z2 ∈ s, ind z1 z2) := by rw [hA, hB]; ring
    _ ≤ ∑ z1 ∈ s, f z1 ^ 2 * (Work.FIArea6.fibCountDvdNear Pa φ d M z1 : ℝ) :=
        Finset.sum_le_sum (fun z1 hz1 => mul_le_mul_of_nonneg_left (hcnt z1 hz1) (sq_nonneg _))
    _ = ∑ z ∈ s, (Work.FIArea6.fibCountDvdNear Pa φ d M z) * f z ^ 2 :=
        Finset.sum_congr rfl (fun z _ => by ring)
    _ = ∑ z ∈ Work.FITop.boxN Pa,
          (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ) * ‖β z‖ ^ 2 := by
        simp only [hs, hM, hf]


/-- **Step 2.** Summing the fibre bound over `d ≤ X`. -/
lemma fiber_sum_le (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z : GaussianInt) (hX : 1 ≤ X)
    (hzIn : Work.FITop3.InPolarBox Pa φ z)
    (hzcop : ∀ d ∈ Finset.Icc 1 X, Nat.Coprime (Work.FIPlan.gnorm z) (4 * d)) :
    (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
        * (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ))
      ≤ 4 * (X : ℝ) ^ 2
          + (10 * Pa.θ * Real.sqrt Pa.N + 2 * Mthr Pa X / Real.sqrt Pa.N) * X
          + 5 * Pa.θ * Mthr Pa X * (1 + Real.log (2 + X)) := by
  set M : ℝ := Mthr Pa X with hM
  set T1 : ℝ := 10 * Pa.θ * Real.sqrt Pa.N + 2 * M / Real.sqrt Pa.N with hT1
  have hNpos : 0 < Real.sqrt Pa.N := Real.sqrt_pos.mpr (by linarith [Pa.hN1])
  have hstep : ∀ d ∈ Finset.Icc 1 X,
      (Work.FIArea6.fibCountDvdNear Pa φ d M z : ℝ) ≤ 4 * (d : ℝ) + T1 + 5 * Pa.θ * M / (d : ℝ) := by
    intro d hdmem
    obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hdmem
    have hfib := Work.FIArea6.card_dvd_delta_fiber_near_le Pa φ d hd1 z hzIn (hzcop d hdmem) M
      (Mthr_nonneg Pa X)
    refine le_trans hfib (le_of_eq ?_)
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hN0 : Real.sqrt Pa.N ≠ 0 := ne_of_gt hNpos
    have h4d0 : 4 * (d : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hd0
    have h2d0 : 2 * (d : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hd0
    have h2dN0 : 2 * (d : ℝ) * Real.sqrt Pa.N ≠ 0 := mul_ne_zero h2d0 hN0
    rw [hT1]
    field_simp
    ring
  have hpt : ∀ d ∈ Finset.Icc 1 X,
      ((Nat.totient d : ℝ) / (d : ℝ)) * (4 * (d : ℝ) + T1 + 5 * Pa.θ * M / (d : ℝ))
        = 4 * (Nat.totient d : ℝ) + T1 * ((Nat.totient d : ℝ) / (d : ℝ))
          + 5 * Pa.θ * M * ((Nat.totient d : ℝ) / (d : ℝ) ^ 2) := by
    intro d hdmem
    have hd0 : (d : ℝ) ≠ 0 := by
      have h1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
      exact_mod_cast (by omega : d ≠ 0)
    field_simp
  have hS1 : (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ)) ≤ (X : ℝ) ^ 2 :=
    Work.FIArea6.totient_sum_le X hX
  have hS2 : (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ)) ≤ (X : ℝ) := by
    calc (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ))
        ≤ ∑ _d ∈ Finset.Icc 1 X, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun d hdmem => ?_)
          obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hdmem
          have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
          have hle : (Nat.totient d : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
          have h := div_le_div_of_nonneg_right hle hdpos.le
          rwa [div_self (ne_of_gt hdpos)] at h
      _ = (X : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc]
          have hc : (X + 1 - 1 : ℕ) = X := by omega
          rw [hc, nsmul_eq_mul, mul_one]
  have hS3 : (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ) ^ 2)
      ≤ 1 + Real.log (2 + (X : ℝ)) := phi_div_sq_sum_le_aux X hX
  have hT1nn : 0 ≤ T1 := by
    rw [hT1]
    have h1 : 0 ≤ 10 * Pa.θ * Real.sqrt Pa.N :=
      mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) hNpos.le
    have h2 : 0 ≤ 2 * M / Real.sqrt Pa.N :=
      div_nonneg (mul_nonneg (by norm_num) (Mthr_nonneg Pa X)) hNpos.le
    linarith
  have hw5 : 0 ≤ 5 * Pa.θ * M :=
    mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) (Mthr_nonneg Pa X)
  rw [show (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
        * (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ))
      = ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
        * (Work.FIArea6.fibCountDvdNear Pa φ d M z : ℝ) from by simp only [hM]]
  calc (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
        * (Work.FIArea6.fibCountDvdNear Pa φ d M z : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
          * (4 * (d : ℝ) + T1 + 5 * Pa.θ * M / (d : ℝ)) := by
        refine Finset.sum_le_sum (fun d hdmem => mul_le_mul_of_nonneg_left (hstep d hdmem) ?_)
        exact div_nonneg (by positivity) (by positivity)
    _ = 4 * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ))
          + T1 * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ))
          + 5 * Pa.θ * M * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ) ^ 2) := by
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 4 * (X : ℝ) ^ 2 + T1 * (X : ℝ) + 5 * Pa.θ * M * (1 + Real.log (2 + X)) := by
        have e1 : 4 * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ)) ≤ 4 * (X : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hS1 (by norm_num)
        have e2 : T1 * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ)) ≤ T1 * (X : ℝ) :=
          mul_le_mul_of_nonneg_left hS2 hT1nn
        have e3 : 5 * Pa.θ * M * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ) ^ 2)
            ≤ 5 * Pa.θ * M * (1 + Real.log (2 + X)) :=
          mul_le_mul_of_nonneg_left hS3 hw5
        linarith
    _ = 4 * (X : ℝ) ^ 2
          + (10 * Pa.θ * Real.sqrt Pa.N + 2 * Mthr Pa X / Real.sqrt Pa.N) * X
          + 5 * Pa.θ * Mthr Pa X * (1 + Real.log (2 + X)) := by
        rw [hT1, hM]

/-- **The near-diagonal mass of §16.**  With `M = 2πN/X`, `1 ≤ X`, `4X ≤ Pz`,

`Σ_{d ≤ X} (φ(d)/d)·nearMass X d β  ≤  C (Σ_{z ∈ boxN} ‖βz‖²)(1+log(2+X))(X² + θ√N·X + √N + θN/X)`

(for the round-6 coefficient class; `nearMass` is the pair mass with `0 < |Δ(z₁,z₂)| ≤ M` and
`4d ∣ |Δ(z₁,z₂)|` defined in `S16ErrTwo/Defs.lean`). -/
theorem nearMass_le :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → 4 * X ≤ Pa.Pz →
      (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * nearMass Pa X d β)
        ≤ C * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ))
            * (1 + Real.log (2 + X))
            * ((X : ℝ) ^ (2 : ℕ) + Pa.θ * Real.sqrt Pa.N * X + Real.sqrt Pa.N
                + Pa.θ * Pa.N / X) := by
  refine ⟨128, by norm_num, ?_⟩
  intro Pa X φ z0 β hβ hX h4X
  set BIG : ℝ := 128 * (1 + Real.log (2 + X))
      * ((X : ℝ) ^ 2 + Pa.θ * Real.sqrt Pa.N * X + Real.sqrt Pa.N + Pa.θ * Pa.N / X) with hBIG
  have hstep1 : ∀ d ∈ Finset.Icc 1 X, nearMass Pa X d β
      ≤ ∑ z ∈ Work.FITop.boxN Pa,
          (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ) * ‖β z‖ ^ 2 := by
    intro d hdmem
    obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp hdmem
    exact nearMass_le_fiber Pa X φ z0 β hβ hd1 (le_trans (Nat.mul_le_mul_left 4 hdX) h4X)
  have hstep2 : (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
        * (∑ z ∈ Work.FITop.boxN Pa,
            (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ) * ‖β z‖ ^ 2))
      ≤ ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 * BIG := by
    calc (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
          * (∑ z ∈ Work.FITop.boxN Pa,
              (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ) * ‖β z‖ ^ 2))
        = ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2
            * (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
                * (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ)) := by
          have h1 : ∀ d : ℕ, ((Nat.totient d : ℝ) / (d : ℝ))
              * (∑ z ∈ Work.FITop.boxN Pa,
                  (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ) * ‖β z‖ ^ 2)
              = ∑ z ∈ Work.FITop.boxN Pa, ((Nat.totient d : ℝ) / (d : ℝ))
                  * ((Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ) * ‖β z‖ ^ 2) := by
            intro d
            rw [Finset.mul_sum]
          rw [Finset.sum_congr rfl (fun d _ => h1 d), Finset.sum_comm]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => by ring)
      _ ≤ ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 * BIG := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          by_cases hbz : β z = 0
          · rw [hbz]; simp
          · have hzIn : Work.FITop3.InPolarBox Pa φ z := hβ.support hbz
            have hzc : ∀ d ∈ Finset.Icc 1 X, Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) := by
              intro d hdmem
              obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp hdmem
              exact Work.FIArea6.coprime_gnorm_four_mul hβ hbz hd1
                (le_trans (Nat.mul_le_mul_left 4 hdX) h4X)
            have hA := fiber_sum_le Pa X φ z hX hzIn hzc
            have hC : 4 * (X : ℝ) ^ 2
                + (10 * Pa.θ * Real.sqrt Pa.N + 2 * Mthr Pa X / Real.sqrt Pa.N) * X
                + 5 * Pa.θ * Mthr Pa X * (1 + Real.log (2 + X)) ≤ BIG := by
              rw [hBIG]; exact s16err_arith_bound_aux Pa X hX
            exact mul_le_mul_of_nonneg_left (le_trans hA hC) (sq_nonneg _)
  have hstep3 : (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 * BIG)
      = 128 * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)) * (1 + Real.log (2 + X))
          * ((X : ℝ) ^ (2 : ℕ) + Pa.θ * Real.sqrt Pa.N * X + Real.sqrt Pa.N
              + Pa.θ * Pa.N / X) := by
    rw [hBIG, ← Finset.sum_mul]
    ring
  calc (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * nearMass Pa X d β)
      ≤ ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))
          * (∑ z ∈ Work.FITop.boxN Pa,
              (Work.FIArea6.fibCountDvdNear Pa φ d (Mthr Pa X) z : ℝ) * ‖β z‖ ^ 2) := by
        refine Finset.sum_le_sum (fun d hdmem => mul_le_mul_of_nonneg_left (hstep1 d hdmem) ?_)
        exact div_nonneg (by positivity) (by positivity)
    _ ≤ ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 * BIG := hstep2
    _ = 128 * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)) * (1 + Real.log (2 + X))
          * ((X : ℝ) ^ (2 : ℕ) + Pa.θ * Real.sqrt Pa.N * X + Real.sqrt Pa.N
              + Pa.θ * Pa.N / X) := hstep3


end


open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `Σ_{k ∈ [1,M]} 1/k ≤ 1 + log M` (the integral comparison, in `ℝ`). -/
lemma sum_inv_Icc_le_far (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, ((k : ℝ))⁻¹) ≤ 1 + Real.log (M : ℝ) := by
  have h : (harmonic M : ℝ) ≤ 1 + Real.log (M : ℝ) := by
    have := harmonic_le_one_add_log M
    exact_mod_cast this
  have h2 : (harmonic M : ℝ) = ∑ k ∈ Finset.Icc 1 M, ((k : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rwa [h2] at h

lemma farMass_le_Sfar (Pa : Work.FITop.Params) (X : ℕ) (d : ℕ) (β : GaussianInt → ℂ)
    (hX : 1 ≤ X) :
    farMass Pa X d β ≤ (8 * Pa.N / (X : ℝ) ^ (3 : ℕ)) * Sfar Pa X β := by
  have h8N : (0 : ℝ) ≤ 8 * (Pa.N : ℝ) := by
    have := Pa.hN1; linarith
  have hX3 : (0 : ℝ) ≤ (X : ℝ) ^ (3 : ℕ) := by positivity
  unfold farMass Sfar
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun z1 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun z2 _ => ?_)
  by_cases hM : Mthr Pa X < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
  · rw [if_pos hM]
    have hde : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≠ 0 := by
      intro h0; rw [h0] at hM; linarith [Mthr_nonneg Pa X]
    by_cases hC : Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        ∧ Mthr Pa X < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
    · rw [if_pos hC]
      have hXne : (X : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hX))
      rw [show ‖β z1‖ * ‖β z2‖ * (8 * Pa.N / ((Work.FIArea6.Kcut X : ℝ)
            * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)))
          = (8 * Pa.N / (X : ℝ) ^ (3 : ℕ))
            * (‖β z1‖ * ‖β z2‖ / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) from by
        rw [Work.FIArea6.Kcut]; push_cast; field_simp]
    · rw [if_neg hC]
      apply mul_nonneg (div_nonneg h8N hX3)
      exact div_nonneg (by positivity) (by positivity)
  · rw [if_neg hM, mul_zero]
    rw [if_neg (fun hC => hM hC.2.2)]

lemma fiber_card_le (R : ℤ) (hR : 0 ≤ R) (a b n : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a.natAbs b.natAbs) :
    ((Work.FIPlan.gBox R).filter (fun z => a * z.im - b * z.re = n)).card
      ≤ 2 * R.natAbs / (max a.natAbs b.natAbs) + 1 := by
  have hRR : (R.natAbs : ℤ) = R := Int.natAbs_of_nonneg hR
  have habs : 1 ≤ a.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ha)
  have boundU : ((Work.FIPlan.gBox R).filter (fun z => a * z.im - b * z.re = n)).card
      ≤ 2 * R.natAbs / a.natAbs + 1 := by
    set S := (Work.FIPlan.gBox R).filter (fun z => a * z.im - b * z.re = n) with hS
    have hmaps : Set.MapsTo (fun z : GaussianInt => z.re) (↑S : Set GaussianInt)
        (↑((Finset.Icc (-(R.natAbs : ℤ)) (R.natAbs : ℤ)).filter
            (fun u => (a.natAbs : ℤ) ∣ (b * u + n))) : Set ℤ) := by
      intro z hz
      rw [Finset.mem_coe, hS, Finset.mem_filter] at hz
      rw [Finset.mem_coe, Finset.mem_filter]
      obtain ⟨hg, hΔ⟩ := hz
      rw [Work.FIArea4.mem_gBox] at hg
      obtain ⟨h1, h2, h3, h4⟩ := hg
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact ⟨by rw [hRR]; exact h1, by rw [hRR]; exact h2⟩
      · rw [Int.natAbs_dvd]
        have hsum : b * z.re + n = a * z.im := by rw [← hΔ]; ring
        rw [hsum]; exact dvd_mul_right a z.im
    have hinj : (↑S : Set GaussianInt).InjOn (fun z : GaussianInt => z.re) := by
      intro z1 hz1 z2 hz2 hre
      change z1.re = z2.re at hre
      rw [Finset.mem_coe, hS, Finset.mem_filter] at hz1 hz2
      obtain ⟨-, hΔ1⟩ := hz1
      obtain ⟨-, hΔ2⟩ := hz2
      refine Zsqrtd.ext hre ?_
      have key : a * z1.im = a * z2.im := by
        have : a * z1.im - b * z1.re = a * z2.im - b * z2.re := by rw [hΔ1, hΔ2]
        rw [hre] at this
        linarith
      exact mul_left_cancel₀ ha key
    calc S.card ≤ _ := Finset.card_le_card_of_injOn _ hmaps hinj
      _ ≤ 2 * R.natAbs / a.natAbs + 1 :=
          card_Icc_filter_dvd_le a.natAbs habs b n R.natAbs hcop
  have boundV : ((Work.FIPlan.gBox R).filter (fun z => a * z.im - b * z.re = n)).card
      ≤ 2 * R.natAbs / b.natAbs + 1 := by
    set S := (Work.FIPlan.gBox R).filter (fun z => a * z.im - b * z.re = n) with hS
    have hmaps : Set.MapsTo (fun z : GaussianInt => z.im) (↑S : Set GaussianInt)
        (↑((Finset.Icc (-(R.natAbs : ℤ)) (R.natAbs : ℤ)).filter
            (fun u => (b.natAbs : ℤ) ∣ (a * u + (-n)))) : Set ℤ) := by
      intro z hz
      rw [Finset.mem_coe, hS, Finset.mem_filter] at hz
      rw [Finset.mem_coe, Finset.mem_filter]
      obtain ⟨hg, hΔ⟩ := hz
      rw [Work.FIArea4.mem_gBox] at hg
      obtain ⟨h1, h2, h3, h4⟩ := hg
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact ⟨by rw [hRR]; exact h3, by rw [hRR]; exact h4⟩
      · rw [Int.natAbs_dvd]
        have hsum : a * z.im + (-n) = b * z.re := by rw [← hΔ]; ring
        rw [hsum]; exact dvd_mul_right b z.re
    have hinj : (↑S : Set GaussianInt).InjOn (fun z : GaussianInt => z.im) := by
      intro z1 hz1 z2 hz2 him
      change z1.im = z2.im at him
      rw [Finset.mem_coe, hS, Finset.mem_filter] at hz1 hz2
      obtain ⟨-, hΔ1⟩ := hz1
      obtain ⟨-, hΔ2⟩ := hz2
      refine Zsqrtd.ext ?_ him
      have key : b * z1.re = b * z2.re := by
        have : a * z1.im - b * z1.re = a * z2.im - b * z2.re := by rw [hΔ1, hΔ2]
        rw [him] at this
        linarith
      exact mul_left_cancel₀ hb key
    calc S.card ≤ _ := Finset.card_le_card_of_injOn _ hmaps hinj
      _ ≤ 2 * R.natAbs / b.natAbs + 1 :=
          card_Icc_filter_dvd_le b.natAbs (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
            a (-n) R.natAbs (Nat.Coprime.symm hcop)
  by_cases h : a.natAbs ≤ b.natAbs
  · rw [max_eq_right h]
    exact boundV
  · rw [max_eq_left (not_le.mp h).le]
    exact boundU

lemma Wsum_le {Pa : Work.FITop.Params} {X : ℕ} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hX : 1 ≤ X) {z : GaussianInt} (hz : β z ≠ 0) :
    Wsum Pa X z ≤ 1000 * (1 + Real.log (2 + (Pa.N : ℝ))) := by
  have hM0 : 0 ≤ Mthr Pa X := Mthr_nonneg Pa X
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := Pa.hN1
  have hpol := Work.FITop4.IsBetaCoeff6.support hβ hz
  obtain ⟨-, hNlt, hNle, -⟩ := hpol
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea6.theta_le_one_of_params Pa
  have hgnorm_le : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * (Pa.N : ℝ) := by
    nlinarith [hNle, hθ1, hN1]
  have hprim0 : Nat.Coprime z.re.natAbs (2 * z.im.natAbs) :=
    (Work.FIArea4.prim_of_beta6 hβ).coprime hz
  have hprim : Nat.Coprime z.re.natAbs z.im.natAbs :=
    hprim0.coprime_dvd_right (dvd_mul_left z.im.natAbs 2)
  have hg2 : 2 ≤ Work.FIPlan.gnorm z := by
    have hgt : (1 : ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by linarith
    have hgt' : (1 : ℕ) < Work.FIPlan.gnorm z := by exact_mod_cast hgt
    omega
  have ha : z.re ≠ 0 := by
    intro h0
    have hre0 : z.re.natAbs = 0 := by simp [h0]
    have hc0 : Nat.Coprime 0 z.im.natAbs := by rw [← hre0]; exact hprim
    have him1 : z.im.natAbs = 1 := (Nat.coprime_zero_left _).mp hc0
    have hg1 : Work.FIPlan.gnorm z = 1 := by
      rw [Work.FIArea4.gnorm_eq_re_sq_add_im_sq, hre0, him1]; norm_num
    omega
  have hb : z.im ≠ 0 := by
    intro h0
    have him0 : z.im.natAbs = 0 := by simp [h0]
    have hc0 : Nat.Coprime z.re.natAbs 0 := by rw [← him0]; exact hprim
    have hre1 : z.re.natAbs = 1 := (Nat.coprime_zero_right _).mp hc0
    have hg1 : Work.FIPlan.gnorm z = 1 := by
      rw [Work.FIArea4.gnorm_eq_re_sq_add_im_sq, hre1, him0]; norm_num
    omega
  have hR0 : (0 : ℤ) ≤ Work.FITop.radN Pa := by rw [Work.FITop.radN]; positivity
  have hRle : ((Work.FITop.radN Pa : ℤ) : ℝ) ≤ 3 * Real.sqrt (Pa.N : ℝ) := by
    have hrad : ((Work.FITop.radN Pa : ℤ) : ℝ) = (⌈Real.sqrt (4 * (Pa.N : ℝ))⌉₊ : ℝ) := by
      rw [Work.FITop.radN]; simp
    rw [hrad]
    have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ Real.sqrt (4 * (Pa.N : ℝ)) by positivity)
    have hsq : Real.sqrt (4 * (Pa.N : ℝ)) = 2 * Real.sqrt (Pa.N : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [hsq] at hceil
    rw [hsq]
    have hsqN : 1 ≤ Real.sqrt (Pa.N : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
    linarith
  have hre_le : |(z.re : ℝ)| ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
    rw [GaussianInt.intCast_re]
    calc |((z : ℂ).re)| ≤ ‖(z : ℂ)‖ := Complex.abs_re_le_norm _
      _ = Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := Work.FIArea4.norm_toComplex_eq_sqrt_gnorm z
  have him_le : |(z.im : ℝ)| ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
    rw [GaussianInt.intCast_im]
    calc |((z : ℂ).im)| ≤ ‖(z : ℂ)‖ := Complex.abs_im_le_norm _
      _ = Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := Work.FIArea4.norm_toComplex_eq_sqrt_gnorm z
  have hDbd : ∀ z2 ∈ Work.FITop.boxN Pa,
      ((Work.FIPlan.absDelta z z2 : ℕ) : ℝ) ≤ 12 * (Pa.N : ℝ) := by
    intro z2 hz2
    have hz2g : z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa) := hz2
    rw [Work.FIArea4.mem_gBox] at hz2g
    obtain ⟨h1, h2, h3, h4⟩ := hz2g
    have hRre : |((z2.re : ℤ) : ℝ)| ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) := by
      rw [abs_le]; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    have hRim : |((z2.im : ℤ) : ℝ)| ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) := by
      rw [abs_le]; exact ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩
    have hcast : ((Work.FIPlan.absDelta z z2 : ℕ) : ℝ) = |((Work.FIPlan.Delta z z2 : ℤ) : ℝ)| := by
      rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
    have hΔeq : ((Work.FIPlan.Delta z z2 : ℤ) : ℝ)
        = (z.re : ℝ) * (z2.im : ℝ) - (z2.re : ℝ) * (z.im : ℝ) := by
      rw [Work.FIArea4.Delta_eq]; push_cast; ring
    rw [hcast, hΔeq]
    have hG : Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ Real.sqrt 2 * Real.sqrt (Pa.N : ℝ) := by
      have := Real.sqrt_le_sqrt hgnorm_le
      rwa [Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)] at this
    have hsum : |(z.re : ℝ)| + |(z.im : ℝ)| ≤ 2 * Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
      linarith [hre_le, him_le]
    have hD1 : |(z.re : ℝ) * (z2.im : ℝ) - (z2.re : ℝ) * (z.im : ℝ)|
        ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) * (|(z.re : ℝ)| + |(z.im : ℝ)|) := by
      calc |(z.re : ℝ) * (z2.im : ℝ) - (z2.re : ℝ) * (z.im : ℝ)|
          ≤ |(z.re : ℝ) * (z2.im : ℝ)| + |(z2.re : ℝ) * (z.im : ℝ)| := abs_sub _ _
        _ = |(z.re : ℝ)| * |(z2.im : ℝ)| + |(z2.re : ℝ)| * |(z.im : ℝ)| := by rw [abs_mul, abs_mul]
        _ ≤ |(z.re : ℝ)| * ((Work.FITop.radN Pa : ℤ) : ℝ)
              + ((Work.FITop.radN Pa : ℤ) : ℝ) * |(z.im : ℝ)| := by
            nlinarith [mul_le_mul_of_nonneg_left hRim (abs_nonneg (z.re : ℝ)),
              mul_le_mul_of_nonneg_right hRre (abs_nonneg (z.im : ℝ))]
        _ = ((Work.FITop.radN Pa : ℤ) : ℝ) * (|(z.re : ℝ)| + |(z.im : ℝ)|) := by ring
    have hT2 : (Real.sqrt (Pa.N : ℝ)) ^ 2 = (Pa.N : ℝ) := Real.sq_sqrt (by linarith)
    have hsq2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hfin : ((Work.FITop.radN Pa : ℤ) : ℝ) * (|(z.re : ℝ)| + |(z.im : ℝ)|)
        ≤ 12 * (Pa.N : ℝ) := by
      have hRs0 : (0 : ℝ) ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) := by exact_mod_cast hR0
      have h1 : ((Work.FITop.radN Pa : ℤ) : ℝ) * (|(z.re : ℝ)| + |(z.im : ℝ)|)
          ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) * (2 * Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hRs0
      have hprod : 2 * ((Work.FITop.radN Pa : ℤ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ)
          ≤ 2 * (3 * Real.sqrt (Pa.N : ℝ)) * (Real.sqrt 2 * Real.sqrt (Pa.N : ℝ)) :=
        mul_le_mul (by linarith [hRle]) hG (Real.sqrt_nonneg _) (by positivity)
      nlinarith [h1, hprod, hT2, hsq2, hN1, hRs0]
    calc |(z.re : ℝ) * (z2.im : ℝ) - (z2.re : ℝ) * (z.im : ℝ)|
        ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) * (|(z.re : ℝ)| + |(z.im : ℝ)|) := hD1
      _ ≤ 12 * (Pa.N : ℝ) := hfin
  set K : ℕ := ⌈12 * (Pa.N : ℝ)⌉₊ with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    have h : (1 : ℝ) ≤ (⌈12 * (Pa.N : ℝ)⌉₊ : ℝ) := le_trans (by linarith [hN1]) (Nat.le_ceil _)
    exact_mod_cast h
  have hmemD : ∀ z2 ∈ Work.FITop.boxN Pa, Work.FIPlan.Delta z z2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro z2 hz2
    rw [Finset.mem_Icc, ← abs_le]
    have hnat : (Work.FIPlan.Delta z z2).natAbs ≤ K := by
      have h1 : ((Work.FIPlan.Delta z z2).natAbs : ℝ) ≤ 12 * (Pa.N : ℝ) := by
        have := hDbd z2 hz2
        rwa [Work.FIPlan.absDelta] at this
      rw [hKdef]
      exact_mod_cast (le_trans h1 (Nat.le_ceil _))
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  set S : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ) with hSdef
  have step1 : Wsum Pa X z ≤ ∑ z2 ∈ Work.FITop.boxN Pa, invNatAbs (Work.FIPlan.Delta z z2) := by
    rw [Wsum]
    refine Finset.sum_le_sum (fun z2 hz2 => ?_)
    rw [invNatAbs]
    by_cases hM : Mthr Pa X < ((Work.FIPlan.absDelta z z2 : ℕ) : ℝ)
    · rw [if_pos hM]
      simp only [Work.FIPlan.absDelta, one_div]
      exact le_refl _
    · rw [if_neg hM]
      positivity
  have step2 : (∑ z2 ∈ Work.FITop.boxN Pa, invNatAbs (Work.FIPlan.Delta z z2))
      = ∑ n ∈ S, invNatAbs n
          * ((((Work.FITop.boxN Pa).filter (fun z2 => Work.FIPlan.Delta z z2 = n))).card : ℝ) := by
    have hterm : ∀ z2 ∈ Work.FITop.boxN Pa,
        invNatAbs (Work.FIPlan.Delta z z2)
          = ∑ n ∈ S, (if Work.FIPlan.Delta z z2 = n then invNatAbs n else 0) := by
      intro z2 hz2
      rw [Finset.sum_ite_eq, if_pos (hmemD z2 hz2)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hB : ∀ n : ℤ,
      ((((Work.FITop.boxN Pa).filter (fun z2 => Work.FIPlan.Delta z z2 = n))).card : ℝ) ≤ 10 := by
    intro n
    have hbox : Work.FITop.boxN Pa = Work.FIPlan.gBox (Work.FITop.radN Pa) := rfl
    have hcard : ((Work.FITop.boxN Pa).filter (fun z2 => Work.FIPlan.Delta z z2 = n)).card
        = ((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
            (fun z2 => z.re * z2.im - z.im * z2.re = n)).card := by
      rw [hbox]; congr 1; ext z2
      rw [Finset.mem_filter, Finset.mem_filter]
      exact and_congr_right (fun _ => by rw [Work.FIArea4.Delta_eq, mul_comm z2.re z.im])
    rw [hcard]
    have hfib := fiber_card_le (Work.FITop.radN Pa) hR0 z.re z.im n ha hb hprim
    have hRle' : (((Work.FITop.radN Pa).natAbs : ℕ) : ℝ) ≤ 3 * Real.sqrt (Pa.N : ℝ) := by
      have hcast : (((Work.FITop.radN Pa).natAbs : ℕ) : ℝ) = ((Work.FITop.radN Pa : ℤ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact abs_of_nonneg (by exact_mod_cast hR0)
      rw [hcast]; exact hRle
    have hmax' : Real.sqrt (Pa.N : ℝ) ≤ Real.sqrt 2 * (max z.re.natAbs z.im.natAbs : ℝ) := by
      have hgn : ((Work.FIPlan.gnorm z : ℕ) : ℝ)
          = (z.re.natAbs : ℝ) ^ 2 + (z.im.natAbs : ℝ) ^ 2 := by
        have h0 := Work.FIArea4.gnorm_eq_re_sq_add_im_sq z
        rw [h0]; push_cast; ring
      have hmax2 : (z.re.natAbs : ℝ) ^ 2 + (z.im.natAbs : ℝ) ^ 2
          ≤ 2 * (max z.re.natAbs z.im.natAbs : ℝ) ^ 2 := by
        have hle1 : (z.re.natAbs : ℝ) ≤ (max z.re.natAbs z.im.natAbs : ℝ) := by
          exact_mod_cast Nat.le_max_left z.re.natAbs z.im.natAbs
        have hle2 : (z.im.natAbs : ℝ) ≤ (max z.re.natAbs z.im.natAbs : ℝ) := by
          exact_mod_cast Nat.le_max_right z.re.natAbs z.im.natAbs
        nlinarith [sq_nonneg ((z.re.natAbs : ℝ) - (max z.re.natAbs z.im.natAbs : ℝ)),
          sq_nonneg ((z.im.natAbs : ℝ) - (max z.re.natAbs z.im.natAbs : ℝ))]
      have hsq : (Pa.N : ℝ) ≤ 2 * (max z.re.natAbs z.im.natAbs : ℝ) ^ 2 := by
        have hlt : (Pa.N : ℝ) < (z.re.natAbs : ℝ) ^ 2 + (z.im.natAbs : ℝ) ^ 2 := by
          rw [← hgn]; exact hNlt
        linarith [hmax2]
      have hmax0 : (0 : ℝ) ≤ (max z.re.natAbs z.im.natAbs : ℝ) := by positivity
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hmax0] at this
    have hmaxpos : (1 : ℝ) ≤ (max z.re.natAbs z.im.natAbs : ℝ) := by
      have h1 : (1 : ℕ) ≤ max z.re.natAbs z.im.natAbs :=
        le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ha))
          (Nat.le_max_left z.re.natAbs z.im.natAbs)
      exact_mod_cast h1
    have h2 : (2 * (Work.FITop.radN Pa).natAbs : ℝ) < 10 * (max z.re.natAbs z.im.natAbs : ℝ) := by
      have h1 : (2 * (Work.FITop.radN Pa).natAbs : ℝ) ≤ 6 * Real.sqrt (Pa.N : ℝ) := by linarith [hRle']
      have hsix : (6 : ℝ) * Real.sqrt 2 < 10 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      have hsN : 0 ≤ Real.sqrt (Pa.N : ℝ) := Real.sqrt_nonneg _
      nlinarith [h1, hmax', hsix, hsN, hmaxpos]
    have h2n : 2 * (Work.FITop.radN Pa).natAbs < 10 * max z.re.natAbs z.im.natAbs := by
      exact_mod_cast h2
    have hma : 0 < max z.re.natAbs z.im.natAbs :=
      lt_of_lt_of_le Nat.zero_lt_one
        (le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ha))
          (Nat.le_max_left z.re.natAbs z.im.natAbs))
    have hdiv : 2 * (Work.FITop.radN Pa).natAbs / max z.re.natAbs z.im.natAbs < 10 :=
      Nat.div_lt_iff_lt_mul hma |>.mpr h2n
    have hfin : 2 * (Work.FITop.radN Pa).natAbs / max z.re.natAbs z.im.natAbs + 1 ≤ 10 := by omega
    exact_mod_cast (le_trans hfib hfin)
  have step3 : (∑ n ∈ S, invNatAbs n
        * ((((Work.FITop.boxN Pa).filter (fun z2 => Work.FIPlan.Delta z z2 = n))).card : ℝ))
      ≤ 10 * ∑ n ∈ S, invNatAbs n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn0 : 0 ≤ invNatAbs n := invNatAbs_nonneg n
    nlinarith [hn0, hB n]
  have step4 : (∑ n ∈ S, invNatAbs n) ≤ 2 * (1 + Real.log (K : ℝ)) := by
    rw [hSdef]
    exact sum_natAbs_inv_le K hK1
  have hmain : Wsum Pa X z ≤ 20 * (1 + Real.log (K : ℝ)) := by
    refine le_trans step1 ?_
    rw [step2]
    refine le_trans step3 ?_
    have h := mul_le_mul_of_nonneg_left step4 (by norm_num : (0 : ℝ) ≤ 10)
    linarith [h]
  refine le_trans hmain ?_
  have hlog : Real.log (K : ℝ) ≤ Real.log 13 + Real.log (2 + (Pa.N : ℝ)) := by
    have hceil : (K : ℝ) < 12 * (Pa.N : ℝ) + 1 := by
      rw [hKdef]; exact Nat.ceil_lt_add_one (by positivity)
    have hle : (K : ℝ) ≤ 13 * (Pa.N : ℝ) := by
      have : 12 * (Pa.N : ℝ) + 1 ≤ 13 * (Pa.N : ℝ) := by linarith [hN1]
      linarith
    have hpos : (0 : ℝ) < (K : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1)
    calc Real.log (K : ℝ) ≤ Real.log (13 * (Pa.N : ℝ)) := Real.log_le_log hpos hle
      _ = Real.log 13 + Real.log (Pa.N : ℝ) := Real.log_mul (by norm_num) (by linarith)
      _ ≤ Real.log 13 + Real.log (2 + (Pa.N : ℝ)) := by
          have hle2 : Real.log (Pa.N : ℝ) ≤ Real.log (2 + (Pa.N : ℝ)) :=
            Real.log_le_log (by linarith) (by linarith)
          linarith
  have hlog12 : Real.log 13 ≤ 4 := by
    have h1 : Real.log (13 : ℝ) ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    rw [h2] at h1; linarith
  have hlog3 : 1 ≤ Real.log (2 + (Pa.N : ℝ)) := by
    have h1 : Real.log 3 ≤ Real.log (2 + (Pa.N : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    have h2 : (1 : ℝ) ≤ Real.log 3 := by
      have h3 := Real.exp_one_lt_three
      have h4 := Real.log_le_log (Real.exp_pos 1) h3.le
      rwa [Real.log_exp] at h4
    linarith
  nlinarith [hlog, hlog12, hlog3, Real.log_nonneg hlog3]

/-- **The far piece of §16.**  With `M = 2πN/X`, `1 ≤ X`, `4X ≤ Pz`, the far pairs
(`GaussCoprime`, `4d ∣ |Δ|`, `|Δ| > M`) weighted by the *pointwise* truncation error
`8N/(X³|Δ|)` satisfy

`Σ_{d ≤ X} (φ(d)/d)·farMass X d β ≤ C (Σ_{z ∈ boxN}‖βz‖²)·N·(1+log(2+N))/X²`.

*Route.*  `‖logFac6 − logFac6Series (Kcut X)‖ ≤ 8N/(X³|Δ|)` for `Δ ≠ 0` on the support
(`Work.FIArea6.error_le_far`), so dropping the `4d ∣ |Δ|` condition and using
`Σ_{d≤X} φ(d)/d ≤ X` reduces the claim to
`(8N/X³)·Σ_{z₁,z₂ ∈ boxN, |Δ(z₁,z₂)| > M} ‖βz₁‖‖βz₂‖/|Δ(z₁,z₂)| ≤ C(Σ_z‖βz‖²)N(1+log(2+N))/X²`,
i.e. to `Σ_{z′ ∈ boxN, |Δ(z,z′)| > M} 1/|Δ(z,z′)| ≤ C(1+log(2+N))` for every `z ∈ supp β`.

*The last sum.*  Write `a = z.re`, `b = z.im`, `R = radN Pa`, and sum over the columns
`z′.re = u ∈ [−R,R]`: in a column, `Δ(z,z′) = a·v − b·u` runs over an arithmetic progression of
spacing `|a|` in `v ∈ [−R,R]`, so (for `|a| ≥ |z|/√2 ≥ √N/√2`, which holds on the support)

`Σ_v [|a v − b u| > M]/|a v − b u| ≤ (1/|a|)·(1 + log(2 + R|a|/M)) ≤ (2/√N)(1 + log(2 + 2RX))`,

since `M = 2πN/X`.  There are `2R+1 ≍ √N` columns, so the total is `≪ 1 + log(2+N)`
(use `absDelta_comm` for the symmetry of the kernel, and `Work.FIArea6.error_le_far` for the
pointwise error). -/
theorem farMass_le :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → 4 * X ≤ Pa.Pz →
      (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * farMass Pa X d β)
        ≤ C * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)) * Pa.N
            * (1 + Real.log (2 + Pa.N)) / (X : ℝ) ^ (2 : ℕ) := by
  refine ⟨8000, by norm_num, ?_⟩
  intro Pa X φ z0 β hβ hX hPz
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := Pa.hN1
  have hstep1 : (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * farMass Pa X d β)
      ≤ (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)))
          * ((8 * Pa.N / (X : ℝ) ^ (3 : ℕ)) * Sfar Pa X β) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun d hd => ?_)
    exact mul_le_mul_of_nonneg_left (farMass_le_Sfar Pa X d β hX)
      (div_nonneg (by positivity) (by positivity))
  have hstep2 : (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ))) ≤ (X : ℝ) := by
    calc (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)))
        ≤ ∑ _d ∈ Finset.Icc 1 X, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun d hd => ?_)
          rw [Finset.mem_Icc] at hd
          have hd0 : (0 : ℝ) < (d : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd.1)
          exact div_le_one_of_le₀ (by exact_mod_cast Nat.totient_le d) (le_of_lt hd0)
      _ = (X : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
          simp
  have hSfar : Sfar Pa X β
      ≤ (1000 * (1 + Real.log (2 + (Pa.N : ℝ))))
          * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)) := by
    refine le_trans (Sfar_le_Wsum Pa X β) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun z hz => ?_)
    by_cases hz0 : β z = 0
    · rw [hz0]; simp
    · have hW := Wsum_le hβ hX hz0
      have hnn : 0 ≤ ‖β z‖ ^ (2 : ℕ) := by positivity
      calc ‖β z‖ ^ (2 : ℕ) * Wsum Pa X z
          ≤ ‖β z‖ ^ (2 : ℕ) * (1000 * (1 + Real.log (2 + (Pa.N : ℝ)))) :=
            mul_le_mul_of_nonneg_left hW hnn
        _ = (1000 * (1 + Real.log (2 + (Pa.N : ℝ)))) * ‖β z‖ ^ (2 : ℕ) := by ring
  have hmain : (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * farMass Pa X d β)
      ≤ (8 * Pa.N / (X : ℝ) ^ (2 : ℕ)) * Sfar Pa X β := by
    have heq2 : (X : ℝ) * ((8 * Pa.N / (X : ℝ) ^ (3 : ℕ)) * Sfar Pa X β)
        = (8 * Pa.N / (X : ℝ) ^ (2 : ℕ)) * Sfar Pa X β := by
      field_simp
    calc (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * farMass Pa X d β)
        ≤ (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)))
            * ((8 * Pa.N / (X : ℝ) ^ (3 : ℕ)) * Sfar Pa X β) := hstep1
      _ ≤ (X : ℝ) * ((8 * Pa.N / (X : ℝ) ^ (3 : ℕ)) * Sfar Pa X β) :=
          mul_le_mul_of_nonneg_right hstep2
            (mul_nonneg (div_nonneg (by positivity) (by positivity)) (Sfar_nonneg Pa X β))
      _ = (8 * Pa.N / (X : ℝ) ^ (2 : ℕ)) * Sfar Pa X β := heq2
  have heq : (8 * Pa.N / (X : ℝ) ^ (2 : ℕ))
        * ((1000 * (1 + Real.log (2 + (Pa.N : ℝ))))
            * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)))
      = 8000 * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)) * Pa.N
          * (1 + Real.log (2 + Pa.N)) / (X : ℝ) ^ (2 : ℕ) := by ring_nf
  calc (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * farMass Pa X d β)
      ≤ (8 * Pa.N / (X : ℝ) ^ (2 : ℕ)) * Sfar Pa X β := hmain
    _ ≤ (8 * Pa.N / (X : ℝ) ^ (2 : ℕ))
          * ((1000 * (1 + Real.log (2 + (Pa.N : ℝ))))
              * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ))) := by
        exact mul_le_mul_of_nonneg_left hSfar (by positivity)
    _ = 8000 * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)) * Pa.N
          * (1 + Real.log (2 + Pa.N)) / (X : ℝ) ^ (2 : ℕ) := heq

end


end

end Work.FIArea6.S16ErrTwo
