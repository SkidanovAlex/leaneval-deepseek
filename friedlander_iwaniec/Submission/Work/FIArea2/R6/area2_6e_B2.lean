/-
# `FIArea2/R6/area2_6e_B2` — the (7.10)/(10.4) replacement error, via the τ-weighted Lemma 10.1

This file proves the "B" half of `Work.FIArea2.area2_6e` (`= Work.FITop4.Area2_6b`):
the difference between the *exact* main term `D0ex` (the (9.11) sum with the exact (6.13) kernel)
and the *approximated* main term `Defs6.D0` (built on the (7.10) main term `Fhat · logFac6`) is

  `‖D₀^exact − D₀‖ ≤ Cb·ϑ⁻¹τ²N²(log N)^{bFun η} + C3·(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}`,

i.e. it is absorbed by the *first* term of *FI* (9.10) for the *lower*-cutoff part and by the
(10.4)/(10.10) error for the rest.

## Route

1. `R6/area2_6e_B`'s `norm_D0ex_sub_D0_le` reduces `‖D₀^exact − D₀‖` to the pair sum of the
   per-pair (7.10) errors; `pair_error_le` below bounds the per-pair error by
   `4·τ₃(|Δ|)·N^{-1/2}·Amax` with `Amax = Ka√Mθ²log N + Kb(log N)/√M` (the (7.10) bracket).
   Hence

     `‖D₀^exact − D₀‖ ≤ 4N^{-1/2}·Amax·T`,   `T := Σ_{(z₁,z₂) coprime} ‖β_{z₁}‖‖β_{z₂}‖τ₃(|Δ|)`.

2. The single analytic input — `WProp` below, *FI* Lemma 10.1 with the `τ(|z|²)`-weights at the
   exponent `θ³` instead of `θ⁴` — bounds the `τ(|z|²)τ(|z'|²)`-weighted pair sum by
   `C·θ³N²(log N)^{2^19}`, hence (the weights being `≥ 1`) `T ≤ Cw·θ³N²(log N)^{2^19}`.

3. The arithmetic: the `Ka`-piece of `Amax` is dominated by the (10.4) error,
   `4Ka Cw θ⁵M^{1/2}N^{3/2}(log N)^{2^20} ≤ C3(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}`
   (because `θ ≤ τ⁻¹+θ`), and the `Kb`-piece by the first term of (9.10),
   `4Kb Cw θ³N^{3/2}M^{-1/2}(log N)^{2^20} ≤ Cbϑ⁻¹τ²N²(log N)^{bFun η}`
   (because `(NM)^{-1/2} ≤ ϑ^{-1/2}x^{-1/2}`, `θ³ϑ^{1/2} ≤ (log x)^{-3·2^20}` and `τ,ϑ⁻¹ ≥ 1`).

## Why the exponent `θ³` (and not the paper's `θ⁴`)

The paper's Lemma 10.1 is stated with the *weights* `τ(|z₁|²)τ(|z₂|²)` present in `Y(β)`; the
`θ⁴` shape holds for the coefficient (i.e. `‖β_{z}‖ ≤ 1`), and provably fails for the
`τ`-weights in the frozen `Params` (`R6/NOTES_notYProp.md`: `A'` is unbounded below-above, so
`θ²N ≈ 1` is admissible, and then a single pair with `τ₃(|Δ|) ≫ (log N)^{2^19}` refutes `θ⁴`).
With `θ³` the pair sum has `θ³N² = (θ√N)³√N`, and since the polar box is contained in a disc of
radius `5θ√N` the box is empty unless `θ√N ≳ 1` — which is exactly the `√N` of room the max-order
bound `τ₃(n) ≤ exp(1.1 log n/loglog n)` needs.  This is the shape `WProp` records.
-/
import Mathlib
import Submission.Work.FIArea2.R6.Inputs6
import Submission.Work.FIArea2.R6.area2_6e_B
import Submission.Work.FIArea4.A6Ener3_le

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **`WProp`** — *FI* Lemma 10.1 for the round-6 coefficient family, with the (10.6) weights
`τ(|z₁|²)τ(|z₂|²)` and at the exponent `θ³`:

  `Σ_{(z₁,z₂)=1} ‖β_{z₁}‖‖β_{z₂}‖τ(|z₁|²)τ(|z₂|²)τ₃(|Δ(z₁,z₂)|) ≤ C·θ³N²(log N)^{2^19}`.

(`θ⁴` would be false in the frozen `Params`, see the module docstring; `θ³` is what the
per-pair (7.10) route consumes.) -/
def WProp : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          copInd z1 z2 * (‖β z1‖ * ‖β z2‖
            * (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
            * (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
            * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)))
        ≤ C * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))

/-- `Ka Cf > 0`. -/
theorem Ka_pos (Cf : ℝ) (hCf : 0 < Cf) : 0 < Ka Cf := by
  rw [Ka]
  have h1 : (0 : ℝ) < Cder6 + 1 := by linarith [Cder6_pos]
  have h2 : (0 : ℝ) < Cf + 1 := by linarith
  positivity

/-- `Kb Cf > 0`. -/
theorem Kb_pos (Cf : ℝ) (hCf : 0 < Cf) : 0 < Kb Cf := by
  rw [Kb]
  have h1 : (0 : ℝ) < Cder6 + 1 := by linarith [Cder6_pos]
  positivity

/-- **The per-pair (7.10) replacement bound.**  On a coprime pair of the support of a round-6
coefficient, the difference of the two main-term kernels is at most
`4τ₃(|Δ|)N^{-1/2}Amax`. -/
theorem pair_error_le (Cf : ℝ) (hCf : 0 < Cf) (hFP : FintBound Cf)
    (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f)
    (hx : 10000 ≤ (Pa.x : ℝ)) {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 z2 : GaussianInt}
    (h1 : β z1 ≠ 0) (h2 : β z2 ≠ 0) (hcop : Work.FIPlan.GaussCoprime z1 z2) :
    |C0ex (majF Pa f hf) z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2|
      ≤ 4 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
        * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf) := by
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hbox1 := Work.FITop4.IsBetaCoeff6.support hβ h1
  have hbox2 := Work.FITop4.IsBetaCoeff6.support hβ h2
  have hodd1 := InPolarBox.odd_gnorm6 hbox1
  have hprim1 := Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
    (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h1) hodd1
  have hprim2 := Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
    (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h2) (InPolarBox.odd_gnorm6 hbox2)
  have hn1 : 2 ≤ Work.FIPlan.gnorm z1 := by
    have hgt : (1 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast Pa.hN1) (InPolarBox.norm_bounds6 hbox1).1
    have hgt' : (1 : ℕ) < Work.FIPlan.gnorm z1 := by exact_mod_cast hgt
    omega
  have hDelta : Work.FIPlan.Delta z1 z2 ≠ 0 :=
    delta_ne_zero_of_coprime hcop hprim1 hprim2 hn1
  have hD : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
    simpa [Work.FIPlan.absDelta] using Int.natAbs_ne_zero.mpr hDelta
  have hbr := bracket_le Cf hCf hFP Pa f hf hx hbox1 hbox2 hD
  have halg := C0ex_sub_C0_eq Pa f hf z1 z2
  have hN2gn : Pa.N ^ (2 : ℕ) ≤ ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
    rw [Work.FIArea4.gnorm_mul]
    push_cast
    have h3 := (InPolarBox.norm_bounds6 hbox1).1
    have h4 := (InPolarBox.norm_bounds6 hbox2).1
    nlinarith [h3, h4, hN1]
  have hgn_ub : (((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) ^ (-(1 : ℝ) / 4)
      ≤ Pa.N ^ (-(1 : ℝ) / 2) := by
    have hposN : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
    have h1 : (((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) ^ (-(1 : ℝ) / 4)
        ≤ (Pa.N ^ (2 : ℕ)) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hN2gn (by norm_num)
    have h2 : (Pa.N ^ (2 : ℕ)) ^ (-(1 : ℝ) / 4) = Pa.N ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hposN)]
      norm_num
    rwa [h2] at h1
  have hG0 := G0_abs_le6 hβ h1 h2 hcop
  have htau : 2 * (1 + ((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ))
      ≤ 4 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) := by
    have h := Work.FIArea3.one_add_tau_le_two_tau3 (Work.FIPlan.absDelta z1 z2)
    have h' : (1 + (Work.FIPlan.absDelta z1 z2).divisors.card : ℕ)
        ≤ 2 * tau3 (Work.FIPlan.absDelta z1 z2) := h
    have h'' : ((1 + (Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)
        ≤ ((2 * tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) := by
      exact_mod_cast h'
    push_cast at h''
    linarith [h'']
  have hA0 : (0 : ℝ) ≤ Amax Pa (Ka Cf) (Kb Cf) := by
    rw [Amax]
    have hK1 : (0 : ℝ) ≤ Ka Cf := le_of_lt (Ka_pos Cf hCf)
    have hK2 : (0 : ℝ) ≤ Kb Cf := le_of_lt (Kb_pos Cf hCf)
    have hs : (0 : ℝ) ≤ Real.sqrt Pa.M := Real.sqrt_nonneg _
    have hθ : (0 : ℝ) ≤ Pa.θ ^ 2 := sq_nonneg _
    have h0 : (0 : ℝ) ≤ Real.log Pa.N := le_trans zero_le_one (one_le_log_N Pa hx)
    have h1 : (0 : ℝ) ≤ Ka Cf * Real.sqrt Pa.M * Pa.θ ^ 2 * Real.log Pa.N := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hK1 hs) hθ) h0
      linarith [this]
    have h2 : (0 : ℝ) ≤ Kb Cf * Real.log Pa.N / Real.sqrt Pa.M :=
      div_nonneg (mul_nonneg hK2 h0) hs
    linarith
  rw [halg, abs_mul, abs_mul]
  have h1' : |((((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) ^ (-(1 : ℝ) / 4))|
      ≤ Pa.N ^ (-(1 : ℝ) / 2) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact hgn_ub
  have h2' : |Work.FITop4.G0 z1 z2|
      ≤ 4 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) := by
    linarith [hG0, htau]
  have h4' : (0 : ℝ) ≤ Pa.N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  calc |((((Work.FIPlan.gnorm (z1 * z2) : ℕ)) : ℝ) ^ (-(1 : ℝ) / 4))|
        * |Work.FITop4.G0 z1 z2|
        * |(Work.FIArea2.Fint (majF Pa f hf) (Work.FIArea2.gamOf z1 z2) 0 0).re
            - (Work.FITop3.Fhat Pa f) * Work.FITop4.logFac6 z1 z2|
      ≤ Pa.N ^ (-(1 : ℝ) / 2)
        * (4 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ))
        * Amax Pa (Ka Cf) (Kb Cf) := by
        refine mul_le_mul (mul_le_mul h1' h2' (abs_nonneg _) h4') hbr (abs_nonneg _) ?_
        positivity
    _ = 4 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
        * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf) := by ring


/-! ## Arithmetic helpers for the case analysis of `Amax` -/

lemma four_le_bFun (η : ℝ) : 4 ≤ Work.FITop4.bFun η := by
  rw [Work.FITop4.bFun]
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 1) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  linarith

lemma theta_pow3_le (Pa : Work.FITop.Params) :
    Pa.θ ^ (3 : ℕ) ≤ (Real.log (Pa.x : ℝ)) ^ (-(3 * (2 : ℝ) ^ (20 : ℕ))) := by
  have hx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := one_le_log_x6 Pa
  have hx0 : (0 : ℝ) < Real.log (Pa.x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hA' : 2 * Pa.A + (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := Pa.hA'
  have hstep : Pa.θ ^ (3 : ℕ) = (Real.log (Pa.x : ℝ)) ^ (-3 * Pa.A') := by
    rw [Pa.hθ, ← Real.rpow_natCast ((Real.log (Pa.x : ℝ)) ^ (-Pa.A')) 3]
    rw [← Real.rpow_mul (le_of_lt hx0) (-Pa.A') ((3 : ℕ) : ℝ)]
    ring_nf
  rw [hstep]
  apply Real.rpow_le_rpow_of_exponent_le hx1
  linarith [Pa.hA]

lemma log_pow_le (Pa : Work.FITop.Params) (hx : 10000 ≤ (Pa.x : ℝ)) :
    (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
      ≤ (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
        * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)) := by
  have hlogN1 : 1 ≤ Real.log Pa.N := one_le_log_N Pa hx
  have hlogN0 : 0 ≤ Real.log Pa.N := le_trans zero_le_one hlogN1
  have hlogx1 : 1 ≤ Real.log (Pa.x : ℝ) := one_le_log_x6 Pa
  have hNx : Pa.N ≤ (Pa.x : ℝ) := by
    have h1 : Pa.N * Pa.N ≤ Pa.M * Pa.N :=
      mul_le_mul_of_nonneg_right Pa.hMge (by linarith [Pa.hN1] : (0 : ℝ) ≤ Pa.N)
    have h2 : Pa.M * Pa.N ≤ (Pa.x : ℝ) := Pa.hMNx
    have h3 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
    nlinarith [h1, h2, h3]
  have hlogNx : Real.log Pa.N ≤ Real.log (Pa.x : ℝ) :=
    Real.log_le_log (by linarith [Pa.hN1] : (0 : ℝ) < Pa.N) hNx
  have hb0 : 0 ≤ Work.FITop4.bFun Pa.η := le_trans (by norm_num) (four_le_bFun Pa.η)
  have h1 : (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
      ≤ (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) :=
    pow_le_pow_right₀ hlogN1 (by norm_num)
  have h2 : (1 : ℝ) ≤ (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) :=
    Real.one_le_rpow hlogN1 hb0
  have h3 : (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))
      ≤ (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)) :=
    pow_le_pow_left₀ hlogN0 hlogNx _
  have h4 : (0 : ℝ) ≤ (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := pow_nonneg hlogN0 _
  calc (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
      ≤ (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := h1
    _ = 1 * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by ring
    _ ≤ (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
          * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) :=
        mul_le_mul_of_nonneg_right h2 h4
    _ ≤ (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
          * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hlogN0 _)

lemma theta_cube_mul_le (Pa : Work.FITop.Params) :
    Pa.θ ^ (3 : ℕ) * (Pa.M * Pa.N) ^ (-(1 : ℝ) / 2)
        * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)) ≤ 1 := by
  have hx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := one_le_log_x6 Pa
  have hx0 : (0 : ℝ) < Real.log (Pa.x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hθ3 := theta_pow3_le Pa
  have hMN1 : (1 : ℝ) ≤ Pa.M * Pa.N := by
    have h1 : (1 : ℝ) ≤ Pa.M := Pa.hM1
    have h2 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
    nlinarith
  have hNM : (Pa.M * Pa.N) ^ (-(1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hMN1 (by norm_num)
  have hL0 : (0 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)) :=
    pow_nonneg (le_of_lt hx0) _
  have hkey : (Real.log (Pa.x : ℝ)) ^ (-(3 * (2 : ℝ) ^ (20 : ℕ)))
      * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)) ≤ 1 := by
    rw [← Real.rpow_natCast (Real.log (Pa.x : ℝ)) ((2 : ℕ) ^ (20 : ℕ))]
    rw [← Real.rpow_add hx0]
    have he : -(3 * (2 : ℝ) ^ (20 : ℕ)) + (((2 : ℕ) ^ (20 : ℕ) : ℕ) : ℝ)
        = -(2 * (2 : ℝ) ^ (20 : ℕ)) := by push_cast; ring
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  calc Pa.θ ^ (3 : ℕ) * (Pa.M * Pa.N) ^ (-(1 : ℝ) / 2)
        * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ))
      ≤ (Real.log (Pa.x : ℝ)) ^ (-(3 * (2 : ℝ) ^ (20 : ℕ))) * 1
          * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)) := by
        apply mul_le_mul_of_nonneg_right _ hL0
        exact mul_le_mul hθ3 hNM (Real.rpow_nonneg (le_trans zero_le_one hMN1) _)
          (Real.rpow_nonneg (le_of_lt hx0) _)
    _ = (Real.log (Pa.x : ℝ)) ^ (-(3 * (2 : ℝ) ^ (20 : ℕ)))
          * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)) := by ring
    _ ≤ 1 := hkey


/-- `(Real.sqrt M)⁻¹ = M^{-1/2}`. -/
lemma rpow_neg_half_inv_sqrt (M : ℝ) (hM : 0 < M) :
    (Real.sqrt M)⁻¹ = M ^ (-(1 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hM.le]
  norm_num

/-- `N^{-1/2}·N² = N^{3/2}`. -/
lemma rpow_neg_half_mul_sq (N : ℝ) (hN : 0 < N) :
    N ^ (-(1 : ℝ) / 2) * N ^ (2 : ℕ) = N ^ ((3 : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hN]
  norm_num

/-- `N^{3/2}·M^{-1/2} = N²·(NM)^{-1/2}`. -/
lemma rpow32_mul_neg_half (M N : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N ^ ((3 : ℝ) / 2) * M ^ (-(1 : ℝ) / 2) = N ^ (2 : ℕ) * (M * N) ^ (-(1 : ℝ) / 2) := by
  rw [Real.mul_rpow hM.le hN.le]
  have h1 : N ^ ((3 : ℝ) / 2) = N ^ (2 : ℕ) * N ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_add hN]
    norm_num
  rw [h1]
  ring

set_option maxHeartbeats 1000000

theorem area2_6e_B2 (hW : WProp) (hF : FintProp) :
    ∃ Cb C3 x0 : ℝ, 0 < Cb ∧ 0 < C3 ∧ 0 < x0 ∧
      ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
      ∀ (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f) (φ : ℝ) (z0 : GaussianInt)
        (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        ‖((D0ex (Work.FITop.radN Pa) (majF Pa f hf) β : ℝ) : ℂ)
            - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖
          ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ (2 : ℕ)
              * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
            + C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
                * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by
  obtain ⟨Cf, hCfpos, hFP⟩ := hF
  obtain ⟨Cw, hCwpos, hWb⟩ := hW
  have hKa : 0 < Ka Cf := Ka_pos Cf hCfpos
  have hKb : 0 < Kb Cf := Kb_pos Cf hCfpos
  refine ⟨4 * Kb Cf * Cw, 4 * Ka Cf * Cw, 10000,
    mul_pos (mul_pos (by norm_num) hKb) hCwpos,
    mul_pos (mul_pos (by norm_num) hKa) hCwpos, by norm_num, ?_⟩
  intro Pa hx f hf φ z0 β hβ
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  have hMpos : (0 : ℝ) < Pa.M := lt_of_lt_of_le zero_lt_one Pa.hM1
  have hlogN1 : 1 ≤ Real.log Pa.N := one_le_log_N Pa hx
  have hlogN0 : 0 ≤ Real.log Pa.N := le_trans zero_le_one hlogN1
  have hτ1 : (1 : ℝ) ≤ Pa.τ :=
    le_trans (Real.one_le_rpow (one_le_log_x6 Pa) (by linarith [Pa.hA])) Pa.hτ1
  have hτ0 : 0 < Pa.τ := lt_of_lt_of_le zero_lt_one hτ1
  have hτinv0 : 0 ≤ Pa.τ⁻¹ := inv_nonneg.mpr (le_of_lt hτ0)
  have hϑ0 : 0 ≤ Pa.ϑ := le_of_lt Pa.hϑ0
  have hϑinv0 : 0 ≤ Pa.ϑ⁻¹ := inv_nonneg.mpr hϑ0
  have hθ0 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
  set Tsum : ℝ := ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
      copInd z1 z2 * (‖β z1‖ * ‖β z2‖ * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ))
      with hTsumdef
  have hWle := hWb Pa φ z0 β hβ
  have hWT : Tsum ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          copInd z1 z2 * (‖β z1‖ * ‖β z2‖
            * (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
            * (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
            * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)) := by
    rw [hTsumdef]
    refine Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => ?_))
    have hc0 : (0 : ℝ) ≤ copInd z1 z2 := copInd_nonneg z1 z2
    by_cases hb1 : β z1 = 0
    · rw [hb1, norm_zero]; simp
    by_cases hb2 : β z2 = 0
    · rw [hb2, norm_zero]; simp
    have hd1 : (1 : ℝ) ≤ (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ) := by
      have hb := Work.FITop4.IsBetaCoeff6.support hβ hb1
      have hgt : (1 : ℕ) < Work.FIPlan.gnorm z1 := by
        have h : (1 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := lt_of_le_of_lt hN1 hb.2.1
        exact_mod_cast h
      have hm : 1 ∈ (Work.FIPlan.gnorm z1).divisors :=
        Nat.one_mem_divisors.mpr (by omega)
      have hcard : 1 ≤ (Work.FIPlan.gnorm z1).divisors.card := Finset.card_pos.mpr ⟨1, hm⟩
      exact_mod_cast hcard
    have hd2 : (1 : ℝ) ≤ (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ) := by
      have hb := Work.FITop4.IsBetaCoeff6.support hβ hb2
      have hgt : (1 : ℕ) < Work.FIPlan.gnorm z2 := by
        have h : (1 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := lt_of_le_of_lt hN1 hb.2.1
        exact_mod_cast h
      have hm : 1 ∈ (Work.FIPlan.gnorm z2).divisors :=
        Nat.one_mem_divisors.mpr (by omega)
      have hcard : 1 ≤ (Work.FIPlan.gnorm z2).divisors.card := Finset.card_pos.mpr ⟨1, hm⟩
      exact_mod_cast hcard
    have ht3 : (0 : ℝ) ≤ ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) := by positivity
    have hb12 : (0 : ℝ) ≤ ‖β z1‖ * ‖β z2‖ := by positivity
    have h1 : (1 : ℝ) ≤ (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
        * (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ) := by
      have h := mul_le_mul hd1 hd2 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
      simpa using h
    refine mul_le_mul_of_nonneg_left ?_ hc0
    calc ‖β z1‖ * ‖β z2‖ * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
        = ‖β z1‖ * ‖β z2‖ * (1 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)) := by ring
      _ ≤ ‖β z1‖ * ‖β z2‖ * ((((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
            * (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
            * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hb12
          exact mul_le_mul_of_nonneg_right h1 ht3
      _ = ‖β z1‖ * ‖β z2‖ * (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
            * (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
            * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) := by ring
  have hTle : Tsum ≤ Cw * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) :=
    le_trans hWT hWle
  have hpairpt : ∀ z1 z2 : GaussianInt,
      (if Work.FIPlan.GaussCoprime z1 z2 then
        ‖β z1‖ * ‖β z2‖ * |C0ex (majF Pa f hf) z1 z2
          - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2|
      else 0)
      ≤ (if Work.FIPlan.GaussCoprime z1 z2 then
        ‖β z1‖ * ‖β z2‖ * (4 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
          * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf))
      else 0) := by
    intro z1 z2
    by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hcop, if_pos hcop]
      by_cases hb1 : β z1 = 0
      · rw [hb1, norm_zero]; simp
      by_cases hb2 : β z2 = 0
      · rw [hb2, norm_zero]; simp
      have hpe := pair_error_le Cf hCfpos hFP Pa f hf hx hβ hb1 hb2 hcop
      exact mul_le_mul_of_nonneg_left hpe (by positivity)
    · rw [if_neg hcop, if_neg hcop]
  have hsum : ‖((D0ex (Work.FITop.radN Pa) (majF Pa f hf) β : ℝ) : ℂ)
        - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖
      ≤ (4 * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf)) * Tsum := by
    refine le_trans (norm_D0ex_sub_D0_le Pa f hf β) ?_
    calc ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if Work.FIPlan.GaussCoprime z1 z2 then
              ‖β z1‖ * ‖β z2‖ * |C0ex (majF Pa f hf) z1 z2
                - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2|
            else 0)
        ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if Work.FIPlan.GaussCoprime z1 z2 then
              ‖β z1‖ * ‖β z2‖ * (4 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
                * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf))
            else 0) :=
          Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => hpairpt z1 z2))
      _ = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            copInd z1 z2 * (‖β z1‖ * ‖β z2‖ * (4 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
              * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf))) := by
          refine Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => ?_))
          rw [copInd]
          by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [hc]
      _ = (4 * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf)) * Tsum := by
          rw [hTsumdef]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z1 _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z2 _ => ?_)
          ring
  have hAmaxsplit : 4 * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf) * Tsum
      = (4 * Ka Cf * Real.sqrt Pa.M * Pa.θ ^ (2 : ℕ) * Real.log Pa.N
            * Pa.N ^ (-(1 : ℝ) / 2)) * Tsum
        + (4 * Kb Cf * Real.log Pa.N / Real.sqrt Pa.M
            * Pa.N ^ (-(1 : ℝ) / 2)) * Tsum := by
    rw [Amax]; ring
  have hL1 : (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
      ≤ (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)) :=
    log_pow_le Pa hx
  have hRHS0 : (0 : ℝ) ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
      * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by
    have h1 : (0 : ℝ) ≤ Pa.τ⁻¹ := inv_nonneg.mpr (le_of_lt hτ0)
    have h2 : (0 : ℝ) ≤ Pa.M ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hMpos) _
    have h3 : (0 : ℝ) ≤ Pa.N ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hNpos) _
    have h4 : (0 : ℝ) ≤ (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := pow_nonneg hlogN0 _
    positivity
  have hIa : (4 * Ka Cf * Real.sqrt Pa.M * Pa.θ ^ (2 : ℕ) * Real.log Pa.N
        * Pa.N ^ (-(1 : ℝ) / 2)) * Tsum
      ≤ (4 * Ka Cf * Cw) * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
          * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) := by
    have hcoef : (0 : ℝ) ≤ 4 * Ka Cf * Real.sqrt Pa.M * Pa.θ ^ (2 : ℕ) * Real.log Pa.N
        * Pa.N ^ (-(1 : ℝ) / 2) := by
      have h1 : (0 : ℝ) ≤ Ka Cf := le_of_lt hKa
      have h2 : (0 : ℝ) ≤ Real.sqrt Pa.M := Real.sqrt_nonneg _
      have h3 : (0 : ℝ) ≤ Pa.θ ^ (2 : ℕ) := by positivity
      have h4 : (0 : ℝ) ≤ Pa.N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hNpos) _
      positivity
    refine le_trans (mul_le_mul_of_nonneg_left hTle hcoef) ?_
    have hlog1 : (Real.log Pa.N) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))
        = (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1) := (pow_succ' _ _).symm
    have hcore : Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
        ≤ (Pa.τ⁻¹ + Pa.θ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by
      calc Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
          ≤ Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlogN1 (by norm_num)) hθ0
        _ ≤ (Pa.τ⁻¹ + Pa.θ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) :=
            mul_le_mul_of_nonneg_right (by linarith [hτinv0]) (pow_nonneg hlogN0 _)
    have hfac : Pa.M ^ ((1 : ℝ) / 2) * Pa.θ ^ (5 : ℕ) * Pa.N ^ ((3 : ℝ) / 2)
          * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
        ≤ (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
          * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by
      have heq : Pa.M ^ ((1 : ℝ) / 2) * Pa.θ ^ (5 : ℕ) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
          = (Pa.M ^ ((1 : ℝ) / 2) * Pa.θ ^ (4 : ℕ) * Pa.N ^ ((3 : ℝ) / 2))
            * (Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)) := by ring
      rw [heq]
      calc (Pa.M ^ ((1 : ℝ) / 2) * Pa.θ ^ (4 : ℕ) * Pa.N ^ ((3 : ℝ) / 2))
              * (Pa.θ * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1))
          ≤ (Pa.M ^ ((1 : ℝ) / 2) * Pa.θ ^ (4 : ℕ) * Pa.N ^ ((3 : ℝ) / 2))
              * ((Pa.τ⁻¹ + Pa.θ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) :=
            mul_le_mul_of_nonneg_left hcore (by positivity)
        _ = (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
              * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by ring
    calc (4 * Ka Cf * Real.sqrt Pa.M * Pa.θ ^ (2 : ℕ) * Real.log Pa.N * Pa.N ^ (-(1 : ℝ) / 2))
          * (Cw * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))
        = (4 * Ka Cf * Cw) * (Real.sqrt Pa.M * Pa.θ ^ (5 : ℕ)
            * (Pa.N ^ (-(1 : ℝ) / 2) * Pa.N ^ (2 : ℕ))
            * (Real.log Pa.N * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))) := by ring
      _ = (4 * Ka Cf * Cw) * (Pa.M ^ ((1 : ℝ) / 2) * Pa.θ ^ (5 : ℕ) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))) := by
          rw [Real.sqrt_eq_rpow, rpow_neg_half_mul_sq Pa.N hNpos]
      _ = (4 * Ka Cf * Cw) * (Pa.M ^ ((1 : ℝ) / 2) * Pa.θ ^ (5 : ℕ) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)) := by rw [hlog1]
      _ ≤ (4 * Ka Cf * Cw) * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
            * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
  have hIb : (4 * Kb Cf * Real.log Pa.N / Real.sqrt Pa.M * Pa.N ^ (-(1 : ℝ) / 2)) * Tsum
      ≤ (4 * Kb Cf * Cw) * (Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)) := by
    have hcoef : (0 : ℝ) ≤ 4 * Kb Cf * Real.log Pa.N / Real.sqrt Pa.M * Pa.N ^ (-(1 : ℝ) / 2) := by
      have h1 : (0 : ℝ) ≤ Kb Cf := le_of_lt hKb
      have h2 : (0 : ℝ) ≤ Real.log Pa.N := hlogN0
      have h3 : (0 : ℝ) ≤ (Real.sqrt Pa.M)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have h4 : (0 : ℝ) ≤ Pa.N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hNpos) _
      positivity
    refine le_trans (mul_le_mul_of_nonneg_left hTle hcoef) ?_
    have hlog1 : (Real.log Pa.N) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))
        = (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1) := (pow_succ' _ _).symm
    have hkey := theta_cube_mul_le Pa
    have hNM3 : Pa.N ^ ((3 : ℝ) / 2) * Pa.M ^ (-(1 : ℝ) / 2)
        = Pa.N ^ (2 : ℕ) * (Pa.M * Pa.N) ^ (-(1 : ℝ) / 2) :=
      rpow32_mul_neg_half Pa.M Pa.N hMpos hNpos
    have hϑinv1 : (1 : ℝ) ≤ Pa.ϑ⁻¹ := by
      rw [one_le_inv₀ Pa.hϑ0]; exact vartheta_le_one6 Pa
    have hτ2 : (1 : ℝ) ≤ Pa.τ ^ (2 : ℕ) := one_le_pow₀ hτ1
    have hL0 : (0 : ℝ) ≤ (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) :=
      Real.rpow_nonneg hlogN0 _
    calc (4 * Kb Cf * Real.log Pa.N / Real.sqrt Pa.M * Pa.N ^ (-(1 : ℝ) / 2))
          * (Cw * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))
        = (4 * Kb Cf * Cw) * (Pa.θ ^ (3 : ℕ) * (Pa.N ^ (-(1 : ℝ) / 2) * Pa.N ^ (2 : ℕ))
            * (Real.log Pa.N * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) * (Real.sqrt Pa.M)⁻¹) := by
          ring
      _ = (4 * Kb Cf * Cw) * (Pa.θ ^ (3 : ℕ) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))
            * Pa.M ^ (-(1 : ℝ) / 2)) := by
          rw [rpow_neg_half_mul_sq Pa.N hNpos, rpow_neg_half_inv_sqrt Pa.M hMpos]
      _ = (4 * Kb Cf * Cw) * (Pa.θ ^ (3 : ℕ) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
            * Pa.M ^ (-(1 : ℝ) / 2)) := by rw [hlog1]
      _ ≤ (4 * Kb Cf * Cw) * (Pa.θ ^ (3 : ℕ) * Pa.N ^ ((3 : ℝ) / 2)
            * ((Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)))
            * Pa.M ^ (-(1 : ℝ) / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have heq : Pa.θ ^ (3 : ℕ) * Pa.N ^ ((3 : ℝ) / 2)
                * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1) * Pa.M ^ (-(1 : ℝ) / 2)
              = (Pa.θ ^ (3 : ℕ) * Pa.N ^ ((3 : ℝ) / 2) * Pa.M ^ (-(1 : ℝ) / 2))
                * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1) := by ring
          rw [heq]
          calc (Pa.θ ^ (3 : ℕ) * Pa.N ^ ((3 : ℝ) / 2) * Pa.M ^ (-(1 : ℝ) / 2))
                * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ) + 1)
              ≤ (Pa.θ ^ (3 : ℕ) * Pa.N ^ ((3 : ℝ) / 2) * Pa.M ^ (-(1 : ℝ) / 2))
                * ((Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
                  * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ))) :=
                mul_le_mul_of_nonneg_left hL1 (by positivity)
            _ = Pa.θ ^ (3 : ℕ) * Pa.N ^ ((3 : ℝ) / 2)
                * ((Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
                  * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)))
                * Pa.M ^ (-(1 : ℝ) / 2) := by ring
      _ = (4 * Kb Cf * Cw) * (Pa.θ ^ (3 : ℕ)
            * (Pa.N ^ ((3 : ℝ) / 2) * Pa.M ^ (-(1 : ℝ) / 2))
            * ((Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
              * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ)))) := by ring
      _ = (4 * Kb Cf * Cw) * ((Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
            * (Pa.N ^ (2 : ℕ) * (Pa.θ ^ (3 : ℕ) * (Pa.M * Pa.N) ^ (-(1 : ℝ) / 2)
              * (Real.log (Pa.x : ℝ)) ^ ((2 : ℕ) ^ (20 : ℕ))))) := by
          rw [hNM3]
          ring
      _ ≤ (4 * Kb Cf * Cw) * ((Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
            * (Pa.N ^ (2 : ℕ) * 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (a := (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η))
            (mul_le_mul_of_nonneg_left (a := Pa.N ^ (2 : ℕ)) hkey (by positivity))
            (Real.rpow_nonneg hlogN0 _)
      _ ≤ (4 * Kb Cf * Cw) * (Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hone : (1 : ℝ) ≤ Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) := by
            have h := mul_le_mul hϑinv1 hτ2 (by norm_num) hϑinv0
            linarith
          calc (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) * (Pa.N ^ (2 : ℕ) * 1)
              ≤ (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
                * (Pa.N ^ (2 : ℕ) * (Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (a := Pa.N ^ (2 : ℕ)) hone (by positivity)) hL0
            _ = Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ (2 : ℕ)
                * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by ring
  calc ‖((D0ex (Work.FITop.radN Pa) (majF Pa f hf) β : ℝ) : ℂ)
        - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖
      ≤ (4 * Pa.N ^ (-(1 : ℝ) / 2) * Amax Pa (Ka Cf) (Kb Cf)) * Tsum := hsum
    _ = (4 * Ka Cf * Real.sqrt Pa.M * Pa.θ ^ (2 : ℕ) * Real.log Pa.N
            * Pa.N ^ (-(1 : ℝ) / 2)) * Tsum
        + (4 * Kb Cf * Real.log Pa.N / Real.sqrt Pa.M * Pa.N ^ (-(1 : ℝ) / 2)) * Tsum := hAmaxsplit
    _ ≤ (4 * Ka Cf * Cw) * ((Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
          * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)))
        + (4 * Kb Cf * Cw) * (Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)) := add_le_add hIa hIb
    _ = (4 * Kb Cf * Cw) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η)
        + (4 * Ka Cf * Cw) * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
          * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by ring


end

end Work.FIArea2.R6
