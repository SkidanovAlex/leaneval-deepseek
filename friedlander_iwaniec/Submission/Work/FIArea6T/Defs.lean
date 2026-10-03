/-
# `Submission.Work.FIArea6T.Defs` — the τ-removal lane of area 6: vocabulary and API

*FI* (10.4) removes the divisor condition (5.9) `τ(|z|²) ≤ τ` from the coefficient, at
polylogarithmic quality, inside the `D₀`/`T(β)` budget.  This directory (`FIArea6T`) implements
that step in the round-6 vocabulary of `Submission/Work/FITop4/`: the clean coefficient class
`Work.FITop4.IsCleanCoeff6` of *FI* Prop. 10.2 / Lemma 16.2 / Prop. 16.3 (i.e. (5.7)+(5.8) only),
the truncation `Work.FITop4.tauCut` of (4.9)–(4.11), and the contract
`Work.FITop4.TauRemoval6` which says that replacing `β` by `tauCut Pa β` changes the cut form
`Tcut` by at most `N²(log N)^{-19·10^8}`.

The method here is Rankin at power `25` (area 7's A3, `Work.FIArea7.deltaTau_mass_le`) together
with an **L² Schur bound** for the sesquilinear form, replacing *FI*'s Lemma 10.1.  The design is
`Submission/Work/FIArea6/AREA6_CONTRACT_LEAD.md` §3.

## What this module contains

* `TcutBil`: the *sesquilinear* form underlying `Work.FITop4.Tcut` (the same double sum with
  `u z₁ * star (v z₂)` in place of `β z₁ * star (β z₂)`), so that `Tcut Rz cut β = TcutBil Rz cut β β`
  (`Tcut_eq_TcutBil`);
* `tauCompl`, the (5.9)-complement `δ = β − tauCut β`, with its elementary pointwise API;
* the API of the clean coefficient class `Work.FITop4.IsCleanCoeff6`: support, squarefreeness of the
  norm, the pointwise bound `‖β z‖ ≤ τ(|z|²)`, and `exists_mollPair` (the `q, p` of the definition).
-/
import Mathlib
import Submission.Work.FITop4.Areas6e

set_option autoImplicit false

namespace Work.FIArea6T

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. The sesquilinear form underlying `Tcut` -/

/-- **The sesquilinear form of the (10.13) expansion.**  This is `Work.FITop4.Tcut` with
`u z₁ * star (v z₂)` in place of `β z₁ * star (β z₂)`:

`TcutBil Rz cut u v = 2 Σ_{z₁,z₂ ∈ gBox Rz, (z₁,z₂)=1} u z₁ star(v z₂) Σ_{4d ∣ |Δ|, d ≤ |Δ|/4+1}
(φ(d)/d)·cut z₁ z₂ d·(z₂/z₁|d)·logFac6 z₁ z₂`.

It is sesquilinear in `(u,v)`, and `Work.FITop4.Tcut Rz cut β = TcutBil Rz cut β β`.  The
τ-removal of *FI* (10.4) is the expansion of `Tcut (tauCut β)` in this form with
`δ = β − tauCut β`, followed by a Schur bound (`TcutBil_le_polar`) and the two mass bounds
(`cleanCoeff_sq_mass_le`, `cleanTau_mass_le`). -/
def TcutBil (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (u v : GaussianInt → ℂ) : ℂ :=
  2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then
      (u z1 * star (v z2)) *
        ((∑ d ∈ Work.FITop4.Sset z1 z2,
            ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
              * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
     else 0)

/-- `Work.FITop4.Tcut` is the diagonal of `TcutBil`. -/
lemma Tcut_eq_TcutBil (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz cut β = TcutBil Rz cut β β := rfl

/-! ## 2. The (5.9)-complement `δ = β − tauCut β` -/

/-- **The (5.9)-complement.**  `tauCompl Pa β z = β z − tauCut Pa β z`, i.e. `β z` on the points
with `τ(|z|²) > Pa.τ` and `0` elsewhere.  *FI* (10.4) pays exactly the mass of this complement. -/
def tauCompl (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun z => β z - Work.FITop4.tauCut Pa β z

lemma tauCompl_apply (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (z : GaussianInt) :
    tauCompl Pa β z = β z - Work.FITop4.tauCut Pa β z := rfl

/-- On the (5.9)-side, `tauCut` is the identity. -/
lemma tauCut_of_le {Pa : Work.FITop.Params} {β : GaussianInt → ℂ} {z : GaussianInt}
    (h : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ) :
    Work.FITop4.tauCut Pa β z = β z := by
  rw [Work.FITop4.tauCut, if_pos h]

/-- Off the (5.9)-side, `tauCut` vanishes. -/
lemma tauCut_of_not_le {Pa : Work.FITop.Params} {β : GaussianInt → ℂ} {z : GaussianInt}
    (h : ¬ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ) :
    Work.FITop4.tauCut Pa β z = 0 := by
  rw [Work.FITop4.tauCut, if_neg h]

/-- `δ` is `β` times the indicator of the complement of (5.9). -/
lemma tauCompl_eq_mul (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (z : GaussianInt) :
    tauCompl Pa β z
      = β z * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1) := by
  by_cases h : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ
  · rw [tauCompl, tauCut_of_le h, if_pos h, mul_zero]
    ring
  · rw [tauCompl, tauCut_of_not_le h, if_neg h, mul_one, sub_zero]

/-- The δ of (10.4) is exactly the complement indicator, applied to `β`. -/
lemma tauCompl_eq_mul' (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (z : GaussianInt) :
    tauCompl Pa β z
      = β z * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 0 else 1) :=
  tauCompl_eq_mul Pa β z

/-- `tauCut Pa β` is obtained from `β` by deleting the (5.9)-complement. -/
lemma tauCut_eq_sub_tauCompl (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) :
    (fun z => Work.FITop4.tauCut Pa β z) = fun z => β z - tauCompl Pa β z := by
  funext z
  rw [tauCompl]
  ring

/-- `tauCut` never increases the modulus. -/
lemma norm_tauCut_le (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (z : GaussianInt) :
    ‖Work.FITop4.tauCut Pa β z‖ ≤ ‖β z‖ := by
  by_cases h : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ
  · rw [tauCut_of_le h]
  · rw [tauCut_of_not_le h]; simp

/-- `δ` never increases the modulus. -/
lemma norm_tauCompl_le (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (z : GaussianInt) :
    ‖tauCompl Pa β z‖ ≤ ‖β z‖ := by
  rw [tauCompl_eq_mul]
  by_cases h : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ
  · rw [if_pos h, mul_zero]; simp
  · rw [if_neg h, mul_one]

/-- `δ z ≠ 0` forces `β z ≠ 0` (so `δ` inherits the support of `β`). -/
lemma tauCompl_ne_zero_imp {Pa : Work.FITop.Params} {β : GaussianInt → ℂ} {z : GaussianInt}
    (h : tauCompl Pa β z ≠ 0) : β z ≠ 0 := by
  rw [tauCompl_eq_mul] at h
  intro h0
  exact h (by rw [h0, zero_mul])

/-! ## 3. The clean coefficient class of *FI* Prop. 10.2 / Lemma 16.2 / Prop. 16.3 -/

/-- A non-zero clean coefficient lies in the polar box (5.14). -/
theorem IsCleanCoeff6.support {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsCleanCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) : Work.FITop4.InPolarBox Pa φ z := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
      ∧ Work.FITop4.SameClass8 z z0
  · exact hc.1
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- A non-zero clean coefficient is free of small primes (5.8). -/
theorem IsCleanCoeff6.noSmallPrimes {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsCleanCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) : Work.FITop4.NoSmallPrimes Pa z := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
      ∧ Work.FITop4.SameClass8 z z0
  · exact hc.2.1
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- The (5.7) content of a clean coefficient: two points of its support lie in the same class
modulo eight. -/
theorem IsCleanCoeff6.sameClass {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsCleanCoeff6 Pa φ z0 β) {z w : GaussianInt}
    (hz : β z ≠ 0) (hw : β w ≠ 0) : Work.FITop4.SameClass8 z w := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  rw [hβ w] at hw
  by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
      ∧ Work.FITop4.SameClass8 z z0
  · by_cases hd : Work.FITop4.InPolarBox Pa φ w ∧ Work.FITop4.NoSmallPrimes Pa w
        ∧ Work.FITop4.SameClass8 w z0
    · rw [Work.FITop4.SameClass8] at *
      rw [hc.2.2, hd.2.2]
    · rw [if_neg hd] at hw; exact absurd rfl hw
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- A non-zero clean coefficient point has squarefree norm: the Möbius factor of (5.13). -/
theorem IsCleanCoeff6.squarefree_gnorm {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsCleanCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) : Squarefree (Work.FIPlan.gnorm z) := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
      ∧ Work.FITop4.SameClass8 z z0
  · have hmu : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ) ≠ 0 := by
      intro h0
      exact hz (by rw [if_pos hc, h0, mul_zero, zero_mul])
    exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp fun h0 => hmu (by rw [h0]; simp)
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- **The pointwise bound of a clean coefficient**: `‖β z‖ ≤ τ(|z|²)`.  This is the only size
information the §16 machinery uses about `β`; it holds by
`|q| ≤ 1`, `|p| ≤ 1`, `|μ| ≤ 1` and `|γ(|z|²;C)| ≤ τ(|z|²)`. -/
theorem IsCleanCoeff6.norm_le_tau {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsCleanCoeff6 Pa φ z0 β) (z : GaussianInt) :
    ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
  obtain ⟨q, p, -, -, hq0, hq1, -, -, hp0, hp1, -, -, hβdef⟩ := h
  rw [hβdef z]
  by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
      ∧ Work.FITop4.SameClass8 z z0
  · rw [if_pos hc]
    have h1 : ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hq0 _) (hp0 _))]
      calc q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≤ 1 * 1 :=
            mul_le_mul (hq1 _) (hp1 _) (hp0 _) (by norm_num)
        _ = 1 := by ring
    have h2 : ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖ ≤ 1 :=
      Work.FITop3.norm_moebius_le_one _
    have h3 : ‖(Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖
        ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.FITop3.abs_gammaTrunc_le Pa.C _
    calc ‖((q _ * p _ : ℝ) : ℂ) * (ArithmeticFunction.moebius _ : ℂ)
            * (Work.FIPlan.gammaTrunc _ _ : ℂ)‖
        = ‖((q _ * p _ : ℝ) : ℂ)‖ * ‖(ArithmeticFunction.moebius _ : ℂ)‖
            * ‖(Work.FIPlan.gammaTrunc _ _ : ℂ)‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _)
            (by positivity)
      _ = (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by ring
  · rw [if_neg hc]; simp

/-- `tauCut Pa β` of a clean coefficient, when (5.9) holds vacuously on the box, is `β` itself. -/
theorem tauCut_eq_self_of_forall {Pa : Work.FITop.Params} {β : GaussianInt → ℂ}
    (h : ∀ z, β z ≠ 0 → (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ) :
    (fun z => Work.FITop4.tauCut Pa β z) = β := by
  funext z
  by_cases hz : β z = 0
  · rw [hz]
    by_cases hc : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ
    · rw [tauCut_of_le hc, hz]
    · rw [tauCut_of_not_le hc]
  · rw [tauCut_of_le (h z hz)]

end

end Work.FIArea6T
