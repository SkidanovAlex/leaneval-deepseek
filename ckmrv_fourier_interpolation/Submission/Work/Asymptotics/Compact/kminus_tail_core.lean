/-
# The cusp-`i∞` expansion of `K_-` along the contour: core algebra

This file sets up the objects of the cusp expansion of `z ↦ K_-^{(d)}(τ,z)` at `z = i∞`,
uniformly for `τ` in a compact `K ⊆ 𝒟`:

* `Sh τ z = E₄(z)³ - Δ(z)j(τ)`: by `Δ(z)j(z) = E₄(z)³` it equals `-Δ(z)(j(τ)-j(z))`, so
  `kpre z τ = -(3456π)·Sh τ z` and `K_- = -(1/(3456π))·(Sh)⁻¹·br`, where `br` is the
  explicit bracket of `KMinus8_eq` / `KMinus24_eq`;
* `br0 d ℓ τ z = 3456π·Gminus d ℓ τ z`, the main part in the same normalisation;
* the reference expansions of the `z`-atoms at the cusp (`Dref`, `Sinvref`, `Wref`, `D2ref`,
  `Lref`, `E14ref`, `E10ref`, `E8ref`, `E6ref`) together with the deviations
  (`dDelta`, `dSinv`, …) whose bounds are the content of `cusp_invDelta`,
  `cusp_inv_divisor_second`, `cusp_W_second`, `cusp_D_second`, `cusp_L_second` and
  `E4Fun_two_term` / `E6Fun_two_term`.

The main estimate is `‖(Sh τ z)⁻¹ * (br + Sh τ z * br0)‖ ≤ C(1+‖z‖)‖Ept z‖`, valid for all
`τ ∈ K` and `1 ≤ z.im`; it is proved by splitting off the reference contributions (an
algebraic identity, `ring`) and bounding the deviations.
-/
import Mathlib
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_bracket
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.cusp_W_second
import Submission.Work.Asymptotics.cusp_D_second
import Submission.Work.Asymptotics.cusp_L_second
import Submission.Work.Asymptotics.cusp_inv_divisor_second
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics.Compact

open Work.Kernels
open Work.Residues (Ept)

/-! ## The two-term `q`-expansions of `E₄` and `E₆`

These are `Work.Residues.E4FunSecondOrder` and `Work.Residues.E6FunSecondOrder`; they are
re-exported here so that the cusp-tail development does not have to import
`Work.Asymptotics.KPlusXiDefs`. -/

theorem E4_two_term_core :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
  Work.Residues.E4FunSecondOrder

theorem E6_two_term_core :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
  Work.Residues.E6FunSecondOrder

/-! ## Definitions -/

/-- `Sh τ z = E₄(z)³ - Δ(z)j(τ) = -Δ(z)(j(τ) - j(z))`. -/
def Sh (τ z : ℍ) : ℂ := E4Fun z ^ 3 - DeltaFun z * jInvariantFun τ

/-- The bracket of `K_-`: the algebraic factor of `K_-` in front of `(kpre)⁻¹`. -/
def brMinus (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  if d = 8 then Work.Residues.bracket8e ℓ z τ else Work.Residues.bracket24e ℓ z τ

/-- The main part `3456π·𝒢_-^{(d)}`, in the normalisation of `brMinus`. -/
def br0 (d : ℕ) (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  (3456 : ℂ) * (Real.pi : ℂ) * Gminus d ℓ τ z

/-- `X = πi z + c`, the constant of the cusp expansion of `𝓛`. -/
def Xc (ℓ : LogLambdaData) (z : ℍ) : ℂ := (Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspC ℓ

/-! ## The bracket identity -/

@[simp] lemma brMinus_eight (ℓ : LogLambdaData) (τ z : ℍ) :
    brMinus ℓ 8 τ z = Work.Residues.bracket8e ℓ z τ := by simp [brMinus]

@[simp] lemma brMinus_twentyfour (ℓ : LogLambdaData) (τ z : ℍ) :
    brMinus ℓ 24 τ z = Work.Residues.bracket24e ℓ z τ := by simp [brMinus]

lemma KMinus_eq_brMinus (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) :
    KMinus ℓ d τ z = (Work.Residues.kpre z τ)⁻¹ * brMinus ℓ d τ z := by
  rcases hd with rfl | rfl
  · rw [KMinus8_eq ℓ τ z, brMinus_eight]
    rfl
  · rw [KMinus24_eq ℓ τ z, brMinus_twentyfour]
    rfl

/-- `Δ(z)j(z) = E₄(z)³`, hence `Δ(z)(j(τ)-j(z)) = -Sh τ z`. -/
lemma DeltaFun_mul_sub (τ z : ℍ) : DeltaFun z * (jInvariantFun τ - jInvariantFun z) = -Sh τ z := by
  rw [Sh, mul_sub, ClassicalFacts.DeltaFun_mul_jInvariantFun]
  ring

/-- `Sh τ z = -(Δ(z) * (j(τ) - j(z)))`. -/
lemma Sh_eq (τ z : ℍ) : Sh τ z = -(DeltaFun z * (jInvariantFun τ - jInvariantFun z)) := by
  rw [DeltaFun_mul_sub, neg_neg]

/-- `kpre z τ = -(3456π)·Sh τ z`. -/
lemma kpre_eq (τ z : ℍ) :
    Work.Residues.kpre z τ = -((3456 : ℂ) * (Real.pi : ℂ)) * Sh τ z := by
  rw [Work.Residues.kpre, Sh_eq τ z]
  simp only [Work.Kernels.c1728]
  ring

/-- The kernel in terms of `Sh` and the bracket. -/
lemma KMinus_eq (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) :
    KMinus ℓ d τ z = -((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * (Sh τ z)⁻¹ * brMinus ℓ d τ z := by
  rw [KMinus_eq_brMinus ℓ d hd τ z, kpre_eq τ z, mul_inv, inv_neg]

/-- The key identity: for `Sh τ z ≠ 0`,
`3456π(K_- - 𝒢_-) = -(Sh τ z)⁻¹ (br + Sh τ z · br0)`. -/
lemma tail_identity (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ)
    (hS : Sh τ z ≠ 0) :
    ((3456 : ℂ) * (Real.pi : ℂ)) * (KMinus ℓ d τ z - Gminus d ℓ τ z) =
      -((Sh τ z)⁻¹ * (brMinus ℓ d τ z + Sh τ z * br0 d ℓ τ z)) := by
  have h1 : KMinus ℓ d τ z = -((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * (Sh τ z)⁻¹ * brMinus ℓ d τ z :=
    KMinus_eq ℓ d hd τ z
  have h2 : ((3456 : ℂ) * (Real.pi : ℂ)) * Gminus d ℓ τ z = br0 d ℓ τ z := by
    rw [br0]
  rw [h1, mul_sub, h2]
  have hA : ((3456 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-! ## The reference expansions of the `z`-atoms

With `e = Ept z` (`‖e‖ = e^{-π z.im}`) the atoms of the bracket have the expansions
`Δ(z)⁻¹ = e^{-2}+24+O(e²)`, `(jτ-j(z))⁻¹·(-Δ(z)⁻¹) = 1+(jτ-720)e²+O(e⁴)`,
`W(z) = 1-8e+24e²+O(e³)`, `U(z)²-V(z)² = 1+16e-144e²+O(e³)`,
`𝓛(z) = πiz+c-8e+12e²+O(e³)`, `E₁₄(z) = 1-24e²+O(e⁴)`, `E₁₀(z) = 1-264e²+O(e⁴)`,
`E₈(z) = 1+480e²+O(e⁴)`, `E₆(z) = 1-504e²+O(e⁴)`.  Below, the `…ref` functions are these
truncations and the `d…` functions the deviations. -/

/-- `e^{-2} = (Ept z)⁻¹²`. -/
def einv2 (z : ℍ) : ℂ := (Ept z)⁻¹ ^ 2

lemma Ept_zpow_two (z : ℍ) : Ept z ^ (-2 : ℤ) = einv2 z := by
  rw [einv2, zpow_neg, zpow_two, mul_inv]
  ring

lemma Ept_zpow_two_ne (z : ℍ) : Ept z ^ (-2 : ℤ) = (Ept z)⁻¹ ^ 2 := Ept_zpow_two z

/-- `Δ(z)⁻¹` reference value. -/
def Dref (z : ℍ) : ℂ := einv2 z + 24
/-- Deviation of `Δ(z)⁻¹`. -/
def dDelta (z : ℍ) : ℂ := (DeltaFun z)⁻¹ - Dref z
/-- `(jτ - j(z))⁻¹` reference value. -/
def Sinvref (τ z : ℍ) : ℂ := 1 + (jInvariantFun τ - 720) * (Ept z) ^ 2
/-- Deviation of `(Sh τ z)⁻¹`. -/
def dSinv (τ z : ℍ) : ℂ := (Sh τ z)⁻¹ - Sinvref τ z
/-- `W(z)` reference value. -/
def Wref (z : ℍ) : ℂ := 1 - 8 * Ept z + 24 * (Ept z) ^ 2
def dW (z : ℍ) : ℂ := WFun z - Wref z
/-- `U(z)² - V(z)²` reference value. -/
def D2ref (z : ℍ) : ℂ := 1 + 16 * Ept z - 144 * (Ept z) ^ 2
def dD2 (z : ℍ) : ℂ := (UFun z ^ 2 - VFun z ^ 2) - D2ref z
/-- `𝓛(z)` reference value. -/
def Lref (ℓ : LogLambdaData) (z : ℍ) : ℂ := Xc ℓ z - 8 * Ept z + 12 * (Ept z) ^ 2
def dL (ℓ : LogLambdaData) (z : ℍ) : ℂ := ℓ.L z - Lref ℓ z
def E14ref (z : ℍ) : ℂ := 1 - 24 * (Ept z) ^ 2
def dE14 (z : ℍ) : ℂ := E14Fun z - E14ref z
def E10ref (z : ℍ) : ℂ := 1 - 264 * (Ept z) ^ 2
def dE10 (z : ℍ) : ℂ := E10Fun z - E10ref z
def E8ref (z : ℍ) : ℂ := 1 + 480 * (Ept z) ^ 2
def dE8 (z : ℍ) : ℂ := E8Fun z - E8ref z
def E6ref (z : ℍ) : ℂ := 1 - 504 * (Ept z) ^ 2
def dE6 (z : ℍ) : ℂ := E6Fun z - E6ref z

/-! ## The decomposition of the bracket in dimension `24` -/

/-- `A₂₄`: the coefficient of `Δ(z)⁻¹` in the bracket. -/
def A24 (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * DeltaFun τ * E14Fun z * ℓ.L z
    - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z
        * (UFun z ^ 2 - VFun z ^ 2)

/-- `C₂₄`: the `J`-free, `Δ(z)`-free coefficient of the bracket. -/
def C24 (ℓ : LogLambdaData) (τ : ℍ) : ℂ :=
  psi2 ℓ τ * E10Fun τ * jInvariantFun τ + psi4 ℓ τ * E8Fun τ * (1728 - jInvariantFun τ)

/-- `B₂₄`: the coefficient of `J = jτ - j(z)` in the bracket. -/
def B24 (ℓ : LogLambdaData) (τ : ℍ) : ℂ :=
  -3456 * DeltaFun τ + 2 * psi2 ℓ τ * E10Fun τ - 2 * psi4 ℓ τ * E8Fun τ

/-- The bracket in dimension `24` is `Δ(z)⁻¹A₂₄ + W(z)C₂₄ + (jτ-j(z))W(z)B₂₄`. -/
lemma brMinus_24_decomp (ℓ : LogLambdaData) (τ z : ℍ) :
    brMinus ℓ 24 τ z = (DeltaFun z)⁻¹ * A24 ℓ τ z + C24 ℓ τ * WFun z
      + (jInvariantFun τ - jInvariantFun z) * WFun z * B24 ℓ τ := by
  simp only [brMinus_twentyfour, Work.Residues.bracket24e, A24, C24, B24, c1728]
  ring

/-- `N`: the coefficient of `e^{-2}` in `br0`. -/
def Nf (ℓ : LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * DeltaFun τ * Xc ℓ z + 3456 * DeltaFun τ
    - 3 * psi2 ℓ τ * E10Fun τ + 3 * psi4 ℓ τ * E8Fun τ

/-- `M`: the `e^{-2}`-free part of `br0`. -/
def Mf (ℓ : LogLambdaData) (τ : ℍ) : ℂ :=
  -41472 * DeltaFun τ - 3456 * DeltaFun τ * (jInvariantFun τ - 768)
    + psi2 ℓ τ * E10Fun τ * (3 * jInvariantFun τ - 1152)
    + psi4 ℓ τ * E8Fun τ * (2880 - 3 * jInvariantFun τ)

lemma Gminus_eight (ℓ : LogLambdaData) (τ z : ℍ) : Gminus 8 ℓ τ z = Gminus8 ℓ τ z := rfl

lemma Gminus_twentyfour (ℓ : LogLambdaData) (τ z : ℍ) : Gminus 24 ℓ τ z = Gminus24 ℓ τ z := by
  simp [Gminus]

lemma pi_ne_zero_complex : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

/-- The main part `br0` in dimension `24`. -/
lemma br0_24 (ℓ : LogLambdaData) (τ z : ℍ) :
    br0 24 ℓ τ z = -Nf ℓ τ z * einv2 z + (-Mf ℓ τ + (720 - jInvariantFun τ) * Nf ℓ τ z) := by
  have hpi := pi_ne_zero_complex
  simp only [br0, Gminus_twentyfour, einv2, Ept_zpow_two]
  simp only [Gminus24, Nf, Mf, Xc]
  field_simp
  ring

/-- The main part `br0` in dimension `8`. -/
lemma br0_8 (ℓ : LogLambdaData) (τ z : ℍ) :
    br0 8 ℓ τ z = 3456 * E4Fun τ * Xc ℓ z - 1728 * psi4 ℓ τ := by
  have hpi := pi_ne_zero_complex
  simp only [br0, Gminus_eight, Gminus8, Xc]
  field_simp
  ring


/-! ## The reference part of the estimate

`Tref8`/`Tref24` is `brMinus + Sh · br0` evaluated on the reference expansions of the
`z`-atoms.  Its expansion in powers of `e = Ept z` starts at order `e¹`; the quotient by `e`
is the explicit polynomial `R8`/`R24`. -/

/-- `brMinus` in dimension `8` with the reference atoms. -/
def br8ref (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * E4Fun τ * E10ref z * Lref l z
    + psi2 l τ * (E14Fun τ / DeltaFun τ) * (E8ref z * Wref z - E6ref z * D2ref z)
    + psi4 l τ * ((1728 - jInvariantFun τ) * E8ref z * Wref z
        + jInvariantFun τ * E6ref z * D2ref z)

/-- `A24` with the reference atoms. -/
def A24ref (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * DeltaFun τ * E14ref z * Lref l z
    - (psi2 l τ * E10Fun τ - psi4 l τ * E8Fun τ) * E10ref z * D2ref z

/-- The reference part in dimension `8`. -/
def Tref8 (l : LogLambdaData) (τ z : ℍ) : ℂ := Sinvref τ z * br8ref l τ z + br0 8 l τ z

/-- The reference part in dimension `24`. -/
def Tref24 (l : LogLambdaData) (τ z : ℍ) : ℂ :=
  Dref z * Sinvref τ z * A24ref l τ z + C24 l τ * Sinvref τ z * Wref z
    - Dref z * Wref z * B24 l τ + br0 24 l τ z

/-- The `Xc`-free coefficient of `Ept z ^ k` in `R8`. -/
def R8_p0 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (27648 : ℂ) * (E4Fun τ) + (-13824 : ℂ) * (psi4 l τ) + (-24 : ℂ) * (psi2 l τ * E14Fun τ / DeltaFun τ) + (24 : ℂ) * (jInvariantFun τ * psi4 l τ)
def R8_p1 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (-41472 : ℂ) * (E4Fun τ) + (-373248 : ℂ) * (psi4 l τ) + (1152 : ℂ) * (psi2 l τ * E14Fun τ / DeltaFun τ) + (576 : ℂ) * (jInvariantFun τ * psi4 l τ)
def R8_p2 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (-27205632 : ℂ) * (E4Fun τ) + (3317760 : ℂ) * (psi4 l τ) + (21504 : ℂ) * (psi2 l τ * E14Fun τ / DeltaFun τ) + (27648 : ℂ) * (jInvariantFun τ * E4Fun τ) + (-35328 : ℂ) * (jInvariantFun τ * psi4 l τ) + (-24 : ℂ) * (jInvariantFun τ * psi2 l τ * E14Fun τ / DeltaFun τ) + (24 : ℂ) * ((jInvariantFun τ) ^ 2 * psi4 l τ)
def R8_p3 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (40808448 : ℂ) * (E4Fun τ) + (-607150080 : ℂ) * (psi4 l τ) + (-890496 : ℂ) * (psi2 l τ * E14Fun τ / DeltaFun τ) + (-41472 : ℂ) * (jInvariantFun τ * E4Fun τ) + (1761408 : ℂ) * (jInvariantFun τ * psi4 l τ) + (1152 : ℂ) * (jInvariantFun τ * psi2 l τ * E14Fun τ / DeltaFun τ) + (-1152 : ℂ) * ((jInvariantFun τ) ^ 2 * psi4 l τ)
def R8_p4 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (5255331840 : ℂ) * (E4Fun τ) + (4777574400 : ℂ) * (psi4 l τ) + (-3041280 : ℂ) * (psi2 l τ * E14Fun τ / DeltaFun τ) + (-7299072 : ℂ) * (jInvariantFun τ * E4Fun τ) + (-3594240 : ℂ) * (jInvariantFun τ * psi4 l τ) + (4224 : ℂ) * (jInvariantFun τ * psi2 l τ * E14Fun τ / DeltaFun τ) + (-4224 : ℂ) * ((jInvariantFun τ) ^ 2 * psi4 l τ)
def R8_p5 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (-7882997760 : ℂ) * (E4Fun τ) + (-14332723200 : ℂ) * (psi4 l τ) + (43960320 : ℂ) * (psi2 l τ * E14Fun τ / DeltaFun τ) + (10948608 : ℂ) * (jInvariantFun τ * E4Fun τ) + (-24053760 : ℂ) * (jInvariantFun τ * psi4 l τ) + (-61056 : ℂ) * (jInvariantFun τ * psi2 l τ * E14Fun τ / DeltaFun τ) + (61056 : ℂ) * ((jInvariantFun τ) ^ 2 * psi4 l τ)

/-- The `Xc`-coefficient of `Ept z ^ k` in `R8`. -/
def R8_q0 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (0 : ℂ)
def R8_q1 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (3400704 : ℂ) * (E4Fun τ) + (-3456 : ℂ) * (jInvariantFun τ * E4Fun τ)
def R8_q2 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (0 : ℂ)
def R8_q3 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (-656916480 : ℂ) * (E4Fun τ) + (912384 : ℂ) * (jInvariantFun τ * E4Fun τ)
def R8_q4 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (0 : ℂ)
def R8_q5 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (0 : ℂ)

/-- The reference part divided by `Ept z`. -/
def R8 (l : LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
  (Xc l z * R8_q0 l τ + R8_p0 l τ) + Ept z * (Xc l z * R8_q1 l τ + R8_p1 l τ)
    + (Ept z) ^ 2 * (Xc l z * R8_q2 l τ + R8_p2 l τ)
    + (Ept z) ^ 3 * (Xc l z * R8_q3 l τ + R8_p3 l τ)
    + (Ept z) ^ 4 * (Xc l z * R8_q4 l τ + R8_p4 l τ)
    + (Ept z) ^ 5 * (Xc l z * R8_q5 l τ + R8_p5 l τ)

/-- The `Xc`-free coefficient of `Ept z ^ k` in `R24`. -/
def R24_p0 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (-29568 : ℂ) * (psi4 l τ * E8Fun τ) + (15744 : ℂ) * (psi2 l τ * E10Fun τ) + (-20570112 : ℂ) * (DeltaFun τ) + (24 : ℂ) * (jInvariantFun τ * psi4 l τ * E8Fun τ) + (-24 : ℂ) * (jInvariantFun τ * psi2 l τ * E10Fun τ) + (27648 : ℂ) * (jInvariantFun τ * DeltaFun τ)
def R24_p1 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (-896832 : ℂ) * (psi4 l τ * E8Fun τ) + (-305856 : ℂ) * (psi2 l τ * E10Fun τ) + (31850496 : ℂ) * (DeltaFun τ) + (2040 : ℂ) * (jInvariantFun τ * psi4 l τ * E8Fun τ) + (-312 : ℂ) * (jInvariantFun τ * psi2 l τ * E10Fun τ) + (-41472 : ℂ) * (jInvariantFun τ * DeltaFun τ) + (-1 : ℂ) * ((jInvariantFun τ) ^ 2 * psi4 l τ * E8Fun τ) + (1 : ℂ) * ((jInvariantFun τ) ^ 2 * psi2 l τ * E10Fun τ)
def R24_p2 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (12616704 : ℂ) * (psi4 l τ * E8Fun τ) + (-2663424 : ℂ) * (psi2 l τ * E10Fun τ) + (-15925248 : ℂ) * (DeltaFun τ) + (-23424 : ℂ) * (jInvariantFun τ * psi4 l τ * E8Fun τ) + (9600 : ℂ) * (jInvariantFun τ * psi2 l τ * E10Fun τ) + (8 : ℂ) * ((jInvariantFun τ) ^ 2 * psi4 l τ * E8Fun τ) + (-8 : ℂ) * ((jInvariantFun τ) ^ 2 * psi2 l τ * E10Fun τ)
def R24_p3 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (-49268736 : ℂ) * (psi4 l τ * E8Fun τ) + (19408896 : ℂ) * (psi2 l τ * E10Fun τ) + (23887872 : ℂ) * (DeltaFun τ) + (86976 : ℂ) * (jInvariantFun τ * psi4 l τ * E8Fun τ) + (-45504 : ℂ) * (jInvariantFun τ * psi2 l τ * E10Fun τ) + (-24 : ℂ) * ((jInvariantFun τ) ^ 2 * psi4 l τ * E8Fun τ) + (24 : ℂ) * ((jInvariantFun τ) ^ 2 * psi2 l τ * E10Fun τ)
def R24_p4 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (72990720 : ℂ) * (psi4 l τ * E8Fun τ) + (-72990720 : ℂ) * (psi2 l τ * E10Fun τ) + (11466178560 : ℂ) * (DeltaFun τ) + (-101376 : ℂ) * (jInvariantFun τ * psi4 l τ * E8Fun τ) + (101376 : ℂ) * (jInvariantFun τ * psi2 l τ * E10Fun τ) + (-15925248 : ℂ) * (jInvariantFun τ * DeltaFun τ)
def R24_p5 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (-656916480 : ℂ) * (psi4 l τ * E8Fun τ) + (656916480 : ℂ) * (psi2 l τ * E10Fun τ) + (-17199267840 : ℂ) * (DeltaFun τ) + (912384 : ℂ) * (jInvariantFun τ * psi4 l τ * E8Fun τ) + (-912384 : ℂ) * (jInvariantFun τ * psi2 l τ * E10Fun τ) + (23887872 : ℂ) * (jInvariantFun τ * DeltaFun τ)

/-- The `Xc`-coefficient of `Ept z ^ k` in `R24`. -/
def R24_q0 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (0 : ℂ)
def R24_q1 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (1990656 : ℂ) * (DeltaFun τ)
def R24_q2 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (0 : ℂ)
def R24_q3 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (-1433272320 : ℂ) * (DeltaFun τ) + (1990656 : ℂ) * (jInvariantFun τ * DeltaFun τ)
def R24_q4 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (0 : ℂ)
def R24_q5 (l : LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (0 : ℂ)

/-- The reference part divided by `Ept z`. -/
def R24 (l : LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
  (Xc l z * R24_q0 l τ + R24_p0 l τ) + Ept z * (Xc l z * R24_q1 l τ + R24_p1 l τ)
    + (Ept z) ^ 2 * (Xc l z * R24_q2 l τ + R24_p2 l τ)
    + (Ept z) ^ 3 * (Xc l z * R24_q3 l τ + R24_p3 l τ)
    + (Ept z) ^ 4 * (Xc l z * R24_q4 l τ + R24_p4 l τ)
    + (Ept z) ^ 5 * (Xc l z * R24_q5 l τ + R24_p5 l τ)

lemma Tref8_eq (l : LogLambdaData) (τ z : ℍ) : Tref8 l τ z = Ept z * R8 l τ z := by
  simp only [Tref8, br8ref, R8, Sinvref, Wref, D2ref, Lref, E14ref, E10ref, E8ref, E6ref,
    Xc, br0_8, R8_p0, R8_p1, R8_p2, R8_p3, R8_p4, R8_p5,
    R8_q0, R8_q1, R8_q2, R8_q3, R8_q4, R8_q5]
  ring

lemma Tref24_eq (l : LogLambdaData) (τ z : ℍ) : Tref24 l τ z = Ept z * R24 l τ z := by
  have he : Ept z ≠ 0 := Work.Residues.Ept_ne_zero z
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  simp only [Tref24, A24ref, R24, Dref, Sinvref, Wref, D2ref, Lref, E14ref, E10ref, einv2,
    Xc, br0_24, Nf, Mf, C24, B24, R24_p0, R24_p1, R24_p2, R24_p3,
    R24_p4, R24_p5, R24_q0, R24_q1, R24_q2, R24_q3, R24_q4, R24_q5]
  field_simp
  ring


end Work.Asymptotics.Compact
