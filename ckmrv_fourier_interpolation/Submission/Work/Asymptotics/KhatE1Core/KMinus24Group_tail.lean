import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.B24XMData
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore
import Submission.Work.Asymptotics.KhatE1Core.XtruncDev.Composites

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane
open Work.Residues (Ept)

noncomputable section

/-!
# The `K₋`-truncation tail of the `d = 24` bracket

`KMinus24Group ℓ τ z = (3456π)⁻¹ (brMinus₍₂₄₎ + Sh·br0₂₄ − Sh·E(z)·(E1combo24 + Am24))` is the
`K₋`-half of `X = Sh τ z·Bracket24 ℓ τ z` (`KhatE1Core.Bracket24TailCore`), and `XMinusT ℓ τ z`
is the same expression with every `z`-atom replaced by its explicit cusp truncation and `𝓛` by
its fifth-order truncation (`KhatE1Core.brMinusT`, `XtruncDev.A24TC`).  Here we prove the
truncation tail

  `‖KMinus24Group ℓ τ z - XMinusT ℓ τ z‖ ≤ C (scale τ)^N (1+t)^M ‖E(z)‖⁴`

on the funnel strip `Funnel τ`, `τ.im + 1 ≤ t = z.im`, `0 ≤ z.re ≤ 1`.

The bookkeeping is the two-exponent calculus `Bound2 f n k` of
`KhatE1Core/DSm1RowBound.lean` (`‖f τ z‖ ≤ C ‖q(τ)‖^n (scale τ)^N (1+t)^M ‖q(z)‖^k`), whose
atoms for the whole `z`-side (`B2_*` of `KhatE1Core/XtruncDev/`) are already proved.  The target
weight is `(0,2)`, i.e. `‖E(z)‖⁴` since `q(z) = E(z)²`.

The difference splits as

  `(Δ(z)⁻¹A₂₄ − (1/Δ)ᵀ·A₂₄ᵀ) + C₂₄(W − Wᵀ) + ((j(τ)−j(z))W B₂₄ − (j(τ)−jᵀ(z))Wᵀ B₂₄)`
  `  + (Sh − Shᵀ)·(br0 − E(z)(E1combo24+Am24))`,

each summand of which lands at a weight with `k ≥ 2` and `n + k ≥ 2`, hence is pushed to `(0,2)`
by `Bound2.shift` / `Bound2.mono`.
-/

/-! ## The pieces -/

/-- The `K₋`-bracket of the truncated expression `XMinusT`. -/
def KM24T (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  invDeltaT z * XtruncDev.A24TC ℓ τ z + Work.Asymptotics.Compact.C24 ℓ τ * WT z
    + (Work.Kernels.jInvariantFun τ - jzT z) * WT z * Work.Asymptotics.Compact.B24 ℓ τ
    + ShT τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z
    - ShT τ z * Ept z * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ)

/-- `-Nf·e^{-2πiz}`: the `q(z)⁻¹`-half of `br0₂₄`. -/
def KM24br0a (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -(Work.Asymptotics.Compact.Nf ℓ τ z) * Work.Asymptotics.Compact.einv2 z

/-- The `q(z)⁻¹`-free half of `br0₂₄`. -/
def KM24br0b (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -(Work.Asymptotics.Compact.Mf ℓ τ)
    + (720 - Work.Kernels.jInvariantFun τ) * Work.Asymptotics.Compact.Nf ℓ τ z

/-- The `Δ(z)⁻¹`-part of the difference. -/
def KM24P1 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Work.Kernels.DeltaFun z)⁻¹ * (Work.Asymptotics.Compact.A24 ℓ τ z - XtruncDev.A24TC ℓ τ z)

/-- The `1/Δ`-truncation part of the difference. -/
def KM24P2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((Work.Kernels.DeltaFun z)⁻¹ - invDeltaT z) * XtruncDev.A24TC ℓ τ z

/-- The `C₂₄`-part of the difference. -/
def KM24P3 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Asymptotics.Compact.C24 ℓ τ * (Work.Kernels.WFun z - WT z)

/-- The `j(τ)(W − Wᵀ)B₂₄`-part of the difference. -/
def KM24P4 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.jInvariantFun τ
    * ((Work.Kernels.WFun z - WT z) * Work.Asymptotics.Compact.B24 ℓ τ)

/-- The `jᵀ(z)(Wᵀ − W)B₂₄`-part of the difference. -/
def KM24P5 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  jzT z * ((WT z - Work.Kernels.WFun z) * Work.Asymptotics.Compact.B24 ℓ τ)

/-- The `(jᵀ(z) − j(z))W B₂₄`-part of the difference. -/
def KM24P6 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (jzT z - Work.Kernels.jInvariantFun z)
    * (Work.Kernels.WFun z * Work.Asymptotics.Compact.B24 ℓ τ)

/-- The `(E₄(z)³ − E₄ᵀ(z)³)·br0a`-part of the difference. -/
def KM24P7 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Work.Kernels.E4Fun z ^ 3 - E4T z ^ 3) * KM24br0a ℓ τ z

/-- The `(E₄(z)³ − E₄ᵀ(z)³)·br0b`-part of the difference. -/
def KM24P8 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Work.Kernels.E4Fun z ^ 3 - E4T z ^ 3) * KM24br0b ℓ τ z

/-- The `(Δ(z) − Δᵀ(z))j(τ)·br0a`-part of the difference. -/
def KM24P9 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Work.Kernels.DeltaFun z - DeltaT z) * Work.Kernels.jInvariantFun τ * KM24br0a ℓ τ z

/-- The `(Δ(z) − Δᵀ(z))j(τ)·br0b`-part of the difference. -/
def KM24P10 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Work.Kernels.DeltaFun z - DeltaT z) * Work.Kernels.jInvariantFun τ * KM24br0b ℓ τ z

/-- The `(E₄(z)³ − E₄ᵀ(z)³)E(z)(E1combo24+Am24)`-part of the difference. -/
def KM24P11 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Work.Kernels.E4Fun z ^ 3 - E4T z ^ 3) * Ept z
    * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ)

/-- The `(Δ(z) − Δᵀ(z))j(τ)E(z)(E1combo24+Am24)`-part of the difference. -/
def KM24P12 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Work.Kernels.DeltaFun z - DeltaT z) * Work.Kernels.jInvariantFun τ * Ept z
    * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ)

/-- The sum of the twelve pieces of the difference. -/
def KM24Sum (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z + KM24P4 ℓ τ z + KM24P5 ℓ τ z + KM24P6 ℓ τ z
    + KM24P7 ℓ τ z + KM24P8 ℓ τ z - KM24P9 ℓ τ z - KM24P10 ℓ τ z - KM24P11 ℓ τ z
    + KM24P12 ℓ τ z

/-! ## `Bound2` atoms -/

lemma KM24_B2_C24 (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ z : ℍ) => Work.Asymptotics.Compact.C24 ℓ τ) (-1) 0 := by
  have h1 : Bound2 (fun (τ z : ℍ) => Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
      * Work.Kernels.jInvariantFun τ) (-1) 0 :=
    (((XtruncDev.B2_psi2 ℓ).mul XtruncDev.B2_E10tau).mul XtruncDev.B2_jtau)
  have h2 : Bound2 (fun (τ z : ℍ) => Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
      * (1728 - Work.Kernels.jInvariantFun τ)) (-1) 0 :=
    (((XtruncDev.B2_psi4 ℓ).mul XtruncDev.B2_E8tau).mul
      ((Bound2.const (1728 : ℂ)).sub XtruncDev.B2_jtau))
  exact (h1.add h2).congr (fun τ z => by simp only [Work.Asymptotics.Compact.C24])

lemma KM24_B2_B24 (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ z : ℍ) => Work.Asymptotics.Compact.B24 ℓ τ) 0 0 := by
  have h1 : Bound2 (fun (τ z : ℍ) => (-3456 : ℂ) * Work.Kernels.DeltaFun τ) 0 0 :=
    XtruncDev.B2_Deltatau.cmul (-3456)
  have h2 : Bound2 (fun (τ z : ℍ) => (2 : ℂ) * Work.Kernels.psi2 ℓ τ
      * Work.Kernels.E10Fun τ) 0 0 :=
    (((Bound2.const (2 : ℂ)).mul (XtruncDev.B2_psi2 ℓ)).mul XtruncDev.B2_E10tau)
  have h3 : Bound2 (fun (τ z : ℍ) => (2 : ℂ) * Work.Kernels.psi4 ℓ τ
      * Work.Kernels.E8Fun τ) 0 0 :=
    (((Bound2.const (2 : ℂ)).mul (XtruncDev.B2_psi4 ℓ)).mul XtruncDev.B2_E8tau)
  exact ((h1.add h2).sub h3).congr (fun τ z => by simp only [Work.Asymptotics.Compact.B24])

lemma KM24_B2_Nf (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ z : ℍ) => Work.Asymptotics.Compact.Nf ℓ τ z) 0 0 := by
  have h1 : Bound2 (fun (τ z : ℍ) => (-3456 : ℂ) * Work.Kernels.DeltaFun τ
      * Work.Asymptotics.Compact.Xc ℓ z) 0 0 :=
    ((Bound2.const (-3456 : ℂ)).mul XtruncDev.B2_Deltatau).mul (B2_Xc ℓ)
  have h2 : Bound2 (fun (τ z : ℍ) => (3456 : ℂ) * Work.Kernels.DeltaFun τ) 0 0 :=
    XtruncDev.B2_Deltatau.cmul 3456
  have h3 : Bound2 (fun (τ z : ℍ) => (3 : ℂ) * Work.Kernels.psi2 ℓ τ
      * Work.Kernels.E10Fun τ) 0 0 :=
    (((Bound2.const (3 : ℂ)).mul (XtruncDev.B2_psi2 ℓ)).mul XtruncDev.B2_E10tau)
  have h4 : Bound2 (fun (τ z : ℍ) => (3 : ℂ) * Work.Kernels.psi4 ℓ τ
      * Work.Kernels.E8Fun τ) 0 0 :=
    (((Bound2.const (3 : ℂ)).mul (XtruncDev.B2_psi4 ℓ)).mul XtruncDev.B2_E8tau)
  exact (((h1.add h2).sub h3).add h4).congr (fun τ z => by
    simp only [Work.Asymptotics.Compact.Nf])

lemma KM24_B2_Mf (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ z : ℍ) => Work.Asymptotics.Compact.Mf ℓ τ) (-1) 0 := by
  have h1 : Bound2 (fun (τ z : ℍ) => (-41472 : ℂ) * Work.Kernels.DeltaFun τ) (-1) 0 :=
    (XtruncDev.B2_Deltatau.cmul (-41472)).mono (by norm_num) le_rfl
  have h2 : Bound2 (fun (τ z : ℍ) => (-3456 : ℂ) * Work.Kernels.DeltaFun τ
      * (Work.Kernels.jInvariantFun τ - 768)) (-1) 0 :=
    (((Bound2.const (-3456 : ℂ)).mul XtruncDev.B2_Deltatau).mul
      (XtruncDev.B2_jtau.sub (Bound2.const (768 : ℂ))))
  have h3 : Bound2 (fun (τ z : ℍ) => Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
      * ((3 : ℂ) * Work.Kernels.jInvariantFun τ - 1152)) (-1) 0 :=
    (((XtruncDev.B2_psi2 ℓ).mul XtruncDev.B2_E10tau).mul
      (((Bound2.const (3 : ℂ)).mul XtruncDev.B2_jtau).sub (Bound2.const (1152 : ℂ))))
  have h4 : Bound2 (fun (τ z : ℍ) => Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
      * (2880 - (3 : ℂ) * Work.Kernels.jInvariantFun τ)) (-1) 0 :=
    (((XtruncDev.B2_psi4 ℓ).mul XtruncDev.B2_E8tau).mul
      ((Bound2.const (2880 : ℂ)).sub ((Bound2.const (3 : ℂ)).mul XtruncDev.B2_jtau)))
  exact (((h1.add h2).add h3).add h4).congr (fun τ z => by
    simp only [Work.Asymptotics.Compact.Mf]
    ring)

/-- `einv2 z = q(z)⁻¹` in the two-exponent calculus. -/
lemma KM24_B2_einv2 :
    Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Asymptotics.Compact.einv2 z) 0 (-1) := by
  have h : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z)⁻¹) 0 (-1) := B2_qinv
  exact h.congr (fun τ z => by
    simp only [Work.Asymptotics.Compact.einv2, Work.Asymptotics.K24F.qParamFun_eq_Ept_sq',
      inv_pow])

/-- The `q(z)⁻¹`-free half of `br0₂₄`. -/
lemma KM24_B2_br0b (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (KM24br0b ℓ) (-1) 0 := by
  have h : Bound2 (fun (τ z : ℍ) => -(Work.Asymptotics.Compact.Mf ℓ τ)
      + (720 - Work.Kernels.jInvariantFun τ) * Work.Asymptotics.Compact.Nf ℓ τ z) (-1) 0 :=
    ((KM24_B2_Mf ℓ).neg).add
      (((Bound2.const (720 : ℂ)).sub XtruncDev.B2_jtau).mul (KM24_B2_Nf ℓ))
  exact h.congr (fun τ z => by simp only [KM24br0b])

/-- The `q(z)⁻¹`-half of `br0₂₄`. -/
lemma KM24_B2_br0a (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (KM24br0a ℓ) 0 (-1) := by
  have h : Bound2 (fun (τ z : ℍ) => -(Work.Asymptotics.Compact.Nf ℓ τ z)
      * Work.Asymptotics.Compact.einv2 z) 0 (-1) :=
    ((KM24_B2_Nf ℓ).neg).mul KM24_B2_einv2
  exact h.congr (fun τ z => by simp only [KM24br0a])

lemma KM24_B2_A24TC (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ z : ℍ) => XtruncDev.A24TC ℓ τ z) 0 0 := by
  have h1 : Bound2 (fun (τ z : ℍ) => (-3456 : ℂ) * Work.Kernels.DeltaFun τ
      * E14T z * XtruncDev.LT5 ℓ z) 0 0 :=
    (((Bound2.const (-3456 : ℂ)).mul XtruncDev.B2_Deltatau).mul B2_E14T).mul
      (XtruncDev.B2_LT5 ℓ)
  have h2 : Bound2 (fun (τ z : ℍ) => (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
      - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ) * E10T z * D2T z) 0 0 :=
    ((((XtruncDev.B2_psi2 ℓ).mul XtruncDev.B2_E10tau).sub
      ((XtruncDev.B2_psi4 ℓ).mul XtruncDev.B2_E8tau)).mul B2_E10T).mul B2_D2T
  exact (h1.sub h2).congr (fun τ z => by
    simp only [XtruncDev.A24TC])

/-- **The `A₂₄`-truncation tail**: `A₂₄ - A₂₄ᵀ = O(‖q(z)‖³)`. -/
lemma KM24_B2_A24diff (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ z : ℍ) => Work.Asymptotics.Compact.A24 ℓ τ z
      - XtruncDev.A24TC ℓ τ z) 0 3 := by
  have h1a : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E14Fun z
      * (ℓ.L z - XtruncDev.LT5 ℓ z)) 0 3 :=
    XtruncDev.B2_E14Fun.mul (XtruncDev.B2_dLT5 ℓ)
  have h1b : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.E14Fun z - E14T z)
      * XtruncDev.LT5 ℓ z) 0 3 :=
    XtruncDev.B2_dE14T.mul (XtruncDev.B2_LT5 ℓ)
  have h1 : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E14Fun z * ℓ.L z
      - E14T z * XtruncDev.LT5 ℓ z) 0 3 :=
    (h1a.add h1b).congr (fun τ z => by ring)
  have hA : Bound2 (fun (τ z : ℍ) => (-3456 : ℂ) * Work.Kernels.DeltaFun τ
      * (Work.Kernels.E14Fun z * ℓ.L z - E14T z * XtruncDev.LT5 ℓ z)) 0 3 :=
    ((Bound2.const (-3456 : ℂ)).mul XtruncDev.B2_Deltatau).mul h1
  have h2a : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E10Fun z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - D2T z)) 0 3 :=
    XtruncDev.B2_E10Fun.mul XtruncDev.D2Tdev
  have h2b : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.E10Fun z - E10T z)
      * D2T z) 0 3 :=
    XtruncDev.E10Tdev.mul B2_D2T
  have h2 : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E10Fun z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
      - E10T z * D2T z) 0 3 :=
    (h2a.add h2b).congr (fun τ z => by ring)
  have h3 : Bound2 (fun (τ _ : ℍ) => Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
      - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ) 0 0 :=
    ((XtruncDev.B2_psi2 ℓ).mul XtruncDev.B2_E10tau).sub
      ((XtruncDev.B2_psi4 ℓ).mul XtruncDev.B2_E8tau)
  have hB : Bound2 (fun (τ z : ℍ) => (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
      - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)
      * (Work.Kernels.E10Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
        - E10T z * D2T z)) 0 3 := h3.mul h2
  exact (hA.sub hB).congr (fun τ z => by
    simp only [Work.Asymptotics.Compact.A24, XtruncDev.A24TC]
    ring)

/-- `E1combo24` is `O(‖q(τ)‖⁻¹(scale τ)^N)`, from the atom bounds. -/
lemma KM24_B2_E1c (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ _ : ℍ) => Work.Asymptotics.E1combo24 ℓ τ) (-1) 0 := by
  have h1 : Bound2 (fun (τ _ : ℍ) => (27648 : ℂ)
      * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)) (-1) 0 :=
    (Bound2.const (27648 : ℂ)).mul (XtruncDev.B2_jtau.mul XtruncDev.B2_Deltatau)
  have h2 : Bound2 (fun (τ _ : ℍ) => (24 : ℂ)
      * (Work.Kernels.jInvariantFun τ * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)))
      (-1) 0 :=
    (Bound2.const (24 : ℂ)).mul
      (XtruncDev.B2_jtau.mul ((XtruncDev.B2_psi2 ℓ).mul XtruncDev.B2_E10tau))
  have h3 : Bound2 (fun (τ _ : ℍ) => (24 : ℂ)
      * (Work.Kernels.jInvariantFun τ * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)))
      (-1) 0 :=
    (Bound2.const (24 : ℂ)).mul
      (XtruncDev.B2_jtau.mul ((XtruncDev.B2_psi4 ℓ).mul XtruncDev.B2_E8tau))
  have h4 : Bound2 (fun (τ _ : ℍ) => (20570112 : ℂ) * Work.Kernels.DeltaFun τ) (-1) 0 :=
    (XtruncDev.B2_Deltatau.cmul 20570112).mono (by norm_num) le_rfl
  have h5 : Bound2 (fun (τ _ : ℍ) => (15744 : ℂ)
      * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)) (-1) 0 :=
    ((Bound2.const (15744 : ℂ)).mul
      ((XtruncDev.B2_psi2 ℓ).mul XtruncDev.B2_E10tau)).mono (by norm_num) le_rfl
  have h6 : Bound2 (fun (τ _ : ℍ) => (29568 : ℂ)
      * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)) (-1) 0 :=
    ((Bound2.const (29568 : ℂ)).mul
      ((XtruncDev.B2_psi4 ℓ).mul XtruncDev.B2_E8tau)).mono (by norm_num) le_rfl
  have h : Bound2 (fun (τ _ : ℍ) => (27648 : ℂ)
        * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)
        - (24 : ℂ) * (Work.Kernels.jInvariantFun τ
            * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ))
        + (24 : ℂ) * (Work.Kernels.jInvariantFun τ
            * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ))
        - (20570112 : ℂ) * Work.Kernels.DeltaFun τ
        + (15744 : ℂ) * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
        - (29568 : ℂ) * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)) (-1) 0 :=
    ((((h1.sub h2).add h3).sub h4).add h5).sub h6
  exact h.congr (fun τ z => by simp only [Work.Asymptotics.E1combo24])

/-- `Am24` is `O(‖q(τ)‖⁻¹(scale τ)^N)`, from the atom bounds. -/
lemma KM24_B2_Am (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ _ : ℍ) => Work.Asymptotics.KhatE1.Am24 ℓ τ) (-1) 0 := by
  have h1 : Bound2 (fun (τ _ : ℍ) => (-73728 : ℂ) * Work.Kernels.DeltaFun τ) (-1) 0 :=
    (XtruncDev.B2_Deltatau.cmul (-73728)).mono (by norm_num) le_rfl
  have h2 : Bound2 (fun (τ _ : ℍ) => (384 : ℂ) * (Work.Kernels.psi2 ℓ τ
      * Work.Kernels.E10Fun τ - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)) (-1) 0 :=
    ((Bound2.const (384 : ℂ)).mul (((XtruncDev.B2_psi2 ℓ).mul XtruncDev.B2_E10tau).sub
      ((XtruncDev.B2_psi4 ℓ).mul XtruncDev.B2_E8tau))).mono (by norm_num) le_rfl
  exact (h1.sub h2).congr (fun τ z => by simp only [Work.Asymptotics.KhatE1.Am24])

/-! ## The twelve pieces at the weight `(0,2)` -/

lemma KM24_B2_P1 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P1 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => (Work.Kernels.DeltaFun z)⁻¹
      * (Work.Asymptotics.Compact.A24 ℓ τ z - XtruncDev.A24TC ℓ τ z)) 0 2 :=
    XtruncDev.B2_DeltaInv.mul (KM24_B2_A24diff ℓ)
  exact h.congr (fun τ z => by simp only [KM24P1])

lemma KM24_B2_P2 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P2 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => ((Work.Kernels.DeltaFun z)⁻¹ - invDeltaT z)
      * XtruncDev.A24TC ℓ τ z) 0 2 :=
    XtruncDev.dinvDeltaTdev.mul (KM24_B2_A24TC ℓ)
  exact h.congr (fun τ z => by simp only [KM24P2])

/-- `Wᵀ - W = -(W - Wᵀ)`. -/
lemma KM24_B2_WTsub : Bound2 (fun (_ : ℍ) (z : ℍ) => WT z - Work.Kernels.WFun z) 0 3 :=
  XtruncDev.WTdev.neg |>.congr (fun τ z => by ring)

lemma KM24_B2_P3 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P3 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => Work.Asymptotics.Compact.C24 ℓ τ
      * (Work.Kernels.WFun z - WT z)) (-1) 3 :=
    (KM24_B2_C24 ℓ).mul XtruncDev.WTdev
  exact (h.shift).congr (fun τ z => by simp only [KM24P3])

lemma KM24_B2_P4 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P4 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => Work.Kernels.jInvariantFun τ
      * ((Work.Kernels.WFun z - WT z) * Work.Asymptotics.Compact.B24 ℓ τ)) (-1) 3 :=
    XtruncDev.B2_jtau.mul (XtruncDev.WTdev.mul (KM24_B2_B24 ℓ))
  exact (h.shift).congr (fun τ z => by simp only [KM24P4])

lemma KM24_B2_P5 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P5 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => jzT z
      * ((WT z - Work.Kernels.WFun z) * Work.Asymptotics.Compact.B24 ℓ τ)) 0 2 :=
    B2_jzT.mul (KM24_B2_WTsub.mul (KM24_B2_B24 ℓ))
  exact h.congr (fun τ z => by simp only [KM24P5])

lemma KM24_B2_P6 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P6 ℓ) 0 2 := by
  have h0 : Bound2 (fun (_ : ℍ) (z : ℍ) => jzT z - Work.Kernels.jInvariantFun z) 0 2 :=
    (XtruncDev.B2_djzT.neg).congr (fun τ z => by ring)
  have h : Bound2 (fun (τ z : ℍ) => (jzT z - Work.Kernels.jInvariantFun z)
      * (Work.Kernels.WFun z * Work.Asymptotics.Compact.B24 ℓ τ)) 0 2 :=
    h0.mul (XtruncDev.B2_WFun.mul (KM24_B2_B24 ℓ))
  exact h.congr (fun τ z => by simp only [KM24P6])

lemma KM24_B2_P7 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P7 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => (Work.Kernels.E4Fun z ^ 3 - E4T z ^ 3)
      * (-(Work.Asymptotics.Compact.Nf ℓ τ z) * Work.Asymptotics.Compact.einv2 z)) 0 2 :=
    XtruncDev.B2_dE4cT.mul ((KM24_B2_Nf ℓ).neg.mul KM24_B2_einv2)
  exact h.congr (fun τ z => by simp only [KM24P7, KM24br0a])

lemma KM24_B2_P8 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P8 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => (Work.Kernels.E4Fun z ^ 3 - E4T z ^ 3)
      * KM24br0b ℓ τ z) (-1) 3 :=
    XtruncDev.B2_dE4cT.mul (KM24_B2_br0b ℓ)
  exact (h.shift).congr (fun τ z => by simp only [KM24P8])

lemma KM24_B2_P9 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P9 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => (Work.Kernels.DeltaFun z - DeltaT z)
      * Work.Kernels.jInvariantFun τ * KM24br0a ℓ τ z) (-1) 3 :=
    (XtruncDev.B2_dDeltaT.mul XtruncDev.B2_jtau).mul (KM24_B2_br0a ℓ)
  exact (h.shift).congr (fun τ z => by simp only [KM24P9])

lemma KM24_B2_P10 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P10 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => (Work.Kernels.DeltaFun z - DeltaT z)
      * Work.Kernels.jInvariantFun τ * KM24br0b ℓ τ z) (-2) 4 :=
    (XtruncDev.B2_dDeltaT.mul XtruncDev.B2_jtau).mul (KM24_B2_br0b ℓ)
  exact ((h.shift).shift).congr (fun τ z => by simp only [KM24P10])

lemma KM24_B2_P11 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P11 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => (Work.Kernels.E4Fun z ^ 3 - E4T z ^ 3)
      * Ept z * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ))
      (-1) 3 :=
    (XtruncDev.B2_dE4cT.mul B2_Ept).mul ((KM24_B2_E1c ℓ).add (KM24_B2_Am ℓ))
  exact (h.shift).congr (fun τ z => by simp only [KM24P11])

lemma KM24_B2_P12 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (KM24P12 ℓ) 0 2 := by
  have h : Bound2 (fun (τ z : ℍ) => (Work.Kernels.DeltaFun z - DeltaT z)
      * Work.Kernels.jInvariantFun τ * Ept z
      * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ)) (-2) 4 :=
    ((XtruncDev.B2_dDeltaT.mul XtruncDev.B2_jtau).mul B2_Ept).mul
      ((KM24_B2_E1c ℓ).add (KM24_B2_Am ℓ))
  exact ((h.shift).shift).congr (fun τ z => by simp only [KM24P12])

/-! ## The algebra -/

/-- **`XMinusT` in materialised form.** -/
theorem KM24_XMinusT_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    XMinusT ℓ τ z = ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * KM24T ℓ τ z := by
  simp only [XMinusT, brMinusT, KM24T, XtruncDev.A24TC, A24T, XtruncDev.LT5, LT, Te, Tq]
  ring_nf

/-- The `Δ(z)⁻¹A₂₄`-group of the identity. -/
lemma KM24_id_a (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    (Work.Kernels.DeltaFun z)⁻¹ * Work.Asymptotics.Compact.A24 ℓ τ z
        - invDeltaT z * XtruncDev.A24TC ℓ τ z = KM24P1 ℓ τ z + KM24P2 ℓ τ z := by
  simp only [KM24P1, KM24P2]
  ring

/-- The `C₂₄`-group of the identity. -/
lemma KM24_id_b (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.Compact.C24 ℓ τ * Work.Kernels.WFun z
        - Work.Asymptotics.Compact.C24 ℓ τ * WT z = KM24P3 ℓ τ z := by
  simp only [KM24P3]
  ring

/-- The `j`-group of the identity. -/
lemma KM24_id_c (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) * Work.Kernels.WFun z
        * Work.Asymptotics.Compact.B24 ℓ τ
      - (Work.Kernels.jInvariantFun τ - jzT z) * WT z * Work.Asymptotics.Compact.B24 ℓ τ
      = KM24P4 ℓ τ z + KM24P5 ℓ τ z + KM24P6 ℓ τ z := by
  simp only [KM24P4, KM24P5, KM24P6]
  ring

/-- The `Sh - Shᵀ`-group of the identity. -/
lemma KM24_id_d (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    (Work.Asymptotics.Compact.Sh τ z - ShT τ z)
        * (Work.Asymptotics.Compact.br0 24 ℓ τ z
            - Ept z * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ))
      = KM24P7 ℓ τ z + KM24P8 ℓ τ z - KM24P9 ℓ τ z - KM24P10 ℓ τ z - KM24P11 ℓ τ z
        + KM24P12 ℓ τ z := by
  rw [Work.Asymptotics.Compact.br0_24]
  simp only [Work.Asymptotics.Compact.Sh, ShT, KM24P7, KM24P8, KM24P9, KM24P10, KM24P11, KM24P12,
    KM24br0a, KM24br0b, DeltaT, E4T]
  ring

/-- **The algebraic identity**: the `K₋`-bracket difference is the sum of the twelve pieces. -/
theorem KM24_bracket_identity (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.Compact.brMinus ℓ 24 τ z
        + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z
        - Work.Asymptotics.Compact.Sh τ z * Ept z
            * (Work.Asymptotics.E1combo24 ℓ τ + Work.Asymptotics.KhatE1.Am24 ℓ τ)
        - KM24T ℓ τ z = KM24Sum ℓ τ z := by
  have ha := KM24_id_a ℓ τ z
  have hb := KM24_id_b ℓ τ z
  have hc := KM24_id_c ℓ τ z
  have hd := KM24_id_d ℓ τ z
  simp only [KM24T, KM24Sum, Work.Asymptotics.Compact.brMinus_24_decomp]
  linear_combination ha + hb + hc + hd

/-- **The `Bound2` form of the `K₋`-tail.** -/
theorem KM24_Bound2 (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun τ z : ℍ => KMinus24Group ℓ τ z - XMinusT ℓ τ z) 0 2 := by
  have h01 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z) 0 2 :=
    (KM24_B2_P1 ℓ).add (KM24_B2_P2 ℓ)
  have h02 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z) 0 2 :=
    h01.add (KM24_B2_P3 ℓ)
  have h03 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z
      + KM24P4 ℓ τ z) 0 2 := h02.add (KM24_B2_P4 ℓ)
  have h04 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z
      + KM24P4 ℓ τ z + KM24P5 ℓ τ z) 0 2 := h03.add (KM24_B2_P5 ℓ)
  have h05 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z
      + KM24P4 ℓ τ z + KM24P5 ℓ τ z + KM24P6 ℓ τ z) 0 2 := h04.add (KM24_B2_P6 ℓ)
  have h06 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z
      + KM24P4 ℓ τ z + KM24P5 ℓ τ z + KM24P6 ℓ τ z + KM24P7 ℓ τ z) 0 2 :=
    h05.add (KM24_B2_P7 ℓ)
  have h07 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z
      + KM24P4 ℓ τ z + KM24P5 ℓ τ z + KM24P6 ℓ τ z + KM24P7 ℓ τ z + KM24P8 ℓ τ z) 0 2 :=
    h06.add (KM24_B2_P8 ℓ)
  have h08 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z
      + KM24P4 ℓ τ z + KM24P5 ℓ τ z + KM24P6 ℓ τ z + KM24P7 ℓ τ z + KM24P8 ℓ τ z
      - KM24P9 ℓ τ z) 0 2 := h07.sub (KM24_B2_P9 ℓ)
  have h09 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z
      + KM24P4 ℓ τ z + KM24P5 ℓ τ z + KM24P6 ℓ τ z + KM24P7 ℓ τ z + KM24P8 ℓ τ z
      - KM24P9 ℓ τ z - KM24P10 ℓ τ z) 0 2 := h08.sub (KM24_B2_P10 ℓ)
  have h10 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z
      + KM24P4 ℓ τ z + KM24P5 ℓ τ z + KM24P6 ℓ τ z + KM24P7 ℓ τ z + KM24P8 ℓ τ z
      - KM24P9 ℓ τ z - KM24P10 ℓ τ z - KM24P11 ℓ τ z) 0 2 := h09.sub (KM24_B2_P11 ℓ)
  have h11 : Bound2 (fun τ z : ℍ => KM24P1 ℓ τ z + KM24P2 ℓ τ z + KM24P3 ℓ τ z
      + KM24P4 ℓ τ z + KM24P5 ℓ τ z + KM24P6 ℓ τ z + KM24P7 ℓ τ z + KM24P8 ℓ τ z
      - KM24P9 ℓ τ z - KM24P10 ℓ τ z - KM24P11 ℓ τ z + KM24P12 ℓ τ z) 0 2 :=
    h10.add (KM24_B2_P12 ℓ)
  have hsum : Bound2 (KM24Sum ℓ) 0 2 := h11.congr (fun τ z => by simp only [KM24Sum])
  refine (hsum.cmul (((3456 : ℂ) * (Real.pi : ℂ))⁻¹)).congr (fun τ z => ?_)
  have hb := KM24_bracket_identity ℓ τ z
  have hx := KM24_XMinusT_eq ℓ τ z
  rw [← hb, hx]
  simp only [KMinus24Group]
  ring

/-! ## The requested tail bound -/

theorem KMinus24Group_tail (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
            - Work.Asymptotics.KhatE1Core.XMinusT ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * ‖Work.Residues.Ept z‖ ^ 4 := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := KM24_Bound2 ℓ
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  have hqE : ‖Work.Kernels.qParamFun z‖ ^ (2 : ℤ) = ‖Work.Residues.Ept z‖ ^ 4 := by
    rw [zpow_ofNat, Work.Asymptotics.K24F.qParamFun_eq_Ept_sq', norm_pow]
    ring
  rw [hqE] at h
  refine le_trans h (le_of_eq ?_)
  rw [zpow_zero]
  ring

end

end Work.Asymptotics.KhatE1Core
