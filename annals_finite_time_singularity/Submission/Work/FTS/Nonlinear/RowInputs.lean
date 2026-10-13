/-
# N4 — the assembly of `pairing_bound` (design §3.6, L-N4.11)

This module contains the **assembly** of the paper's estimate
`|(gRHS, g)| ≤ C·Pbd α X` (Elgindi, §Modulation, Proposition `innerproductestimate`, tex 1536)
from the term-by-term estimates of design §3.4 and the modulation bound of §3.5.

It is the honest content of L-N4.11: once the 26 per-piece estimates of the design's table
(`Structure RowInputs`, below — each of which is a statement about *concrete* functions) and the two exact splits
`N₀ = N₀^{F_*} + Σ …, N = Σ_{i,a,b} N_i^{ab}, N_* = μ(D_zg - g)` are available, the estimate
follows by

* additivity of `IP` in its first argument (`N4Extra.add`, `N4Extra.smul`), which is where the
  split of `gRHS` into `-μ̄AK + N₀ + N + N_*` is performed;
* Cauchy–Schwarz (`N4Extra.cs`) for the pieces carrying an `ℋ⁴`-bound,
* the transport estimates (`N4Extra.t1`–`t5`) for the pieces in which a derivative falls on
  `g`, and
* `N4Extra.dz` for the `N_*`-pairing — the lossless `D_z`-self-pairing (design §5 T5), which
  is what keeps the `N_*`-contribution at `α^{-5/2}X⁴` instead of the fatal `α^{-2}X⁴`;
* the elementary monomial comparisons of `Defs.lean` (`…_le_Pbd`), which put every exponent
  inside `Pbd α X = α²X + √αX² + α^{-3/2}X³ + α^{-5/2}X⁴`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.Nonlinear.Mu

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `Pbd α X ≥ 0` for `0 ≤ α`, `0 ≤ X`. -/
theorem Pbd_nonneg {α X : ℝ} (hα : 0 ≤ α) (hX : 0 ≤ X) : 0 ≤ Pbd α X := by
  rw [Pbd]
  have h1 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 := mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα _) (by positivity)
  have h4 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα _) (by positivity)
  linarith

/-- `√α·X³ ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem sqrt_mul_cube_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    Real.sqrt α * X ^ 3 ≤ Pbd α X := by
  have hle : Real.sqrt α ≤ α ^ (-(3 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have h : Real.sqrt α * X ^ 3 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  have h0 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 := mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h4 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  rw [Pbd] at *; linarith

/-- `α³·X ≤ Pbd α X` for `0 < α ≤ 1`. -/
theorem cube_alpha_mul_le_Pbd {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ 3 * X ≤ Pbd α X := by
  have h32 : α ^ 3 ≤ α ^ 2 := by
    have he : α ^ 3 = α ^ 2 * α := by ring
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hα1
  exact le_trans (mul_le_mul_of_nonneg_right h32 hX) (alpha_sq_mul_le_Pbd hα hX)

/-- `α^{-1/2}X³ ≤ Pbd α X` in the form used for the rows: `√α X³ ≤ Pbd` and
`α^{-1}X³ ≤ Pbd` are the two `α`-factors that occur. -/
theorem rpow_neg_half_mul_cube_le_Pbd' {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ (-(1 / 2 : ℝ)) * X ^ 3 ≤ Pbd α X := rpow_neg_half_mul_cube_le_Pbd hα hα1 hX

/-- The per-piece inputs of the design's table (§3.4) together with the exact splits of
`N₀`, `N` and `N_*` and the three zero-mode estimates of §3.5.

Every field is a statement about *concrete* functions; none of them mentions `UnifIP`.  The
constant `C` is the single universal constant of the table. -/
structure RowInputs (IP : ℝ → Fn → Fn → ℝ) (α C : ℝ) (g Φs Φg : Fn) : Prop where
  /-- the perturbation is in the `ℋ⁴`-class of the frozen vocabulary -/
  reg4 : RegQ α 4 g
  /-- row 1: `|N₀₁+N₀₂|_{ℋ⁴} ≤ Cα²` (tex 1398--1402, `H4N_GammaTerm_le`) -/
  r1 : Xn α (N0fix α) ≤ C * α ^ 2
  /-- row 2: `|N₀₃|_{ℋ⁴} ≤ Cα^{-1}X²` (tex 1404--1406) -/
  r2 : Xn α (N03g α g) ≤ C * (α ^ (-(1 : ℝ)) * Xn α g ^ 2)
  /-- row 3: `|N₀₄ᵃ|_{ℋ⁴} ≤ C√α X` (tex 1410--1412) -/
  r3 : Xn α (N04aF α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 4: `|(N₀₄ᵇ, g)| ≤ Cα^{-3/2}X³` (tex 1414, `Transport1`) -/
  r4 : |IP α (N04bF α g) g| ≤ C * (α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 5: `|N₀₅ᵃ|_{ℋ⁴} ≤ C√α X` (tex 1416--1418) -/
  r5 : Xn α (N05aF α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 6: `|(N₀₅ᵇ, g)| ≤ Cα^{-1/2}X³` (tex 1419, `Transport2`) -/
  r6 : |IP α (N05bF α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 7: `|(N₀₆, g)| ≤ C√α X²` (tex 1421--1423, `Transport3`) -/
  r7 : |IP α (N06F α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  /-- row 8: `|N₁^{gg}|_{ℋ⁴} ≤ Cα^{-1/2}X²` (tex 1450, `HProductRule` + `RemovingL12`) -/
  r8 : Xn α (N1gg α g Φg) ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2)
  /-- row 9: `|N₁^{g*}|_{ℋ⁴} ≤ C√α X` (tex 1451, `WProductRule`) -/
  r9 : Xn α (N1gs α g Φg) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 10: `|N₁^{*g}|_{ℋ⁴} ≤ C√α X` (tex 1451, `PhiStarRegularity`) -/
  r10 : Xn α (N1sg α Φs g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 11: `|N₁^{**}|_{ℋ⁴} ≤ Cα²` (tex 1452--1454, `WtoH` + `ProdW`) -/
  r11 : Xn α (N1ss α Φs) ≤ C * α ^ 2
  /-- row 12: `|(N₂^{gg}, g)| ≤ Cα^{-1/2}X³` (tex 1470, `Transport1`) -/
  r12 : |IP α (N2gg α g Φg) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 13: `|N₂^{g*}|_{ℋ⁴} ≤ Cα^{3/2}X` (tex 1471, `WProductRule`) -/
  r13 : Xn α (N2gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  /-- row 14: `|(N₂^{*g}, g)| ≤ C√α X²` (tex 1473, `SpecialTransport`) -/
  r14 : |IP α (N2sg α Φs g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  /-- row 15: `|N₂^{**}|_{ℋ⁴} ≤ Cα²` (tex 1475, `WtoH` + `WtoW`) -/
  r15 : Xn α (N2ss α Φs) ≤ C * α ^ 2
  /-- row 16: `|(N₃^{gg}, g)| ≤ C√α X³` (tex 1484, `Transport2`) -/
  r16 : |IP α (N3gg α g Φg) g| ≤ C * (Real.sqrt α * Xn α g ^ 3)
  /-- row 17: `|N₃^{g*}|_{ℋ⁴} ≤ Cα^{3/2}X` -/
  r17 : Xn α (N3gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  /-- row 18: `|(N₃^{*g}, g)| ≤ Cα^{3/2}X²` (`Transport3`) -/
  r18 : |IP α (N3sg α Φs g) g| ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g ^ 2)
  /-- row 19: `|N₃^{**}|_{ℋ⁴} ≤ Cα³` (`WtoH`) -/
  r19 : Xn α (N3ss α Φs) ≤ C * (α ^ 3)
  /-- row 20: `|(N₄^{gg}, g)| ≤ Cα^{-1/2}X³` (`Transport1`, `FKg = -D_zL₁₂g`) -/
  r20 : |IP α (N4gg α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 21: `|N₄^{gs}|_{ℋ⁴} ≤ Cα^{3/2}X` -/
  r21 : Xn α (N4gs α g) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  /-- row 22: `|(N₄^{sg}, g)| ≤ C√α X²` (`Transport3`) -/
  r22 : |IP α (N4sg α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  /-- row 23: `|N₄^{**}|_{ℋ⁴} ≤ Cα³` -/
  r23 : Xn α (N4ss α) ≤ C * (α ^ 3)
  /-- row 24: `|N₅^{gg}|_{ℋ⁴} ≤ CX²` (`radial_prod` + `angmul_radial`) -/
  r24 : Xn α (N5gg g) ≤ C * Xn α g ^ 2
  /-- row 25: `|N₅^{gs}| + |N₅^{*g}| ≤ C√α X` (`WProductRule`) -/
  r25 : Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 26: `|N₅^{**}|_{ℋ⁴} ≤ Cα²` -/
  r26 : Xn α (N5ss α) ≤ C * α ^ 2
  /-- the `ℋ⁴`-bound of `AK` (design §3.2, `AK_H4`) -/
  rak : Xn α (Work.Construction.AK α) ≤ C
  /-- `L-N4.6`, constant pieces: `|L₁₂(N₀)(0)| ≤ C(α² + √α X + α^{-3/2}X²)` -/
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  /-- `L-N4.6`, the `N`-pieces -/
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  /-- `L-N4.6`, the `3D_θg/(1+z)`-piece (θ-integration by parts, tex 1517--1521) -/
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ C * Xn α g
  /-- **the split of `N₀`** (design L-N4.3, from `N0_first_two_eq'` and `N04/N05_eq_halves`) -/
  hN0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
          + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)
  /-- **the four-way split of `N`** (design L-N4.3, from `PhiTil_split`, additivity of `FK`
  and the product rule for `∂_θ`, `D_z`) -/
  hN : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
        + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
        + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
        + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
        + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)
  /-- **the `N_*`-collapse** (design §5 T6: `N_* = -μ g - (μ+λ+μλ)D_zg` with
  `λ = lamfun μ` is `μ(D_z g - g)`) -/
  hNs : ∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ

/-! ## Sum additivity of `IP` -/

theorem IP_add6 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4Extra IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ f₅ f₆ : Fn} (hg : RegQ α 4 g) :
    IP α (f₁ + f₂ + f₃ + f₄ + f₅ + f₆) g
      = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g + IP α f₅ g + IP α f₆ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃ + f₄ + f₅) f₆ g hg,
    hE.add α hα (f₁ + f₂ + f₃ + f₄) f₅ g hg,
    hE.add α hα (f₁ + f₂ + f₃) f₄ g hg,
    hE.add α hα (f₁ + f₂) f₃ g hg,
    hE.add α hα f₁ f₂ g hg]

theorem IP_add7 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4Extra IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Fn} (hg : RegQ α 4 g) :
    IP α (f₁ + f₂ + f₃ + f₄ + f₅ + f₆ + f₇) g
      = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g + IP α f₅ g + IP α f₆ g
        + IP α f₇ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃ + f₄ + f₅ + f₆) f₇ g hg,
    hE.add α hα (f₁ + f₂ + f₃ + f₄ + f₅) f₆ g hg,
    hE.add α hα (f₁ + f₂ + f₃ + f₄) f₅ g hg,
    hE.add α hα (f₁ + f₂ + f₃) f₄ g hg,
    hE.add α hα (f₁ + f₂) f₃ g hg,
    hE.add α hα f₁ f₂ g hg]

theorem IP_add4 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4Extra IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ : Fn} (hg : RegQ α 4 g) :
    IP α (f₁ + f₂ + f₃ + f₄) g = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃) f₄ g hg, hE.add α hα (f₁ + f₂) f₃ g hg,
    hE.add α hα f₁ f₂ g hg]

theorem IP_add5 {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct α : ℝ} (hE : N4Extra IP α₂ Ct)
    (hα : α ∈ Set.Ioc 0 α₂) {g f₁ f₂ f₃ f₄ f₅ : Fn} (hg : RegQ α 4 g) :
    IP α (f₁ + f₂ + f₃ + f₄ + f₅) g
      = IP α f₁ g + IP α f₂ g + IP α f₃ g + IP α f₄ g + IP α f₅ g := by
  rw [hE.add α hα (f₁ + f₂ + f₃ + f₄) f₅ g hg,
    hE.add α hα (f₁ + f₂ + f₃) f₄ g hg, hE.add α hα (f₁ + f₂) f₃ g hg,
    hE.add α hα f₁ f₂ g hg]

end Work.FTS.Nonlin
