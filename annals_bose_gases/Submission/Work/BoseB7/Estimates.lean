import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7.Q3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.Estimates` — the statements of FS §10

This module states, **relative to the `B4` Fock interface** (`FockData`) and one
parameter point (`Q3Env`), the three results of FS §10:

* `EstQ3one` — `lem:EstimatesOnQ3-js` `eq:EstimateQ3Tilde1`,
* `EstQ3twoThree` — `eq:EstimateQ3Tilde2+3`,
* `EstQ3four` — `eq:EstimateQ3Tilde4`,
* `Control3Q` — `thm:Control3Q` `eq:Q3Cancels`,

together with the explicit error functions `err1`, `err23`, `err4`, `controlErr`
of the paper (with FS's universal constant `C` left free, as in the paper) and
the *arithmetic* hypothesis `ErrDominated` — FS's "Theorem `thm:Control3Q`
follows by adding the estimates of Lemma `lem:EstimatesOnQ3-js`, using that the
`K`'s are larger than `1` and `con:KBellKM` to simplify the total remainder".

Everything is stated for a *fixed state* `Φ` in FS's spectral window
`eq:LocalizedAftercNumber` (`FockData.SpectLe E.bigM Φ`), with the errors
multiplied by `‖Φ‖² = F.bp Φ Φ` so that the statements are homogeneous (FS write
them for normalised `Φ`).

## The four statements in FS's notation

```
EstQ3one      : ⟨Φ, Q₃^(1)(z) + (1-𝓁²)(2π)⁻³ℓ³∫_{P_H}D_kb_k†b_k + Q₂^ex
                    + (b/100)(ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H) Φ⟩ ≥ -err1
EstQ3twoThree : ⟨Φ, Q₃^(2)(z) + Q₃^(3)(z) + 𝓁²(2π)⁻³ℓ³∫_{P_H}D_kb_k†b_k Φ⟩ ≥ -err23
EstQ3four     : ⟨Φ, Q₃^(4)(z) + ρ_z z Ŵ₁ω(0)(2π)⁻³∫χ̂²(s)(ã_s†+ã_s)ds
                    + (1/100)(b/ℓ²)n₊ Φ⟩ ≥ -err4
Control3Q     : ⟨Φ, (2π)⁻³ℓ³∫D_kb_k†b_k + Q₃(z) + Q₂^ex
                    + ρ_z z Ŵ₁ω(0)(2π)⁻³∫χ̂²(s)(ã_s†+ã_s)ds
                    + (b/50)(ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H) Φ⟩ ≥ -controlErr
```
(`P_H` here is FS's `{|k| ≥ ½K_H⁻¹a⁻¹}` — the *half* is FS's.)
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable (F : FockData Mode)

/-- The *quadratic form* of an operator at a state: `⟨Φ, X Φ⟩` (FS's notation).
Every estimate of §10 is an inequality between such numbers for a **fixed** `Φ`;
this is the reason the statements are `Φ`-first and the errors carry `‖Φ‖²`. -/
def qw (Φ : F.H) (X : F.H →ₗ[ℝ] F.H) : ℝ := F.bp (X Φ) Φ

/-- `‖Φ‖² = ⟨Φ,Φ⟩`, the normalisation in FS's estimates. -/
def normSq (Φ : F.H) : ℝ := F.bp Φ Φ

end FockData

section

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The error functions of FS §10 -/

/-- FS's `(μa³)^c`. -/
noncomputable def dil (E : Q3Env Mode) (c : ℝ) : ℝ := (E.mu * E.aScat ^ 3) ^ c

/-- FS `eq:EstimateQ3Tilde1`'s error bracket:

`C μ²aℓ³[ 𝓁K_ℓ^{-3/2}(μa³)^{1/4}(𝓜 + K_ℓ³K_L³)(K_ℓ^{-2}𝓁)^{(M-1)/2}
        + (μa³)^{1/2}K_ℓ^{-3}d^{-12}δ²(K_ℓ^{-2}𝓁)^{M-1} ]`.

(FS print the second inner factor as `K_ℓ^{-2}K_H²(μa³)^{1/6}`, which *is*
`K_ℓ^{-2}𝓁` when `K_H` is the tilde parameter, i.e. the same factor as in
`eq:DecayPH`; the chapter writes it in the unambiguous form `K_ℓ^{-2}𝓁`.) -/
noncomputable def err1 (E : Q3Env Mode) (C : ℝ) : ℝ :=
  C * (E.mu ^ 2 * E.aScat * E.ell ^ 3) *
    (E.lille * E.Kl ^ (-(3 / 2 : ℝ)) * dil E (1 / 4) * (E.bigM + E.Kl ^ 3 * E.KL ^ 3) *
        (E.Kl ^ (-(2 : ℝ)) * E.lille) ^ (((E.intM : ℝ) - 1) / 2) +
      dil E (1 / 2) * (E.Kl ^ (-(3 : ℝ)) * E.d ^ (-(12 : ℝ)) * E.delta ^ 2 *
        (E.Kl ^ (-(2 : ℝ)) * E.lille) ^ ((E.intM : ℝ) - 1)))

/-- FS `eq:EstimateQ3Tilde2+3`'s error bracket:

`C μ²aℓ³ (K_ℓ^{-2}𝓁)^{M̃} K_L³K_ℓ^{3/2}(μa³)^{1/4}`.

(FS write the exponent `M̃`; the chapter uses the one integer `E.intM`, which is
what `Basic.mValue` instantiates; the difference is absorbed by the free
constant `C` and is recorded in the `B8` arithmetic leg.) -/
noncomputable def err23 (E : Q3Env Mode) (C : ℝ) : ℝ :=
  C * (E.mu ^ 2 * E.aScat * E.ell ^ 3) *
    (E.Kl ^ (-(2 : ℝ)) * E.lille) ^ (E.intM : ℝ) * E.KL ^ 3 *
      E.Kl ^ (3 / 2 : ℝ) * dil E (1 / 4)

/-- FS `eq:EstimateQ3Tilde4`'s error bracket:

`Cρ_z²aℓ³√(𝓜/|z|²)[ K_H^{-1}(μa³)^{5/12} + (K_ℓK_L)^{-M}
    + K_ℓ^{3/2}K_L^{3/2}(K_ℓ^{-2}𝓁)^{(M-1)/2} ] + Cμ²aℓ³𝓁⁴ a/ℓ`. -/
noncomputable def err4 (E : Q3Env Mode) (C : ℝ) : ℝ :=
  C * (E.rho ^ 2 * E.aScat * E.ell ^ 3) *
      (Real.sqrt (E.bigM / E.z ^ 2) *
        (E.KH ^ (-(1 : ℝ)) * dil E (5 / 12) + (E.Kl * E.KL) ^ (-(E.intM : ℝ)) +
          E.Kl ^ (3 / 2 : ℝ) * E.KL ^ (3 / 2 : ℝ) *
            (E.Kl ^ (-(2 : ℝ)) * E.lille) ^ (((E.intM : ℝ) - 1) / 2)) +
        E.lille ^ 4 * E.aScat / E.ell) +
    C * (E.mu ^ 2 * E.aScat * E.ell ^ 3) * (E.lille ^ 4 * E.aScat / E.ell)

/-- FS `eq:Q3Cancels`'s error bracket:

`Cμ²aℓ³[ √(𝓜/|z|²)(K_H^{-1}(μa³)^{5/12} + (K_ℓK_L)^{-M} + K_ℓ³K_L³(K_ℓ^{-2}𝓁)^{(M-1)/2})
        + 𝓁⁴a/ℓ + (μa³)^{1/2}K_ℓ^{-3}d^{-12}δ²(K_ℓ^{-2}δ)^{M-1} ]`. -/
noncomputable def controlErr (E : Q3Env Mode) (C : ℝ) : ℝ :=
  C * (E.mu ^ 2 * E.aScat * E.ell ^ 3) *
    (Real.sqrt (E.bigM / E.z ^ 2) *
        (E.KH ^ (-(1 : ℝ)) * dil E (5 / 12) + (E.Kl * E.KL) ^ (-(E.intM : ℝ)) +
          E.Kl ^ 3 * E.KL ^ 3 * (E.Kl ^ (-(2 : ℝ)) * E.lille) ^ (((E.intM : ℝ) - 1) / 2)) +
      E.lille ^ 4 * E.aScat / E.ell +
      dil E (1 / 2) * (E.Kl ^ (-(3 : ℝ)) * E.d ^ (-(12 : ℝ)) * E.delta ^ 2 *
        (E.Kl ^ (-(2 : ℝ)) * E.delta) ^ ((E.intM : ℝ) - 1)))

/-- **FS's "adding the estimates" arithmetic**: the sum of the three error
brackets of `lem:EstimatesOnQ3-js` (with their constants `C1, C23, C4`) is
dominated by one `thm:Control3Q` bracket (with the constant `C`).  FS: "We have
used that the `K`'s are larger than `1` and `con:KBellKM` to simplify the total
remainder."  This is a *hypothesis* of the assembly `Control3Q_of_estimates`;
at FS's own parameters it is a theorem of real arithmetic
(`Work.BoseB7.ErrDominated_fsParams`, proved). -/
def ErrDominated (E : Q3Env Mode) (C1 C23 C4 C : ℝ) : Prop :=
  err1 E C1 + err23 E C23 + err4 E C4 ≤ controlErr E C

/-! ## 2. The kernel hypotheses shared by the estimates -/

/-- The hypotheses on the kernels that the proofs of `lem:EstimatesOnQ3-js` use:
the smallness `2|ℬ| ≤ 𝒜` (`eq:BoverA`), the squeezing bound `|α| ≤ 𝓁`
(`eq:alphaInPH`), evenness of the kernels, positivity/smallness of `f_L`, and
(the `B4` side) FS's commutator kernel `eq:Commutator_general` together with its
uniform bound `eq:Commutator`.

Everything here is either an FS assumption or a *consequence* of `sec:params`
plus `χ_Λ ∈ C_c^∞`; none of it is a mathematical input beyond what FS use. -/
structure EstHyp (F : FockData Mode) (E : Q3Env Mode) : Prop where
  /-- FS `eq:BoverA`: `|ℬ(k)/𝒜(k)| ≤ ½` for small `μ` (via `con:KLKH`). -/
  Bsmall : ∀ k : Mode, 2 * |E.B k| ≤ E.A k
  /-- FS `eq:alphaInPH`: `|α_k| ≤ 𝓁` on `P_H` (and everywhere the estimates use
  it; in FS this is `|ℬ/𝒜| ≤ C𝓁` plus the expansion of `√(1-x)`). -/
  alphaLe : ∀ k : Mode, |E.alpha k| ≤ E.lille
  /-- `α` is even (FS use `α_k = α_{-k}` throughout, e.g. in `eq:asInTermsOfbs`). -/
  alphaEven : ∀ k : Mode, E.alpha (-k) = E.alpha k
  /-- `f_L` is non-negative. -/
  fLnonneg : ∀ s : Mode, 0 ≤ E.fL s
  /-- `f_L ≤ 1` (it is a localisation of the low momenta). -/
  fLle_one : ∀ s : Mode, E.fL s ≤ 1
  /-- `f_L` is even. -/
  fLeven : ∀ s : Mode, E.fL (-s) = E.fL s
  /-- `χ̂²` is even (it is the Fourier transform of a radial `χ_Λ²`). -/
  hatChiSqEven : ∀ s : Mode, E.hatChiSq (-s) = E.hatChiSq s
  /-- `χ̂` is even. -/
  hatChiEven : ∀ s : Mode, E.hatChi (-s) = E.hatChi s
  /-- `Ŵ₁` is even. -/
  W1even : ∀ s : Mode, E.W1 (-s) = E.W1 s
  /-- `Ŵ₁ω` is even. -/
  W1omegaEven : ∀ s : Mode, E.W1omega (-s) = E.W1omega s
  /-- FS `eq:Commutator_general`: the `B4` commutator kernel is the box kernel
  `χ̂²(ℓ(k-k')) - χ̂(kℓ)χ̂(k'ℓ)`. -/
  hasKernel : ∀ i j : Mode, F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  /-- FS `eq:Commutator`: `[a_k,a_k†] ≤ 1` (uniformly, from
  `χ̂² ≤ 1` and the Cauchy–Schwarz inequality in the box). -/
  ccrBound : ∀ i j : Mode, |F.ccrK i j| ≤ 1
  /-- FS `eq:DefT`: `τ ≥ 0` (the localised kinetic symbol is non-negative). -/
  tauNonneg : ∀ k : Mode, 0 ≤ E.tau k
  /-- `𝒜 = τ + ρ_zŴ₁ ≥ 0` and in fact positive: the estimates divide by `𝒜`. -/
  Apos : ∀ k : Mode, 0 < E.A k
  /-- `ℓ > 0`, `μ > 0`, `a > 0`: the physical parameter range. -/
  ell_pos : 0 < E.ell
  mu_pos : 0 < E.mu
  a_pos : 0 < E.aScat
  /-- `z ≠ 0`: the `c`-number is non-zero (FS's `inf` over `z ∈ ℝ₊`; the
  statements below are for a fixed `z`). -/
  z_ne : E.z ≠ 0
  /-- `b ≥ 0`, `ε_T ≥ 0`: the gap terms are nonnegative. -/
  b_nonneg : 0 ≤ E.b
  eT_nonneg : 0 ≤ E.eT
  /-- `𝓜 ≥ 0`: the spectral window. -/
  bigM_nonneg : 0 ≤ E.bigM

/-! ## 3. The three estimates of `lem:EstimatesOnQ3-js` -/

/-- FS `eq:EstimateQ3Tilde1`:
`⟨Φ, Q₃^(1) + (1-𝓁²)(2π)⁻³ℓ³∫_{P_H}D_kb_k†b_k + Q₂^ex
   + (b/100)(ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H) Φ⟩ ≥ -err1 · ‖Φ‖²`
for every `Φ` in FS's spectral window `eq:LocalizedAftercNumber`. -/
def EstQ3one (F : FockData Mode) (E : Q3Env Mode) (C : ℝ) : Prop :=
  ∀ Φ : F.H, F.SpectLe E.bigM Φ →
    -(err1 E C) * F.normSq Φ ≤
      F.qw Φ (F.Q3one E +
        (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) + F.Q2ex E +
        (E.b / 100) • F.gapOp E)

/-- FS `eq:EstimateQ3Tilde2+3`:
`⟨Φ, Q₃^(2)(z) + Q₃^(3)(z) + 𝓁²(2π)⁻³ℓ³∫_{P_H}D_kb_k†b_k Φ⟩ ≥ -err23 · ‖Φ‖²`
for every `Φ` in the spectral window. -/
def EstQ3twoThree (F : FockData Mode) (E : Q3Env Mode) (C : ℝ) : Prop :=
  ∀ Φ : F.H, F.SpectLe E.bigM Φ →
    -(err23 E C) * F.normSq Φ ≤
      F.qw Φ (F.Q3two E + F.Q3three E +
        E.lille ^ 2 • F.dNumOpR E (F.PH E.KH E.aScat))

/-- FS `eq:EstimateQ3Tilde4`:
`⟨Φ, Q₃^(4)(z) + ρ_z z Ŵ₁ω(0)(2π)⁻³∫χ̂²(s)(ã_s†+ã_s)ds + (1/100)(b/ℓ²)n₊ Φ⟩
   ≥ -err4 · ‖Φ‖²`
for every `Φ` in the spectral window. -/
def EstQ3four (F : FockData Mode) (E : Q3Env Mode) (C : ℝ) : Prop :=
  ∀ Φ : F.H, F.SpectLe E.bigM Φ →
    -(err4 E C) * F.normSq Φ ≤
      F.qw Φ (F.Q3four E + F.linOp E +
        ((1 / 100 : ℝ) * (E.b * E.ell ^ (-(2 : ℝ)))) • F.nPlus)

/-! ## 4. FS `thm:Control3Q` -/

/-- **FS `thm:Control3Q`** (`eq:Q3Cancels`):
`⟨Φ, (2π)⁻³ℓ³∫D_kb_k†b_k + Q₃(z) + Q₂^ex
   + ρ_z z Ŵ₁ω(0)(2π)⁻³∫χ̂²(s)(ã_s†+ã_s)ds
   + (b/50)(ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H) Φ⟩ ≥ -controlErr · ‖Φ‖²`
for every `Φ` in the spectral window `eq:LocalizedAftercNumber`.

This is the *whole* content of FS §10 with respect to node `B7`: the quadratic
Bogoliubov operator `(2π)⁻³ℓ³∫D_kb_k†b_k` controls the cubic term `Q₃(z)`, the
`1Q` terms `Q₂^ex`, the linear term and the gap terms. -/
def Control3Q (F : FockData Mode) (E : Q3Env Mode) (C : ℝ) : Prop :=
  ∀ Φ : F.H, F.SpectLe E.bigM Φ →
    -(controlErr E C) * F.normSq Φ ≤ F.qw Φ (F.controlWord E)

/-! ## 5. Elementary consequences of the interface (proved here) -/

namespace FockData

open FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode}

/-- `𝒟_k ≥ 0` whenever `|ℬ_k| ≤ 𝒜_k` (FS `thm:BogHamDiag`'s `𝒟_k = ½(𝒜_k+√(𝒜_k²-ℬ_k²))`). -/
theorem Dcoef_nonneg {A B : ℝ} (hB : |B| ≤ A) : 0 ≤ Dcoef A B := by
  have h := Submission.BoseGases.bogS_nonneg A B
  have hA : 0 ≤ A := le_trans (abs_nonneg B) hB
  rw [Dcoef, Submission.BoseGases.bogD]
  linarith

/-- `α_k(𝒜_k + √(𝒜_k²-ℬ_k²)) = ℬ_k` at one mode (the `Q3Env` form of
`Work.BoseB7.alphaCoef_mul_denom`), the rewriting FS use in the proof of
`lem:EstimateIntegral`. -/
theorem alpha_mul_denom (E : Q3Env Mode) {k : Mode} (hA : 0 < E.A k)
    (hB : |E.B k| ≤ E.A k) :
    E.alpha k * (E.A k + Submission.BoseGases.bogS (E.A k) (E.B k)) = E.B k :=
  alphaCoef_mul_denom hA hB

end FockData

end

end Work.BoseB7
