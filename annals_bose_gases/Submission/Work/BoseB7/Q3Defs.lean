import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7.Coef
import Submission.Work.BoseB7.FockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.Q3Defs` — the `3Q` word of FS §10

FS `thm:Control3Q` and `lem:EstimatesOnQ3-js` are statements about five operators
on the mode lattice:

* `Q3(z)` (FS `eq:kroelleQ3z`):
  `ℓ³(2π)^{-6} z ∬_{k ∈ P_H} f_L(s) Ŵ₁(k)(ã_s†a_{s-k}a_k + a_k†a_{s-k}†ã_s)`,
* its four pieces `Q3^(1) … Q3^(4)` of `lem:EstimatesOnQ3-js`, obtained from the
  FS substitution `a_k = (b_k - α_k b_{-k}†)/(1-α_k²)`,
* the diagonalised Bogoliubov quadratic `(2π)^{-3}ℓ³∫_R 𝒟_k b_k†b_k dk`,
* `Q2^ex`, the linear term `ρ_z z Ŵ₁ω(0)(2π)^{-3}∫χ̂²(s)(ã_s†+ã_s)ds`, and the
  gap terms `ℓ^{-2}n₊ + ε_T(dℓ)^{-2}n₊^H`.

All `(2π)^{-3}ℓ³∫dk` are the *normalised sums* over the mode lattice, so on
`FockData` the words are finite sums (`FockData.regionSum`).  The scalar data of
one parameter point (FS's `z, ℓ, μ, a, K_H, K_L, d, s, ε_T, b, M, ρ_z, 𝓜, 𝓁, δ`
and the mode-indexed kernels `f_L, Ŵ₁, Ŵ₁ω, χ̂, χ̂², τ, 𝒜, ℬ`) is bundled in
`Q3Env`; `𝒟` and `α` are *derived* from `𝒜, ℬ` (`Work.BoseB7.Coef`), so the
chapter cannot disagree with FS (or with `B6`) about them.

## The `* + h.c.` convention

Every piece `Q3^(j)` is `coef • (T + T†)` with `T†` written out explicitly as the
formal adjoint word (`a† ↔ a`, reversed order); the only exception is `Q3^(4)`,
which FS write without `h.c.` (it is self-adjoint by construction).

## Notation

Every declaration takes the `FockData` `F` as its first argument (used by field
notation, `F.Q3 E`) and the environment `E : Q3Env Mode` as its second.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The scalar data of one parameter point of FS §10.**  `𝒜, ℬ` are the
mode-indexed kernels `𝒜(k) = τ(k) + ρ_zŴ₁(k)`, `ℬ(k) = ρ_zŴ₁(k)`; everything else
is a number or a mode-indexed kernel.  `𝒟` and `α` are derived from `𝒜, ℬ`. -/
structure Q3Env (Mode : Type*) [AddCommGroup Mode] [Fintype Mode] where
  /-- FS's `c`-number `z` (`thm:Kafz`). -/
  z : ℝ
  /-- FS's box side `ℓ` (`eq:def_ell`). -/
  ell : ℝ
  /-- FS's chemical potential `μ`. -/
  mu : ℝ
  /-- FS's scattering length `a`. -/
  aScat : ℝ
  /-- FS's `K_H` (`sec:params`), whose inverse is the `P_H` cutoff. -/
  KH : ℝ
  /-- FS's `K_ℓ` (`sec:params`); it enters the box side `ℓ = K_ℓ(μa)^{-1/2}` and
  every error term of `lem:EstimatesOnQ3-js` through `K_ℓ^{-2}𝓁`. -/
  Kl : ℝ
  /-- FS's `K_L = (K_ℓd²)^{-1}` (`eq:KL_d`). -/
  KL : ℝ
  /-- FS's `d`. -/
  d : ℝ
  /-- FS's `s`. -/
  s : ℝ
  /-- FS's `ε_T`. -/
  eT : ℝ
  /-- FS's universal gap coefficient `b` of `eq:DefT`. -/
  b : ℝ
  /-- FS's regularity integer `M` of the localisation function. -/
  intM : ℕ
  /-- FS's `𝓜` (`eq:DefM`). -/
  bigM : ℝ
  /-- FS's `δ` of §9, entering the errors of `eq:EstimateQ3Tilde1`. -/
  delta : ℝ
  /-- FS's low-momentum localisation `f_L(s)`. -/
  fL : Mode → ℝ
  /-- FS's `Ŵ₁(k)` (the even, decaying potential kernel). -/
  W1 : Mode → ℝ
  /-- FS's `Ŵ₁ω(k)`. -/
  W1omega : Mode → ℝ
  /-- FS's `Ŵ₁ω(0)` (the value at the origin, which is what `lem:EstimateIntegral`
  compares the `P_H`-integral `(2π)^{-3}∫Ŵ₁(k)α_k dk` with). -/
  W1omega0 : ℝ
  /-- The mode-indexed `χ̂` (`χ̂(ℓk)`). -/
  hatChi : Mode → ℝ
  /-- The mode-indexed `χ̂²`, the Fourier transform of `χ_Λ²` (`χ̂²(ℓ(k-k'))`). -/
  hatChiSq : Mode → ℝ
  /-- FS `def:tau`, the kinetic symbol, as a function of the mode. -/
  tau : Mode → ℝ
  /-- FS's `𝒜(k) = τ(k) + ρ_zŴ₁(k)`. -/
  A : Mode → ℝ
  /-- FS's `ℬ(k) = ρ_zŴ₁(k)`. -/
  B : Mode → ℝ

namespace Q3Env

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Q3Env Mode)

/-- FS `thm:Kafz`: the substituted condensate density `ρ_z = z²/ℓ³` (derived from
`z` and `ℓ`, not independent data). -/
noncomputable def rho : ℝ := rhoZ E.z E.ell

/-- FS `eq:DefLille`: `𝓁 = (μa³)^{1/6}K_H²` (derived, cf. `Work.BoseB7.lille`). -/
noncomputable def lille : ℝ := Work.BoseB7.lille E.mu E.aScat E.KH

/-- FS `thm:BogHamDiag`: `𝒟_k = ½(𝒜_k + √(𝒜_k²-ℬ_k²))`, derived from `𝒜, ℬ`. -/
noncomputable def D (k : Mode) : ℝ := Dcoef (E.A k) (E.B k)

/-- FS `thm:BogHamDiag`: `α_k = ℬ_k/(𝒜_k + √(𝒜_k²-ℬ_k²))`, derived from `𝒜, ℬ`. -/
noncomputable def alpha (k : Mode) : ℝ := alphaCoef (E.A k) (E.B k)

/-- The common denominator `((1-α_k²)(1-α_{s-k}²))^{-1}` of the four pieces of
`lem:EstimatesOnQ3-js`. -/
noncomputable def q3Denom (s k : Mode) : ℝ :=
  1 / ((1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2))

end Q3Env

namespace FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable (F : FockData Mode)

instance regionDecidable (ell d : ℝ) : DecidablePred ((nPlusHRegion ell d) ∘ F.kmom) :=
  fun i => decidable_of_iff (1 / (d ^ 2 * ell) ≤ ‖F.kmom i‖) Iff.rfl

/-! ## 1. The `3Q` monomials -/

/-- `ã_s† a_{s-k} a_k`, the cubic monomial of FS `eq:kroelleQ3z`. -/
def qterm (s k : Mode) : F.H →ₗ[ℝ] F.H := F.aDag s ∘ₗ (F.a (s - k) ∘ₗ F.a k)

/-- Its formal adjoint `a_k† a_{s-k}† ã_s`. -/
def qtermDag (s k : Mode) : F.H →ₗ[ℝ] F.H := F.aDag k ∘ₗ (F.aDag (s - k) ∘ₗ F.a s)

/-- The `P_H` mode set of the `3Q` sum (FS's `P_H`), restricted to the excited
modes. -/
def PHset (E : Q3Env Mode) : Finset Mode := (excited Mode).filter (F.PH E.KH E.aScat)

/-- FS `eq:kroelleQ3z`: `Q3(z) = ℓ³(2π)^{-6}z∬_{k∈P_H}f_L(s)Ŵ₁(k)(ã_s†a_{s-k}a_k + h.c.)`,
with `(2π)^{-3}ℓ³∫dk → ∑_k` (so `ℓ³(2π)^{-6}∬ → ℓ^{-3}∑_s∑_k`). -/
def Q3 (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) •
    ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
      (E.fL s * E.W1 k) • (F.qterm s k + F.qtermDag s k)

/-! ## 2. The four pieces of `lem:EstimatesOnQ3-js` -/

/-- `ã_s† b_{s-k} b_k` (FS `Q3^(1)`, first term). -/
def T1a (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.aDag s ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ F.bOp E.alpha k)

/-- `ã_s† b_{k-s}† b_{-k}†` (FS `Q3^(1)`, second term). -/
def T1b (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.aDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOpDag E.alpha (-k))

/-- The formal adjoint of `T1a`. -/
def T1aDag (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOpDag E.alpha k ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ F.a s)

/-- The formal adjoint of `T1b`. -/
def T1bDag (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOp E.alpha (-k) ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ F.a s)

/-- FS `lem:EstimatesOnQ3-js`: `Q3^{(1)}(z)`, the `b b` and `b† b†` pieces
(together with their adjoints):

  `(2π)^{-6}zℓ³∬ f_L(s)Ŵ₁(k)((1-α_k²)(1-α_{s-k}²))^{-1}
     (ã_s†b_{s-k}b_k + α_kα_{s-k}ã_s†b_{k-s}†b_{-k}† + h.c.)`.

Note the factor `α_kα_{s-k}` on the `b† b†` pair: it is FS's, and it is exactly
what the substitution `a_k = (b_k - α_kb_{-k}†)/(1-α_k²)` produces (`T1b` and
`T1bDag` carry it, `T1a`, `T1aDag` do not). -/
def Q3one (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) •
    ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
      (E.fL s * E.W1 k * E.q3Denom s k) •
        (F.T1a E s k + (E.alpha k * E.alpha (s - k)) • F.T1b E s k +
          F.T1aDag E s k + (E.alpha k * E.alpha (s - k)) • F.T1bDag E s k)

/-- `ã_s† b_{-k}† b_{s-k}` (FS `Q3^(2)`). -/
def T2 (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.aDag s ∘ₗ (F.bOpDag E.alpha (-k) ∘ₗ F.bOp E.alpha (s - k))

/-- The formal adjoint of `T2`. -/
def T2Dag (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOpDag E.alpha (s - k) ∘ₗ (F.bOp E.alpha (-k) ∘ₗ F.a s)

/-- FS `lem:EstimatesOnQ3-js`: `Q3^{(2)}(z)`. -/
def Q3two (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) •
    ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
      (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)) • (F.T2 E s k + F.T2Dag E s k)

/-- `ã_s† b_{k-s}† b_k` (FS `Q3^(3)`). -/
def T3 (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.aDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOp E.alpha k)

/-- The formal adjoint of `T3`. -/
def T3Dag (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOpDag E.alpha k ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ F.a s)

/-- FS `lem:EstimatesOnQ3-js`: `Q3^{(3)}(z)`. -/
def Q3three (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) •
    ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
      (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k)) •
        (F.T3 E s k + F.T3Dag E s k)

/-- The squeezed commutator `[b_{s-k}, b_{-k}†]` (FS's fourth piece). -/
def bCommutator (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOp E.alpha (s - k) ∘ₗ F.bOpDag E.alpha (-k) -
    F.bOpDag E.alpha (-k) ∘ₗ F.bOp E.alpha (s - k)

/-- **The linear weight of `Q₃⁽⁴⁾` at the mode `s`** (kernel form):
`Σ_{k∈P_H} (ccrK (s−k) (−k) − α_{s−k}α_{−k}ccrK k (k−s))·(−f_L(s)Ŵ₁(k)α_kq3Denom s k)`.
By `Q3four_eq_linear` the operator `Q₃⁽⁴⁾` is the linear combination
`(z/ℓ³)Σ_s q3fourWeight s • (ã_s†+ã_s)`; FS's `EstQ3four` compares the `k`-sum
with the coefficient `ρ_zzŴ₁ω(0)` of `linOp` (`lem:EstimateIntegral`). -/
noncomputable def q3fourWeight (E : Q3Env Mode) (F : FockData Mode) (s : Mode) : ℝ :=
  ∑ k ∈ F.PHset E,
    ((F.ccrK (s - k) (-k) - E.alpha (s - k) * E.alpha (-k) * F.ccrK k (k - s)) *
      (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)))

/-- The same weight after the FS `eq:Commutator_general` substitution, i.e. FS's
`eq:1Q-integral`/`eq:1Q-integral2` decomposition
`(1−α_{s−k}α_{−k})χ̂²(s) − χ̂(s−k)χ̂(−k) + α_{s−k}α_{−k}χ̂(k)χ̂(k−s)`
(`Q3four_weight_eq`). -/
noncomputable def q3fourWeightSplit (E : Q3Env Mode) (F : FockData Mode) (s : Mode) : ℝ :=
  ∑ k ∈ F.PHset E,
    (((1 - E.alpha (s - k) * E.alpha (-k)) * E.hatChiSq s
        - E.hatChi (s - k) * E.hatChi (-k)
        + E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))) *
      (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)))

/-- FS `lem:EstimatesOnQ3-js`: `Q3^{(4)}(z)`, the commutator piece
`(2π)^{-6}zℓ³∬ f_L(s)Ŵ₁(k)(-α_k/((1-α_k²)(1-α_{s-k}²)))[b_{s-k},b_{-k}†](ã_s†+ã_s)`. -/
def Q3four (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) •
    ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
      (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)) •
        (F.bCommutator E s k ∘ₗ (F.aDag s + F.a s))

/-! ## 3. The remaining operators of `eq:Q3Cancels` -/

/-- The diagonalised Bogoliubov quadratic on the region `R`:
`(2π)^{-3}ℓ³∫_R 𝒟_k b_k†b_k dk`. -/
def dNumOpR (E : Q3Env Mode) (R : Mode → Prop) [DecidablePred R] : F.H →ₗ[ℝ] F.H :=
  F.regionSum R E.D (F.bNumOp E.alpha)

/-- FS `eq:Kz`: `Q2^ex = (2π)^{-3}ρ_zℓ³∫(Ŵ₁ω(k)+Ŵ₁ω(0))a_k†a_k dk`. -/
def Q2ex (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  ∑ k ∈ excited Mode, (E.rho * (E.W1omega k + E.W1omega0)) • F.nOp k

/-- The linear operator of `eq:Q3Cancels`,
`ρ_z z Ŵ₁ω(0)(2π)^{-3}∫χ̂²(s)(ã_s†+ã_s)ds`. -/
def linOp (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.rho * E.z * E.W1omega0) • ∑ s ∈ excited Mode, (E.hatChiSq s) • (F.aDag s + F.a s)

/-- FS §7's `n₊^H = Σ Q 1_{(d⁻²ℓ⁻¹,∞)}(√-Δ) Q`: the number of particles with
momentum above `(d²ℓ)⁻¹`. -/
def nPlusH (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  F.regionSum ((nPlusHRegion E.ell E.d) ∘ F.kmom) (fun _ => 1) F.nOp

/-- FS's gap word `ℓ^{-2}n₊ + ε_T(dℓ)^{-2}n₊^H` of `eq:DefT`/`eq:Q3Cancels`. -/
def gapOp (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  E.ell ^ (-(2 : ℝ)) • F.nPlus +
    (E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) • F.nPlusH E

/-- **FS `eq:Q3Cancels`'s left-hand side** (the operator that `thm:Control3Q`
bounds from below):

  `(2π)^{-3}ℓ³∫𝒟_kb_k†b_k dk + Q3(z) + Q2^ex
    + ρ_z z Ŵ₁ω(0)(2π)^{-3}∫χ̂²(s)(ã_s†+ã_s)ds
    + (b/50)(ℓ^{-2}n₊ + ε_T(dℓ)^{-2}n₊^H)`.

(FS's `thm:Control3Q` writes `b_k` with the `c`-number shift `c_k`; the estimates
of `lem:EstimatesOnQ3-js` are proved for the unshifted `b_k = a_k + α_ka_{-k}†`,
which is what the chapter uses everywhere.  The shift contributes only linear
terms, recorded in `Coef.cCoef`.) -/
def controlWord (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  F.dNumOpR E (fun _ => True) + F.Q3 E + F.Q2ex E + F.linOp E +
    ((E.b / 50) • F.gapOp E)

end FockData

end Work.BoseB7
