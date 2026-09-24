import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.Statements

/-!
# The objects of GM §10 (Prop 10.1 assembly)

`Work.GM.S3.prop101_of_pieces` derives `S3Statement` from GM 7.2 (`Prop72Statement`), the two
`L²`/`L⁴` bounds for `R` (Lemmas 8.2, 8.3), the Fourier decay of `ψ₁|R̃|²` (Lemma 8.4) and GM 9.1
(`AffineStatement`).  This file fixes the objects appearing in that argument:

* `idx1 M₁`, `idxM M` -- the index sets of the sum in GM 7.2 (`M₁ < |m₁| ≤ 2M₁`, `M < |m| ≤ 2M`);
* `idxMpos M` -- its positive-`m₂` part (`M < m ≤ 2M`), which is the `m₂`-range of `affineSum`;
* `arg1`, `arg2` -- the two arguments of `R̃` in GM 10.1;
* `S30` -- the double sum `S₃,₀` of GM 10.1 (the right side of GM 7.2);
* `Gsum`, `S32` -- the sum `G(v) = Σ_m R̃(a₁)R̃(a₂)` and `S₃,₂ = ∫_{1/2}^2 G²`;
* `Asum`, `S33` -- `Σ_m R̃(a₁)²` and `S₃,₃ = ∫_{1/2}^2 (Σ_m R̃(a₁)²)²`;
* `Bsum`, `S34` -- `Σ_m R̃(a₂)²` and `S₃,₄ = ∫_{1/2}^2 (Σ_m R̃(a₂)²)²`;
* `AsumInv` -- the `u = 1/v` form of `Asum` (`Σ_m R̃((m₃u+m₁)/m₂)²`);
* `AsumPos`, `BsumPos`, `AsumInvPos` -- their `m₂ > 0` parts.

The two Cauchy–Schwarz steps of GM 10.1 are
`S30 ≤ (∫‖R‖²)^{1/2} S32^{1/2}` and `S32 ≤ S33^{1/2} S34^{1/2}`, and the two remaining bounds are
obtained from `hAff` applied to `f = ψ' · R̃²`, once the sums are recognized as `affineSum`s.
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun energy affineSum Separated)

noncomputable section

/-- The `m₁`-index set of GM 7.2 (`|m₁| ∼ M₁`): `M₁ < |m₁| ≤ 2 M₁`. -/
def idx1 (M₁ : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌊2 * M₁⌋) ⌊2 * M₁⌋).filter (fun m : ℤ => M₁ < |(m : ℝ)|)

/-- The `m₂`- and `m₃`-index set of GM 7.2 (`|m| ≍ M`): `M < |m| ≤ 2 M`. -/
def idxM (M : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌊2 * M⌋) ⌊2 * M⌋).filter (fun m : ℤ => M < |(m : ℝ)|)

/-- The positive part of `idxM`: `M < m ≤ 2 M`.  This is exactly the `m₂`-range of `affineSum`. -/
def idxMpos (M : ℝ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) ⌊2 * M⌋).filter (fun m : ℤ => M < (m : ℝ))

/-- GM 10.1, first argument of `R̃`: `(m₁ v + m₃)/(m₂ v)`. -/
def arg1 (m₁ m₂ m₃ : ℤ) (v : ℝ) : ℝ := ((m₁ : ℝ) * v + (m₃ : ℝ)) / ((m₂ : ℝ) * v)

/-- GM 10.1, second argument of `R̃`: `(m₁ v + m₃)/m₂`. -/
def arg2 (m₁ m₂ m₃ : ℤ) (v : ℝ) : ℝ := ((m₁ : ℝ) * v + (m₃ : ℝ)) / (m₂ : ℝ)

/-- `S₃,₀` of GM Prop 10.1: the sum produced by GM 7.2 (with smoothing frequency `N B`). -/
def S30 (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M, ∑ m₃ ∈ idxM M,
    ∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ *
      Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) * Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v)

/-- `G(v) = Σ_m R̃(a₁(m,v)) R̃(a₂(m,v))`, the inner sum of `S₃,₀`. -/
def Gsum (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M, ∑ m₃ ∈ idxM M,
    Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) * Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v)

/-- `S₃,₂ = ∫_{1/2}^2 G(v)² dv`. -/
def S32 (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) : ℝ :=
  ∫ v in (1 / 2 : ℝ)..2, (Gsum N W B M₁ M ψ₁ ψ₂ v) ^ 2

/-- `Σ_m R̃(a₁(m,v))²`. -/
def Asum (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M, ∑ m₃ ∈ idxM M,
    Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) ^ 2

/-- `Σ_m R̃(a₂(m,v))²`. -/
def Bsum (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M, ∑ m₃ ∈ idxM M,
    Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v) ^ 2

/-- `S₃,₃ = ∫_{1/2}^2 (Σ_m R̃(a₁(m,v))²)² dv`. -/
def S33 (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) : ℝ :=
  ∫ v in (1 / 2 : ℝ)..2, (Asum N W B M₁ M ψ₁ ψ₂ v) ^ 2

/-- `S₃,₄ = ∫_{1/2}^2 (Σ_m R̃(a₂(m,v))²)² dv`. -/
def S34 (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) : ℝ :=
  ∫ v in (1 / 2 : ℝ)..2, (Bsum N W B M₁ M ψ₁ ψ₂ v) ^ 2

/-- The `u = 1/v` form of `Asum`: `Σ_m R̃((m₃u + m₁)/m₂)²`. -/
def AsumInv (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M, ∑ m₃ ∈ idxM M,
    Rtilde W N B ψ₁ ψ₂ (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) ^ 2

/-- The `m₂ > 0` part of `AsumInv`. -/
def AsumInvPos (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M,
    Rtilde W N B ψ₁ ψ₂ (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) ^ 2

/-- The `m₂ > 0` part of `Asum`. -/
def AsumPos (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M,
    Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) ^ 2

/-- The `m₂ > 0` part of `Bsum`. -/
def BsumPos (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M,
    Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v) ^ 2

/-- The test function of GM 10.1: `f = ψ' · R̃²`, with `ψ'` a bump majorizing the support of `R̃²`
(playing the role of GM's `ψ₁` multiplying `|R̃|²`). -/
def testfun (N : ℕ) (W : Finset ℝ) (B : ℝ) (ψ₁ ψ₂ ψ' : ℝ → ℝ) : ℝ → ℝ :=
  fun u => ψ' u * RtildeSq W N B ψ₁ ψ₂ u

end

end Work.GM.S3
