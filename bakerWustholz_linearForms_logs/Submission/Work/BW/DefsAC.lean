import Mathlib
import Submission.Work.BW.ACBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! Definitions for the split of `analytic_core` (BW §14–20). Install as
`Submission/Work/BW/DefsAC.lean`, importing `Submission.Work.BW.analytic_core` (for `Qpoly`),
in `namespace Work.BW`. No `sorry`. Section, equation and page numbers are BW's
(Crelle 442, 1993). Throughout, BW's `·` in `7·2S'`, `9·274` etc. is a decimal point. -/

open Complex

/-! ### Parameters as functions of the data (`d = [K:ℚ]`). -/

/-- `d = [K:ℚ]`. -/
noncomputable abbrev dK (K : Type*) [Field K] [NumberField K] : ℕ := Module.finrank ℚ K

/-- `h = [h'(L) + v log 2]`. -/
noncomputable abbrev acH (K : Type*) [Field K] [NumberField K] {n : ℕ} (b : Fin n → ℤ) (v : ℕ) : ℕ :=
  ph (hL b (dK K)) v

/-- `S = 16 r d h` as a real number. -/
noncomputable abbrev acS (K : Type*) [Field K] [NumberField K] {n : ℕ} (r : ℕ) (b : Fin n → ℤ) (v : ℕ) : ℝ :=
  (pS r (dK K) (acH K b v) : ℝ)

/-- `D = 2 r^r (32d)^{r+1} log(2rd) σ₁⋯σ_r`. -/
noncomputable abbrev acD (K : Type*) [Field K] [NumberField K] {r : ℕ} (σ : Fin r → ℝ) : ℝ := pD r (dK K) σ

/-- `T = [11.75 r D]` as a real number. -/
noncomputable abbrev acT (K : Type*) [Field K] [NumberField K] {r : ℕ} (σ : Fin r → ℝ) : ℝ :=
  (pT r (dK K) σ : ℝ)

/-- `S^{(J)} = ξ^{-rJ} S` (BW p. 58). -/
noncomputable def SJ (K : Type*) [Field K] [NumberField K] {n : ℕ} (r : ℕ) (b : Fin n → ℤ) (v J : ℕ) : ℝ :=
  pxi r ^ (-((r * J : ℕ) : ℤ)) * acS K r b v

/-- `T^{(J)} = ξ^{rJ} T` (BW p. 58). -/
noncomputable def TJ (K : Type*) [Field K] [NumberField K] {r : ℕ} (σ : Fin r → ℝ) (J : ℕ) : ℝ :=
  pxi r ^ (r * J) * acT K σ

/-- BW's bound for the Kummer (2-adic) contribution after `J` descents (p. 58–59):
`2hJ(D₀+1) log 2 ≤ {0·044 J / log(2rd)} S D`. -/
noncomputable def kumJ (K : Type*) [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ) (v : ℕ) (σ : Fin r → ℝ)
    (J : ℕ) : ℝ :=
  0.044 * J / Real.log (2 * r * dK K) * acS K r b v * acD K σ

/-- `ln(p) = log max_λ |p(λ)|` at the embedding `φ` (BW (13)). -/
noncomputable def lnp {K : Type*} [Field K] {ι' : Type*} [Fintype ι'] (φ : K →+* ℂ)
    (p : ι' → K) : ℝ :=
  Real.log (⨆ i, ‖φ (p i)‖)

/-! ### Points and auxiliary functions (BW §14). -/

/-- The point `(z, e^{zℓ₁}, …, e^{zℓ_r})` for complex `z`. -/
noncomputable def ptC {r : ℕ} (ℓ : Fin r → ℂ) (z : ℂ) : Fin (r + 1) → ℂ :=
  Fin.cons z (fun i => Complex.exp (z * ℓ i))

/-- `z ↦ P(z, e^{zℓ₁}, …)`. With `ℓ = lamP` this is BW's `g`, with `ℓ = ellM` BW's `f`. -/
noncomputable def fAt {r : ℕ} (ℓ : Fin r → ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ) (z : ℂ) : ℂ :=
  MvPolynomial.eval (ptC ℓ z) P

/-- BW §14: `M_j = L_j − b_k^{-1}(∂L_j/∂z_k) L` on the line `z_i = 2^{-v} z log α_i`, divided by
`z`: `log α'_j − (L_{jk}/b_k) 2^{-v} Λ`. -/
noncomputable def ellM {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (k : Fin n) (v : ℕ) (L : Fin r → Fin n → ℤ) (j : Fin r) : ℂ :=
  lamP φ α v L j - ((L j k : ℂ) / (b k : ℂ)) * ((2 : ℂ) ^ v)⁻¹ * lam φ α b

/-! ### The descended polynomials (BW §20). -/

/-- `Q^{(J)}` with accumulated parity residue `μ` (`0 ≤ μ_j < 2^J`): the terms of `Q(t)` with
`λ_j ≡ μ_j (mod 2^J)`, with `Y_j^{λ_j}` replaced by `Y_j^{⌊λ_j/2^J⌋}` and `Y₀` by `2^{-J}Y₀`.
Iterating BW's (28) with `X₀ = ½Y₀^{(1)}`, `X_j = Y_j^{(1)}` gives exactly these polynomials:
choosing `ε` at step `J+1` means `μ ↦ μ + 2^J ε`. `Qdesc 0 0 = Qpoly` (node `Qdesc_zero`). -/
noncomputable def Qdesc {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ lm : AuxIdx r h D0 Dj,
    if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
      MvPolynomial.C (φ (p lm) *
          (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0)
        * Polynomial.aeval
            (MvPolynomial.C (((2 : ℂ) ^ J)⁻¹) * MvPolynomial.X 0 + MvPolynomial.C ((lm.1 : ℕ) : ℂ))
            (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1)))
        * ∏ j : Fin r, MvPolynomial.X j.succ ^ ((lm.2.2 j : ℕ) / 2 ^ J)
    else 0

/-- `Q^{(J)}_μ(·; t)` with the parameters of `analytic_core` (`h`, `D₀`, `D_j` from `Defs`). -/
noncomputable abbrev QJ {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (v : ℕ) (σ : Fin r → ℝ)
    (p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K) (J : ℕ) (μ : Fin r → ℕ)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) : MvPolynomial (Fin (r + 1)) ℂ :=
  Qdesc φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t

/-- BW's `g^{(J)}(z; t) = Q^{(J)}(z, α'^z; t)` (determinations of `α'^z` from `lamP`). -/
noncomputable abbrev acg {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (v : ℕ)
    (σ : Fin r → ℝ) (p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K)
    (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (z : ℂ) : ℂ :=
  fAt (fun j => lamP φ α v L j) (QJ φ b k L ι v σ p J μ t0 t) z

/-- BW's `f^{(J)}(z; t) = Q^{(J)}(z, e^{zM₁}, …; t)`. -/
noncomputable abbrev acf {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (v : ℕ)
    (σ : Fin r → ℝ) (p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K)
    (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (z : ℂ) : ℂ :=
  fAt (ellM φ α b k v L) (QJ φ b k L ι v σ p J μ t0 t) z

/-- BW §17: `f_m(z) = (1/m!) (d/dz)^m f(z)`. -/
noncomputable def taylorC (f : ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv m f z / (m.factorial : ℂ)

/-- Vanishing of a `t`-family `Qf` at the points `(s/q, e^{(s/q)ℓ})`, `s ∈ pts`, for all
`t₀ + ⋯ + t_{r-1} ≤ Tt`. -/
def VanSet {r : ℕ} (ℓ : Fin r → ℂ) (Qf : ℕ → (Fin (r - 1) → ℕ) → MvPolynomial (Fin (r + 1)) ℂ)
    (pts : Set ℤ) (q : ℕ) (Tt : ℝ) : Prop :=
  ∀ s ∈ pts, ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ), ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tt →
    fAt ℓ (Qf t0 t) ((s : ℂ) / (q : ℂ)) = 0

/-- `{s ∈ ℤ : |s| ≤ X}`. -/
def ballZ (X : ℝ) : Set ℤ := {s | ((|s| : ℤ) : ℝ) ≤ X}

/-- `{s ∈ ℤ : s odd, |s| ≤ X}`. -/
def oddBallZ (X : ℝ) : Set ℤ := {s | Odd s ∧ ((|s| : ℤ) : ℝ) ≤ X}

/-! ### Blaschke products (BW §18). -/

/-- `β(z; k) = R(z − k)/(R² − kz)`. -/
noncomputable def bfac (R : ℝ) (k : ℤ) (z : ℂ) : ℂ :=
  ((R : ℂ) * (z - k)) / ((R : ℂ) ^ 2 - (k : ℂ) * z)

/-- `B(z; X) = ∏_{|k| ≤ X} β(z; k)`. -/
noncomputable def bprod (R : ℝ) (X : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ Finset.Icc (-(X : ℤ)) X, bfac R k z

/-- The lacunary product `B'(z; X) = ∏_{|k| ≤ X, k odd} β(z; k)` (`X` even). -/
noncomputable def bprodOdd (R : ℝ) (X : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ (Finset.Icc (-(X : ℤ)) X).filter Odd, bfac R k z

/-! ### The hypotheses of `analytic_core`, bundled. -/

/-- All hypotheses of `analytic_core` (BW §11–13: standing assumptions, `BH` at `r`, `ι`, and a
nonzero `p` with (9), (12), (10)). -/
structure ACHyp {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K)
    (σ : Fin r → ℝ) (ι : Fin (r - 1) → Fin n)
    (p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K) : Prop where
  hst : Standing φ α b k c
  hr : 2 ≤ r
  hBH : BH φ α b v c r L α' σ
  hι : IotaOK b k L ι
  hp0 : p ≠ 0
  hp9 : ∀ (s : ℤ), |s| ≤ (pS r (dK K) (acH K b v) : ℤ) → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
    t0 + ∑ m, t m ≤ pT r (dK K) σ →
    Qval φ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p t0 t s = 0
  hp12 : Height.logHeight p ≤ 0.85 * acS K r b v * acD K σ
  h10 : Real.log ‖lam φ α b‖ ≤ -(9 * 2 ^ r * acS K r b v * acD K σ)

end Work.BW
