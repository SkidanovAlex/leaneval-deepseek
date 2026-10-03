/-
# `Work.FIArea7.Prop172Classical` — *FI* Proposition 17.2 (17.18) in the paper's own form

This file fixes the **paper's** statement of *FI* Proposition 17.2 — the deep input of area 7 — in
the form in which the paper proves and uses it, namely for the **moment-free** coefficient (17.15)

  `β_z = p(n) μ(n) γ(n; C)`,   `n = |z|²`,

over the annulus `N < |z|² ≤ (1+θ)N` (no angular mollifier, no sector support: both were removed in
*FI* §16/§17 by the Fourier expansion (16.27) of the angle mollifier `q`), and for an arbitrary
frequency `m`:

  (17.14)  `S^m_χ(β') = Σ^∧_{(z,Π)=1} β_z [z] χ(z) (z/|z|)^m`,

  (17.18)  `S^m_χ(β') ≪ N^{1-δ}`  uniformly in `d(|m|+1) ≤ N^δ`,

`d` being the modulus of the character `χ` of the Hecke character (17.17).  The sector of the
polar box (5.14) is *not* part of the coefficient here: as `NOTES.md` §60 records, the round-6
coefficient `IsBetaCoeff6` carries the angular mollifier `q(α)` and the sector support, and §17 of
the paper turns both into the free frequency `m = k + ℓ` of the Fourier expansion of `q`; the
per-mode statement is therefore the one below, with the *frequency* as a parameter.

The proof is *FI* §25 (`S^m_χ(β') = Σ_{(n,Π)=1} g(n)μ(n)γ(n)λ(n)` — the reduction to the quadratic
eigenvalue (23.1) — then the combinatorial identity (24.13) and the estimates of `T(c,d)`, `T(c)`,
`S(c)`) together with *FI* §26 (Theorem 2ψ, from Vaughan's identity, Lemma 26.1 and Props. 23.1,
23.2).  The classical inputs themselves are stated in `Classical172Defs.lean`.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.UniMollify6

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The coefficient (17.15)**: `β_z = p(|z|²)·μ(|z|²)·γ(|z|²;C)` for primary `z` free of small
primes (5.3)/(5.8), and `0` otherwise.  This is `IsBetaCoeff6`'s coefficient *without* the angular
mollifier `q(arg z − φ)`. -/
def radBeta (Pa : Work.FITop.Params) (P : ℝ → ℝ) (Cc : ℝ) (z : GaussianInt) : ℂ :=
  if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
    ((P (Work.FIPlan.gnorm z) : ℝ) : ℂ)
      * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
      * ((Work.FIPlan.gammaTrunc Cc (Work.FIPlan.gnorm z) : ℝ) : ℂ)
  else 0

/-- **(17.14)**: `S^m_χ(β') = Σ^∧_{(z,Π)=1} β_z [z] χ(z) (z/|z|)^m` with the coefficient (17.15)
of `radBeta`.  The sum runs over the box `gBox (radN Pa)`; `β` vanishes off the annulus
`N < |z|² ≤ (1+θ)N` by the hypotheses on `P`. -/
def SChiRad (Pa : Work.FITop.Params) (P : ℝ → ℝ) (Cc : ℝ) (chi : GaussianInt → ℂ)
    (m : ℤ) : ℂ :=
  ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
    radBeta Pa P Cc z * JKSym z * chi z * uniPow z m

/-- ***FI* Proposition 17.2 / (17.18), in the paper's form.**  For every `η ∈ (0, 3/32)` there are
`δ₁ > 0`, `c₁ > 0` and a threshold `x₀` such that for every admissible datum `Pa` with
`Pa.x ≥ x₀` and `Pa.η = η`, every radial mollifier `P` supported on `N < u ≤ (1+θ)N` with the
§7 derivative bounds `|P^{(j)}| ≤ c_j (θN)^{-j}` (`j ≤ 2`), every truncation
`1 ≤ C ≤ N^{1-η}` (25.2), every character `χ` of modulus `4d` (`‖χ‖ ≤ 1`, multiplicative on
coprime arguments, `4d`-periodic) and every frequency `m` with `d(|m|+1) ≤ N^{δ₁}`,

  `‖S^m_χ(β')‖ ≤ c₁ N^{1-δ₁}`.

This is the *only* place in area 7 where the deep *FI* §§19–26 input is consumed; it is proved from
`Prop231`, `Prop232` and `Theorem2psi` (the classical inputs of `Classical172Defs.lean`) by *FI* §25
together with *FI* §26. -/
def Prop172Classical : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ δ₁ c₁ x0 : ℝ, 0 < δ₁ ∧ 0 < c₁ ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
    ∀ (P : ℝ → ℝ) (Cc : ℝ) (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ),
      ContDiff ℝ 2 P →
      (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
      (∀ u, P u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) →
      (∀ j : ℕ, j ≤ 2 → ∀ u : ℝ,
        |iteratedDeriv j P u| ≤ Work.FITop4.cMoll j * (Pa.θ * Pa.N) ^ (-(j : ℝ))) →
      1 ≤ Cc → Cc ≤ Pa.N ^ (1 - η) →
      1 ≤ d →
      (∀ z, ‖chi z‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
      (∀ (a b' : ℤ), chi (⟨a + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a, b'⟩) →
      (∀ (a b' : ℤ), chi (⟨a, b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a, b'⟩) →
      (d : ℝ) * (|(m : ℝ)| + 1) ≤ Pa.N ^ δ₁ →
      ‖SChiRad Pa P Cc chi m‖ ≤ c₁ * Pa.N ^ (1 - δ₁)

end

end Work.FIArea7
