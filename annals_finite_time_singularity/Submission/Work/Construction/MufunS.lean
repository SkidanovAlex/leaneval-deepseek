/-
# `Construction.MufunS` — the corrected modulation constant `μ` (sign fix, option (a′))

The ruling `Submission/Work/FTS/FTS_MUFUN_SIGN.md` §5 fixes the sign of the transport zero-mode
in the modulation constant of Elgindi's §Modulation.  For

  `𝓛_Γ^T(g) = 𝓛_Γ g − T g + AK·L₁₂(T g)(0)   (T g = Coercivity.Transport g = 3 D_θ g/(1+z))`

(`Construction.LGammaT_eq`) the paper's `g`-equation `gEquationFinal` closes only when

  `2αμ = μ̄ + L₁₂(Transport g)(0)`,   `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)`,

whereas the definition `Construction.mufun` carries the opposite sign of the transport term
(the sign of the paper's own display at tex 1380), i.e. `2αμ = μ̄ − L₁₂(Transport g)(0)`.  The
two agree exactly when the transport zero-mode vanishes — a condition that is false in general
(`FTS_MUFUN_SIGN.md` §3), so the delivered modulation constant solves a *different* PDE.

This module provides the **corrected** constant `mufunS`, its defining identity `two_mul_mufunS`,
and the reduction `mufunS_eq_mufun_neg` which lets every existing *generic* estimate about
`mufun` be reused at the flipped profile `−g` (so none of them has to be re-proved from the
explicit formula).  The file imports `Construction.Defs` only, and it modifies no live file: the
coordinated rebuild (which replaces `Galerkin.muDyn` and `Apriori.muOf` by `mufunS`) is the
lead's, serialized step — see `Submission/Work/FTS/MuFix/APPLY.md`.

## Conventions of the file

* `L12` is `Work.Construction.L12` (= `Work.FM.L12 Spaces.K`), the paper's
  `L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds`, and `f ↦ L₁₂(f)(0)` is the linear
  functional whose zero-mode governs the transport defect.
* `L12_neg` / `L12_transport_neg` are stated *unconditionally* (no integrability hypotheses):
  they are `deriv_neg` for `∂_θ` (and `D_θ = sin(2θ)∂_θ` commutes with the pointwise sign) plus
  `L₁₂`-linearity in the profile (`FM.L12_const_mul` at `c = −1`).
* `two_mul_mufunS` and `mu_bound_mulS` are the two facts the rebuild consumes: the first is the
  defining relation of `μ` (it is what makes `DynEqF` hold with no `L₁₂`-zero-mode hypothesis),
  the second is `Work.FTS.Nonlin.mu_bound_mul` transported to `mufunS`.
* **Never** unfold `mufun`, `mufunS`, `Galerkin.muDyn` or `Apriori.muOf` by `rfl` into the
  explicit `L₁₂`-formula downstream: go through `two_mul_mufunS`, `mufunS_eq_mufun_neg` and the
  `|·|`-bounds.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## The corrected modulation constant -/

/-- **The corrected modulation constant `μ` of the modulation problem** (ruling
`FTS_MUFUN_SIGN.md` §5, option (a′)):

  `mufunS α N₀ N g = (1/(2α))(L₁₂(N₀)(0) + L₁₂(N)(0)) + (1/(2α)) L₁₂(3 D_θ g/(1+z))(0)`,

i.e. `2α · mufunS = μ̄ + L₁₂(Transport g)(0)` (`two_mul_mufunS`) — the sign forced by
`LGammaT_eq` and the paper's `gEquationFinal`.  It differs from `Construction.mufun` only in the
sign of the transport zero-mode (`mufunS_eq_mufun_neg`: `mufunS α N₀ N g = mufun α N₀ N (−g)`).

`mufunS` is the constant that `Galerkin.muDyn` and `Apriori.muOf` become in the coordinated
rebuild; `Construction.mufun` is retained (unchanged, so that its ~10⁴ importers keep building)
as the paper-display variant and is *superseded*. -/
def mufunS (α : ℝ) (N0v Nv g : ℝ → ℝ → ℝ) : ℝ :=
  (1 / (2 * α)) * (L12 N0v 0 + L12 Nv 0)
    + (1 / (2 * α)) * L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0

/-! ## Linearity of `L₁₂` in the profile, in the form used below -/

/-- `L₁₂` is odd in its profile argument: `L₁₂(−f)(ρ) = −L₁₂(f)(ρ)`, unconditionally.  The
Bochner integral is total and `L₁₂^K(f)(ρ) = ∫_ρ^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds`, so this is
`integral_neg` twice — no integrability hypothesis is needed. -/
theorem L12_neg (f : ℝ → ℝ → ℝ) (ρ : ℝ) : L12 (fun z θ => -f z θ) ρ = -L12 f ρ := by
  have hpoint : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K (fun z θ => -f z θ) s
      = -Work.FM.L12dens Work.Spaces.K f s := by
    intro s
    rw [Work.FM.L12dens, Work.FM.L12dens, ← integral_neg]
    congr 1 with θ
    ring
  rw [L12, L12, Work.FM.L12, Work.FM.L12]
  simp only [hpoint, integral_neg]

/-- **The transport zero-mode is odd in the profile.**  The linear functional
`g ↦ L₁₂(3 D_θ g/(1+z))(0)` is negated by the pointwise sign change `g ↦ −g`: it is `L12_neg`
together with `deriv.fun_neg` for `pth` (`D_θ = sin(2θ)∂_θ`).  Stated unconditionally. -/
theorem L12_transport_neg (g : ℝ → ℝ → ℝ) :
    L12 (fun z θ => 3 * Work.Spaces.Dth (fun z θ => -g z θ) z θ / (1 + z)) 0
      = -L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0 := by
  have hfun : (fun z θ => 3 * Work.Spaces.Dth (fun z θ => -g z θ) z θ / (1 + z))
      = fun z θ => -(3 * Work.Spaces.Dth g z θ / (1 + z)) := by
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth, deriv.fun_neg]
    ring
  rw [hfun]
  exact L12_neg (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0

/-- **`mufunS` is `mufun` at the flipped profile**: `mufunS α N₀ N g = mufun α N₀ N (−g)`.
This is the bridge that lets *every* generic estimate already proved about `Construction.mufun`
be reused for `mufunS` — at the cost of carrying the hypotheses at `−g`, which are the same
norms (the classes `HkMem`, `RegQ`, … are invariant under pointwise negation, and the two
`L₁₂`-inputs `N₀`, `N` of a *caller* are unchanged). -/
theorem mufunS_eq_mufun_neg (α : ℝ) (N0v Nv g : ℝ → ℝ → ℝ) :
    mufunS α N0v Nv g = mufun α N0v Nv (fun z θ => -g z θ) := by
  rw [mufunS, mufun, L12_transport_neg]
  ring

/-- **The defining relation of the corrected modulation constant**:
`2α · mufunS α N₀ N g = μ̄ + L₁₂(Transport g)(0)`, where `μ̄ = mubar N₀ N` and
`Transport g = 3 D_θ g/(1+z)`.  This is the relation assumed by the paper's derivation
(`Construction/Equation.lean`, `gEquationFinal`) and the one that makes the dynamic profile
equation `(E)` hold *identically*, with no `L₁₂`-zero-mode hypothesis
(`Work.FTS.MeridianDyn.DynEqF_of_isDynEqOn` after the rebuild). -/
theorem two_mul_mufunS (α : ℝ) (N0v Nv g : ℝ → ℝ → ℝ) (hα : α ≠ 0) :
    2 * α * mufunS α N0v Nv g
      = mubar N0v Nv + L12 (Work.Coercivity.Transport g) 0 := by
  have hT : L12 (Work.Coercivity.Transport g) 0
      = L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0 := rfl
  rw [hT, mufunS, mubar]
  field_simp

/-- `mufunS α N₀ N g = mufun α N₀ N g` **iff** the transport zero-mode
`L₁₂(3 D_θ g/(1+z))(0)` vanishes (for `α ≠ 0`).  So the corrected and the paper-display
constants coincide precisely on the zero-mode class; off it they solve different equations.
This is the formal content of `FTS_MUFUN_SIGN.md` §3 (option (b) is not available: the
zero-mode is not zero for the solution). -/
theorem mufunS_eq_mufun_iff (α : ℝ) (N0v Nv g : ℝ → ℝ → ℝ) (hα : α ≠ 0) :
    mufunS α N0v Nv g = mufun α N0v Nv g
      ↔ L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0 = 0 := by
  set A := L12 N0v 0 + L12 Nv 0 with hA
  set D := L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0 with hD
  have hS : mufunS α N0v Nv g = (1 / (2 * α)) * A + (1 / (2 * α)) * D := by
    rw [mufunS, ← hA, ← hD]
  have hm : mufun α N0v Nv g = (1 / (2 * α)) * A - (1 / (2 * α)) * D := by
    rw [mufun, ← hA, ← hD]
  have hc : (1 / (2 * α)) ≠ 0 :=
    div_ne_zero one_ne_zero (mul_ne_zero two_ne_zero hα)
  constructor
  · intro h
    rw [hS, hm] at h
    have hd : (1 / (2 * α)) * D = 0 := by linarith
    exact (mul_eq_zero.mp hd).resolve_left hc
  · intro h
    rw [hS, hm, h]
    ring

/-! ## The `|μ|`-bound -/

/-- **Design L-N4.8 for the corrected constant.**  Exactly the hypotheses of
`Work.FTS.Nonlin.mu_bound_mul` (the paper's three zero-mode estimates of Proposition
`muestimate`, each carrying a scaling constant `K`), with the conclusion for `mufunS`:

  `|mufunS α N₀ N g| ≤ 4K(α + α^{-1}X + α^{-5/2}X²)`.

Only the triangle inequality changes: `mufunS` is `(1/(2α))` times the **sum** (rather than the
signed sum) of the three `L₁₂`-values, and `|a + b + c| ≤ |a| + |b| + |c|` is the same bound.
The constant `4` is untouched, so every downstream consumer (`Nonlinear/Assembly`,
`OpenPkg/AssemblyOpen`, `Open2/Assembly2`) keeps its arithmetic. -/
theorem mu_bound_mulS {α X K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) (hK : 0 ≤ K)
    {N0v Nv g : ℝ → ℝ → ℝ}
    (h0 : |L12 N0v 0| ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h1 : |L12 Nv 0| ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h2 : |L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ K * X) :
    |mufunS α N0v Nv g|
      ≤ 4 * (K * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)) := by
  set a := L12 N0v 0 with ha
  set b := L12 Nv 0 with hb
  set d := L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0 with hd
  set S := α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 with hS
  set T := α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2 with hT
  have h0' : |a| ≤ K * S := by rw [ha, hS]; exact h0
  have h1' : |b| ≤ K * S := by rw [hb, hS]; exact h1
  have h2' : |d| ≤ K * X := by rw [hd]; exact h2
  have hmu : mufunS α N0v Nv g = (1 / (2 * α)) * ((a + b) + d) := by
    rw [mufunS, ha, hb, hd]; ring
  have htri : |(a + b) + d| ≤ K * (2 * S + X) := by
    have h12 : |(a + b) + d| ≤ |a + b| + |d| := abs_add_le (a + b) d
    have h3 : |a + b| ≤ |a| + |b| := abs_add_le a b
    linarith
  have hSle : S ≤ α * T := by
    rw [hS, hT]
    have hsq : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
    have h1_ : α * (α ^ (-(1 : ℝ)) * X) = X := by
      nth_rewrite 1 [← Real.rpow_one α]
      rw [← mul_assoc, ← Real.rpow_add hα, show (1 : ℝ) + (-(1 : ℝ)) = 0 by norm_num,
        Real.rpow_zero, one_mul]
    have h2_ : α * (α ^ (-(5 / 2 : ℝ)) * X ^ 2) = α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
      nth_rewrite 1 [← Real.rpow_one α]
      rw [← mul_assoc, ← Real.rpow_add hα,
        show (1 : ℝ) + (-(5 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num]
    rw [mul_add, mul_add, h1_, h2_]
    have hαα : α * α = α ^ 2 := by ring
    rw [hαα]
    have hsx : Real.sqrt α * X ≤ X := by
      simpa using mul_le_mul_of_nonneg_right hsq hX
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ α ^ 2 := by positivity
    linarith
  have hXT : X ≤ α * T := by
    have h1_ : α * (α ^ (-(1 : ℝ)) * X) = X := by
      nth_rewrite 1 [← Real.rpow_one α]
      rw [← mul_assoc, ← Real.rpow_add hα, show (1 : ℝ) + (-(1 : ℝ)) = 0 by norm_num,
        Real.rpow_zero, one_mul]
    have h2_ : α * (α ^ (-(5 / 2 : ℝ)) * X ^ 2) = α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
      nth_rewrite 1 [← Real.rpow_one α]
      rw [← mul_assoc, ← Real.rpow_add hα,
        show (1 : ℝ) + (-(5 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num]
    rw [hT, mul_add, mul_add, h1_, h2_]
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ α * α := by positivity
    nlinarith [hX]
  have hTnn : 0 ≤ T := by
    rw [hT]
    have h3 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
    have h1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) * X :=
      mul_nonneg (Real.rpow_nonneg hα.le _) hX
    linarith [hα.le]
  have hcoef : (0 : ℝ) < 1 / (2 * α) := by positivity
  have hST : 2 * S + X ≤ 3 * (α * T) := by linarith [hSle, hXT]
  have hmain : |mufunS α N0v Nv g| ≤ (1 / (2 * α)) * (K * (2 * S + X)) := by
    rw [hmu, abs_mul, abs_of_nonneg hcoef.le]
    exact mul_le_mul_of_nonneg_left htri hcoef.le
  have hkey : (1 / (2 * α)) * (K * (3 * (α * T))) = (3 / 2) * (K * T) := by
    field_simp
  calc |mufunS α N0v Nv g| ≤ (1 / (2 * α)) * (K * (2 * S + X)) := hmain
    _ ≤ (1 / (2 * α)) * (K * (3 * (α * T))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hST hK) hcoef.le
    _ = (3 / 2) * (K * T) := hkey
    _ ≤ 4 * (K * T) := by nlinarith [hK, hTnn]

/-- **Design L-N4.8 without the scaling constant** (the `K = 1` case of `mu_bound_mulS`). -/
theorem mu_boundS {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X)
    {N0v Nv g : ℝ → ℝ → ℝ}
    (h0 : |L12 N0v 0| ≤ α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
    (h1 : |L12 Nv 0| ≤ α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
    (h2 : |L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ X) :
    |mufunS α N0v Nv g|
      ≤ 4 * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
  have h := mu_bound_mulS (K := 1) hα hα1 hX (by norm_num) (N0v := N0v) (Nv := Nv) (g := g)
    (by simpa using h0) (by simpa using h1) (by simpa using h2)
  simpa using h

end Work.Construction
