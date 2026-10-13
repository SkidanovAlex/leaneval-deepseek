/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary definitions for Lemma `Transport3` (tex 1119)

This file fixes the vocabulary used by the auxiliary lemmas of
`Submission.Work.FTS.H2.Transport3`: the "exceptional" (all derivatives on `g`) part of
the integrand of the flat `ℋ⁴`-pairing `H4Pair α (fun z θ => f z θ * D g z θ) g`.

The point of the splitting is that

* every summand of the good part (the complement of the exceptional part) has at least one
  derivative falling on `f`, or is a block of total order `≤ 3`, so that its `g`-factors are
  genuine `ℋ⁴`-blocks: it is bounded pointwise by
  `C |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`, whence its integral is
  `≤ C |f|_{𝒲^{4,∞}} |g|²_{ℋ⁴}`;
* the exceptional part consists of the summands of the Leibniz expansion of
  `D_z^jD_θ^i(f D g)` with `i+j = 4` in which *all* derivatives fall on `g`; each of the
  corresponding blocks `h = D_z^jD_θ^i g` is an `ℋ⁴`-block while the object paired with it
  is `D_θh` resp. `D_zh`, one derivative higher, and has to be handled by an integration by
  parts.

The two pairings are

* `Badθ`, `Badz`: the exceptional parts of the `D_θ`- resp. `D_z`-pairing integrand;
* `H4PairInt α (fun z θ => f z θ * Dth g z θ) g - Badθ` and
  `H4PairInt α (fun z θ => f z θ * Dz g z θ) g - Badz`: the good parts.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.H2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-- The exceptional ("all derivatives on `g`") part of the integrand of the pairing
`H4Pair α (fun z θ => f z θ * Dth g z θ) g`: for the block `(j,i)` of total order `i+j = 4`
(with `i ≥ 1` in the mixed sum, and the `i = 4` block of the pure `D_z` sum) the summand
`f · D_θ(D_z^jD_θ^i g) · D_z^jD_θ^i g · W²`, i.e. the Leibniz term of
`D_z^jD_θ^i(f D_θg)` in which every derivative falls on `g`. -/
def Badθ (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  f z θ * (Spaces.Dth (Spaces.DzIter 4 g) z θ) * Spaces.DzIter 4 g z θ * Whz z θ ^ 2
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j = 4 then
          f z θ * (Spaces.Dth (Spaces.mixed j i g) z θ) * Spaces.mixed j i g z θ
            * Wm α z θ ^ 2
        else 0)

/-- The exceptional ("all derivatives on `g`") part of the integrand of the pairing
`H4Pair α (fun z θ => f z θ * Dz g z θ) g`. -/
def Badz (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  f z θ * (Spaces.Dz (Spaces.DzIter 4 g) z θ) * Spaces.DzIter 4 g z θ * Whz z θ ^ 2
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j = 4 then
          f z θ * (Spaces.Dz (Spaces.mixed j i g) z θ) * Spaces.mixed j i g z θ
            * Wm α z θ ^ 2
        else 0)

theorem Badθ_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Badθ α f g z θ
      = f z θ * (Spaces.Dth (Spaces.DzIter 4 g) z θ) * Spaces.DzIter 4 g z θ
          * Whz z θ ^ 2
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j = 4 then
              f z θ * (Spaces.Dth (Spaces.mixed j i g) z θ) * Spaces.mixed j i g z θ
                * Wm α z θ ^ 2
            else 0) := rfl

theorem Badz_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Badz α f g z θ
      = f z θ * (Spaces.Dz (Spaces.DzIter 4 g) z θ) * Spaces.DzIter 4 g z θ
          * Whz z θ ^ 2
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j = 4 then
              f z θ * (Spaces.Dz (Spaces.mixed j i g) z θ) * Spaces.mixed j i g z θ
                * Wm α z θ ^ 2
            else 0) := rfl

/-- The "mismatch" part of the `D_z`-pairing integrand: the Leibniz summands of
`D_z^jD_θ^i(f·D_zg)` in which *all* the `θ`-derivatives fall on `f` (`a = i`, `b` the
number of `z`-derivatives falling on `f`).  Then the remaining `g`-factor
`D_z^{j-b+1}g` carries no `θ`-derivative (so its natural weight is only
`sin(2θ)^{-η}`) while the pairing weight of the block `(j,i)` with `i ≥ 1` is
`sin(2θ)^{-γ}` — these summands therefore cannot be estimated by Cauchy–Schwarz with a
weight split and have to be integrated by parts in `θ`
(the factor `mixed j i g = D_θ(mixed j (i-1) g)` supplies the derivative). -/
def Mismatchz (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, ∑ b ∈ Finset.range (j + 1),
    (if 1 ≤ i ∧ i + j ≤ 4 then
      ((i.choose i : ℝ) * (j.choose b : ℝ))
        * (Spaces.mixed b i f z θ * Spaces.mixed (j - b + 1) 0 g z θ)
        * (Spaces.mixed j i g z θ * Wm α z θ ^ 2)
    else 0)

/-- The enlarged exceptional part of the `D_z`-pairing: the order-five ("all derivatives on
`g`") summands together with the "mismatch" summands `Mismatchz`; both are estimated by an
integration by parts. -/
def Badz2 (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  Badz α f g z θ + Mismatchz α f g z θ

theorem Badz2_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Badz2 α f g z θ = Badz α f g z θ + Mismatchz α f g z θ := rfl

end Work.FTS.H2
