/-
Copyright: work module for the Elgindi finite-time singularity project.

# Splitting the `D_z`-transport pairing into its "easy" and "hard" parts

`Transport2` bounds `|(f D_z g, g)_{ℋ⁴}|` by `C/√(γ-1) |f|_{ℋ⁴} |g|²_{ℋ⁴}` for the flat
pairing `Work.FTS.H2.H4Pair`.  Expanding the Leibniz rule leaves, in the two "top" slots
(the `i = 4` slot of the `D_z`-sum and the mixed slots with `i + j = 4`), exactly five
terms in which five derivatives fall on `g`:

* `f · D_z^5 g · D_z^4 g · Whz²`                     (the `D_z`-slot, weight `sin(2θ)^{-η}`),
* `f · mixed (j+1) i g · mixed j i g · Wm²`,  `(j,i) = (3,1),(2,2),(1,3),(0,4)`,
  i.e. `f · D_z(mixed j i g) · mixed j i g · w² sin(2θ)^{-γ}`.

These are the terms whose `g`-factor has order `5`, so they cannot be estimated by a
weighted `L²` norm of `g`; they are removed by integrating by parts in `z`
(`T2Hard`).  This file names them:

* `Thard g k` (`k : Fin 5`) is the list `D_z^4 g, D_z^3D_θ g, D_z^2D_θ^2 g, D_zD_θ^3 g,
  D_θ^4 g` of `g`-derivatives of order `4`,
* `sghard α k` is the corresponding angular weight `sin(2θ)^{-η}` (for `k = 0`) resp.
  `sin(2θ)^{-γ}` (for `k ≥ 1`),
* `Hhard α f g` is their contribution to the pairing integrand, and
* `Heasy α f g` is what remains of `H4PairInt α (f D_z g) g`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-- The five order-`4` `g`-derivatives appearing in the "top" (order `5`) terms of the
pairing `(f D_z g, g)_{ℋ⁴}`: `D_z^4 g`, `D_z^3 D_θ g`, `D_z^2 D_θ^2 g`, `D_z D_θ^3 g`,
`D_θ^4 g`. -/
def Thard (g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  match k.val with
  | 0 => fun z θ => Spaces.mixed 4 0 g z θ
  | 1 => fun z θ => Spaces.mixed 3 1 g z θ
  | 2 => fun z θ => Spaces.mixed 2 2 g z θ
  | 3 => fun z θ => Spaces.mixed 1 3 g z θ
  | _ => fun z θ => Spaces.mixed 0 4 g z θ

/-- The angular weight of the top terms: `sin(2θ)^{-η}` for the `D_z`-slot (`k = 0`) and
`sin(2θ)^{-γ}` for the mixed slots (`k ≥ 1`). -/
def sghard (α : ℝ) (k : Fin 5) : ℝ → ℝ :=
  match k.val with
  | 0 => fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.eta))
  | _ => fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-- The "hard" part of the pairing integrand `H4PairInt α (f D_z g) g`: the five terms in
which all five derivatives fall on `g`. -/
def Hhard (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  f z θ * z * (∑ k : Fin 5, Spaces.pz (Thard g k) z θ * Thard g k z θ
    * (Spaces.w z) ^ 2 * sghard α k θ)

/-- The "easy" part of the pairing integrand: everything except the five order-five terms. -/
def Heasy (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  H4PairInt α (fun z θ => f z θ * Spaces.Dz g z θ) g z θ - Hhard α f g z θ

/-- Pointwise, the pairing integrand is the sum of its easy and hard parts. -/
theorem H4PairInt_eq_easy_add_hard (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    H4PairInt α (fun z θ => f z θ * Spaces.Dz g z θ) g z θ
      = Heasy α f g z θ + Hhard α f g z θ := by
  simp only [Heasy]
  ring

end Work.FTS.H2
