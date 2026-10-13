/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/H2/`: the facts of §`H2` of the paper

This directory formalises §`H2` ("Some useful facts about `ℋ^k` and `𝒲^{l,∞}`") of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

`Papers/elgindi/Classical_Euler_arXiv_2.tex`, tex lines 1040--1315, at the values
`k = 4`, `l = 5` fixed by the paper: the product rules (`HProductRule`, `WProductRule`,
in `Submission/Work/Spaces/`), the transport estimates (`Transport1`, `Transport2`,
`Transport3`, `SpecialTransport`), `PhiStarRegularity`, `WtoH`, `WtoW`, `L12H`,
`DivisionBySin` and `muestimate`.

## The flat `ℋ⁴` pairing

Every statement of §`H2` about an *inner product* is a statement about the pairing
associated with the norm

  `|f|²_{ℋ⁴} = ∑_{i=0}^4 |D_z^i f · w/√(sin 2θ)^η|²_{L²}
      + ∑_{0 ≤ i+j ≤ 4, i ≥ 1} |D_z^j D_θ^i f · W|²_{L²}`

(paper (HkNorm), tex 206), namely

  `(u,v)_{ℋ⁴} = ∑_{i=0}^4 (D_z^i u w, D_z^i v w / sin(2θ)^η)_{L²}
      + ∑_{0 ≤ i+j ≤ 4, i ≥ 1} (D_z^j D_θ^i u W, D_z^j D_θ^i v W)_{L²}`.

This is *not* the inductively constructed coercive inner product of §`Linearization
with angular transport` (`Work.Coercivity.H1IP`, `Work.Coercivity.HkIPStep`), which is
a different, equivalent-on-the-admissible-class functional; it is the flat form the
proofs of §`H2` actually estimate, term by term, as one sees from the model cases
`(D_θ⁴(fD_θg), D_θ⁴g W²)_{L²}` and `(D_z³D_θ(fD_θg), D_z³D_θg W²)_{L²}` displayed in
the proof of `Transport1`.

`H4PairInt α u v` is the integrand of this pairing and `H4Pair α u v` its iterated
integral over `Iz × Iθ` with the measure `dz dθ` (the Warning of §Notation: **not**
`z dz dθ`).  The identification `H4Pair α u u = Spaces.HkSq α 4 u` is
`H4Pair_self`.

## Conventions

* Functions of the self-similar variables are curried, `f : ℝ → ℝ → ℝ`, evaluated as
  `f z θ`, exactly as in `Work.Spaces`, `Work.FM`, `Work.Elliptic` and
  `Work.Coercivity`.
* Hypotheses are the standing ones of the area: `Spaces.SmoothNbhd` (smoothness on an
  open neighbourhood of the closed quadrant, so that Leibniz rules and the
  fundamental theorem of calculus apply without boundary bookkeeping),
  `Spaces.SmoothInt` (smoothness on the open strip, used for the `𝒲^{4,∞}` velocity
  of `SpecialTransport`), `Spaces.VanishTheta` (vanishing on the two angular
  boundaries), `Spaces.DecayAll` (decay at `z → ∞`) and `Spaces.HkMem` /
  `Spaces.WlInfMem` (the honesty hypotheses that make the weighted integrals and
  suprema honest rather than Lean's junk values).
* The constant `C` of every statement is **universal**: independent of `α` (and of
  `γ = 1 + α/10`).  Every statement holds for `0 < α ≤ 1`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

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

/-! ## The weights of the flat `ℋ⁴` pairing -/

/-- The weight `w(z)/√(sin(2θ)^η)` carried by the `D_z`-only summands (`i = 0`) of the
`ℋ⁴`-norm (paper (HkNorm): the first sum). -/
def Whz (z θ : ℝ) : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)

/-- The weight `W = w · w_θ` carried by the summands with at least one `θ`-derivative
(`i ≥ 1`) of the `ℋ⁴`-norm (paper (HkNorm): the second sum). -/
def Wm (α z θ : ℝ) : ℝ := Spaces.Wt α z θ

theorem Whz_eq (z θ : ℝ) : Whz z θ = Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2) :=
  rfl

theorem Wm_eq (α z θ : ℝ) : Wm α z θ = Spaces.Wt α z θ := rfl

/-! ## The flat `ℋ⁴` pairing -/

/-- The integrand of the flat `ℋ⁴` pairing of the paper: the bilinear version of
`Spaces.HkIntegrand α 4`, i.e. the sum over the same finitely many weighted derivatives
of the products `D u · D v` in place of the squares `(D u)²`. -/
def H4PairInt (α : ℝ) (u v : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 5,
      (Spaces.DzIter i u z θ * Whz z θ) * (Spaces.DzIter i v z θ * Whz z θ))
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Spaces.mixed j i u z θ * Wm α z θ) * (Spaces.mixed j i v z θ * Wm α z θ)
        else 0)

/-- The flat `ℋ⁴` pairing `(u,v)_{ℋ⁴}` of the paper, integrated over `Iz × Iθ` with the
measure `dz dθ`.  On the diagonal it is the squared `ℋ⁴`-norm (`H4Pair_self`). -/
def H4Pair (α : ℝ) (u v : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, H4PairInt α u v z θ

/-! ## Elementary API -/

/-- On the diagonal the flat pairing is the squared `ℋ⁴`-norm. -/
theorem H4Pair_self (α : ℝ) (u : ℝ → ℝ → ℝ) : H4Pair α u u = Spaces.HkSq α 4 u := by
  unfold H4Pair Spaces.HkSq Spaces.HkIntegrand H4PairInt Whz Wm Spaces.Wt
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [pow_two]

/-- The integrand of the flat pairing is symmetric. -/
theorem H4PairInt_comm (α : ℝ) (u v : ℝ → ℝ → ℝ) (z θ : ℝ) :
    H4PairInt α u v z θ = H4PairInt α v u z θ := by
  unfold H4PairInt
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring

/-- The flat pairing is symmetric. -/
theorem H4Pair_comm (α : ℝ) (u v : ℝ → ℝ → ℝ) : H4Pair α u v = H4Pair α v u := by
  unfold H4Pair
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact H4PairInt_comm α u v z θ

/-- The `D_z`-only part of the flat pairing integrand, as a named sum. -/
theorem H4PairInt_eq (α : ℝ) (u v : ℝ → ℝ → ℝ) (z θ : ℝ) :
    H4PairInt α u v z θ
      = (∑ i ∈ Finset.range 5,
          (Spaces.DzIter i u z θ * Whz z θ) * (Spaces.DzIter i v z θ * Whz z θ))
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Spaces.mixed j i u z θ * Wm α z θ) * (Spaces.mixed j i v z θ * Wm α z θ)
            else 0) := rfl

/-- The squared `ℋ⁴`-norm is the `ℋ⁴`-norm squared. -/
theorem HkNorm_sq (α : ℝ) (u : ℝ → ℝ → ℝ) :
    Spaces.HkNorm α 4 u ^ 2 = Spaces.HkSq α 4 u :=
  Real.sq_sqrt (Spaces.HkSq_nonneg α 4 u)

end Work.FTS.H2
