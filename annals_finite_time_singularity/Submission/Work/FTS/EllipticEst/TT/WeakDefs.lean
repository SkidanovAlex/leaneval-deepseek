/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.WeakDefs`: the interface of the *weak-hypothesis* form of Elgindi's Proposition `prop:Hk`

This module fixes the vocabulary in which the analytic inputs of the `ℋ^k` elliptic estimate
`Work.FTS.EllipticEst.TT.propHk_core` are stated, and proves the (purely bookkeeping) reduction
of the target to those inputs.

## The target and its weak hypothesis class

`propHk_core` is Proposition `prop:Hk` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
  Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

tex 986 (`α²|R²∂_RRΨ|_{ℋ^k} + |∂_θθΨ|_{ℋ^k} ≤ C_k |F|_{ℋ^k}`, uniformly in `α ∈ (0,1/4]`),
in the weakest hypothesis class in which its two left-hand side integrals are honest:

* the equation `bslOp α Ψ = F` on the *open* quadrant only,
* the Dirichlet data `Ψ(z,0) = Ψ(z,π/2) = 0`,
* the two solvability conditions `OrthCond F`, `OrthCond Ψ`,
* smoothness of `Ψ` on the open quadrant only (no `SmoothNbhd`, no `ZDecay`),
* honesty (`HkMem`) of the source and of the two left-hand side quantities.

The predicates below bundle this class (`EllWeakPos`), the level-`0` estimate (`EllWeak0`,
the paper's `prop:L2` with its weights, i.e. Steps 1–2 of `prop:H2`) and the target estimate at
level `k` (`EllEstUnif`).

## The reduction

`propHk_core_of` records the assembly: the level-`0` estimate, the level-`2` estimate
(the paper's `prop:H2`) and the induction step (the paper's §"General `ℋ^k` Case") together give
`propHk_core`.  The three analytic inputs are the *pieces* proved in the sibling modules
`TT.l2eta_weak`, `TT.est_two_weak`, `TT.est_step_weak`; this file contains no analysis.

## Notes for a consumer of `EllWeakPos` (read before using it)

* **The moment conditions, and how the slices get theirs.**  The two conditions are `Fstar F z = 0`
  and `Fstar Ψ z = 0` for `z > 0` (`Fstar f z = ∫_θ f(z,θ) sinθcos²θ dθ`); the full `OrthCond`
  of `propHk_core` holds for every real `z` and implies them.  They are consumed *slicewise in
  `z`* by the proof of the level-`0` estimate (the Fourier/Parseval argument excludes the
  angular mode `sin 2θ` on each slice).

  For the **radially differentiated data** `(D_z^j F, D_z^j Ψ)`, to which Steps 1–3 of the
  paper's proof of `prop:H2` are applied, the moment conditions are obtained from the base ones
  in two steps (implemented in `Submission/Work/FTS/EllipticEst/remov/`):

  \- *integrated form of the differentiation under the `θ`-integral*: the chain relation
  `Fstar (D_z^j f)(z) - Fstar (D_z^j f)(s) = ∫_s^z Fstar (D_z^{j+1} f)(r)/r dr` for `0 < s ≤ z`
  (this is the Fubini/fundamental-theorem statement, whose hypotheses are `SmoothOpen f` and the
  `HkMem`-honesty of `f` at the relevant level: `remov/FstarDzIter_chain_open`);

  \- *from that to the pointwise statement*: the chain relation gives `Fstar (D_z^{j+1} f) = 0`
  almost everywhere (its integral over every interval `(s,z)` vanishes), and the same relation
  (its right-hand side bounded by Cauchy–Schwarz on the short interval) gives the *continuity*
  of `z ↦ Fstar (D_z^{j+1} f)(z)`; together they give the pointwise vanishing used here
  (`remov/Fstar_DzIter_one_Psi`, `remov/Fstar_DzIter_one_F`,
  `remov/EllWeakPos_DzIter_one_shift`).

* **`D_z^j` commutes with the equation.**  `bslOp α Ψ = -α² D_z²Ψ - 5α D_zΨ + LzeroΨ` and
  `Lzero` is `z`-independent, so `D_z^j` commutes with `bslOp α` on the open quadrant; hence
  `bslOp α (D_z^j Ψ) = D_z^j F` there (`TT.bslOp_DzIter_eq`, proved), i.e. the slices are again
  data of the class, with the same Dirichlet data (`TT.DzIter_zero_at_zero`,
  `TT.DzIter_zero_at_pi_half`, proved) and the level-`0` certificates `HkMem α 0` obtained from
  `HkMem α k` by monotonicity of the `ℋ`-integrand in the index (`TT.HkMem_descend_open`,
  together with `Work.FTS.CoercivityStep.Norm.HkSq_mono_le`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- **The weak hypothesis class of the elliptic `ℋ^k` estimate.**

The only difference with respect to the hypotheses written out in `propHk_core` is that the two
moment conditions (`OrthCond`) are demanded only for `z > 0`: the full `OrthCond` holds for every
real `z` and implies this version. -/
def EllWeakPos (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
  (∀ z, Ψ z 0 = 0) ∧ (∀ z, Ψ z (Real.pi / 2) = 0) ∧
  (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) ∧
  (∀ z, 0 < z → Work.Elliptic.Fstar Ψ z = 0) ∧
  (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
  Work.Spaces.HkMem α k F ∧
  Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
  Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) ∧
  -- the *diagonal second-order honesty* `HkMem α k (∂_θθ(z∂_zΨ))`: the clause Step 2 of
  -- `prop:H2` consumes (`AeI1Paper_repair.md`), not implied by the other fields
  -- (`H2W/AeWAux/NOTES_aeI1Data_FALSE.md`).
  Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)

/-- **The level-`0` estimate** (Elgindi, Proposition `prop:L2` with the weights
`w²/sin^η`, i.e. Steps 1 and 2 of the proof of Proposition `prop:H2`), in the form in which the
slices `D_z^jΨ` consume it: with `C` universal, for `0 < α ≤ 1/4` and every datum of the weak
class,

  `α⁴|z²∂_zzΨ|²_{ℋ⁰} + |∂_θθΨ|²_{ℋ⁰} ≤ C |F|²_{ℋ⁰}`,

where `|·|_{ℋ⁰}` is the `η`-weighted `L²`-norm `w/sin(2θ)^{η/2}`. -/
def EllWeak0 (C : ℝ) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllWeakPos α 0 F Ψ →
    α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) ≤ C * Work.Spaces.HkSq α 0 F

/-- **The estimate at level `k`** (the conclusion of `prop:Hk`, with a named constant). -/
def EllEstUnif (k : ℕ) (C : ℝ) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllWeakPos α k F Ψ →
    α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψ) ≤ C * Work.Spaces.HkNorm α k F

/-! ## Elementary API of the hypothesis bundle -/

theorem EllWeakPos.eq {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ :=
  h.1

theorem EllWeakPos.zero {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, Ψ z 0 = 0 := h.2.1

theorem EllWeakPos.pi_half {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, Ψ z (Real.pi / 2) = 0 := h.2.2.1

theorem EllWeakPos.orthF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar F z = 0 := h.2.2.2.1

theorem EllWeakPos.orthPsi {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar Ψ z = 0 := h.2.2.2.2.1

theorem EllWeakPos.smooth {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.2.2.2.2.2.1

theorem EllWeakPos.memF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.Spaces.HkMem α k F := h.2.2.2.2.2.2.1

theorem EllWeakPos.memA {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  h.2.2.2.2.2.2.2.1

theorem EllWeakPos.memB {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := h.2.2.2.2.2.2.2.2.1


/-- **The diagonal second-order honesty** of the weak class: `HkMem α k (∂_θθ(z∂_zΨ))`, i.e. the
honesty of `fun z θ => z * ∂_z∂_θθΨ`.  This is the conjunct Step 2 of `prop:H2` consumes; see
`AeI1Paper_repair.md`. -/
theorem EllWeakPos.memZPth2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllWeakPos α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
  h.2.2.2.2.2.2.2.2.2

/-- The hypotheses of `propHk_core` written out imply the weak class `EllWeakPos`. -/
theorem ellWeakPos_of_hyps {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (h0 : ∀ z, Ψ z 0 = 0) (h1 : ∀ z, Ψ z (Real.pi / 2) = 0)
    (hOF : Work.Elliptic.OrthCond F) (hOP : Work.Elliptic.OrthCond Ψ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmF : Work.Spaces.HkMem α k F)
    (hmA : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hmB : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ))
    (hmZ : Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    EllWeakPos α k F Ψ :=
  ⟨hEq, h0, h1, fun z _ => hOF z, fun z _ => hOP z, hsm, hmF, hmA, hmB, hmZ⟩

/-! ## The assembly

The three analytic inputs listed in the module docstring give the target.  The proof is the
induction on `k`: level `2` is the paper's Proposition `prop:H2`, and the passage from `k-1` to
`k` (`k ≥ 3`) is the paper's §"General `ℋ^k` Case".  Both are stated with a constant that is
*uniform in `α ∈ (0,1/4]`*, which is what makes the induction produce the `α`-uniform constant
demanded by `prop:Hk`. -/

theorem propHk_core_of (h0 : ∃ C : ℝ, 0 < C ∧ EllWeak0 C)
    (h2 : ∃ C : ℝ, 0 < C ∧ EllEstUnif 2 C)
    (hstep : ∀ k : ℕ, 3 ≤ k → (∃ C : ℝ, 0 < C ∧ EllEstUnif (k - 1) C) →
      ∃ C : ℝ, 0 < C ∧ EllEstUnif k C) :
    ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧ EllEstUnif k C := by
  obtain ⟨C2, hC2pos, hC2⟩ := h2
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact hstep k hlt (ih (k - 1) (by omega) (by omega))
    · subst heq
      exact ⟨C2, hC2pos, hC2⟩

end Work.FTS.EllipticEst.TT
