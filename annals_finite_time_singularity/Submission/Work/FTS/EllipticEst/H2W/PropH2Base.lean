/-
Copyright: work module for the Elgindi finite-time singularity project.

# `propH2WeakFts` — Proposition `prop:H2` of §'Elliptic Regularity Estimates' (weak class)

Target: `Work.FTS.EllipticEst.propH2WeakFts`, i.e. Elgindi's Proposition `prop:H2`
(*Finite-time singularity formation for `C^{1,α}` solutions to the incompressible Euler
equations on `ℝ³`*, Annals of Math. **194** (2021), tex 837; the case `k = 2` of `prop:Hk`,
tex 986):

  `α² |z²∂_zzΨ|_{ℋ²} + |∂_θθΨ|_{ℋ²} ≤ C |F|_{ℋ²}`,   `L(Ψ) = F` = (PolarBSL),

with an `α`-uniform `C`, in the *weak* hypothesis class in which the two left-hand side
integrals are merely *defined* (totalised Bochner integrals): the equation only on the open
quadrant, the Dirichlet *values* `Ψ(·,0) = Ψ(·,π/2) = 0`, decay `Ψ(·,θ) → 0` at `z → ∞`, both
solvability conditions `OrthCond F`, `OrthCond Ψ`, smoothness on the open quadrant only, and
honesty (`Work.Spaces.HkMem`) of the **source only**.  This is the `k = 2` instance of
`Work.FTS.EllipticEst.propHkWeakOpenFts`.

## The route recorded here (and the routes that are dead)

The estimate is reduced, in this file, to **three pieces stated directly in the weak class** —
the pure (`D_z`-only) components of the two left-hand side quantities, and the two mixed
(angular) bounds — each with a universal constant, the pure part kept as slack:

```
propH2WeakFts  ⟸  weakPure           (level-0 estimate on the radially differentiated data)
                 + weakMixedA, weakMixedB   (one and two angular derivatives)
```

`propH2WeakFts_of_pieces` below is the (proved) assembly: it is pure arithmetic on
`HkSq = HkNorm²`, and — crucially — it needs **no** honesty hypothesis on the left-hand side and
**no** case distinction, because the three pieces are inequalities between real numbers in which
the totalised (`0` on junk) values already occur on both sides.

**Dead routes (recorded so they are not re-proposed).**

* The route through the honest-class estimate `TT.EllEstUnif 2` needs *both* left-hand side
  quantities to satisfy `HkMem`, which is not a hypothesis here, and the "honesty transfer"
  that would supply it is **false**: see `NOTES_propHkWeakOpenFts.md` §"Both natural
  formulations of the junk layer are FALSE".  The pointwise slice transfer
  (`FTS/EllipticEst/OpenJunk/slice_honest_open`) and the "no partial junk" statement
  (`FTS/EllipticEst/OpenJunk/hksq_ne_zero_imp_hkMem`, whose `k = 2` instance
  `H2W/hksqNeZeroImpMemK2` was also refuted) each fail: at `θ = π/2`, `Lzero` has indicial
  exponents `±1` *and* a `t·log t` mode, so a bump-shaped `t^{-1}` coefficient of `Ψ` can be
  cancelled in the source by its `t log t` companion, leaving data whose source is honest while
  `Ψ` has both bad slices (on the bump) and honest non-zero slices (elsewhere).
* Consequently the honesty dichotomy `hk_of_hkMemF` is false, and the estimate must be proved in
  the weak class directly, i.e. including the indicial behaviour of `Ψ` at the angular endpoints
  and the totalised left-hand side.  That is exactly what the three pieces above ask for.
* Approximating `Ψ` by `z`-truncations and applying the honest estimate in the limit also fails
  (`NOTES_propHkWeakOpenFts.md` §3, trap 4): the truncation's source differs from `χ_R F` by the
  commutator `-α²z²(χ_R''Ψ + 2χ_R'∂_zΨ) - α(5+α)zχ_R'Ψ`, which does not vanish in the norm
  without decay of `∂_zΨ`.

**The `π` convention.**  The target statement is reproduced *verbatim* from the request; it uses
the notation `π`.  `lakefile.toml` sets `autoImplicit = false` workspace-wide, so a bare `π`
would *not* elaborate as `Real.pi` unless the `Real` scope is open — the statement is therefore
parsed with `open scoped Real` (as in every sibling module of the elliptic chapter, where
`Work.Spaces.Iθ = Set.Icc 0 (π/2)` is the paper's interval `[0, π/2]`).  Without this line the
statement does not even elaborate; the statement text itself is untouched.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- `L2Sq` is nonnegative. -/
theorem L2Sq_nonneg_fts (g : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.L2Sq g :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

/-- `Work.Spaces.HkSq α k g` is an iterated Bochner integral of a nonnegative integrand, so a
quantity whose outer `z`-integral is not honest contributes the totalised value `0`. -/
theorem HkSq_eq_zero_of_not_integrableOn_fts (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ)
    (h : ¬ MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      Work.Spaces.Iz) :
    Work.Spaces.HkSq α k g = 0 := by
  rw [Work.Spaces.HkSq]
  exact MeasureTheory.integral_undef h

/-- At level `0` the `ℋ`-square is the `L²`-square of `g · w / sin(2θ)^{η/2}`. -/
theorem HkSq_zero_eq_L2Sq_fts (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = Work.Spaces.L2Sq (fun z θ =>
          g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  simp only [Work.Spaces.HkSq, Work.Spaces.HkIntegrand, Work.Spaces.L2Sq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp

/-- The level-`0` square of the radially differentiated source is a summand of the level-`2`
square of the source (a direct instance of `Work.Spaces.L2Sq_DzIter_le_HkSq`). -/
theorem L2Sq_DzIter_le_HkSq_fts (α : ℝ) (F : ℝ → ℝ → ℝ) (hF : Work.Spaces.HkMem α 2 F)
    (j : ℕ) (hj : j ≤ 2) :
    Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.DzIter j F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ≤ Work.Spaces.HkSq α 2 F :=
  Work.Spaces.L2Sq_DzIter_le_HkSq α 2 F hF j hj

/-! ## The two weak classes

`WeakPos2` is the hypothesis list of the target, bundled; `WeakPos0` is the level-`0` analogue,
the class of the pair `(G, Φ)` that the level-`0` estimate is applied to.  Both differ from
`TT.EllWeakPos` in that the honesty of the two *left-hand side* quantities is **not** demanded —
only the source is honest.  (The moment conditions are demanded for `z > 0` only, which is the
form in which the estimate is applied to the radially differentiated data; in `WeakPos0` they
are demanded only **a.e.** in `z`, because that is what the shift `D_z^j` of the moment condition
delivers: the pointwise-in-`z` form for the shifted data is *not* a consequence of the level-`2`
hypotheses — see `H2W/Fstar_DzIter_two_F.lean` and `remov/NOTES_Fstar_DzIter_one_eq_zero.md`,
and since the estimate is an inequality between integrals, a.e. information suffices.) -/

/-- The weak class at level `2`: exactly the hypotheses of `propH2WeakFts`. -/
def WeakPos2 (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, Ψ z 0 = 0) ∧ (∀ z, Ψ z (Real.pi / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) ∧
        Work.Elliptic.OrthCond F ∧ Work.Elliptic.OrthCond Ψ ∧
          (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
            Work.Spaces.HkMem α 2 F

/-- The weak class at level `0` (the class of the data the level-`0` estimate consumes). -/
def WeakPos0 (α : ℝ) (G Φ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Φ z θ = G z θ) ∧
    (∀ z, Φ z 0 = 0) ∧ (∀ z, Φ z (Real.pi / 2) = 0) ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar G z = 0) ∧
        (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar Φ z = 0) ∧
          (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
            Work.Spaces.HkMem α 0 G

/-- **The `L¹_θ` control of the moment and of its `z`-derivatives.**

The `θ`-integrals against `sinθcos²θ` of `Φ`, `∂_zΦ` and `∂²_zΦ` are honest, and `z ↦ Fstar Φ z`
is twice differentiable with those integrals as its derivatives (i.e. the moment integral may be
differentiated under the integral sign, twice).

This is *exactly* the input the truncation argument of
`remov/NOTES_level0WeakBridge_truncation.md` needs in order to pass from the honest level-`0`
estimate to the weak one: with it the moment correction `c(z)·sin2θ` of the `θ`-truncation
vanishes together with its first two `z`-derivatives, so the truncated sources converge in
`HkSq α 0`.  It is **not** implied by `WeakPos0` (which constrains `z²∂²Φ` and `∂_θθΦ` in the
`η`-weighted `L²` sense, not `∂_zΦ` in `L¹_θ`); whether it is derivable from the equation in the
weak class, or must be assumed, is the residual question of the node. -/
def MomentZ (Φ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Set.Ioi 0, ∀ k ≤ 2, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pzIter k Φ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) ∧
    (∀ z ∈ Set.Ioi 0, deriv (fun z' => Work.Elliptic.Fstar Φ z') z
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Φ z θ * Work.Elliptic.sinCos2 θ) ∧
    (∀ z ∈ Set.Ioi 0, deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Φ z'') z') z
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Φ z θ * Work.Elliptic.sinCos2 θ)

/-! ## `weakPureFts`: the pure components, from the level-`0` estimate and the shift

The pure components of the two level-`2` integrands are the level-`0` quantities of the
radially differentiated data `(D_z^j F, D_z^j Ψ)`, `j ≤ 2`; the paper's Step 3 is exactly the
statement that those data are again admissible, and the level-`0` estimate applied to them gives
the pure bound. -/

/-- **The pure part of the level-`2` estimate, from the level-`0` estimate and the shift.** -/
theorem weakPureFts_of_pieces
    (hL0 : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (α : ℝ) (G Φ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      WeakPos0 α G Φ →
      α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Φ z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Φ) ≤ C₁ * Work.Spaces.HkSq α 0 G)
    (hshift : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → WeakPos2 α F Ψ →
      ∀ j : ℕ, j ≤ 2 →
        WeakPos0 α (Work.Spaces.DzIter j F) (Work.Spaces.DzIter j Ψ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
      (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) →
      Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond Ψ →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 2 F →
      α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        + ∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₁, hC₁, hL0'⟩ := hL0
  refine ⟨3 * C₁ + 1, by linarith, ?_⟩
  intro α F Ψ hα hα4 hEq h0 h1 hdec hOF hOP hsm hmF
  have hFnn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have h2 : WeakPos2 α F Ψ := ⟨hEq, h0, h1, hdec, hOF, hOP, hsm, hmF⟩
  have hstep : ∀ j ∈ Finset.range 3,
      α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        + Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ≤ C₁ * Work.Spaces.HkSq α 2 F := by
    intro j hj
    have hjle : j ≤ 2 := by
      have := Finset.mem_range.mp hj
      omega
    have hb := hL0' α (Work.Spaces.DzIter j F) (Work.Spaces.DzIter j Ψ) hα hα4
      (hshift α F Ψ hα hα4 h2 j hjle)
    have hle : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F) ≤ Work.Spaces.HkSq α 2 F := by
      rw [HkSq_zero_eq_L2Sq_fts]
      exact L2Sq_DzIter_le_HkSq_fts α F hmF j hjle
    have hb2 : α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        ≤ C₁ * Work.Spaces.HkSq α 2 F :=
      le_trans hb (mul_le_mul_of_nonneg_left hle (le_of_lt hC₁))
    rw [HkSq_zero_eq_L2Sq_fts, HkSq_zero_eq_L2Sq_fts] at hb2
    exact hb2
  have hsum : (∑ j ∈ Finset.range 3,
        (α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
            z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
          + Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))))
      ≤ ∑ _j ∈ Finset.range 3, C₁ * Work.Spaces.HkSq α 2 F :=
    Finset.sum_le_sum hstep
  have h3 : (∑ _j ∈ Finset.range 3, C₁ * Work.Spaces.HkSq α 2 F)
      = 3 * (C₁ * Work.Spaces.HkSq α 2 F) := by
    rw [Finset.sum_const, Finset.card_range]
    ring
  have hsplit : α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      + ∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = ∑ j ∈ Finset.range 3,
          (α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
              z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
            + Work.Spaces.L2Sq (fun z θ =>
                Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsplit]
  rw [h3] at hsum
  nlinarith [hsum, hFnn]

/-! ## The three weak-class pieces, and the assembly

`PA`, `PB` below are the *pure* (`D_z`-only) components of the two left-hand side integrands at
level `2`: `PA = ∑_{j≤2} |z²∂_zz(D_z^jΨ)·w·sin(2θ)^{-η/2}|²_{L²}` and
`PB = ∑_{j≤2} |∂_θθ(D_z^jΨ)·w·sin(2θ)^{-η/2}|²_{L²}`.  They are the quantities controlled by the
level-`0` estimate applied to the shifted data `(D_z^jF, D_z^jΨ)`, `j ≤ 2`. -/

/-- **The target from the three weak-class pieces.**  Everything here is arithmetic on
`HkSq = HkNorm²`: the two mixed bounds turn the level-`2` `HkSq`'s into the pure parts plus
`HkSq α 2 F`, the pure bound (with `α⁴ ≤ 1`) absorbs the pure parts into `C₀·HkSq α 2 F`, and
the square roots give the `HkNorm` form with the constant `√(K(C₀+1))` for each of the two
terms. -/
theorem propH2WeakFts_of_pieces
    (hweak : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
      (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) →
      Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond Ψ →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 2 F →
      α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        + ∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ≤ C₀ * Work.Spaces.HkSq α 2 F)
    (hA : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
      (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) →
      Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond Ψ →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 2 F →
      α ^ 4 * Work.Spaces.HkSq α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ≤
        K * (α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
          + Work.Spaces.HkSq α 2 F))
    (hB : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
      (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) →
      Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond Ψ →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 2 F →
      Work.Spaces.HkSq α 2 (Work.Spaces.pthIter 2 Ψ) ≤
        K * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
          + Work.Spaces.HkSq α 2 F)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
    (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (π / 2) = 0) →
    (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => Ψ z θ) Filter.atTop (nhds 0)) →
    Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond Ψ →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
    Work.Spaces.HkMem α 2 F →
    α ^ 2 * Work.Spaces.HkNorm α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkNorm α 2 (Work.Spaces.pthIter 2 Ψ)
    ≤ C * Work.Spaces.HkNorm α 2 F := by
  obtain ⟨C₀, hC₀, hpure⟩ := hweak
  obtain ⟨KA, hKA, hKA'⟩ := hA
  obtain ⟨KB, hKB, hKB'⟩ := hB
  refine ⟨Real.sqrt (KA * (C₀ + 1)) + Real.sqrt (KB * (C₀ + 1)) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hEq h0 h1 hdec hOF hOP hsm hmF
  have hα0 : 0 ≤ α := le_of_lt hα
  have hα4nn : 0 ≤ α ^ 4 := pow_nonneg hα0 4
  have hFnn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hFnorm : 0 ≤ Work.Spaces.HkNorm α 2 F := Work.Spaces.HkNorm_nonneg α 2 F
  have hP := hpure α F Ψ hα hα4 hEq h0 h1 hdec hOF hOP hsm hmF
  have hPAnn : 0 ≤ α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
      z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) :=
    mul_nonneg hα4nn (Finset.sum_nonneg fun _ _ => L2Sq_nonneg_fts _)
  have hPBnn : 0 ≤ (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) :=
    Finset.sum_nonneg fun _ _ => L2Sq_nonneg_fts _
  have hPA4 : α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
      z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      ≤ C₀ * Work.Spaces.HkSq α 2 F := by linarith [hP, hPBnn]
  have hPB : (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      ≤ C₀ * Work.Spaces.HkSq α 2 F := by linarith [hP, hPAnn]
  have hAfin : α ^ 4 * Work.Spaces.HkSq α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      ≤ KA * (C₀ + 1) * Work.Spaces.HkSq α 2 F := by
    have h1 := hKA' α F Ψ hα hα4 hEq h0 h1 hdec hOF hOP hsm hmF
    have h2 : KA * (α ^ 4 * (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        + Work.Spaces.HkSq α 2 F) ≤ KA * ((C₀ + 1) * Work.Spaces.HkSq α 2 F) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hKA)
      nlinarith [hPA4, hFnn]
    have h3 : KA * ((C₀ + 1) * Work.Spaces.HkSq α 2 F)
        = KA * (C₀ + 1) * Work.Spaces.HkSq α 2 F := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hBfin : Work.Spaces.HkSq α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ KB * (C₀ + 1) * Work.Spaces.HkSq α 2 F := by
    have h1 := hKB' α F Ψ hα hα4 hEq h0 h1 hdec hOF hOP hsm hmF
    have h2 : KB * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        + Work.Spaces.HkSq α 2 F) ≤ KB * ((C₀ + 1) * Work.Spaces.HkSq α 2 F) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hKB)
      nlinarith [hPB, hFnn]
    have h3 : KB * ((C₀ + 1) * Work.Spaces.HkSq α 2 F)
        = KB * (C₀ + 1) * Work.Spaces.HkSq α 2 F := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hKA1 : 0 ≤ KA * (C₀ + 1) := by positivity
  have hKB1 : 0 ≤ KB * (C₀ + 1) := by positivity
  have hnA : α ^ 2 * Work.Spaces.HkNorm α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      ≤ Real.sqrt (KA * (C₀ + 1)) * Work.Spaces.HkNorm α 2 F := by
    have hsq : (α ^ 2 * Work.Spaces.HkNorm α 2 (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2
        = α ^ 4 * Work.Spaces.HkSq α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
      rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 2 _)]
      ring
    have hnn : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α 2 (fun z θ =>
        z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      mul_nonneg (pow_nonneg hα0 2) (Work.Spaces.HkNorm_nonneg α 2 _)
    have hkey : α ^ 2 * Work.Spaces.HkNorm α 2 (fun z θ =>
          z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        = Real.sqrt (α ^ 4 * Work.Spaces.HkSq α 2 (fun z θ =>
            z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
      rw [← hsq, Real.sqrt_sq hnn]
    rw [hkey]
    refine le_trans (Real.sqrt_le_sqrt hAfin) ?_
    rw [Real.sqrt_mul hKA1, Work.Spaces.HkNorm]
  have hnB : Work.Spaces.HkNorm α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ Real.sqrt (KB * (C₀ + 1)) * Work.Spaces.HkNorm α 2 F := by
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hBfin) ?_
    rw [Real.sqrt_mul hKB1, Work.Spaces.HkNorm]
  calc α ^ 2 * Work.Spaces.HkNorm α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkNorm α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ Real.sqrt (KA * (C₀ + 1)) * Work.Spaces.HkNorm α 2 F
        + Real.sqrt (KB * (C₀ + 1)) * Work.Spaces.HkNorm α 2 F := by linarith [hnA, hnB]
    _ = (Real.sqrt (KA * (C₀ + 1)) + Real.sqrt (KB * (C₀ + 1))) * Work.Spaces.HkNorm α 2 F := by
        ring
    _ ≤ (Real.sqrt (KA * (C₀ + 1)) + Real.sqrt (KB * (C₀ + 1)) + 1) * Work.Spaces.HkNorm α 2 F := by
        nlinarith [hFnorm]

end Work.FTS.EllipticEst
