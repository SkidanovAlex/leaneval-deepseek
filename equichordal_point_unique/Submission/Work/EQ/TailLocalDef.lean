import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs

/-! # The product neighbourhoods of `H0` and the local boundedness of the tail index

`Work.EQ.tailP_bdd_on_compact` (the tail index is bounded on compact subsets of `H0`) is the
compactness corollary of the *local* boundedness of the tail index, recorded here:

* `tailNbhd p K ε` — a product neighbourhood of `p`: finitely many chain coordinates
  (`|k| ≤ K`) and the two linearising parameters, each within `ε`;
* `TailLocallyBounded a h` — every point of `H0 a h` has such a neighbourhood on which the
  forward tail is uniformly the principal leaf.

`tailNbhd` is open (`isOpen_tailNbhd`), so a compact `C ⊆ H0` is covered by finitely many of
these neighbourhoods, and the maximum of the finitely many indices is the uniform bound; that
assembly is `Work.EQ.tailP_bdd_of_locallyBounded` in
`Submission.Work.EQ.tailP_bdd_on_compact`.

## Route to `TailLocallyBounded a h`

* `Work.EQ.chain_eq_fan` (`H0_invParam_ge`, proved) reads the `0`-th point of a chain as a fan
  value `p.1 0 = fan a h ε p.2.1`; applied to the shift `shiftZ a n p` it gives the suffix form
  `p.1 n = fan a h ε (λⁿ ψ₁ p)`.  If `n < tailIdx p` then the last letter of `ε` is `false`
  (the last letter is `true` exactly when `invBranch true (germC (λ^{n+1}ψ₁)) = germC (λⁿψ₁)`,
  which would make `n` a principal-tail index).
* Separation: for `ε` ending in `false` the point `fan a h ε v` stays a definite distance away
  from `germC a h v` (that is `Work.EQ.fan_ne_germC`).  The two backward branches at a regular
  point are distinct (`invBranch_true_ne_false`), and `Work.EQ.fan_induction` (`fan_estimates`)
  bounds the deviation of every fan point from its centre, so the only case needing care is the
  one where the fan point lies near the *same* centre `A₁ = -1/2` as the germ point; there the
  characteristic value `Work.EQ.charVal` (a product of the walk weights, `charVal_props`,
  `walk_bounds`, `walk_count`) is `< 1` with a definite gap, giving the separation.
* Contradiction: if `p ∈ H0` had no such neighbourhood, choosing `K = N = k`, `ε = 1/(k+1)`
  would give `q_k ∈ H0` with `q_k → p` and `tailIdx q_k > k`; with `n := tailIdx p` the points
  `fan a h ε_k (λⁿ ψ₁ q_k) = q_k.1 n` would converge to `germC a h (λⁿ ψ₁ p)`, contradicting the
  separation.-/

namespace Work.EQ

open Filter _root_.Topology
open Complex
open Classical

noncomputable section

/-- A *product neighbourhood* of `p`: finitely many chain coordinates and the two linearising
parameters, each within `ε`.  These are the neighbourhoods of the product topology. -/
def tailNbhd (p : ChainData) (K : ℕ) (ε : ℝ) : Set ChainData :=
  {q | (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - p.1 k‖ < ε) ∧ ‖q.2.1 - p.2.1‖ < ε ∧
      ‖q.2.2 - p.2.2‖ < ε}

lemma isOpen_tailNbhd (p : ChainData) (K : ℕ) (ε : ℝ) : IsOpen (tailNbhd p K ε) := by
  have h1 : {q : ChainData | ∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - p.1 k‖ < ε}
      = ⋂ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), {q : ChainData | ‖q.1 k - p.1 k‖ < ε} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Icc, abs_le]
  have h2 : IsOpen {q : ChainData | ∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - p.1 k‖ < ε} := by
    rw [h1]
    exact isOpen_biInter_finset fun k _ =>
      isOpen_lt (continuous_norm.comp (((continuous_apply k).comp continuous_fst).sub
        continuous_const)) continuous_const
  have h3 : IsOpen {q : ChainData | ‖q.2.1 - p.2.1‖ < ε} :=
    isOpen_lt (continuous_norm.comp ((continuous_fst.comp continuous_snd).sub continuous_const))
      continuous_const
  have h4 : IsOpen {q : ChainData | ‖q.2.2 - p.2.2‖ < ε} :=
    isOpen_lt (continuous_norm.comp ((continuous_snd.comp continuous_snd).sub continuous_const))
      continuous_const
  exact h2.inter (h3.inter h4)

/-- **Local boundedness of the tail index** (the analytic input): every point of `H0` has a
product neighbourhood on which the forward tail is uniformly the principal leaf. -/
def TailLocallyBounded (a : ℝ) (h : ℂ → ℂ) : Prop :=
  ∀ p ∈ H0 a h, ∃ (N K : ℕ) (ε : ℝ), 0 < ε ∧
    ∀ q ∈ H0 a h, q ∈ tailNbhd p K ε → TailP a h q N

end

end Work.EQ
