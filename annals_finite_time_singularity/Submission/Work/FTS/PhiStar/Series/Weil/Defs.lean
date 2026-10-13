/-
# `Weil/Defs` — notation for the Weyl-lemma route to `SmoothOpen (psiSeries α (RemSource α ψ))`

The smoothness conjunct of `psiSeries_solves_rem` is obtained from the *interior* regularity of
the elliptic operator `bslOp α` on the open quadrant `Q0 = (0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.Final.interiorSmoothQ0_fts`: Weyl's lemma for `bslOp α`, weight
`z^{(5-α)/α} cos θ`), whose hypotheses are

* `SmoothOpen F` and `LocallyIntegrableOn (uncurry Ψ) Q0` for the datum/solution, and
* the *weak* (test-function) formulation
  `∫_{Q0} Ψ·(bslOp α φ)·w = ∫_{Q0} F·φ·w` for every `φ` smooth and compactly supported in `Q0`.

The theorem then returns a `C^∞` function `Φ` with `Ψ =ᵐ Φ`; combining with the continuity of
`Ψ` on `Q0` (which the mode series has, by local uniform convergence from the term majorant)
upgrades the a.e. identity to a pointwise one, giving `SmoothOpen Ψ` itself.

This file fixes the notation shared by the pieces of that argument:

* `R α ψ` — the mode series `psiSeries α (RemSource α ψ)`;
* `trm α ψ m` — its `m`-th mode term `acoeff α m (RemSource α ψ) z · eFam m θ`;
* `wgt α` — the weight `p.1^((5-α)/α)·cos p.2` of the weak formulation;
* `box` — the closed boxes `[a,b] × [c,d] ⊆ Q0` on which the majorant is uniform;
* `csrc α ψ N` — the `N`-th partial sum of the *source* series `Σ_m cmode m (RemSource α ψ)·e_m`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false

/-- The mode series of the remainder source: the function whose `C^∞`-regularity on `Q0` is
conjunct 1 of `psiSeries_solves_rem`. -/
abbrev R (α : ℝ) (ψ : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ

/-- The `m`-th mode term of `R α ψ`. -/
abbrev trm (α : ℝ) (ψ : ℝ → ℝ) (m : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
    * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- The weight of the weak formulation of `bslOp α` on the quadrant,
`z^{(5-α)/α}·cos θ` (the weight that puts `bslOp α` into divergence form). -/
def wgt (α : ℝ) (p : ℝ × ℝ) : ℝ := p.1 ^ ((5 - α) / α) * Real.cos p.2

/-- The truncated source: the `N`-th partial sum of `Σ_m cmode m (RemSource α ψ) · e_m`. -/
abbrev csrc (α : ℝ) (ψ : ℝ → ℝ) (N : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ m ∈ Finset.range (N + 1),
    Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- A closed box `[a,b] × [c,d]` of the quadrant. -/
def box (a b c d : ℝ) : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d

@[simp] theorem R_apply (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    R α ψ z θ = Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ := rfl

@[simp] theorem trm_apply (α : ℝ) (ψ : ℝ → ℝ) (m : ℕ) (z θ : ℝ) :
    trm α ψ m z θ = Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ := rfl

@[simp] theorem wgt_apply (α : ℝ) (p : ℝ × ℝ) :
    wgt α p = p.1 ^ ((5 - α) / α) * Real.cos p.2 := rfl

@[simp] theorem csrc_apply (α : ℝ) (ψ : ℝ → ℝ) (N : ℕ) (z θ : ℝ) :
    csrc α ψ N z θ = ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ := rfl

theorem mem_box {a b c d : ℝ} {p : ℝ × ℝ} :
    p ∈ box a b c d ↔ p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc c d := Iff.rfl

/-- A box with `0 < a`, `a ≤ b`, `0 < c`, `c ≤ d < π/2` lies in the open quadrant. -/
theorem box_subset_Q0 {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < π / 2) : box a b c d ⊆ Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨h1, h2⟩ := mem_box.mp hp
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha h1.1, lt_of_lt_of_le hc h2.1,
    lt_of_le_of_lt h2.2 hd⟩

/-- The mode series is the `tsum` of the mode terms. -/
theorem R_eq_tsum (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    R α ψ z θ = ∑' m : ℕ, trm α ψ m z θ := rfl

end Work.FTS.PhiStar.Series.Weil
