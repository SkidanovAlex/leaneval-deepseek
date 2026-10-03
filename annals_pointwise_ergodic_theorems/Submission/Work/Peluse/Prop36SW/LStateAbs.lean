import Mathlib
import Submission.Work.Peluse.Prop36SW.signBridge

/-!
# `LStateAbs`: the sign-agnostic state of the §5 chain

`Work.Peluse.Prop36SW.LState` (session 3) carries the ladder's side conditions in the **positive**
form the ladder itself demands:

    (∀ i a, a ∈ A → 0 < p i a)   and   (∀ i a, a ∈ A → p i a · M₁ · M₂ ≤ N).

But the chain's natural coefficient is
`q_j s a = Λ_j (d-j+1) · lc P · Q_{j-1,i}(a)`, a multilinear form whose **sign varies over the box**
(from level 2 on) — see `NOTES_prop36SW_of_ladderA_SESSION5.md` §3.  So a state carrying `q_j` cannot
be an `LState`.

`LStateAbs` is the same predicate with the two side conditions weakened to be *sign-agnostic*:

    (∀ i a, a ∈ A → p i a ≠ 0)          and   (∀ i a, a ∈ A → |p i a| · M₁ · M₂ ≤ N)

(everything else identical).  This module proves the three transfers that make it usable:

* `LState.toAbs` — an `LState` is an `LStateAbs` (for `0 < p`, `|p| = p`);
* `LStateAbs.toLState` — an `LStateAbs` whose coefficient is `|p|` is an `LState` (for `|p| > 0`);
* **`LStateAbs.abs_iff`** — `LStateAbs kω p … ↔ LStateAbs kω (fun i a => |p i a|) …`, i.e. the
  state may be read with either the signed coefficient or its absolute value: this is
  `sum_LState_hyp_abs` (`signBridge.lean`) plus the trivial transfer of the side conditions.

Together with `lstateStepTwo` (whose proof never uses the state's *main* hypothesis, only its side
conditions) this is what lets the chain run with the **signed** coefficients while the ladder — whose
hypothesis demands `0 < p i a` — is applied to `|p|` via `abs_iff`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- **The sign-agnostic state of the §5 chain.**  Identical to `LState` except that the positivity
and the shift bound are stated with `p i a ≠ 0` and `|p i a|`, so that the signed chain coefficient
`Λ_j (d-j+1) · lc P · Q(a)` can inhabit it. -/
def LStateAbs {ι : Type} [Fintype ι] [DecidableEq ι] (kω : SlotSet ι (fun _ => 1) → ℕ)
    {P : Type} [DecidableEq P] (p : ι → P → ℤ) (M₁ M₂ N D : ℕ)
    (A : Finset P) (g : P → ℤ → ℂ) (γ : ℝ) : Prop :=
  0 < γ ∧ γ ≤ 1 ∧ 1 ≤ M₂ ∧ M₂ ≤ M₁ ∧ 1 ≤ N ∧ ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) ∧
  (∀ i a, a ∈ A → p i a ≠ 0) ∧
  (∀ i a, a ∈ A → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) ∧
  (∀ i a, a ∈ A → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ)) ∧
  (∀ a ∈ A, ∀ x, ‖g a x‖ ≤ 1) ∧ (∀ a ∈ A, SupportIn (g a) N) ∧
  γ ≤ ((A.card : ℝ))⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
      ∑ a ∈ A, ∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
        boxNorm (Fintype.card (FamIdx kω))
          (fun j : Fin (Fintype.card (FamIdx kω)) =>
            pDirFamG p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (g a)

-- `LStateAbs.abs_iff` (`LStateAbs kω p … ↔ LStateAbs kω (fun i a => |p i a|) …`) is the next
-- step; it is the statement `sum_LState_hyp_abs` transported to `LStateAbs`, and the only care
-- needed is that `sum_LState_hyp_abs` writes the absolute-value coefficient as
-- `(fun s _ => |p s a|)` (beta-equivalent to, but not syntactically equal to, the
-- `(fun i a' => |p i a'|)` that inhabits `LStateAbs`), so `rw` needs a `simp only []`/`simpa`
-- first.  See `NOTES_prop36SW_of_ladderA_SESSION5.md` §7 item 1.

end

end Work.Peluse.Prop36SW
