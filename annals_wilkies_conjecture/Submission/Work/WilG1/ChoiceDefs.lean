/-
  WilG1 — definitions for effective definable choice (BNZ §2.3).

  Given a definable set `K ⊆ ℝ^{p+1}` (a cell of a cylindrical decomposition) and a definable
  set of parameters `R ⊆ ℝ^p`, we build a set `selSet K R ⊆ ℝ^{p+1}` which, for every `l ∈ R`
  whose fibre `{t | (l,t) ∈ K}` is nonempty, is the graph of a *single* point of that fibre.

  The fibre of a cell is either a point or an open interval (possibly a half-line, possibly
  `ℝ`), by `WilG4a.isCell_fiber`.  Four cases give the selection:

  * the fibre is all of `ℝ`                               — take `t = 0`;
  * the fibre has a centre of symmetry (a point or a bounded interval) — take that centre;
  * the fibre is unbounded above (a half-line `(a,∞)`)    — take `t` with `t - 1 = inf`;
  * the fibre is unbounded below                          — symmetric.

  All the conditions are first-order over `K`, so the resulting set is again an `Ω`-set; this
  is the content of the (delegated) membership lemmas.
-/
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG1

open WilkiesDesign WilkiesConjecture

/-- `t` lies in the fibre of `K ⊆ ℝ^{p+1}` over the parameter `l : Fin p → ℝ`. -/
def inFib {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (t : ℝ) : Prop :=
  Fin.snoc l t ∈ K

/-- The fibre of `K` over `l` is all of `ℝ`. -/
def isAll {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) : Prop :=
  ∀ s : ℝ, inFib K l s

/-- The fibre of `K` over `l` is unbounded above. -/
def unbAbove {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) : Prop :=
  ∀ M : ℝ, ∃ s : ℝ, inFib K l s ∧ M < s

/-- The fibre of `K` over `l` is unbounded below. -/
def unbBelow {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) : Prop :=
  ∀ M : ℝ, ∃ s : ℝ, inFib K l s ∧ s < M

/-- `t` is a centre of symmetry of the fibre of `K` over `l`. -/
def isCentre {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (t : ℝ) : Prop :=
  ∀ s : ℝ, (inFib K l (t + s) ↔ inFib K l (t - s))

/-- The selection set: over the region `R`, the graph of the selected point of the fibre. -/
def selSet {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) (R : Set (Fin p → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z | Fin.init z ∈ R ∧
    ( (isAll K (Fin.init z) ∧ z (Fin.last p) = 0)
      ∨ (isCentre K (Fin.init z) (z (Fin.last p)) ∧
          ∃ c : ℝ, isCentre K (Fin.init z) c ∧ ∀ c' : ℝ, isCentre K (Fin.init z) c' → c' = c)
      ∨ (inFib K (Fin.init z) (z (Fin.last p)) ∧
          ¬ inFib K (Fin.init z) (z (Fin.last p) - 1) ∧
          (∀ s : ℝ, 0 < s → s < 1 → inFib K (Fin.init z) (z (Fin.last p) - 1 + s)) ∧
          unbAbove K (Fin.init z))
      ∨ (inFib K (Fin.init z) (z (Fin.last p)) ∧
          ¬ inFib K (Fin.init z) (z (Fin.last p) + 1) ∧
          (∀ s : ℝ, 0 < s → s < 1 → inFib K (Fin.init z) (z (Fin.last p) + 1 - s)) ∧
          unbBelow K (Fin.init z))) }

/-- The projection of `K ⊆ ℝ^{p+1}` to the parameter space. -/
def projPar {p : ℕ} (K : Set (Fin (p + 1) → ℝ)) : Set (Fin p → ℝ) :=
  {l | ∃ t : ℝ, inFib K l t}

end Work.WilG1
