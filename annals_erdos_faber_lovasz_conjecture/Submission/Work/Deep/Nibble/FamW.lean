import Submission.Work.Deep.Nibble.FamWaste
import Submission.Work.Deep.Nibble.r2_Wfam_mean

/-!
# The per-set clauses of one round, in edge-charged (`badSum`) form

One round of the "wasteful" Rödl nibble keeps every edge of the `r`-uniform
linear hypergraph `𝓖` independently with probability `p = θ/D`, and matches the
*isolated* kept edges.  For a prescribed finite vertex set `S` the vertices split
into *uncovered*, *matched* and *wasted* (`FamWaste`), and the iteration of the
round only needs the two one-sided bounds

* `uncovFam 𝓖 ω S ≤ (e^{-θ} + δ)|S|` — the residual set shrinks by `e^{-θ}`;
* `wasteFam 𝓖 ω S ≤ (1+δ)·2rθ²·|S|` — the waste is small.

The second is obtained from `wasteFam ≤ badSum` (`wasteFam_le_badSum`), whose mean
is `≤ 2rθ²|S|` (`r2_Wfam_mean`); its tail is `Work.Deep.Nibble.r2_Wfam_tail`.
This is the per-set vocabulary of the family nibble: it deliberately avoids the
*matched* count, whose natural Bruhn–Joos certificate has size `O(rD|S|)` and
therefore degrades with `D`, whereas `badSum` has a certificate of size
`O(θ|S|)`.

The set-valued form `RoundGoodFamF` (two-sided, in `FamEst`) is *not* used by the
iteration; `RoundGoodFamW` below is the one-sided predicate the iteration
consumes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped BigOperators

namespace Work.Deep.Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The per-set clauses of one (wasteful) round, one-sided form.**  For every
member `S` of the family `𝓕`: at most a `(e^{-θ}+δ)`-fraction of `S` is left
uncovered, and at most a `(1+δ)·2rθ²`-fraction is wasted. -/
noncomputable def RoundGoodFamW (𝓖 : Set (Set V)) (r : ℕ) (θ δ : ℝ)
    (𝓕 : Finset (Finset V)) (ω : 𝓖 → Bool) : Prop :=
  (∀ S ∈ 𝓕, ((uncovFam 𝓖 ω S : ℕ) : ℝ) ≤ (Real.exp (-θ) + δ) * (S.card : ℝ)) ∧
  (∀ S ∈ 𝓕, ((badSum 𝓖 ω S : ℕ) : ℝ) ≤ (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ))

/-- Monotonicity in the family: a smaller family is easier. -/
theorem RoundGoodFamW.mono {𝓖 : Set (Set V)} {r : ℕ} {θ δ : ℝ} {𝓕 𝓕' : Finset (Finset V)}
    {ω : 𝓖 → Bool} (h : RoundGoodFamW 𝓖 r θ δ 𝓕 ω) (hsub : 𝓕' ⊆ 𝓕) :
    RoundGoodFamW 𝓖 r θ δ 𝓕' ω :=
  ⟨fun S hS => h.1 S (hsub hS), fun S hS => h.2 S (hsub hS)⟩

/-- The uncovered count of a prescribed set is at most its size. -/
theorem uncovFam_le_card (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    uncovFam 𝓖 ω S ≤ S.card := by
  classical
  exact Finset.card_filter_le _ _

/-- The edge-charged waste vanishes on an edgeless hypergraph. -/
theorem badSum_eq_zero_of_empty {𝓖 : Set (Set V)} (h : 𝓖 = ∅) (ω : 𝓖 → Bool)
    (S : Finset V) : badSum 𝓖 ω S = 0 := by
  classical
  subst h
  simp [badSum]

end Work.Deep.Nibble
