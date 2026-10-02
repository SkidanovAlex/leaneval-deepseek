import Submission.EFL.Nibble
import Submission.Work.Deep.Nibble.NibbleFinal

/-!
# `lem:nibble2` (the Nibble Lemma) in the form the §12 chain consumes

The Nibble Lemma of the paper (`lem:nibble2`), in the **asymptotic form** in which it is
proved by the `Deep/Nibble` chapter: the constants `r, β, γ, ε, ρ, ξ` are fixed first
(subject to the `n`-free relations of `Work.Deep.Nibble.MarginsConst`) and *only then* is a
threshold `N₀` chosen; the conclusion then holds for every `n ≥ N₀`.

* `NibbleStatementFixed` — the statement, as a `Prop`.  It is *definitionally* the type of
  `Work.Deep.Nibble.nibbleStatementFixed` (the chapter's headline), so
  `Submission.lean` can write `have hNib : NibbleStatementFixed :=
  Work.Deep.Nibble.nibbleStatementFixed`.
* `NibblePointwise r β γ ε ρ ξ n` — the same conclusion, at the *fixed* constants
  `(r, β, γ, ε, ρ, ξ)` and at the *fixed* `n`, without a threshold.  This is the form the
  §12 chain carries down to its single application site (`s12_step6`).
* `nibbleThr r β γ ε ρ ξ` — the threshold chosen from the deep input (by `Classical.choose`
  from `NibbleStatementFixed`), and `nibbleAbove_nibbleThr`: it *is* a threshold, i.e. every
  `n ≥ nibbleThr …` carries the pointwise statement.  A §12 branch that knows its own
  constants can therefore take its threshold to be (at least) `nibbleThr …`.
* `marginsConst_of_bundle` — the (small) bridge between the cone's margin bundle
  `NibbleMarginsStrong` and the chapter's constant conditions `MarginsConst`: it needs
  `3 ≤ r` and `4·10⁻⁹ ε ≤ ρ`, both of which the §12 constants satisfy.

The pointwise-in-`n` form with *no* threshold (what `NibbleStatementFixed` used to be) is
*stronger* than the paper's lemma — the chapter's `NOTES_SESSION7.md` (defect D7) shows that
the `10^400`-large bounds of `NibbleMarginsStrong` do not dominate the actual threshold —
and is not what the chapter proves.  The §12 chain was accordingly re-wired to carry
`NibblePointwise` above `nibbleThr` instead.
-/

set_option autoImplicit false

open scoped BigOperators

open Classical

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **The Nibble Lemma (`lem:nibble2`)**, in the paper's asymptotic form: constants first
(as in `Work.Deep.Nibble.MarginsConst`), then a threshold `N₀`, then all `n ≥ N₀`. -/
def NibbleStatementFixed : Prop :=
  ∀ (r : ℕ) (β γ ε ρ ξ : ℝ), Work.Deep.Nibble.MarginsConst r β γ ε ρ ξ →
    ∃ N₀ : ℕ, ∀ (n : ℕ), N₀ ≤ n →
      ∀ (D : ℕ) (𝓗 𝓗' : MultiHypergraph n) (R : Hypergraph (Fin n))
        {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} (M : Fin D → Set (Set (Fin n))),
        NibbleMarginsStrong n (D : ℝ) r β γ ε ρ ξ →
        U = VplusTwo (MultiHypergraph.pow2 𝓗) (1 - ε) → S ⊆ U →
        ((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) →
          (D : ℝ) + γ * (n : ℝ) ≤ (S.ncard : ℝ)) →
        U ∈ 𝓥 → (Set.univ : Set (Fin n)) ∈ 𝓥 →
        IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) R 𝓥 ρ γ ξ →
        𝓗.IsLinear → 𝓗' ≤ 𝓗 → (∀ e ∈ 𝓗'.edges, e ∉ R) → 𝓗'.IsLinear →
        (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
        (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ)) →
        (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
        (∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j)) →
        (∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet) → (∀ i, ∀ e ∈ M i, e ∉ R) →
        (∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ)) →
        (∀ e ∈ 𝓗'.edgeSet,
          (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) →
        NibbleConclusion (U := U) (S := S) (γ := γ) (β := β) (ε := ε) 𝓗 𝓗' R M

/-- The Nibble Lemma **above its threshold**, at *fixed* constants and *fixed* `n`: this is
the form the §12 chain threads (the constants of a §12 branch are fixed before `n`, so the
only extra information needed is the threshold, which the branch absorbs into its own
threshold `N`). -/
def NibblePointwise (r : ℕ) (β γ ε ρ ξ : ℝ) (n : ℕ) : Prop :=
  ∀ (D : ℕ) (𝓗 𝓗' : MultiHypergraph n) (R : Hypergraph (Fin n))
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} (M : Fin D → Set (Set (Fin n))),
    NibbleMarginsStrong n (D : ℝ) r β γ ε ρ ξ →
    U = VplusTwo (MultiHypergraph.pow2 𝓗) (1 - ε) → S ⊆ U →
    ((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (D : ℝ) + γ * (n : ℝ) ≤ (S.ncard : ℝ)) →
    U ∈ 𝓥 → (Set.univ : Set (Fin n)) ∈ 𝓥 →
    IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) R 𝓥 ρ γ ξ →
    𝓗.IsLinear → 𝓗' ≤ 𝓗 → (∀ e ∈ 𝓗'.edges, e ∉ R) → 𝓗'.IsLinear →
    (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
    (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ)) →
    (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
    (∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j)) →
    (∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet) → (∀ i, ∀ e ∈ M i, e ∉ R) →
    (∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ)) →
    (∀ e ∈ 𝓗'.edgeSet,
      (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) →
    NibbleConclusion (U := U) (S := S) (γ := γ) (β := β) (ε := ε) 𝓗 𝓗' R M

/-- **`lem:nibble2`, proved** (the chapter's headline, re-exported at the cone's type). -/
theorem nibbleStatementFixed_cone : NibbleStatementFixed :=
  Work.Deep.Nibble.nibbleStatementFixed

/-- The threshold of the Nibble Lemma at the constants `(r, β, γ, ε, ρ, ξ)`: the witness of
`NibbleStatementFixed` (chosen classically; it is `0` when the constant conditions fail). -/
noncomputable def nibbleThr (r : ℕ) (β γ ε ρ ξ : ℝ) : ℕ :=
  if h : Work.Deep.Nibble.MarginsConst r β γ ε ρ ξ then
    Classical.choose (Work.Deep.Nibble.nibbleStatementFixed r β γ ε ρ ξ h) else 0

/-- `nibbleThr` unfolds to the deep input's witness. -/
theorem nibbleThr_eq {r : ℕ} {β γ ε ρ ξ : ℝ}
    (h : Work.Deep.Nibble.MarginsConst r β γ ε ρ ξ) :
    nibbleThr r β γ ε ρ ξ =
      Classical.choose (Work.Deep.Nibble.nibbleStatementFixed r β γ ε ρ ξ h) := by
  unfold nibbleThr
  rw [dif_pos h]

/-- **`nibbleThr` is a threshold**: every `n ≥ nibbleThr r β γ ε ρ ξ` carries the pointwise
Nibble Lemma at those constants. -/
theorem nibbleAbove_nibbleThr {r : ℕ} {β γ ε ρ ξ : ℝ}
    (h : Work.Deep.Nibble.MarginsConst r β γ ε ρ ξ) :
    ∀ {n : ℕ}, nibbleThr r β γ ε ρ ξ ≤ n → NibblePointwise r β γ ε ρ ξ n := by
  intro n hn
  rw [nibbleThr_eq h] at hn
  exact Classical.choose_spec (Work.Deep.Nibble.nibbleStatementFixed r β γ ε ρ ξ h) n hn

/-- **From the cone's margin bundle to the chapter's constant conditions.**  The only two
facts the bundle does not already contain are `3 ≤ r` (the chapter's `lem:embed` and
`lem:pseudorandom_matching` need it) and `4·10⁻⁹ ε ≤ ρ` (which turns the bundle's
`10^12 ξ ≤ γρε` into the crossing-absorption field `4000 ξ ≤ γρ²`); both hold for the §12
constants. -/
theorem marginsConst_of_bundle {n : ℕ} {D : ℝ} {r : ℕ} {β γ ε ρ ξ : ℝ}
    (hm : NibbleMarginsStrong n D r β γ ε ρ ξ) (hr3 : 3 ≤ r)
    (hε9 : 4 * 10 ^ (-9 : ℤ) * ε ≤ ρ) :
    Work.Deep.Nibble.MarginsConst r β γ ε ρ ξ := by
  refine Work.Deep.Nibble.marginsConst_of_strong hm ?_ hr3
  have hγ0 : (0 : ℝ) < γ := hm.base.hγ0
  have hρ0 : (0 : ℝ) < ρ := hm.base.hρ0
  have hξ := hm.hξ
  have hε9' : (4 : ℝ) / 10 ^ 9 * ε ≤ ρ := by
    have h : (4 : ℝ) * 10 ^ (-9 : ℤ) = 4 / 10 ^ 9 := by norm_num [zpow_neg]
    rwa [h] at hε9
  have hL : (4 : ℝ) / 10 ^ 9 * (10 ^ 12 * ξ) = 4000 * ξ := by ring
  have hmul : (4 : ℝ) / 10 ^ 9 * (10 ^ 12 * ξ) ≤
      (4 : ℝ) / 10 ^ 9 * (γ * ρ * ε) :=
    mul_le_mul_of_nonneg_left hξ (by norm_num)
  have hrc : (4 : ℝ) / 10 ^ 9 * (γ * ρ * ε) = γ * ρ * ((4 : ℝ) / 10 ^ 9 * ε) := by ring
  have hstep2 : γ * ρ * ((4 : ℝ) / 10 ^ 9 * ε) ≤ γ * ρ * ρ :=
    mul_le_mul_of_nonneg_left hε9' (le_of_lt (mul_pos hγ0 hρ0))
  linarith [hL, hmul, hrc, hstep2]

end

end ErdosFaberLovaszConjecture
