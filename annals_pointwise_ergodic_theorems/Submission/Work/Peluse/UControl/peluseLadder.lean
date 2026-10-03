import Mathlib
import Submission.Work.Peluse.Nodes

/-!
# Peluse's Lemma 5.7 (the concatenation ladder's engine)

`Work.Peluse.UControl.peluseLadder` states the paper's Lemma 5.7 (*Bounds for sets with no
polynomial progressions*, Forum Math. Pi **8** (2020)) — the lemma by which the average of a family
of Gowers box norms over a parameter box is "peeled", one parameter at a time, the peeled
parameter's directions being lengthened from `M₁` to `M₁M₂` and the remaining ones staying at `M₁`.
Peluse's Proposition 3.6 is Lemma 5.7 iterated (one round per level of the nested family `A_j`).

The statement is *self-contained*: it quantifies over the data of the lemma and does not need the
nested family of Proposition 3.4.  Its proof is the paper's half page plus the box-norm expansion,
and it should be derived from `Work.Peluse.PeluseConcatenation` (Peluse's Theorem 3.5), which is the
theorem the paper applies.

## The data, in the workspace's notation

* `ι` — the index set `I`; `k : ι → ℕ` — the multiplicities `k_i`;
* `Slot ι k := Σ i, Fin (k i)` — the slots `(i,r)` (a sigma type!); `SlotSet ι k` — the nonempty
  *subsets* `ω` of the slots (the index set `I'`); `FamIdx kω := Σ_{ω} [k_ω]` — the index set of the
  hypothesis's family, whose level is `Fintype.card (FamIdx kω) = Σ_ω k_ω`;
* `A : Finset (Fin n → ℤ)` — the old parameter set; `paramBox M₂ : Finset (Slot ι k → ℤ)` — the box
  `((-M₂,M₂) ∩ ℤ)^t` of the new parameters `a'`;
* `pDir p M₁ a a' ω = arithIcc (∑_{s ∈ ω} p s.1 a * a' s) M₁` — the direction `p'_ω(a,a')[M₁]`;
* hypothesis: `γ ≤ E_{a ∈ A} E_{a'} boxNorm (level) (pDir p M₁ a a') (symIcc N) (f a)`, the support
  and sup bounds, and the paper's shift bound `|p i a| M₁ M₂ ≤ D N`;
* conclusion: there are `t'` and `c > 0` (uniform in the peeled slot `s₀`) such that for every slot
  `s₀ = (i₀,r₀)` the average over the remaining parameters `b` of the box norm at level
  `Fintype.card (ConclIdx s₀ kω t')` is at least `c γ^K`; the first `t'` direction sets are the
  (equal) long AP `arithIcc (p s₀.1 a) ⌊γ'M₁M₂⌋` and the remaining ones are
  `arithIcc (∑_{s ∈ ω} p s.1 a * b s) M₁` over the nonempty subsets `ω` of the slots *not*
  containing `s₀`;
* the paper's `γ' ≪ γ^{O_t(1)}` is carried as `γ' ≤ γ^K` and its non-degeneracy
  `M₁M₂ ≫_{C,t,(k_ω)} (γγ')^{-O(1)}` as `D⁻¹ (γγ')^{-K} ≤ M₁ M₂` (the paper's implied constant is
  displayed as `D`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- The slots `(i,r)`, `i ∈ ι`, `r ∈ [k_i]`, of Peluse's Lemma 5.7. -/
abbrev Slot (ι : Type) (k : ι → ℕ) : Type := Σ i : ι, Fin (k i)

/-- The nonempty subsets `ω` of the slots — the index set `I'` of the lemma. -/
abbrev SlotSet (ι : Type) (k : ι → ℕ) : Type := {s : Finset (Slot ι k) // s.Nonempty}

/-- The parameter box `((-M,M) ∩ ℤ)` on the slot type: the new parameters `a'` of the lemma. -/
def paramBox {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} (M : ℕ) :
    Finset (Slot ι k → ℤ) :=
  Fintype.piFinset (fun _ : Slot ι k => Finset.Ioo (-(M : ℤ)) (M : ℤ))

/-- Peluse's `p'_ω(a,a') = ∑_{(i,r) ∈ ω} p_i(a) a_{i,r}`, as the direction of length `M₁`. -/
def pDir {ι : Type} {k : ι → ℕ} {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a' : Slot ι k → ℤ) (ω : SlotSet ι k) : Finset ℤ :=
  arithIcc (∑ s ∈ ω.1, p s.1 a * a' s) M₁

/-- The index type `Σ_{ω ∈ I'} [k_ω]` of the hypothesis's family. -/
abbrev FamIdx {ι : Type} {k : ι → ℕ} (kω : SlotSet ι k → ℕ) : Type :=
  Σ ω : SlotSet ι k, Fin (kω ω)

/-- The hypothesis's family, as a function of the index `j`: the direction of `j`. -/
def pDirFam {ι : Type} {k : ι → ℕ} {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a' : Slot ι k → ℤ) {kω : SlotSet ι k → ℕ} (j : FamIdx kω) : Finset ℤ :=
  pDir p M₁ a a' j.1

/-- The conclusion's family index type (for the peeled slot `s₀`): the `t'` long directions
together with the `Σ_{ω ∈ J}[k_ω]` short ones, `J` being the nonempty subsets of the slots not
containing `s₀`.  Its cardinality is the level of the conclusion's box norm. -/
abbrev ConclIdx {ι : Type} {k : ι → ℕ} (s₀ : Slot ι k) (kω : SlotSet ι k → ℕ) (t' : ℕ) : Type :=
  Sum (Fin t') (Σ ω : {s : Finset (Slot ι k) // s.Nonempty ∧ s₀ ∉ s}, Fin (kω ⟨ω.1, ω.2.1⟩))

/-- The conclusion's direction family (a function of the sigma index type). -/
def conclDir {ι : Type} {k : ι → ℕ} {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Slot ι k) (t' : ℕ) (a : Fin n → ℤ) (b : Slot ι k → ℤ) {kω : SlotSet ι k → ℕ} :
    ConclIdx s₀ kω t' → Finset ℤ :=
  fun j => match j with
    | Sum.inl _ => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat
    | Sum.inr ⟨ω, r⟩ => arithIcc (∑ s ∈ ω.1, p s.1 a * b s) M₁

/-- **Peluse's Lemma 5.7**, in the workspace's normalisation.

Quantifier order and hypotheses, matching the source: for every datum `(k, kω, p, D)` (the index
set, the multiplicities of the hypothesis's family, the coefficient functions and the shift-bound
constant `D`, i.e. the paper's `C`) there are an exponent `K` and a constant `C₀` — both allowed to
depend on that datum, as in the paper's `O_{t,(k_ω)}(1)` — such that for every `A, M₁, M₂, N, γ, γ'`
and every `1`-bounded family `f` supported in `[-N,N]`:

* `γ' ≤ γ^K` (the paper's `γ' ≪_{C,t,(k_ω)} γ^{O_t(1)}`);
* `0 < p i a` and `p i a · M₁ M₂ ≤ N` for `a ∈ A` (the paper's (5.6) *without* slack, which is the
  form in which Theorem 3.5 is applied — the positive coefficient is the AP step of the conclusion);
* `C₀ · (γγ')^{-K} ≤ M₁ M₂` (the paper's `M₁M₂ ≫_{C,t,(k_ω)} (γγ')^{-O(1)}`);
* the family hypothesis `γ ≤ E_{a ∈ A} E_{a'} boxNorm (Σ_ω k_ω) (p'_ω(a,a')[M₁]) (symIcc N) (f a)`;

the conclusion is: there are `t' ≥ 1` and `c > 0` (uniform in the peeled slot `s₀`) such that for
every slot `s₀`, the average over the remaining parameters `b` of the box norm at level
`Fintype.card (ConclIdx s₀ kω t')` is at least `c γ^K`. -/
def PeluseLadder : Prop :=
  ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (kω : SlotSet ι k → ℕ)
    (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ),
    ∃ (K : ℕ) (C₀ : ℝ), 1 ≤ K ∧ 0 < C₀ ∧
      ∀ (A : Finset (Fin n → ℤ)) (M₁ M₂ N : ℕ) (γ γ' : ℝ) (f : (Fin n → ℤ) → ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N →
        ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
        0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ γ ^ K →
        (∀ i a, a ∈ A → 0 < p i a) →
        (∀ i a, a ∈ A → p i a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) →
        (∀ i a, a ∈ A → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ)) →
        (∀ a ∈ A, ∀ x, ‖f a x‖ ≤ 1) → (∀ a ∈ A, SupportIn (f a) N) →
        C₀ * (γ * γ') ^ (-(K : ℤ)) ≤ (M₁ : ℝ) * (M₂ : ℝ) →
        γ ≤ ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
              ∑ a ∈ A, ∑ a' ∈ paramBox (k := k) M₂,
                boxNorm (Fintype.card (FamIdx kω))
                  (fun j : Fin (Fintype.card (FamIdx kω)) =>
                    pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (f a) →
        ∃ (t' : ℕ) (c : ℝ), 1 ≤ t' ∧ 0 < c ∧
          ∀ s₀ : Slot ι k,
            c * γ ^ K ≤
              ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
                ∑ a ∈ A, ∑ b ∈ paramBox (k := k) M₂,
                  boxNorm (Fintype.card (ConclIdx s₀ kω t'))
                    (fun j : Fin (Fintype.card (ConclIdx s₀ kω t')) =>
                      conclDir p M₁ M₂ γ' s₀ t' a b
                        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
                    (symIcc N) (f a)

end

end Work.Peluse.UControl
