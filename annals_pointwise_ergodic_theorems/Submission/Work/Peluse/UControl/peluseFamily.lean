import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The nested PET family of Peluse's §3, and the two chapters of her §§4-6

This module fixes the *vocabulary* of Peluse's nested index construction (S. Peluse, *Bounds for sets
with no polynomial progressions*, Forum of Math. Pi **8** (2020), §3) and states the two chapters of
her §4-§6 chain for the configuration `(x, x + y, x + P(y))` (`2 ≤ deg P = d`) obtained by embedding
it in the full polynomial progression `(x, x+y, x+y², …, x+y^{d-1}, x+P(y))` (`P_i = X^i` for
`i = 1,…,d-1`, `P_d = P`).

## Peluse's index construction

For `j = 0,1,…,ℓ-1`:

* `I_0 = {0}` and, for `j ≥ 1`, `I_j` is the set of *nonempty subsets* of the "slots" of level `j`;
* the slots of level `j + 1` are the pairs `(i, r)` with `i ∈ I_j` and `1 ≤ r ≤ k_i`, where the
  multiplicities `k_i ≪_ℓ 1` are part of the datum;
* `A_0 = {c}` (the base direction) and, for `j ≥ 1`,
  `A_j = {Σ_{(i,r) ∈ ω} (ℓ - j + 1)·p_i·a_{i,r} : ω ∈ I_j}`, where `p_i ∈ A_{j-1}` is the direction of
  the index `i ∈ I_{j-1}` and `a_{i,r}` are the level-`j` parameters.

The slot types `S j` and the attachment maps `S (j+1) → I_j` are collected in the structure
`IdxDatum`; `I j` and `dir j` below are the paper's `I_j` and the evaluation of `A_j`.

## The two chapters

* `Prop34` (the paper's Proposition 3.4, specialised to the embeddable configuration): a large
  multilinear average along the progression forces the average, over the parameter box
  `(-⌊δ'M⌋, ⌊δ'M⌋)^{Σ|S j|}`, of the level-`|I_{ℓ-1}|` box-norm power of the last function at the
  directions `p(⌊δ'M⌋)`, `p ∈ A_{ℓ-1}`.
* `Prop36` (the paper's Proposition 3.6): that family average is concatenated (by iterating her
  Lemma 5.7, whose engine is Theorem 3.5 = `Work.Peluse.PeluseConcatenation`) up to a single
  uniformity-norm power at the long scale `ℓ!·c_ℓ·[δ'M^ℓ]`.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- Peluse's index/slot datum: for each level `j` the type `S j` of the level-`j` slots, and, for
each `j`, an attachment map sending every level-`(j+1)` slot to the nonempty subset of level-`j`
slots it belongs to (the paper's `k_i`: the level-`(j+1)` slots attached to `i ∈ I_j` are exactly the
points of the fibre `par j ⁻¹ {i}`). -/
structure IdxDatum where
  S : ℕ → Type
  [finS : ∀ j : ℕ, Fintype (S j)]
  [decS : ∀ j : ℕ, DecidableEq (S j)]
  par : (j : ℕ) → S (j + 1) → {T : Finset (S j) // T.Nonempty}

namespace IdxDatum

instance (D : IdxDatum) (j : ℕ) : Fintype (D.S j) := D.finS j
instance (D : IdxDatum) (j : ℕ) : DecidableEq (D.S j) := D.decS j

/-- Peluse's `I_j`: the nonempty subsets of the level-`j` slots. -/
def I (D : IdxDatum) (j : ℕ) : Type := {T : Finset (D.S j) // T.Nonempty}

instance (D : IdxDatum) (j : ℕ) : Fintype (D.I j) :=
  inferInstanceAs (Fintype {T : Finset (D.S j) // T.Nonempty})
instance (D : IdxDatum) (j : ℕ) : DecidableEq (D.I j) :=
  inferInstanceAs (DecidableEq {T : Finset (D.S j) // T.Nonempty})

/-- Peluse's `A_j`, evaluated: the direction attached to the index `w ∈ I_j` at the parameter
family `a`.  `dir D ℓ c 0 _ _ = c` is the base `A_0 = {c}`, and for a level `j+1` direction `w`,
`dir D ℓ c (j+1) w a = Σ_{s ∈ w} (ℓ - j)·(dir D ℓ c j (par j s) a)·a s`. -/
def dir (D : IdxDatum) (l : ℕ) (c : ℤ) : (j : ℕ) → D.I j → ((j : ℕ) → D.S j → ℤ) → ℤ
  | 0, _, _ => c
  | (j+1), w, a => ∑ s ∈ w.val, (((l : ℤ) - (j : ℤ)) * D.dir l c j (D.par j s) a) * a (j+1) s

/-- The parameter family at the levels `0,…,ℓ-1`. -/
abbrev Idx (D : IdxDatum) (l : ℕ) : Type := (j : Fin l) → D.S j → ℤ

/-- Extension of a parameter family at the levels `< ℓ` to all levels (the extra values are
irrelevant: `dir` only reads levels `≤ ℓ-1`). -/
def pad (D : IdxDatum) (l : ℕ) (a : D.Idx l) : (j : ℕ) → D.S j → ℤ :=
  fun j s => if h : j < l then a ⟨j, h⟩ s else 0

/-- The parametrisation of a box value: `Fin (2H+1) → ℤ` by `k ↦ k - H`. -/
def boxVal (H : ℕ) (k : Fin (2 * H + 1)) : ℤ := (k : ℤ) - (H : ℤ)

lemma boxVal_mem (H : ℕ) (k : Fin (2 * H + 1)) :
    -(H : ℤ) ≤ boxVal H k ∧ boxVal H k ≤ (H : ℤ) := by
  have h1 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
  have h2 : (k : ℤ) < (2 * H + 1 : ℕ) := by exact_mod_cast k.isLt
  refine ⟨?_, ?_⟩ <;> simp only [boxVal] <;> omega

/-- The parameter box `((-H,H) ∩ ℤ)^{Σ_j |S_j|}`. -/
def parBox (D : IdxDatum) (l H : ℕ) : Finset (D.Idx l) :=
  (Fintype.piFinset fun j : Fin l =>
    Fintype.piFinset fun _ : D.S j => (Finset.univ : Finset (Fin (2 * H + 1)))).image
    fun f => fun j s => boxVal H (f j s)

lemma mem_parBox {D : IdxDatum} {l H : ℕ} {a : D.Idx l} :
    a ∈ D.parBox l H ↔ ∀ j s, -(H : ℤ) ≤ a j s ∧ a j s ≤ (H : ℤ) := by
  constructor
  · intro h j s
    rw [parBox, Finset.mem_image] at h
    obtain ⟨f, _, rfl⟩ := h
    exact boxVal_mem H (f j s)
  · intro h
    rw [parBox, Finset.mem_image]
    refine ⟨fun j s => ⟨Int.toNat (a j s + H), ?_⟩, ?_, ?_⟩
    · have h1 : a j s + H < (2 * H + 1 : ℕ) := by
        have := (h j s).2
        omega
      have h0 : 0 ≤ a j s + H := by have := (h j s).1; omega
      omega
    · simp
    · funext j s
      simp only [boxVal]
      have h0 : 0 ≤ a j s + H := by have := (h j s).1; omega
      have h1 : (Int.toNat (a j s + H) : ℤ) = a j s + H := Int.toNat_of_nonneg h0
      omega

/-- The level-`|I_{ℓ-1}|` box norm of `f` at the directions `p(a)[H]`, `p ∈ A_{ℓ-1}` (a *norm*, not
a power: this is the normalisation used by the paper, by Lemma 5.7 and by
`Work.Peluse.PeluseConcatenation`). -/
def famNorm (D : IdxDatum) (l H : ℕ) (c : ℤ) (N : ℕ) (a : D.Idx l) (f : ℤ → ℂ) : ℝ :=
  boxNorm (Fintype.card (D.I (l - 1)))
    (fun i : Fin (Fintype.card (D.I (l - 1))) =>
      arithIcc (D.dir l c (l - 1) ((Fintype.equivFin (D.I (l - 1))).symm i) (D.pad l a)) H)
    (symIcc N) f

/-- The average of `famNorm` over the parameter box: the quantity produced by Proposition 3.4 and
consumed by Proposition 3.6. -/
def famAvg (D : IdxDatum) (l H : ℕ) (c : ℤ) (N : ℕ) (f : ℤ → ℂ) : ℝ :=
  (((D.parBox l H).card : ℕ) : ℝ)⁻¹ * ∑ a ∈ D.parBox l H, D.famNorm l H c N a f

lemma famAvg_nonneg (D : IdxDatum) (l H : ℕ) (c : ℤ) (N : ℕ) (f : ℤ → ℂ) :
    0 ≤ D.famAvg l H c N f := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => ?_)
  rw [famNorm, boxNorm]
  exact Real.rpow_nonneg (norm_nonneg _) _

end IdxDatum

/-! ## The embedded configuration -/

/-- The multilinear average over the full polynomial progression
`(x, x + y, x + y², …, x + y^{d-1}, x + P(y))` with `d = P.natDegree`:
`(NM)⁻¹ Σ_x F_0(x) Σ_{y ∈ [M]} (∏_{i<d-1} F_{i+1}(x + y^{i+1})) · F_d(x + P(y))`. -/
def LambdaMD (N M : ℕ) (P : Polynomial ℤ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) : ℂ :=
  ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F ⟨0, Nat.succ_pos _⟩ x *
    (∑ y ∈ Finset.Icc 1 M,
      (∏ i : Fin (P.natDegree - 1), F ⟨i.val + 1, by omega⟩ (x + (y : ℤ) ^ (i.val + 1))) *
      F ⟨P.natDegree, Nat.lt_succ_self _⟩ (x + P.eval (y : ℤ)))

/-! ## The two chapters of Peluse's §§4-6 -/

/-- **Chapter A — Peluse's Proposition 3.4** for the embeddable configuration.

There is a level datum `D` (the multiplicities `k_i ≪_d 1` of her §3) and an exponent `K` such that
a large multilinear average along `(x, x+y, x+y², …, x+y^{d-1}, x+P(y))` forces the average, over
the parameter box `((-⌊δ'M⌋,⌊δ'M⌋) ∩ ℤ)^{Σ_j |S_j|}`, of the level-`|I_{d-1}|` box-norm power of the
last function at the directions `p(a)[⌊δ'M⌋]`, `p ∈ A_{d-1}`, to be at least `(γ/A)^K`.

This is the paper's Proposition 3.4 with `ℓ = d`, `P_i = X^i` (`i < d`), `P_d = P`, `q = 1`: the
scale condition `1/C ≤ M^d/N ≤ C` is recorded as the two `A₀`-hypotheses *with `A₀` a parameter of
the chapter* (the paper's `C` is given data, so the conclusion's constant may depend on it — this is
what makes the chapter usable by a consumer whose scale imbalance is `A'`), the paper's
`δ' ≪_{C,d} δ^{O_d(1)}` as `A·δ' ≤ γ^K`, and the non-degeneracy of the parameter window as
`2 ≤ ⌊δ'M⌋` (without which the statement is false: at `⌊δ'M⌋ ≤ 1` the direction sets are
singletons, the family average is phase-blind, and it carries no arithmetic information).
-/
def Prop34 (P : Polynomial ℤ) : Prop :=
  ∃ D : IdxDatum, ∃ K : ℕ, 1 ≤ K ∧
    ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ A : ℝ, 1 ≤ A ∧
    ∀ (N M : ℕ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) (γ δ' : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M →
      (N : ℝ) ≤ A₀ * (M : ℝ) ^ P.natDegree →
      γ * (M : ℝ) ^ P.natDegree ≤ A₀ * (N : ℝ) →
      0 < γ → γ ≤ 1 → 0 < δ' → A * δ' ≤ γ ^ K →
      2 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, SupportIn (F i) N) →
      γ ≤ ‖LambdaMD N M P F‖ →
      (γ / A) ^ K ≤ D.famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N
        (F ⟨P.natDegree, Nat.lt_succ_self _⟩)

/-- **Chapter B — Peluse's Proposition 3.6** for the same configuration.

For the datum `D` produced by `Prop34`, a family average `η` (at the inner window `⌊δ'M⌋`) is
concatenated, by iterating her Lemma 5.7 (`d-1` rounds, one per level of the construction), into a
uniformity-norm power of a single function at the long scale `d!·lc P [⌊δ'M^d⌋]`.

The hypotheses are the paper's: the scale relation `M^d ≍ N` (`N ≤ A₀·M^d`, `M^d ≤ A₀·N`, with the
imbalance bound `A₀` a *parameter* of the chapter; *both* are needed, since the paper's
`M = (N/q^{ℓ-1})^{1/ℓ}` is not free), the smallness
`δ' ≪_{C,d} η^{O_d(1)}` (`A·δ' ≤ η^K`), the non-degeneracy `N ≫_{C,d} (q/ηδ')^{O_d(1)}`
(`A·(ηδ')^{-K} ≤ N`, with `q = 1`), and the window non-degeneracy `2 ≤ ⌊δ'M⌋` (without which the
statement is false, by the same phase-blindness as in `Prop34`).
-/
def Prop36 (P : Polynomial ℤ) : Prop :=
  ∀ D : IdxDatum, ∃ s : ℕ, 2 ≤ s ∧
    ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ A : ℝ, 1 ≤ A ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (N M : ℕ) (f : ℤ → ℂ) (η δ' : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M →
      (N : ℝ) ≤ A₀ * (M : ℝ) ^ P.natDegree →
      (M : ℝ) ^ P.natDegree ≤ A₀ * (N : ℝ) →
      0 < η → η ≤ 1 → 0 < δ' → A * δ' ≤ η ^ K →
      2 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
      A * (η * δ') ^ (-(K : ℤ)) ≤ (N : ℝ) →
      η ≤ D.famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N f →
      η ^ K ≤ A * uNormPow s
        (arithIcc (P.natDegree.factorial * P.leadingCoeff)
          (⌊δ' * (M : ℝ) ^ P.natDegree⌋).toNat) (symIcc N) f


/-- **Chapter B', Peluse's Proposition 3.6 proved from scratch** (no hypothesis).

`Prop36` above takes `Work.Peluse.PeluseConcatenation` as an unused-through-usual hypothesis; but
that statement is a *weakened* transcription of Peluse's Theorem 3.5 (its shifts are forced to be
multiples of the coefficient, and its witnesses are quantified after `∀ c`), and the proof of
Proposition 3.6 needs the theorem in its full form (Lemma 5.7 applies Theorem 3.5 with coefficient
`p_{i₀}(a)` and arbitrary absolute shifts).  This chapter is therefore the source's §5 *from
scratch*: Theorem 3.5's proof (Lemmas 5.1–5.6) together with Lemma 5.7 and the iteration, giving
Proposition 3.6 in the same shape as `Prop36`.

It is the honest form of the §5 obligation: it does not use, and does not need, any recorded
concatenation statement.
-/
def Prop36S (P : Polynomial ℤ) : Prop :=
  ∀ D : IdxDatum, ∃ s : ℕ, 2 ≤ s ∧
    ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ A : ℝ, 1 ≤ A ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (N M : ℕ) (f : ℤ → ℂ) (η δ' : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M →
      (N : ℝ) ≤ A₀ * (M : ℝ) ^ P.natDegree →
      (M : ℝ) ^ P.natDegree ≤ A₀ * (N : ℝ) →
      0 < η → η ≤ 1 → 0 < δ' → A * δ' ≤ η ^ K →
      2 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
      A * (η * δ') ^ (-(K : ℤ)) ≤ (N : ℝ) →
      η ≤ D.famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N f →
      η ^ K ≤ A * uNormPow s
        (arithIcc (P.natDegree.factorial * P.leadingCoeff)
          (⌊δ' * (M : ℝ) ^ P.natDegree⌋).toNat) (symIcc N) f

end

end Work.Peluse.UControl
