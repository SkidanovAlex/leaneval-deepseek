import Submission.Work.CancelPair
import Submission.Work.FactorAbsorption

open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# T1 — the general-`k` aggregate lemma (Nielsen's "Aggregat"-Lemma)

## Statement (machine-validated: exhaustive n=2, word length ≤ 3, k=2..5
1.6M instances + 16 562 random k ≤ 8, alphabets 2-3: 0 failures; k=2,3
PROVEN in Lean as `two_factor_peel` (NielsenPeel) and `factor_absorption_three`
(FactorAbsorption))

**Align-level form.**  For reduced words `L₁, …, Lₖ` (`k ≥ 2`) with reduced
concatenation of length ≤ 1,

    (∃ j < k, align Lⱼ Lⱼ₊₁ = Lⱼ.length) ∨
    (∃ j < k, align Lⱼ Lⱼ₊₁ = Lⱼ₊₁.length) ∨
    (∃ j, 2 ≤ j ∧ j ≤ k-1, align Lⱼ₋₁ Lⱼ + align Lⱼ Lⱼ₊₁ ≥ Lⱼ.length)

**Absorption-level form (group elements `e₁..eₖ`, product norm ≤ 1):**
some factor is fully absorbed by its ≤ 2 neighbours:

    (∃ j ≤ k-1, AbsorbedRight eⱼ eⱼ₊₁) ∨ (∃ 2 ≤ j, AbsorbedLeft eⱼ eⱼ₋₁) ∨
    (∃ 2 ≤ j ≤ k-1, MiddleAbsorbed eⱼ₋₁ eⱼ eⱼ₊₁)

(the alignment form transfers to the absorption form by
`absorbedRight_of_align_eq_left` / `absorbedLeft_of_align_eq_right` /
`middleAbsorbed_of_align_ge`, FactorAbsorption.lean).

## Proof roadmap through the `CancelPair.lean` pairing layer (CORRECTED)

Fix the concatenation `W = L₁ ++ ⋯ ++ Lₖ` (factor `j` occupies block
`[sⱼ, sⱼ₊₁)`, `s₁ = 0`, `sⱼ₊₁ = sⱼ + Lⱼ.length`).  `reduce W` has length
≤ 1, so by `survivorPos_length` at most **one** survivor position exists;
every other position lies in a cancelled pair (`position_covered` +
`survivor_not_pair`; `in_pair_iff_not_survivor`,
`segment_fully_cancelled_iff_no_survivor` in this file).  A factor is *fully
cancelled* when its block contains no survivor.

**WARNING — earlier Claims A/B are FALSE.**  The leftmost fully-cancelled
factor need NOT be absorbed by its ≤ 2 neighbours: `W = [a] ++ [b] ++
[b⁻¹ a⁻¹]` has pairs `(0,3), (1,2)` (verified by `#eval`), so factor 1's
letter (position 0) pairs with position 3 — two blocks away — jumping over
the fully-cancelled factor 2.  The jump is always a *nested* pair enclosing
fully-cancelled inner factors (`pairs_no_cross`,
`pair_not_in_reduced_factor` forbids partners inside one factor, so inner
fully-cancelled factors are consumed across block boundaries).

**Correct target (machine-validated: exhaustive n=2, word length ≤ 3,
k = 2..5 — 1 615 272 instances — 0 failures):** there is a **confined fully
cancelled factor**: a factor whose block has no survivor and whose every
letter-position is paired with a position of block `j-1` or `j+1` only.
(Then the confinement + order of the non-crossing pairing yields the
junction alignment conclusion: for the confined factor the partners in the
left block form a suffix and in the right block a prefix of the neighbours,
splitting the factor word — `prefix_suffix_split` — which gives
`align Lⱼ₋₁ Lⱼ = r₁`, `align Lⱼ Lⱼ₊₁ = r₂` with `r₁ + r₂ = Lⱼ.length`
(or a one-sided variant at the ends), the desired absorption.)

**Selection rule — RESOLVED and FORMALISED (`Submission/Work/Confine.lean`,
`theorem Submission.Nielsen.confined_factor_exists`, kernel-checked):** a
cancelled pair whose endpoints lie in blocks at distance ≥ 2 is a *jump*;
machine validation (1 301 284 letter instances with ≤ 1 survivor + all
non-crossing perfect matchings on ≤ 10 points) shows that a *minimal-length*
jump `(i,j)` with `i` in block `t` makes block `t+1` confined & fully
cancelled (every letter of `B_{t+1}` lies strictly inside `(i,j)` by
`pair_interval_complete`, has no survivor by `survivor_not_inside_pair`, and
pairs only with `B_t ∪ B_{t+2}` — a partner in `B_{t'}` (`t' ≥ t+3`) would
be a shorter jump); if no jump exists every block is confined and any block
avoiding the (≤ 1) survivor works.  The formal proof uses
`confined_after_jump`, `confined_no_jump`, `exists_minimal_jump`,
`exists_fully_cancelled` (all in `Submission.Nielsen`).

## Supporting lemmas to build (generic where possible, else in-module)

1. `segment_fully_cancelled_iff_no_survivor`: a contiguous block of `W` has
   every position cancelled iff it contains no survivor position (follows
   from `position_covered`, `survivor_not_pair`; needed to phrase "fully
   cancelled factor" via survivors).
2. Factor block positions & lengths: `sⱼ₊₁ = sⱼ + Lⱼ.length` with
   `W = L₁ ++ ⋯ ++ Lₖ`; position of factor `j`'s `t`-th letter in `W` is
   `sⱼ + t`; letters agree: `W[sⱼ + t]? = Lⱼ[t]?` (getElem over a
   multi-append; the k = 2 and induction cases via a Commons-grade
   `getElem?_append` lemma).
3. `confine_partners` — **DONE (`Confine.lean`)** as `confined_after_jump`
   (minimal-jump witness, with `partner_inside_pair` and `no_pair_inside_block`
   as the two engines) and `confined_no_jump`; the existence theorem
   `confined_factor_exists` is PROVEN.
4. `junction_mirror` + `align_ge_crossCount` — **DONE
   (`Submission/Work/ConfineTransfer.lean`)**: for ANY two adjacent reduced
   blocks, the cross pairs at their junction are exactly the mirror pairs
   `(e-1-s, e+s)` for `s < crossCount Fs t` (`junction_mirror`), and hence
   `align L_t L_{t+1} ≥ crossCount Fs t` (`align_ge_crossCount`).  Remaining:
   the confined-factor count identity — for a *confined* `B_j`, every letter
   pairs into `B_{j-1} ∪ B_{j+1}`, giving `|L_j| = crossCount (j-1) +
   crossCount j` (interior; one-sided at the ends); then `t1_align_general`
   (the align-level disjunction of T1) assembles from
   `confined_factor_exists` + `align_ge_crossCount`.
5. `align_of_confined_suffix` — **SUPERSEDED / DONE at a stronger level**: the
   reverse mirror `junction_mirror_rev` + the confined counts + the alignment
   bounds give the align-level disjunction **`t1_align_general`**
   (`ConfineT1.lean`), and **`t1_absorb_general`** (`T1Absorb.lean`) is the
   absorption-level general-`k` aggregate (via
   `reduce_flatten_toWord_prod` + the `FactorAbsorption` transfers).  T1 for
   arbitrary `k` is PROVEN; next on the aggregate route: T2/T3
   (balanced-phase analysis + rebalancing/termination).

**`in_pair_iff_not_survivor` and `segment_fully_cancelled_iff_no_survivor`
— DONE (this file):** a position of `W` occurs in a cancelled pair iff it is
not a survivor (`position_covered` against `survivor_not_pair`), and a
segment `[a, b]` has every position cancelled iff it contains no survivor.

**Confined-factor existence — DONE (`Submission/Work/Confine.lean`):** the
general-`k` selection rule described above, kernel-checked (`theorem
Submission.Nielsen.confined_factor_exists`, axioms `[propext,
Classical.choice, Quot.sound]`).

**Block bookkeeping — DONE (this file, module `Submission.Nielsen`):**
`getElem_append_if` (two-list positional lookup: before the first block reads
the first list, afterwards the second), `block_getElem_right` (a letter of
block `f` at in-block index `t` sits at global position `|P| + t` of
`P ++ (f ++ B)`), `block2_getElem_right` (third block at `|P| + |f| + t`).
The same two-list fact is now also in the shared commons as
`Commons.Data.List.List.getElem_append` (import
`Submission.Commons.Data.List.List.getElem_append`).

The roadmap file keeps no statements with `sorry`; each lemma is added as it
is proved.  All lemmas kernel-checked, axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- Positional lookup over an append: before the first block it reads the
first list, afterwards the second. -/
lemma getElem_append_if {α : Type*} (X Y : List α) (n : ℕ) :
    (X ++ Y)[n]? = if h : n < X.length then X[n]? else Y[n - X.length]? := by
  induction X generalizing n with
  | nil =>
      have hn : n - 0 = n := by simp
      simp [hn]
  | cons a rest ih =>
      cases n with
      | zero => simp
      | succ n' =>
          have hstep : ((a :: rest) ++ Y)[n' + 1]? = (rest ++ Y)[n']? := by
            induction n' with
            | zero => rfl
            | succ m ihm => simpa using ihm
          rw [hstep]
          have ih' := ih n'
          rw [ih']
          by_cases hn' : n' < rest.length
          · have hn'' : n' + 1 < (a :: rest).length := by simp [hn']
            have hsub : n' + 1 - (a :: rest).length = n' - rest.length := by
              simp [hn'']
            simp [hn', hn'']
          · have hn'' : ¬ n' + 1 < (a :: rest).length := by simp [hn']
            have hsub : n' + 1 - (a :: rest).length = n' - rest.length := by
              have h1 : (a :: rest).length = rest.length + 1 := by simp
              omega
            simp [hn', hn'', hsub]

/-- A letter of the block `f` at in-block index `t` sits at global position
`|P| + t` of `P ++ (f ++ B)`. -/
lemma block_getElem_right {α : Type*} (P f B : List α) {t : ℕ}
    (ht : t < f.length) :
    (P ++ (f ++ B))[P.length + t]? = f[t]? := by
  have h1 := getElem_append_if P (f ++ B) (P.length + t)
  rw [h1]
  have hnot : ¬ P.length + t < P.length := by omega
  simp [hnot]
  have h2 := getElem_append_if f B t
  rw [h2]
  simp [ht]

/-- A letter of the third block `g` at in-block index `t` sits at global
position `|P| + |f| + t` of `P ++ (f ++ (g ++ B))`. -/
lemma block2_getElem_right {α : Type*} (P f g B : List α) {t : ℕ}
    (ht : t < g.length) :
    (P ++ (f ++ (g ++ B)))[P.length + f.length + t]? = g[t]? := by
  have h1 := getElem_append_if P (f ++ (g ++ B)) (P.length + f.length + t)
  rw [h1]
  have hnot : ¬ P.length + f.length + t < P.length := by omega
  simp [hnot]
  have hsub1 : P.length + f.length + t - P.length = f.length + t := by omega
  rw [hsub1]
  have h2 := getElem_append_if f (g ++ B) (f.length + t)
  rw [h2]
  have hnot2 : ¬ f.length + t < f.length := by omega
  simp [hnot2]
  have h3 := getElem_append_if g B t
  rw [h3]
  simp [ht]


/-! ## A position is cancelled iff it is not a survivor -/

/-- A position of `W` occurs in a cancelled pair iff it is not a survivor
(coverage `position_covered` against `survivor_not_pair`). -/
lemma in_pair_iff_not_survivor {α : Type*} [DecidableEq α] (W : List (α × Bool))
    {x : ℕ} (hx : x < W.length) :
    (∃ y : ℕ, (x, y) ∈ cancelledPairs W ∨ (y, x) ∈ cancelledPairs W) ↔
      x ∉ survivorPos W := by
  constructor
  · intro hp hsur
    rcases hp with ⟨y, hy⟩
    rcases hy with hy | hy
    · have hnp := survivor_not_pair W hy hsur
      exact (hnp.1 rfl)
    · have hnp := survivor_not_pair W hy hsur
      exact (hnp.2 rfl)
  · intro hns
    have hcov := position_covered W x hx
    rcases hcov with hsur | hpair
    · exact False.elim (hns hsur)
    · rcases hpair with hpair | hpair
      · rcases hpair with ⟨j, hj⟩
        refine ⟨j, ?_⟩
        left
        exact hj
      · rcases hpair with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        right
        exact hi

/-- A segment `[a, b]` of `W` has every position cancelled iff it contains no
survivor position. -/
lemma segment_fully_cancelled_iff_no_survivor {α : Type*} [DecidableEq α]
    (W : List (α × Bool)) {a b : ℕ} (hab : a ≤ b) (hb : b < W.length) :
    (∀ x : ℕ, a ≤ x → x ≤ b → ¬ x ∈ survivorPos W) ↔
      (∀ x : ℕ, a ≤ x → x ≤ b →
        ∃ y : ℕ, (x, y) ∈ cancelledPairs W ∨ (y, x) ∈ cancelledPairs W) := by
  constructor
  · intro hns x hxa hxb
    have hxW : x < W.length := by omega
    exact (in_pair_iff_not_survivor W hxW).mpr (hns x hxa hxb)
  · intro hcov x hxa hxb
    have hxW : x < W.length := by omega
    exact (in_pair_iff_not_survivor W hxW).mp (hcov x hxa hxb)

end Submission.Nielsen
