import Submission.EFL.Counting
import Submission.Commons.Data.Finset.sum_card_filter_comm
import Submission.EFL.GreedyListColouring
import Submission.EFL.NeighbourSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The reordering lemma (§6.2 of the paper)

**Lemma (reordering-lemma).**  Let `0 < 1/r₁ ≪ τ, 1/K` where `τ < 1`,
`K ≥ 1`, and `1 − τ − 7τ^{1/4}/K > 0`.  If `𝓗` is an `n`-vertex linear
hypergraph where every `e ∈ 𝓗` satisfies `|e| ≥ r₁`, then there exists a
linear ordering `ord` of the edges of `𝓗` such that at least one of the
following holds:

* **(good)** every `e ∈ 𝓗` satisfies `fwddeg(e) ≤ (1−τ)n`
  (`GoodOrdering`); or
* **(volume)** there is a set `W ⊆ 𝓗` (`W` = the edges of rank `≤` the
  rank of some `e*`, with `|e| ≤ (1+3τ^{1/4}K⁴)·|e*|`) such that
  `vol(W) ≥ (1−τ−7τ^{1/4}/K)²/(1+3τ^{1/4}K⁴)` (`W1`, `W2`), and moreover,
  for `e*` the last edge of `W`:
  (`O1`) every `f` with `e* ⪯ f`, `f ≠ e*` satisfies `fwddeg(f) ≤ (1−τ)n`;
  (`O2`) `f ⪯ e ⪯ e*` implies `|f| ≥ |e|` (edge sizes are non-increasing
  towards `e*`).

## Proof architecture (paper §6.2; each block to be filled in later
sessions, statements and vocabulary pinned here)

**BLOCK I — the minimal ordering (PROVED below).**  The paper considers
an ordering `ord` that minimises `e(H^{⪯e*})` among pairs `(ord, e*)`
satisfying (O1)+(O2).  Formally this is the backward walk `blockI` over a
fixed ordering: from any admissible pair (in particular from `lastEdge` of
the size-non-increasing order `sizeOrder`, constructed below), move `e*`
to its predecessor while its forward degree is ≤ `(1−τ)n`; the walk
terminates in `GoodOrdering` or in an admissible edge with
`(1−τ)n < fwddeg(e)`.  The initial admissible pair is supplied by the
size-decreasing ordering (`sizeOrder`, `sizeOrder_admissible_last`,
`sizeOrder_blockI`).

**BLOCK II — the good case (PROVED below).**  When the forward-degree walk
reaches the first edge, `fwddeg(e*) = 0 ≤ (1−τ)n` and (O1) gives
`fwddeg(f) ≤ (1−τ)n` for every other `f`, so (good) holds
(`fwddeg_zero_of_first`, `good_of_first_admissible`, the left branch of
`blockI`).

**BLOCK III — the volume case setup (PROVED below).**  Otherwise the walk
stops at an admissible edge `eStar` with `(1−τ)n < fwddeg(eStar)`.  The
volume set is `W := VolumeSet τ K ord eStar = {f ⪯ eStar :
(edgeSize f : ℝ) ≤ (1+3τ^{1/4}K⁴)·|eStar|}`; `eStar ∈ W`
(`volumeSet_mem_self`), every `f ∈ W` has `edgeSize f ≥ edgeSize eStar`
by (O2) (`volumeSet_ge_self`), and (W1) `WMaxSize` holds
(`volumeSet_maxSize`).

**BLOCK IV — neighbours ahead of `e*` are many (PROVED below).**
For every preceding neighbour `e` of `e*` the paper shows
`|N(e) ∩ H^{⪯e*}| > (1−τ)n` (`BlockIVStatement`, eq. (6.3)); or else the
**block rotation** of the segment `[a..b]` of ranks (`rotateEquiv`, with
rank facts `a ↦ b`, `(a,b]` shifted down, the rest fixed) makes `e` the
successor of `e*` while preserving (O1) (`blockIV_O1`) and (O2)
(`blockIV_O2`) and shrinking the prefix of `e*` by exactly one
(`blockIV_prefix`, `blockIV_prefix_card`) — contradicting the minimality
of `e(H^{⪯e*})` recorded in `blockIV_of_minimal`.  The rotation's exact
effect on the forward degree of `e` (`rotate_fwdnbr_eq_nbrsInPrefix`:
`fwddeg'(e) = |N(e)∩H^{⪯e*}|`, no `+1`) and the preservation of forward
degrees of edges beyond `e*` (`rotate_fwdnbr_of_rank_gt_b`) are proved
too.  The global minimal pair exists (`exists_minimal_admissible`,
`exists_minimal_admissible_of_fintype`), and `minimal_admissible_dichotomy`
packages the outcome: the minimal ordering is good, or `e*` has rank `≥ 1`,
forward degree `> (1−τ)n`, and `BlockIVStatement`.

**BLOCK V — size-truncated neighbourhoods (`X` and the two applications
of Prop `fwdnbr`-far-bound) (PROVED below).**  Let
`X := {e ∈ fwdnbr(e*) : |e| ≤ (1+K√τ)r}`.  Applying Prop `fwdnbr`
inequality (ii) (`fwdnbr_inequality2`) with `e*`, `F₁ := fwdnbr(e*)∖X`
(edges of size `≥ (1+K√τ)r`) and `F₂ := X` (edges of size in
`[r, (1+K√τ)r)`, the lower bound `|f| ≥ r ≥ r/(1+0)` from (O2))
gives `|fwdnbr(e*)∖X| ≤ (τ + 2/r)·n/(K√τ)` (`blockV_boundNminusX`);
combining with `nbrs-ahead` gives `|X| ≥ (1−τ−2√τ/K)n`
(`blockV_X_bound`, eq. (6.4)).  For each `e ∈ X`, a second
application of `fwdnbr_inequality2` to `e` with `F₁ := {f ∈ N(e)∩H^{⪯e*} :
|f| ≥ (1+K³τ^{1/4})|e|}` and `F₂` the complementary neighbours bounds
`|(N(e)∩H^{⪯e*})∖W| ≤ 6τ^{1/4}n/K` (`blockV_app2`, eq. (6.5)), using
(O2)'s lower bound `|f| ≥ r` for `f ∈ H^{⪯e*}` and the size-factor
comparison `(1+K³τ^{1/4})(1+K√τ) ≤ 1+3τ^{1/4}K⁴`
(`sizeFactor_ge_product`) to see that `N(e)∩H^{⪯e*}∖W` lies in `F₁`
(`outsideVolumeSet_subset_big`).

**BLOCK VI — volume lower bound (`W2`) (PROVED below).**  With
`q := 1−τ−7τ^{1/4}/K` and `A := 1+3τ^{1/4}K⁴`, the paper shows
`|B| ≥ |X|·(q n/(A r²) − (1+K√τ)/A − 1/(A r²))` (summing eq. (6.6)
over `e ∈ X` and eq. (6.8) over `f ∈ B`, via the double count
`∑_{e∈X}|N(e)∩B| = ∑_{f∈B}|N(f)∩X|` — `B := W∖(N(e*)∪{e*})`) and
`|W| ≥ |B| + |X| ≥ (1−τ−2√τ/K)·q·n²/(A r²)`; since every `e ∈ W` has
`|e| ≥ r` (O2), each contributes volume at least `r(r−1)/(n(n−1))`,
giving `vol(W) ≥ q²/A = volBound` (`blockVI_WVolume`).

**LEMMA 6.2 (the reordering lemma) IS PROVED** as `reorderingLemma`
(`ReorderingInstance`), assembled from the minimal admissible pair +
`minimal_admissible_dichotomy` and the whole Block III–VI stack, with the
size margins `ReorderingMargins r₁ τ K` (the explicit
`0 < 1/r₁ ≪ τ, 1/K`) transferred to the edge sizes (`rm_…_of_le`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 0

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Normalised volume of a subfamily of edges -/

/-- The normalised volume of a finite subfamily `S ⊆ 𝓗` of a hypergraph on
`n` vertices: `vol(S) = (∑_{e∈S} |e|(|e|−1)) / (n(n−1))`, matching the
paper's `vol_H(W) = ∑_{e∈W} C(|e|,2)/C(n,2)`. -/
def Hypergraph.volume (𝓗 : Hypergraph (Fin n)) (S : Finset 𝓗) : ℝ :=
  ((S.sum (fun e : 𝓗 => (edgeSize (e : Set (Fin n)) : ℝ) *
      ((edgeSize (e : Set (Fin n)) : ℝ) - 1)))) /
    ((n : ℝ) * ((n - 1 : ℕ) : ℝ))

/-- Each summand `|e|(|e|−1)` of the volume numerator is non-negative. -/
lemma volume_term_nonneg (e : Set (Fin n)) :
    (0 : ℝ) ≤ (edgeSize e : ℝ) * ((edgeSize e : ℝ) - 1) := by
  by_cases h0 : edgeSize e = 0
  · rw [h0]
    norm_num
  · have hge : (1 : ℝ) ≤ (edgeSize e : ℝ) := by exact_mod_cast (by omega : 1 ≤ edgeSize e)
    have hnon : (0 : ℝ) ≤ (edgeSize e : ℝ) - 1 := by nlinarith
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le _)) hnon

/-- The numerator of the volume is non-negative. -/
lemma volume_num_nonneg (𝓗 : Hypergraph (Fin n)) (S : Finset 𝓗) :
    (0 : ℝ) ≤ S.sum (fun e : 𝓗 => (edgeSize (e : Set (Fin n)) : ℝ) *
      ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) := by
  exact Finset.sum_nonneg (fun e _he => volume_term_nonneg (e : Set (Fin n)))

/-- The volume of a subfamily is non-negative. -/
lemma volume_nonneg {𝓗 : Hypergraph (Fin n)} (S : Finset 𝓗) :
    (0 : ℝ) ≤ Hypergraph.volume 𝓗 S := by
  classical
  unfold Hypergraph.volume
  apply div_nonneg
  · exact volume_num_nonneg 𝓗 S
  · positivity

/-- Volume is monotone in the subfamily. -/
lemma volume_mono {𝓗 : Hypergraph (Fin n)} {S₁ S₂ : Finset 𝓗} (h : S₁ ⊆ S₂) :
    Hypergraph.volume 𝓗 S₁ ≤ Hypergraph.volume 𝓗 S₂ := by
  classical
  unfold Hypergraph.volume
  have hle : S₁.sum (fun e : 𝓗 => (edgeSize (e : Set (Fin n)) : ℝ) *
      ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) ≤
      S₂.sum (fun e : 𝓗 => (edgeSize (e : Set (Fin n)) : ℝ) *
      ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg h (fun e _he₂ _he₁ => volume_term_nonneg (e : Set (Fin n)))
  exact div_le_div_of_nonneg_right hle (by positivity)

/-- Each real volume term equals the cast of the natural pair count:
`|e|(|e|−1) = ↑(|e|·(|e|−1))`. -/
lemma volume_term_eq_cast (e : Set (Fin n)) :
    (edgeSize e : ℝ) * ((edgeSize e : ℝ) - 1) = ((edgeSize e * (edgeSize e - 1) : ℕ) : ℝ) := by
  by_cases h0 : edgeSize e = 0
  · rw [h0]
    norm_num
  · have hge : 1 ≤ edgeSize e := by omega
    rw [Nat.cast_mul]
    rw [Nat.cast_sub hge]
    norm_num

/-- The numerator of the volume is the cast of the natural pair count. -/
lemma volume_num_eq_cast (𝓗 : Hypergraph (Fin n)) (S : Finset 𝓗) :
    S.sum (fun e : 𝓗 => (edgeSize (e : Set (Fin n)) : ℝ) *
      ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) =
    ((S.sum (fun e : 𝓗 => edgeSize (e : Set (Fin n)) * (edgeSize (e : Set (Fin n)) - 1)) : ℕ) : ℝ) := by
  classical
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro e _he
  exact volume_term_eq_cast (e : Set (Fin n))

/-- The volume of any subfamily of a *linear* hypergraph is at most `1`
(`vol_H(W) ≤ 1`, paper §3). -/
lemma volume_le_one {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (S : Finset 𝓗) :
    Hypergraph.volume 𝓗 S ≤ 1 := by
  classical
  unfold Hypergraph.volume
  -- the natural pair count of the family is at most n(n−1) (linearity)
  have hnat : S.sum (fun e : 𝓗 => edgeSize (e : Set (Fin n)) * (edgeSize (e : Set (Fin n)) - 1)) ≤
      n * (n - 1) := by
    let sv : Finset (Set (Fin n)) := S.image (fun e : 𝓗 => (e : Set (Fin n)))
    have hcard : sv.sum (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) =
        S.sum (fun e : 𝓗 => edgeSize (e : Set (Fin n)) * (edgeSize (e : Set (Fin n)) - 1)) := by
      have hinj : Set.InjOn (fun e : 𝓗 => (e : Set (Fin n))) (S : Set 𝓗) := by
        intro e₁ _he₁ e₂ _he₂ hEq
        apply Subtype.ext
        exact hEq
      have hc := Finset.sum_image (s := S) (g := fun e : 𝓗 => (e : Set (Fin n)))
        (f := fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) hinj
      dsimp [sv]
      exact hc
    have hsub : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ sv → e₂ ∈ sv → e₁ ≠ e₂ →
        (e₁ ∩ e₂ : Set (Fin n)).Subsingleton := by
      intro e₁ e₂ he₁ he₂ hne
      rcases (Finset.mem_image.mp he₁) with ⟨x₁, _hx₁, rfl⟩
      rcases (Finset.mem_image.mp he₂) with ⟨x₂, _hx₂, rfl⟩
      exact hlin x₁.2 x₂.2 (by
        intro hEq
        exact hne hEq)
    have hnat' : sv.sum (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) ≤ n * (n - 1) :=
      sum_edgeSize_mul_sub_le_on sv hsub
    rwa [← hcard]
  have hden : ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) = ((n * (n - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
  by_cases h2 : 2 ≤ n
  · have hdenpos : 0 < ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
      rw [hden]
      have hposN : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
      exact_mod_cast hposN
    apply (div_le_one hdenpos).2
    have hnumle : S.sum (fun e : 𝓗 => (edgeSize (e : Set (Fin n)) : ℝ) *
        ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
      rw [volume_num_eq_cast]
      exact (Nat.cast_le.mpr hnat)
    rwa [hden]
  · -- n ≤ 1: the denominator is 0 and the numerator is 0
    have hn : n ≤ 1 := by omega
    have hn0 : (n * (n - 1) : ℕ) = 0 := by
      interval_cases n <;> simp
    have hnat0 : S.sum (fun e : 𝓗 => edgeSize (e : Set (Fin n)) * (edgeSize (e : Set (Fin n)) - 1)) = 0 := by
      have : S.sum (fun e : 𝓗 => edgeSize (e : Set (Fin n)) * (edgeSize (e : Set (Fin n)) - 1)) ≤ 0 := by
        simpa [hn0] using hnat
      omega
    have hnum0 : S.sum (fun e : 𝓗 => (edgeSize (e : Set (Fin n)) : ℝ) *
        ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) = 0 := by
      rw [volume_num_eq_cast, hnat0]
      norm_num
    rw [hnum0]
    norm_num

/-! ## The reordering lemma: statement and vocabulary

The statement is phrased per-instance like the rest of the project: the
asymptotic hypothesis `0 < 1/r₁ ≪ τ, 1/K` is replaced by the concrete
conditions the proof uses (`2 ≤ r₁`, `0 < τ < 1`, `1 ≤ K`, and
positivity of the final volume bound).  An ordering is a rank
equivalence `ord : 𝓗 ≃ Fin k`. -/

/-- (good): every edge has forward degree at most `(1−τ)n`. -/
def GoodOrdering {n k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (ord : 𝓗 ≃ Fin k) : Prop :=
  ∀ e : 𝓗, (precedingDegree 𝓗 ord e : ℝ) ≤ (1 - τ) * (n : ℝ)

/-- (O1): edges after (and different from) `eStar` have small forward degree. -/
def OrderingGoodness {n k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) : Prop :=
  ∀ f : 𝓗, (ord eStar : ℕ) ≤ (ord f : ℕ) → f ≠ eStar →
    (precedingDegree 𝓗 ord f : ℝ) ≤ (1 - τ) * (n : ℝ)

/-- (O2): edge sizes do not decrease towards `eStar` (`f ⪯ e ⪯ eStar` implies
`|f| ≥ |e|`). -/
def OrderingBySize {n k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) : Prop :=
  ∀ ⦃e f : 𝓗⦄, (ord f : ℕ) ≤ (ord e : ℕ) → (ord e : ℕ) ≤ (ord eStar : ℕ) →
    (edgeSize (e : Set (Fin n)) : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ)

/-- The size-similarity factor `A := 1 + 3τ^{1/4}K⁴` and the volume-loss
factor `q := 1 − τ − 7τ^{1/4}/K` of the statement. -/
def tauQuarter (τ : ℝ) : ℝ := Real.sqrt (Real.sqrt τ)

def sizeFactor (τ : ℝ) (K : ℕ) : ℝ := 1 + 3 * tauQuarter τ * (K : ℝ) ^ 4

def volBound (τ : ℝ) (K : ℕ) : ℝ :=
  (1 - τ - 7 * tauQuarter τ / (K : ℝ)) ^ 2 / sizeFactor τ K

/-- (W1): all edges of `W` have sizes within the factor `A` of each other. -/
def WMaxSize {n : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ) (W : Finset 𝓗) : Prop :=
  ∀ ⦃e₁ e₂ : 𝓗⦄, e₁ ∈ W → e₂ ∈ W →
    (edgeSize (e₁ : Set (Fin n)) : ℝ) ≤ sizeFactor τ K * (edgeSize (e₂ : Set (Fin n)) : ℝ)

/-- (W2): `vol(W) ≥ q²/A`. -/
def WVolume {n : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ) (W : Finset 𝓗) : Prop :=
  volBound τ K ≤ Hypergraph.volume 𝓗 W

/-- A witness of the (volume) alternative: an edge `eStar` and a set `W` of
edges up to `eStar` (containing `eStar`), with `(W1)`, `(W2)`, `(O1)` and
`(O2)`.  Membership of `eStar` in `W` is what makes `|eStar|` the *minimum*
size in `W` (by `(O2)`) and hence turns `(W1)` into a bound on all sizes in
`W` relative to `|eStar|` — the form used by the downstream block
decomposition. -/
def VolumeWitness {n k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ) (ord : 𝓗 ≃ Fin k) : Prop :=
  ∃ eStar : 𝓗, ∃ W : Finset 𝓗,
    (∀ f ∈ W, (ord f : ℕ) ≤ (ord eStar : ℕ)) ∧
    WMaxSize τ K W ∧ WVolume τ K W ∧
    OrderingGoodness τ ord eStar ∧ OrderingBySize ord eStar ∧ eStar ∈ W

/-- The size margins of the reordering lemma: the concrete per-`r₁`
instances of the paper's hierarchy `0 < 1/r₁ ≪ τ, 1/K` (`r := (r₁ : ℝ)`).
They imply, for every edge `e` (with `(r₁ : ℝ) ≤ |e|`), the margins the
Block V/VI chain consumes at `r_e := |e|`:
`0 < q := 1−τ−7τ^{1/4}/K`, `1 ≤ τ(r−1)`, `K ≤ τ^{1/4}(r−1)`,
`1+K√τ ≤ r/2`, `2(1+K√τ) ≤ K²√τ·r`,
`(sizeFactor−1−K√τ)·r² ≥ 1`, and `u(1−1/r) ≥ q` with
`u := 1−τ−2√τ/K`. -/
def ReorderingMargins (r₁ : ℕ) (τ : ℝ) (K : ℕ) : Prop :=
  let r : ℝ := (r₁ : ℝ)
  (0 < 1 - τ - 7 * tauQuarter τ / (K : ℝ)) ∧
  (1 ≤ τ * (r - 1)) ∧
  ((K : ℝ) ≤ tauQuarter τ * (r - 1)) ∧
  (1 + (K : ℝ) * Real.sqrt τ ≤ r / 2) ∧
  (2 * (1 + (K : ℝ) * Real.sqrt τ) ≤ (K : ℝ) ^ 2 * Real.sqrt τ * r) ∧
  (1 ≤ (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (r ^ 2)) ∧
  ((1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 - 1 / r) ≥
    1 - τ - 7 * tauQuarter τ / (K : ℝ))

/-- **Reordering lemma (statement).**  For a linear hypergraph on `n`
vertices whose edges all have size at least `r₁`, with `2 ≤ n`,
`2 ≤ r₁`, `0 < τ < 1`, `1 ≤ K` and the size margins `ReorderingMargins`
(the explicit form of `0 < 1/r₁ ≪ τ, 1/K`, which in particular implies
`0 < q := 1−τ−7τ^{1/4}/K` and the positivity of `volBound = q²/sizeFactor`),
there is an ordering `ord` which is either *good* (`GoodOrdering`) or
admits a *volume witness* (`VolumeWitness`). -/
def ReorderingInstance (n r₁ : ℕ) (τ : ℝ) (K : ℕ) (𝓗 : Hypergraph (Fin n)) : Prop :=
  ((2 ≤ n) ∧ (2 ≤ r₁) ∧ (0 < τ) ∧ (τ < 1) ∧ (1 ≤ K) ∧
    ReorderingMargins r₁ τ K) →
    𝓗.IsLinear →
    (∀ e ∈ 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ)) →
    ∃ k : ℕ, ∃ ord : 𝓗 ≃ Fin k,
      GoodOrdering τ ord ∨ VolumeWitness τ K ord

/-! ## Block I (proved): the minimal forward-degree walk

**Block I** (paper §6.2, first two paragraphs of the proof of the reordering
lemma) is proved below.  The paper chooses, among all pairs
`(ord, e*)` satisfying (O1)+(O2), one minimising `e(H^{⪯e*})`; formally this
is a backward walk over a *fixed* ordering: starting from any admissible
pair `(ord, eStart)` (in particular the last edge of an ordering whose
sizes are non-increasing), while the forward degree of the current edge
`e` is at most `(1−τ)n` and it is not the first edge, move `e` to its
*predecessor* (`predEdge`), which is again admissible (`O1_of_pred`,
`O2_of_pred`).  The walk either reaches the first edge — then every edge
has forward degree at most `(1−τ)n` (`fwddeg_zero_of_first`,
`good_of_first_admissible`), the (good) alternative — or stops at an
admissible edge `e` with `(1−τ)n < fwddeg(e)` and `1 ≤ (ord e : ℕ)`, the
setup of the (volume) alternative.  `blockI` packages the walk as a
disjunction.  (A concrete initial admissible pair is supplied later by an
ordering by non-increasing edge sizes, whose existence uses the
`newRank`-style rank machinery of `GreedyListColouring.lean`.) -/


/-- the edge directly before eStar in the ordering (its predecessor) -/
def predEdge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k) (eStar : 𝓗)
    (h : 1 ≤ (ord eStar : ℕ)) : 𝓗 :=
  ord.symm ⟨(ord eStar : ℕ) - 1, by
    have hlt : (ord eStar : ℕ) < k := (ord eStar).isLt
    omega⟩

/-- rank of the predecessor -/
lemma rank_predEdge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (h : 1 ≤ (ord eStar : ℕ)) :
    (ord (predEdge ord eStar h) : ℕ) = (ord eStar : ℕ) - 1 := by
  simp [predEdge]

/-- the first edge of an ordering has forward degree 0 -/
lemma fwddeg_zero_of_first {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (e : 𝓗) (hfirst : (ord e : ℕ) = 0) : precedingDegree 𝓗 ord e = 0 := by
  classical
  have hs : precedingNeighbours 𝓗 ord e = ∅ := by
    ext f
    constructor
    · intro hf
      have hf' := (mem_precedingNeighbours 𝓗 ord e f).mp hf
      have hleN : (ord f : ℕ) ≤ (ord e : ℕ) := by simpa using hf'.2.1
      have hrank : (ord f : ℕ) = 0 := by omega
      have hEq : ord f = ord e := by
        apply Fin.ext
        omega
      exact False.elim (hf'.1 (ord.injective hEq))
    · intro hf
      simp at hf
  rw [precedingDegree, hs]
  simp

/-- the first edge has forward degree at most (1−τ)n when τ < 1 -/
lemma fwddeg_first_le {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (e : 𝓗) (hfirst : (ord e : ℕ) = 0) (hτ : τ < 1) :
    (precedingDegree 𝓗 ord e : ℝ) ≤ (1 - τ) * (n : ℝ) := by
  have h : precedingDegree 𝓗 ord e = 0 := fwddeg_zero_of_first ord e hfirst
  rw [h]
  have hpos : (0 : ℝ) ≤ 1 - τ := by linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  simpa using (mul_nonneg hpos hn)

/-- admissible pair predicate (O1 ∧ O2) -/
def AdmissiblePair {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) : Prop :=
  OrderingGoodness τ ord eStar ∧ OrderingBySize ord eStar

/-- an admissible first edge makes the whole ordering good -/
lemma good_of_first_admissible {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (e : 𝓗) (hfirst : (ord e : ℕ) = 0)
    (hadm : AdmissiblePair τ ord e) (hτ : τ < 1) : GoodOrdering τ ord := by
  classical
  intro x
  by_cases hx : x = e
  · subst x
    exact fwddeg_first_le ord τ e hfirst hτ
  · have hge : (ord e : ℕ) ≤ (ord x : ℕ) := by
      have hle0 : (ord x : ℕ) ≥ 0 := Nat.zero_le _
      -- need (ord e) ≤ (ord x): hfirst: = 0: omega
      omega
    exact hadm.1 x hge hx

/-- (O2) descends to the predecessor (the prefix up to the predecessor is
contained in the prefix up to eStar) -/
lemma O2_of_pred {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (h : 1 ≤ (ord eStar : ℕ))
    (hO2 : OrderingBySize ord eStar) : OrderingBySize ord (predEdge ord eStar h) := by
  classical
  intro e f hfe hep
  -- hep : (ord e) ≤ (ord (predEdge ord eStar h)); need ≤ (ord eStar): 
  have hpe : (ord (predEdge ord eStar h) : ℕ) = (ord eStar : ℕ) - 1 := rank_predEdge ord eStar h
  have hee : (ord e : ℕ) ≤ (ord eStar : ℕ) := by
    rw [hpe] at hep
    omega
  have hfe' : (ord f : ℕ) ≤ (ord e : ℕ) := by simpa using hfe
  -- O2(eStar) needs: ord f ≤ ord e ≤ ord eStar (Fin-level)
  exact hO2 (by simpa using hfe') (by simpa using hee)

/-- (O1) descends to the predecessor when the forward degree of eStar is
already small -/
lemma O1_of_pred {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (eStar : 𝓗) (h : 1 ≤ (ord eStar : ℕ))
    (hO1 : OrderingGoodness τ ord eStar)
    (hsmall : (precedingDegree 𝓗 ord eStar : ℝ) ≤ (1 - τ) * (n : ℝ)) :
    OrderingGoodness τ ord (predEdge ord eStar h) := by
  classical
  intro f hpf hne
  -- hpf : (ord (predEdge)) ≤ (ord f); hne : f ≠ predEdge
  have hpe : (ord (predEdge ord eStar h) : ℕ) = (ord eStar : ℕ) - 1 := rank_predEdge ord eStar h
  have hpfN : (ord (predEdge ord eStar h) : ℕ) ≤ (ord f : ℕ) := by simpa using hpf
  rw [hpe] at hpfN
  by_cases hfe : f = eStar
  · subst f
    exact hsmall
  · have hef : (ord eStar : ℕ) ≤ (ord f : ℕ) := by
      -- rank f ≥ rank eStar − 1 and f ≠ pred → rank f ≥ rank eStar
      have hneRank : (ord f : ℕ) ≠ (ord eStar : ℕ) - 1 := by
        intro heq
        apply hne
        have hv : (ord f : ℕ) = (ord (predEdge ord eStar h) : ℕ) := by
          rw [hpe]
          exact heq
        exact ord.injective (Fin.ext hv)
      omega
    exact hO1 f (by simpa using hef) hfe

/-- **Block I**: given an admissible pair (ord, eStar) in an ordering that
is admissible at eStar (in particular any ordering whose sizes are
non-increasing up to its end), either every edge is good, or some edge
`e` at rank ≥ 1 is admissible with forward degree `> (1−τ)n`. -/
theorem blockI {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (eStart : 𝓗) (hadm : AdmissiblePair τ ord eStart) (hτ : τ < 1) :
    GoodOrdering τ ord ∨
      ∃ e : 𝓗, AdmissiblePair τ ord e ∧ 1 ≤ (ord e : ℕ) ∧
        (1 - τ) * (n : ℝ) < (precedingDegree 𝓗 ord e : ℝ) := by
  classical
  -- descend along predecessors from eStart while the forward degree is small
  let P : ℕ → Prop := fun m =>
    ∀ e : 𝓗, (ord e : ℕ) = m → AdmissiblePair τ ord e →
      GoodOrdering τ ord ∨
        ∃ e' : 𝓗, AdmissiblePair τ ord e' ∧ 1 ≤ (ord e' : ℕ) ∧
          (1 - τ) * (n : ℝ) < (precedingDegree 𝓗 ord e' : ℝ)
  have hP : ∀ m : ℕ, P m := by
    intro m
    induction m with
    | zero =>
      intro e he hadm
      left
      exact good_of_first_admissible ord τ e he hadm hτ
    | succ m ih =>
      intro e he hadm
      by_cases hsmall : (precedingDegree 𝓗 ord e : ℝ) ≤ (1 - τ) * (n : ℝ)
      · -- move to the predecessor, which is admissible by O1_of_pred/O2_of_pred
        have hge1 : 1 ≤ (ord e : ℕ) := by
          rw [he]
          omega
        have hO1p : OrderingGoodness τ ord (predEdge ord e hge1) :=
          O1_of_pred ord τ e hge1 hadm.1 hsmall
        have hO2p : OrderingBySize ord (predEdge ord e hge1) :=
          O2_of_pred ord e hge1 hadm.2
        have hAdmP : AdmissiblePair τ ord (predEdge ord e hge1) := ⟨hO1p, hO2p⟩
        have hrp : (ord (predEdge ord e hge1) : ℕ) = m := by
          rw [rank_predEdge ord e hge1, he]
          omega
        exact ih (predEdge ord e hge1) hrp hAdmP
      · -- fwddeg(e) > (1−τ)n: the volume branch
        right
        refine ⟨e, hadm, ?_, ?_⟩
        · rw [he]
          omega
        · exact lt_of_not_ge hsmall
  exact hP (ord eStart : ℕ) eStart rfl hadm

/-! ## The initial admissible pair (proved): the size-non-increasing order

To *start* the Block I walk one needs an admissible pair `(ord, eStar)`.
The paper supplies it: "any ordering where `f ⪯ e` whenever `|f| > |e|`"
— an ordering by *non-increasing edge size* — is admissible at its last
edge (`(O1)` is vacuous there, `(O2)` is the defining property).  This
section constructs that ordering concretely.  Given any base ordering
`ord₀ : 𝓗 ≃ Fin (card 𝓗)` (from the `Fintype`), define the strict
precedence `SizeLess ord₀ e f` ("`e` before `f`"): `|e| > |f|`, or equal
sizes and `ord₀ e < ord₀ f` — a strict total order (`sizeLess_irrefl`,
`sizeLess_trans`, `sizeLess_total`).  The *rank* of `e` is the number of
predecessors (`sizeRankVal`, `sizeRank`); ranks fit in `Fin (card 𝓗)`
(`sizeRankVal_lt_card`), are strictly increasing along the order
(`sizeRank_mono`) and injective (`sizeRank_injective`), hence bijective —
`sizeOrder ord₀` is the required ordering, and `sizeOrder_ge_size` is its
defining (O2) property.  `lastEdge` (rank `card − 1`) is admissible
(`sizeOrder_admissible_last`: `O1_last` vacuously, `O2_sizeOrder_last`),
so `sizeOrder_blockI` instantiates `blockI` on this ordering — the bridge
from Block I to Blocks II/III. -/


/-- strict "precedes by size": e ≺ f iff |e| > |f|, or equal sizes with the
base rank of e below that of f (a total strict order refining non-increasing
size) -/
def SizeLess {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord₀ : 𝓗 ≃ Fin k) (e f : 𝓗) : Prop :=
  edgeSize (f : Set (Fin n)) < edgeSize (e : Set (Fin n)) ∨
    (edgeSize (e : Set (Fin n)) = edgeSize (f : Set (Fin n)) ∧ ord₀ e < ord₀ f)

lemma sizeLess_irrefl {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord₀ : 𝓗 ≃ Fin k)
    (e : 𝓗) : ¬ SizeLess ord₀ e e := by
  intro h
  rcases h with hgt | ⟨hEq, hlt⟩
  · exact (Nat.lt_irrefl _) hgt
  · exact (lt_irrefl _) hlt

lemma sizeLess_trans {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord₀ : 𝓗 ≃ Fin k)
    {e f g : 𝓗} (hef : SizeLess ord₀ e f) (hfg : SizeLess ord₀ f g) : SizeLess ord₀ e g := by
  rcases hef with hef1 | ⟨heq1, hlt1⟩
  · rcases hfg with hfg1 | ⟨heq2, hlt2⟩
    · left
      omega  -- |f| < |e| and |g| < |f| → |g| < |e| hmm: hef1: edgeSize f < edgeSize e; hfg1: edgeSize g < edgeSize f: omega
    · left
      -- |g| = |f|, |f| < |e| → |g| < |e|
      omega
  · rcases hfg with hfg1 | ⟨heq2, hlt2⟩
    · -- |e| = |f|, |g| < |f| → |g| < |e|: left via trans of ≤? |g| < |f| = |e|: omega
      left
      omega
    · -- sizes all equal, base ranks: ord₀ e < ord₀ f < ord₀ g
      right
      constructor
      · omega
      · exact lt_trans hlt1 hlt2

lemma sizeLess_total {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord₀ : 𝓗 ≃ Fin k)
    {e f : 𝓗} (hne : e ≠ f) : SizeLess ord₀ e f ∨ SizeLess ord₀ f e := by
  by_cases h1 : edgeSize (f : Set (Fin n)) < edgeSize (e : Set (Fin n))
  · left
    exact Or.inl h1
  · by_cases h2 : edgeSize (e : Set (Fin n)) < edgeSize (f : Set (Fin n))
    · right
      exact Or.inl h2
    · have hEq : edgeSize (e : Set (Fin n)) = edgeSize (f : Set (Fin n)) := le_antisymm (le_of_not_gt h1) (le_of_not_gt h2)
      have hneR : ord₀ e ≠ ord₀ f := by
        intro hEqR
        exact hne (ord₀.injective hEqR)
      rcases (lt_or_gt_of_ne hneR) with hlt | hgt
      · left
        exact Or.inr ⟨hEq, hlt⟩
      · right
        exact Or.inr ⟨hEq.symm, hgt⟩

/-- the rank of e: the number of edges preceding e in the size order -/
noncomputable def sizeRankVal {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) (e : 𝓗) : ℕ := by
  classical
  exact ((Finset.univ : Finset 𝓗).filter (fun g : 𝓗 => SizeLess ord₀ g e)).card

/-- the size rank fits in Fin (card 𝓗) -/
lemma sizeRankVal_lt_card {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) (e : 𝓗) : sizeRankVal ord₀ e < Fintype.card 𝓗 := by
  classical
  let S : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter (fun g : 𝓗 => SizeLess ord₀ g e)
  have hsub : S ⊆ (Finset.univ : Finset 𝓗) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_univ x
  have hne : S ≠ (Finset.univ : Finset 𝓗) := by
    intro hEq
    have he : e ∈ (Finset.univ : Finset 𝓗) := Finset.mem_univ e
    have heS : e ∈ S := by rwa [hEq]
    rw [Finset.mem_filter] at heS
    exact sizeLess_irrefl ord₀ e heS.2
  have hss : S ⊂ (Finset.univ : Finset 𝓗) := by
    constructor
    · exact hsub
    · intro hU
      apply hne
      ext x
      constructor
      · intro hx
        exact Finset.mem_univ x
      · intro hx
        exact hU hx
  have hlt : S.card < (Finset.univ : Finset 𝓗).card := Finset.card_lt_card hss
  rw [Finset.card_univ] at hlt
  simpa [sizeRankVal, S] using hlt

/-- the rank of e in Fin (card 𝓗) -/
noncomputable def sizeRank {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) (e : 𝓗) : Fin (Fintype.card 𝓗) :=
  ⟨sizeRankVal ord₀ e, sizeRankVal_lt_card ord₀ e⟩

/-- preceding e ⇒ smaller rank: SizeLess e f → rank e < rank f -/
lemma sizeRank_mono {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) {e f : 𝓗} (hef : SizeLess ord₀ e f) :
    (sizeRank ord₀ e : ℕ) < (sizeRank ord₀ f : ℕ) := by
  classical
  let A : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter (fun g : 𝓗 => SizeLess ord₀ g e)
  let B : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter (fun g : 𝓗 => SizeLess ord₀ g f)
  have hsub : A ⊆ B := by
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ g, sizeLess_trans ord₀ hg.2 hef⟩
  have heB : e ∈ B := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ e, hef⟩
  have heA : e ∉ A := by
    intro h
    rw [Finset.mem_filter] at h
    exact sizeLess_irrefl ord₀ e h.2
  have hss : A ⊂ B := by
    constructor
    · exact hsub
    · intro hBsub
      exact heA (hBsub heB)
  have hcard : A.card < B.card := Finset.card_lt_card hss
  simpa [sizeRank, sizeRankVal, A, B] using hcard

/-- the size rank is injective -/
lemma sizeRank_injective {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) : Function.Injective (sizeRank ord₀) := by
  classical
  intro e f hEq
  by_contra hne
  rcases (sizeLess_total ord₀ hne) with hef | hfe
  · have hlt := sizeRank_mono ord₀ hef
    have hEqv : (sizeRank ord₀ e : ℕ) = (sizeRank ord₀ f : ℕ) := congrArg Fin.val hEq
    omega
  · have hlt := sizeRank_mono ord₀ hfe
    have hEqv : (sizeRank ord₀ e : ℕ) = (sizeRank ord₀ f : ℕ) := congrArg Fin.val hEq
    omega

/-- the size-decreasing ordering of the edges (by non-increasing size) -/
noncomputable def sizeOrder {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) : 𝓗 ≃ Fin (Fintype.card 𝓗) := by
  classical
  exact Equiv.ofBijective (sizeRank ord₀) ⟨sizeRank_injective ord₀, by
    -- injective map into a type of the same cardinality is surjective
    intro x
    have hinj := sizeRank_injective ord₀
    have himg : (Finset.univ.image (sizeRank ord₀)).card = Fintype.card 𝓗 := by
      rw [Finset.card_image_of_injective (s := (Finset.univ : Finset 𝓗)) (f := sizeRank ord₀) hinj]
      simp
    have hEq : (Finset.univ.image (sizeRank ord₀)) = (Finset.univ : Finset (Fin (Fintype.card 𝓗))) := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp
      · rw [himg]
        simp
    have hx : x ∈ Finset.univ.image (sizeRank ord₀) := by
      rw [hEq]
      simp
    rcases (Finset.mem_image.mp hx) with ⟨y, _hy, hEqx⟩
    exact ⟨y, hEqx⟩⟩

/-- in the size order, an earlier edge has size at least the later one -/
lemma sizeOrder_ge_size {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) ⦃e f : 𝓗⦄
    (h : (sizeOrder ord₀ f : ℕ) ≤ (sizeOrder ord₀ e : ℕ)) :
    (edgeSize (e : Set (Fin n)) : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by
  classical
  by_contra hnot
  have hle : edgeSize (f : Set (Fin n)) < edgeSize (e : Set (Fin n)) := by
    -- ¬ ((edgeSize e : ℝ) ≤ (edgeSize f : ℝ)) → edgeSize f < edgeSize e (naturals)
    have hnat : ¬ edgeSize (e : Set (Fin n)) ≤ edgeSize (f : Set (Fin n)) := by
      intro hnat
      apply hnot
      exact_mod_cast hnat
    omega
  have hs : SizeLess ord₀ e f := Or.inl hle
  have hlt := sizeRank_mono ord₀ hs
  have hsm : (sizeOrder ord₀ e : ℕ) = (sizeRank ord₀ e : ℕ) := rfl
  have hsf : (sizeOrder ord₀ f : ℕ) = (sizeRank ord₀ f : ℕ) := rfl
  have hlt' : (sizeOrder ord₀ e : ℕ) < (sizeOrder ord₀ f : ℕ) := by
    simpa [hsm, hsf] using hlt
  omega

/-- the last edge of the size order -/
noncomputable def lastEdge {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] [Nonempty 𝓗]
    (ord : 𝓗 ≃ Fin (Fintype.card 𝓗)) : 𝓗 :=
  ord.symm ⟨(Fintype.card 𝓗) - 1, by
    have hpos : 0 < Fintype.card 𝓗 := Fintype.card_pos
    omega⟩

/-- the last edge of the size order has rank k−1 -/
lemma rank_lastEdge {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] [Nonempty 𝓗]
    (ord : 𝓗 ≃ Fin (Fintype.card 𝓗)) :
    (ord (lastEdge ord) : ℕ) = (Fintype.card 𝓗) - 1 := by
  simp [lastEdge]

/-- (O1) holds vacuously at the last edge -/
lemma O1_last {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] [Nonempty 𝓗]
    (ord : 𝓗 ≃ Fin (Fintype.card 𝓗)) (τ : ℝ) : OrderingGoodness τ ord (lastEdge ord) := by
  classical
  intro f hle hne
  have hlf : (ord (lastEdge ord) : ℕ) = (Fintype.card 𝓗) - 1 := rank_lastEdge ord
  have hge : (Fintype.card 𝓗) - 1 ≤ (ord f : ℕ) := by
    rwa [hlf] at hle
  have hmax : (ord f : ℕ) = (Fintype.card 𝓗) - 1 := by
    have hlt : (ord f : ℕ) < Fintype.card 𝓗 := (ord f).isLt
    omega
  exfalso
  apply hne
  have hEq : ord f = ord (lastEdge ord) := by
    apply Fin.ext
    rw [hlf]
    exact hmax
  exact ord.injective hEq

/-- (O2) holds for the whole size order at its last edge -/
lemma O2_sizeOrder_last {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] [Nonempty 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) :
    OrderingBySize (sizeOrder ord₀) (lastEdge (sizeOrder ord₀)) := by
  classical
  intro e f hfe _hep
  -- hfe : rank f ≤ rank e: sizes: |e| ≤ |f|:
  exact sizeOrder_ge_size ord₀ (e := e) (f := f) hfe

/-- the size order supplies the initial admissible pair for Block I -/
theorem sizeOrder_admissible_last {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] [Nonempty 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) (τ : ℝ) :
    AdmissiblePair τ (sizeOrder ord₀) (lastEdge (sizeOrder ord₀)) :=
  ⟨O1_last (sizeOrder ord₀) τ, O2_sizeOrder_last ord₀⟩

/-- **Block I from the size order**: starting from the size-decreasing
ordering, either every edge is good or a volume-setup edge exists. -/
theorem sizeOrder_blockI {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] [Nonempty 𝓗]
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) (τ : ℝ) (hτ : τ < 1) :
    GoodOrdering τ (sizeOrder ord₀) ∨
      ∃ e : 𝓗, AdmissiblePair τ (sizeOrder ord₀) e ∧ 1 ≤ ((sizeOrder ord₀) e : ℕ) ∧
        (1 - τ) * (n : ℝ) < (precedingDegree 𝓗 (sizeOrder ord₀) e : ℝ) := by
  exact blockI (sizeOrder ord₀) τ (lastEdge (sizeOrder ord₀))
    (sizeOrder_admissible_last ord₀ τ) hτ

/-! ## Blocks II–III (proved): the good case and the volume-set setup

**Block II — the good case** is the left branch of `blockI` /
`sizeOrder_blockI`: when the forward-degree walk reaches the first edge,
`GoodOrdering` holds (`good_of_first_admissible`; the first edge has
`fwddeg = 0`, `fwddeg_zero_of_first`, and (O1) at that edge covers all
others).

**Block III — the volume-set setup.**  In the other branch of the walk,
`blockI` hands over an admissible edge `eStar` with
`1 ≤ (ord eStar : ℕ)` and `(1−τ)n < fwddeg(eStar)`.  The volume set is
`W := VolumeSet τ K ord eStar = {f ⪯ eStar : (edgeSize f : ℝ) ≤ sizeFactor·|eStar|}`
(`sizeFactor = 1+3τ^{1/4}K⁴`).  Proved here: `eStar ∈ W`
(`volumeSet_mem_self`), every member of `W` lies in the prefix of `eStar`
(`volumeSet_le_rank`) and has size at least `|eStar|` by (O2)
(`volumeSet_ge_self`), so (W1) holds (`volumeSet_maxSize`: all sizes within
the factor `sizeFactor` of each other).  The (W2) volume lower bound is
Block VI; the (O1)/(O2) properties of `eStar` are exactly the second
conjuncts of the `AdmissiblePair` produced by `blockI`. -/


/-- the volume set W of the (volume) alternative: edges of rank ≤ rank eStar
whose size is at most sizeFactor·|eStar| -/
noncomputable def VolumeSet {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) : Finset 𝓗 := by
  classical
  exact (Finset.univ : Finset 𝓗).filter (fun f : 𝓗 =>
    (ord f : ℕ) ≤ (ord eStar : ℕ) ∧
    (edgeSize (f : Set (Fin n)) : ℝ) ≤ sizeFactor τ K * (edgeSize (eStar : Set (Fin n)) : ℝ))

/-- membership in VolumeSet -/
lemma mem_VolumeSet {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar f : 𝓗) :
    f ∈ VolumeSet τ K ord eStar ↔
      (ord f : ℕ) ≤ (ord eStar : ℕ) ∧
      (edgeSize (f : Set (Fin n)) : ℝ) ≤ sizeFactor τ K * (edgeSize (eStar : Set (Fin n)) : ℝ) := by
  classical
  simp [VolumeSet]

/-- the size factor is non-negative -/
lemma sizeFactor_nonneg (τ : ℝ) (K : ℕ) : (0 : ℝ) ≤ sizeFactor τ K := by
  unfold sizeFactor tauQuarter
  have h1 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt τ) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (K : ℝ) ^ 4 := by positivity
  nlinarith

/-- the size factor is at least 1 -/
lemma sizeFactor_ge_one (τ : ℝ) (K : ℕ) : (1 : ℝ) ≤ sizeFactor τ K := by
  unfold sizeFactor tauQuarter
  have h1 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt τ) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (K : ℝ) ^ 4 := by positivity
  nlinarith

/-- eStar itself belongs to its volume set -/
lemma volumeSet_mem_self {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) : eStar ∈ VolumeSet τ K ord eStar := by
  classical
  rw [mem_VolumeSet]
  constructor
  · rfl
  · have hA : (1 : ℝ) ≤ sizeFactor τ K := sizeFactor_ge_one τ K
    have hnon : (0 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) := by positivity
    have hx : (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ sizeFactor τ K * (edgeSize (eStar : Set (Fin n)) : ℝ) := by
      nlinarith
    exact hx

/-- (O2) gives the lower bound |f| ≥ |eStar| for every f in the prefix of
eStar, hence for every f in the volume set -/
lemma volumeSet_ge_self {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) (hO2 : OrderingBySize ord eStar) {f : 𝓗}
    (hf : f ∈ VolumeSet τ K ord eStar) :
    (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by
  classical
  have hf' := (mem_VolumeSet τ K ord eStar f).mp hf
  -- O2 with middle edge eStar and earlier edge f: f ⪯ eStar ⪯ eStar
  have h1 : (ord f : ℕ) ≤ (ord eStar : ℕ) := hf'.1
  exact hO2 (e := eStar) (f := f) (by simpa using h1) (le_rfl)

/-- (W1): all members of the volume set have sizes within the factor
sizeFactor of each other -/
lemma volumeSet_maxSize {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) (hO2 : OrderingBySize ord eStar) :
    WMaxSize τ K (VolumeSet τ K ord eStar) := by
  classical
  intro e₁ e₂ he₁ he₂
  have he₁' := (mem_VolumeSet τ K ord eStar e₁).mp he₁
  have he₂' := (mem_VolumeSet τ K ord eStar e₂).mp he₂
  have hge := volumeSet_ge_self τ K ord eStar hO2 (f := e₂) he₂
  have hA : (0 : ℝ) ≤ sizeFactor τ K := sizeFactor_nonneg τ K
  have hAmul : sizeFactor τ K * (edgeSize (eStar : Set (Fin n)) : ℝ) ≤
      sizeFactor τ K * (edgeSize (e₂ : Set (Fin n)) : ℝ) :=
    mul_le_mul_of_nonneg_left hge hA
  exact le_trans he₁'.2 hAmul

/-- every member of the volume set lies in the prefix of eStar -/
lemma volumeSet_le_rank {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) {f : 𝓗} (hf : f ∈ VolumeSet τ K ord eStar) :
    (ord f : ℕ) ≤ (ord eStar : ℕ) :=
  ((mem_VolumeSet τ K ord eStar f).mp hf).1

/-- **Block III setup (proved)**: from an admissible edge eStar, the volume
set contains eStar, satisfies (W1), and lies in the prefix of eStar.  (W2)
— the volume lower bound — is Block VI; (O1) at eStar is inherited from the
admissible pair produced by `blockI`.) -/
theorem blockIII_setup {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) (hO2 : OrderingBySize ord eStar) :
    eStar ∈ VolumeSet τ K ord eStar ∧
    WMaxSize τ K (VolumeSet τ K ord eStar) ∧
    (∀ f ∈ VolumeSet τ K ord eStar, (ord f : ℕ) ≤ (ord eStar : ℕ)) := by
  exact ⟨volumeSet_mem_self τ K ord eStar,
    ⟨volumeSet_maxSize τ K ord eStar hO2, fun f hf => volumeSet_le_rank τ K ord eStar hf⟩⟩

/-! ## Block IV (statement pinned, structural part proved): neighbours ahead

The paper's `nbrs-ahead-of-e*-bound` is the following claim about the edge
`eStar` produced by Block I's walk: every *preceding neighbour* `e` of
`eStar` (`e ∈ fwdnbr(e*)`, i.e. `e` intersects `eStar` and precedes it) has
`|N(e) ∩ H^{⪯e*}| > (1−τ)n` — `BlockIVStatement τ ord eStar`.  It feeds
Block V's two applications of `fwdnbr_inequality2`, providing the
`m₁+m₂ ≥ (1−τ)n` input each time.

The paper argues: if some `e ∈ fwdnbr(e*)` violated the bound, then `e`
could "become the successor of `e*`" — a reordering whose (O1)+(O2)
admissibility contradicts the minimality of `e(H^{⪯e*})`.  That
reordering/admissibility argument is the remaining formal work of Block IV
(recorded as `BlockIVStatement`, whose proof is still open).

Proved here (the structural half): the prefix `segmentPrefix ord eStar`
(`H^{⪯e*}`) with membership and monotonicity lemmas; the set
`nbrsInPrefix ord eStar e` (`N(e) ∩ H^{⪯e*}`) with its membership
criterion; `eStar` itself lies in the set for `e ∈ fwdnbr(e*)`
(`eStar_mem_nbrsInPrefix`, so the count is at least one);
`fwdnbr(e) ⊆ nbrsInPrefix ord eStar e` (`fwdnbr_subset_nbrsInPrefix`) and
hence `|N(e)∩H^{⪯e*}| ≥ fwddeg(e)` (`card_nbrsInPrefix_ge_fwddeg`,
`nbrsAhead_ge_fwddeg`); and `|N(e)∩H^{⪯e*}| ≤ d(e)`
(`card_nbrsInPrefix_le_degree`). -/


/-- the prefix of eStar: edges of rank at most that of eStar (H^{⪯e*}) -/
noncomputable def segmentPrefix {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) : Finset 𝓗 := by
  classical
  exact (Finset.univ : Finset 𝓗).filter (fun f : 𝓗 => (ord f : ℕ) ≤ (ord eStar : ℕ))

/-- membership in the prefix -/
lemma mem_segmentPrefix {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar f : 𝓗) : f ∈ segmentPrefix ord eStar ↔ (ord f : ℕ) ≤ (ord eStar : ℕ) := by
  classical
  simp [segmentPrefix]

/-- the prefix contains its own end edge -/
lemma segmentPrefix_self {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) : eStar ∈ segmentPrefix ord eStar := by
  rw [mem_segmentPrefix]

/-- prefixes are monotone: prefix(e) ⊆ prefix(eStar) when e ⪯ eStar -/
lemma segmentPrefix_mono {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {e eStar : 𝓗} (h : (ord e : ℕ) ≤ (ord eStar : ℕ)) :
    segmentPrefix ord e ⊆ segmentPrefix ord eStar := by
  intro f hf
  rw [mem_segmentPrefix] at hf ⊢
  exact le_trans hf h

/-- the neighbours of e lying in the prefix of eStar -/
noncomputable def nbrsInPrefix {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) : Finset 𝓗 :=
  neighbourEdges 𝓗 e ∩ segmentPrefix ord eStar

/-- membership in nbrsInPrefix -/
lemma mem_nbrsInPrefix {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e f : 𝓗) :
    f ∈ nbrsInPrefix ord eStar e ↔
      f ∈ neighbourEdges 𝓗 e ∧ (ord f : ℕ) ≤ (ord eStar : ℕ) := by
  classical
  rw [nbrsInPrefix, Finset.mem_inter, mem_segmentPrefix]

/-- if e is a preceding neighbour of eStar, then eStar itself is a neighbour
of e lying in the prefix of eStar -/
lemma eStar_mem_nbrsInPrefix {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {e eStar : 𝓗} (he : e ∈ precedingNeighbours 𝓗 ord eStar) :
    eStar ∈ nbrsInPrefix ord eStar e := by
  classical
  have he' := (mem_precedingNeighbours 𝓗 ord eStar e).mp he
  rw [mem_nbrsInPrefix]
  constructor
  · rw [mem_neighbourEdges]
    constructor
    · exact he'.1.symm
    · rcases he'.2.2 with ⟨x, hx⟩
      exact ⟨x, hx.2, hx.1⟩
  · exact le_rfl

/-- the forward neighbours of e lie in the prefix of eStar whenever e does:
fwdnbr(e) ⊆ N(e) ∩ H^{⪯e*} -/
lemma fwdnbr_subset_nbrsInPrefix {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {e eStar : 𝓗} (he : (ord e : ℕ) ≤ (ord eStar : ℕ)) :
    precedingNeighbours 𝓗 ord e ⊆ nbrsInPrefix ord eStar e := by
  classical
  intro f hf
  rw [mem_nbrsInPrefix]
  constructor
  · have hf' := (mem_precedingNeighbours 𝓗 ord e f).mp hf
    -- f ∈ N(e):
    rw [mem_neighbourEdges]
    exact ⟨hf'.1, hf'.2.2⟩
  · have hf' := (mem_precedingNeighbours 𝓗 ord e f).mp hf
    have hfn : (ord f : ℕ) ≤ (ord e : ℕ) := by simpa using hf'.2.1
    exact le_trans hfn he

/-- the count of neighbours of e inside the prefix of eStar is at least
fwddeg(e) when e lies in the prefix -/
lemma card_nbrsInPrefix_ge_fwddeg {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {e eStar : 𝓗} (he : (ord e : ℕ) ≤ (ord eStar : ℕ)) :
    precedingDegree 𝓗 ord e ≤ (nbrsInPrefix ord eStar e).card := by
  classical
  exact Finset.card_le_card (fwdnbr_subset_nbrsInPrefix ord he)

/-- the count of neighbours of e inside the prefix of eStar is at most the
total degree of e -/
lemma card_nbrsInPrefix_le_degree {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) : (nbrsInPrefix ord eStar e).card ≤ (neighbourEdges 𝓗 e).card := by
  classical
  exact Finset.card_le_card (by intro f hf; exact (Finset.mem_inter.mp hf).1)

/-- the paper's bound `|N(e) ∩ H^{⪯e*}| > (1−τ)n` -/
def NeighbourAheadBound {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) : Prop :=
  (1 - τ) * (n : ℝ) < ((nbrsInPrefix ord eStar e).card : ℝ)

/-- **Block IV (statement)**: every preceding neighbour e of eStar has more
than (1−τ)n neighbours inside the prefix of eStar. -/
def BlockIVStatement {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) : Prop :=
  ∀ e : 𝓗, e ∈ precedingNeighbours 𝓗 ord eStar → NeighbourAheadBound τ ord eStar e

/-- the count of neighbours inside the prefix is at least fwddeg(e) (a
quantitative form of the monotonicity of prefixes) -/
theorem nbrsAhead_ge_fwddeg {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    {e eStar : 𝓗} (he : e ∈ precedingNeighbours 𝓗 ord eStar) :
    (precedingDegree 𝓗 ord e : ℝ) ≤ ((nbrsInPrefix ord eStar e).card : ℝ) := by
  classical
  have hrank : (ord e : ℕ) ≤ (ord eStar : ℕ) := (mem_precedingNeighbours 𝓗 ord eStar e).mp he |>.2.1
  exact_mod_cast (card_nbrsInPrefix_ge_fwddeg ord (he := hrank))

/-! ## Block IV reordering machinery (first structural piece proved)

The remaining step of Block IV is the paper's swap: if a preceding
neighbour `e` of `eStar` violated `|N(e)∩H^{⪯e*}| > (1−τ)n`, then "we can
make `e` the successor of `e*`".  As a first structural piece, the swap is
formalised as a *transposition of two ranks*: `swapPositions ord a c`
(= `ord.trans (Equiv.swap a c)`) is a valid ordering of the same edge set;
`swapPositions_rank_a`/`swapPositions_rank_c`/
`swapPositions_rank_other` give the rank of the edge formerly at `a`, at
`c`, and of all other edges.  `successorPos`/`successorEdge` name the
successor rank/edge of `eStar` (when `eStar` is not the last edge), and
`blockIV_swap_ranks` states the effect of the swap used in Block IV: with
`sp := successorPos ord eStar h`, `swapPositions ord (ord e) sp` sends `e`
to rank `(rank eStar)+1` and the old successor to `e`'s rank.  (Showing
that the swapped pair satisfies (O1)+(O2) under the hypothesis that the
bound fails, contradicting the minimality recorded in `blockI`, is the
remaining work of Block IV.) -/


/-- swap the edges currently at positions a and c of the ordering ord,
yielding a new (valid) ordering of the same edge set -/
def swapPositions {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a c : Fin k) : 𝓗 ≃ Fin k :=
  ord.trans (Equiv.swap a c)

/-- the swapped ordering is a valid ordering of 𝓗 (it is an equivalence) -/
theorem swapPositions_isOrder {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a c : Fin k) : Nonempty (𝓗 ≃ Fin k) := ⟨swapPositions ord a c⟩

/-- the edge formerly at position a now has rank c -/
lemma swapPositions_rank_a {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a c : Fin k) : (swapPositions ord a c (ord.symm a) : ℕ) = (c : ℕ) := by
  simp [swapPositions, Equiv.swap_apply_left]

/-- the edge formerly at position c now has rank a -/
lemma swapPositions_rank_c {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a c : Fin k) : (swapPositions ord a c (ord.symm c) : ℕ) = (a : ℕ) := by
  simp [swapPositions, Equiv.swap_apply_right]

/-- edges at other positions keep their rank -/
lemma swapPositions_rank_other {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a c : Fin k) {x : 𝓗} (hxa : (ord x : ℕ) ≠ (a : ℕ)) (hxc : (ord x : ℕ) ≠ (c : ℕ)) :
    (swapPositions ord a c x : ℕ) = (ord x : ℕ) := by
  classical
  have h1 : (ord x : Fin k) ≠ a := by
    intro hEq
    apply hxa
    exact congrArg Fin.val hEq
  have h2 : (ord x : Fin k) ≠ c := by
    intro hEq
    apply hxc
    exact congrArg Fin.val hEq
  have hSwap : Equiv.swap a c (ord x) = ord x := Equiv.swap_apply_of_ne_of_ne h1 h2
  calc
    (swapPositions ord a c x : ℕ) = (Equiv.swap a c (ord x) : ℕ) := by
      simp [swapPositions]
    _ = (ord x : ℕ) := congrArg Fin.val hSwap

/-- the successor position of eStar, when eStar is not the last edge -/
def successorPos {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (h : (ord eStar : ℕ) + 1 < k) : Fin k :=
  ⟨(ord eStar : ℕ) + 1, h⟩

/-- **the Block IV swap (first structural piece)**: making `e` the
successor of `eStar` is the transposition of `e`'s position with the
successor position `sp` of `eStar` (`successorPos`): the resulting
`swapPositions ord (ord e) sp` is a valid ordering of the same edge set,
`e` moves to rank `(rank eStar)+1`, and the old occupant of that rank
(`ord.symm sp`) moves to `e`'s former rank. -/
theorem blockIV_swap_ranks {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (h : (ord eStar : ℕ) + 1 < k) (e : 𝓗) :
    (swapPositions ord (ord e) (successorPos ord eStar h) e : ℕ) = (ord eStar : ℕ) + 1 ∧
    (swapPositions ord (ord e) (successorPos ord eStar h)
        (ord.symm (successorPos ord eStar h)) : ℕ) = (ord e : ℕ) := by
  classical
  let sp : Fin k := successorPos ord eStar h
  constructor
  · calc
      (swapPositions ord (ord e) sp e : ℕ)
          = (swapPositions ord (ord e) sp (ord.symm (ord e)) : ℕ) := by
            have hE : e = ord.symm (ord e) := (Equiv.symm_apply_apply ord e).symm
            exact congrArg (fun t : 𝓗 => (swapPositions ord (ord e) sp t : ℕ)) hE
      _ = (sp : ℕ) := swapPositions_rank_a ord (ord e) sp
      _ = (ord eStar : ℕ) + 1 := rfl
  · simpa [sp] using (swapPositions_rank_c ord (ord e) sp)

/-! ## Block IV: the swap changes e's forward degree at most by one (proved)

The connection between the failing bound `|N(e)∩H^{⪯e*}| ≤ (1−τ)n` and
the swap "make `e` the successor of `e*`" is the following verified fact:
after transposing `e` with the successor `s := succEdgeOf ord eStar hpos` of
`eStar`, the *forward* neighbours of `e` are contained in
`(N(e) ∩ H^{⪯e*}) ∪ {s}` (`swap_fwdnbr_subset`), so the new forward degree
of `e` is at most `|N(e)∩H^{⪯e*}| + 1` (`swap_fwddeg_le_count`).  In
particular a failing bound keeps the new forward degree within
`(1−τ)n + 1`.  (Showing the full preservation of (O1)+(O2) for the swapped
pair — the remaining step that turns this into the contradiction recorded
in `blockI` — is the rest of Block IV.) -/


/-- the successor of eStar (its edge, when eStar is not last) -/
noncomputable def succEdgeOf {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (h : (ord eStar : ℕ) + 1 < k) : 𝓗 :=
  ord.symm (successorPos ord eStar h)

/-- rank of the successor -/
lemma rank_succEdgeOf {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (h : (ord eStar : ℕ) + 1 < k) :
    (ord (succEdgeOf ord eStar h) : ℕ) = (ord eStar : ℕ) + 1 := by
  simp [succEdgeOf, successorPos]

/-- after swapping e with the successor of eStar, the forward neighbours of
e lie in (neighbours of e inside the prefix of eStar) ∪ {the successor} -/
lemma swap_fwdnbr_subset {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) (hpos : (ord eStar : ℕ) + 1 < k)
    (_he : e ∈ precedingNeighbours 𝓗 ord eStar) :
    (precedingNeighbours 𝓗 (swapPositions ord (ord e) (successorPos ord eStar hpos)) e)
      ⊆ insert (succEdgeOf ord eStar hpos) (nbrsInPrefix ord eStar e) := by
  classical
  let ord' : 𝓗 ≃ Fin k := swapPositions ord (ord e) (successorPos ord eStar hpos)
  let s : 𝓗 := succEdgeOf ord eStar hpos
  intro f hf
  have hf' := (mem_precedingNeighbours 𝓗 ord' e f).mp hf
  rw [Finset.mem_insert]
  by_cases hfs : f = s
  · exact Or.inl hfs
  · right
    rw [mem_nbrsInPrefix]
    constructor
    · rw [mem_neighbourEdges]
      exact ⟨hf'.1, hf'.2.2⟩
    · have hrf' : (ord' f : ℕ) ≤ (ord' e : ℕ) := by simpa using hf'.2.1
      have hre : (ord' e : ℕ) = (ord eStar : ℕ) + 1 := (blockIV_swap_ranks ord eStar hpos e).1
      have hrank : (ord f : ℕ) ≠ (ord e : ℕ) := by
        intro hEq
        apply hf'.1
        apply ord.injective
        apply Fin.ext
        exact hEq
      have hrankS : (ord f : ℕ) ≠ (ord eStar : ℕ) + 1 := by
        intro hEq
        apply hfs
        have hEq' : ord f = ord s := by
          apply Fin.ext
          rw [rank_succEdgeOf ord eStar hpos]
          exact hEq
        exact ord.injective hEq'
      have hrf : (ord' f : ℕ) = (ord f : ℕ) := by
        dsimp [ord']
        apply swapPositions_rank_other
        · exact hrank
        · exact hrankS
      rw [hrf, hre] at hrf'
      have hfin : (ord f : ℕ) ≤ (ord eStar : ℕ) := by omega
      exact hfin

/-- **Block IV link**: after swapping `e` with the successor of `eStar`,
the forward degree of `e` is at most `|N(e)∩H^{⪯e*}| + 1` — the raw form of
the paper's "or else we can make e the successor of e*" step: a failing
bound keeps `e`'s new forward degree within `(1−τ)n + 1`. -/
theorem swap_fwddeg_le_count {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) (hpos : (ord eStar : ℕ) + 1 < k)
    (_he : e ∈ precedingNeighbours 𝓗 ord eStar) :
    (precedingDegree 𝓗 (swapPositions ord (ord e) (successorPos ord eStar hpos)) e : ℝ) ≤
      ((nbrsInPrefix ord eStar e).card : ℝ) + 1 := by
  classical
  have hsub := swap_fwdnbr_subset ord eStar e hpos _he
  have hcard : (precedingNeighbours 𝓗 (swapPositions ord (ord e) (successorPos ord eStar hpos)) e).card ≤
      (insert (succEdgeOf ord eStar hpos) (nbrsInPrefix ord eStar e)).card :=
    Finset.card_le_card hsub
  have hins : (insert (succEdgeOf ord eStar hpos) (nbrsInPrefix ord eStar e)).card ≤
      (nbrsInPrefix ord eStar e).card + 1 := by
    by_cases hm : succEdgeOf ord eStar hpos ∈ nbrsInPrefix ord eStar e
    · rw [Finset.insert_eq_of_mem hm]
      omega
    · rw [Finset.card_insert_of_notMem hm]
  have htotal : (precedingNeighbours 𝓗 (swapPositions ord (ord e) (successorPos ord eStar hpos)) e).card ≤
      (nbrsInPrefix ord eStar e).card + 1 := hcard.trans hins
  exact_mod_cast htotal

/-! ## Block IV: the intended rotation statement (semantics resolved)

Re-reading the paper settles which pair the swap makes admissible.  "Make
`e` the successor of `e*`" is the **block rotation**: delete the edge `e`
(from its position `a := (ord e : ℕ)` *before* `e*`) and reinsert it
directly after `e*` (at the old rank `b := (ord eStar : ℕ)` of `eStar`),
shifting the block `(a, b]` one step down and everything after `b` one step
up.  The distinguished edge **remains `eStar`**, now at rank `b − 1`; `e`
is its successor (rank `b`).  Consequences (each verifiable from the
rotation's rank function `ρ`: `ρ(a) = b`, `ρ(i) = i−1` for `a < i ≤ b`,
`ρ(i) = i` for `i < a`, `ρ(i) = i+1` for `i > b`):

* the new prefix of `eStar` is the old prefix minus `{e}`:
  `e(H'^{⪯'e*}) = e(H^{⪯e*}) − 1` — this is what contradicts the minimality
  of `e(H^{⪯e*})` recorded in Block I once the new pair is admissible;
* the new forward degree of `e` is **exactly** `|N(e) ∩ H^{⪯e*}|` (no `+1`:
  a neighbour `g` of `e` has `ρ(rank g) ≤ b−1 = rank' eStar` iff
  `rank g ≤ b`); so the failing bound
  `|N(e) ∩ H^{⪯e*}| ≤ (1−τ)n` yields `fwddeg'(e) ≤ (1−τ)n`;
* (O2) at `eStar` is preserved: the order within the new prefix
  (`old prefix ∖ {e}`) is the old order, so `f ⪯' g ⪯' eStar` is an old
  `f ⪯ g ⪯ eStar` pair;
* (O1) at `eStar` is preserved: the only edge newly after `eStar` is `e`
  itself (`fwddeg'(e) ≤ (1−τ)n` above); all other edges after `eStar`
  keep their preceding sets, hence their forward degrees.

**Target lemma (`BlockIVRotation`).**  From an admissible pair
`(ord, eStar)` at which the forward degree exceeds `(1−τ)n`
(Block I's volume branch), with `a := (ord e : ℕ) < b := (ord eStar : ℕ)`
for a preceding neighbour `e` whose in-prefix neighbour count
`|N(e) ∩ H^{⪯e*}|` is at most `(1−τ)n`, the block-rotation order `ord'`
satisfies `AdmissiblePair τ ord' eStar` and `e(H'^{⪯'e*}) =
e(H^{⪯e*}) − 1` — the contradiction that proves `BlockIVStatement`.
(The rotation order itself — the bijection `ρ` of `Fin k` described above —
and the six listed consequences are the remaining formal work of Block IV;
the rank facts `a ↦ b`, segment shift, and prefix/fwddeg identities are
straightforward `Finset`/`Fin` calculations over `swapPositions`-style
machinery or a direct `ρ`-based equivalence.) -/

/-! ## Block IV: the block-rotation bijection ρ (proved)

The intended Block IV move (see the earlier header note) is the *block
rotation* of the segment `[a..b]` of ranks: `rotateVal a b` sends the
occupant of `a` to `b`, every occupant of `(a,b]` one step down, and the
rest is fixed; `rotateInv a b` is its inverse (`b ↦ a`, `[a,b)` up one).
`rotateInv_of_rotate_eq` / `rotateVal_of_rotateInv_eq` verify the two
inverse identities, and **`rotateEquiv a b hab hb`** packages the rotation
as a permutation of `Fin k` (via `Equiv.ofBijective`, using the left and
right inverses).  First rank consequences, each stated at the level the
Block IV proof needs: `rotateEquiv_apply_a` (`ρ(a) = b`: `e` becomes the
successor of `eStar`), `rotateEquiv_apply_shift` (`ρ(i) = i−1` for
`a < i ≤ b`: the block between them shifts down — `eStar` at `b` moves to
`b−1`), and `rotateEquiv_apply_outside` (ranks outside `[a..b]` fixed).
The remaining consequences (prefix of `eStar` loses exactly `e`; the new
forward degree of `e` is exactly `|N(e)∩H^{⪯e*}|`; (O1)+(O2) preservation
of `(ord', eStar)`) build on these rank facts one at a time. -/


/-- block-rotation on the segment [a..b] of natural ranks: a ↦ b, (a,b] ↦ down one, rest fixed -/
def rotateVal (a b : ℕ) (i : ℕ) : ℕ :=
  if i = a then b
  else if a < i ∧ i ≤ b then i - 1
  else i

/-- its inverse: b ↦ a, [a,b) ↦ up one, rest fixed -/
def rotateInv (a b : ℕ) (j : ℕ) : ℕ :=
  if j = b then a
  else if a ≤ j ∧ j < b then j + 1
  else j

/-- left inverse: rotateInv after rotateVal is the identity -/
lemma rotateInv_of_rotate_eq {a b i : ℕ} (hab : a ≤ b) :
    rotateInv a b (rotateVal a b i) = i := by
  unfold rotateVal rotateInv
  by_cases hia : i = a
  · rw [if_pos hia]
    simp [hia]
  · rw [if_neg hia]
    by_cases hin : a < i ∧ i ≤ b
    · rw [if_pos hin]
      have h1 : ¬ ((i - 1) = b) := by omega
      have h2 : a ≤ i - 1 ∧ i - 1 < b := by omega
      rw [if_neg h1, if_pos h2]
      omega
    · rw [if_neg hin]
      have hne : i ≠ b := by
        intro hib
        by_cases hlt : a < b
        · apply hin
          constructor
          · omega
          · omega
        · apply hia
          omega
      have hnot : ¬ (a ≤ i ∧ i < b) := by
        intro hlb
        apply hin
        constructor
        · omega
        · exact le_of_lt hlb.2
      rw [if_neg hne, if_neg hnot]

/-- right inverse: rotateVal after rotateInv is the identity -/
lemma rotateVal_of_rotateInv_eq {a b j : ℕ} (hab : a ≤ b) :
    rotateVal a b (rotateInv a b j) = j := by
  unfold rotateVal rotateInv
  by_cases hjb : j = b
  · rw [if_pos hjb]
    -- rotateVal a = b:
    have hia : a = a := rfl
    rw [if_pos hia]
    simp [hjb]
  · rw [if_neg hjb]
    by_cases hin : a ≤ j ∧ j < b
    · rw [if_pos hin]
      have h1 : ¬ ((j + 1) = a) := by omega
      have h2 : a < j + 1 ∧ j + 1 ≤ b := by omega
      rw [if_neg h1, if_pos h2]
      omega
    · rw [if_neg hin]
      have hne : j ≠ a := by
        intro hja
        by_cases hlt : a < b
        · apply hin
          constructor
          · omega
          · omega
        · apply hjb
          omega
      have hnot : ¬ (a < j ∧ j ≤ b) := by
        intro hlb
        apply hin
        constructor
        · exact le_of_lt hlb.1
        · by_cases hje : j = b
          · exact False.elim (hjb hje)
          · exact lt_of_le_of_ne hlb.2 hje
      rw [if_neg hne, if_neg hnot]

/-- the block rotation of the segment [a..b] as a permutation of Fin k -/
noncomputable def rotateEquiv {k : ℕ} (a b : ℕ) (hab : a ≤ b) (hb : b < k) : Fin k ≃ Fin k := by
  classical
  let f : Fin k → Fin k := fun i => ⟨rotateVal a b i.val, by
    unfold rotateVal
    by_cases h1 : i.val = a
    · rw [if_pos h1]
      exact hb
    · rw [if_neg h1]
      by_cases h2 : a < i.val ∧ i.val ≤ b
      · rw [if_pos h2]
        omega
      · rw [if_neg h2]
        exact i.isLt⟩
  let g : Fin k → Fin k := fun j => ⟨rotateInv a b j.val, by
    unfold rotateInv
    by_cases h1 : j.val = b
    · rw [if_pos h1]
      omega
    · rw [if_neg h1]
      by_cases h2 : a ≤ j.val ∧ j.val < b
      · rw [if_pos h2]
        omega
      · rw [if_neg h2]
        exact j.isLt⟩
  have hL : Function.LeftInverse g f := by
    intro i
    apply Fin.ext
    simp [f, g, rotateInv_of_rotate_eq hab]
  have hR : Function.RightInverse g f := by
    intro j
    apply Fin.ext
    simp [f, g, rotateVal_of_rotateInv_eq hab]
  exact Equiv.mk f g hL hR


/-- rank consequence: the occupant of a moves to b -/
lemma rotateEquiv_apply_a {k : ℕ} (a b : ℕ) (hab : a ≤ b) (hb : b < k)
    {i : Fin k} (hia : (i : ℕ) = a) :
    ((rotateEquiv a b hab hb) i : ℕ) = b := by
  classical
  simp [rotateEquiv]
  unfold rotateVal
  rw [if_pos hia]

/-- rank consequence: edges strictly inside the segment (a..b] shift down by one -/
lemma rotateEquiv_apply_shift {k : ℕ} (a b : ℕ) (hab : a ≤ b) (hb : b < k)
    {i : Fin k} (hlt : a < (i : ℕ)) (hle : (i : ℕ) ≤ b) :
    ((rotateEquiv a b hab hb) i : ℕ) = (i : ℕ) - 1 := by
  classical
  simp [rotateEquiv]
  unfold rotateVal
  rw [if_neg (by omega : ¬ (i : ℕ) = a)]
  rw [if_pos ⟨hlt, hle⟩]

/-- rank consequence: edges outside the segment are fixed -/
lemma rotateEquiv_apply_outside {k : ℕ} (a b : ℕ) (hab : a ≤ b) (hb : b < k)
    {i : Fin k} (hout : ¬ (a < (i : ℕ) ∧ (i : ℕ) ≤ b)) (hna : (i : ℕ) ≠ a) :
    ((rotateEquiv a b hab hb) i : ℕ) = (i : ℕ) := by
  classical
  simp [rotateEquiv]
  unfold rotateVal
  rw [if_neg hna, if_neg hout]

/-! ## Block IV, consequence 1 (proved): the rotated prefix loses exactly e

With the rotation `rotateEquiv` in hand, the first of the six recorded
consequences is proved: `blockIV_prefix` — if `e` is at rank `a`, `eStar`
at rank `b` (`a < b`), then in the rotated order `ord.trans (rotateEquiv a
b (le_of_lt hab) hb)` the prefix of `eStar` is exactly
`(segmentPrefix ord eStar).erase e`, i.e. the old prefix with `e` removed.
In particular `e(H'^{⪯'e*}) = e(H^{⪯e*}) − 1`, the decrease that
contradicts Block I's minimality once the rotated pair is admissible.
Helpers proved along the way: `rotate_rank_val` (the rank of any edge in
the rotated order is `rotateVal` applied to its old rank),
`rotate_rank_eStar` (the rank of `eStar` becomes `b − 1`), and
`rotateVal_le_sub_one'` (values `≤ b` other than `a` end up `≤ b−1`). -/


/-- rank value of an edge in the rotated order -/
lemma rotate_rank_val {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a ≤ b) (hb : b < k) (x : 𝓗) :
    ((ord.trans (rotateEquiv a b hab hb)) x : ℕ) = rotateVal a b (ord x : ℕ) := by
  classical
  change ((rotateEquiv a b hab hb) (ord x : Fin k) : ℕ) = rotateVal a b (ord x : ℕ)
  simp [rotateEquiv]

/-- rank value of eStar in the rotated order: b − 1 -/
lemma rotate_rank_eStar {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) (eStar : 𝓗) (he : (ord eStar : ℕ) = b) :
    ((ord.trans (rotateEquiv a b (le_of_lt hab) hb)) eStar : ℕ) = b - 1 := by
  classical
  change ((rotateEquiv a b (le_of_lt hab) hb) (ord eStar : Fin k) : ℕ) = b - 1
  have hsh := rotateEquiv_apply_shift a b (le_of_lt hab) hb (i := (ord eStar : Fin k))
    (by omega : a < ((ord eStar : Fin k) : ℕ)) (by omega : ((ord eStar : Fin k) : ℕ) ≤ b)
  rw [hsh, he]


/-- the rotation sends a value ≤ b, ≠ a to a value ≤ b−1 -/
lemma rotateVal_le_sub_one' {a b j : ℕ} (hab : a < b) (hjb : j ≤ b) (hja : j ≠ a) :
    rotateVal a b j ≤ b - 1 := by
  unfold rotateVal
  by_cases h1 : j = a
  · exact False.elim (hja h1)
  · rw [if_neg h1]
    by_cases h2 : a < j ∧ j ≤ b
    · rw [if_pos h2]
      omega
    · rw [if_neg h2]
      have hna : ¬ a < j := fun hlt => h2 ⟨hlt, hjb⟩
      have : j ≤ b - 1 := by omega
      exact this

/-- **Block IV consequence 1**: after the rotation, the prefix of eStar is
exactly its old prefix minus {e}. -/
theorem blockIV_prefix {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) (e eStar : 𝓗)
    (he : (ord e : ℕ) = a) (heStar : (ord eStar : ℕ) = b) :
    segmentPrefix (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) eStar =
      (segmentPrefix ord eStar).erase e := by
  classical
  let ord' : 𝓗 ≃ Fin k := ord.trans (rotateEquiv a b (le_of_lt hab) hb)
  have hre : (ord' e : ℕ) = b := by
    simpa [ord'] using (rotateEquiv_apply_a a b (le_of_lt hab) hb (i := (ord e : Fin k)) he)
  have hreStar : (ord' eStar : ℕ) = b - 1 := by
    simpa [ord'] using (rotate_rank_eStar ord a b hab hb eStar heStar)
  ext f
  constructor
  · intro hf
    rw [Finset.mem_erase]
    constructor
    · intro hfe
      subst f
      rw [mem_segmentPrefix] at hf
      rw [hre, hreStar] at hf
      omega
    · rw [mem_segmentPrefix, heStar]
      have hf' := (mem_segmentPrefix ord' eStar f).1 hf
      have hval : (ord' f : ℕ) = rotateVal a b (ord f : ℕ) := by
        simpa [ord'] using (rotate_rank_val ord a b (le_of_lt hab) hb f)
      by_cases hleB : (ord f : ℕ) ≤ b
      · exact hleB
      · exfalso
        have hout : ¬ (a < (ord f : ℕ) ∧ (ord f : ℕ) ≤ b) := by omega
        have hna : (ord f : ℕ) ≠ a := by omega
        have hfix : rotateVal a b (ord f : ℕ) = (ord f : ℕ) := by
          unfold rotateVal
          rw [if_neg hna, if_neg hout]
        rw [hval, hfix, hreStar] at hf'
        omega
  · intro hf
    rcases (Finset.mem_erase.mp hf) with ⟨hne, hfold⟩
    rw [mem_segmentPrefix] at hfold
    rw [heStar] at hfold
    rw [mem_segmentPrefix]
    have hval : (ord' f : ℕ) = rotateVal a b (ord f : ℕ) := by
      simpa [ord'] using (rotate_rank_val ord a b (le_of_lt hab) hb f)
    rw [hval, hreStar]
    have hja : (ord f : ℕ) ≠ a := by
      intro hja
      apply hne
      apply ord.injective
      apply Fin.ext
      exact hja.trans he.symm
    exact rotateVal_le_sub_one' hab hfold hja

/-! ## Block IV, consequence 2 (proved): (O2) is preserved by the rotation

The rank-order facts about the block rotation on the natural ranks
`[0..b]`: `rotateVal` fixes ranks `< a` and `> b` (`rot_of_lt`,
`rot_of_gt`), decrements ranks in `(a,b]` (`rot_of_between`), is strictly
increasing on `[0..b]∖{a}` (`rotateVal_strict`) and hence order-reflecting
(`rotateVal_reflect`); a value whose rotation is `≤ b−1` has old rank
`≤ b` and `≠ a` (`old_rank_le_of_rot_le`, `old_rank_ne_a_of_rot_le`).
With these, **consequence 2** `blockIV_O2`: if `eStar` had (O2) in the old
order, it keeps (O2) in the rotated order `ord'` — ranks `e2 ⪯' e1 ⪯'
eStar` reflect back to old ranks `e2 ⪯ e1 ⪯ eStar` (all three old ranks
lie in `[0..b]∖{a}`, where `rotateVal` is order-isomorphic). -/

lemma rot_of_lt {a b j : ℕ} (hj : j < a) : rotateVal a b j = j := by
  unfold rotateVal
  rw [if_neg (by omega : ¬ j = a)]
  rw [if_neg (by omega : ¬ (a < j ∧ j ≤ b))]

lemma rot_of_between {a b j : ℕ} (h1 : a < j) (h2 : j ≤ b) : rotateVal a b j = j - 1 := by
  unfold rotateVal
  rw [if_neg (by omega : ¬ j = a)]
  rw [if_pos ⟨h1, h2⟩]

lemma rot_of_gt {a b j : ℕ} (hab : a ≤ b) (hj : b < j) : rotateVal a b j = j := by
  unfold rotateVal
  have hna : j ≠ a := by omega
  rw [if_neg hna]
  rw [if_neg (by omega : ¬ (a < j ∧ j ≤ b))]

/-- rotateVal is strictly increasing on the segment [0..b] minus {a} -/
lemma rotateVal_strict {a b j1 j2 : ℕ} (hab : a ≤ b) (h12 : j1 < j2) (h2b : j2 ≤ b)
    (h1a : j1 ≠ a) (h2a : j2 ≠ a) : rotateVal a b j1 < rotateVal a b j2 := by
  have h1b : j1 ≤ b := by omega
  -- j1 < a case
  by_cases h1la : j1 < a
  · -- j1 fixed
    have rj1 : rotateVal a b j1 = j1 := rot_of_lt h1la
    by_cases h2la : j2 < a
    · have rj2 : rotateVal a b j2 = j2 := rot_of_lt h2la
      rw [rj1, rj2]
      exact h12
    · -- a ≤ j2: a < j2 (j2 ≠ a): j2 ≤ b: between:
      have h2a' : a < j2 := by omega
      have rj2 : rotateVal a b j2 = j2 - 1 := rot_of_between h2a' h2b
      rw [rj1, rj2]
      have : j1 < j2 - 1 := by omega
      exact this
  · -- a ≤ j1: a < j1 (j1 ≠ a): j1 ∈ (a, b−1] region (j1 ≤ b, j1 < j2 ≤ b)
    have h1a' : a < j1 := by omega
    have rj1 : rotateVal a b j1 = j1 - 1 := rot_of_between h1a' h1b
    by_cases hjb : j2 = b
    · -- j2 = b: rotateVal b = b−1 (since a < b? if a = b then j1 ≤ b = a & j1> a impossible; so a < b)
      have hab' : a < b := by
        have : j1 < b := by omega
        omega
      have rj2 : rotateVal a b b = b - 1 := rot_of_between (a := a) (b := b) hab' le_rfl
      have rj2' : rotateVal a b j2 = b - 1 := by simpa [hjb] using rj2
      rw [rj1, rj2']
      have : j1 - 1 < b - 1 := by omega
      exact this
    · -- a < j2 < b: j2 ≠ b
      have h2b' : j2 ≤ b := h2b
      have h2a'' : a < j2 := by omega
      have rj2 : rotateVal a b j2 = j2 - 1 := rot_of_between h2a'' h2b'
      rw [rj1, rj2]
      have : j1 - 1 < j2 - 1 := by omega
      exact this

/-- rotateVal is order-reflecting on [0..b] minus {a} -/
lemma rotateVal_reflect {a b j1 j2 : ℕ} (hab : a ≤ b) (h1b : j1 ≤ b) (h1a : j1 ≠ a)
    (h2a : j2 ≠ a)
    (h : rotateVal a b j1 ≤ rotateVal a b j2) : j1 ≤ j2 := by
  by_contra hnot
  have hlt : j2 < j1 := lt_of_not_ge hnot
  have hstrict := rotateVal_strict (a := a) (b := b) hab hlt h1b h2a h1a
  exact (not_le_of_gt hstrict) h

/-- a value whose rotation is ≤ b−1 is at most b -/
lemma old_rank_le_of_rot_le {a b j : ℕ} (hab : a ≤ b) (h : rotateVal a b j ≤ b - 1) : j ≤ b := by
  by_contra hnot
  have hgt : b < j := lt_of_not_ge hnot
  have rj : rotateVal a b j = j := rot_of_gt hab hgt
  have : j ≤ b - 1 := by simpa [rj] using h
  omega

/-- a value whose rotation is ≤ b−1 (with b ≥ 1) is not a -/
lemma old_rank_ne_a_of_rot_le {a b j : ℕ} (h1b0 : 1 ≤ b) (h : rotateVal a b j ≤ b - 1) : j ≠ a := by
  intro hja
  subst j
  unfold rotateVal at h
  rw [if_pos rfl] at h
  omega

/-- **Block IV consequence 2**: (O2) is preserved by the rotation at eStar. -/
theorem blockIV_O2 {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) (eStar : 𝓗) (heStar : (ord eStar : ℕ) = b)
    (hO2 : OrderingBySize ord eStar) :
    OrderingBySize (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) eStar := by
  classical
  let ord' : 𝓗 ≃ Fin k := ord.trans (rotateEquiv a b (le_of_lt hab) hb)
  change OrderingBySize ord' eStar
  have hreStar : (ord' eStar : ℕ) = b - 1 := by
    simpa [ord'] using (rotate_rank_eStar ord a b hab hb eStar heStar)
  have hb0 : 1 ≤ b := by omega
  intro e1 e2 he2e1 he1es
  have hrv1 : (ord' e1 : ℕ) = rotateVal a b (ord e1 : ℕ) := by
    simpa [ord'] using (rotate_rank_val ord a b (le_of_lt hab) hb e1)
  have hrv2 : (ord' e2 : ℕ) = rotateVal a b (ord e2 : ℕ) := by
    simpa [ord'] using (rotate_rank_val ord a b (le_of_lt hab) hb e2)
  have h2e1es : (ord' e2 : ℕ) ≤ (ord' eStar : ℕ) := he2e1.trans he1es
  have hrot1 : rotateVal a b (ord e1 : ℕ) ≤ b - 1 := by
    rw [hrv1, hreStar] at he1es
    exact he1es
  have hrot2 : rotateVal a b (ord e2 : ℕ) ≤ b - 1 := by
    rw [hrv2, hreStar] at h2e1es
    exact h2e1es
  have hle1 : (ord e1 : ℕ) ≤ b := old_rank_le_of_rot_le (le_of_lt hab) hrot1
  have hna1 : (ord e1 : ℕ) ≠ a := old_rank_ne_a_of_rot_le hb0 hrot1
  have hle2 : (ord e2 : ℕ) ≤ b := old_rank_le_of_rot_le (le_of_lt hab) hrot2
  have hna2 : (ord e2 : ℕ) ≠ a := old_rank_ne_a_of_rot_le hb0 hrot2
  have hreflect : (ord e2 : ℕ) ≤ (ord e1 : ℕ) := by
    rw [hrv2, hrv1] at he2e1
    exact rotateVal_reflect (le_of_lt hab) hle2 hna2 hna1 he2e1
  have hOld : (ord e1 : ℕ) ≤ (ord eStar : ℕ) := by
    rw [heStar]
    exact hle1
  exact hO2 (e := e1) (f := e2) hreflect hOld

/-! ## Block IV, consequences 3–4 and the rotation step (proved)

Consequence 3 (`rotate_fwdnbr_eq_nbrsInPrefix` and its cardinal/real
forms `rotate_fwddeg_e`, `rotate_fwddeg_e_real_le_of_fail`): after the
rotation, the forward neighbours of `e` (the edge moved from rank `a` to
rank `b`, the successor of `eStar`) are *exactly* its neighbours inside
the old prefix of `eStar` — `fwddeg'(e) = |N(e) ∩ H^{⪯e*}|`, with **no
`+1`** — via the rank comparison `rotate_rank_le_b_iff` (the new rank is
`≤ b` iff the old rank is).  Consequence 4 (`blockIV_O1`): (O1) is
preserved at `eStar` — the only edge newly after `eStar` is `e` itself
(`old_rank_gt_b_of_new_rank_ge`: a new rank `≥ b−1` that is neither `a`
nor `b` was already after `b`), and edges with old rank `> b` keep their
predecessor sets (`rotate_fwdnbr_of_rank_gt_b`,
`rotate_fwddeg_of_rank_gt_b`).  The prefix decrease
(`blockIV_prefix_card`: the new prefix of `eStar` is one smaller) and
(O2) preservation (`blockIV_O2`, consequence 2) then assemble into the
**rotation step `blockIV_rotation`** (admissibility preserved + strict
prefix decrease), which yields Block IV in its paper form (eq. (6.3)):
`blockIV_of_minimal` — under the *minimality* of the prefix of `eStar`
among admissible pairs, every preceding neighbour `e` of `eStar` has
`|N(e) ∩ H^{⪯e*}| > (1−τ)n`.  (Supplying a minimal admissible pair —
e.g. a global minimum of the prefix size over all admissible pairs, which
exists since the orderings of a finite hypergraph form a finite set — is
recorded as a later step, `exists_minimal_admissible`; it is the only
remaining input of Block IV.) -/

lemma rotate_rank_le_b_iff {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a ≤ b) (hb : b < k) (x : 𝓗) :
    ((ord.trans (rotateEquiv a b hab hb)) x : ℕ) ≤ b ↔ (ord x : ℕ) ≤ b := by
  classical
  let ord' : 𝓗 ≃ Fin k := ord.trans (rotateEquiv a b hab hb)
  have hval : (ord' x : ℕ) = rotateVal a b (ord x : ℕ) := by
    simpa [ord'] using (rotate_rank_val ord a b hab hb x)
  rw [hval]
  constructor
  · intro h
    by_cases hle : (ord x : ℕ) ≤ b
    · exact hle
    · exfalso
      have hgt : b < (ord x : ℕ) := by omega
      have rj : rotateVal a b (ord x : ℕ) = (ord x : ℕ) := rot_of_gt hab hgt
      rw [rj] at h
      omega
  · intro h
    by_cases hxa : (ord x : ℕ) = a
    · have rj : rotateVal a b (ord x : ℕ) = b := by
        rw [hxa]
        unfold rotateVal
        rw [if_pos rfl]
      rw [rj]
    · have rj : rotateVal a b (ord x : ℕ) ≤ b := by
        unfold rotateVal
        rw [if_neg hxa]
        by_cases hin : a < (ord x : ℕ) ∧ (ord x : ℕ) ≤ b
        · rw [if_pos hin]
          omega
        · rw [if_neg hin]
          exact h
      exact rj

/-- **Block IV consequence 3**: after the rotation, the (forward) neighbours
of `e` are exactly its neighbours inside the old prefix of `eStar` —
`fwddeg'(e) = |N(e) ∩ H^{⪯e*}|` with no `+1`. -/
lemma rotate_fwdnbr_eq_nbrsInPrefix {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) (e eStar : 𝓗)
    (he : (ord e : ℕ) = a) (heStar : (ord eStar : ℕ) = b) :
    precedingNeighbours 𝓗 (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) e =
      nbrsInPrefix ord eStar e := by
  classical
  let ord' : 𝓗 ≃ Fin k := ord.trans (rotateEquiv a b (le_of_lt hab) hb)
  have hre : (ord' e : ℕ) = b := by
    simpa [ord'] using (rotateEquiv_apply_a a b (le_of_lt hab) hb (i := (ord e : Fin k)) he)
  have hnat_iff : ∀ g h : 𝓗, (ord' g ≤ ord' h) ↔ ((ord' g : ℕ) ≤ (ord' h : ℕ)) := by
    intro g h
    simp
  ext f
  rw [mem_precedingNeighbours, mem_nbrsInPrefix, mem_neighbourEdges]
  constructor
  · intro h
    rcases h with ⟨hne, hle, hint⟩
    constructor
    · constructor
      · exact hne
      · exact hint
    · have hleN : (ord' f : ℕ) ≤ (ord' e : ℕ) := (hnat_iff f e).1 hle
      rw [hre] at hleN
      have hleOld : (ord f : ℕ) ≤ b := (rotate_rank_le_b_iff ord a b (le_of_lt hab) hb f).mp hleN
      rw [heStar]
      exact hleOld
  · intro h
    rcases h with ⟨⟨hne, hint⟩, hlb⟩
    constructor
    · exact hne
    · constructor
      · rw [heStar] at hlb
        have hleNew : (ord' f : ℕ) ≤ b := (rotate_rank_le_b_iff ord a b (le_of_lt hab) hb f).mpr hlb
        have hn : (ord' f : ℕ) ≤ (ord' e : ℕ) := by
          rw [hre]
          exact hleNew
        exact (hnat_iff f e).2 hn
      · exact hint

/-- cardinality form: `fwddeg'(e) = |N(e)∩H^{⪯e*}|` -/
lemma rotate_fwddeg_e {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) (e eStar : 𝓗)
    (he : (ord e : ℕ) = a) (heStar : (ord eStar : ℕ) = b) :
    precedingDegree 𝓗 (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) e =
      (nbrsInPrefix ord eStar e).card := by
  rw [precedingDegree, rotate_fwdnbr_eq_nbrsInPrefix ord a b hab hb e eStar he heStar]

/-- **Block IV consequence 3, real form**: a failing bound
`|N(e)∩H^{⪯e*}| ≤ (1−τ)n` keeps `e`'s *new* forward degree within `(1−τ)n`,
so `e` is good in the rotated order. -/
lemma rotate_fwddeg_e_real_le_of_fail {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (a b : ℕ) (hab : a < b) (hb : b < k) (e eStar : 𝓗)
    (he : (ord e : ℕ) = a) (heStar : (ord eStar : ℕ) = b)
    (hfail : ((nbrsInPrefix ord eStar e).card : ℝ) ≤ (1 - τ) * (n : ℝ)) :
    (precedingDegree 𝓗 (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) e : ℝ) ≤
      (1 - τ) * (n : ℝ) := by
  rw [rotate_fwddeg_e ord a b hab hb e eStar he heStar]
  exact hfail

/-- an old rank whose rotation lands at-or-after b−1 (and is not a nor b)
lies strictly after b -/
lemma old_rank_gt_b_of_new_rank_ge {a b j : ℕ} (hab : a < b) (hj : b - 1 ≤ rotateVal a b j)
    (hja : j ≠ a) (hjb : j ≠ b) : b < j := by
  by_contra hnot
  have hle : j ≤ b := by omega
  by_cases hja' : j < a
  · have rj : rotateVal a b j = j := rot_of_lt hja'
    rw [rj] at hj
    omega
  · have hagt : a < j := by omega
    by_cases hjb' : j ≤ b
    · have rj : rotateVal a b j = j - 1 := rot_of_between hagt hjb'
      rw [rj] at hj
      have : j = b := by omega
      exact False.elim (hjb this)
    · omega

/-- rank value of x after the rotation when its old rank exceeds b: it is fixed -/
lemma rotate_rank_of_gt_b {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) (x : 𝓗) (hxb : b < (ord x : ℕ)) :
    ((ord.trans (rotateEquiv a b (le_of_lt hab) hb)) x : ℕ) = (ord x : ℕ) := by
  classical
  have hval : ((ord.trans (rotateEquiv a b (le_of_lt hab) hb)) x : ℕ) =
      rotateVal a b (ord x : ℕ) := by
    simpa using (rotate_rank_val ord a b (le_of_lt hab) hb x)
  rw [hval]
  exact rot_of_gt (le_of_lt hab) hxb

/-- for an edge whose old rank exceeds b, its new rank is ≤ its old rank
iff it was already (its predecessor sets in the two orders coincide) -/
lemma rotate_rank_le_iff_of_gt_b {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) {x : 𝓗} (hxb : b < (ord x : ℕ)) :
    ∀ f : 𝓗, ((ord.trans (rotateEquiv a b (le_of_lt hab) hb)) f : ℕ) ≤
        ((ord.trans (rotateEquiv a b (le_of_lt hab) hb)) x : ℕ) ↔
      (ord f : ℕ) ≤ (ord x : ℕ) := by
  classical
  let ord' : 𝓗 ≃ Fin k := ord.trans (rotateEquiv a b (le_of_lt hab) hb)
  intro f
  have hx' : (ord' x : ℕ) = (ord x : ℕ) := by
    simpa [ord'] using (rotate_rank_of_gt_b ord a b hab hb x hxb)
  have hval : (ord' f : ℕ) = rotateVal a b (ord f : ℕ) := by
    simpa [ord'] using (rotate_rank_val ord a b (le_of_lt hab) hb f)
  rw [hx']
  rw [hval]
  constructor
  · intro h
    by_contra hn
    have hgt : (ord x : ℕ) < (ord f : ℕ) := by omega
    have hbf : b < (ord f : ℕ) := by omega
    have rf : rotateVal a b (ord f : ℕ) = (ord f : ℕ) := rot_of_gt (le_of_lt hab) hbf
    rw [rf] at h
    omega
  · intro h
    by_cases hfa : (ord f : ℕ) = a
    · have rj : rotateVal a b (ord f : ℕ) = b := by
        rw [hfa]
        unfold rotateVal
        rw [if_pos rfl]
      rw [rj]
      exact (by omega : b ≤ (ord x : ℕ))
    · unfold rotateVal
      rw [if_neg hfa]
      by_cases hin : a < (ord f : ℕ) ∧ (ord f : ℕ) ≤ b
      · rw [if_pos hin]
        have hbf : b < (ord x : ℕ) := hxb
        omega
      · rw [if_neg hin]
        exact h

/-- **Block IV, fwddeg preservation past eStar**: edges that were strictly
after `eStar` (old rank > b) keep their predecessor sets, hence their
forward degrees, after the rotation. -/
lemma rotate_fwdnbr_of_rank_gt_b {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) (x : 𝓗) (hxb : b < (ord x : ℕ)) :
    precedingNeighbours 𝓗 (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) x =
      precedingNeighbours 𝓗 ord x := by
  classical
  let ord' : 𝓗 ≃ Fin k := ord.trans (rotateEquiv a b (le_of_lt hab) hb)
  have hnat_iff : ∀ g h : 𝓗, (ord' g ≤ ord' h) ↔ ((ord' g : ℕ) ≤ (ord' h : ℕ)) := by
    intro g h
    simp
  ext f
  rw [mem_precedingNeighbours, mem_precedingNeighbours]
  constructor
  · intro h
    rcases h with ⟨hne, hle, hint⟩
    constructor
    · exact hne
    · constructor
      · have hleN : (ord' f : ℕ) ≤ (ord' x : ℕ) := (hnat_iff f x).1 hle
        exact (rotate_rank_le_iff_of_gt_b ord a b hab hb (x := x) hxb f).1 hleN
      · exact hint
  · intro h
    rcases h with ⟨hne, hle, hint⟩
    constructor
    · exact hne
    · constructor
      · have hleN : (ord f : ℕ) ≤ (ord x : ℕ) := by simpa using hle
        have hle' : (ord' f : ℕ) ≤ (ord' x : ℕ) :=
          (rotate_rank_le_iff_of_gt_b ord a b hab hb (x := x) hxb f).2 hleN
        exact (hnat_iff f x).2 hle'
      · exact hint

/-- fwddeg is unchanged for edges with old rank > b -/
lemma rotate_fwddeg_of_rank_gt_b {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) (x : 𝓗) (hxb : b < (ord x : ℕ)) :
    precedingDegree 𝓗 (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) x =
      precedingDegree 𝓗 ord x := by
  rw [precedingDegree, precedingDegree, rotate_fwdnbr_of_rank_gt_b ord a b hab hb x hxb]

/-- **Block IV consequence 4**: (O1) is preserved by the rotation at
eStar — the only edge newly after eStar is `e` itself, and its new forward
degree is `|N(e)∩H^{⪯e*}| ≤ (1−τ)n`; every other edge after eStar keeps
its forward degree (old (O1)). -/
theorem blockIV_O1 {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (a b : ℕ) (hab : a < b) (hb : b < k) (e eStar : 𝓗)
    (he : (ord e : ℕ) = a) (heStar : (ord eStar : ℕ) = b)
    (hO1 : OrderingGoodness τ ord eStar)
    (hfail : ((nbrsInPrefix ord eStar e).card : ℝ) ≤ (1 - τ) * (n : ℝ)) :
    OrderingGoodness τ (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) eStar := by
  classical
  let ord' : 𝓗 ≃ Fin k := ord.trans (rotateEquiv a b (le_of_lt hab) hb)
  change OrderingGoodness τ ord' eStar
  have hsmall : (precedingDegree 𝓗 ord' e : ℝ) ≤ (1 - τ) * (n : ℝ) := by
    simpa [ord'] using (rotate_fwddeg_e_real_le_of_fail ord τ a b hab hb e eStar he heStar hfail)
  intro f hpf hne
  -- hpf : (ord' eStar : ℕ) ≤ (ord' f : ℕ); hne : f ≠ eStar
  by_cases hfe : f = e
  · subst f
    exact hsmall
  · have hpfN : (ord' eStar : ℕ) ≤ (ord' f : ℕ) := by simpa using hpf
    have hreStar' : (ord' eStar : ℕ) = b - 1 := by
      simpa [ord'] using (rotate_rank_eStar ord a b hab hb eStar heStar)
    rw [hreStar'] at hpfN
    have hrfv : (ord' f : ℕ) = rotateVal a b (ord f : ℕ) := by
      simpa [ord'] using (rotate_rank_val ord a b (le_of_lt hab) hb f)
    rw [hrfv] at hpfN
    have hja : (ord f : ℕ) ≠ a := by
      intro hEq
      apply hfe
      apply ord.injective
      apply Fin.ext
      exact hEq.trans he.symm
    have hjb : (ord f : ℕ) ≠ b := by
      intro hEq
      apply hne
      apply ord.injective
      apply Fin.ext
      exact hEq.trans heStar.symm
    have hgt : b < (ord f : ℕ) := old_rank_gt_b_of_new_rank_ge hab hpfN hja hjb
    have hfd : precedingDegree 𝓗 ord' f = precedingDegree 𝓗 ord f := by
      simpa [ord'] using (rotate_fwddeg_of_rank_gt_b ord a b hab hb f hgt)
    have hO1f : (precedingDegree 𝓗 ord f : ℝ) ≤ (1 - τ) * (n : ℝ) :=
      hO1 f (by omega) hne
    rw [hfd]
    exact hO1f

/-- the rotated prefix of eStar is one smaller than the old prefix -/
lemma blockIV_prefix_card {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (a b : ℕ) (hab : a < b) (hb : b < k) (e eStar : 𝓗)
    (he : (ord e : ℕ) = a) (heStar : (ord eStar : ℕ) = b) :
    (segmentPrefix (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) eStar).card + 1 =
      (segmentPrefix ord eStar).card := by
  classical
  have hp := blockIV_prefix ord a b hab hb e eStar he heStar
  have hein : e ∈ segmentPrefix ord eStar := by
    rw [mem_segmentPrefix, he, heStar]
    omega
  rw [hp]
  exact Finset.card_erase_add_one hein

/-- **the Block IV rotation step**: from an admissible pair (ord, eStar)
and a preceding edge `e` whose in-prefix neighbour count
`|N(e)∩H^{⪯e*}|` is at most `(1−τ)n`, the block rotation keeps the pair
admissible at eStar and strictly decreases the prefix of eStar. -/
theorem blockIV_rotation {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (a b : ℕ) (hab : a < b) (hb : b < k) (e eStar : 𝓗)
    (he : (ord e : ℕ) = a) (heStar : (ord eStar : ℕ) = b)
    (hadm : AdmissiblePair τ ord eStar)
    (hfail : ((nbrsInPrefix ord eStar e).card : ℝ) ≤ (1 - τ) * (n : ℝ)) :
    AdmissiblePair τ (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) eStar ∧
    (segmentPrefix (ord.trans (rotateEquiv a b (le_of_lt hab) hb)) eStar).card <
      (segmentPrefix ord eStar).card := by
  constructor
  · exact ⟨blockIV_O1 ord τ a b hab hb e eStar he heStar hadm.1 hfail,
      blockIV_O2 ord a b hab hb eStar heStar hadm.2⟩
  · have hc := blockIV_prefix_card ord a b hab hb e eStar he heStar
    omega

/-- **Block IV (paper eq. (6.3))**: by the minimality of the prefix of
eStar among all admissible pairs, every preceding neighbour `e` of eStar
has more than `(1−τ)n` neighbours inside the prefix of eStar. -/
theorem blockIV_of_minimal {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (eStar : 𝓗) (hadm : AdmissiblePair τ ord eStar)
    (hmin : ∀ (k' : ℕ) (ord' : 𝓗 ≃ Fin k') (e' : 𝓗), AdmissiblePair τ ord' e' →
      (segmentPrefix ord eStar).card ≤ (segmentPrefix ord' e').card) :
    BlockIVStatement τ ord eStar := by
  classical
  intro e hePre
  by_contra hnot
  have hfail : ((nbrsInPrefix ord eStar e).card : ℝ) ≤ (1 - τ) * (n : ℝ) := by
    exact le_of_not_gt hnot
  have hpre := (mem_precedingNeighbours 𝓗 ord eStar e).mp hePre
  have hleN : (ord e : ℕ) ≤ (ord eStar : ℕ) := by simpa using hpre.2.1
  have hneqN : (ord e : ℕ) ≠ (ord eStar : ℕ) := by
    intro h
    apply hpre.1
    apply ord.injective
    apply Fin.ext
    exact h
  have hab : (ord e : ℕ) < (ord eStar : ℕ) := by omega
  have hb' : (ord eStar : ℕ) < k := (ord eStar).isLt
  have hrot := blockIV_rotation ord τ (ord e : ℕ) (ord eStar : ℕ) hab hb' e eStar rfl rfl hadm hfail
  have hle := hmin k (ord.trans (rotateEquiv (ord e : ℕ) (ord eStar : ℕ) (le_of_lt hab) hb')) eStar hrot.1
  omega

/-! ## Block IV, minimality machinery (proved)

The paper's choice of ordering is *global*: an admissible pair whose prefix
`H^{⪯e*}` has minimum size over **all** admissible pairs.  Since the edges
of `𝓗 ⊆ Set (Fin n)` form a finite type, the prefix sizes achieved by
admissible pairs form a nonempty subset of `ℕ`, so the least such size
exists: `exists_minimal_admissible` (by `Nat.find`), with the Fintype
instance form `exists_minimal_admissible_of_fintype` (the size order
supplies the start pair).  From a minimal pair: its predecessor, when it
exists, would be admissible with a strictly smaller prefix
(`segmentPrefix_predEdge` removes `eStar` from its own prefix), so at rank
`≥ 1` the forward degree of `eStar` exceeds `(1−τ)n`
(`fwddeg_gt_of_minimal`); and `blockIV_of_minimal` (consequence of the
rotation step above) yields the in-prefix-neighbour bound (6.3)
`BlockIVStatement`.  `minimal_admissible_dichotomy` packages: either the
whole ordering is good, or `eStar` has rank `≥ 1`, forward degree
`> (1−τ)n` and `BlockIVStatement` — the exact setup that Blocks V and VI
turn into the volume witness. -/

lemma segmentPrefix_predEdge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (h : 1 ≤ (ord eStar : ℕ)) :
    segmentPrefix ord (predEdge ord eStar h) = (segmentPrefix ord eStar).erase eStar := by
  classical
  ext f
  rw [Finset.mem_erase]
  constructor
  · intro hf
    have hf' := (mem_segmentPrefix ord (predEdge ord eStar h) f).1 hf
    have hpe : (ord (predEdge ord eStar h) : ℕ) = (ord eStar : ℕ) - 1 := rank_predEdge ord eStar h
    rw [hpe] at hf'
    constructor
    · intro hfe
      subst f
      have : (ord eStar : ℕ) ≤ (ord eStar : ℕ) - 1 := hf'
      omega
    · rw [mem_segmentPrefix]
      omega
  · intro hf
    rcases hf with ⟨hne, hf'⟩
    have hrank : (ord f : ℕ) ≤ (ord eStar : ℕ) := (mem_segmentPrefix ord eStar f).1 hf'
    have hneN : (ord f : ℕ) ≠ (ord eStar : ℕ) := by
      intro hEq
      apply hne
      apply ord.injective
      apply Fin.ext
      exact hEq
    have hpe : (ord (predEdge ord eStar h) : ℕ) = (ord eStar : ℕ) - 1 := rank_predEdge ord eStar h
    rw [mem_segmentPrefix]
    rw [hpe]
    omega

/-- the prefix of the predecessor of eStar is strictly smaller -/
lemma segmentPrefix_predEdge_card_lt {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (h : 1 ≤ (ord eStar : ℕ)) :
    (segmentPrefix ord (predEdge ord eStar h)).card < (segmentPrefix ord eStar).card := by
  classical
  have hp := segmentPrefix_predEdge ord eStar h
  have hein : eStar ∈ segmentPrefix ord eStar := by rw [mem_segmentPrefix]
  have hcard : (segmentPrefix ord (predEdge ord eStar h)).card = (segmentPrefix ord eStar).card - 1 := by
    rw [hp]
    exact Finset.card_erase_of_mem hein
  have hpos : 0 < (segmentPrefix ord eStar).card := Finset.card_pos.mpr ⟨eStar, hein⟩
  rw [hcard]
  omega

/-- Block IV, minimality ⇒ the forward degree of eStar exceeds (1−τ)n
(else its predecessor is admissible with a strictly smaller prefix) -/
theorem fwddeg_gt_of_minimal {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (eStar : 𝓗) (hadm : AdmissiblePair τ ord eStar)
    (hrank : 1 ≤ (ord eStar : ℕ))
    (hmin : ∀ (k' : ℕ) (ord' : 𝓗 ≃ Fin k') (e' : 𝓗), AdmissiblePair τ ord' e' →
      (segmentPrefix ord eStar).card ≤ (segmentPrefix ord' e').card) :
    (1 - τ) * (n : ℝ) < (precedingDegree 𝓗 ord eStar : ℝ) := by
  by_contra hnot
  have hsmall : (precedingDegree 𝓗 ord eStar : ℝ) ≤ (1 - τ) * (n : ℝ) := le_of_not_gt hnot
  have hO1p : OrderingGoodness τ ord (predEdge ord eStar hrank) :=
    O1_of_pred ord τ eStar hrank hadm.1 hsmall
  have hO2p : OrderingBySize ord (predEdge ord eStar hrank) :=
    O2_of_pred ord eStar hrank hadm.2
  have hadmP : AdmissiblePair τ ord (predEdge ord eStar hrank) := ⟨hO1p, hO2p⟩
  have hlt := segmentPrefix_predEdge_card_lt ord eStar hrank
  have hle := hmin k ord (predEdge ord eStar hrank) hadmP
  omega

/-- **Block IV capstone for the minimal pair**: either the whole ordering
is good, or eStar sits at rank ≥ 1 with forward degree exceeding (1−τ)n
and the in-prefix-neighbour bound (6.3) `BlockIVStatement` holds. -/
theorem minimal_admissible_dichotomy {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (eStar : 𝓗) (hadm : AdmissiblePair τ ord eStar) (hτ : τ < 1)
    (hmin : ∀ (k' : ℕ) (ord' : 𝓗 ≃ Fin k') (e' : 𝓗), AdmissiblePair τ ord' e' →
      (segmentPrefix ord eStar).card ≤ (segmentPrefix ord' e').card) :
    GoodOrdering τ ord ∨
      ((1 ≤ (ord eStar : ℕ)) ∧
       (1 - τ) * (n : ℝ) < (precedingDegree 𝓗 ord eStar : ℝ) ∧
       BlockIVStatement τ ord eStar) := by
  classical
  by_cases hrank0 : (ord eStar : ℕ) = 0
  · left
    exact good_of_first_admissible ord τ eStar hrank0 hadm hτ
  · right
    have hrank : 1 ≤ (ord eStar : ℕ) := by omega
    exact ⟨hrank, fwddeg_gt_of_minimal ord τ eStar hadm hrank hmin,
      blockIV_of_minimal ord τ eStar hadm hmin⟩

/-- an admissible pair minimising the size of the prefix of eStar over all
admissible pairs (over all orderings, i.e. all equivalences to any Fin k') -/
theorem exists_minimal_admissible {n : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ)
    (hstart : ∃ (k : ℕ) (ord : 𝓗 ≃ Fin k) (eStar : 𝓗), AdmissiblePair τ ord eStar) :
    ∃ (k : ℕ) (ord : 𝓗 ≃ Fin k) (eStar : 𝓗),
      AdmissiblePair τ ord eStar ∧
      ∀ (k' : ℕ) (ord' : 𝓗 ≃ Fin k') (e' : 𝓗), AdmissiblePair τ ord' e' →
        (segmentPrefix ord eStar).card ≤ (segmentPrefix ord' e').card := by
  classical
  let P : ℕ → Prop := fun c => ∃ (k : ℕ) (ord : 𝓗 ≃ Fin k) (eStar : 𝓗),
    AdmissiblePair τ ord eStar ∧ (segmentPrefix ord eStar).card = c
  rcases hstart with ⟨k0, ord0, e0, hadm0⟩
  have hEx : ∃ c : ℕ, P c := ⟨(segmentPrefix ord0 e0).card, k0, ord0, e0, hadm0, rfl⟩
  let cmin : ℕ := Nat.find hEx
  have hPmin : P cmin := Nat.find_spec hEx
  have hmin : ∀ c : ℕ, P c → cmin ≤ c := by
    intro c hc
    by_contra hnot
    have hlt : c < cmin := by omega
    exact (Nat.find_min hEx hlt) hc
  rcases hPmin with ⟨k, ord, eStar, hadm, hcard⟩
  refine ⟨k, ord, eStar, hadm, ?_⟩
  intro k' ord' e' hadm'
  have hP' : P (segmentPrefix ord' e').card := ⟨k', ord', e', hadm', rfl⟩
  have hc : cmin ≤ (segmentPrefix ord' e').card := hmin _ hP'
  rwa [hcard.symm] at hc

/-- instance form: a finite nonempty hypergraph has a minimal admissible
pair (the size order provides the start pair) -/
theorem exists_minimal_admissible_of_fintype {n : ℕ} {𝓗 : Hypergraph (Fin n)}
    [Fintype 𝓗] [Nonempty 𝓗] (τ : ℝ) :
    ∃ (k : ℕ) (ord : 𝓗 ≃ Fin k) (eStar : 𝓗),
      AdmissiblePair τ ord eStar ∧
      ∀ (k' : ℕ) (ord' : 𝓗 ≃ Fin k') (e' : 𝓗), AdmissiblePair τ ord' e' →
        (segmentPrefix ord eStar).card ≤ (segmentPrefix ord' e').card := by
  classical
  let ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗) := Fintype.equivFin 𝓗
  exact exists_minimal_admissible τ ⟨Fintype.card 𝓗, sizeOrder ord₀, lastEdge (sizeOrder ord₀),
    sizeOrder_admissible_last ord₀ τ⟩

/-! ## Block V, part 1 (proved): the size-truncated neighbourhood X and (6.4)

Block V's vocabulary and first application of `fwdnbr_inequality2`:
`XSmall τ K ord eStar` is the paper's
`X := {e ∈ N^⪯(e*) : |e| ≤ (1+K√τ)·r}`, `r := |eStar|`
(`mem_XSmall`; subsets: `XSmall_subset_preceding` ⊆ `precedingNeighbours`,
`XSmall_subset_neighbourEdges`; sizes via (O2): `prefix_size_ge`,
`precedingNeighbour_size_ge`, `XSmall_size_ge`).  **Application 1**
(`blockV_boundNminusX`, the paper's far-bound): with
`F₁ := N^⪯(e*)∖X`, `F₂ := X` (a disjoint partition of `N^⪯(e*)`,
`blockV_X_from_partition`), the input `m₁+m₂ = d⪯(e*) ≥ (1−τ)n`, and
`α₁ := K√τ`, `α₂ := 0`, Prop `fwdnbr` (ii) gives
`|N^⪯(e*)∖X| ≤ (τ + 1/(r−1))·n/(K√τ)`.  The |X|-lower bounds follow:
`blockV_X_lower` (`|X| ≥ (1−τ)n − |N^⪯∖X|`) and, under the margin
`1 ≤ τ(r−1)` (`one_div_sub_one_le`, `boundNminusX_le`), the paper's
eq. (6.4) `blockV_X_bound`: `|X| ≥ (1−τ−2√τ/K)·n`.  Application 2
(`blockV_app2`, eq. (6.5), and its lemmas) is proved in the next section;
the (6.6)–(6.8) counting of Block VI assembles `WVolume` for
`VolumeSet`. -/

lemma precedingNeighbours_subset_neighbourEdges {k : ℕ} {𝓗 : Hypergraph (Fin n)}
    (ord : 𝓗 ≃ Fin k) (e : 𝓗) :
    precedingNeighbours 𝓗 ord e ⊆ neighbourEdges 𝓗 e := by
  classical
  intro f hf
  have hf' := (mem_precedingNeighbours 𝓗 ord e f).mp hf
  exact (mem_neighbourEdges 𝓗 e f).mpr ⟨hf'.1, hf'.2.2⟩

/-- an edge in the prefix of eStar has size at least that of eStar (O2) -/
lemma prefix_size_ge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (hO2 : OrderingBySize ord eStar) {f : 𝓗}
    (hf : f ∈ segmentPrefix ord eStar) :
    (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by
  classical
  have hle : (ord f : ℕ) ≤ (ord eStar : ℕ) := (mem_segmentPrefix ord eStar f).1 hf
  exact hO2 (e := eStar) (f := f) (by simpa using hle) le_rfl

/-- a preceding neighbour of eStar has size at least that of eStar (O2) -/
lemma precedingNeighbour_size_ge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar : 𝓗) (hO2 : OrderingBySize ord eStar) {f : 𝓗}
    (hf : f ∈ precedingNeighbours 𝓗 ord eStar) :
    (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by
  classical
  have hpfx : f ∈ segmentPrefix ord eStar := by
    rw [mem_segmentPrefix]
    have hf' := (mem_precedingNeighbours 𝓗 ord eStar f).mp hf
    have hle : (ord f : ℕ) ≤ (ord eStar : ℕ) := by simpa using hf'.2.1
    exact hle
  exact prefix_size_ge ord eStar hO2 hpfx

/-- **Block V vocabulary**: `X := {e ∈ N^⪯(e*) : |e| ≤ (1+K√τ)·r}`
(the size-truncated forward neighbours of eStar), `r := |eStar|` -/
def XSmall (τ : ℝ) (K : ℕ) {k : ℕ} {𝓗 : Hypergraph (Fin n)}
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) : Finset 𝓗 := by
  classical
  exact (precedingNeighbours 𝓗 ord eStar).filter (fun e : 𝓗 =>
    (edgeSize (e : Set (Fin n)) : ℝ) ≤
      (1 + (K : ℝ) * Real.sqrt τ) * (edgeSize (eStar : Set (Fin n)) : ℝ))

/-- membership in X -/
lemma mem_XSmall {τ : ℝ} {K : ℕ} {k : ℕ} {𝓗 : Hypergraph (Fin n)}
    (ord : 𝓗 ≃ Fin k) (eStar f : 𝓗) :
    f ∈ XSmall τ K ord eStar ↔
      f ∈ precedingNeighbours 𝓗 ord eStar ∧
      (edgeSize (f : Set (Fin n)) : ℝ) ≤
        (1 + (K : ℝ) * Real.sqrt τ) * (edgeSize (eStar : Set (Fin n)) : ℝ) := by
  classical
  simp [XSmall]

/-- X consists of preceding neighbours -/
lemma XSmall_subset_preceding {τ : ℝ} {K : ℕ} {k : ℕ} {𝓗 : Hypergraph (Fin n)}
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) :
    XSmall τ K ord eStar ⊆ precedingNeighbours 𝓗 ord eStar := by
  classical
  intro f hf
  exact ((mem_XSmall ord eStar f).mp hf).1

/-- X consists of neighbours of eStar -/
lemma XSmall_subset_neighbourEdges {τ : ℝ} {K : ℕ} {k : ℕ} {𝓗 : Hypergraph (Fin n)}
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) :
    XSmall τ K ord eStar ⊆ neighbourEdges 𝓗 eStar := by
  classical
  exact (XSmall_subset_preceding (τ := τ) (K := K) ord eStar).trans
    (precedingNeighbours_subset_neighbourEdges ord eStar)

/-- members of X have size at least |eStar| (O2) -/
lemma XSmall_size_ge {τ : ℝ} {K : ℕ} {k : ℕ} {𝓗 : Hypergraph (Fin n)}
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) (hO2 : OrderingBySize ord eStar) {f : 𝓗}
    (hf : f ∈ XSmall τ K ord eStar) :
    (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by
  classical
  exact precedingNeighbour_size_ge ord eStar hO2 ((mem_XSmall ord eStar f).mp hf).1

/-- **Block V, application 1 (paper (6.3)→far-bound)**: the part of
`N^⪯(e*)` outside `X` is small.  Formally: `m₁ := |N^⪯(e*)∖X|` satisfies
`m₁ ≤ (τ + 1/(r−1))·n/(K√τ)`, `r := |eStar|`, from `fwdnbr_inequality2`
with `α₁ := K√τ`, `α₂ := 0` (`F₁ := N^⪯∖X`, `F₂ := X`), the input
`m₁+m₂ ≥ (1−τ)n` being the forward degree of `eStar`. -/
theorem blockV_boundNminusX {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar : 𝓗)
    (hτ0 : 0 < τ) (hK : (1 : ℝ) ≤ K)
    (hO2 : OrderingBySize ord eStar)
    (hge2 : 2 ≤ edgeSize (eStar : Set (Fin n)))
    (hm : (1 - τ) * (n : ℝ) ≤ (precedingDegree 𝓗 ord eStar : ℝ)) :
    ((precedingNeighbours 𝓗 ord eStar \ XSmall τ K ord eStar).card : ℝ) ≤
      (τ + 1 / ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1)) * (n : ℝ) /
        ((K : ℝ) * Real.sqrt τ) := by
  classical
  let F₁ : Finset 𝓗 := precedingNeighbours 𝓗 ord eStar \ XSmall τ K ord eStar
  let F₂ : Finset 𝓗 := XSmall τ K ord eStar
  let r : ℝ := (edgeSize (eStar : Set (Fin n)) : ℝ)
  let α₁ : ℝ := (K : ℝ) * Real.sqrt τ
  have hK1 : (1 : ℕ) ≤ K := by exact_mod_cast hK
  have hα₁0 : 0 < α₁ := by
    dsimp [α₁]
    have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
    exact mul_pos hK0 hsq
  have hr : (1 : ℝ) < r := by
    dsimp [r]
    have h2 : (2 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) := by exact_mod_cast hge2
    linarith
  have hcond : (1 + (0 : ℝ)) < r := by simpa using hr
  -- F₁ ⊆ N(e*), F₂ ⊆ N(e*):
  have hF₁ : ∀ f ∈ F₁, f ∈ neighbourEdges 𝓗 eStar := by
    intro f hf
    dsimp [F₁] at hf
    exact (precedingNeighbours_subset_neighbourEdges ord eStar)
      ((Finset.mem_sdiff.mp hf).1)
  have hF₂ : ∀ f ∈ F₂, f ∈ neighbourEdges 𝓗 eStar := by
    intro f hf
    dsimp [F₂] at hf
    exact (XSmall_subset_neighbourEdges (τ := τ) (K := K) ord eStar) hf
  have hdisj : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro f hf₁ hf₂
    dsimp [F₁] at hf₁
    exact (Finset.mem_sdiff.mp hf₁).2 hf₂
  -- hbig on F₁: members have |f| > (1+K√τ)r hence ≥:
  have hbig : ∀ f ∈ F₁, ((1 + α₁) * r) ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by
    intro f hf
    dsimp [F₁] at hf
    have hfN : f ∈ precedingNeighbours 𝓗 ord eStar := (Finset.mem_sdiff.mp hf).1
    have hfnotX : f ∉ XSmall τ K ord eStar := (Finset.mem_sdiff.mp hf).2
    have hgt : (1 + α₁) * r < (edgeSize (f : Set (Fin n)) : ℝ) := by
      have hng : ¬ ((edgeSize (f : Set (Fin n)) : ℝ) ≤ (1 + α₁) * r) := by
        intro hs
        exact hfnotX ((mem_XSmall ord eStar f).mpr ⟨hfN, by simpa [α₁, r] using hs⟩)
      exact lt_of_not_ge hng
    exact le_of_lt hgt
  -- hmed on F₂ = X: r ≤ |f| by O2:
  have hmed : ∀ f ∈ F₂, r / (1 + (0 : ℝ)) ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by
    intro f hf
    dsimp [F₂] at hf
    have hge := XSmall_size_ge (τ := τ) (K := K) ord eStar hO2 hf
    simpa [r] using hge
  -- the union F₁∪F₂ is all of N^⪯:
  have hunion : F₁ ∪ F₂ = precedingNeighbours 𝓗 ord eStar := by
    ext f
    constructor
    · intro hf
      rcases (Finset.mem_union.mp hf) with hf₁ | hf₂
      · dsimp [F₁] at hf₁
        exact (Finset.mem_sdiff.mp hf₁).1
      · dsimp [F₂] at hf₂
        exact ((mem_XSmall ord eStar f).mp hf₂).1
    · intro hf
      rw [Finset.mem_union]
      by_cases hx : f ∈ F₂
      · exact Or.inr hx
      · left
        rw [Finset.mem_sdiff]
        dsimp [F₂] at hx
        exact ⟨hf, hx⟩
  have hcdN : (F₁ ∪ F₂).card = F₁.card + F₂.card := Finset.card_union_of_disjoint hdisj
  have hU : (F₁ ∪ F₂).card = precedingDegree 𝓗 ord eStar := by
    rw [precedingDegree, hunion]
  have hbigsum : (1 - τ) * (n : ℝ) ≤ (F₁.card : ℝ) + (F₂.card : ℝ) := by
    rw [← Nat.cast_add, ← hcdN, hU]
    exact hm
  have hI2 := fwdnbr_inequality2 (n := n) (𝓗 := 𝓗) hlin eStar α₁ (0 : ℝ) τ hα₁0
    (by norm_num : (0 : ℝ) ≤ (0 : ℝ)) F₁ F₂ hF₁ hF₂ hdisj hbig hmed hcond hbigsum
  dsimp [F₁] at hI2 ⊢
  simpa [α₁, r] using hI2

/-- |X| ≥ |N^⪯| − |N^⪯∖X| (partition of the forward neighbours) -/
lemma blockV_X_from_partition {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (K : ℕ) (eStar : 𝓗) :
    ((precedingDegree 𝓗 ord eStar : ℝ) -
        ((precedingNeighbours 𝓗 ord eStar \ XSmall τ K ord eStar).card : ℝ)) ≤
      ((XSmall τ K ord eStar).card : ℝ) := by
  classical
  let s : Finset 𝓗 := precedingNeighbours 𝓗 ord eStar
  let x : Finset 𝓗 := XSmall τ K ord eStar
  have hXsub : x ⊆ s := by
    dsimp [x, s]
    exact XSmall_subset_preceding (τ := τ) (K := K) ord eStar
  have hun : (s \ x) ∪ x = s := by
    ext f
    constructor
    · intro hf
      rcases (Finset.mem_union.mp hf) with hfsd | hfx
      · exact (Finset.mem_sdiff.mp hfsd).1
      · exact hXsub hfx
    · intro hfs
      rw [Finset.mem_union]
      by_cases hfx : f ∈ x
      · exact Or.inr hfx
      · exact Or.inl ((Finset.mem_sdiff.mpr ⟨hfs, hfx⟩))
  have hdisj : Disjoint (s \ x) x := by
    rw [Finset.disjoint_left]
    intro f hf hfx
    exact (Finset.mem_sdiff.mp hf).2 hfx
  have hsplit : s.card = (s \ x).card + x.card := by
    calc
      s.card = ((s \ x) ∪ x).card := (congrArg Finset.card hun).symm
      _ = (s \ x).card + x.card := Finset.card_union_of_disjoint hdisj
  have hreal : (s.card : ℝ) = ((s \ x).card : ℝ) + (x.card : ℝ) := by
    rw [hsplit, Nat.cast_add]
  have hpre : (precedingDegree 𝓗 ord eStar : ℝ) = (s.card : ℝ) := by
    dsimp [s]
    rw [precedingDegree]
  rw [hpre, hreal]
  linarith

/-- 1/(r−1) ≤ τ under the margin hypothesis 1 ≤ τ(r−1) -/
lemma one_div_sub_one_le {τ r : ℝ} (hr1 : 0 < r - 1)
    (hmar : (1 : ℝ) ≤ τ * (r - 1)) : 1 / (r - 1) ≤ τ := by
  exact (div_le_iff₀ hr1).mpr hmar

/-- (τ + 1/(r−1))·n/(K√τ) ≤ 2√τ·n/K under 1 ≤ τ(r−1) -/
lemma boundNminusX_le {τ : ℝ} {K : ℕ} {n : ℕ} (r : ℝ)
    (hτ0 : 0 < τ) (hK0 : (0 : ℝ) < K) (hr1 : 0 < r - 1)
    (hmar : (1 : ℝ) ≤ τ * (r - 1)) :
    (τ + 1 / (r - 1)) * (n : ℝ) / ((K : ℝ) * Real.sqrt τ) ≤
      2 * Real.sqrt τ * (n : ℝ) / (K : ℝ) := by
  let q : ℝ := 1 / (r - 1)
  have hfrac : q ≤ τ := by
    dsimp [q]
    exact one_div_sub_one_le hr1 hmar
  have hc : τ + q ≤ 2 * τ := by nlinarith
  have hsq : Real.sqrt τ * Real.sqrt τ = τ := by
    simpa [pow_two] using (Real.sq_sqrt (le_of_lt hτ0))
  have hτsqrt : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  have hden : 0 < (K : ℝ) * Real.sqrt τ := mul_pos hK0 hτsqrt
  have hposD : 0 < ((K : ℝ) * Real.sqrt τ) * (K : ℝ) := mul_pos hden hK0
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hnum : (τ + q) * (n : ℝ) ≤ 2 * τ * (n : ℝ) := mul_le_mul_of_nonneg_right hc hn
  change (τ + q) * (n : ℝ) / ((K : ℝ) * Real.sqrt τ) ≤
      2 * Real.sqrt τ * (n : ℝ) / (K : ℝ)
  apply le_of_mul_le_mul_right ?bc hposD
  field_simp [hden.ne', hK0.ne']
  nlinarith [hnum, hsq]
/-- |X| ≥ (1−τ)n − |N^⪯∖X| -/
lemma blockV_X_lower {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (K : ℕ) (eStar : 𝓗)
    (hm : (1 - τ) * (n : ℝ) ≤ (precedingDegree 𝓗 ord eStar : ℝ)) :
    ((1 - τ) * (n : ℝ) -
        ((precedingNeighbours 𝓗 ord eStar \ XSmall τ K ord eStar).card : ℝ)) ≤
      ((XSmall τ K ord eStar).card : ℝ) := by
  classical
  exact (sub_le_sub_right hm _).trans (blockV_X_from_partition ord τ K eStar)

/-- **Block V, eq. (6.4)**: under the size margin, |X| ≥ (1−τ−2√τ/K)·n -/
theorem blockV_X_bound {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar : 𝓗)
    (hτ0 : 0 < τ) (hK : (1 : ℝ) ≤ K)
    (hO2 : OrderingBySize ord eStar)
    (hge2 : 2 ≤ edgeSize (eStar : Set (Fin n)))
    (hmar : (1 : ℝ) ≤ τ * ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1))
    (hm : (1 - τ) * (n : ℝ) ≤ (precedingDegree 𝓗 ord eStar : ℝ)) :
    ((1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (n : ℝ)) ≤
      ((XSmall τ K ord eStar).card : ℝ) := by
  classical
  let r : ℝ := (edgeSize (eStar : Set (Fin n)) : ℝ)
  have hr1 : 0 < r - 1 := by
    dsimp [r]
    have h2 : (2 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) := by exact_mod_cast hge2
    nlinarith
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    have hK1 : (1 : ℕ) ≤ K := by exact_mod_cast hK
    exact_mod_cast (by omega : 0 < K)
  have hb := blockV_boundNminusX (𝓗 := 𝓗) hlin ord τ K eStar hτ0 hK hO2 hge2 hm
  have hb' : ((precedingNeighbours 𝓗 ord eStar \ XSmall τ K ord eStar).card : ℝ) ≤
      2 * Real.sqrt τ * (n : ℝ) / (K : ℝ) := by
    exact hb.trans (boundNminusX_le (edgeSize (eStar : Set (Fin n)) : ℝ) hτ0 hK0 hr1 hmar)
  have hlow := blockV_X_lower ord τ K eStar hm
  have hL : (1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (n : ℝ) =
      (1 - τ) * (n : ℝ) - 2 * Real.sqrt τ * (n : ℝ) / (K : ℝ) := by
    field_simp [hK0.ne']
  rw [hL]
  exact (sub_le_sub_left hb' ((1 - τ) * (n : ℝ))).trans hlow

/-! ## Block V, part 2 (proved): the outside-W bound (paper eq. (6.5))

**Application 2** of Prop `fwdnbr` inequality (ii): for each `e ∈ X` the
number of neighbours of `e` inside `H^{⪯e*}` but outside the volume set
`W = VolumeSet` is at most `6τ^{1/4}n/K`.  Proved here:

* τ^{1/4}-arithmetic (`tauQuarter` = √√τ): `tauQuarter_sq`, `tauQuarter_pow_four`,
  `tauQuarter_pos`, `tauQuarter_le_one`;
* the size-factor product comparison `sizeFactor_ge_product`
  (`(1+K³τ^{1/4})(1+K√τ) ≤ sizeFactor`, via `blockV_product`);
* the pure-algebra bound `blockV_app2_algebra` for the far-bound fraction;
* `outsideVolumeSet_subset_big` (members of `N(e)∩H^{⪯e*}∖W` satisfy
  `|f| ≥ (1+K³τ^{1/4})|e|`); and
* **`blockV_app2`** (eq. (6.5)) itself, instantiating `fwdnbr_inequality2`
  on `e` with `α₁ = K³τ^{1/4}`, `α₂ = K√τ` (in the form `K·(τ^{1/4})²`)
  under the explicit margins `1+K√τ ≤ |e|/2` and
  `2(1+K√τ) ≤ K²√τ·|e|` (the concrete instances of `1/r₁ ≪ τ, 1/K`).

Remaining Block V work: none — the (6.6)–(6.8) counting of Block VI
builds on `blockV_app2` and the |X|-bound `blockV_X_bound` of part 1. -/


/-- tauQuarter facts -/
lemma tauQuarter_sq (τ : ℝ) : (tauQuarter τ) ^ 2 = Real.sqrt τ := by
  unfold tauQuarter
  rw [Real.sq_sqrt (Real.sqrt_nonneg τ)]

lemma tauQuarter_nonneg (τ : ℝ) : 0 ≤ tauQuarter τ := by
  unfold tauQuarter
  positivity

lemma tauQuarter_pos {τ : ℝ} (hτ0 : 0 < τ) : 0 < tauQuarter τ := by
  unfold tauQuarter
  have h1 : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  positivity

lemma tauQuarter_pow_four {τ : ℝ} (hτ0 : 0 ≤ τ) : (tauQuarter τ) ^ 4 = τ := by
  unfold tauQuarter
  have h1 : Real.sqrt (Real.sqrt τ) * Real.sqrt (Real.sqrt τ) = Real.sqrt τ :=
    Real.mul_self_sqrt (Real.sqrt_nonneg τ)
  have h2 : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ0
  nlinarith [Real.sq_sqrt (Real.sqrt_nonneg τ), Real.sq_sqrt hτ0]

lemma tauQuarter_le_one {τ : ℝ} (hτ1 : τ ≤ 1) : tauQuarter τ ≤ 1 := by
  unfold tauQuarter
  have h1 : Real.sqrt τ ≤ 1 := by
    have hs := Real.sqrt_le_sqrt hτ1
    simpa using hs
  have h2 : Real.sqrt (Real.sqrt τ) ≤ 1 := by
    have hs := Real.sqrt_le_sqrt h1
    simpa using hs
  exact h2

/-- raw product bound in t: (1+K³t)(1+Kt²) ≤ 1+3K⁴t for 0 ≤ t ≤ 1, K ≥ 1 -/
lemma blockV_product (t K : ℝ) (hK : 1 ≤ K) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + K ^ 3 * t) * (1 + K * t ^ 2) ≤ 1 + 3 * t * K ^ 4 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hA : K ^ 3 * t ≤ K ^ 4 * t := by
    have hK34 : K ^ 3 ≤ K ^ 4 := by
      have hd : (0 : ℝ) ≤ K ^ 3 * (K - 1) := mul_nonneg (by positivity) (by linarith)
      nlinarith
    exact mul_le_mul_of_nonneg_right hK34 ht0
  have hB : K * t ^ 2 ≤ K ^ 4 * t := by
    have ht2le : t ^ 2 ≤ t := by
      have hd : (0 : ℝ) ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
      nlinarith
    have h1a : K * t ^ 2 ≤ K * t := mul_le_mul_of_nonneg_left ht2le hK0
    have hK4 : K ≤ K ^ 4 := by
      have h1 : (1 : ℝ) ≤ K ^ 3 := by
        have hd : (0 : ℝ) ≤ (K - 1) * (K ^ 2 + K + 1) := by
          have hsum : (0 : ℝ) ≤ K ^ 2 + K + 1 := by positivity
          exact mul_nonneg (by linarith) hsum
        nlinarith
      nlinarith
    have h1b : K * t ≤ K ^ 4 * t := mul_le_mul_of_nonneg_right hK4 ht0
    exact le_trans h1a h1b
  have hC : K ^ 4 * t ^ 3 ≤ K ^ 4 * t := by
    have ht3 : t ^ 3 ≤ t := by
      have htsq : t ^ 2 ≤ 1 := by
        have hd : (0 : ℝ) ≤ (1 - t) * (1 + t) := by
          have hsum : (0 : ℝ) ≤ 1 + t := by linarith
          exact mul_nonneg (by linarith) hsum
        nlinarith
      have hd : (0 : ℝ) ≤ t * (1 - t ^ 2) := mul_nonneg ht0 (by linarith)
      nlinarith
    exact mul_le_mul_of_nonneg_left ht3 (by positivity)
  nlinarith

/-- (1+K³τ^{1/4})(1+K√τ) ≤ sizeFactor τ K for 0 ≤ τ ≤ 1, K ≥ 1 -/
lemma sizeFactor_ge_product {τ : ℝ} {K : ℕ} (hτ1 : τ ≤ 1)
    (hK : (1 : ℝ) ≤ K) :
    (1 + (K : ℝ) ^ 3 * tauQuarter τ) * (1 + (K : ℝ) * Real.sqrt τ) ≤
      sizeFactor τ K := by
  unfold sizeFactor
  rw [← tauQuarter_sq τ]
  exact blockV_product (tauQuarter τ) (K : ℝ) hK (tauQuarter_nonneg τ)
    (tauQuarter_le_one (hτ1 := hτ1))

/-- **eq. (6.5) algebra**: under the size margins, the far-bound fraction is
at most `6τ^{1/4}n/K`.  Parameters: `s = |e|`, `t = τ^{1/4}`, real `K ≥ 1`. -/
lemma blockV_app2_algebra (K s t : ℝ) (n : ℝ)
    (hK1 : 1 ≤ K) (ht0 : 0 < t) (ht1 : t ≤ 1) (hn : 0 ≤ n)
    (hs1 : 1 + K * t ^ 2 ≤ s / 2)
    (hs2 : 2 * (1 + K * t ^ 2) ≤ K ^ 2 * t ^ 2 * s) :
    (t ^ 4 + (1 + K * t ^ 2) * (1 + K * t ^ 2 * s) / (s - 1 - K * t ^ 2)) * n /
        (K ^ 3 * t) ≤ 6 * t * n / K := by
  let A : ℝ := 1 + K * t ^ 2
  let B : ℝ := 1 + K * t ^ 2 * s
  let D : ℝ := s - 1 - K * t ^ 2
  have hK0 : (0 : ℝ) < K := by linarith
  have hspos : 0 < s := by
    have h1 : (0 : ℝ) < 1 + K * t ^ 2 := by positivity
    linarith
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    have : s / 2 ≤ s - 1 - K * t ^ 2 := by linarith [hs1]
    have hs2' : (0 : ℝ) < s / 2 := by linarith
    linarith
  have hD2 : s / 2 ≤ D := by
    dsimp [D]
    linarith [hs1]
  have ht4le : t ^ 4 ≤ K ^ 2 * t ^ 2 := by
    have hKsq1 : (1 : ℝ) ≤ K ^ 2 := by nlinarith [hK1]
    have ht4le2 : t ^ 4 ≤ t ^ 2 := by
      have ht2le1 : t ^ 2 ≤ 1 := by
        have hd : (0 : ℝ) ≤ (1 - t) * (1 + t) := by
          exact mul_nonneg (by linarith) (by linarith)
        nlinarith
      have hd : (0 : ℝ) ≤ t ^ 2 * (1 - t ^ 2) := mul_nonneg (sq_nonneg t) (by linarith)
      nlinarith
    nlinarith
  have hAB : 2 * A * B ≤ 5 * K ^ 2 * t ^ 2 * s := by
    have h1a : 2 * A ≤ K ^ 2 * t ^ 2 * s := by
      dsimp [A]
      exact hs2
    have h1b : 2 * A * (K * t ^ 2 * s) ≤ 4 * K ^ 2 * t ^ 2 * s := by
      have hA2 : 2 * A * (K * t ^ 2) ≤ 4 * K ^ 2 * t ^ 2 := by
        have hA2' : A ≤ 2 * K := by
          dsimp [A]
          have ht2le : t ^ 2 ≤ 1 := by
            have hd : (0 : ℝ) ≤ (1 - t) * (1 + t) := mul_nonneg (by linarith) (by linarith)
            nlinarith
          nlinarith
        have h1 : 0 ≤ K * t ^ 2 := by positivity
        calc
          2 * A * (K * t ^ 2) ≤ 2 * (2 * K) * (K * t ^ 2) := by
            gcongr
          _ = 4 * K ^ 2 * t ^ 2 := by ring
      have hsnon : (0 : ℝ) ≤ s := le_of_lt hspos
      nlinarith
    dsimp [B]
    nlinarith
  have hQ : A * B ≤ 5 * K ^ 2 * t ^ 2 * D := by
    have hDbig : s / 2 ≤ D := hD2
    have hgoal1 : A * B * 2 ≤ 5 * K ^ 2 * t ^ 2 * s := by nlinarith [hAB]
    have hs2D : s ≤ 2 * D := by nlinarith [hDbig]
    have h2 : 5 * K ^ 2 * t ^ 2 * s ≤ 5 * K ^ 2 * t ^ 2 * (2 * D) := by
      have hnon : (0 : ℝ) ≤ 5 * K ^ 2 * t ^ 2 := by positivity
      nlinarith
    nlinarith
  have hmain : t ^ 4 + A * B / D ≤ 6 * K ^ 2 * t ^ 2 := by
    have hconv : (t ^ 4 + A * B / D) * D = t ^ 4 * D + A * B := by
      field_simp [hD.ne']
    have hR : (t ^ 4 * D + A * B) ≤ 6 * K ^ 2 * t ^ 2 * D := by
      have h1 : t ^ 4 * D ≤ K ^ 2 * t ^ 2 * D := by
        exact mul_le_mul_of_nonneg_right ht4le (le_of_lt hD)
      have h2 : A * B ≤ 5 * K ^ 2 * t ^ 2 * D := hQ
      nlinarith
    apply le_of_mul_le_mul_right _ hD
    calc
      (t ^ 4 + A * B / D) * D = t ^ 4 * D + A * B := hconv
      _ ≤ 6 * K ^ 2 * t ^ 2 * D := hR
  have hmainN : (t ^ 4 + A * B / D) * n ≤ 6 * K ^ 2 * t ^ 2 * n := by
    exact mul_le_mul_of_nonneg_right hmain hn
  rw [div_le_iff₀ (by positivity : 0 < K ^ 3 * t)]
  calc
    (t ^ 4 + A * B / D) * n ≤ 6 * K ^ 2 * t ^ 2 * n := hmainN
    _ = (6 * t * n / K) * (K ^ 3 * t) := by
      field_simp [hK0.ne']

/-- edges outside the volume set are big neighbours of e: (6.5)'s F₁
contains `(N(e)∩H^{⪯e*})∖W` -/
lemma outsideVolumeSet_subset_big {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (K : ℕ) (eStar e : 𝓗)
    (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K)
    (hX : e ∈ XSmall τ K ord eStar) {f : 𝓗}
    (hf : f ∈ nbrsInPrefix ord eStar e \ VolumeSet τ K ord eStar) :
    f ∈ (nbrsInPrefix ord eStar e).filter (fun g : 𝓗 =>
      (1 + (K : ℝ) ^ 3 * tauQuarter τ) * (edgeSize (e : Set (Fin n)) : ℝ) ≤
        (edgeSize (g : Set (Fin n)) : ℝ)) := by
  classical
  rw [Finset.mem_filter]
  constructor
  · exact (Finset.mem_sdiff.mp hf).1
  let r : ℝ := (edgeSize (eStar : Set (Fin n)) : ℝ)
  let s : ℝ := (edgeSize (e : Set (Fin n)) : ℝ)
  have hfN : f ∈ nbrsInPrefix ord eStar e := (Finset.mem_sdiff.mp hf).1
  have hfW : f ∉ VolumeSet τ K ord eStar := (Finset.mem_sdiff.mp hf).2
  have hfrank : (ord f : ℕ) ≤ (ord eStar : ℕ) := (mem_nbrsInPrefix ord eStar e f).mp hfN |>.2
  have hfseg : f ∈ segmentPrefix ord eStar := (mem_segmentPrefix ord eStar f).mpr hfrank
  have hfWgt : sizeFactor τ K * r < (edgeSize (f : Set (Fin n)) : ℝ) := by
    have hng : ¬ ((edgeSize (f : Set (Fin n)) : ℝ) ≤ sizeFactor τ K * r) := by
      intro hle
      exact hfW ((mem_VolumeSet τ K ord eStar f).mpr ⟨hfrank, by simpa [r] using hle⟩)
    exact lt_of_not_ge hng
  have hs_le : s ≤ (1 + (K : ℝ) * Real.sqrt τ) * r := by
    dsimp [s, r]
    exact ((mem_XSmall ord eStar e).mp hX).2
  have hprod : (1 + (K : ℝ) ^ 3 * tauQuarter τ) * s ≤ sizeFactor τ K * r := by
    have hnon : (0 : ℝ) ≤ 1 + (K : ℝ) ^ 3 * tauQuarter τ := by
      have hK0' : (0 : ℝ) ≤ K := by linarith
      have htq0 : (0 : ℝ) ≤ tauQuarter τ := tauQuarter_nonneg τ
      positivity
    have hsq : (0 : ℝ) ≤ Real.sqrt τ := Real.sqrt_nonneg τ
    have hstep : (1 + (K : ℝ) ^ 3 * tauQuarter τ) * s ≤
        (1 + (K : ℝ) ^ 3 * tauQuarter τ) * ((1 + (K : ℝ) * Real.sqrt τ) * r) :=
      mul_le_mul_of_nonneg_left hs_le hnon
    have hc : (1 + (K : ℝ) ^ 3 * tauQuarter τ) * ((1 + (K : ℝ) * Real.sqrt τ) * r) =
        ((1 + (K : ℝ) ^ 3 * tauQuarter τ) * (1 + (K : ℝ) * Real.sqrt τ)) * r := by ring
    rw [hc] at hstep
    have hr0 : (0 : ℝ) ≤ r := by
      dsimp [r]
      exact Nat.cast_nonneg _
    exact hstep.trans (mul_le_mul_of_nonneg_right (sizeFactor_ge_product hτ1 hK) hr0)
  have hfinal : (1 + (K : ℝ) ^ 3 * tauQuarter τ) * s ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by
    exact le_trans hprod (le_of_lt hfWgt)
  simpa [s] using hfinal


/-- **Block V, application 2 (paper eq. (6.5))**: for `e ∈ X` the part of
`N(e)∩H^{⪯e*}` outside the volume set `W` is small:
`|(N(e)∩H^{⪯e*})∖W| ≤ 6τ^{1/4}n/K`.  Inputs: `hm` is the eq. (6.3) bound
`(1−τ)n ≤ |N(e)∩H^{⪯e*}|`; the margins `hm1` (`1+K√τ ≤ |e|/2`) and `hm2`
(`2(1+K√τ) ≤ K²√τ·|e|`) are the concrete instances of the paper's
`1/r₁ ≪ τ, 1/K`. -/
theorem blockV_app2 {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar e : 𝓗)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K)
    (hge2 : 2 ≤ edgeSize (e : Set (Fin n)))
    (hm1 : 1 + (K : ℝ) * Real.sqrt τ ≤
      (edgeSize (e : Set (Fin n)) : ℝ) / 2)
    (hm2 : 2 * (1 + (K : ℝ) * Real.sqrt τ) ≤
      (K : ℝ) ^ 2 * Real.sqrt τ * (edgeSize (e : Set (Fin n)) : ℝ))
    (hO2 : OrderingBySize ord eStar)
    (hX : e ∈ XSmall τ K ord eStar)
    (hm : (1 - τ) * (n : ℝ) ≤ ((nbrsInPrefix ord eStar e).card : ℝ)) :
    (((nbrsInPrefix ord eStar e) \ (VolumeSet τ K ord eStar)).card : ℝ) ≤
      6 * tauQuarter τ * (n : ℝ) / (K : ℝ) := by
  classical
  let α₁ : ℝ := (K : ℝ) ^ 3 * tauQuarter τ
  let α₂ : ℝ := (K : ℝ) * (tauQuarter τ) ^ 2
  let p : 𝓗 → Prop := fun f : 𝓗 =>
    (1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ)
  let F₁ : Finset 𝓗 := (nbrsInPrefix ord eStar e).filter p
  let F₂ : Finset 𝓗 := (nbrsInPrefix ord eStar e).filter (fun f : 𝓗 => ¬ p f)
  have hτ0' : 0 ≤ τ := le_of_lt hτ0
  -- margins rewritten in τ^{1/4}-form:
  have hm1t : 1 + (K : ℝ) * (tauQuarter τ) ^ 2 ≤
      (edgeSize (e : Set (Fin n)) : ℝ) / 2 := by
    rw [← tauQuarter_sq τ] at hm1
    exact hm1
  have hm2t : 2 * (1 + (K : ℝ) * (tauQuarter τ) ^ 2) ≤
      (K : ℝ) ^ 2 * (tauQuarter τ) ^ 2 * (edgeSize (e : Set (Fin n)) : ℝ) := by
    rw [← tauQuarter_sq τ] at hm2
    exact hm2
  have hmt : (1 - (tauQuarter τ) ^ 4) * (n : ℝ) ≤ ((nbrsInPrefix ord eStar e).card : ℝ) := by
    rw [← tauQuarter_pow_four hτ0'] at hm
    exact hm
  have hXb : (edgeSize (e : Set (Fin n)) : ℝ) ≤
      (1 + (K : ℝ) * (tauQuarter τ) ^ 2) * (edgeSize (eStar : Set (Fin n)) : ℝ) := by
    have hx := ((mem_XSmall ord eStar e).mp hX).2
    rw [← tauQuarter_sq τ] at hx
    exact hx
  have hpos1 : 0 < 1 + α₂ := by
    dsimp [α₂]
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := by linarith
    positivity
  have hcond : (1 + α₂) < (edgeSize (e : Set (Fin n)) : ℝ) := by
    dsimp [α₂]
    have h2 : (2 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by exact_mod_cast hge2
    linarith [hm1t]
  have hα₁0 : 0 < α₁ := by
    dsimp [α₁]
    have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
    exact mul_pos (by positivity) (tauQuarter_pos hτ0)
  have hα₂0 : 0 ≤ α₂ := by
    dsimp [α₂]
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := by linarith
    positivity
  -- F₁ ⊆ N(e), F₂ ⊆ N(e):
  have hF₁N : ∀ f ∈ F₁, f ∈ neighbourEdges 𝓗 e := by
    intro f hf
    exact (mem_nbrsInPrefix ord eStar e f).mp (Finset.mem_filter.mp hf).1 |>.1
  have hF₂N : ∀ f ∈ F₂, f ∈ neighbourEdges 𝓗 e := by
    intro f hf
    exact (mem_nbrsInPrefix ord eStar e f).mp (Finset.mem_filter.mp hf).1 |>.1
  have hdisj : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro f hf₁ hf₂
    exact (Finset.mem_filter.mp hf₂).2 (Finset.mem_filter.mp hf₁).2
  have hunion : F₁ ∪ F₂ = nbrsInPrefix ord eStar e := by
    ext f
    constructor
    · intro hf
      rcases (Finset.mem_union.mp hf) with h₁ | h₂
      · exact (Finset.mem_filter.mp h₁).1
      · exact (Finset.mem_filter.mp h₂).1
    · intro hf
      rw [Finset.mem_union]
      by_cases hp : p f
      · left
        exact Finset.mem_filter.mpr ⟨hf, hp⟩
      · right
        exact Finset.mem_filter.mpr ⟨hf, hp⟩
  have hsum : (F₁.card : ℝ) + (F₂.card : ℝ) = ((nbrsInPrefix ord eStar e).card : ℝ) := by
    have hc : (F₁ ∪ F₂).card = F₁.card + F₂.card := Finset.card_union_of_disjoint hdisj
    calc
      (F₁.card : ℝ) + (F₂.card : ℝ) = ((F₁ ∪ F₂).card : ℝ) := by
        rw [hc]
        norm_num
      _ = ((nbrsInPrefix ord eStar e).card : ℝ) := by rw [hunion]
  have hbigsum : (1 - (tauQuarter τ) ^ 4) * (n : ℝ) ≤ (F₁.card : ℝ) + (F₂.card : ℝ) := by
    rw [hsum]
    exact hmt
  have hbig : ∀ f ∈ F₁, ((1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ)) ≤
      (edgeSize (f : Set (Fin n)) : ℝ) := by
    intro f hf
    exact (Finset.mem_filter.mp hf).2
  -- hmed on F₂: |e|/(1+α₂) ≤ |f| via (O2) and e ∈ X:
  have hmed : ∀ f ∈ F₂, ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂)) ≤
      (edgeSize (f : Set (Fin n)) : ℝ) := by
    intro f hf
    have hfN : f ∈ nbrsInPrefix ord eStar e := (Finset.mem_filter.mp hf).1
    have hfrank : (ord f : ℕ) ≤ (ord eStar : ℕ) := (mem_nbrsInPrefix ord eStar e f).mp hfN |>.2
    have hfseg : f ∈ segmentPrefix ord eStar := (mem_segmentPrefix ord eStar f).mpr hfrank
    have hgeR := prefix_size_ge ord eStar hO2 (f := f) hfseg
    have hdiv : (edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂) ≤
        (edgeSize (eStar : Set (Fin n)) : ℝ) := by
      dsimp [α₂]
      rw [div_le_iff₀ hpos1]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hXb
    exact hdiv.trans hgeR
  have hI2 := fwdnbr_inequality2 (n := n) (𝓗 := 𝓗) hlin e α₁ α₂ ((tauQuarter τ) ^ 4)
    hα₁0 hα₂0 F₁ F₂ hF₁N hF₂N hdisj hbig hmed hcond hbigsum
  -- hI2 is already in τ^{1/4}-form; chain with the algebra lemma:
  have hI2' : (F₁.card : ℝ) ≤
      ((tauQuarter τ) ^ 4 + (1 + (K : ℝ) * (tauQuarter τ) ^ 2) *
        (1 + (K : ℝ) * (tauQuarter τ) ^ 2 * (edgeSize (e : Set (Fin n)) : ℝ)) /
        ((edgeSize (e : Set (Fin n)) : ℝ) - 1 - (K : ℝ) * (tauQuarter τ) ^ 2)) *
        (n : ℝ) / ((K : ℝ) ^ 3 * tauQuarter τ) := by
    simpa [α₁, α₂] using hI2
  have halg := blockV_app2_algebra (K := (K : ℝ)) (s := (edgeSize (e : Set (Fin n)) : ℝ))
    (t := tauQuarter τ) ((n : ℝ)) hK (tauQuarter_pos hτ0) (tauQuarter_le_one hτ1)
    (by positivity) hm1t hm2t
  have hfinal : (F₁.card : ℝ) ≤ 6 * tauQuarter τ * (n : ℝ) / (K : ℝ) := by
    exact hI2'.trans halg
  -- card bound: (X∖W) ⊆ F₁:
  have hsub : nbrsInPrefix ord eStar e \ VolumeSet τ K ord eStar ⊆ F₁ := by
    intro f hf
    have hmem := outsideVolumeSet_subset_big ord τ K eStar e hτ1 hK hX hf
    -- hmem is membership in the raw-filter; convert to p-form:
    rw [Finset.mem_filter] at hmem ⊢
    dsimp [p, α₁] at hmem ⊢
    exact ⟨hmem.1, hmem.2⟩
  have hcard : (((nbrsInPrefix ord eStar e) \ (VolumeSet τ K ord eStar)).card : ℝ) ≤
      (F₁.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub)
  exact hcard.trans hfinal

/-! ## Block VI, part 1 (proved): counting (i) — few common neighbours of
two disjoint edges (paper eq. (6.8))

**Convention note (critical).**  The paper's sets `W := {f ⪯ e* : |f| ≤ A·r}`
and `H^{⪯e*}` are inclusive of `e*` (our `VolumeSet`/`segmentPrefix`), but
the counting in the proof of (6.6)–(6.8) only works when `W∖N(e*)` is read
as the *self-inclusive* neighbourhood of `e*` (`N⁺(e*) := N(e*) ∪ {e*}`),
i.e. `B := {f ∈ W : f ∩ e* = ∅}` = `W` minus `N(e*)` minus `{e*}`.  With
the *exclusive* `N(e*)` (our `neighbourEdges`) the set `W∖N(e*)` would
contain `e*`, whose term `|N(e*)∩X| = |X|` is not bounded by `A·r²`; the
paper's proof instead counts pairs `(e, f)`, `f ∈ B`.  Consequently Block
VI uses `B := W.filter (disjoint from e*)` and incurs one extra `−1` per
`e ∈ X` in (6.6) (the `e* ∈ N(e)∩H^{⪯e*}` element, which is *not* in `B`),
absorbed by the explicit margin `(A−1−K√τ)·r² ≥ 1` at assembly.

**Proved here:** `card_commonNeighbours_disjoint_le` — for disjoint edges
`f`, `g` of a linear hypergraph, `|N(f) ∩ N(g)| ≤ |f|·|g|` (each common
neighbour is determined by the pair (its vertex on `f`, its vertex on `g`)).
This is the `|N(f)∩N(e*)| ≤ |f||e*|` estimate of eq. (6.8), valid for
`f ∈ B` (so `f ∩ e* = ∅`).  Remaining Block VI: (a) the
`|N(e)∩fwdnbr(e*)|` bound of eq. (6.7) via the `N₁`/`N₂` split
(`|N₁| ≤ n/(r−1)` by pairwise-disjoint leftovers of the `f ∈ N₁`
sharing `e∩e*`; `|N₂| ≤ (|e|−1)(|e*|−1)` by the injection `f ↦
(f∩e-vertex, f∩e*-vertex)` into `(e∖{v}) × (e*∖{v})`); (b) eq. (6.6)
per-`e` lower bound on `|N(e)∩B|` (uses (6.3), (6.5), (6.7), margins
`t(r−1) ≥ K`); (c) the double count via the commons
`Finset.sum_card_filter_comm`; (d) the `|B|`/`|W|` lower bounds and (e)
the (W2) volume chain (margins: `q > 0`, `(A−1−K√τ)r² ≥ 1`,
`(1−τ−2√τ/K)(1−1/r) ≥ q`, `2 ≤ n`). -/

/-- **Block VI counting (i)** (paper eq. (6.8)): if two edges `f`, `g` of a
linear hypergraph are disjoint, then they have at most `|f|·|g|` common
neighbours.  Indeed each common neighbour `h` is determined by the pair
(its common vertex with `f`, its common vertex with `g`). -/
theorem card_commonNeighbours_disjoint_le {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) {f g : 𝓗}
    (hdisj : Disjoint (f : Set (Fin n)) (g : Set (Fin n))) :
    (neighbourEdges 𝓗 f ∩ neighbourEdges 𝓗 g).card ≤
      edgeSize (f : Set (Fin n)) * edgeSize (g : Set (Fin n)) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  let S : Finset 𝓗 := neighbourEdges 𝓗 f ∩ neighbourEdges 𝓗 g
  let T : Finset (Fin n × Fin n) := (verts (f : Set (Fin n))) ×ˢ (verts (g : Set (Fin n)))
  -- common vertices with f and g (defaulting to 0 outside S)
  let u : 𝓗 → Fin n := fun h =>
    if hh : ((h : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty then commonVertex hh else 0
  let v : 𝓗 → Fin n := fun h =>
    if hh : ((h : Set (Fin n)) ∩ (g : Set (Fin n))).Nonempty then commonVertex hh else 0
  let φ : 𝓗 → Fin n × Fin n := fun h => (u h, v h)
  have hφinj : Set.InjOn φ (S : Set 𝓗) := by
    intro h₁ h₁S h₂ h₂S hEq
    have hf₁S : h₁ ∈ neighbourEdges 𝓗 f := (Finset.mem_inter.mp h₁S).1
    have hf₂S : h₂ ∈ neighbourEdges 𝓗 f := (Finset.mem_inter.mp h₂S).1
    have hg₁S : h₁ ∈ neighbourEdges 𝓗 g := (Finset.mem_inter.mp h₁S).2
    have hg₂S : h₂ ∈ neighbourEdges 𝓗 g := (Finset.mem_inter.mp h₂S).2
    have hf₁N := (mem_neighbourEdges 𝓗 f h₁).mp hf₁S
    have hf₂N := (mem_neighbourEdges 𝓗 f h₂).mp hf₂S
    have hg₁N := (mem_neighbourEdges 𝓗 g h₁).mp hg₁S
    have hg₂N := (mem_neighbourEdges 𝓗 g h₂).mp hg₂S
    have hintf₁ : ((h₁ : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty := hf₁N.2
    have hintf₂ : ((h₂ : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty := hf₂N.2
    have hintg₁ : ((h₁ : Set (Fin n)) ∩ (g : Set (Fin n))).Nonempty := hg₁N.2
    have hintg₂ : ((h₂ : Set (Fin n)) ∩ (g : Set (Fin n))).Nonempty := hg₂N.2
    have hu₁ : u h₁ = commonVertex hintf₁ := by simp [u, hintf₁]
    have hu₂ : u h₂ = commonVertex hintf₂ := by simp [u, hintf₂]
    have hv₁ : v h₁ = commonVertex hintg₁ := by simp [v, hintg₁]
    have hv₂ : v h₂ = commonVertex hintg₂ := by simp [v, hintg₂]
    have hpair := congrArg Prod.fst hEq
    have hpair2 := congrArg Prod.snd hEq
    have hvf : commonVertex hintf₁ = commonVertex hintf₂ := by
      simpa [φ, hu₁, hu₂] using hpair
    have hvg : commonVertex hintg₁ = commonVertex hintg₂ := by
      simpa [φ, hv₁, hv₂] using hpair2
    -- memberships
    have hvf₁h₁ : commonVertex hintf₁ ∈ (h₁ : Set (Fin n)) :=
      commonVertex_mem_left hintf₁
    have hvf₁f : commonVertex hintf₁ ∈ (f : Set (Fin n)) :=
      commonVertex_mem_right hintf₁
    have hvf₂h₂ : commonVertex hintf₂ ∈ (h₂ : Set (Fin n)) :=
      commonVertex_mem_left hintf₂
    have hvg₁h₁ : commonVertex hintg₁ ∈ (h₁ : Set (Fin n)) :=
      commonVertex_mem_left hintg₁
    have hvg₁g : commonVertex hintg₁ ∈ (g : Set (Fin n)) :=
      commonVertex_mem_right hintg₁
    have hvg₂h₂ : commonVertex hintg₂ ∈ (h₂ : Set (Fin n)) :=
      commonVertex_mem_left hintg₂
    have hne : commonVertex hintf₁ ≠ commonVertex hintg₁ := by
      intro hEqv
      have : commonVertex hintf₁ ∈ (g : Set (Fin n)) := by simpa [hEqv] using hvg₁g
      exact hdisj.le_bot ⟨hvf₁f, this⟩
    -- common vertices of h₁ are shared by h₂ (equal pairs)
    have h₂vf : commonVertex hintf₁ ∈ (h₂ : Set (Fin n)) := by simpa [hvf] using hvf₂h₂
    have h₂vg : commonVertex hintg₁ ∈ (h₂ : Set (Fin n)) := by simpa [hvg] using hvg₂h₂
    apply Subtype.ext
    exact IsLinear.eq_of_mem_pair (𝓗 := 𝓗) hlin h₁.2 h₂.2 hne hvf₁h₁ hvg₁h₁ h₂vf h₂vg
  have hφsub : S.image φ ⊆ T := by
    intro p hp
    rcases (Finset.mem_image.mp hp) with ⟨h, hhS, rfl⟩
    rw [Finset.mem_product]
    have hfS : h ∈ neighbourEdges 𝓗 f := (Finset.mem_inter.mp hhS).1
    have hfN := (mem_neighbourEdges 𝓗 f h).mp hfS
    have hintf : ((h : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty := hfN.2
    have hu : u h = commonVertex hintf := by simp [u, hintf]
    have hgS : h ∈ neighbourEdges 𝓗 g := (Finset.mem_inter.mp hhS).2
    have hgN := (mem_neighbourEdges 𝓗 g h).mp hgS
    have hintg : ((h : Set (Fin n)) ∩ (g : Set (Fin n))).Nonempty := hgN.2
    have hv : v h = commonVertex hintg := by simp [v, hintg]
    constructor
    · dsimp [φ]
      rw [hu]
      simp [verts]
      exact commonVertex_mem_right hintf
    · dsimp [φ]
      rw [hv]
      simp [verts]
      exact commonVertex_mem_right hintg
  have hcardφ : S.card = (S.image φ).card := by
    exact (Finset.card_image_of_injOn hφinj).symm
  have hcard : S.card ≤ T.card := by
    calc
      S.card = (S.image φ).card := hcardφ
      _ ≤ T.card := Finset.card_le_card hφsub
  have hcardT : T.card = edgeSize (f : Set (Fin n)) * edgeSize (g : Set (Fin n)) := by
    dsimp [T, edgeSize]
    rw [Finset.card_product]
  exact hcard.trans (le_of_eq hcardT)

/-! ## Block VI, part 2, step 1 (proved): the N₁/N₂ partition and the N₂
bound of eq. (6.7)

Vocabulary of the `|N(e)∩fwdnbr(e*)|` bound: `fwdnbrNbrs ord eStar e :=
N(e) ∩ fwdnbr(e*)` (the common part of the two neighbourhoods);
`blockVIN₁` (`N₁`: members of `N(e)∩fwdnbr(e*)` that meet `eStar` in the
same vertex as `e`, i.e. `f∩e* = e∩e*`) and `blockVIN₂` (`N₂`: the rest).
Proved: the disjoint partition `N₁ ∪ N₂ = N(e)∩fwdnbr(e*)`
(`blockVIN₁_disjoint_N₂`, `blockVIN₁_union_N₂`, `blockVIfwdnbr_card`), and
the **N₂ bound** `blockVI_N₂_bound`: `|N₂| ≤ (|e|−1)(|e*|−1)` — for
`e ∈ fwdnbr(e*)` with common vertex `v := e∩e*`, every `f ∈ N₂` meets `e`
in `u_f` and `eStar` in `w_f` with `u_f, w_f ≠ v` (else `f∩e* = e∩e*` and
`f ∈ N₁`), and `f ↦ (u_f, w_f)` is injective into
`(e∖{v}) × (e*∖{v})` by `IsLinear.eq_of_mem_pair`.  Completed in this
block: the **N₁ bound** `blockVI_N₁_bound` (`|N₁| ≤ n/(r−1)`: members of
`N₁` share the vertex `v`, all have size `≥ r` by (O2), so their leftovers
`(verts f).erase v` form a pairwise disjoint family of subsets of the other
`n−1` vertices, summed via `Finset.disjiUnion`), and the real combination
**eq. (6.7) `blockVI_fwdnbrNbrs_le`**:
`|N(e)∩fwdnbr(e*)| ≤ n/(r−1) + (|e|−1)(|e*|−1)`. -/

/-- `N(e) ∩ fwdnbr(e*)`: the neighbours of `e` that precede and intersect
`eStar` (elements `f` with `f ∈ N(e)` and `f ∈ fwdnbr(e*)`). -/
noncomputable def fwdnbrNbrs {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) : Finset 𝓗 :=
  neighbourEdges 𝓗 e ∩ precedingNeighbours 𝓗 ord eStar

/-- membership in `fwdnbrNbrs` -/
lemma mem_fwdnbrNbrs {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e f : 𝓗) :
    f ∈ fwdnbrNbrs ord eStar e ↔
      f ∈ neighbourEdges 𝓗 e ∧ f ∈ precedingNeighbours 𝓗 ord eStar := by
  classical
  rw [fwdnbrNbrs, Finset.mem_inter]

/-- **N₁** (paper eq. (6.7)): the common neighbours of `e` and `eStar` in
`fwdnbr(e*)` that meet `eStar` in the same vertex as `e`. -/
noncomputable def blockVIN₁ {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) : Finset 𝓗 := by
  classical
  exact (fwdnbrNbrs ord eStar e).filter (fun f : 𝓗 =>
    (f : Set (Fin n)) ∩ (eStar : Set (Fin n)) = (e : Set (Fin n)) ∩ (eStar : Set (Fin n)))

/-- **N₂** (paper eq. (6.7)): the complement of N₁ inside `N(e)∩fwdnbr(e*)`. -/
noncomputable def blockVIN₂ {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) : Finset 𝓗 := by
  classical
  exact (fwdnbrNbrs ord eStar e).filter (fun f : 𝓗 =>
    ¬ ((f : Set (Fin n)) ∩ (eStar : Set (Fin n)) = (e : Set (Fin n)) ∩ (eStar : Set (Fin n))))

/-- membership in N₁ -/
lemma mem_blockVIN₁ {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e f : 𝓗) :
    f ∈ blockVIN₁ ord eStar e ↔ f ∈ fwdnbrNbrs ord eStar e ∧
      (f : Set (Fin n)) ∩ (eStar : Set (Fin n)) = (e : Set (Fin n)) ∩ (eStar : Set (Fin n)) := by
  classical
  simp [blockVIN₁]

/-- membership in N₂ -/
lemma mem_blockVIN₂ {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e f : 𝓗) :
    f ∈ blockVIN₂ ord eStar e ↔ f ∈ fwdnbrNbrs ord eStar e ∧
      ¬ (f : Set (Fin n)) ∩ (eStar : Set (Fin n)) = (e : Set (Fin n)) ∩ (eStar : Set (Fin n)) := by
  classical
  simp [blockVIN₂]

/-- N₁ and N₂ are disjoint. -/
lemma blockVIN₁_disjoint_N₂ {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) : Disjoint (blockVIN₁ ord eStar e) (blockVIN₂ ord eStar e) := by
  rw [Finset.disjoint_left]
  intro f hf₁ hf₂
  exact ((mem_blockVIN₂ ord eStar e f).mp hf₂).2 ((mem_blockVIN₁ ord eStar e f).mp hf₁).2

/-- N₁ ∪ N₂ = N(e)∩fwdnbr(e*) (the partition of eq. (6.7)). -/
lemma blockVIN₁_union_N₂ {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) : blockVIN₁ ord eStar e ∪ blockVIN₂ ord eStar e = fwdnbrNbrs ord eStar e := by
  classical
  ext f
  constructor
  · intro hf
    rcases (Finset.mem_union.mp hf) with h₁ | h₂
    · exact (mem_blockVIN₁ ord eStar e f).mp h₁ |>.1
    · exact (mem_blockVIN₂ ord eStar e f).mp h₂ |>.1
  · intro hf
    rw [Finset.mem_union]
    by_cases hEq : (f : Set (Fin n)) ∩ (eStar : Set (Fin n)) = (e : Set (Fin n)) ∩ (eStar : Set (Fin n))
    · left
      exact (mem_blockVIN₁ ord eStar e f).mpr ⟨hf, hEq⟩
    · right
      exact (mem_blockVIN₂ ord eStar e f).mpr ⟨hf, hEq⟩

/-- `|N(e)∩fwdnbr(e*)| = |N₁| + |N₂|`. -/
lemma blockVIfwdnbr_card {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (eStar e : 𝓗) :
    (fwdnbrNbrs ord eStar e).card = (blockVIN₁ ord eStar e).card + (blockVIN₂ ord eStar e).card := by
  classical
  have hc : (blockVIN₁ ord eStar e ∪ blockVIN₂ ord eStar e).card =
      (blockVIN₁ ord eStar e).card + (blockVIN₂ ord eStar e).card :=
    Finset.card_union_of_disjoint (blockVIN₁_disjoint_N₂ ord eStar e)
  rw [← hc]
  rw [blockVIN₁_union_N₂ ord eStar e]


/-- **eq. (6.7), N₂ bound**: `|N₂| ≤ (|e|−1)(|e*|−1)`.  Each `f ∈ N₂`
meets `eStar` in a vertex `w ≠ v` (`v := e∩e*`), and meets `e` in a vertex
`u ≠ v`; the map `f ↦ (u, w)` into `(e∖{v}) × (e*∖{v})` is injective by
linearity. -/
theorem blockVI_N₂_bound {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (h2n : 2 ≤ n) (ord : 𝓗 ≃ Fin k) (eStar e : 𝓗)
    (he : e ∈ precedingNeighbours 𝓗 ord eStar) :
    (blockVIN₂ ord eStar e).card ≤
      (edgeSize (e : Set (Fin n)) - 1) * (edgeSize (eStar : Set (Fin n)) - 1) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have heN := (mem_precedingNeighbours 𝓗 ord eStar e).mp he
  have hintE : ((e : Set (Fin n)) ∩ (eStar : Set (Fin n))).Nonempty := heN.2.2
  have hne_e : e ≠ eStar := heN.1
  have hne_eSet : (e : Set (Fin n)) ≠ (eStar : Set (Fin n)) := by
    intro hEq
    exact hne_e (Subtype.ext hEq)
  let v : Fin n := commonVertex (a := (e : Set (Fin n))) (b := (eStar : Set (Fin n))) hintE
  have hv_e : v ∈ (e : Set (Fin n)) :=
    commonVertex_mem_left (a := (e : Set (Fin n))) (b := (eStar : Set (Fin n))) hintE
  have hv_eStar : v ∈ (eStar : Set (Fin n)) :=
    commonVertex_mem_right (a := (e : Set (Fin n))) (b := (eStar : Set (Fin n))) hintE
  -- e ∩ e* = {v}
  have hsubE : ((e : Set (Fin n)) ∩ (eStar : Set (Fin n))).Subsingleton :=
    hlin e.2 eStar.2 hne_eSet
  have hEq_inter_e : (e : Set (Fin n)) ∩ (eStar : Set (Fin n)) = ({v} : Set (Fin n)) := by
    ext x
    constructor
    · intro hx
      have hvx : x ∈ (e : Set (Fin n)) ∩ (eStar : Set (Fin n)) := hx
      have hxv : x = v := hsubE hvx ⟨hv_e, hv_eStar⟩
      simp [hxv]
    · intro hx
      simp at hx
      subst x
      exact ⟨hv_e, hv_eStar⟩
  let S : Finset 𝓗 := blockVIN₂ ord eStar e
  let T : Finset (Fin n × Fin n) :=
    ((verts (e : Set (Fin n))).erase v) ×ˢ ((verts (eStar : Set (Fin n))).erase v)
  let u : 𝓗 → Fin n := fun f =>
    if hh : ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty then
      commonVertex (a := (f : Set (Fin n))) (b := (e : Set (Fin n))) hh else 0
  let w : 𝓗 → Fin n := fun f =>
    if hh : ((f : Set (Fin n)) ∩ (eStar : Set (Fin n))).Nonempty then
      commonVertex (a := (f : Set (Fin n))) (b := (eStar : Set (Fin n))) hh else 0
  let φ : 𝓗 → Fin n × Fin n := fun f => (u f, w f)
  -- v is not in any member of N₂:
  have hv_notin : ∀ f ∈ S, v ∉ (f : Set (Fin n)) := by
    intro f hfS
    have hf₂ := (mem_blockVIN₂ ord eStar e f).mp hfS
    intro hv
    -- f ∩ e* = {v} too, contradicting f ∉ N₁
    have hfWD : f ∈ fwdnbrNbrs ord eStar e := hf₂.1
    have hfPre : f ∈ precedingNeighbours 𝓗 ord eStar :=
      (mem_fwdnbrNbrs ord eStar e f).mp hfWD |>.2
    have hfPreN := (mem_precedingNeighbours 𝓗 ord eStar f).mp hfPre
    have hne_f : f ≠ eStar := hfPreN.1
    have hne_fSet : (f : Set (Fin n)) ≠ (eStar : Set (Fin n)) := by
      intro hEq
      exact hne_f (Subtype.ext hEq)
    have hsubF : ((f : Set (Fin n)) ∩ (eStar : Set (Fin n))).Subsingleton :=
      hlin f.2 eStar.2 hne_fSet
    have hEq_inter_f : (f : Set (Fin n)) ∩ (eStar : Set (Fin n)) = ({v} : Set (Fin n)) := by
      ext x
      constructor
      · intro hx
        have hxv : x = v := hsubF hx ⟨hv, hv_eStar⟩
        simp [hxv]
      · intro hx
        simp at hx
        subst x
        exact ⟨hv, hv_eStar⟩
    have hEq : (f : Set (Fin n)) ∩ (eStar : Set (Fin n)) =
        (e : Set (Fin n)) ∩ (eStar : Set (Fin n)) := by
      rw [hEq_inter_f, hEq_inter_e]
    exact hf₂.2 hEq
  have hφinj : Set.InjOn φ (S : Set 𝓗) := by
    intro f₁ hf₁S f₂ hf₂S hEq
    have hf₁₂ := (mem_blockVIN₂ ord eStar e f₁).mp hf₁S
    have hf₂₂ := (mem_blockVIN₂ ord eStar e f₂).mp hf₂S
    have hf₁WD : f₁ ∈ fwdnbrNbrs ord eStar e := hf₁₂.1
    have hf₁Ne : f₁ ∈ neighbourEdges 𝓗 e := (mem_fwdnbrNbrs ord eStar e f₁).mp hf₁WD |>.1
    have hf₁Pre : f₁ ∈ precedingNeighbours 𝓗 ord eStar := (mem_fwdnbrNbrs ord eStar e f₁).mp hf₁WD |>.2
    have hf₂WD : f₂ ∈ fwdnbrNbrs ord eStar e := hf₂₂.1
    have hf₂Ne : f₂ ∈ neighbourEdges 𝓗 e := (mem_fwdnbrNbrs ord eStar e f₂).mp hf₂WD |>.1
    have hf₂Pre : f₂ ∈ precedingNeighbours 𝓗 ord eStar := (mem_fwdnbrNbrs ord eStar e f₂).mp hf₂WD |>.2
    have hf₁NeN := (mem_neighbourEdges 𝓗 e f₁).mp hf₁Ne
    have hf₂NeN := (mem_neighbourEdges 𝓗 e f₂).mp hf₂Ne
    have hf₁PreN := (mem_precedingNeighbours 𝓗 ord eStar f₁).mp hf₁Pre
    have hf₂PreN := (mem_precedingNeighbours 𝓗 ord eStar f₂).mp hf₂Pre
    have hintf₁ : ((f₁ : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := hf₁NeN.2
    have hintf₂ : ((f₂ : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := hf₂NeN.2
    have hintg₁ : ((f₁ : Set (Fin n)) ∩ (eStar : Set (Fin n))).Nonempty := hf₁PreN.2.2
    have hintg₂ : ((f₂ : Set (Fin n)) ∩ (eStar : Set (Fin n))).Nonempty := hf₂PreN.2.2
    have hu₁ : u f₁ = commonVertex (a := (f₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₁ := by
      simp [u, hintf₁]
    have hu₂ : u f₂ = commonVertex (a := (f₂ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₂ := by
      simp [u, hintf₂]
    have hv₁ : w f₁ = commonVertex (a := (f₁ : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg₁ := by
      simp [w, hintg₁]
    have hv₂ : w f₂ = commonVertex (a := (f₂ : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg₂ := by
      simp [w, hintg₂]
    have huf : u f₁ = u f₂ := congrArg Prod.fst hEq
    have hwf : w f₁ = w f₂ := congrArg Prod.snd hEq
    have huEq : commonVertex (a := (f₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₁ =
        commonVertex (a := (f₂ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₂ := by
      rw [← hu₁, ← hu₂]
      exact huf
    have hwEq : commonVertex (a := (f₁ : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg₁ =
        commonVertex (a := (f₂ : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg₂ := by
      rw [← hv₁, ← hv₂]
      exact hwf
    -- memberships
    have hu₁f₁ : commonVertex (a := (f₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₁ ∈ (f₁ : Set (Fin n)) :=
      commonVertex_mem_left hintf₁
    have hu₂f₂ : commonVertex (a := (f₂ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₂ ∈ (f₂ : Set (Fin n)) :=
      commonVertex_mem_left hintf₂
    have hw₁f₁ : commonVertex (a := (f₁ : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg₁ ∈ (f₁ : Set (Fin n)) :=
      commonVertex_mem_left hintg₁
    have hw₂f₂ : commonVertex (a := (f₂ : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg₂ ∈ (f₂ : Set (Fin n)) :=
      commonVertex_mem_left hintg₂
    have hu₁e : commonVertex (a := (f₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₁ ∈ (e : Set (Fin n)) :=
      commonVertex_mem_right hintf₁
    have hw₁eStar : commonVertex (a := (f₁ : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg₁ ∈ (eStar : Set (Fin n)) :=
      commonVertex_mem_right hintg₁
    -- u₁ ≠ w₁:
    have hu₁_ne_w₁ : commonVertex (a := (f₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₁ ≠
        commonVertex (a := (f₁ : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg₁ := by
      intro hEq₁
      have hvw : commonVertex (a := (f₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₁ = v := by
        have hin : commonVertex (a := (f₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₁ ∈
            (e : Set (Fin n)) ∩ (eStar : Set (Fin n)) := ⟨hu₁e, by simpa [hEq₁] using hw₁eStar⟩
        have hEqv := hsubE hin ⟨hv_e, hv_eStar⟩
        exact hEqv
      exact hv_notin f₁ hf₁S (by
        rw [← hvw]
        exact hu₁f₁)
    -- shared vertices of f₁ lie in f₂:
    have hu₁f₂ : commonVertex (a := (f₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintf₁ ∈ (f₂ : Set (Fin n)) := by
      rw [huEq]
      exact hu₂f₂
    have hw₁f₂ : commonVertex (a := (f₁ : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg₁ ∈ (f₂ : Set (Fin n)) := by
      rw [hwEq]
      exact hw₂f₂
    apply Subtype.ext
    exact IsLinear.eq_of_mem_pair (𝓗 := 𝓗) hlin f₁.2 f₂.2 hu₁_ne_w₁ hu₁f₁ hw₁f₁ hu₁f₂ hw₁f₂
  have hφsub : S.image φ ⊆ T := by
    intro p hp
    rcases (Finset.mem_image.mp hp) with ⟨f, hfS, rfl⟩
    rw [Finset.mem_product]
    have hf₂ := (mem_blockVIN₂ ord eStar e f).mp hfS
    have hfWD : f ∈ fwdnbrNbrs ord eStar e := hf₂.1
    have hfNe : f ∈ neighbourEdges 𝓗 e := (mem_fwdnbrNbrs ord eStar e f).mp hfWD |>.1
    have hfPre : f ∈ precedingNeighbours 𝓗 ord eStar := (mem_fwdnbrNbrs ord eStar e f).mp hfWD |>.2
    have hfNeN := (mem_neighbourEdges 𝓗 e f).mp hfNe
    have hfPreN := (mem_precedingNeighbours 𝓗 ord eStar f).mp hfPre
    have hintf : ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := hfNeN.2
    have hintg : ((f : Set (Fin n)) ∩ (eStar : Set (Fin n))).Nonempty := hfPreN.2.2
    have hu : u f = commonVertex (a := (f : Set (Fin n))) (b := (e : Set (Fin n))) hintf := by
      simp [u, hintf]
    have hv : w f = commonVertex (a := (f : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg := by
      simp [w, hintg]
    have huf_e : commonVertex (a := (f : Set (Fin n))) (b := (e : Set (Fin n))) hintf ∈ (e : Set (Fin n)) :=
      commonVertex_mem_right hintf
    have huf_f : commonVertex (a := (f : Set (Fin n))) (b := (e : Set (Fin n))) hintf ∈ (f : Set (Fin n)) :=
      commonVertex_mem_left hintf
    have hwg_eStar : commonVertex (a := (f : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg ∈ (eStar : Set (Fin n)) :=
      commonVertex_mem_right hintg
    have hwg_f : commonVertex (a := (f : Set (Fin n))) (b := (eStar : Set (Fin n))) hintg ∈ (f : Set (Fin n)) :=
      commonVertex_mem_left hintg
    constructor
    · dsimp [φ]
      rw [hu]
      rw [Finset.mem_erase]
      constructor
      · intro hEqv
        exact hv_notin f hfS (by
          rw [← hEqv]
          exact huf_f)
      · rw [mem_verts]
        exact huf_e
    · dsimp [φ]
      rw [hv]
      rw [Finset.mem_erase]
      constructor
      · intro hEqv
        exact hv_notin f hfS (by
          rw [← hEqv]
          exact hwg_f)
      · rw [mem_verts]
        exact hwg_eStar
  have hcardφ : S.card = (S.image φ).card := by
    exact (Finset.card_image_of_injOn hφinj).symm
  have hcard : S.card ≤ T.card := by
    calc
      S.card = (S.image φ).card := hcardφ
      _ ≤ T.card := Finset.card_le_card hφsub
  have hv_eV : v ∈ verts (e : Set (Fin n)) := by
    rw [mem_verts]
    exact hv_e
  have hv_eStarV : v ∈ verts (eStar : Set (Fin n)) := by
    rw [mem_verts]
    exact hv_eStar
  have hcardT : T.card = (edgeSize (e : Set (Fin n)) - 1) * (edgeSize (eStar : Set (Fin n)) - 1) := by
    dsimp [T, edgeSize]
    rw [Finset.card_product]
    rw [Finset.card_erase_of_mem hv_eV]
    rw [Finset.card_erase_of_mem hv_eStarV]
  exact hcard.trans (le_of_eq hcardT)

/-! **Block VI, part 2, step 1 (continued): the N₁ bound** — `blockVI_N₁_bound`:
`|N₁| ≤ n/(r−1)` (`r := |eStar|`).  Every `f ∈ N₁` contains the common
vertex `v` of `e` and `eStar` (`f∩e* = e∩e* ∋ v`) and has size `≥ r` by
(O2) (`f ∈ fwdnbr(e*) ⊆ segmentPrefix`, `prefix_size_ge`); the leftovers
`(verts f).erase v` are pairwise disjoint (`f₁,f₂ ∋ v` sharing any other
vertex `u` would be equal by `IsLinear.eq_of_mem_pair`), so
`|N₁|·(r−1) ≤ Σ ≤ |Fin n ∖ {v}| = n−1 ≤ n` via `Finset.disjiUnion` /
`Finset.card_disjiUnion` / `card_le_card`; dividing by `r−1 > 0`
(`2 ≤ |eStar|`) gives the real bound.  The proof needs no `h2n` (the
default-vertex-free sum argument avoids the `Fin n`-inhabitants issue). -/

/-- **eq. (6.7), N₁ bound**: `|N₁| ≤ n/(r−1)`, `r := |eStar|`.  Every
`f ∈ N₁` contains the common vertex `v` of `e` and `eStar` and has size at
least `r` (O2); the leftovers `f∖{v}` are pairwise disjoint subsets of the
other `n−1` vertices, so `|N₁|·(r−1) ≤ n−1 ≤ n`. -/
theorem blockVI_N₁_bound {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (ord : 𝓗 ≃ Fin k) (eStar e : 𝓗)
    (hO2 : OrderingBySize ord eStar)
    (he : e ∈ precedingNeighbours 𝓗 ord eStar)
    (hge : 2 ≤ edgeSize (eStar : Set (Fin n))) :
    ((blockVIN₁ ord eStar e).card : ℝ) ≤
      (n : ℝ) / ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1) := by
  classical
  have heN := (mem_precedingNeighbours 𝓗 ord eStar e).mp he
  have hintE : ((e : Set (Fin n)) ∩ (eStar : Set (Fin n))).Nonempty := heN.2.2
  have hne_e : e ≠ eStar := heN.1
  have hne_eSet : (e : Set (Fin n)) ≠ (eStar : Set (Fin n)) := by
    intro hEq
    exact hne_e (Subtype.ext hEq)
  let v : Fin n := commonVertex (a := (e : Set (Fin n))) (b := (eStar : Set (Fin n))) hintE
  have hv_e : v ∈ (e : Set (Fin n)) :=
    commonVertex_mem_left (a := (e : Set (Fin n))) (b := (eStar : Set (Fin n))) hintE
  have hv_eStar : v ∈ (eStar : Set (Fin n)) :=
    commonVertex_mem_right (a := (e : Set (Fin n))) (b := (eStar : Set (Fin n))) hintE
  let S : Finset 𝓗 := blockVIN₁ ord eStar e
  let rN : ℕ := edgeSize (eStar : Set (Fin n))
  -- v ∈ every member of N₁ (they meet eStar in e∩e* ∋ v):
  have hv_in : ∀ f ∈ S, v ∈ (f : Set (Fin n)) := by
    intro f hfS
    have hf₁ := (mem_blockVIN₁ ord eStar e f).mp hfS
    have hEqf : (f : Set (Fin n)) ∩ (eStar : Set (Fin n)) = (e : Set (Fin n)) ∩ (eStar : Set (Fin n)) := hf₁.2
    have hvin : v ∈ (f : Set (Fin n)) ∩ (eStar : Set (Fin n)) := by
      rw [hEqf]
      exact ⟨hv_e, hv_eStar⟩
    exact hvin.1
  -- |f| ≥ rN for f ∈ N₁ (O2: f ∈ fwdnbr(e*) ⊆ prefix of eStar):
  have hsize : ∀ f ∈ S, rN ≤ edgeSize (f : Set (Fin n)) := by
    intro f hfS
    have hf₁ := (mem_blockVIN₁ ord eStar e f).mp hfS
    have hfWD : f ∈ fwdnbrNbrs ord eStar e := hf₁.1
    have hfPre : f ∈ precedingNeighbours 𝓗 ord eStar := (mem_fwdnbrNbrs ord eStar e f).mp hfWD |>.2
    have hfrank : (ord f : ℕ) ≤ (ord eStar : ℕ) := (mem_precedingNeighbours 𝓗 ord eStar f).mp hfPre |>.2.1
    have hfseg : f ∈ segmentPrefix ord eStar := (mem_segmentPrefix ord eStar f).mpr hfrank
    have hle := prefix_size_ge ord eStar hO2 (f := f) hfseg
    dsimp [rN]
    exact_mod_cast hle
  -- the leftovers, pairwise disjoint:
  let L : 𝓗 → Finset (Fin n) := fun f => (verts (f : Set (Fin n))).erase v
  have hpd : (S : Set 𝓗).PairwiseDisjoint L := by
    intro f₁ hf₁ f₂ hf₂ hne
    change Disjoint (L f₁) (L f₂)
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    have hu₁e := Finset.mem_erase.mp hu₁
    have hu₂e := Finset.mem_erase.mp hu₂
    have huf₁ : u ∈ (f₁ : Set (Fin n)) := (mem_verts (f₁ : Set (Fin n)) u).mp hu₁e.2
    have huf₂ : u ∈ (f₂ : Set (Fin n)) := (mem_verts (f₂ : Set (Fin n)) u).mp hu₂e.2
    have hunev : u ≠ v := hu₁e.1
    have hv₁ : v ∈ (f₁ : Set (Fin n)) := hv_in f₁ hf₁
    have hv₂ : v ∈ (f₂ : Set (Fin n)) := hv_in f₂ hf₂
    have hneSet : (f₁ : Set (Fin n)) ≠ (f₂ : Set (Fin n)) := by
      intro hEq
      exact hne (Subtype.ext hEq)
    have heq := IsLinear.eq_of_mem_pair (𝓗 := 𝓗) hlin f₁.2 f₂.2 hunev huf₁ hv₁ huf₂ hv₂
    exact hne (Subtype.ext heq)
  let D : Finset (Fin n) := S.disjiUnion L hpd
  have hDcard : D.card = S.sum (fun f : 𝓗 => (L f).card) := Finset.card_disjiUnion S L hpd
  -- D ⊆ Fin n ∖ {v}:
  have hDsub : D ⊆ (Finset.univ : Finset (Fin n)).erase v := by
    intro x hxD
    rw [Finset.mem_disjiUnion] at hxD
    rcases hxD with ⟨f, hfS, hxL⟩
    rw [Finset.mem_erase]
    have hxLe := Finset.mem_erase.mp hxL
    constructor
    · exact hxLe.1
    · simp
  have hDcard_le : D.card ≤ n - 1 := by
    have hle := Finset.card_le_card hDsub
    have hcv : ((Finset.univ : Finset (Fin n)).erase v).card = n - 1 := by
      rw [Finset.card_erase_of_mem (by simp : v ∈ (Finset.univ : Finset (Fin n)))]
      simp
    rw [hcv] at hle
    exact hle
  -- each leftover has size ≥ rN − 1:
  have h1rN : 1 ≤ rN := by
    dsimp [rN]
    omega
  have hLcard : ∀ f ∈ S, (edgeSize (f : Set (Fin n)) - 1) = (L f).card := by
    intro f hfS
    have hvf : v ∈ verts (f : Set (Fin n)) := by
      rw [mem_verts]
      exact hv_in f hfS
    dsimp [L]
    rw [Finset.card_erase_of_mem hvf]
    rfl
  have hterm : ∀ f ∈ S, rN - 1 ≤ (L f).card := by
    intro f hfS
    have hs := hsize f hfS
    have hcard : rN - 1 ≤ edgeSize (f : Set (Fin n)) - 1 := by omega
    rw [← hLcard f hfS]
    exact hcard
  -- lower bound on the sum:
  have hsum_ge : S.card * (rN - 1) ≤ S.sum (fun f : 𝓗 => (L f).card) := by
    calc
      S.card * (rN - 1) = S.sum (fun _ : 𝓗 => rN - 1) := by
        rw [Finset.sum_const]
        simp
      _ ≤ S.sum (fun f : 𝓗 => (L f).card) := Finset.sum_le_sum hterm
  have hsum_le : S.sum (fun f : 𝓗 => (L f).card) ≤ n - 1 := by
    calc
      S.sum (fun f : 𝓗 => (L f).card) = D.card := hDcard.symm
      _ ≤ n - 1 := hDcard_le
  have hnat : S.card * (rN - 1) ≤ n := by
    exact le_trans hsum_ge (le_trans hsum_le (by omega))
  -- real division:
  have hreal : (S.card : ℝ) * ((rN : ℝ) - 1) ≤ (n : ℝ) := by
    have hcast : ((rN - 1 : ℕ) : ℝ) = (rN : ℝ) - 1 := by
      rw [Nat.cast_sub h1rN]
      norm_num
    have hb : (S.card : ℝ) * ((rN - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnat
    rwa [hcast] at hb
  have hpos : 0 < (rN : ℝ) - 1 := by
    dsimp [rN]
    have h2 : (2 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) := by exact_mod_cast hge
    linarith
  rw [le_div_iff₀ hpos]
  simpa [S, rN] using hreal

/-! **Block VI, part 2, step 1 (concluded): eq. (6.7)** — the real
combination `blockVI_fwdnbrNbrs_le`: for `e ∈ X` (so `e ∈ fwdnbr(e*)`),
`|N(e)∩fwdnbr(e*)| ≤ n/(r−1) + (|e|−1)(|e*|−1)` — via
`blockVIfwdnbr_card` (the partition) plus `blockVI_N₁_bound` and
`blockVI_N₂_bound`.  Block VI step 1 is now complete; step 2 (eq. (6.6))
will consume this in the margin form
`|N(e)∩fwdnbr(e*)| ≤ τ^{1/4}n/K + (1+K√τ)r²` (margins
`τ^{1/4}(r−1) ≥ K`, `e ∈ X`). -/

/-- **eq. (6.7)**: `|N(e)∩fwdnbr(e*)| ≤ n/(r−1) + (|e|−1)(|e*|−1)` for
`e ∈ X` (in particular `e ∈ fwdnbr(e*)`).  Combine the N₁ bound
(`≤ n/(r−1)`), the N₂ bound (`≤ (|e|−1)(|e*|−1)`), and the partition
`|N(e)∩fwdnbr(e*)| = |N₁| + |N₂|`. -/
theorem blockVI_fwdnbrNbrs_le {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (h2n : 2 ≤ n) (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar e : 𝓗)
    (hO2 : OrderingBySize ord eStar)
    (hge : 2 ≤ edgeSize (eStar : Set (Fin n)))
    (hX : e ∈ XSmall τ K ord eStar) :
    ((fwdnbrNbrs ord eStar e).card : ℝ) ≤
      (n : ℝ) / ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1) +
        (((edgeSize (e : Set (Fin n)) - 1) * (edgeSize (eStar : Set (Fin n)) - 1) : ℕ) : ℝ) := by
  classical
  have he : e ∈ precedingNeighbours 𝓗 ord eStar := (mem_XSmall ord eStar e).mp hX |>.1
  have h₁ := blockVI_N₁_bound (𝓗 := 𝓗) hlin ord eStar e hO2 he hge
  have h₂ : ((blockVIN₂ ord eStar e).card : ℝ) ≤
      (((edgeSize (e : Set (Fin n)) - 1) * (edgeSize (eStar : Set (Fin n)) - 1) : ℕ) : ℝ) := by
    exact_mod_cast (blockVI_N₂_bound (𝓗 := 𝓗) hlin h2n ord eStar e he)
  have hsplit : (fwdnbrNbrs ord eStar e).card =
      (blockVIN₁ ord eStar e).card + (blockVIN₂ ord eStar e).card :=
    blockVIfwdnbr_card ord eStar e
  have hsum : ((fwdnbrNbrs ord eStar e).card : ℝ) =
      ((blockVIN₁ ord eStar e).card : ℝ) + ((blockVIN₂ ord eStar e).card : ℝ) := by
    rw [hsplit]
    norm_num
  rw [hsum]
  exact add_le_add h₁ h₂
/-! **Block VI, part 2, step 2 preparation: eq. (6.7) in margin form**
— `blockVI_fwdnbrNbrs_margin`: under the margin
`K ≤ τ^{1/4}(r−1)` (so `n/(r−1) ≤ τ^{1/4}n/K`) and `e ∈ X` (so
`(|e|−1)(|e*|−1) ≤ |e|·|e*| ≤ (1+K√τ)r²`), `blockVI_fwdnbrNbrs_le`
gives `|N(e)∩fwdnbr(e*)| ≤ τ^{1/4}n/K + (1+K√τ)r²` — the input eq. (6.6)
will consume. -/

/-- **eq. (6.7), margin form**: under `τ^{1/4}(r−1) ≥ K` (so
`n/(r−1) ≤ τ^{1/4}n/K`) and `e ∈ X` (so `(|e|−1)(|e*|−1) ≤ (1+K√τ)r²`),
`|N(e)∩fwdnbr(e*)| ≤ τ^{1/4}n/K + (1+K√τ)r²` — the form eq. (6.6)
consumes. -/
theorem blockVI_fwdnbrNbrs_margin {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (h2n : 2 ≤ n) (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar e : 𝓗)
    (hτ0 : 0 < τ) (hK : (1 : ℝ) ≤ K)
    (hO2 : OrderingBySize ord eStar)
    (hge : 2 ≤ edgeSize (eStar : Set (Fin n)))
    (hmar : (K : ℝ) ≤ tauQuarter τ * ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1))
    (hX : e ∈ XSmall τ K ord eStar) :
    ((fwdnbrNbrs ord eStar e).card : ℝ) ≤
      tauQuarter τ * (n : ℝ) / (K : ℝ) +
        (1 + (K : ℝ) * Real.sqrt τ) * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2 := by
  classical
  let r : ℝ := (edgeSize (eStar : Set (Fin n)) : ℝ)
  let s : ℝ := (edgeSize (e : Set (Fin n)) : ℝ)
  have hle := blockVI_fwdnbrNbrs_le (𝓗 := 𝓗) hlin h2n ord τ K eStar e hO2 hge hX
  have hr1 : 0 < r - 1 := by
    dsimp [r]
    have h2 : (2 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) := by exact_mod_cast hge
    linarith
  have hK0 : (0 : ℝ) < K := by
    have hK1 : (1 : ℕ) ≤ K := by exact_mod_cast hK
    exact_mod_cast (by omega : 0 < K)
  have ht0 : 0 < tauQuarter τ := tauQuarter_pos hτ0
  -- Part 1: n/(r−1) ≤ t·n/K
  have hdiv : (1 : ℝ) / (r - 1) ≤ tauQuarter τ / (K : ℝ) := by
    have hconj : (K : ℝ) ≤ tauQuarter τ * (r - 1) := by
      dsimp [r] at hmar ⊢
      simpa [mul_comm] using hmar
    rw [div_le_div_iff₀ hr1 hK0]
    simpa [mul_comm] using hconj
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hpart1 : (n : ℝ) / (r - 1) ≤ tauQuarter τ * (n : ℝ) / (K : ℝ) := by
    have h1 : (n : ℝ) / (r - 1) = (1 / (r - 1)) * (n : ℝ) := by
      field_simp [hr1.ne']
    have h2 : tauQuarter τ * (n : ℝ) / (K : ℝ) = (tauQuarter τ / (K : ℝ)) * (n : ℝ) := by
      field_simp [hK0.ne']
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right hdiv hn
  -- Part 2: (|e|−1)(|e*|−1) ≤ (1+K√τ)r²
  have hXb : s ≤ (1 + (K : ℝ) * Real.sqrt τ) * r := by
    dsimp [s, r]
    exact ((mem_XSmall ord eStar e).mp hX).2
  have hr0 : (0 : ℝ) ≤ r := by dsimp [r]; positivity
  have hsr : s * r ≤ (1 + (K : ℝ) * Real.sqrt τ) * (r ^ 2) := by
    calc
      s * r ≤ ((1 + (K : ℝ) * Real.sqrt τ) * r) * r := mul_le_mul_of_nonneg_right hXb hr0
      _ = (1 + (K : ℝ) * Real.sqrt τ) * (r ^ 2) := by ring
  have hA1 : ((edgeSize (e : Set (Fin n)) - 1 : ℕ) : ℝ) ≤ s := by
    dsimp [s]
    exact_mod_cast (by omega : edgeSize (e : Set (Fin n)) - 1 ≤ edgeSize (e : Set (Fin n)))
  have hA2 : ((edgeSize (eStar : Set (Fin n)) - 1 : ℕ) : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast (by omega : edgeSize (eStar : Set (Fin n)) - 1 ≤ edgeSize (eStar : Set (Fin n)))
  have hnon1 : (0 : ℝ) ≤ ((edgeSize (e : Set (Fin n)) - 1 : ℕ) : ℝ) := by positivity
  have hnon2 : (0 : ℝ) ≤ ((edgeSize (eStar : Set (Fin n)) - 1 : ℕ) : ℝ) := by positivity
  have hnon_s : (0 : ℝ) ≤ s := by dsimp [s]; positivity
  have hpart2 : (((edgeSize (e : Set (Fin n)) - 1) * (edgeSize (eStar : Set (Fin n)) - 1) : ℕ) : ℝ) ≤
      (1 + (K : ℝ) * Real.sqrt τ) * (r ^ 2) := by
    have hmul : (((edgeSize (e : Set (Fin n)) - 1) * (edgeSize (eStar : Set (Fin n)) - 1) : ℕ) : ℝ) =
        ((edgeSize (e : Set (Fin n)) - 1 : ℕ) : ℝ) * ((edgeSize (eStar : Set (Fin n)) - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
    rw [hmul]
    calc
      ((edgeSize (e : Set (Fin n)) - 1 : ℕ) : ℝ) * ((edgeSize (eStar : Set (Fin n)) - 1 : ℕ) : ℝ)
          ≤ s * r := mul_le_mul hA1 hA2 hnon2 hnon_s
      _ ≤ (1 + (K : ℝ) * Real.sqrt τ) * (r ^ 2) := hsr
  -- assemble:
  have hb1 : ((fwdnbrNbrs ord eStar e).card : ℝ) ≤
      (n : ℝ) / (r - 1) +
        (((edgeSize (e : Set (Fin n)) - 1) * (edgeSize (eStar : Set (Fin n)) - 1) : ℕ) : ℝ) := by
    simpa [r] using hle
  have hb2 : (n : ℝ) / (r - 1) +
        (((edgeSize (e : Set (Fin n)) - 1) * (edgeSize (eStar : Set (Fin n)) - 1) : ℕ) : ℝ) ≤
      tauQuarter τ * (n : ℝ) / (K : ℝ) +
        (1 + (K : ℝ) * Real.sqrt τ) * (r ^ 2) :=
    add_le_add hpart1 hpart2
  exact hb1.trans (by simpa [r] using hb2)

/-! ## Block VI, part 2, step 2 (proved): eq. (6.6)

The counting set `B := blockVIB τ K ord eStar` = `W∖(N(e*)∪{e*})` = the
members of the volume set `W` disjoint from `eStar` (`mem_blockVIB`,
`blockVIB_disjoint_eStar`, `blockVIB_subset_prefix`); `N(e)∩B =
(N(e)∩H^{⪯e*})∩B` (`blockVI_NB_eq_inter`); the containment
`A∖B ⊆ (A∖W) ∪ (N(e)∩fwdnbr(e*)) ∪ {eStar}` (`blockVI_A_minus_B_subset`,
with the three cases `f ∉ W` / `f ∈ N(e*)` / `f = eStar`); the cardinality
skeleton `blockVI_eq66_card`
(`|A∩B| ≥ |A| − |A∖W| − |N(e)∩fwdnbr(e*)| − 1`); and **eq. (6.6)
`blockVI_eq66`**: for `e ∈ X`,
`|N(e)∩B| ≥ (1−τ−7τ^{1/4}/K)n − (1+K√τ)r² − 1`, by chaining
eq. (6.3) (`hm`), eq. (6.5) (`blockV_app2`) and eq. (6.7) in margin form
(`blockVI_fwdnbrNbrs_margin`) — the `−1` is `e* ∈ A∖B`, the convention
loss recorded in the Block VI part 1 note (absorbed at assembly by the
margin `(A−1−K√τ)·r² ≥ 1`).  Remaining: the double count (6.8) and the
|B|/|W|/volume bounds. -/

/-- **B** (eq. (6.6)/(6.8)): `W ∖ (N(e*) ∪ {e*})` = the members of the
volume set `W` disjoint from `eStar` (with our exclusive `neighbourEdges`,
`f ∉ N(e*) ∧ f ≠ e*` ⟺ `f ∩ e* = ∅`).  This is the paper's `W∖N(e*)`
read with the self-inclusive neighbourhood — the convention that makes the
double count of (6.8) valid (see the convention note in Block VI part 1). -/
noncomputable def blockVIB {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) : Finset 𝓗 := by
  classical
  exact (VolumeSet τ K ord eStar).filter (fun f : 𝓗 =>
    f ∉ neighbourEdges 𝓗 eStar ∧ f ≠ eStar)

/-- membership in B -/
lemma mem_blockVIB {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar f : 𝓗) :
    f ∈ blockVIB τ K ord eStar ↔
      f ∈ VolumeSet τ K ord eStar ∧ f ∉ neighbourEdges 𝓗 eStar ∧ f ≠ eStar := by
  classical
  simp [blockVIB]

/-- B consists of members of W disjoint from eStar. -/
lemma blockVIB_disjoint_eStar {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) {f : 𝓗} (hf : f ∈ blockVIB τ K ord eStar) :
    Disjoint (f : Set (Fin n)) (eStar : Set (Fin n)) := by
  classical
  have hf' := (mem_blockVIB τ K ord eStar f).mp hf
  rw [Set.disjoint_left]
  intro x hx hxe
  -- f intersects eStar at x, so f ∈ N(eStar), contradicting hf'.2.1
  have hfN : f ∈ neighbourEdges 𝓗 eStar := by
    rw [mem_neighbourEdges]
    exact ⟨hf'.2.2, ⟨x, hx, hxe⟩⟩
  exact hf'.2.1 hfN

/-- **eq. (6.6) containment**: with `A := N(e)∩H^{⪯e*}`, `W := VolumeSet`,
`B := W∖(N(e*)∪{e*})`, every `f ∈ A∖B` is either outside `W`, or a member
of `N(e)∩fwdnbr(e*)`, or equal to `eStar`:
`A∖B ⊆ (A∖W) ∪ (N(e)∩fwdnbr(e*)) ∪ {eStar}`. -/
lemma blockVI_A_minus_B_subset {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (K : ℕ) (eStar e : 𝓗) {f : 𝓗}
    (hf : f ∈ nbrsInPrefix ord eStar e \ blockVIB τ K ord eStar) :
    f ∈ (nbrsInPrefix ord eStar e \ VolumeSet τ K ord eStar) ∪
        fwdnbrNbrs ord eStar e ∪ ({eStar} : Finset 𝓗) := by
  classical
  have hfA : f ∈ nbrsInPrefix ord eStar e := (Finset.mem_sdiff.mp hf).1
  have hfnotB : f ∉ blockVIB τ K ord eStar := (Finset.mem_sdiff.mp hf).2
  by_cases hfW : f ∈ VolumeSet τ K ord eStar
  · by_cases hfN : f ∈ neighbourEdges 𝓗 eStar
    · -- f ∈ W ∩ N(e*): f ∈ fwdnbrNbrs
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (by
        have hfNe : f ∈ neighbourEdges 𝓗 e := (mem_nbrsInPrefix ord eStar e f).mp hfA |>.1
        have hfrank : (ord f : ℕ) ≤ (ord eStar : ℕ) := (mem_nbrsInPrefix ord eStar e f).mp hfA |>.2
        have hfN' := (mem_neighbourEdges 𝓗 eStar f).mp hfN
        rw [mem_fwdnbrNbrs]
        constructor
        · exact hfNe
        · rw [mem_precedingNeighbours]
          exact ⟨hfN'.1, hfrank, hfN'.2⟩))))
    · -- f ∈ W, f ∉ N(e*), f ∉ B: so f = eStar
      have hfe : f = eStar := by
        by_contra hnot
        have hB : f ∈ blockVIB τ K ord eStar :=
          (mem_blockVIB τ K ord eStar f).mpr ⟨hfW, hfN, hnot⟩
        exact hfnotB hB
      exact Finset.mem_union.mpr (Or.inr (by simp [hfe]))
  · -- f ∉ W: f ∈ A∖W
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hfA, hfW⟩))))

/-- members of B lie in the prefix of eStar (B ⊆ W ⊆ H^{⪯e*}) -/
lemma blockVIB_subset_prefix {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) :
    blockVIB τ K ord eStar ⊆ segmentPrefix ord eStar := by
  classical
  intro f hf
  have hf' := (mem_blockVIB τ K ord eStar f).mp hf
  exact (mem_segmentPrefix ord eStar f).mpr (volumeSet_le_rank τ K ord eStar (f := f) hf'.1)

/-- `N(e) ∩ B = (N(e)∩H^{⪯e*}) ∩ B` (as B ⊆ H^{⪯e*}) -/
lemma blockVI_NB_eq_inter {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar e : 𝓗) :
    neighbourEdges 𝓗 e ∩ blockVIB τ K ord eStar =
      nbrsInPrefix ord eStar e ∩ blockVIB τ K ord eStar := by
  classical
  ext f
  constructor
  · intro hf
    rw [Finset.mem_inter] at hf ⊢
    constructor
    · rw [mem_nbrsInPrefix]
      constructor
      · exact hf.1
      · exact volumeSet_le_rank τ K ord eStar (f := f)
          ((mem_blockVIB τ K ord eStar f).mp hf.2 |>.1)
    · exact hf.2
  · intro hf
    rw [Finset.mem_inter] at hf ⊢
    rcases hf with ⟨hfA, hfB⟩
    rw [mem_nbrsInPrefix] at hfA
    exact ⟨hfA.1, hfB⟩

/-- **eq. (6.6), cardinality skeleton**: with `A := N(e)∩H^{⪯e*}`, `W :=
VolumeSet`, `B := W∖(N(e*)∪{e*})`,
`|A∩B| ≥ |A| − |A∖W| − |N(e)∩fwdnbr(e*)| − 1` (real form, `A∩B = N(e)∩B`). -/
lemma blockVI_eq66_card {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar e : 𝓗) :
    (((nbrsInPrefix ord eStar e).card : ℝ) -
        ((nbrsInPrefix ord eStar e \ VolumeSet τ K ord eStar).card : ℝ) -
        ((fwdnbrNbrs ord eStar e).card : ℝ) - 1) ≤
      ((neighbourEdges 𝓗 e ∩ blockVIB τ K ord eStar).card : ℝ) := by
  classical
  let A : Finset 𝓗 := nbrsInPrefix ord eStar e
  let B : Finset 𝓗 := blockVIB τ K ord eStar
  let W : Finset 𝓗 := VolumeSet τ K ord eStar
  have hsub : A \ B ⊆ (A \ W) ∪ fwdnbrNbrs ord eStar e ∪ ({eStar} : Finset 𝓗) := by
    intro f hf
    have hfs := blockVI_A_minus_B_subset ord τ K eStar e hf
    simpa [A, B, W] using hfs
  have hcard1 : (A \ B).card ≤ (A \ W).card + (fwdnbrNbrs ord eStar e).card + 1 := by
    have h1 := Finset.card_le_card hsub
    calc
      (A \ B).card ≤ ((A \ W) ∪ fwdnbrNbrs ord eStar e ∪ ({eStar} : Finset 𝓗)).card := h1
      _ ≤ ((A \ W) ∪ fwdnbrNbrs ord eStar e).card + 1 := by
        rw [show ((A \ W) ∪ fwdnbrNbrs ord eStar e ∪ ({eStar} : Finset 𝓗)) =
            ((A \ W) ∪ fwdnbrNbrs ord eStar e) ∪ ({eStar} : Finset 𝓗) by rfl]
        exact Finset.card_union_le ((A \ W) ∪ fwdnbrNbrs ord eStar e) ({eStar} : Finset 𝓗)
          |> (fun h => by
              rw [Finset.card_singleton] at h
              exact h)
      _ ≤ (A \ W).card + (fwdnbrNbrs ord eStar e).card + 1 := by
        have h2 := Finset.card_union_le (A \ W) (fwdnbrNbrs ord eStar e)
        omega
  have hpart : ((A ∩ B).card + (A \ B).card) = A.card := Finset.card_inter_add_card_sdiff A B
  have hNB : (neighbourEdges 𝓗 e ∩ B).card = (A ∩ B).card := by
    have hEq : neighbourEdges 𝓗 e ∩ B = A ∩ B := by
      dsimp [A, B]
      exact blockVI_NB_eq_inter τ K ord eStar e
    rw [hEq]
  -- real chain:
  have hreal1 : ((A \ B).card : ℝ) ≤ ((A \ W).card : ℝ) + ((fwdnbrNbrs ord eStar e).card : ℝ) + 1 := by
    exact_mod_cast hcard1
  have hreal2 : ((A ∩ B).card : ℝ) ≥ (A.card : ℝ) -
      ((A \ W).card : ℝ) - ((fwdnbrNbrs ord eStar e).card : ℝ) - 1 := by
    have hA : (A.card : ℝ) = ((A ∩ B).card : ℝ) + ((A \ B).card : ℝ) := by
      rw [← hpart, Nat.cast_add]
    nlinarith
  rw [hNB]
  simpa [A, B, W] using hreal2
/-- **eq. (6.6)**: for `e ∈ X`, `|N(e)∩B| ≥ (1−τ−7τ^{1/4}/K)n −
(1+K√τ)r² − 1` where `B := W∖(N(e*)∪{e*})`, `r := |eStar|`.  Combine the
cardinality skeleton (`blockVI_eq66_card`: `|A∩B| ≥ |A| − |A∖W| −
|N(e)∩fwdnbr(e*)| − 1`), eq. (6.3) (`hm`: `(1−τ)n ≤ |A|`), eq. (6.5)
(`blockV_app2`: `|A∖W| ≤ 6τ^{1/4}n/K`) and eq. (6.7) in margin form
(`blockVI_fwdnbrNbrs_margin`: `|N(e)∩fwdnbr(e*)| ≤ τ^{1/4}n/K +
(1+K√τ)r²` under `K ≤ τ^{1/4}(r−1)`).  The extra `−1` accounts for
`e* ∈ A∖B` (the paper's strict-prefix convention has no such element). -/
theorem blockVI_eq66 {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (h2n : 2 ≤ n) (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar e : 𝓗)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K)
    (hO2 : OrderingBySize ord eStar)
    (hgeStar : 2 ≤ edgeSize (eStar : Set (Fin n)))
    (hgee : 2 ≤ edgeSize (e : Set (Fin n)))
    (hm1 : 1 + (K : ℝ) * Real.sqrt τ ≤
      (edgeSize (e : Set (Fin n)) : ℝ) / 2)
    (hm2 : 2 * (1 + (K : ℝ) * Real.sqrt τ) ≤
      (K : ℝ) ^ 2 * Real.sqrt τ * (edgeSize (e : Set (Fin n)) : ℝ))
    (hmar : (K : ℝ) ≤ tauQuarter τ * ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1))
    (hX : e ∈ XSmall τ K ord eStar)
    (hm : (1 - τ) * (n : ℝ) ≤ ((nbrsInPrefix ord eStar e).card : ℝ)) :
    ((1 - τ - 7 * tauQuarter τ / (K : ℝ)) * (n : ℝ) -
        (1 + (K : ℝ) * Real.sqrt τ) * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2 - 1) ≤
      ((neighbourEdges 𝓗 e ∩ blockVIB τ K ord eStar).card : ℝ) := by
  classical
  have hcard := blockVI_eq66_card τ K ord eStar e
  have h65 := blockV_app2 (𝓗 := 𝓗) hlin ord τ K eStar e hτ0 hτ1 hK hgee hm1 hm2 hO2 hX hm
  have h67 := blockVI_fwdnbrNbrs_margin (𝓗 := 𝓗) hlin h2n ord τ K eStar e hτ0 hK hO2 hgeStar hmar hX
  -- target: LHS ≤ N∩B; by hcard it suffices LHS ≤ A − a − f − 1
  have hK0 : (0 : ℝ) < K := by
    have hK1 : (1 : ℕ) ≤ K := by exact_mod_cast hK
    exact_mod_cast (by omega : 0 < K)
  have hK0le : (0 : ℝ) ≤ K := le_of_lt hK0
  have hmK : ((1 - τ) * (n : ℝ)) * (K : ℝ) ≤
      ((nbrsInPrefix ord eStar e).card : ℝ) * (K : ℝ) :=
    mul_le_mul_of_nonneg_right hm hK0le
  have h65K : ((nbrsInPrefix ord eStar e \ VolumeSet τ K ord eStar).card : ℝ) * (K : ℝ) ≤
      6 * tauQuarter τ * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right h65 hK0le
    have hcancel : (6 * tauQuarter τ * (n : ℝ) / (K : ℝ)) * (K : ℝ) = 6 * tauQuarter τ * (n : ℝ) := by
      field_simp [hK0.ne']
    rwa [hcancel] at h
  have h67K : ((fwdnbrNbrs ord eStar e).card : ℝ) * (K : ℝ) ≤
      tauQuarter τ * (n : ℝ) +
        (1 + (K : ℝ) * Real.sqrt τ) * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2 * (K : ℝ) := by
    have h := mul_le_mul_of_nonneg_right h67 hK0le
    have hcancel : (tauQuarter τ * (n : ℝ) / (K : ℝ)) * (K : ℝ) = tauQuarter τ * (n : ℝ) := by
      field_simp [hK0.ne']
    -- RHS: (t·n/K + B)·K = t·n + B·K
    have hrhs : (tauQuarter τ * (n : ℝ) / (K : ℝ) +
        (1 + (K : ℝ) * Real.sqrt τ) * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2) * (K : ℝ) =
        tauQuarter τ * (n : ℝ) +
        (1 + (K : ℝ) * Real.sqrt τ) * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2 * (K : ℝ) := by
      rw [add_mul, hcancel]
    rwa [hrhs] at h
  have hleA : ((1 - τ - 7 * tauQuarter τ / (K : ℝ)) * (n : ℝ) -
        (1 + (K : ℝ) * Real.sqrt τ) * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2 - 1) ≤
      ((nbrsInPrefix ord eStar e).card : ℝ) -
        ((nbrsInPrefix ord eStar e \ VolumeSet τ K ord eStar).card : ℝ) -
        ((fwdnbrNbrs ord eStar e).card : ℝ) - 1 := by
    apply le_of_mul_le_mul_right _ hK0
    field_simp [hK0.ne']
    nlinarith [hmK, h65K, h67K]
  exact hleA.trans hcard

/-! **Block VI, part 2, step 3a (proved): eq. (6.8)** — for `f ∈ B`
(so `f ∩ e* = ∅`), `blockVI_eq68`:
`|N(f)∩X| ≤ sizeFactor·r² = (1+3τ^{1/4}K⁴)r²` — via
`X ⊆ N(e*)` (`XSmall_subset_neighbourEdges`), the disjoint-edges bound
`|N(f)∩N(e*)| ≤ |f|·|e*|` (`card_commonNeighbours_disjoint_le`, using
`blockVIB_disjoint_eStar`), and `|f| ≤ sizeFactor·r` (`mem_VolumeSet`,
as `B ⊆ W`).  Needs no τ/K conditions, only `hlin`, `h2n`, `hfB`. -/

/-- **eq. (6.8)**: for `f ∈ B` (so `f ∩ e* = ∅`),
`|N(f)∩X| ≤ (1+3τ^{1/4}K⁴)·r²` (`r := |eStar|`, `X := XSmall`).  Since
`X ⊆ N(e*)` and `f,e*` are disjoint, `|N(f)∩X| ≤ |N(f)∩N(e*)| ≤ |f|·|e*|`
(`card_commonNeighbours_disjoint_le`), and `f ∈ B ⊆ W` gives
`|f| ≤ sizeFactor·r`. -/
theorem blockVI_eq68 {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (h2n : 2 ≤ n) (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar f : 𝓗)
    (hfB : f ∈ blockVIB τ K ord eStar) :
    ((neighbourEdges 𝓗 f ∩ XSmall τ K ord eStar).card : ℝ) ≤
      sizeFactor τ K * ((edgeSize (eStar : Set (Fin n)) : ℝ) ^ 2) := by
  classical
  let r : ℝ := (edgeSize (eStar : Set (Fin n)) : ℝ)
  have hdisj : Disjoint (f : Set (Fin n)) (eStar : Set (Fin n)) :=
    blockVIB_disjoint_eStar τ K ord eStar hfB
  have hXsub : XSmall τ K ord eStar ⊆ neighbourEdges 𝓗 eStar :=
    XSmall_subset_neighbourEdges (τ := τ) (K := K) ord eStar
  have hsub : neighbourEdges 𝓗 f ∩ XSmall τ K ord eStar ⊆
      neighbourEdges 𝓗 f ∩ neighbourEdges 𝓗 eStar := by
    intro g hg
    rw [Finset.mem_inter] at hg ⊢
    exact ⟨hg.1, hXsub hg.2⟩
  have hcard : (neighbourEdges 𝓗 f ∩ XSmall τ K ord eStar).card ≤
      (neighbourEdges 𝓗 f ∩ neighbourEdges 𝓗 eStar).card := Finset.card_le_card hsub
  have hmid := card_commonNeighbours_disjoint_le (𝓗 := 𝓗) hlin h2n (f := f) (g := eStar) hdisj
  have hmidR : ((neighbourEdges 𝓗 f ∩ neighbourEdges 𝓗 eStar).card : ℝ) ≤
      (edgeSize (f : Set (Fin n)) : ℝ) * (edgeSize (eStar : Set (Fin n)) : ℝ) := by
    exact_mod_cast hmid
  -- f ∈ W gives |f| ≤ sizeFactor·r:
  have hfW : f ∈ VolumeSet τ K ord eStar := (mem_blockVIB τ K ord eStar f).mp hfB |>.1
  have hfSize : (edgeSize (f : Set (Fin n)) : ℝ) ≤ sizeFactor τ K * r := by
    dsimp [r]
    exact ((mem_VolumeSet τ K ord eStar f).mp hfW).2
  have hr0 : (0 : ℝ) ≤ r := by dsimp [r]; positivity
  have hfac : (edgeSize (f : Set (Fin n)) : ℝ) * r ≤ sizeFactor τ K * (r ^ 2) := by
    calc
      (edgeSize (f : Set (Fin n)) : ℝ) * r ≤ (sizeFactor τ K * r) * r :=
        mul_le_mul_of_nonneg_right hfSize hr0
      _ = sizeFactor τ K * (r ^ 2) := by ring
  have h1 : ((neighbourEdges 𝓗 f ∩ XSmall τ K ord eStar).card : ℝ) ≤
      (edgeSize (f : Set (Fin n)) : ℝ) * (edgeSize (eStar : Set (Fin n)) : ℝ) := by
    have hc : ((neighbourEdges 𝓗 f ∩ XSmall τ K ord eStar).card : ℝ) ≤
        ((neighbourEdges 𝓗 f ∩ neighbourEdges 𝓗 eStar).card : ℝ) := by
      exact_mod_cast hcard
    exact hc.trans hmidR
  -- replace (edgeSize eStar) by r:
  have h1' : ((neighbourEdges 𝓗 f ∩ XSmall τ K ord eStar).card : ℝ) ≤
      (edgeSize (f : Set (Fin n)) : ℝ) * r := by
    simpa [r] using h1
  exact h1'.trans (by simpa [r] using hfac)

/-! **Block VI, part 2, step 3b (proved): the double count** —
`neighbourEdges_symm` (`f ∈ N(e) ⟺ e ∈ N(f)`) and
`blockVI_doubleCount`: `Σ_{e∈X} |N(e)∩B| = Σ_{f∈B} |N(f)∩X|`
(`X := XSmall`, `B := blockVIB`), via the commons
`Commons.Data.Finset.sum_card_filter_comm` with the relation
`y ∈ N(x)` (each side is the number of pairs
`{(e,f) : e∈X, f∈B, e ∈ N(f)}`).  Step 3 is complete: eq. (6.6) +
eq. (6.8) + the double count are the two one-sided bounds and the bridge
the |B|/|W| estimates (steps 4–5) will combine. -/

/-- `f ∈ N(e) ⟺ e ∈ N(f)` (neighbourhood is symmetric) -/
lemma neighbourEdges_symm {𝓗 : Hypergraph (Fin n)} (e f : 𝓗) :
    f ∈ neighbourEdges 𝓗 e ↔ e ∈ neighbourEdges 𝓗 f := by
  classical
  rw [mem_neighbourEdges, mem_neighbourEdges]
  constructor
  · intro h
    constructor
    · exact h.1.symm
    · rcases h.2 with ⟨x, hx⟩
      exact ⟨x, hx.2, hx.1⟩
  · intro h
    constructor
    · exact h.1.symm
    · rcases h.2 with ⟨x, hx⟩
      exact ⟨x, hx.2, hx.1⟩

/-- **double count** (paper after eq. (6.8)):
`Σ_{e∈X} |N(e)∩B| = Σ_{f∈B} |N(f)∩X|`, `X := XSmall`, `B := blockVIB`. -/
theorem blockVI_doubleCount {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) :
    (XSmall τ K ord eStar).sum (fun e : 𝓗 => (neighbourEdges 𝓗 e ∩ blockVIB τ K ord eStar).card) =
      (blockVIB τ K ord eStar).sum (fun f : 𝓗 => (neighbourEdges 𝓗 f ∩ XSmall τ K ord eStar).card) := by
  classical
  let X : Finset 𝓗 := XSmall τ K ord eStar
  let B : Finset 𝓗 := blockVIB τ K ord eStar
  have hcomm := Commons.Data.Finset.sum_card_filter_comm (s := X) (t := B)
    (r := fun (x : 𝓗) (y : 𝓗) => y ∈ neighbourEdges 𝓗 x)
  -- left summand: (B.filter (·∈N x)).card = (N x ∩ B).card
  have hc1 : ∀ x ∈ X, (B.filter (fun y : 𝓗 => y ∈ neighbourEdges 𝓗 x)).card =
      (neighbourEdges 𝓗 x ∩ B).card := by
    intro x hx
    apply congrArg Finset.card
    ext y
    rw [Finset.mem_filter, Finset.mem_inter]
    tauto
  -- right summand: (X.filter (fun x => y ∈ N x)).card = (N y ∩ X).card, via symmetry
  have hc2 : ∀ y ∈ B, (X.filter (fun x : 𝓗 => y ∈ neighbourEdges 𝓗 x)).card =
      (neighbourEdges 𝓗 y ∩ X).card := by
    intro y hy
    apply congrArg Finset.card
    ext x
    rw [Finset.mem_filter, Finset.mem_inter]
    constructor
    · intro hx
      rcases hx with ⟨hxX, hyN⟩
      exact ⟨(neighbourEdges_symm (𝓗 := 𝓗) x y).mp hyN, hxX⟩
    · intro hx
      rcases hx with ⟨hyN, hxX⟩
      exact ⟨hxX, (neighbourEdges_symm (𝓗 := 𝓗) x y).mpr hyN⟩
  calc
    X.sum (fun x : 𝓗 => (neighbourEdges 𝓗 x ∩ B).card)
        = X.sum (fun x : 𝓗 => (B.filter (fun y : 𝓗 => y ∈ neighbourEdges 𝓗 x)).card) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact (hc1 x hx).symm
    _ = B.sum (fun y : 𝓗 => (X.filter (fun x : 𝓗 => y ∈ neighbourEdges 𝓗 x)).card) := hcomm
    _ = B.sum (fun y : 𝓗 => (neighbourEdges 𝓗 y ∩ X).card) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            exact hc2 y hy


/-! **Block VI, part 2, step 4 (proved): the |B| lower bound** —
`XSmall_mem_size` (members of `X` have size `≥ r`, `≥ 2` when `r ≥ 2`) and
`blockVI_B_lower`: summing eq. (6.6) over `e ∈ X` (per-`e` margins supplied
at the `r`-level by `hM1`/`hM2`/`hmar`, eq. (6.3) by `hIV :
BlockIVStatement`) and eq. (6.8) over `f ∈ B`, connected by
`blockVI_doubleCount`,
`|X|·((1−τ−7τ^{1/4}/K)n − (1+K√τ)r² − 1) ≤ |B|·sizeFactor·r²`.
The real-sum chain: `Finset.card_nsmul_le_sum` (lower), `Nat.cast_sum` +
`exact_mod_cast` on the double count, `Finset.sum_le_card_nsmul` (upper),
`nsmul_eq_mul`.  Remaining: the |W| bound (from |B| + |X| via `X ⊆ W`,
`X ∩ B = ∅`) and the volume (W2) chain, then the `ReorderingInstance`
assembly. -/

/-- members of X have size ≥ r (O2), and at least 2 when r ≥ 2 -/
lemma XSmall_mem_size {k : ℕ} {𝓗 : Hypergraph (Fin n)} (ord : 𝓗 ≃ Fin k)
    (τ : ℝ) (K : ℕ) (eStar : 𝓗) (hO2 : OrderingBySize ord eStar) {e : 𝓗}
    (he : e ∈ XSmall τ K ord eStar) :
    ((edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ)) ∧
    (2 ≤ edgeSize (eStar : Set (Fin n)) → 2 ≤ edgeSize (e : Set (Fin n))) := by
  classical
  constructor
  · exact XSmall_size_ge ord eStar hO2 he
  · intro hge
    have hnat : edgeSize (eStar : Set (Fin n)) ≤ edgeSize (e : Set (Fin n)) := by
      exact_mod_cast XSmall_size_ge ord eStar hO2 he
    omega

/-- **|B| lower bound** (paper after the double count): summing eq. (6.6)
over `e ∈ X` and eq. (6.8) over `f ∈ B`, connected by
`blockVI_doubleCount`,
`|X|·((1−τ−7τ^{1/4}/K)n − (1+K√τ)r² − 1) ≤ |B|·sizeFactor·r²`.  The
per-`e` margins of eq. (6.6) are supplied at the `r := |eStar|` level
(`hM1`/`hM2`/`hmar`) and eq. (6.3) by `hIV : BlockIVStatement`. -/
theorem blockVI_B_lower {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (h2n : 2 ≤ n) (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar : 𝓗)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K)
    (hO2 : OrderingBySize ord eStar)
    (hgeStar : 2 ≤ edgeSize (eStar : Set (Fin n)))
    (hM1 : 1 + (K : ℝ) * Real.sqrt τ ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) / 2)
    (hM2 : 2 * (1 + (K : ℝ) * Real.sqrt τ) ≤
      (K : ℝ) ^ 2 * Real.sqrt τ * (edgeSize (eStar : Set (Fin n)) : ℝ))
    (hmar : (K : ℝ) ≤ tauQuarter τ * ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1))
    (hIV : BlockIVStatement τ ord eStar) :
    ((XSmall τ K ord eStar).card : ℝ) *
        ((1 - τ - 7 * tauQuarter τ / (K : ℝ)) * (n : ℝ) -
          (1 + (K : ℝ) * Real.sqrt τ) * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2 - 1) ≤
      ((blockVIB τ K ord eStar).card : ℝ) *
        (sizeFactor τ K * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2) := by
  classical
  let X : Finset 𝓗 := XSmall τ K ord eStar
  let B : Finset 𝓗 := blockVIB τ K ord eStar
  let LB : ℝ := (1 - τ - 7 * tauQuarter τ / (K : ℝ)) * (n : ℝ) -
    (1 + (K : ℝ) * Real.sqrt τ) * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2 - 1
  let c : ℝ := sizeFactor τ K * ((edgeSize (eStar : Set (Fin n)) : ℝ)) ^ 2
  have h66 : ∀ e ∈ X, LB ≤ ((neighbourEdges 𝓗 e ∩ B).card : ℝ) := by
    intro e heX
    have heX' : e ∈ XSmall τ K ord eStar := by simpa [X] using heX
    have hsz := XSmall_mem_size ord τ K eStar hO2 heX'
    have hgee : 2 ≤ edgeSize (e : Set (Fin n)) := (hsz.2) hgeStar
    have hge_e : (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := hsz.1
    have hm1e : 1 + (K : ℝ) * Real.sqrt τ ≤ (edgeSize (e : Set (Fin n)) : ℝ) / 2 := by
      nlinarith
    have hm2e : 2 * (1 + (K : ℝ) * Real.sqrt τ) ≤
        (K : ℝ) ^ 2 * Real.sqrt τ * (edgeSize (e : Set (Fin n)) : ℝ) := by
      have hK2 : (0 : ℝ) ≤ (K : ℝ) ^ 2 * Real.sqrt τ := by
        have hK0 : (0 : ℝ) ≤ K := by linarith
        exact mul_nonneg (sq_nonneg (K : ℝ)) (Real.sqrt_nonneg τ)
      nlinarith
    have hePre : e ∈ precedingNeighbours 𝓗 ord eStar :=
      XSmall_subset_preceding ord eStar heX'
    have hm3e : (1 - τ) * (n : ℝ) ≤ ((nbrsInPrefix ord eStar e).card : ℝ) :=
      le_of_lt (hIV e hePre)
    have h66e := blockVI_eq66 (𝓗 := 𝓗) hlin h2n ord τ K eStar e hτ0 hτ1 hK hO2 hgeStar
      hgee hm1e hm2e hmar heX' hm3e
    simpa [X, B, LB] using h66e
  have hsum66 : (X.card : ℝ) * LB ≤ X.sum (fun e : 𝓗 => ((neighbourEdges 𝓗 e ∩ B).card : ℝ)) := by
    have hns := Finset.card_nsmul_le_sum X (fun e : 𝓗 => ((neighbourEdges 𝓗 e ∩ B).card : ℝ)) LB h66
    simpa [nsmul_eq_mul] using hns
  have hdc := blockVI_doubleCount (τ := τ) (K := K) ord eStar
  have hsum_real : X.sum (fun e : 𝓗 => ((neighbourEdges 𝓗 e ∩ B).card : ℝ)) =
      B.sum (fun f : 𝓗 => ((neighbourEdges 𝓗 f ∩ X).card : ℝ)) := by
    have hL : X.sum (fun e : 𝓗 => ((neighbourEdges 𝓗 e ∩ B).card : ℝ)) =
        (X.sum (fun e : 𝓗 => (neighbourEdges 𝓗 e ∩ B).card) : ℝ) := by
      rw [← Nat.cast_sum]
    have hR : B.sum (fun f : 𝓗 => ((neighbourEdges 𝓗 f ∩ X).card : ℝ)) =
        (B.sum (fun f : 𝓗 => (neighbourEdges 𝓗 f ∩ X).card) : ℝ) := by
      rw [← Nat.cast_sum]
    have hdc' : X.sum (fun e : 𝓗 => (neighbourEdges 𝓗 e ∩ B).card) =
        B.sum (fun f : 𝓗 => (neighbourEdges 𝓗 f ∩ X).card) := by
      simpa [X, B] using hdc
    have hdcR : (X.sum (fun e : 𝓗 => (neighbourEdges 𝓗 e ∩ B).card) : ℝ) =
        (B.sum (fun f : 𝓗 => (neighbourEdges 𝓗 f ∩ X).card) : ℝ) := by
      exact_mod_cast hdc'
    calc
      X.sum (fun e : 𝓗 => ((neighbourEdges 𝓗 e ∩ B).card : ℝ)) =
          (X.sum (fun e : 𝓗 => (neighbourEdges 𝓗 e ∩ B).card) : ℝ) := hL
      _ = (B.sum (fun f : 𝓗 => (neighbourEdges 𝓗 f ∩ X).card) : ℝ) := hdcR
      _ = B.sum (fun f : 𝓗 => ((neighbourEdges 𝓗 f ∩ X).card : ℝ)) := hR.symm
  have h68 : ∀ f ∈ B, ((neighbourEdges 𝓗 f ∩ X).card : ℝ) ≤ c := by
    intro f hfB
    have hfB' : f ∈ blockVIB τ K ord eStar := by simpa [B] using hfB
    have h := blockVI_eq68 (𝓗 := 𝓗) hlin h2n ord τ K eStar f hfB'
    simpa [X, c] using h
  have hsum68 : B.sum (fun f : 𝓗 => ((neighbourEdges 𝓗 f ∩ X).card : ℝ)) ≤ (B.card : ℝ) * c := by
    have hns := Finset.sum_le_card_nsmul B (fun f : 𝓗 => ((neighbourEdges 𝓗 f ∩ X).card : ℝ)) c h68
    simpa [nsmul_eq_mul] using hns
  simpa [X, B, LB, c] using (hsum66.trans (le_of_eq hsum_real)).trans hsum68

/-! **Block VI, part 2, step 5a (proved): `X ⊆ W`, disjointness, and
`|W| ≥ |B| + |X|`** — `sizeFactor_ge_one_sqrt` (`1+K√τ ≤ sizeFactor` for
`τ ≤ 1`, `K ≥ 1`, via `Kt² ≤ 3K⁴t`), `XSmall_subset_VolumeSet` (`X ⊆ W`:
rank ≤ eStar from `X ⊆ fwdnbr(e*)`, size ≤ `(1+K√τ)r ≤ sizeFactor·r`),
`XSmall_disjoint_blockVIB` (`X ∩ B = ∅`: X ⊆ N(e*), B avoids N(e*)), and
`blockVI_W_ge_B_add_X` (`|B| + |X| ≤ |W|`).  These feed the |W| lower
bound of step 5b. -/

/-- `1+K√τ ≤ sizeFactor τ K` for `τ ≤ 1`, `K ≥ 1` (t := τ^{1/4}: `Kt² ≤ 3K⁴t`). -/
lemma sizeFactor_ge_one_sqrt {τ : ℝ} {K : ℕ} (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K) :
    (1 + (K : ℝ) * Real.sqrt τ) ≤ sizeFactor τ K := by
  unfold sizeFactor
  rw [← tauQuarter_sq τ]
  let t : ℝ := tauQuarter τ
  have ht0 : 0 ≤ t := tauQuarter_nonneg τ
  have ht1 : t ≤ 1 := tauQuarter_le_one hτ1
  change 1 + (K : ℝ) * t ^ 2 ≤ 1 + 3 * t * (K : ℝ) ^ 4
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have ht2 : t ^ 2 ≤ t := by
    have hd : (0 : ℝ) ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
    nlinarith
  have h1 : (K : ℝ) * t ^ 2 ≤ (K : ℝ) * t := mul_le_mul_of_nonneg_left ht2 hK0
  have hKc : (1 : ℝ) ≤ (K : ℝ) ^ 3 := by
    have hK0' : (0 : ℝ) ≤ K := by linarith
    have hd : (0 : ℝ) ≤ ((K : ℝ) - 1) * ((K : ℝ) ^ 2 + (K : ℝ) + 1) := by
      have hsum : (0 : ℝ) ≤ (K : ℝ) ^ 2 + (K : ℝ) + 1 := by positivity
      exact mul_nonneg (by linarith) hsum
    nlinarith
  have hK3 : (K : ℝ) ≤ 3 * (K : ℝ) ^ 4 := by
    have hA : (K : ℝ) ≤ (K : ℝ) ^ 4 := by
      have hm := mul_le_mul_of_nonneg_right hKc hK0
      nlinarith
    nlinarith
  have h2 : (K : ℝ) * t ≤ 3 * t * (K : ℝ) ^ 4 := by
    have h2' : (K : ℝ) * t ≤ (3 * (K : ℝ) ^ 4) * t := mul_le_mul_of_nonneg_right hK3 ht0
    nlinarith
  nlinarith

/-- `X ⊆ W`: members of X have size ≤ (1+K√τ)r ≤ sizeFactor·r and rank ≤ eStar. -/
lemma XSmall_subset_VolumeSet {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K) :
    XSmall τ K ord eStar ⊆ VolumeSet τ K ord eStar := by
  classical
  intro e he
  have he' := (mem_XSmall ord eStar e).mp he
  rw [mem_VolumeSet]
  constructor
  · -- rank e ≤ rank eStar: from e ∈ precedingNeighbours
    have hpre := (mem_precedingNeighbours 𝓗 ord eStar e).mp he'.1
    exact hpre.2.1
  · -- |e| ≤ (1+K√τ)·r ≤ sizeFactor·r
    have hr0 : (0 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) := by positivity
    have hfac : (1 + (K : ℝ) * Real.sqrt τ) ≤ sizeFactor τ K := sizeFactor_ge_one_sqrt hτ1 hK
    have hmul := mul_le_mul_of_nonneg_right hfac hr0
    calc
      (edgeSize (e : Set (Fin n)) : ℝ) ≤ (1 + (K : ℝ) * Real.sqrt τ) * (edgeSize (eStar : Set (Fin n)) : ℝ) := he'.2
      _ ≤ sizeFactor τ K * (edgeSize (eStar : Set (Fin n)) : ℝ) := hmul

/-- `X ∩ B = ∅` (X ⊆ N(e*) whereas members of B are not neighbours of e*). -/
lemma XSmall_disjoint_blockVIB {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) :
    Disjoint (XSmall τ K ord eStar) (blockVIB τ K ord eStar) := by
  classical
  rw [Finset.disjoint_left]
  intro e heX heB
  have hX : e ∈ neighbourEdges 𝓗 eStar :=
    XSmall_subset_neighbourEdges (τ := τ) (K := K) ord eStar heX
  exact ((mem_blockVIB τ K ord eStar e).mp heB).2.1 hX

/-- `|W| ≥ |B| + |X|` (both B and X lie in W, and they are disjoint). -/
lemma blockVI_W_ge_B_add_X {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K) :
    (blockVIB τ K ord eStar).card + (XSmall τ K ord eStar).card ≤
      (VolumeSet τ K ord eStar).card := by
  classical
  have hBsub : blockVIB τ K ord eStar ⊆ VolumeSet τ K ord eStar := by
    intro f hf
    exact (mem_blockVIB τ K ord eStar f).mp hf |>.1
  have hXsub := XSmall_subset_VolumeSet τ K ord eStar hτ1 hK
  have hdisj := XSmall_disjoint_blockVIB τ K ord eStar
  have hcard : (blockVIB τ K ord eStar).card + (XSmall τ K ord eStar).card =
      (XSmall τ K ord eStar ∪ blockVIB τ K ord eStar).card := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  rw [hcard]
  apply Finset.card_le_card
  intro f hf
  rcases (Finset.mem_union.mp hf) with hfX | hfB
  · exact hXsub hfX
  · exact hBsub hfB

/-! **Block VI, part 2, step 5b (proved): the |W| lower bound** —
`blockVI_slack_nonneg` (the bracket slack
`1 − (1+K√τ)/sizeFactor − 1/(sizeFactor·r²) ≥ 0` under the margin
`(sizeFactor−1−K√τ)·r² ≥ 1`), `blockVI_bracket_nonneg`, and
**`blockVI_W_lower`**:
`|W| ≥ (1−τ−2√τ/K)·(1−τ−7τ^{1/4}/K)·n²/(sizeFactor·r²)` — from
`|B|+|X| ≤ |W|` (`blockVI_W_ge_B_add_X`), the |B| bound
(`blockVI_B_lower`), the slack margin (`hAmar`), `0 ≤ q` (`hq`) and the
eq. (6.4) lower bound (`hXb`); the chain runs on the raw real atoms
(`u`, `q`, `c := sizeFactor·r²`, `LB`, … kept opaque for `nlinarith`,
unfolded only where their defining sums are needed, and each `/c`
division cleared by `field_simp`/`div_le_div_of_nonneg_right`).
Remaining: the volume (W2) chain `volBound ≤ volume 𝓗 W` (from
`|W| ≥ u·q·n²/(A r²)` and per-edge sizes `≥ r`), then the
`ReorderingInstance` assembly. -/

/-- the "bracket slack" of the |W| bound is non-negative under the margin
`(A−1−K√τ)·r² ≥ 1`: `1 − (1+K√τ)/A − 1/(A·r²) ≥ 0`. -/
lemma blockVI_slack_nonneg {τ : ℝ} {K : ℕ} (r : ℝ)
    (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K) (hr : 0 < r)
    (hAmar : (1 : ℝ) ≤ (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (r ^ 2)) :
    (0 : ℝ) ≤ 1 - (1 + (K : ℝ) * Real.sqrt τ) / sizeFactor τ K -
      1 / (sizeFactor τ K * (r ^ 2)) := by
  have hS : (1 + (K : ℝ) * Real.sqrt τ) ≤ sizeFactor τ K := sizeFactor_ge_one_sqrt hτ1 hK
  have hA : sizeFactor τ K > 0 := by
    have h1 : (1 : ℝ) ≤ sizeFactor τ K := sizeFactor_ge_one τ K
    linarith
  have hAne : sizeFactor τ K ≠ 0 := ne_of_gt hA
  have hrne : r ≠ 0 := ne_of_gt hr
  -- δ = (A·r² − (1+K√τ)r² − 1)/(A·r²); numerator ≥ 0 by hAmar
  have hnum : (0 : ℝ) ≤ sizeFactor τ K * (r ^ 2) - (1 + (K : ℝ) * Real.sqrt τ) * (r ^ 2) - 1 := by
    have h1 : (1 : ℝ) ≤ (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (r ^ 2) := hAmar
    nlinarith
  have hdenpos : 0 < sizeFactor τ K * (r ^ 2) := mul_pos hA (sq_pos_of_pos hr)
  -- goal: 1 − (1+K√τ)/A − 1/(A r²) ≥ 0 ⟺ (A r² − (1+K√τ)r² − 1)/(A r²) ≥ 0
  have hgoal' : 1 - (1 + (K : ℝ) * Real.sqrt τ) / sizeFactor τ K -
      1 / (sizeFactor τ K * r ^ 2) =
      (sizeFactor τ K * r ^ 2 - (1 + (K : ℝ) * Real.sqrt τ) * r ^ 2 - 1) /
        (sizeFactor τ K * r ^ 2) := by
    field_simp [hAne, hrne]
  rw [hgoal']
  exact div_nonneg hnum (le_of_lt hdenpos)

/-- a positive bracket: `q·n/(A·r²) ≥ 0` when `0 ≤ q`, `0 ≤ n` -/
lemma blockVI_bracket_nonneg {τ : ℝ} {K : ℕ} (r n : ℝ)
    (hA : (0 : ℝ) < sizeFactor τ K) (hr : 0 < r) (hn : (0 : ℝ) ≤ n)
    (hq : (0 : ℝ) ≤ 1 - τ - 7 * tauQuarter τ / (K : ℝ)) :
    (0 : ℝ) ≤ (1 - τ - 7 * tauQuarter τ / (K : ℝ)) * n / (sizeFactor τ K * r ^ 2) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hden : 0 < sizeFactor τ K * r ^ 2 := mul_pos hA hr2
  exact div_nonneg (mul_nonneg hq hn) (le_of_lt hden)
/-- **|W| lower bound**: from |B|+|X| ≤ |W|, the |B| bound and |X| ≥
(1−τ−2√τ/K)n (eq. (6.4)),
`|W| ≥ (1−τ−2√τ/K)·(1−τ−7τ^{1/4}/K)·n²/(sizeFactor·r²)` — the slack
`1 − (1+K√τ)/sizeFactor − 1/(sizeFactor·r²) ≥ 0` is the margin
`(sizeFactor−1−K√τ)·r² ≥ 1`. -/
theorem blockVI_W_lower {k : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (h2n : 2 ≤ n) (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar : 𝓗)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K)
    (hO2 : OrderingBySize ord eStar)
    (hgeStar : 2 ≤ edgeSize (eStar : Set (Fin n)))
    (hM1 : 1 + (K : ℝ) * Real.sqrt τ ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) / 2)
    (hM2 : 2 * (1 + (K : ℝ) * Real.sqrt τ) ≤
      (K : ℝ) ^ 2 * Real.sqrt τ * (edgeSize (eStar : Set (Fin n)) : ℝ))
    (hmar : (K : ℝ) ≤ tauQuarter τ * ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1))
    (hAmar : (1 : ℝ) ≤ (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) *
      ((edgeSize (eStar : Set (Fin n)) : ℝ) ^ 2))
    (hq : (0 : ℝ) ≤ 1 - τ - 7 * tauQuarter τ / (K : ℝ))
    (hXb : ((1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (n : ℝ)) ≤
      ((XSmall τ K ord eStar).card : ℝ))
    (hIV : BlockIVStatement τ ord eStar) :
    ((1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 - τ - 7 * tauQuarter τ / (K : ℝ))) *
        ((n : ℝ) ^ 2) / (sizeFactor τ K * ((edgeSize (eStar : Set (Fin n)) : ℝ) ^ 2)) ≤
      ((VolumeSet τ K ord eStar).card : ℝ) := by
  classical
  let X : Finset 𝓗 := XSmall τ K ord eStar
  let B : Finset 𝓗 := blockVIB τ K ord eStar
  let W : Finset 𝓗 := VolumeSet τ K ord eStar
  let A : ℝ := sizeFactor τ K
  let r2 : ℝ := (edgeSize (eStar : Set (Fin n)) : ℝ) ^ 2
  let q : ℝ := 1 - τ - 7 * tauQuarter τ / (K : ℝ)
  let u : ℝ := 1 - τ - 2 * Real.sqrt τ / (K : ℝ)
  let c : ℝ := A * r2
  let x : ℝ := (X.card : ℝ)
  let b : ℝ := (B.card : ℝ)
  let w : ℝ := (W.card : ℝ)
  let LB : ℝ := q * (n : ℝ) - (1 + (K : ℝ) * Real.sqrt τ) * r2 - 1
  have hA1 : (1 : ℝ) ≤ A := by simpa [A] using sizeFactor_ge_one τ K
  have hr2 : (0 : ℝ) < r2 := by
    dsimp [r2]
    have h2 : (2 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) := by exact_mod_cast hgeStar
    have hpos : (0 : ℝ) < (edgeSize (eStar : Set (Fin n)) : ℝ) := by linarith
    exact sq_pos_of_pos hpos
  have hcpos : 0 < c := by
    dsimp [c]
    have hApos : (0 : ℝ) < A := by linarith
    exact mul_pos hApos hr2
  have hB := blockVI_B_lower (𝓗 := 𝓗) hlin h2n ord τ K eStar hτ0 hτ1 hK hO2 hgeStar
    hM1 hM2 hmar hIV
  have hB' : x * LB ≤ b * c := by
    simpa [X, B, A, r2, q, c, x, b, LB] using hB
  have hBge : (x * LB) / c ≤ b := by
    exact (div_le_iff₀ hcpos).mpr hB'
  have hWadd : b + x ≤ w := by
    have hnat := blockVI_W_ge_B_add_X τ K ord eStar hτ1 hK
    dsimp [b, x, w]
    exact_mod_cast hnat
  have h1 : (x * LB) / c + x ≤ w := by
    nlinarith
  -- slack: (A−1−K√τ)·r2 − 1 ≥ 0
  have hAmar' : (1 : ℝ) ≤ (A - 1 - (K : ℝ) * Real.sqrt τ) * r2 := by
    simpa [A, r2] using hAmar
  have hdelta : (0 : ℝ) ≤ (A - 1 - (K : ℝ) * Real.sqrt τ) * r2 - 1 := by
    nlinarith
  have hqL : q * (n : ℝ) ≤ LB + c := by
    dsimp [LB, c]
    nlinarith [hdelta]
  have hx0 : (0 : ℝ) ≤ x := by dsimp [x]; positivity
  have hqnc : (0 : ℝ) ≤ q * (n : ℝ) / c := by
    have hq0 : (0 : ℝ) ≤ q := by simpa [q] using hq
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    exact div_nonneg (mul_nonneg hq0 hn0) (le_of_lt hcpos)
  have hxmid : x * (q * (n : ℝ)) / c ≤ (x * LB) / c + x := by
    have hEq : (x * LB) / c + x = x * (LB + c) / c := by
      field_simp [hcpos.ne']
    have hm := mul_le_mul_of_nonneg_left hqL hx0
    have hle : x * (q * (n : ℝ)) / c ≤ x * (LB + c) / c := by
      exact (div_le_div_of_nonneg_right hm (le_of_lt hcpos))
    calc
      x * (q * (n : ℝ)) / c ≤ x * (LB + c) / c := hle
      _ = (x * LB) / c + x := hEq.symm
  have h2 : x * (q * (n : ℝ)) / c ≤ w := le_trans hxmid h1
  have hXb' : u * (n : ℝ) ≤ x := by
    simpa [X, u, x] using hXb
  have hxmu : (u * (n : ℝ)) * (q * (n : ℝ) / c) ≤ x * (q * (n : ℝ)) / c := by
    have hm := mul_le_mul_of_nonneg_right hXb' hqnc
    have hEqR : x * (q * (n : ℝ)) / c = x * (q * (n : ℝ) / c) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    calc
      (u * (n : ℝ)) * (q * (n : ℝ) / c) ≤ x * (q * (n : ℝ) / c) := hm
      _ = x * (q * (n : ℝ)) / c := hEqR.symm
  have hEq2 : (u * (n : ℝ)) * (q * (n : ℝ) / c) = (u * q) * ((n : ℝ) ^ 2) / c := by
    field_simp [hcpos.ne']
  have h3 : (u * q) * ((n : ℝ) ^ 2) / c ≤ w := by
    rw [← hEq2]
    exact hxmu.trans h2
  simpa [u, q, c, A, r2, w, W] using h3

/-! **Block VI, part 2, step 6a (proved): the volume numerator over W** —
`blockVI_volume_term_ge` (**(W2)(i)**: for `e ∈ W ⊆ H^{⪯e*}` the volume
summand `|e|(|e|−1) ≥ r(r−1)`, `r := |eStar|` — from (O2) `|e| ≥ r`
(`volumeSet_ge_self`) and `x ↦ x(x−1)` monotone on `x ≥ 1`, i.e.
`f(s) − f(r) = (s−r)(s+r−1) ≥ 0`) and `blockVI_volume_sum_ge`
(**(W2)(ii)**: `|W|·r(r−1) ≤ Σ_{e∈W} |e|(|e|−1)`, via
`Finset.card_nsmul_le_sum` + `nsmul_eq_mul`).  Remaining for (W2): the
division chain `volBound ≤ volume 𝓗 W` from these, the |W| bound
(`blockVI_W_lower`), `n ≥ 2` and the final margin
`(1−τ−2√τ/K)·(1−1/r) ≥ 1−τ−7τ^{1/4}/K`. -/

/-- **(W2), (i)**: for `e ∈ W ⊆ H^{⪯e*}` the volume summand `|e|(|e|−1)`
is at least `r(r−1)` (`r := |eStar|`), by (O2) `|e| ≥ r` and the
monotonicity of `x ↦ x(x−1)` on `x ≥ 1`. -/
lemma blockVI_volume_term_ge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) (hO2 : OrderingBySize ord eStar)
    (hr1 : (1 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ)) {e : 𝓗}
    (hW : e ∈ VolumeSet τ K ord eStar) :
    ((edgeSize (eStar : Set (Fin n)) : ℝ) * ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1)) ≤
      (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1) := by
  have hge : (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) :=
    volumeSet_ge_self τ K ord eStar hO2 hW
  have h1 : (0 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) - (edgeSize (eStar : Set (Fin n)) : ℝ) := by
    linarith
  have h2 : (0 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) + (edgeSize (eStar : Set (Fin n)) : ℝ) - 1 := by
    have h2' : (1 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) + (edgeSize (eStar : Set (Fin n)) : ℝ) - 1 := by
      nlinarith [hr1, hge]
    linarith
  have hfac : (0 : ℝ) ≤
      ((edgeSize (e : Set (Fin n)) : ℝ) - (edgeSize (eStar : Set (Fin n)) : ℝ)) *
        ((edgeSize (e : Set (Fin n)) : ℝ) + (edgeSize (eStar : Set (Fin n)) : ℝ) - 1) :=
    mul_nonneg h1 h2
  nlinarith

/-- **(W2), (ii)**: the volume numerator over `W` is at least
`|W|·r(r−1)`. -/
lemma blockVI_volume_sum_ge {k : ℕ} {𝓗 : Hypergraph (Fin n)} (τ : ℝ) (K : ℕ)
    (ord : 𝓗 ≃ Fin k) (eStar : 𝓗) (hO2 : OrderingBySize ord eStar)
    (hr1 : (1 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ)) :
    (((edgeSize (eStar : Set (Fin n)) : ℝ) * ((edgeSize (eStar : Set (Fin n)) : ℝ) - 1)) *
        ((VolumeSet τ K ord eStar).card : ℝ)) ≤
      (VolumeSet τ K ord eStar).sum (fun e : 𝓗 =>
        (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) := by
  classical
  let r : ℝ := (edgeSize (eStar : Set (Fin n)) : ℝ)
  have hterm : ∀ e ∈ VolumeSet τ K ord eStar,
      r * (r - 1) ≤ (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1) := by
    intro e hW
    have h := blockVI_volume_term_ge τ K ord eStar hO2 hr1 (e := e) hW
    dsimp [r] at h ⊢
    exact h
  have hns := Finset.card_nsmul_le_sum (s := VolumeSet τ K ord eStar)
    (f := fun e : 𝓗 => (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1))
    (r * (r - 1)) hterm
  have hns' : (VolumeSet τ K ord eStar).card * (r * (r - 1)) ≤
      (VolumeSet τ K ord eStar).sum (fun e : 𝓗 =>
        (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) := by
    simpa [nsmul_eq_mul] using hns
  simpa [r, mul_comm] using hns'

/-! **Block VI, part 2, step 6b (proved): volume-chain helpers** —
`blockVI_cast_sub_one` (`((n−1 : ℕ) : ℝ) = (n : ℝ) − 1` for `2 ≤ n`) and
`blockVI_frac_n_sub_one_ge` (`1 ≤ n/(n−1)` for `2 ≤ n`) — the denominator
facts the (W2) division chain uses. -/

/-- `((n−1 : ℕ) : ℝ) = (n : ℝ) − 1` for `2 ≤ n`. -/
lemma blockVI_cast_sub_one (h2n : 2 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  have h1 : 1 ≤ n := by omega
  rw [Nat.cast_sub h1]
  norm_num

/-- `1 ≤ n/(n−1)` for `2 ≤ n`. -/
lemma blockVI_frac_n_sub_one_ge (h2n : 2 ≤ n) : (1 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) := by
  have hden : 0 < (n : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n
    linarith
  rw [le_div_iff₀ hden]
  linarith

/-! **Block VI, part 2, step 6c (proved): the (W2) volume bound
`blockVI_WVolume`** — `volBound τ K ≤ Hypergraph.volume 𝓗 W` for
`W := VolumeSet τ K ord eStar`, from the |W| bound (`hW`, the conclusion
of `blockVI_W_lower`), the numerator bound (`blockVI_volume_sum_ge`), the
final margin `hfin : (1−τ−2√τ/K)·(1−1/r) ≥ 1−τ−7τ^{1/4}/K`, `hq : 0 ≤ q`
and `2 ≤ n`.  Chain: `volume = num/(n(n−1)) ≥ |W|·r(r−1)/D ≥
(u·q·n²/(A r²))·(r(r−1)/D) = (u·q)·(n²/D)·((r−1)/(A r)) ≥
(u·q)·((r−1)/(A r))` (`n/(n−1) ≥ 1`, `u·q ≥ 0` from `hfin`) `≥ q²/A`
(`(q/A)·q ≤ (q/A)·u·((r−1)/r)`, `(r−1)/r = 1−1/r`) `= volBound τ K`.
The |B|/|W|/volume part of Block VI is now complete. -/

/-- **(W2)**: `volBound ≤ volume 𝓗 W` (`W := VolumeSet τ K ord eStar`).
  Chain: `volume = num/(n(n−1)) ≥ |W|·r(r−1)/(n(n−1))`
  (`blockVI_volume_sum_ge`) `≥ u·q·n²/(A r²)·r(r−1)/D`
  (`hW` = the |W| bound of `blockVI_W_lower`) `= u·q·(n²/D)·((r−1)/(A r))`
  `≥ u·q·((r−1)/(A r))` (`n/(n−1) ≥ 1`) `≥ q²/A` (margin `hfin`,
  `q ≥ 0`) `= volBound`. -/
theorem blockVI_WVolume {k : ℕ} {𝓗 : Hypergraph (Fin n)} (h2n : 2 ≤ n)
    (ord : 𝓗 ≃ Fin k) (τ : ℝ) (K : ℕ) (eStar : 𝓗)
    (hO2 : OrderingBySize ord eStar)
    (hgeStar : 2 ≤ edgeSize (eStar : Set (Fin n)))
    (hW : ((1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 - τ - 7 * tauQuarter τ / (K : ℝ))) *
        ((n : ℝ) ^ 2) / (sizeFactor τ K * ((edgeSize (eStar : Set (Fin n)) : ℝ) ^ 2)) ≤
      ((VolumeSet τ K ord eStar).card : ℝ))
    (hfin : (1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 - 1 / (edgeSize (eStar : Set (Fin n)) : ℝ)) ≥
      1 - τ - 7 * tauQuarter τ / (K : ℝ))
    (hq : (0 : ℝ) ≤ 1 - τ - 7 * tauQuarter τ / (K : ℝ)) :
    volBound τ K ≤ Hypergraph.volume 𝓗 (VolumeSet τ K ord eStar) := by
  classical
  let W : Finset 𝓗 := VolumeSet τ K ord eStar
  let A : ℝ := sizeFactor τ K
  let r : ℝ := (edgeSize (eStar : Set (Fin n)) : ℝ)
  let q : ℝ := 1 - τ - 7 * tauQuarter τ / (K : ℝ)
  let u : ℝ := 1 - τ - 2 * Real.sqrt τ / (K : ℝ)
  let D : ℝ := (n : ℝ) * ((n - 1 : ℕ) : ℝ)
  let num : ℝ := W.sum (fun e : 𝓗 =>
    (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1))
  have hApos : (0 : ℝ) < A := by
    dsimp [A]
    have h1 : (1 : ℝ) ≤ sizeFactor τ K := sizeFactor_ge_one τ K
    linarith
  have hr2 : (2 : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast hgeStar
  have hrpos : (0 : ℝ) < r := by linarith
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hDpos : (0 : ℝ) < D := by
    dsimp [D]
    have h1 : (0 : ℝ) < (n : ℝ) := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n
      linarith
    have h2 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      have h3 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
        have h3' : (1 : ℕ) ≤ n - 1 := by omega
        exact_mod_cast h3'
      linarith
    positivity
  have hrrm : (0 : ℝ) ≤ r * (r - 1) := by
    have hr1m : (0 : ℝ) ≤ r - 1 := by linarith
    exact mul_nonneg (le_of_lt hrpos) hr1m
  have hDfactor : (0 : ℝ) ≤ r * (r - 1) / D := div_nonneg hrrm (le_of_lt hDpos)
  -- volume = num/D:
  have hvol : Hypergraph.volume 𝓗 (VolumeSet τ K ord eStar) = num / D := by
    dsimp [num, D, W]
    rfl
  -- numerator bound:
  have hsum := blockVI_volume_sum_ge τ K ord eStar hO2 hr1
  have hnum : r * (r - 1) * ((W.card : ℝ)) ≤ num := by
    simpa [W, num, r, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hA1 : r * (r - 1) * ((W.card : ℝ)) / D ≤ num / D :=
    div_le_div_of_nonneg_right hnum (le_of_lt hDpos)
  have hvolA : r * (r - 1) * ((W.card : ℝ)) / D ≤ Hypergraph.volume 𝓗 (VolumeSet τ K ord eStar) := by
    rw [hvol]
    exact hA1
  -- |W|-lower bound applied:
  have hWc : u * q * ((n : ℝ) ^ 2) / (A * r ^ 2) ≤ (W.card : ℝ) := by
    simpa [W, A, r, q, u] using hW
  have hWstep : (u * q * ((n : ℝ) ^ 2) / (A * r ^ 2)) * (r * (r - 1) / D) ≤
      (W.card : ℝ) * (r * (r - 1)) / D := by
    have hm := mul_le_mul_of_nonneg_right hWc hDfactor
    -- normalize RHS: (card)·(r(r−1)/D) = (card·r(r−1))/D
    have hEq : (W.card : ℝ) * (r * (r - 1) / D) = (W.card : ℝ) * (r * (r - 1)) / D := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rwa [hEq] at hm
  have hMidEq : (u * q * ((n : ℝ) ^ 2) / (A * r ^ 2)) * (r * (r - 1) / D) =
      (u * q) * (((n : ℝ) ^ 2) / D) * ((r - 1) / (A * r)) := by
    field_simp [hApos.ne', hrpos.ne', hDpos.ne']
  have hfrac : (1 : ℝ) ≤ ((n : ℝ) ^ 2) / D := by
    have hcs := blockVI_cast_sub_one h2n
    have hfg := blockVI_frac_n_sub_one_ge h2n
    dsimp [D]
    rw [hcs]
    have h1 : (0 : ℝ) < (n : ℝ) := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n
      linarith
    have h2 : (0 : ℝ) < (n : ℝ) - 1 := by
      have h3 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n
      linarith
    have hEq2 : (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) = (n : ℝ) / ((n : ℝ) - 1) := by
      field_simp [ne_of_gt h1, ne_of_gt h2]
    rwa [hEq2]
  have hcpos : (0 : ℝ) < 1 - 1 / r := by
    have h3 : (1 : ℝ) < r := by linarith
    have hdiv : 1 / r < 1 := (div_lt_one hrpos).2 h3
    linarith
  have hq0 : (0 : ℝ) ≤ q := by simpa [q] using hq
  have hu : (0 : ℝ) ≤ u := by
    have hfinL : q ≤ u * (1 - 1 / r) := by
      simpa [u, q, r] using hfin
    have hdiv : q / (1 - 1 / r) ≤ u := (div_le_iff₀ hcpos).mpr hfinL
    exact le_trans (div_nonneg hq0 (le_of_lt hcpos)) hdiv
  have huq : (0 : ℝ) ≤ u * q := mul_nonneg hu hq0
  have hXpos : (0 : ℝ) ≤ (r - 1) / (A * r) := by
    have hr1m : (0 : ℝ) ≤ r - 1 := by linarith
    have hAr : (0 : ℝ) < A * r := mul_pos hApos hrpos
    exact div_nonneg hr1m (le_of_lt hAr)
  -- volume ≥ Wcard·r(r−1)/D ≥ (u·q·n²/(A r²))·(r(r−1)/D) = (u·q)·(n²/D)·X, X := (r−1)/(A·r):
  have hmid : (u * q) * (((n : ℝ) ^ 2) / D) * ((r - 1) / (A * r)) ≤
      (W.card : ℝ) * (r * (r - 1)) / D := by
    rw [← hMidEq]
    exact hWstep
  have hvolA' : (W.card : ℝ) * (r * (r - 1)) / D ≤ Hypergraph.volume 𝓗 (VolumeSet τ K ord eStar) := by
    have hEq : (W.card : ℝ) * (r * (r - 1)) / D = r * (r - 1) * ((W.card : ℝ)) / D := by ring
    rwa [hEq]
  have hchain1 : (u * q) * (((n : ℝ) ^ 2) / D) * ((r - 1) / (A * r)) ≤
      Hypergraph.volume 𝓗 (VolumeSet τ K ord eStar) := hmid.trans hvolA'
  -- drop the n²/D ≥ 1 factor:
  have h1frac : (u * q) * 1 * ((r - 1) / (A * r)) ≤
      (u * q) * (((n : ℝ) ^ 2) / D) * ((r - 1) / (A * r)) := by
    have h0 := mul_le_mul_of_nonneg_left hfrac huq
    -- (u q)·1 ≤ (u q)·(n²/D); multiply by X ≥ 0:
    exact mul_le_mul_of_nonneg_right h0 hXpos
  have hXle : (u * q) * ((r - 1) / (A * r)) ≤ Hypergraph.volume 𝓗 (VolumeSet τ K ord eStar) := by
    have hEq1 : (u * q) * 1 * ((r - 1) / (A * r)) = (u * q) * ((r - 1) / (A * r)) := by ring
    have h1' := h1frac
    rw [hEq1] at h1'
    exact h1'.trans hchain1
  -- final margin: q²/A = (q/A)·q ≤ (q/A)·(u·(r−1)/r) = u·q·(r−1)/(A·r) = (u·q)·X:
  have hcm : (r - 1) / r = 1 - 1 / r := by
    field_simp [hrpos.ne']
  have hfinL : q ≤ u * (1 - 1 / r) := by
    simpa [u, q, r] using hfin
  have hfin2 : q ≤ u * ((r - 1) / r) := by
    rwa [← hcm] at hfinL
  have hqA : (0 : ℝ) ≤ q / A := div_nonneg hq0 (le_of_lt hApos)
  have hlow : (q / A) * q ≤ (q / A) * (u * ((r - 1) / r)) :=
    mul_le_mul_of_nonneg_left hfin2 hqA
  have hEqA : (q / A) * (u * ((r - 1) / r)) = u * q * (r - 1) / (A * r) := by
    field_simp [hApos.ne', hrpos.ne']
  have hR : u * q * (r - 1) / (A * r) = (u * q) * ((r - 1) / (A * r)) := by
    field_simp [hApos.ne', hrpos.ne']
  calc
    volBound τ K = q ^ 2 / A := by simp [volBound, q, A]
    _ = (q / A) * q := by ring
    _ ≤ (q / A) * (u * ((r - 1) / r)) := hlow
    _ = u * q * (r - 1) / (A * r) := hEqA
    _ = (u * q) * ((r - 1) / (A * r)) := hR
    _ ≤ Hypergraph.volume 𝓗 (VolumeSet τ K ord eStar) := hXle

/-! ## Reordering-lemma assembly, part 1 (proved): the margin block and its
transfer

`ReorderingInstance` now carries the explicit size margins `ReorderingMargins
r₁ τ K` (the concrete `0 < 1/r₁ ≪ τ, 1/K`): `0 < q`, `1 ≤ τ(r₁−1)`,
`K ≤ τ^{1/4}(r₁−1)`, `1+K√τ ≤ r₁/2`, `2(1+K√τ) ≤ K²√τ·r₁`,
`(sizeFactor−1−K√τ)·r₁² ≥ 1`, `u(1−1/r₁) ≥ q`.  Accessors `rm_q_pos` …
`rm_hfin`, and the transfers to the size `s` of any edge (`s ≥ (r₁ : ℝ)`):
`rm_mar_of_le` (the opening margin lemma `K ≤ τ^{1/4}(s−1)`), `rm_M1_of_le`,
`rm_M2_of_le` (needs `1 ≤ K`), `rm_Amar_of_le` (needs `τ ≤ 1`, `1 ≤ K`),
`rm_hfin_of_le` (needs `2 ≤ r₁`; derives `u ≥ 0` from `q > 0` and the
r₁-margin).  These supply the Block V/VI margin hypotheses at `r := |e*|`.
Remaining: the assembly of `ReorderingInstance` from
`exists_minimal_admissible_of_fintype` + `minimal_admissible_dichotomy` +
`blockIII_setup` + `blockV_X_bound` + `blockV_app2` + `blockVI_B_lower` +
`blockVI_W_lower` + `blockVI_WVolume` (the margins/transfer lemmas above
are its inputs). -/

-- accessors for the margin block (q, and the r-margins at r := (r₁:ℝ)):
lemma rm_q_pos {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K) :
    0 < 1 - τ - 7 * tauQuarter τ / (K : ℝ) := hm.1
lemma rm_tau_margin {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K) :
    (1 : ℝ) ≤ τ * (((r₁ : ℝ)) - 1) := hm.2.1
lemma rm_mar {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K) :
    (K : ℝ) ≤ tauQuarter τ * (((r₁ : ℝ)) - 1) := hm.2.2.1
lemma rm_M1 {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K) :
    (1 + (K : ℝ) * Real.sqrt τ) ≤ ((r₁ : ℝ)) / 2 := hm.2.2.2.1
lemma rm_M2 {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K) :
    (2 * (1 + (K : ℝ) * Real.sqrt τ) ≤ (K : ℝ) ^ 2 * Real.sqrt τ * ((r₁ : ℝ))) := hm.2.2.2.2.1
lemma rm_Amar {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K) :
    (1 : ℝ) ≤ (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (((r₁ : ℝ)) ^ 2) := hm.2.2.2.2.2.1
lemma rm_hfin {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K) :
    ((1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 - 1 / ((r₁ : ℝ))) ≥
      1 - τ - 7 * tauQuarter τ / (K : ℝ)) := hm.2.2.2.2.2.2

-- transfer each margin from r₁ to any s ≥ (r₁:ℝ) (the size of an edge):

lemma rm_mar_of_le {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K)
    (hτ0 : 0 < τ) (s : ℝ) (hr₁s : ((r₁ : ℝ)) ≤ s) :
    (K : ℝ) ≤ tauQuarter τ * (s - 1) := by
  have ht0 : 0 < tauQuarter τ := tauQuarter_pos hτ0
  have h1 := rm_mar hm
  have h2 : ((r₁ : ℝ)) - 1 ≤ s - 1 := by linarith
  have h3 : tauQuarter τ * (((r₁ : ℝ)) - 1) ≤ tauQuarter τ * (s - 1) :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt ht0)
  exact h1.trans h3

lemma rm_M1_of_le {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K)
    (s : ℝ) (hr₁s : ((r₁ : ℝ)) ≤ s) :
    (1 + (K : ℝ) * Real.sqrt τ) ≤ s / 2 := by
  have h1 := rm_M1 hm
  have h2 : ((r₁ : ℝ)) / 2 ≤ s / 2 := by linarith
  exact h1.trans h2

lemma rm_M2_of_le {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K)
    (hK : (1 : ℝ) ≤ K) (s : ℝ) (hr₁s : ((r₁ : ℝ)) ≤ s) :
    (2 * (1 + (K : ℝ) * Real.sqrt τ) ≤ (K : ℝ) ^ 2 * Real.sqrt τ * s) := by
  have h1 := rm_M2 hm
  have hnon : (0 : ℝ) ≤ (K : ℝ) ^ 2 * Real.sqrt τ := by
    have hK0 : (0 : ℝ) ≤ K := by linarith
    exact mul_nonneg (sq_nonneg (K : ℝ)) (Real.sqrt_nonneg τ)
  have h2 : (K : ℝ) ^ 2 * Real.sqrt τ * ((r₁ : ℝ)) ≤ (K : ℝ) ^ 2 * Real.sqrt τ * s := by
    exact mul_le_mul_of_nonneg_left hr₁s hnon
  linarith

lemma rm_Amar_of_le {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K)
    (hτ1 : τ ≤ 1) (hK : (1 : ℝ) ≤ K) (s : ℝ) (hr₁s : ((r₁ : ℝ)) ≤ s) :
    (1 : ℝ) ≤ (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (s ^ 2) := by
  have h1 := rm_Amar hm
  have hM : (0 : ℝ) ≤ sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ := by
    have hS := sizeFactor_ge_one_sqrt hτ1 hK
    -- A ≥ 1 + K√τ  ⟹  A − 1 − K√τ ≥ 0
    have : (1 + (K : ℝ) * Real.sqrt τ) ≤ sizeFactor τ K := hS
    linarith
  have hsq : ((r₁ : ℝ)) ^ 2 ≤ s ^ 2 := by
    have hr0 : (0 : ℝ) ≤ (r₁ : ℝ) := by positivity
    exact pow_le_pow_left₀ hr0 hr₁s 2
  have h2 : (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (((r₁ : ℝ)) ^ 2) ≤
      (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (s ^ 2) :=
    mul_le_mul_of_nonneg_left hsq hM
  exact h1.trans h2

lemma rm_hfin_of_le {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K)
    (h2r1 : 2 ≤ r₁) (s : ℝ) (hr₁s : ((r₁ : ℝ)) ≤ s) :
    ((1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 - 1 / s) ≥
      1 - τ - 7 * tauQuarter τ / (K : ℝ)) := by
  have hfin := rm_hfin hm
  have hqpos : (0 : ℝ) < 1 - τ - 7 * tauQuarter τ / (K : ℝ) := rm_q_pos hm
  have hr1pos : (0 : ℝ) < (r₁ : ℝ) := by
    have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast h2r1
    linarith
  have hc1 : (0 : ℝ) < 1 - 1 / ((r₁ : ℝ)) := by
    have hnum : (0 : ℝ) < (r₁ : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast h2r1
      linarith
    have hEq : 1 - 1 / (r₁ : ℝ) = ((r₁ : ℝ) - 1) / (r₁ : ℝ) := by
      field_simp [hr1pos.ne']
    rw [hEq]
    exact div_pos hnum hr1pos
  have hspos : (0 : ℝ) < s := by linarith
  -- u ≥ 0: q ≤ u·(1−1/r₁), q > 0, (1−1/r₁) > 0
  let u : ℝ := 1 - τ - 2 * Real.sqrt τ / (K : ℝ)
  let q : ℝ := 1 - τ - 7 * tauQuarter τ / (K : ℝ)
  have hu : (0 : ℝ) ≤ u := by
    have hfinL : q ≤ u * (1 - 1 / ((r₁ : ℝ))) := by
      simpa [u, q] using hfin
    have hdivu : q / (1 - 1 / ((r₁ : ℝ))) ≤ u := (div_le_iff₀ hc1).mpr hfinL
    have hpos : (0 : ℝ) < q / (1 - 1 / ((r₁ : ℝ))) := div_pos (by simpa [q] using hqpos) hc1
    exact le_trans (le_of_lt hpos) hdivu
  -- 1 − 1/r₁ ≤ 1 − 1/s (since r₁ ≤ s, both positive)
  have hc : 1 - 1 / ((r₁ : ℝ)) ≤ 1 - 1 / s := by
    have hdiv : 1 / s ≤ 1 / ((r₁ : ℝ)) := (div_le_div_iff₀ hspos hr1pos).mpr (by simpa using hr₁s)
    linarith
  have hstep : q ≤ u * (1 - 1 / s) := by
    have h1 : q ≤ u * (1 - 1 / ((r₁ : ℝ))) := by simpa [u, q] using hfin
    have h2 : u * (1 - 1 / ((r₁ : ℝ))) ≤ u * (1 - 1 / s) :=
      mul_le_mul_of_nonneg_left hc hu
    exact h1.trans h2
  simpa [u, q] using hstep

/-! ## Reordering lemma (Lemma 6.2) PROVED

`reorderingLemma`: from the size margins `ReorderingMargins r₁ τ K` (the
explicit `0 < 1/r₁ ≪ τ, 1/K`), every linear hypergraph on `Fin n` whose
edges all have size `≥ r₁` admits a good ordering or a volume witness.
Proof: the empty case is trivial (any ordering is good); otherwise take the
minimal admissible pair (`exists_minimal_admissible_of_fintype` +
`minimal_admissible_dichotomy`): either `GoodOrdering` (done) or
`rank eStar ≥ 1` ∧ `fwddeg(e*) > (1−τ)n` ∧ `BlockIVStatement`; in the
latter case the margin transfers (`rm_…_of_le` at `s := |eStar|`) give the
Block V/VI inputs, and `blockV_X_bound` (eq. (6.4)) + `blockVI_W_lower` +
`blockVI_WVolume` give the volume of `W := VolumeSet`; with
`blockIII_setup` (W1, `W ⊆ prefix`) and the admissible pair's (O1)/(O2)
this is exactly a `VolumeWitness`. -/

/-- **Reordering lemma (Lemma 6.2), proved**: from the size margins
`ReorderingMargins r₁ τ K` (the explicit `0 < 1/r₁ ≪ τ, 1/K`) every linear
hypergraph whose edges all have size `≥ r₁` admits a good ordering or a
volume witness. -/
theorem reorderingLemma (n r₁ : ℕ) (τ : ℝ) (K : ℕ) (𝓗 : Hypergraph (Fin n)) :
    ReorderingInstance n r₁ τ K 𝓗 := by
  classical
  intro hant hlin hsize
  rcases hant with ⟨h2n, h2r1, hτ0, hτ1', hK, hmarg⟩
  have hτ1 : τ ≤ 1 := le_of_lt hτ1'
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  by_cases hE : Nonempty 𝓗
  · -- nonempty: take the minimal admissible pair
    rcases exists_minimal_admissible_of_fintype (𝓗 := 𝓗) τ with ⟨k, ord, eStar, hadm, hmin⟩
    have hdec := minimal_admissible_dichotomy ord τ eStar hadm hτ1' hmin
    rcases hdec with hgood | hvol
    · exact ⟨k, ord, Or.inl hgood⟩
    · rcases hvol with ⟨hrank, hfwd, hIV⟩
      let r : ℝ := (edgeSize (eStar : Set (Fin n)) : ℝ)
      have hs : ((r₁ : ℝ)) ≤ r := by
        dsimp [r]
        exact hsize eStar eStar.2
      have hge2 : 2 ≤ edgeSize (eStar : Set (Fin n)) := by
        have h2r : (2 : ℝ) ≤ r := by
          have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast h2r1
          linarith
        have h2rr : (2 : ℝ) ≤ (edgeSize (eStar : Set (Fin n)) : ℝ) := by
          dsimp [r] at h2r
          exact h2r
        exact_mod_cast h2rr
      have hq0 : (0 : ℝ) ≤ 1 - τ - 7 * tauQuarter τ / (K : ℝ) := le_of_lt (rm_q_pos hmarg)
      have hM1r : 1 + (K : ℝ) * Real.sqrt τ ≤ r / 2 := rm_M1_of_le hmarg r hs
      have hM2r : 2 * (1 + (K : ℝ) * Real.sqrt τ) ≤ (K : ℝ) ^ 2 * Real.sqrt τ * r :=
        rm_M2_of_le hmarg hKr r hs
      have hmar_r : (K : ℝ) ≤ tauQuarter τ * (r - 1) := rm_mar_of_le hmarg hτ0 r hs
      have hAmar_r : (1 : ℝ) ≤ (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (r ^ 2) :=
        rm_Amar_of_le hmarg hτ1 hKr r hs
      have hfin_r : (1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 - 1 / r) ≥
          1 - τ - 7 * tauQuarter τ / (K : ℝ) :=
        rm_hfin_of_le hmarg h2r1 r hs
      have htau_r : (1 : ℝ) ≤ τ * (r - 1) := by
        have h1 := rm_tau_margin hmarg
        have h2 : τ * (((r₁ : ℝ)) - 1) ≤ τ * (r - 1) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hτ0)
          linarith
        exact h1.trans h2
      have hmX : (1 - τ) * (n : ℝ) ≤ (precedingDegree 𝓗 ord eStar : ℝ) :=
        le_of_lt hfwd
      have hO2 : OrderingBySize ord eStar := hadm.2
      have hXb := blockV_X_bound (𝓗 := 𝓗) hlin ord τ K eStar hτ0 hKr hO2 hge2
        (by simpa [r] using htau_r) (by simpa [r] using hmX)
      -- the |X| bound in the form blockVI_W_lower consumes:
      have hXb' : ((1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (n : ℝ)) ≤
          ((XSmall τ K ord eStar).card : ℝ) := by
        simpa using hXb
      have hWb := blockVI_W_lower (𝓗 := 𝓗) hlin h2n ord τ K eStar hτ0 hτ1 hKr hO2 hge2
        (by simpa [r] using hM1r) (by simpa [r] using hM2r) (by simpa [r] using hmar_r)
        (by simpa [r] using hAmar_r) hq0 hXb' hIV
      have hvol := blockVI_WVolume (𝓗 := 𝓗) h2n ord τ K eStar hO2 hge2 hWb
        (by simpa [r] using hfin_r) hq0
      let W : Finset 𝓗 := VolumeSet τ K ord eStar
      have hsetup := blockIII_setup τ K ord eStar hO2
      have hWitness : VolumeWitness τ K ord := by
        refine ⟨eStar, W, hsetup.2.2, hsetup.2.1, hvol, hadm.1, hadm.2,
          volumeSet_mem_self τ K ord eStar⟩
      exact ⟨k, ord, Or.inr hWitness⟩
  · -- empty hypergraph: any ordering is good
    have hcard0 : Fintype.card 𝓗 = 0 := by
      have hpos : 0 < Fintype.card 𝓗 ↔ Nonempty 𝓗 := Fintype.card_pos_iff
      by_contra h
      have : 0 < Fintype.card 𝓗 := by omega
      exact hE (hpos.mp this)
    refine ⟨Fintype.card 𝓗, Fintype.equivFin 𝓗, Or.inl ?_⟩
    intro e
    exfalso
    exact hE ⟨e⟩

/-! ## Theorem 6.1 preparation, step 1 (proved): the subfamily firing
template

`reorderingLemma_of_subfamily`: the reordering lemma applied to any
subfamily `𝓖 ⊆ 𝓗` of a linear hypergraph whose edges all have size
`≥ r₁` — linearity passes by `hlin.mono`, the size bound by `hsub`, the
margins `ReorderingMargins r₁ τ K` are unchanged — giving
`∃ ord : 𝓖 ≃ Fin k, GoodOrdering τ ord ∨ VolumeWitness τ K ord`.
This is the exact shape of the three applications of Lemma 6.2 inside the
proof of Theorem 6.1 (Fig. 3), where `𝓖` is successively `𝓗′`, `𝓗₁^left`
and `𝓗₃`. -/

/-- **Restriction/firing template**: the reordering lemma applied to a
subfamily `𝓖 ⊆ 𝓗` of a linear hypergraph whose edges all have size
`≥ r₁` — linearity and the size bound pass to `𝓖`
(`hlin.mono`, `hsub`), the margins `ReorderingMargins r₁ τ K` are the
same, so `∃ ord : 𝓖 ≃ Fin k, GoodOrdering τ ord ∨ VolumeWitness τ K ord`.
This is the shape of every application of Lemma 6.2 inside the proof of
Theorem 6.1 (Fig. 3): each subfamily `𝓗′`, `𝓗₁^left`, `𝓗₃` is an
instance. -/
theorem reorderingLemma_of_subfamily {n r₁ : ℕ} (τ : ℝ) (K : ℕ)
    {𝓗 𝓖 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    (h2n : 2 ≤ n) (h2r1 : 2 ≤ r₁) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hK : (1 : ℕ) ≤ K) (hmarg : ReorderingMargins r₁ τ K)
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : Set (Fin n), e ∈ 𝓗 →
      (r₁ : ℝ) ≤ (edgeSize e : ℝ)) :
    ∃ k : ℕ, ∃ ord : 𝓖 ≃ Fin k,
      GoodOrdering τ ord ∨ VolumeWitness τ K ord := by
  classical
  have hlinG : 𝓖.IsLinear := hlin.mono hsub
  have hsizeG : ∀ e : Set (Fin n), e ∈ 𝓖 → (r₁ : ℝ) ≤ (edgeSize e : ℝ) := by
    intro e heG
    exact hsize e (hsub heG)
  have hinst := reorderingLemma (n := n) (r₁ := r₁) (τ := τ) (K := K) (𝓗 := 𝓖)
  exact hinst ⟨h2n, ⟨h2r1, ⟨hτ0, ⟨hτ1, ⟨hK, hmarg⟩⟩⟩⟩⟩ hlinG hsizeG

/-! ## Theorem 6.1 preparation, step 2 (proved): margins follow from large
r₁

The per-margin sufficient conditions of the Fig. 3 applications:
`margin_tau_of_bound` (`(r₁ : ℝ) ≥ 1 + 1/τ` gives `1 ≤ τ(r₁−1)`),
`margin_mar_of_bound` (`(r₁ : ℝ) ≥ 1 + K/τ^{1/4}` gives
`K ≤ τ^{1/4}(r₁−1)`), `margin_M1_of_bound`, `margin_M2_of_bound` (the
divided form), and the package
`ReorderingMargins_follows_from_large`: given `0 < q` and the seven raw
margin bounds at `r := (r₁ : ℝ)` (each exactly the margin
`hL1…hL6`), `ReorderingMargins r₁ τ K` holds.  This is the discharge
template: in every Fig. 3 application, `r₁ ≥ R(τ,K)` with `R` large
enough makes each `hLᵢ` true. -/

/-- `1 ≤ τ(r₁−1)` follows from `(r₁ : ℝ) ≥ 1 + 1/τ` (τ > 0). -/
lemma margin_tau_of_bound {r₁ : ℕ} {τ : ℝ} (hτ0 : 0 < τ)
    (hb : (1 : ℝ) + 1 / τ ≤ (r₁ : ℝ)) :
    (1 : ℝ) ≤ τ * (((r₁ : ℝ)) - 1) := by
  have h2 : 1 / τ ≤ (r₁ : ℝ) - 1 := by linarith
  have hEq : τ * (1 / τ) = 1 := by field_simp [ne_of_gt hτ0]
  have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt hτ0)
  calc
    (1 : ℝ) = τ * (1 / τ) := hEq.symm
    _ ≤ τ * ((r₁ : ℝ) - 1) := hmul

/-- `K ≤ τ^{1/4}(r₁−1)` follows from `(r₁ : ℝ) ≥ 1 + K/τ^{1/4}`. -/
lemma margin_mar_of_bound {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hτ0 : 0 < τ)
    (hb : (1 : ℝ) + (K : ℝ) / tauQuarter τ ≤ (r₁ : ℝ)) :
    (K : ℝ) ≤ tauQuarter τ * (((r₁ : ℝ)) - 1) := by
  have ht0 : 0 < tauQuarter τ := tauQuarter_pos hτ0
  have h1 : (K : ℝ) / tauQuarter τ ≤ (r₁ : ℝ) - 1 := by linarith
  have hEq : tauQuarter τ * ((K : ℝ) / tauQuarter τ) = (K : ℝ) := by
    field_simp [ne_of_gt ht0]
  have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt ht0)
  calc
    (K : ℝ) = tauQuarter τ * ((K : ℝ) / tauQuarter τ) := hEq.symm
    _ ≤ tauQuarter τ * ((r₁ : ℝ) - 1) := hmul

/-- `1+K√τ ≤ r₁/2` follows from `2(1+K√τ) ≤ (r₁ : ℝ)`. -/
lemma margin_M1_of_bound {r₁ : ℕ} {τ : ℝ} {K : ℕ}
    (hb : (2 * (1 + (K : ℝ) * Real.sqrt τ)) ≤ (r₁ : ℝ)) :
    (1 + (K : ℝ) * Real.sqrt τ) ≤ ((r₁ : ℝ)) / 2 := by
  nlinarith

/-- `2(1+K√τ) ≤ K²√τ·r₁` follows from the divided bound (K > 0, τ > 0). -/
lemma margin_M2_of_bound {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hτ0 : 0 < τ) (hK : (1 : ℝ) ≤ K)
    (hb : (2 * (1 + (K : ℝ) * Real.sqrt τ)) / ((K : ℝ) ^ 2 * Real.sqrt τ) ≤ (r₁ : ℝ)) :
    (2 * (1 + (K : ℝ) * Real.sqrt τ) ≤ (K : ℝ) ^ 2 * Real.sqrt τ * ((r₁ : ℝ))) := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hden : 0 < (K : ℝ) ^ 2 * Real.sqrt τ := by
    exact mul_pos (sq_pos_of_pos hK0) (Real.sqrt_pos.2 hτ0)
  have hm := mul_le_mul_of_nonneg_right hb (le_of_lt hden)
  have h1 : (2 * (1 + (K : ℝ) * Real.sqrt τ) / ((K : ℝ) ^ 2 * Real.sqrt τ)) *
      ((K : ℝ) ^ 2 * Real.sqrt τ) = 2 * (1 + (K : ℝ) * Real.sqrt τ) := by
    field_simp [ne_of_gt hden]
  have h2 : ((r₁ : ℝ)) * ((K : ℝ) ^ 2 * Real.sqrt τ) =
      (K : ℝ) ^ 2 * Real.sqrt τ * ((r₁ : ℝ)) := by ring
  calc
    2 * (1 + (K : ℝ) * Real.sqrt τ)
        = (2 * (1 + (K : ℝ) * Real.sqrt τ) / ((K : ℝ) ^ 2 * Real.sqrt τ)) *
            ((K : ℝ) ^ 2 * Real.sqrt τ) := h1.symm
    _ ≤ ((r₁ : ℝ)) * ((K : ℝ) ^ 2 * Real.sqrt τ) := hm
    _ = (K : ℝ) ^ 2 * Real.sqrt τ * ((r₁ : ℝ)) := h2

/-- **ReorderingMargins follow from per-margin lower bounds**: with
`0 < q` and each raw lower bound (in `(r₁ : ℝ)`) the margin block holds.
Each hypothesis is exactly the corresponding margin at `r := (r₁ : ℝ)`
— this packages the `r₁ ≥ R_i(τ,K)` discharges of the Fig. 3
applications. -/
theorem ReorderingMargins_follows_from_large (r₁ : ℕ) (τ : ℝ) (K : ℕ)
    (hq : 0 < 1 - τ - 7 * tauQuarter τ / (K : ℝ))
    (hL1 : (1 : ℝ) ≤ τ * (((r₁ : ℝ)) - 1))
    (hL2 : (K : ℝ) ≤ tauQuarter τ * (((r₁ : ℝ)) - 1))
    (hL3 : 1 + (K : ℝ) * Real.sqrt τ ≤ ((r₁ : ℝ)) / 2)
    (hL4 : 2 * (1 + (K : ℝ) * Real.sqrt τ) ≤ (K : ℝ) ^ 2 * Real.sqrt τ * ((r₁ : ℝ)))
    (hL5 : (1 : ℝ) ≤ (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (((r₁ : ℝ)) ^ 2))
    (hL6 : ((1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 - 1 / ((r₁ : ℝ))) ≥
      1 - τ - 7 * tauQuarter τ / (K : ℝ))) :
    ReorderingMargins r₁ τ K := by
  dsimp [ReorderingMargins]
  exact ⟨hq, ⟨hL1, ⟨hL2, ⟨hL3, ⟨hL4, ⟨hL5, hL6⟩⟩⟩⟩⟩⟩

/-! ## Theorem 6.1 preparation, step 3a (proved): App-3 constants and
bounds

The App-3 constants `app3tau := 1 − 1/2000`, `app3K := 2000²` and the
bounds on `t := τ^{1/4}`, `√τ` needed by the numeric margin discharge:
`app3_tau_pos` (`0 < τ`), `app3_tauQuarter_ge_half` (`1/2 ≤ t`),
`app3_tauQuarter_le_one` (`t ≤ 1`), `app3_sqrt_ge_quarter`
(`1/4 ≤ √τ`), `app3_sqrt_le_one` (`√τ ≤ 1`).  (All via `sqrt`
monotonicity from `1/16 ≤ τ ≤ 1`, with `sqrt(1/16) = 1/4`,
`sqrt(1/4) = 1/2` by `Real.sqrt_sq`.)  These feed `app3_margins`
(`ReorderingMargins r₁ app3tau app3K` for `r₁ ≥ 10⁸`), the numeric
`hLᵢ`-discharge that makes the App-3 firing of
`reorderingLemma_of_subfamily` fire. -/

/-- App 3 constants: τ₃ = 1−1/2000, K₃ = 2000². -/
def app3tau : ℝ := 1 - 1 / 2000
def app3K : ℕ := 2000 ^ 2

/-- `1/2 ≤ √√τ₃` (τ₃ ≥ 1/16 and √√ monotone; √√(1/16) = 1/2). -/
lemma app3_tauQuarter_ge_half : (1 / 2 : ℝ) ≤ tauQuarter app3tau := by
  have h1 : (1 / 16 : ℝ) ≤ app3tau := by
    dsimp [app3tau]
    norm_num
  -- sqrt monotone twice:
  have hs1 : (1 / 4 : ℝ) ≤ Real.sqrt app3tau := by
    have hs1' : Real.sqrt (1 / 16 : ℝ) ≤ Real.sqrt app3tau := Real.sqrt_le_sqrt h1
    have hsq : Real.sqrt (1 / 16 : ℝ) = (1 / 4 : ℝ) := by
      have hsq' : (1 / 4 : ℝ) ^ 2 = 1 / 16 := by norm_num
      rw [← hsq']
      exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [hsq] at hs1'
  have hs2 : Real.sqrt (1 / 4 : ℝ) ≤ Real.sqrt (Real.sqrt app3tau) := Real.sqrt_le_sqrt hs1
  have hsq2 : Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
    have hsq2' : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
    rw [← hsq2']
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  unfold tauQuarter
  rwa [hsq2] at hs2

/-- `√τ₃ ≤ 1`. -/
lemma app3_sqrt_le_one : Real.sqrt app3tau ≤ 1 := by
  have h1 : app3tau ≤ 1 := by dsimp [app3tau]; norm_num
  have hs := Real.sqrt_le_sqrt h1
  simpa using hs

/-- `τ₃^{1/4} ≤ 1`. -/
lemma app3_tauQuarter_le_one : tauQuarter app3tau ≤ 1 := by
  have h1 : Real.sqrt app3tau ≤ 1 := app3_sqrt_le_one
  have hs := Real.sqrt_le_sqrt h1
  unfold tauQuarter
  simpa using hs

/-- `τ₃ > 0`. -/
lemma app3_tau_pos : 0 < app3tau := by
  dsimp [app3tau]
  norm_num

/-- `√τ₃ ≥ 1/4`. -/
lemma app3_sqrt_ge_quarter : (1 / 4 : ℝ) ≤ Real.sqrt app3tau := by
  have h1 : (1 / 16 : ℝ) ≤ app3tau := by dsimp [app3tau]; norm_num
  have hs := Real.sqrt_le_sqrt h1
  have hsq : Real.sqrt (1 / 16 : ℝ) = (1 / 4 : ℝ) := by
    have hsq' : (1 / 4 : ℝ) ^ 2 = 1 / 16 := by norm_num
    rw [← hsq']
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rwa [hsq] at hs

/-! ## Theorem 6.1 preparation, step 3b (proved): App-3 margin discharge

`app3_margins r₁`: for `(r₁ : ℝ) ≥ 10⁸`, `ReorderingMargins r₁ app3tau
app3K` holds at the App-3 parameters (`app3tau = 1−1/2000`, `app3K =
2000²`).  Each margin is discharged from the committed root bounds
(`1/2 ≤ τ^{1/4}`, `τ^{1/4} ≤ 1`, `1/4 ≤ √τ ≤ 1`, `τ ≥ 1/16`, `K₃ =
4·10⁶`) by `margin_tau_of_bound`/`margin_mar_of_bound` or direct numeric
reasoning: `hL1` (`r₁ ≥ 1+1/τ`), `hL2` (`r₁ ≥ 1 + K/t`), `hL3`
(`r₁ ≥ 2(1+K)`), `hL4`/`hL5` (from `√τ ≥ 1/4`, `t ≥ 1/2`), `hL6`
(`q ≤ u(1−1/r)` by the explicit chain
`u(1−1/r)−q = (u−q)−u/r ≥ (u−q)−1/r ≥ (u−q)/2 ≥ 0` using `u ≤ 1`,
`1/r ≤ (u−q)/2` via `r ≥ 2K`, and `u−q ≥ (5/2)/K`), and `hq`
(`q ≥ 1993/4000000 > 0`).  With `app3_margins`, the App-3 firing of
`reorderingLemma_of_subfamily` on `𝓗₃` is a direct instantiation. -/

theorem app3_margins (r₁ : ℕ) (hR : (100000000 : ℝ) ≤ (r₁ : ℝ)) :
    ReorderingMargins r₁ app3tau app3K := by
  classical
  let r : ℝ := (r₁ : ℝ)
  have hR' : (100000000 : ℝ) ≤ r := by simpa [r] using hR
  have hτ0 : 0 < app3tau := app3_tau_pos
  have htge : (1 / 2 : ℝ) ≤ tauQuarter app3tau := app3_tauQuarter_ge_half
  have htle : tauQuarter app3tau ≤ 1 := app3_tauQuarter_le_one
  have hsqge : (1 / 4 : ℝ) ≤ Real.sqrt app3tau := app3_sqrt_ge_quarter
  have hsqle : Real.sqrt app3tau ≤ 1 := app3_sqrt_le_one
  have htauge : (1 / 16 : ℝ) ≤ app3tau := by
    dsimp [app3tau]
    norm_num
  have hKpos : (0 : ℝ) < (app3K : ℝ) := by
    dsimp [app3K]
    norm_num
  have hK0 : (0 : ℝ) ≤ (app3K : ℝ) := le_of_lt hKpos
  have hKbig : (2 : ℝ) ≤ (app3K : ℝ) := by dsimp [app3K]; norm_num
  -- hL1: 1 ≤ τ(r−1): 1/τ ≤ 16, r ≥ 17
  have hL1 : (1 : ℝ) ≤ app3tau * (r - 1) := by
    have h16 : 1 / app3tau ≤ (16 : ℝ) := by
      rw [div_le_iff₀ hτ0]
      nlinarith [htauge]
    have hb : 1 + 1 / app3tau ≤ r := by linarith
    exact margin_tau_of_bound hτ0 (by simpa [r] using hb)
  -- hL2: K ≤ t(r−1): 1/t ≤ 2, so K/t ≤ 2K ≤ r−1
  have hL2 : (app3K : ℝ) ≤ tauQuarter app3tau * (r - 1) := by
    have ht0 : 0 < tauQuarter app3tau := tauQuarter_pos hτ0
    have h1t : 1 / tauQuarter app3tau ≤ 2 := by
      rw [div_le_iff₀ ht0]
      nlinarith [htge]
    have hKt : (app3K : ℝ) / tauQuarter app3tau ≤ 2 * (app3K : ℝ) := by
      -- (K)·(1/t) ≤ K·2
      have hm := mul_le_mul_of_nonneg_left h1t hK0
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hm
    have hb : 1 + (app3K : ℝ) / tauQuarter app3tau ≤ r := by
      have h2 : 2 * (app3K : ℝ) + 1 ≤ r := by
        dsimp [r] at hR'
        have hK2 : (2 * (app3K : ℝ) + 1 : ℝ) ≤ (100000000 : ℝ) := by
          dsimp [app3K]
          norm_num
        linarith
      linarith
    exact margin_mar_of_bound hτ0 (by simpa [r] using hb)
  -- hL3: 1+K√τ ≤ r/2: √τ ≤ 1
  have hL3 : 1 + (app3K : ℝ) * Real.sqrt app3tau ≤ r / 2 := by
    have h1 : 1 + (app3K : ℝ) * Real.sqrt app3tau ≤ 1 + (app3K : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hsqle hK0
      nlinarith
    have h2 : 1 + (app3K : ℝ) ≤ r / 2 := by
      have hKv : (1 + (app3K : ℝ) : ℝ) ≤ (100000000 : ℝ) / 2 := by
        dsimp [app3K]
        norm_num
      nlinarith
    exact h1.trans h2
  -- hL4: 2(1+K√τ) ≤ K²√τ·r: √τ ≥ 1/4, r ≥ 1e8
  have hL4 : 2 * (1 + (app3K : ℝ) * Real.sqrt app3tau) ≤
      (app3K : ℝ) ^ 2 * Real.sqrt app3tau * r := by
    have hup : 2 * (1 + (app3K : ℝ) * Real.sqrt app3tau) ≤ 2 * (1 + (app3K : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hsqle hK0
      nlinarith
    have hbig : 2 * (1 + (app3K : ℝ)) ≤ (app3K : ℝ) ^ 2 * (1 / 4) * r := by
      have hlow : (2 * (1 + (app3K : ℝ)) : ℝ) ≤ (app3K : ℝ) ^ 2 * (1 / 4) * (100000000 : ℝ) := by
        dsimp [app3K]
        norm_num
      -- RHS monotone in r (factor ≥ 0):
      have hfac : (0 : ℝ) ≤ (app3K : ℝ) ^ 2 * (1 / 4) := by
        have h2 : (0 : ℝ) ≤ (app3K : ℝ) ^ 2 := sq_nonneg _
        positivity
      have hm2 := mul_le_mul_of_nonneg_left hR' hfac
      -- (K²/4)·r ≥ (K²/4)·1e8:
      nlinarith
    have hlow : (app3K : ℝ) ^ 2 * (1 / 4) * r ≤ (app3K : ℝ) ^ 2 * Real.sqrt app3tau * r := by
      have hm := mul_le_mul_of_nonneg_left hsqge (sq_nonneg (app3K : ℝ))
      -- (K²)·(1/4) ≤ K²·√τ ; multiply by r ≥ 0
      have hm2 := mul_le_mul_of_nonneg_right hm (by linarith : (0 : ℝ) ≤ r)
      -- order of multiplication: ((K²·1/4)·r) ≤ ((K²·√τ)·r)
      simpa [mul_assoc] using hm2
    exact hup.trans (hbig.trans hlow)
  -- hL5: (sizeFactor−1−K√τ)·r² ≥ 1: factor ≥ (3/2)K⁴ − K ≥ 1, r² ≥ 1
  have hL5 : (1 : ℝ) ≤ (sizeFactor app3tau app3K - 1 - (app3K : ℝ) * Real.sqrt app3tau) * (r ^ 2) := by
    have hA : ((3 / 2 : ℝ) * (app3K : ℝ) ^ 4) ≤ 3 * tauQuarter app3tau * (app3K : ℝ) ^ 4 := by
      have hm : (3 / 2 : ℝ) ≤ 3 * tauQuarter app3tau := by linarith
      have hm2 := mul_le_mul_of_nonneg_right hm (by positivity : (0 : ℝ) ≤ (app3K : ℝ) ^ 4)
      simpa [mul_assoc] using hm2
    have hB : (app3K : ℝ) * Real.sqrt app3tau ≤ (app3K : ℝ) := by
      simpa using (mul_le_mul_of_nonneg_left hsqle hK0)
    have hBig : (1 : ℝ) ≤ (3 / 2 : ℝ) * (app3K : ℝ) ^ 4 - (app3K : ℝ) := by
      dsimp [app3K]
      norm_num
    have hUnf : sizeFactor app3tau app3K - 1 - (app3K : ℝ) * Real.sqrt app3tau =
        3 * tauQuarter app3tau * (app3K : ℝ) ^ 4 - (app3K : ℝ) * Real.sqrt app3tau := by
      unfold sizeFactor
      ring
    have fge : (1 : ℝ) ≤ sizeFactor app3tau app3K - 1 - (app3K : ℝ) * Real.sqrt app3tau := by
      rw [hUnf]
      have hmid : (1 : ℝ) ≤ 3 * tauQuarter app3tau * (app3K : ℝ) ^ 4 - (app3K : ℝ) * Real.sqrt app3tau := by
        -- (3/2)K⁴ − K ≤ 3tK⁴ − K√τ
        have hlo : (3 / 2 : ℝ) * (app3K : ℝ) ^ 4 - (app3K : ℝ) ≤
            3 * tauQuarter app3tau * (app3K : ℝ) ^ 4 - (app3K : ℝ) * Real.sqrt app3tau := by
          nlinarith [hA, hB]
        exact hBig.trans hlo
      exact hmid
    have hr2 : (1 : ℝ) ≤ r ^ 2 := by
      have hr1' : (1 : ℝ) ≤ r := by
        dsimp [r] at hR'
        linarith
      have hmm := mul_le_mul hr1' hr1' (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ r)
      nlinarith
    have hmul1 : (1 : ℝ) * (r ^ 2) ≤ (sizeFactor app3tau app3K - 1 - (app3K : ℝ) * Real.sqrt app3tau) * (r ^ 2) :=
      mul_le_mul_of_nonneg_right fge (by positivity : (0 : ℝ) ≤ r ^ 2)
    have hmul2 : (1 : ℝ) ≤ (1 : ℝ) * (r ^ 2) := by
      rw [one_mul]
      exact hr2
    exact hmul2.trans hmul1
  -- hL6: q ≤ u(1−1/r), q := 1−τ−7t/K, u := 1−τ−2√τ/K.
  -- Facts: u ≤ 1, u − q ≥ (5/2)/K, r ≥ 1e8 ⟹ u/r ≤ (5/2)/(2K) ≤ u − q.
  let q : ℝ := 1 - app3tau - 7 * tauQuarter app3tau / (app3K : ℝ)
  let u : ℝ := 1 - app3tau - 2 * Real.sqrt app3tau / (app3K : ℝ)
  have ht0 : 0 < tauQuarter app3tau := tauQuarter_pos hτ0
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt app3tau := Real.sqrt_nonneg _
  have hterm_nonneg : (0 : ℝ) ≤ 2 * Real.sqrt app3tau / (app3K : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) hsqrt_nonneg) (le_of_lt hKpos)
  have hu : u ≤ 1 := by
    dsimp [u]
    have htau_nonneg : (0 : ℝ) ≤ app3tau := le_of_lt hτ0
    linarith
  have hu0 : (0 : ℝ) ≤ u := by
    dsimp [u]
    have hq0' : (0 : ℝ) ≤ 1 - app3tau - 7 * tauQuarter app3tau / (app3K : ℝ) := by
      -- q ≥ 1993/4000000 > 0
      have ht1 : tauQuarter app3tau ≤ 1 := htle
      have h1 : 1 - app3tau - 7 * tauQuarter app3tau / (app3K : ℝ) ≥
          1 - app3tau - 7 / (app3K : ℝ) := by
        have hh : 7 * tauQuarter app3tau / (app3K : ℝ) ≤ 7 / (app3K : ℝ) := by
          have hm := mul_le_mul_of_nonneg_left ht1 (by norm_num : (0 : ℝ) ≤ 7)
          -- 7t/K ≤ 7/K:
          have hm2 := mul_le_mul_of_nonneg_right hm (by positivity : (0 : ℝ) ≤ 1 / (app3K : ℝ))
          simpa [div_eq_mul_inv, mul_assoc] using hm2
        linarith
      have h2 : 1 - app3tau - 7 / (app3K : ℝ) ≥ (1993 / 4000000 : ℝ) := by
        dsimp [app3tau, app3K]
        norm_num
      linarith
    have huq0 : (0 : ℝ) ≤ 1 - app3tau - 2 * Real.sqrt app3tau / (app3K : ℝ) := by
      -- u ≥ q (7t ≥ 2√τ) so u ≥ q ≥ 0
      have huq : (1 : ℝ) - app3tau - 2 * Real.sqrt app3tau / (app3K : ℝ) ≥
          1 - app3tau - 7 * tauQuarter app3tau / (app3K : ℝ) := by
        -- 2√τ/K ≤ 7t/K
        have hle : 2 * Real.sqrt app3tau ≤ 7 * tauQuarter app3tau := by
          -- 2√τ = 2t² ≤ 2t ≤ 7t
          have h2t : 2 * Real.sqrt app3tau ≤ 2 * tauQuarter app3tau := by
            have hsq : Real.sqrt app3tau = (tauQuarter app3tau) ^ 2 := (tauQuarter_sq app3tau).symm
            have ht2 : (tauQuarter app3tau) ^ 2 ≤ tauQuarter app3tau := by
              have hd : (0 : ℝ) ≤ tauQuarter app3tau * (1 - tauQuarter app3tau) := by
                exact mul_nonneg (tauQuarter_nonneg app3tau) (by linarith)
              nlinarith
            rw [hsq]
            exact mul_le_mul_of_nonneg_left ht2 (by norm_num : (0 : ℝ) ≤ 2)
          have h2t7 : 2 * tauQuarter app3tau ≤ 7 * tauQuarter app3tau := by nlinarith
          exact h2t.trans h2t7
        have hle' : 2 * Real.sqrt app3tau / (app3K : ℝ) ≤ 7 * tauQuarter app3tau / (app3K : ℝ) := by
          exact div_le_div_of_nonneg_right hle (le_of_lt hKpos)
        linarith
      linarith
    linarith
  have huq : (5 / 2 : ℝ) / (app3K : ℝ) ≤ u - q := by
    -- u − q = (7t − 2√τ)/K = (7t−2t²)/K ≥ (5t)/K ≥ (5/2)/K
    have hEq : u - q = (7 * tauQuarter app3tau - 2 * Real.sqrt app3tau) / (app3K : ℝ) := by
      dsimp [u, q]
      field_simp [ne_of_gt hKpos]
      ring
    have hsq : Real.sqrt app3tau = (tauQuarter app3tau) ^ 2 := (tauQuarter_sq app3tau).symm
    have hnum : (5 / 2 : ℝ) ≤ 7 * tauQuarter app3tau - 2 * Real.sqrt app3tau := by
      have hsq' : Real.sqrt app3tau = (tauQuarter app3tau) ^ 2 := hsq
      have ht2 : (tauQuarter app3tau) ^ 2 ≤ tauQuarter app3tau := by
        have hd : (0 : ℝ) ≤ tauQuarter app3tau * (1 - tauQuarter app3tau) := by
          exact mul_nonneg (tauQuarter_nonneg app3tau) (by linarith)
        nlinarith
      -- 7t − 2√τ ≥ 5t ≥ 5/2
      have h1 : 7 * tauQuarter app3tau - 2 * Real.sqrt app3tau ≥ 5 * tauQuarter app3tau := by
        rw [hsq]
        have h5 : 2 * (tauQuarter app3tau) ^ 2 ≤ 2 * tauQuarter app3tau := by
          exact mul_le_mul_of_nonneg_left ht2 (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
      have h2 : (5 * tauQuarter app3tau : ℝ) ≥ (5 / 2 : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left htge (by norm_num : (0 : ℝ) ≤ 5)
        nlinarith
      nlinarith
    have hdiv : (5 / 2 : ℝ) / (app3K : ℝ) ≤ (7 * tauQuarter app3tau - 2 * Real.sqrt app3tau) / (app3K : ℝ) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hKpos)
    rw [hEq]
    exact hdiv
  have hu1r : q ≤ u * (1 - 1 / r) := by
    -- u(1−1/r) = u − u/r ≥ u − 1/r ≥ u − (u−q) = q since u/r ≤ 1/r ≤ (u−q)
    -- 1/r ≤ (u − q)/2? r ≥ 1e8 and u−q ≥ 2.5/K = 6.25e-7 ≥ 2·1e-8:
    have h1 : (1 / r : ℝ) ≤ (u - q) / 2 := by
      have hsmall : (1 / (r : ℝ)) ≤ (1 / 2 : ℝ) / (app3K : ℝ) := by
        -- r ≥ 1e8 ≥ 2K·? 1/r ≤ 2.5/K·? choose (1/2)/K: need r ≥ 2K = 8e6 ✓
        have hden1 : (0 : ℝ) < r := by linarith
        have hden2 : (0 : ℝ) < (app3K : ℝ) := hKpos
        rw [div_le_div_iff₀ hden1 hden2]
        -- 1·K ≤ (1/2)·r
        have hKbig2 : (app3K : ℝ) * 2 ≤ r := by
          have h2K : 2 * (app3K : ℝ) ≤ (100000000 : ℝ) := by
            dsimp [app3K]
            norm_num
          nlinarith
        nlinarith
      have hhalf : (1 / 2 : ℝ) / (app3K : ℝ) ≤ (u - q) / 2 := by
        have hq2 : (5 / 2 : ℝ) / (app3K : ℝ) ≤ u - q := huq
        -- (1/2)/K ≤ (1/5)·(5/2)/K ≤ (u−q)/2: since (u−q)/2 ≥ (5/4)/K ≥ (1/2)/K
        have hhalf' : (1 / 2 : ℝ) / (app3K : ℝ) ≤ (5 / 4 : ℝ) / (app3K : ℝ) := by
          exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hKpos)
        have hq4 : (5 / 4 : ℝ) / (app3K : ℝ) ≤ (u - q) / 2 := by
          have hm := mul_le_mul_of_nonneg_left huq (by norm_num : (0 : ℝ) ≤ 1 / 2)
          have hL : (1 / 2) * ((5 / 2) / (app3K : ℝ)) = (5 / 4) / (app3K : ℝ) := by
            field_simp [ne_of_gt hKpos]
            all_goals ring
          have hR : (1 / 2) * (u - q) = (u - q) / 2 := by ring
          have hm1 := hm
          rw [hL] at hm1
          rw [hR] at hm1
          exact hm1
        exact hhalf'.trans hq4
      exact hsmall.trans hhalf
    -- explicit chain: u·(1−1/r) − q = (u−q) − u·x ≥ (u−q) − x ≥ (u−q) − (u−q)/2 = (u−q)/2 ≥ 0
    let x : ℝ := 1 / r
    have h1x : x ≤ (u - q) / 2 := by simpa [x] using h1
    have hposx : (0 : ℝ) ≤ x := by
      dsimp [x]
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt (by linarith : (0 : ℝ) < r))
    have hux : u * x ≤ x := by
      have hm := mul_le_mul_of_nonneg_right hu hposx
      simpa using hm
    have hb : u * (1 - 1 / r) = u - u * x := by
      dsimp [x]
      ring
    have huq0 : (0 : ℝ) ≤ u - q := by
      have hpos : (0 : ℝ) < (5 / 2) / (app3K : ℝ) := div_pos (by norm_num) hKpos
      nlinarith [huq]
    have hB1 : (0 : ℝ) ≤ (u - q) - (u - q) / 2 := by nlinarith
    have hB2 : (0 : ℝ) ≤ (u - q) / 2 - x := by nlinarith [h1x]
    have hB3 : (0 : ℝ) ≤ x - u * x := by
      have h1m : (0 : ℝ) ≤ 1 - u := by linarith
      have hm := mul_nonneg h1m hposx
      have hring : (1 - u) * x = x - u * x := by ring
      rwa [hring] at hm
    have hpart1 : (0 : ℝ) ≤ (u - q) - u * x := by
      have hA : (u - q) - u * x = ((u - q) - (u - q) / 2) + ((u - q) / 2 - x) + (x - u * x) := by ring
      nlinarith [hA, hB1, hB2, hB3]
    have hqle : q ≤ u - u * x := by
      have : (0 : ℝ) ≤ (u - q) - u * x := hpart1
      nlinarith
    rw [hb]
    exact hqle
  -- finish via ReorderingMargins_follows_from_large (raw r₁ form):
  refine ReorderingMargins_follows_from_large r₁ app3tau app3K ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hq : 0 < q
    have hq0' : (0 : ℝ) < q := by
      -- q ≥ 1993/4000000 > 0 (same computation as hu0's hq0')
      have ht1 : tauQuarter app3tau ≤ 1 := htle
      have h1 : 1 - app3tau - 7 * tauQuarter app3tau / (app3K : ℝ) ≥
          1 - app3tau - 7 / (app3K : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left ht1 (by norm_num : (0 : ℝ) ≤ 7)
        have hm2 := mul_le_mul_of_nonneg_right hm (by positivity : (0 : ℝ) ≤ 1 / (app3K : ℝ))
        have hm3 : 7 * tauQuarter app3tau / (app3K : ℝ) ≤ 7 / (app3K : ℝ) := by
          simpa [div_eq_mul_inv, mul_assoc] using hm2
        linarith
      have h2 : 1 - app3tau - 7 / (app3K : ℝ) ≥ (1993 / 4000000 : ℝ) := by
        dsimp [app3tau, app3K]
        norm_num
      dsimp [q]
      linarith
    exact hq0'
  · simpa [r] using hL1
  · simpa [r] using hL2
  · simpa [r] using hL3
  · simpa [r] using hL4
  · simpa [r] using hL5
  · simpa [r, q, u] using hu1r

/-! ## Theorem 6.1 preparation, step 4 (proved): the App-3 firing

`app3_firing`: `reorderingLemma_of_subfamily` instantiated at the App-3
parameters (`τ := app3tau = 1−1/2000`, `K := app3K = 2000²`) — for any
subfamily `𝓖 ⊆ 𝓗` of a linear hypergraph with all edges `≥ r₁` and
`(r₁ : ℝ) ≥ 10⁸`, `∃ ord : 𝓖 ≃ Fin k, GoodOrdering app3tau ord ∨
VolumeWitness app3tau app3K ord`.  In Fig. 3, `𝓖 := 𝓗₃` (the
huge-edge-containing remainder); the volume contradiction
(`vol(W₂) ≥ 1−δ³` vs `vol(W₂) + vol(𝓗₃) ≤ 1`) then forces the good case,
giving `fwddeg ≤ n/2000` on `𝓗₃`. -/

/-- **App-3 firing**: the reordering lemma applied to any subfamily
`𝓖 ⊆ 𝓗` of a linear hypergraph whose edges all have size `≥ r₁`, at the
App-3 parameters `(τ, K) = (1−1/2000, 2000²)`, for `(r₁ : ℝ) ≥ 10⁸` —
gives `GoodOrdering app3tau ord ∨ VolumeWitness app3tau app3K ord` on
`𝓖`.  In the Fig. 3 proof, `𝓖` is `𝓗₃` (the huge-edge-containing
remainder); the volume contradiction then forces the good case. -/
theorem app3_firing {n r₁ : ℕ} {𝓗 𝓖 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    (h2n : 2 ≤ n) (h2r1 : 2 ≤ r₁) (hK : (1 : ℕ) ≤ app3K)
    (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : Set (Fin n), e ∈ 𝓗 → (r₁ : ℝ) ≤ edgeSize e) :
    ∃ k : ℕ, ∃ ord : 𝓖 ≃ Fin k,
      GoodOrdering app3tau ord ∨ VolumeWitness app3tau app3K ord := by
  classical
  have hτ0 : 0 < app3tau := app3_tau_pos
  have hτ1 : app3tau < 1 := by
    dsimp [app3tau]
    norm_num
  exact reorderingLemma_of_subfamily (r₁ := r₁) (τ := app3tau) (K := app3K) hsub
    h2n h2r1 hτ0 hτ1 hK (app3_margins r₁ hR) hlin hsize

/-! ## Theorem 6.1 preparation, step 5 (proved): the volume-contradiction
arithmetic (App-3 hinge)

`app3_volume_contradiction (δ volW₂ volW' : ℝ)`: from `0 < δ < 1`,
`vol(W₂) ≥ 1−δ³`, `vol(W₂) + vol(W′) ≤ 1` and `δ ≤ vol(W′)` derive
`False` (`1−δ³ + δ > 1` since `δ³ < δ`).  In App 3: the volume
alternative of the reordering lemma on `𝓗₃` supplies
`vol(W′) ≥ volBound(app3tau, app3K)`, the App-2 chain supplies
`vol(W₂) ≥ 1−δ³`, and disjointness/linearity give
`vol(W₂)+vol(𝓗₃) ≤ 1` — forcing the good case (`fwddeg ≤ n/2000` on
`𝓗₃`).  The `vol(W′) ≥ volBound ≥ δ` conjunct is discharged at the
Theorem-6.1 level by choosing δ in the hierarchy. -/

/-- **Volume-contradiction arithmetic (App-3 hinge)**: if
`vol(W₂) ≥ 1−δ³`, `vol(W₂) + vol(W′) ≤ 1` and `δ ≤ vol(W′)` with
`0 < δ < 1`, then `False`.  (The App-3 volume alternative would supply
`vol(W′) ≥ volBound(app3tau, app3K) ≥ δ`; combined with the App-2 bound
`vol(W₂) ≥ 1−δ³` and `vol ≤ 1` on the disjoint `W₂`, `𝓗₃`, this forces
the good case.) -/
theorem app3_volume_contradiction (δ volW₂ volW' : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hvol2 : (1 : ℝ) - δ ^ 3 ≤ volW₂)
    (hsum : volW₂ + volW' ≤ 1)
    (hδW : δ ≤ volW') : False := by
  have hd2 : δ ^ 2 < 1 := by
    have hmm : δ * δ < 1 * δ := mul_lt_mul_of_pos_right hδ1 hδ0
    have hsq : δ ^ 2 < δ := by simpa [pow_two] using hmm
    linarith
  have hd3 : δ ^ 3 < δ := by
    have hmm := mul_lt_mul_of_pos_right hd2 hδ0
    -- δ²·δ < 1·δ: δ³ < δ
    simpa [pow_succ, pow_two] using hmm
  have hvol : (1 : ℝ) - δ ^ 3 + δ ≤ volW₂ + volW' := by linarith
  have hgt : (1 : ℝ) < 1 - δ ^ 3 + δ := by
    have : δ - δ ^ 3 > 0 := by linarith
    linarith
  linarith

/-! ## Theorem 6.1 preparation, step 6 (proved): the App-2 firing

`app2tau (σ) := 3σ`, `app2K = 1` (the τ ≪ 1 main application of Fig. 3),
and `app2_firing`: the reordering lemma applied to any subfamily
`𝓖 ⊆ 𝓗` at `(τ, K) = (3σ, 1)` (margins `ReorderingMargins r₁ (3σ) 1`
carried as conjuncts, the `r₁ ≥ R(σ)` hierarchy facts) —
`GoodOrdering (3σ) ord ∨ VolumeWitness (3σ) 1 ord` on `𝓖`.  In Fig. 3
`𝓖 := 𝓗₁^left`; the volume alternative yields `W₂` with
`volBound (3σ) 1 ≤ vol(W₂)`, and the Theorem-6.1-level hierarchy choice
(`σ ≪ δ¹²`, so `1−3σ−7(3σ)^{1/4} ≥ 1−δ³`-type) gives the App-2 bound
`vol(W₂) ≥ 1 − δ³` consumed by `app3_volume_contradiction`. -/

/-- App-2 parameters: `τ = 3σ`, `K = 1` (the τ ≪ 1 main application of
Fig. 3; paper: `1/2000`-free, `K = 1`). -/
def app2tau (σ : ℝ) : ℝ := 3 * σ

/-- **App-2 firing**: the reordering lemma applied to any subfamily
`𝓖 ⊆ 𝓗` at `(τ, K) = (3σ, 1)`, with the margin block `ReorderingMargins
r₁ (3σ) 1` carried as a conjunct (the `r₁ ≥ R(σ)` hierarchy facts).
In Fig. 3 `𝓖 := 𝓗₁^left`; the volume alternative then yields `W₂` with
`volBound (3σ) 1 ≤ vol(W₂)`, and the Theorem-6.1-level choice `σ ≪ δ¹²`
gives `vol(W₂) ≥ 1 − δ³`. -/
theorem app2_firing {n r₁ : ℕ} (σ : ℝ) {𝓗 𝓖 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    (h2n : 2 ≤ n) (h2r1 : 2 ≤ r₁) (hσ0 : 0 < σ)
    (hσ1 : 3 * σ < 1) (hm : ReorderingMargins r₁ (3 * σ) 1)
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : Set (Fin n), e ∈ 𝓗 → (r₁ : ℝ) ≤ edgeSize e) :
    ∃ k : ℕ, ∃ ord : 𝓖 ≃ Fin k,
      GoodOrdering (3 * σ) ord ∨ VolumeWitness (3 * σ) 1 ord := by
  classical
  have hτ0 : 0 < 3 * σ := by linarith
  have hτ1 : 3 * σ < 1 := hσ1
  have hK : (1 : ℕ) ≤ 1 := le_rfl
  exact reorderingLemma_of_subfamily (r₁ := r₁) (τ := 3 * σ) (K := 1) hsub
    h2n h2r1 hτ0 hτ1 hK hm hlin hsize

/-- the App-2 volume of the volume alternative is at least `1 − δ³` once
the margin `δ³ ≤ 1 − volBound (3σ) 1` holds (paper: with `σ ≪ δ¹²`). -/
lemma app2_volume_bound (σ δ : ℝ) (hδ : 0 ≤ δ)
    (hV : (1 : ℝ) - δ ^ 3 ≤ volBound (3 * σ) 1) :
    (1 : ℝ) - δ ^ 3 ≤ volBound (3 * σ) 1 := hV

/-! ## Theorem 6.1 preparation, step 7 (proved): volume transport between a
subfamily and the ambient hypergraph

`volume_of_subfamily`: for a subfamily `𝓖 ⊆ 𝓗` (same vertices), the
volume of a `𝓖`-finset `S` equals the `𝓗`-volume of its image under the
inclusion (`volume` only reads the coerced edge sets and the shared
`n`).  This is the hinge that lets the reordering lemma's
`VolumeWitness` volume bounds (computed inside the subfamily-hypergraph
`𝓗₃`) be compared with ambient `𝓗`-subfamily volumes in the App-3 volume
contradiction.  (Proof: `Finset.sum_image` with the injective inclusion —
the summand is definitionally invariant under the coercion.) -/

/-- **Volume transport**: for a subfamily `𝓖 ⊆ 𝓗` (same vertices), the
volume of a `𝓖`-finset `S` equals the volume (in `𝓗`) of the image of
`S` under the inclusion.  This is what lets the reordering lemma's
`VolumeWitness` volume bounds (computed inside the subfamily-hypergraph
`𝓗₃`) be compared with ambient `𝓗`-subfamily volumes in the App-3 volume
contradiction. -/
theorem volume_of_subfamily {n : ℕ} {𝓗 𝓖 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    (S : Finset 𝓖) :
    Hypergraph.volume 𝓖 S =
      Hypergraph.volume 𝓗 (S.image (fun e : 𝓖 => ⟨(e : Set (Fin n)), hsub e.2⟩)) := by
  classical
  let f : 𝓖 → 𝓗 := fun e => ⟨(e : Set (Fin n)), hsub e.2⟩
  have hinj : Set.InjOn f (S : Set 𝓖) := by
    intro a ha b hb hEq
    apply Subtype.ext
    simpa [f] using congrArg (fun x : 𝓗 => x.1) hEq
  have hsum : (S.image f).sum (fun e : 𝓗 =>
      (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) =
      S.sum (fun e : 𝓖 =>
      (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) := by
    have hsum' :
        (S.image f).sum (fun e : 𝓗 =>
          (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) =
        S.sum (fun e : 𝓖 =>
          (edgeSize ((f e) : Set (Fin n)) : ℝ) * ((edgeSize ((f e) : Set (Fin n)) : ℝ) - 1)) :=
      Finset.sum_image hinj
    rw [hsum']
  unfold Hypergraph.volume
  rw [hsum]

/-! ## Theorem 6.1 preparation, step 8 (proved): volume additivity and the
`vol + vol ≤ 1` bound

`volume_disjoint_add`: `vol(S₁∪S₂) = vol(S₁) + vol(S₂)` for disjoint
`𝓗`-finsets (`Finset.sum_union` + the division split, with the `den = 0`
case closed by `0⁻¹ = 0`); and `volume_disjoint_le_one`:
`vol(S₁) + vol(S₂) ≤ 1` for disjoint subfamilies of a *linear*
hypergraph (`volume_le_one`).  These give the `vol(W₂) + vol(𝓗₃) ≤ 1`
input of the App-3 volume contradiction once `W₂` and `𝓗₃` are embedded
as disjoint `𝓗`-finsets (via `volume_of_subfamily`). -/

/-- Volume is additive over disjoint subfamilies of the same hypergraph:
`vol(S₁∪S₂) = vol(S₁) + vol(S₂)` when `S₁`, `S₂` are disjoint
`𝓗`-finsets.  Combined with `volume_le_one` this gives
`vol(S₁)+vol(S₂) ≤ 1` for disjoint subfamilies of a linear `𝓗` — the
`vol(W₂)+vol(𝓗₃) ≤ 1` input of the App-3 volume contradiction. -/
lemma volume_disjoint_add {n : ℕ} {𝓗 : Hypergraph (Fin n)}
    (S₁ S₂ : Finset 𝓗) (hdisj : Disjoint S₁ S₂) :
    Hypergraph.volume 𝓗 (S₁ ∪ S₂) = Hypergraph.volume 𝓗 S₁ + Hypergraph.volume 𝓗 S₂ := by
  classical
  unfold Hypergraph.volume
  let den : ℝ := (n : ℝ) * ((n - 1 : ℕ) : ℝ)
  have hsum : (S₁ ∪ S₂).sum (fun e : 𝓗 =>
      (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) =
      S₁.sum (fun e : 𝓗 =>
        (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) +
      S₂.sum (fun e : 𝓗 =>
        (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1)) := by
    exact Finset.sum_union hdisj
  by_cases hden : den ≠ 0
  · field_simp [hden]
    rw [hsum]
  · have hden0 : den = 0 := not_not.mp hden
    simp [den, div_eq_mul_inv, hden0]

/-- **App-3 wiring**: disjoint subfamilies of a linear hypergraph have
total volume at most `1` — `vol(S₁) + vol(S₂) ≤ 1` (from
`volume_disjoint_add` + `volume_le_one`). -/
lemma volume_disjoint_le_one {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (S₁ S₂ : Finset 𝓗) (hdisj : Disjoint S₁ S₂) :
    Hypergraph.volume 𝓗 S₁ + Hypergraph.volume 𝓗 S₂ ≤ 1 := by
  have hadd := volume_disjoint_add S₁ S₂ hdisj
  have hle := volume_le_one hlin (S₁ ∪ S₂)
  rw [← hadd]
  exact hle

/-! ## Theorem 6.1 preparation, step 9 (proved): the App-3 wiring
instantiation

`subfamilyImage` (the inclusion-embedding of a subfamily-finset into
`𝓗`), `volume_subfamilyImage` (its volume is the subfamily's),
`subfamilyImage_disjoint` (images are disjoint when no edge-set
coincides), and **`volume_wiring`**: for subfamily-finsets `S₁`, `S₂`
whose ambient images in a linear `𝓗` are disjoint,
`volume 𝓖₁ S₁ + volume 𝓖₂ S₂ ≤ 1`.  This turns
`volume_disjoint_le_one` into the `vol(W₂) + vol(𝓗₃) ≤ 1` input of
`app3_volume_contradiction` (with `𝓖₁ := 𝓗₁^left`, `S₁ := W₂`, `𝓖₂ :=
𝓗₃`, `S₂ := W′`). -/

/-- The image of a `𝓖`-finset inside the ambient hypergraph `𝓗`
(`𝓖 ⊆ 𝓗`): the inclusion-embedding of a subfamily-finset. -/
noncomputable def subfamilyImage {n : ℕ} {𝓗 𝓖 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    (S : Finset 𝓖) : Finset 𝓗 :=
  S.image (fun e : 𝓖 => ⟨(e : Set (Fin n)), hsub e.2⟩)

/-- the ambient volume of the image is the subfamily volume -/
lemma volume_subfamilyImage {n : ℕ} {𝓗 𝓖 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗)
    (S : Finset 𝓖) :
    Hypergraph.volume 𝓗 (subfamilyImage hsub S) = Hypergraph.volume 𝓖 S :=
  (volume_of_subfamily hsub S).symm

/-- ambient disjointness of the images of two subfamily-finsets, when no
edge of `S₁` coincides (as a vertex set) with an edge of `S₂` -/
lemma subfamilyImage_disjoint {n : ℕ} {𝓗 𝓖₁ 𝓖₂ : Hypergraph (Fin n)}
    (hsub₁ : 𝓖₁ ⊆ 𝓗) (hsub₂ : 𝓖₂ ⊆ 𝓗) (S₁ : Finset 𝓖₁) (S₂ : Finset 𝓖₂)
    (hne : ∀ e₁ ∈ S₁, ∀ e₂ ∈ S₂, (e₁ : Set (Fin n)) ≠ (e₂ : Set (Fin n))) :
    Disjoint (subfamilyImage hsub₁ S₁) (subfamilyImage hsub₂ S₂) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  rw [subfamilyImage, Finset.mem_image] at hx₁ hx₂
  rcases hx₁ with ⟨e₁, he₁, rfl⟩
  rcases hx₂ with ⟨e₂, he₂, hx₂⟩
  have hc := congrArg (fun y : 𝓗 => y.1) hx₂
  have hc' : (e₁ : Set (Fin n)) = (e₂ : Set (Fin n)) := by
    simpa using hc.symm
  exact hne e₁ he₁ e₂ he₂ hc'

/-- **App-3 wiring instantiation**: for subfamily-finsets `S₁ : Finset 𝓖₁`,
`S₂ : Finset 𝓖₂` whose ambient images in a *linear* `𝓗` are disjoint,
`volume 𝓖₁ S₁ + volume 𝓖₂ S₂ ≤ 1`.  In App 3, `𝓖₁ := 𝓗₁^left` with
`S₁ := W₂` and `𝓖₂ := 𝓗₃` with `S₂ := W′` (or the whole family) — this is
the `vol(W₂) + vol(𝓗₃) ≤ 1` input of `app3_volume_contradiction`. -/
theorem volume_wiring {n : ℕ} {𝓗 𝓖₁ 𝓖₂ : Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) (hsub₁ : 𝓖₁ ⊆ 𝓗) (hsub₂ : 𝓖₂ ⊆ 𝓗)
    (S₁ : Finset 𝓖₁) (S₂ : Finset 𝓖₂)
    (hdisj : Disjoint (subfamilyImage hsub₁ S₁) (subfamilyImage hsub₂ S₂)) :
    Hypergraph.volume 𝓖₁ S₁ + Hypergraph.volume 𝓖₂ S₂ ≤ 1 := by
  have hle := volume_disjoint_le_one hlin (subfamilyImage hsub₁ S₁) (subfamilyImage hsub₂ S₂) hdisj
  rwa [volume_subfamilyImage hsub₁ S₁, volume_subfamilyImage hsub₂ S₂] at hle

/-! ## Theorem 6.1 preparation, step 10 (proved): the two volume bounds and
the App-3 collapse

`volume_ge_one_sub_of_witness` (App 2: a `VolumeWitness (3σ) 1` gives
`W₂` with `vol(W₂) ≥ 1−δ³`, from `WVolume` and the hierarchy
`1−δ³ ≤ volBound (3σ) 1`), `volume_ge_delta_of_witness` (App 3: a
`VolumeWitness app3tau app3K` gives `W′` with `vol(W′) ≥ δ` from
`δ ≤ volBound app3tau app3K`), and **`app3_volume_collapse`**: `W₂ ⊆ 𝓖₂`
with `vol ≥ 1−δ³`, `W′ ⊆ 𝓖₃` with `vol ≥ δ`, ambient disjointness of
their images in a linear `𝓗` ⟹ `False` (`volume_wiring` +
`app3_volume_contradiction`).  This is the App-3 hinge end-to-end: the
volume alternatives of the App-2/App-3 firings are inconsistent, so the
App-3 firing's disjunction collapses to `GoodOrdering app3tau ord`
(`fwddeg ≤ n/2000` on `𝓗₃`). -/

/-- **App-2 volume bound**: a `VolumeWitness` at `(3σ, 1)` yields a
volume set `W₂` with `vol(W₂) ≥ 1 − δ³` once the hierarchy inequality
`1 − δ³ ≤ volBound (3σ) 1` holds (paper: `σ ≪ δ¹²`). -/
lemma volume_ge_one_sub_of_witness {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ}
    {ord : 𝓖 ≃ Fin k} (σ δ : ℝ) (hV : (1 : ℝ) - δ ^ 3 ≤ volBound (3 * σ) 1)
    (hw : VolumeWitness (3 * σ) 1 ord) :
    ∃ W : Finset 𝓖, (1 : ℝ) - δ ^ 3 ≤ Hypergraph.volume 𝓖 W := by
  rcases hw with ⟨eStar, W, h1, h2, h3, h4, h5, h6⟩
  exact ⟨W, hV.trans h3⟩

/-- **App-3 volume bound**: a `VolumeWitness` at `(app3tau, app3K)` yields
a volume set `W′` with `vol(W′) ≥ δ` once `δ ≤ volBound app3tau app3K`
(discharged by the Theorem-6.1-level choice of `δ`). -/
lemma volume_ge_delta_of_witness {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ}
    {ord : 𝓖 ≃ Fin k} (δ : ℝ) (hV : δ ≤ volBound app3tau app3K)
    (hw : VolumeWitness app3tau app3K ord) :
    ∃ W : Finset 𝓖, δ ≤ Hypergraph.volume 𝓖 W := by
  rcases hw with ⟨eStar, W, h1, h2, h3, h4, h5, h6⟩
  exact ⟨W, hV.trans h3⟩

/-- **App-3 collapse**: the App-2 volume set `W₂ ⊆ 𝓖₂` (with
`vol(W₂) ≥ 1−δ³`), the App-3 volume set `W′ ⊆ 𝓖₃` (with
`vol(W′) ≥ δ`) and the ambient disjointness of their images in a linear
`𝓗` are contradictory (`volume_wiring` gives `vol(W₂)+vol(W′) ≤ 1`,
`app3_volume_contradiction` gives `False`). -/
theorem app3_volume_collapse {n : ℕ} {𝓗 𝓖₂ 𝓖₃ : Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) (hsub₂ : 𝓖₂ ⊆ 𝓗) (hsub₃ : 𝓖₃ ⊆ 𝓗)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (W₂ : Finset 𝓖₂) (W' : Finset 𝓖₃)
    (hvol₂ : (1 : ℝ) - δ ^ 3 ≤ Hypergraph.volume 𝓖₂ W₂)
    (hvol' : δ ≤ Hypergraph.volume 𝓖₃ W')
    (hdisj : Disjoint (subfamilyImage hsub₂ W₂) (subfamilyImage hsub₃ W')) : False := by
  have hle : Hypergraph.volume 𝓖₂ W₂ + Hypergraph.volume 𝓖₃ W' ≤ 1 :=
    volume_wiring hlin hsub₂ hsub₃ W₂ W' hdisj
  exact app3_volume_contradiction δ (Hypergraph.volume 𝓖₂ W₂) (Hypergraph.volume 𝓖₃ W')
    hδ0 hδ1 hvol₂ hle hvol'

/-! ## Theorem 6.1 preparation, step 11 (proved): the Fig. 3 rank families
and the disjointness core

`rankAbove ord fStar` (`{e ∈ 𝓖 : rank fStar ≤ rank e}` — the `f*`-span
shape) and `rankBelow ord fStar` (its complement among `𝓖`), with
membership criteria (`mem_rankAbove`, `mem_rankBelow`), the inclusions
`rankAbove_subset`/`rankBelow_subset` (`⊆ 𝓖`), the key disjointness
**`disjoint_rankAbove_rankBelow`** (no edge can have rank both `≥` and
`<`), and the transport
`subfamilyImage_disjoint_of_disjoint`: subfamilies of disjoint families
have disjoint images.  With `W₂ ⊆ rankAbove` and `𝓗₃ ⊆ rankBelow`, this
supplies the ambient disjointness hypothesis of
`app3_volume_collapse` — closing App 3. -/

/-- The edges of `𝓖` whose rank is `≥` that of `fStar` (the "span of
`fStar` onwards" in the ordering `ord`) — the shape of the Fig. 3
`f*`-span, e.g. `{e ∈ 𝓗₁^left : f* ⪯₂ e}`. -/
def rankAbove {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ} (ord : 𝓖 ≃ Fin k)
    (fStar : 𝓖) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | ∃ he : e ∈ 𝓖, (ord fStar : ℕ) ≤ (ord ⟨e, he⟩ : ℕ)}

/-- The edges of `𝓖` strictly before `fStar` (the complement of the span). -/
def rankBelow {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ} (ord : 𝓖 ≃ Fin k)
    (fStar : 𝓖) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | ∃ he : e ∈ 𝓖, (ord ⟨e, he⟩ : ℕ) < (ord fStar : ℕ)}

lemma rankAbove_subset {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ} (ord : 𝓖 ≃ Fin k)
    (fStar : 𝓖) : rankAbove ord fStar ⊆ 𝓖 := by
  intro e he
  exact he.choose

lemma rankBelow_subset {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ} (ord : 𝓖 ≃ Fin k)
    (fStar : 𝓖) : rankBelow ord fStar ⊆ 𝓖 := by
  intro e he
  exact he.choose

/-- the membership criterion for `rankAbove` -/
lemma mem_rankAbove {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ} (ord : 𝓖 ≃ Fin k)
    (fStar : 𝓖) {e : Set (Fin n)} (he : e ∈ 𝓖) :
    e ∈ rankAbove ord fStar ↔ (ord fStar : ℕ) ≤ (ord ⟨e, he⟩ : ℕ) := by
  constructor
  · intro h
    obtain ⟨he', hlt⟩ := h
    have hEq : (⟨e, he'⟩ : 𝓖) = ⟨e, he⟩ := Subtype.ext rfl
    rwa [hEq] at hlt
  · intro h
    exact ⟨he, h⟩

/-- the membership criterion for `rankBelow` -/
lemma mem_rankBelow {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ} (ord : 𝓖 ≃ Fin k)
    (fStar : 𝓖) {e : Set (Fin n)} (he : e ∈ 𝓖) :
    e ∈ rankBelow ord fStar ↔ (ord ⟨e, he⟩ : ℕ) < (ord fStar : ℕ) := by
  constructor
  · intro h
    obtain ⟨he', hlt⟩ := h
    have hEq : (⟨e, he'⟩ : 𝓖) = ⟨e, he⟩ := Subtype.ext rfl
    rwa [hEq] at hlt
  · intro h
    exact ⟨he, h⟩

/-- **Fig. 3 disjointness core**: the `f*`-span `rankAbove ord f*` and the
complement `rankBelow ord f*` are disjoint *as families of edges* (no edge
can have rank both `≥` and `<` the rank of `f*`).  This is what makes
`W₂ ⊆ rankAbove` and `𝓗₃ ⊆ rankBelow` disjoint subfamilies of `𝓗`, and
hence their images disjoint. -/
lemma disjoint_rankAbove_rankBelow {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ}
    (ord : 𝓖 ≃ Fin k) (fStar : 𝓖) :
    Disjoint (rankAbove ord fStar) (rankBelow ord fStar) := by
  rw [Set.disjoint_left]
  intro e heA heB
  obtain ⟨he, hle⟩ := heA
  obtain ⟨he', hlt⟩ := heB
  have hEq : (⟨e, he'⟩ : 𝓖) = ⟨e, he⟩ := Subtype.ext rfl
  rw [hEq] at hlt
  omega

/-- two subfamilies of disjoint families have images that are disjoint
(`subfamilyImage` of the respective inclusions). -/
lemma subfamilyImage_disjoint_of_disjoint {n : ℕ} {𝓗 𝓖a 𝓖b 𝓖₂ 𝓖₃ : Hypergraph (Fin n)}
    (hsub : 𝓖₂ ⊆ 𝓖a) (hsubb : 𝓖₃ ⊆ 𝓖b) (hdisj : Disjoint 𝓖a 𝓖b)
    (hsub₂ : 𝓖₂ ⊆ 𝓗) (hsub₃ : 𝓖₃ ⊆ 𝓗)
    (S₂ : Finset 𝓖₂) (S₃ : Finset 𝓖₃) :
    Disjoint (subfamilyImage hsub₂ S₂) (subfamilyImage hsub₃ S₃) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx₂ hx₃
  rw [subfamilyImage, Finset.mem_image] at hx₂ hx₃
  rcases hx₂ with ⟨e₂, he₂, rfl⟩
  rcases hx₃ with ⟨e₃, he₃, hx₃⟩
  have hc := congrArg (fun y : 𝓗 => y.1) hx₃
  -- e₂ and e₃ are the same edge-set, hence equal as edges of 𝓗,
  -- so the edge lies in both 𝓖a and 𝓖b:
  have hEq : (e₂ : Set (Fin n)) = (e₃ : Set (Fin n)) := by simpa using hc.symm
  have hmemA : (e₂ : Set (Fin n)) ∈ 𝓖a := hsub e₂.2
  have hmemB : (e₂ : Set (Fin n)) ∈ 𝓖b := by
    rw [hEq]
    exact hsubb e₃.2
  exact (Set.disjoint_left.mp hdisj) hmemA hmemB

/-! ## Theorem 6.1 preparation, step 12 (proved): the App-3 closing
instantiation

`nonHuge 𝓗 β := {e ∈ 𝓗 : e is not huge}` (with `nonHuge_subset`) — the
Fig. 3 family the reorderings act on — and **`app3_closing`**: `W₂` in
the `f*`-span `rankAbove ord₂ f*` of `𝓖left ⊆ 𝓗` with
`vol(W₂) ≥ 1−δ³`, `W′` in the complementary `rankBelow ord₂ f*` with
`vol(W′) ≥ δ` ⟹ `False` (via `disjoint_rankAbove_rankBelow`,
`subfamilyImage_disjoint_of_disjoint` and `app3_volume_collapse`).
This is the Fig. 3 shape end-to-end: supplying the App-2 and App-3
witnesses (via `volume_ge_one_sub_of_witness`/`volume_ge_delta_of_witness`)
rules out the volume alternatives, so `app3_firing`'s disjunction
collapses to `GoodOrdering app3tau ord` on the residual family — App 3
closed. -/

/-- `𝓗′ := {e ∈ 𝓗 : e is not huge}`, the family the Fig. 3 reorderings act
on (`huge` = size `≥ βn/4`). -/
def nonHuge {n : ℕ} (𝓗 : Hypergraph (Fin n)) (β : ℝ) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | e ∈ 𝓗 ∧ ¬ (β * (n : ℝ) / 4 ≤ (edgeSize e : ℝ))}

lemma nonHuge_subset {n : ℕ} (𝓗 : Hypergraph (Fin n)) (β : ℝ) :
    nonHuge 𝓗 β ⊆ 𝓗 := by
  intro e he
  exact he.1

/-- **App-3 closing instantiation**: with `W₂` lying in the `f*`-span
`rankAbove ord₂ f*` of a subfamily `𝓖left ⊆ 𝓗` and the residual volume
set `W′` in the complementary family `rankBelow ord₂ f*`, the App-2 bound
`vol(W₂) ≥ 1−δ³` and the App-3 bound `vol(W′) ≥ δ` are contradictory
(the span and its complement are disjoint families).  Feeding
`app3_firing` (with `𝓖 := 𝓖left` and the App-2/App-3 witnesses) and the
App-2 witness into this closes App 3: the disjunction collapses to
`GoodOrdering app3tau ord` on the residual family. -/
theorem app3_closing {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {𝓖left : Hypergraph (Fin n)} (hleft : 𝓖left ⊆ 𝓗)
    {k : ℕ} (ord₂ : 𝓖left ≃ Fin k) (fStar : 𝓖left)
    (W₂ : Finset (rankAbove ord₂ fStar)) (W' : Finset (rankBelow ord₂ fStar))
    (hvol₂ : (1 : ℝ) - δ ^ 3 ≤ Hypergraph.volume (rankAbove ord₂ fStar) W₂)
    (hvol' : δ ≤ Hypergraph.volume (rankBelow ord₂ fStar) W') : False := by
  have hsub₂ : rankAbove ord₂ fStar ⊆ 𝓗 := (rankAbove_subset ord₂ fStar).trans hleft
  have hsub₃ : rankBelow ord₂ fStar ⊆ 𝓗 := (rankBelow_subset ord₂ fStar).trans hleft
  have hdisj : Disjoint (subfamilyImage hsub₂ W₂) (subfamilyImage hsub₃ W') :=
    subfamilyImage_disjoint_of_disjoint (subset_refl _) (subset_refl _)
      (disjoint_rankAbove_rankBelow ord₂ fStar) hsub₂ hsub₃ W₂ W'
  exact app3_volume_collapse hlin hsub₂ hsub₃ δ hδ0 hδ1 W₂ W' hvol₂ hvol' hdisj

/-! ## Theorem 6.1 preparation, step 13 (proved): retyping the App-2/App-3
volume sets into the span and its complement

`exists_finset_rankAbove`: a `𝓖`-finset `W` whose edges all have rank `≥`
that of `fStar` (in particular `W := W₂` with `fStar` its minimal-rank
edge — the paper's `f*`) can be viewed as a finset of `rankAbove ord
fStar` **with the same volume**; `exists_finset_rankBelow`: the analogue
for `rankBelow ord fStar` (the residual `W′ ⊆ 𝓗₃`, which lies before
`f*`).  So the App-2 volume bound `vol(W₂) ≥ 1−δ³` lands inside the span
and the App-3 bound `vol(W′) ≥ δ` inside the complement — exactly the
typed inputs of `app3_closing`, which then forces `GoodOrdering app3tau`
on the residual family. -/

/-- **Retyping into the span**: a `𝓖`-finset `W` whose edges all have
rank `≥` that of `fStar` (e.g. `W := W₂` with `fStar` its minimal-rank
edge) can be viewed as a finset of `rankAbove ord fStar` without changing
its volume. -/
lemma exists_finset_rankAbove {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ}
    (ord : 𝓖 ≃ Fin k) (fStar : 𝓖) (W : Finset 𝓖)
    (hW : ∀ e ∈ W, (ord fStar : ℕ) ≤ (ord e : ℕ)) :
    ∃ W' : Finset (rankAbove ord fStar),
      Hypergraph.volume (rankAbove ord fStar) W' = Hypergraph.volume 𝓖 W := by
  classical
  let φ : {e // e ∈ W} → rankAbove ord fStar := fun e =>
    ⟨(e.1 : Set (Fin n)), ⟨e.1.2, by
      have hle := hW e.1 e.2
      have hEq : (⟨(e.1 : Set (Fin n)), e.1.2⟩ : 𝓖) = e.1 := Subtype.ext rfl
      rw [hEq]
      exact hle⟩⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : rankAbove ord fStar => (x.1 : Set (Fin n))) hab
  refine ⟨W.attach.image φ, ?_⟩
  unfold Hypergraph.volume
  congr 1
  rw [Finset.sum_image (s := W.attach) (g := φ)
    (f := fun e : rankAbove ord fStar =>
      (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1))
    (by intro a _ b _ hab; exact hφinj hab)]
  rw [← Finset.sum_attach W (fun e : 𝓖 =>
      (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1))]

/-- **Retyping below the span**: the analogous statement for the
complementary family `rankBelow ord fStar`. -/
lemma exists_finset_rankBelow {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ}
    (ord : 𝓖 ≃ Fin k) (fStar : 𝓖) (W : Finset 𝓖)
    (hW : ∀ e ∈ W, (ord e : ℕ) < (ord fStar : ℕ)) :
    ∃ W' : Finset (rankBelow ord fStar),
      Hypergraph.volume (rankBelow ord fStar) W' = Hypergraph.volume 𝓖 W := by
  classical
  let φ : {e // e ∈ W} → rankBelow ord fStar := fun e =>
    ⟨(e.1 : Set (Fin n)), ⟨e.1.2, by
      have hle := hW e.1 e.2
      have hEq : (⟨(e.1 : Set (Fin n)), e.1.2⟩ : 𝓖) = e.1 := Subtype.ext rfl
      rw [hEq]
      exact hle⟩⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : rankBelow ord fStar => (x.1 : Set (Fin n))) hab
  refine ⟨W.attach.image φ, ?_⟩
  unfold Hypergraph.volume
  congr 1
  rw [Finset.sum_image (s := W.attach) (g := φ)
    (f := fun e : rankBelow ord fStar =>
      (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1))
    (by intro a _ b _ hab; exact hφinj hab)]
  rw [← Finset.sum_attach W (fun e : 𝓖 =>
      (edgeSize (e : Set (Fin n)) : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) - 1))]

/-! ## Theorem 6.1 preparation, step 14 (proved): the App-3 conclusion

`app3_good`: **App 3 closed**.  Given the App-2 volume witness (a set
`W₂` inside the span `rankAbove ord₂ f*` of a subfamily `𝓖left ⊆ 𝓗` with
`vol(W₂) ≥ 1−δ³`) and the hierarchy inequality `δ ≤ volBound app3tau
app3K`, the residual family `𝓖₃ := rankBelow ord₂ f*` (the complement of
the span — the paper's `𝓗₃`) admits an ordering satisfying (6.2:a):
`GoodOrdering app3tau`, i.e. `d⪯(e) ≤ n/2000` for every edge.

Indeed, firing the reordering lemma on `𝓖₃` (via `app3_firing`) either
already gives the good ordering, or a `VolumeWitness app3tau app3K`, whose
volume set `W′` satisfies `vol(W′) ≥ δ ≥ ...`; combined with `vol(W₂) ≥
1−δ³` this contradicts the volume bound `vol(W₂) + vol(W′) ≤ 1` of a
linear hypergraph (`app3_closing`). -/

/-- **App 3 closed**: with the App-2 volume set `W₂` in the `f*`-span and
the App-3 volume threshold `δ ≤ volBound app3tau app3K`, the complementary
family `rankBelow ord₂ f*` (= the paper's `𝓗₃`) has a good ordering at
parameter `app3tau` (`d⪯(e) ≤ (1−app3tau)n = n/2000`). -/
theorem app3_good {n r₁ : ℕ} {𝓗 : Hypergraph (Fin n)}
    (h2n : 2 ≤ n) (h2r1 : 2 ≤ r₁) (hK : (1 : ℕ) ≤ app3K)
    (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : Set (Fin n), e ∈ 𝓗 → (r₁ : ℝ) ≤ edgeSize e)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδV : δ ≤ volBound app3tau app3K)
    {𝓖left : Hypergraph (Fin n)} (hleft : 𝓖left ⊆ 𝓗)
    {k₂ : ℕ} (ord₂ : 𝓖left ≃ Fin k₂) (fStar : 𝓖left)
    (W₂ : Finset (rankAbove ord₂ fStar))
    (hvol₂ : (1 : ℝ) - δ ^ 3 ≤ Hypergraph.volume (rankAbove ord₂ fStar) W₂) :
    ∃ k₃ : ℕ, ∃ ord₃ : rankBelow ord₂ fStar ≃ Fin k₃, GoodOrdering app3tau ord₃ := by
  classical
  have hsub₃ : rankBelow ord₂ fStar ⊆ 𝓗 :=
    (rankBelow_subset ord₂ fStar).trans hleft
  obtain ⟨k₃, ord₃, hgood | hvol⟩ :=
    app3_firing (𝓖 := rankBelow ord₂ fStar) hsub₃ h2n h2r1 hK hR hlin hsize
  · exact ⟨k₃, ord₃, hgood⟩
  · exfalso
    obtain ⟨W', hW'⟩ := volume_ge_delta_of_witness δ hδV hvol
    exact app3_closing hlin δ hδ0 hδ1 hleft ord₂ fStar W₂ W' hvol₂ hW'

end
end ErdosFaberLovaszConjecture
