import Submission.EFL.ColourClassSplitting
import Submission.EFL.LargeEdge

/-!
# The honest colour-class splitting theorem

`ColourClassSplitting.lean` proves the *margin* split: every colour class of
a proper edge-colouring decomposes into `PieceOKMargin` pieces plus a
matching leftover (`SplitColourClassMarginStatement`).  This file completes
the milestone by packaging that output into the honest, self-contained
splitting theorem that Proposition `few-large-colour-classes`(ii) of the
paper (§6.3, Prop. 6.8) needs:

> Every colour class splits into pairwise edge-disjoint matching pieces such
> that every edge of the class lies in exactly one piece, every piece is a
> matching that either is a single edge or covers `< αn + 1` vertices, and
> the number of pieces is at most `2/α + 1`.

Two notes on the difference from the paper's Prop. 6.8 proof, which claims
*every* piece covers `≥ αn/2` vertices and that there are at most `2/α`
pieces: both are false in corner cases (e.g. a colour class consisting of
three pairwise disjoint edges of size `0.4αn` covers `1.2αn > αn` but cannot
be partitioned into pieces all covering `≥ αn/2`; the greedy chunking of a
list of total coverage just above `αn` can leave one remainder piece below
`αn/2`).  The honest form therefore (a) allows one exceptional piece (the
leftover, whose coverage is `< ⌈αn/2⌉`, hence comfortably below `αn`) and
(b) counts `2/α + 1` pieces.  The `+1`-style margin `αn + 1` in the piece
bound is the price of the integer threshold `⌈αn/2⌉`: chunk coverage lies
in `[⌈αn/2⌉, 2⌈αn/2⌉−1] ⊆ [αn/2, αn + 1)`.  Downstream applications absorb
both margins by taking the split parameter slightly smaller than the
boundedness parameter (e.g. `α/2`), exactly as the `≪`-hierarchy allows.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- A piece of an honest split: a matching that either is a single edge or
covers fewer than `αn + 1` vertices (the `+1` margin, cf. the module
header). -/
def SplitPieceOK (α : ℝ) (M : Finset (Set (Fin n))) : Prop :=
  IsMatchingFamily M ∧
    (M.card = 1 ∨ (FamilyVertexCount M : ℝ) < (α : ℝ) * (n : ℝ) + 1)

/-- The honest colour-class splitting statement: every colour class of every
proper edge-colouring of `𝓗` splits into at most `2/α + 1` pairwise
edge-disjoint matching pieces, each a subfamily of the class and either a
single edge or covering fewer than `αn + 1` vertices, such that every edge
of the class lies in exactly one piece.  (No hypothesis on the colour-class
coverage is needed: a class of coverage below the threshold is itself its
own leftover piece.) -/
def SplitColourClassHonest (α : ℝ) (𝓗 : Hypergraph (Fin n)) : Prop :=
  ∀ (φ : 𝓗.Coloring (Fin n)) (c : Fin n),
    ∃ P : Finset (Finset (Set (Fin n))),
      (∀ M ∈ P, M ⊆ EdgeSetFamily (φ.colorClass c)) ∧
      (∀ M ∈ P, SplitPieceOK α M) ∧
      (∀ e : Set (Fin n), e ∈ EdgeSetFamily (φ.colorClass c) →
        ∃! M : Finset (Set (Fin n)), M ∈ P ∧ e ∈ M) ∧
      ((P.card : ℝ) ≤ (2 : ℝ) / α + 1)

/-- `⌈αn/2⌉ < αn + 1` (real): the leftover coverage bound fits the margin. -/
theorem SplitThreshold_lt_alpha_add_one {α : ℝ} {n : ℕ} (hα : 0 ≤ α) :
    (SplitThreshold α n : ℝ) < (α : ℝ) * (n : ℝ) + 1 := by
  dsimp [SplitThreshold]
  have hx : 0 ≤ (α / 2 : ℝ) * (n : ℝ) := by
    have hα2 : 0 ≤ α / 2 := div_nonneg hα (by norm_num)
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    exact mul_nonneg hα2 hn
  have hlt := Nat.ceil_lt_add_one (a := (α / 2 : ℝ) * (n : ℝ)) hx
  have hle : (α / 2 : ℝ) * (n : ℝ) + 1 ≤ (α : ℝ) * (n : ℝ) + 1 := by
    have hg : 0 ≤ (α : ℝ) * (n : ℝ) := by
      exact mul_nonneg hα (by exact_mod_cast (Nat.zero_le n))
    nlinarith
  exact hlt.trans_le hle

/-- The number of vertices covered by a matching piece is the sum of its edge
sizes (rewriting version of `sumEdgeSizes_eq_FamilyVertexCount_of_matching`). -/
lemma FamilyVertexCount_eq_sumEdgeSizes_of_matching {s : Finset (Set (Fin n))}
    (hM : IsMatchingFamily s) : FamilyVertexCount s = sumEdgeSizes s :=
  (sumEdgeSizes_eq_FamilyVertexCount_of_matching s hM).symm

/-- The sum of the edge sizes is additive over a disjoint union of pieces. -/
lemma sumEdgeSizes_disjiUnion {P : Finset (Finset (Set (Fin n)))}
    (hpd : (P : Set (Finset (Set (Fin n)))).PairwiseDisjoint id) :
    sumEdgeSizes (P.disjiUnion id hpd) =
      P.sum (fun M : Finset (Set (Fin n)) => sumEdgeSizes M) := by
  classical
  unfold sumEdgeSizes
  simpa using
    (Finset.sum_disjiUnion (s := P) (t := id) hpd (f := fun e : Set (Fin n) => edgeSize e))

/-- Sums of edge sizes are monotone in the family. -/
lemma sumEdgeSizes_mono {s t : Finset (Set (Fin n))} (hst : s ⊆ t) :
    sumEdgeSizes s ≤ sumEdgeSizes t := by
  classical
  unfold sumEdgeSizes
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (by intro x _hx _hnx; exact Nat.zero_le (edgeSize x))

/-- A family of edges all lying in a matching family, pairwise edge-disjoint,
has total covered-vertex count at most the covered-vertex count of the
matching: `Σ_{M∈P} |V(M)| = |V(⋃P)| ≤ |V(F)|` (for matching pieces the
covered-vertex count equals the sum of edge sizes, which is additive over
the disjoint union). -/
lemma sum_FamilyVertexCount_le {F : Finset (Set (Fin n))}
    (P : Finset (Finset (Set (Fin n))))
    (hpieceMatch : ∀ M ∈ P, IsMatchingFamily M)
    (hdisjP : ∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂)
    (hsub : ∀ M ∈ P, M ⊆ F) (hFmatch : IsMatchingFamily F) :
    P.sum (fun M => FamilyVertexCount M) ≤ FamilyVertexCount F := by
  classical
  have hpd : (P : Set (Finset (Set (Fin n)))).PairwiseDisjoint id := by
    intro M₁ hM₁ M₂ hM₂ hne
    exact hdisjP M₁ hM₁ M₂ hM₂ hne
  calc
    P.sum (fun M => FamilyVertexCount M)
        = P.sum (fun M => sumEdgeSizes M) := by
            apply Finset.sum_congr rfl
            intro M hM
            exact FamilyVertexCount_eq_sumEdgeSizes_of_matching (hpieceMatch M hM)
    _ = sumEdgeSizes (P.disjiUnion id hpd) := (sumEdgeSizes_disjiUnion hpd).symm
    _ ≤ sumEdgeSizes F := by
            apply sumEdgeSizes_mono
            intro e he
            rcases (Finset.mem_disjiUnion.mp he) with ⟨M, hM, heM⟩
            exact hsub M hM heM
    _ = FamilyVertexCount F := sumEdgeSizes_eq_FamilyVertexCount_of_matching F hFmatch

/-- The threshold `⌈αn/2⌉` is at least `1` once `α > 0` and `n ≥ 1`. -/
lemma one_le_SplitThreshold {α : ℝ} {n : ℕ} (hα : 0 < α) (hn : 1 ≤ n) :
    1 ≤ SplitThreshold α n := by
  have hx : 0 < (α / 2 : ℝ) * (n : ℝ) := by
    have hα2 : 0 < α / 2 := half_pos hα
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    exact mul_pos hα2 hn0
  by_contra h
  have hle : SplitThreshold α n ≤ 0 := by
    have hlt : SplitThreshold α n < 1 := lt_of_not_ge h
    omega
  have hxle : (α / 2 : ℝ) * (n : ℝ) ≤ (0 : ℝ) := by
    simpa using (Nat.ceil_le.mp hle)
  linarith

/-- **Honest colour-class splitting theorem.**  Every colour class of every
proper edge-colouring of a hypergraph with positive edge sizes splits into
at most `2/α + 1` pairwise edge-disjoint matching pieces, each a subfamily
of the colour class and either a single edge or covering fewer than
`αn + 1` vertices, and every edge of the class lies in exactly one piece. -/
theorem splitColourClassHonest {α : ℝ} (hα : 0 < α) (hn : 1 ≤ n)
    {𝓗 : Hypergraph (Fin n)} (hpos : ∀ e ∈ 𝓗, 1 ≤ edgeSize e) :
    SplitColourClassHonest α 𝓗 := by
  classical
  intro φ c
  let F : Finset (Set (Fin n)) := EdgeSetFamily (φ.colorClass c)
  have hαle : 0 ≤ α := le_of_lt hα
  have hA1 : 1 ≤ SplitThreshold α n := one_le_SplitThreshold hα hn
  rcases splitColourClassMargin hαle hA1 (𝓗 := 𝓗) hpos φ c with
    ⟨P, left, hOK, hDisjP, hDisjL, hMatchL, hLeftCov, hcover⟩
  let P' : Finset (Finset (Set (Fin n))) := insert left P
  -- pieces (and the leftover) are subfamilies of the colour class
  have hsubP : ∀ M ∈ P, M ⊆ EdgeSetFamily (φ.colorClass c) := by
    intro M hM e he
    exact (hcover e).2 (Or.inl ⟨M, hM, he⟩)
  have hsubL : left ⊆ EdgeSetFamily (φ.colorClass c) := by
    intro e he
    exact (hcover e).2 (Or.inr he)
  have hsubBoth : ∀ M ∈ P', M ⊆ EdgeSetFamily (φ.colorClass c) := by
    intro M hM
    dsimp [P'] at hM
    simp at hM
    rcases hM with rfl | hM
    · exact hsubL
    · exact hsubP M hM
  -- every piece is an admissible `SplitPieceOK`
  have hOK' : ∀ M ∈ P', SplitPieceOK α M := by
    intro M hM
    dsimp [P'] at hM
    simp at hM
    rcases hM with hEq | hM
    · have hML : M = left := by simpa [eq_comm] using hEq
      constructor
      · simpa [hML] using hMatchL
      · right
        have hcast : (FamilyVertexCount left : ℝ) < (SplitThreshold α n : ℝ) := by
          exact_mod_cast hLeftCov
        have hltL : (FamilyVertexCount left : ℝ) < (α : ℝ) * (n : ℝ) + 1 :=
          hcast.trans (SplitThreshold_lt_alpha_add_one hαle)
        simpa [hML] using hltL
    · rcases hOK M hM with ⟨hMatch, _hCov, hOneOrBdd⟩
      exact ⟨hMatch, hOneOrBdd⟩
  -- exact-once cover
  have hOnce : ∀ e : Set (Fin n), e ∈ EdgeSetFamily (φ.colorClass c) →
      ∃! M : Finset (Set (Fin n)), M ∈ P' ∧ e ∈ M := by
    intro e he
    have hc := (hcover e).1 he
    have hfold := fold_leftover_exactly_once P left hDisjP hDisjL e hc
    simpa [P'] using hfold
  -- count bound
  have hFmatch : IsMatchingFamily F := by
    dsimp [F]
    exact IsMatchingFamily_of_IsMatching (Hypergraph.Coloring.colorClass_isMatching φ c)
  have hFVC_le : FamilyVertexCount F ≤ n := by
    dsimp [F]
    rw [← classVertexCount_eq_FamilyVertexCount]
    exact classVertexCount_le_n φ c
  have hsum_le : P.sum (fun M => FamilyVertexCount M) ≤ n := by
    calc
      P.sum (fun M => FamilyVertexCount M) ≤ FamilyVertexCount F :=
            sum_FamilyVertexCount_le (F := F) P (fun M hM => (hOK M hM).1) hDisjP hsubP hFmatch
      _ ≤ n := hFVC_le
  have hc_pos : (0 : ℝ) < (α / 2 : ℝ) * (n : ℝ) := by
    exact mul_pos (half_pos hα) (by exact_mod_cast hn)
  have hpiece_low : ∀ M ∈ P, ((α / 2 : ℝ) * (n : ℝ)) ≤ (FamilyVertexCount M : ℝ) := by
    intro M hM
    exact (hOK M hM).2.1
  have hCardP : ((P.card : ℕ) : ℝ) ≤ (2 : ℝ) / α := by
    have hreal_sum : P.sum (fun M : Finset (Set (Fin n)) => (FamilyVertexCount M : ℝ)) ≤ (n : ℝ) := by
      calc
        P.sum (fun M : Finset (Set (Fin n)) => (FamilyVertexCount M : ℝ))
            = ((P.sum (fun M => FamilyVertexCount M) : ℕ) : ℝ) := by
              exact (Nat.cast_sum (s := P) (f := fun M : Finset (Set (Fin n)) => FamilyVertexCount M)).symm
        _ ≤ (n : ℝ) := by exact_mod_cast hsum_le
    have hsum_low : ((P.card : ℕ) : ℝ) * ((α / 2 : ℝ) * (n : ℝ)) ≤
        P.sum (fun M : Finset (Set (Fin n)) => (FamilyVertexCount M : ℝ)) := by
      calc
        ((P.card : ℕ) : ℝ) * ((α / 2 : ℝ) * (n : ℝ))
            = P.sum (fun M : Finset (Set (Fin n)) => (α / 2 : ℝ) * (n : ℝ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ P.sum (fun M : Finset (Set (Fin n)) => (FamilyVertexCount M : ℝ)) := by
              exact Finset.sum_le_sum (by intro M hM; exact hpiece_low M hM)
    have hcard_le : ((P.card : ℕ) : ℝ) ≤ (n : ℝ) / ((α / 2 : ℝ) * (n : ℝ)) := by
      exact (le_div_iff₀ hc_pos).mpr (hsum_low.trans hreal_sum)
    have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    calc
      ((P.card : ℕ) : ℝ) ≤ (n : ℝ) / ((α / 2 : ℝ) * (n : ℝ)) := hcard_le
      _ = (2 : ℝ) / α := by
        field_simp [hα.ne', hnz]
  have hCardP' : ((P'.card : ℕ) : ℝ) ≤ (2 : ℝ) / α + 1 := by
    have hle : P'.card ≤ P.card + 1 := by
      dsimp [P']
      exact Finset.card_insert_le left P
    have hcast : ((P'.card : ℕ) : ℝ) ≤ ((P.card : ℕ) : ℝ) + 1 := by exact_mod_cast hle
    exact hcast.trans (by linarith)
  exact ⟨P', hsubBoth, hOK', hOnce, hCardP'⟩

/-- At the *halved* parameter `β/2` the margin bound of a piece becomes
strict once `βn ≥ 2`: `FVC M < βn/2 + 1 ≤ βn`.  This is how the `+1` margin
is absorbed by the α-bounded recolouring step of `few-large-colour-classes`
(ii): apply `splitColourClassHonest` with `β/2` and obtain pieces covering
at most `βn` vertices. -/
theorem SplitPieceOK_half_strict {β : ℝ} (hβ2 : (2 : ℝ) ≤ β * (n : ℝ))
    {M : Finset (Set (Fin n))} (hM : SplitPieceOK (β / 2) M) :
    M.card = 1 ∨ (FamilyVertexCount M : ℝ) ≤ β * (n : ℝ) := by
  rcases hM with ⟨_hMatch, hOneOrBdd⟩
  rcases hOneOrBdd with hOne | hBdd
  · exact Or.inl hOne
  · right
    have hle : (β / 2 : ℝ) * (n : ℝ) + 1 ≤ β * (n : ℝ) := by
      nlinarith
    exact le_of_lt (hBdd.trans_le hle)

/-!
## Next step: done — see `AlphaBoundedColouring.lean`

The recolouring step of Prop 6.8(ii) is proved in
`AlphaBoundedColouring.lean` (`alpha_bounded_recolour`), using this file's
`splitColourClassHonest` at the halved parameter `β/2`, the strictness
corollary `SplitPieceOK_half_strict`, host-independent
`Coloring.AlphaBounded`, and the colouring-from-family machinery
(`colouringOfFamilies_fin_AlphaBounded`).  Big colour classes (covering
`> βn/2`) are split into at most `2/(β/2)+1` pieces each (single edge or
`≤ βn` vertices); the classes outside are kept; the resulting β-bounded
colouring uses at most `|C| + (2/(β/2)+1)·n/((β/2)r)` colours.  The
`2n/(β²r)`-type additive of the paper appears with an absolute constant,
which the `≪`-hierarchy absorbs.
-/
