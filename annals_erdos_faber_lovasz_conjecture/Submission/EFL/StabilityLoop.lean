import Submission.EFL.Reordering
import Submission.EFL.SubfamilyConcat
import Submission.Commons.Data.Finset.restrict_ordering

/-!
# The stability loop of Theorem 1.3

The proof of the paper's stability theorem (Theorem 1.3, `weak-stability-thm`)
repeatedly applies the reordering lemma (Lemma 6.2), extracting the bad
"volume" blocks `W₁, W₂, …` and keeping the good blocks `𝓗_i^good`; the
`W_i` are pairwise disjoint with `vol(W_i) ≥ ε²⁰`, so the loop terminates
after at most `ε^{-20} + 1` steps, and the good part `𝓗^good = ⊔_i
𝓗_i^good` carries an ordering with forward degree `≤ εn/6` (hence is
colourable with `εn/3` colours by Proposition 6.9), while the `W_i` are
coloured by the locally-sparse corollary `corollary_6_7` (Alon–Krivlevich–
Sudakov).

This module develops the loop.  The first part provides the subfamily-level
volume bookkeeping: the subfamily `finFam S` of a `𝓗`-finset `S`
(`mem_finFam`), with the identification of the two volume notions
(`volume_finFam`), and monotonicity/additivity of the subfamily volume
`volume n` under inclusion and disjoint union
(`volume_subfamily_mono`, `volume_subfamily_union`).
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The subfamily of `𝓗` consisting of the members of a `𝓗`-finset. -/
def finFam {𝓗 : Hypergraph (Fin n)} (S : Finset 𝓗) : Hypergraph (Fin n) :=
  {e | ∃ he : e ∈ 𝓗, (⟨e, he⟩ : 𝓗) ∈ S}

lemma mem_finFam {𝓗 : Hypergraph (Fin n)} {S : Finset 𝓗} {e : Set (Fin n)} :
    e ∈ finFam S ↔ ∃ he : e ∈ 𝓗, (⟨e, he⟩ : 𝓗) ∈ S := Iff.rfl

lemma finFam_subset {𝓗 : Hypergraph (Fin n)} (S : Finset 𝓗) : finFam S ⊆ 𝓗 :=
  fun _ he => he.choose

/-- `|e|(|e|−1)` agrees in `ℕ` and `ℝ` (using `|e| − 1 = 0` in `ℕ` when
`|e| = 0`). -/
lemma cast_edgeTerm (a : ℕ) : ((a : ℝ) * ((a : ℝ) - 1)) = ((a * (a - 1) : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; norm_num
  · push_cast [Nat.cast_sub h]; ring

/-- The two volume notions agree: the volume of a `𝓗`-finset is the volume of
the corresponding subfamily. -/
theorem volume_finFam {𝓗 : Hypergraph (Fin n)} (S : Finset 𝓗) :
    Hypergraph.volume 𝓗 S = volume n (finFam S) := by
  classical
  have himg : (Finset.univ.filter (fun e : Set (Fin n) => e ∈ finFam S))
      = S.image (fun e : 𝓗 => (e : Set (Fin n))) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, mem_finFam]
    constructor
    · rintro ⟨he𝓗, hmem⟩
      exact ⟨⟨e, he𝓗⟩, hmem, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
  simp only [Hypergraph.volume, volume]
  congr 1
  rw [himg, Finset.sum_image]
  · rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun e _ => cast_edgeTerm (edgeSize (e : Set (Fin n))))
  · intro a _ b _ hab
    exact Subtype.ext hab

/-- The canonical finset of edges of a hypergraph on `Fin n`. -/
def canonFinset (𝓖 : Hypergraph (Fin n)) : Finset (Set (Fin n)) := by
  classical
  exact (Finset.univ : Finset (Set (Fin n))).filter (fun e => e ∈ 𝓖)

/-- The volume of a subfamily, in terms of its canonical finset. -/
lemma volume_eq_canon (𝓖 : Hypergraph (Fin n)) :
    volume n 𝓖 = (((canonFinset 𝓖).sum
      (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) : ℕ) : ℝ)
      / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
  simp only [volume, canonFinset]

/-- Volume is monotone under inclusion of subfamilies. -/
theorem volume_subfamily_mono {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗) :
    volume n 𝓖 ≤ volume n 𝓗 := by
  classical
  rw [volume_eq_canon, volume_eq_canon]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsum : (canonFinset 𝓖).sum (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1))
      ≤ (canonFinset 𝓗).sum (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      simp only [canonFinset, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact hsub he
    · intro e _ _
      exact Nat.zero_le _
  exact_mod_cast hsum

/-- Volume is additive over disjoint subfamilies. -/
theorem volume_subfamily_union {𝓖₁ 𝓖₂ : Hypergraph (Fin n)} (hdisj : Disjoint 𝓖₁ 𝓖₂) :
    volume n (𝓖₁ ∪ 𝓖₂) = volume n 𝓖₁ + volume n 𝓖₂ := by
  classical
  rw [volume_eq_canon, volume_eq_canon, volume_eq_canon]
  have hunion : canonFinset (𝓖₁ ∪ 𝓖₂) = canonFinset 𝓖₁ ∪ canonFinset 𝓖₂ := by
    ext e
    simp only [canonFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Set.mem_union]
  have hdisj' : Disjoint (canonFinset 𝓖₁) (canonFinset 𝓖₂) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [canonFinset, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
    exact (Set.disjoint_left.mp hdisj he₁) he₂
  rw [hunion, Finset.sum_union hdisj', Nat.cast_add, add_div]

/-! ## The blocks of one reordering step

One application of the reordering lemma to a family `𝓖` splits (a subfamily
of) `𝓖` into the three blocks of the paper's loop: the part *before* the
first edge `f*` of the volume set (`rankBelow ord fStar`), the *middle*
interval `[f*, e*]`, and the *good* part after `e*`. -/

variable {𝓖 : Hypergraph (Fin n)}

/-- The middle block `[f*, e*]`: the edges of rank between `f*` and `e*`. -/
def midBlock {k : ℕ} (ord : 𝓖 ≃ Fin k) (fStar eStar : 𝓖) : Hypergraph (Fin n) :=
  {e | ∃ he : e ∈ 𝓖, (ord fStar : ℕ) ≤ (ord ⟨e, he⟩ : ℕ) ∧
    (ord ⟨e, he⟩ : ℕ) ≤ (ord eStar : ℕ)}

/-- The good block after `e*`. -/
def goodBlock {k : ℕ} (ord : 𝓖 ≃ Fin k) (eStar : 𝓖) : Hypergraph (Fin n) :=
  {e | ∃ he : e ∈ 𝓖, (ord eStar : ℕ) < (ord ⟨e, he⟩ : ℕ)}

lemma mem_midBlock {k : ℕ} (ord : 𝓖 ≃ Fin k) (fStar eStar : 𝓖) {e : Set (Fin n)}
    (he : e ∈ 𝓖) :
    e ∈ midBlock ord fStar eStar ↔ (ord fStar : ℕ) ≤ (ord ⟨e, he⟩ : ℕ) ∧
      (ord ⟨e, he⟩ : ℕ) ≤ (ord eStar : ℕ) := by
  constructor
  · intro h
    obtain ⟨he', h1, h2⟩ := h
    have hEq : (⟨e, he'⟩ : 𝓖) = ⟨e, he⟩ := Subtype.ext rfl
    rw [hEq] at h1 h2
    exact ⟨h1, h2⟩
  · intro h
    exact ⟨he, h.1, h.2⟩

lemma mem_goodBlock {k : ℕ} (ord : 𝓖 ≃ Fin k) (eStar : 𝓖) {e : Set (Fin n)}
    (he : e ∈ 𝓖) :
    e ∈ goodBlock ord eStar ↔ (ord eStar : ℕ) < (ord ⟨e, he⟩ : ℕ) := by
  constructor
  · intro h
    obtain ⟨he', h1⟩ := h
    have hEq : (⟨e, he'⟩ : 𝓖) = ⟨e, he⟩ := Subtype.ext rfl
    rw [hEq] at h1
    exact h1
  · intro h
    exact ⟨he, h⟩

lemma midBlock_subset {k : ℕ} (ord : 𝓖 ≃ Fin k) (fStar eStar : 𝓖) :
    midBlock ord fStar eStar ⊆ 𝓖 := fun _ h => h.choose

lemma goodBlock_subset {k : ℕ} (ord : 𝓖 ≃ Fin k) (eStar : 𝓖) :
    goodBlock ord eStar ⊆ 𝓖 := fun _ h => h.choose

/-- **The three blocks cover `𝓖`** (given `f* ⪯ e*`, which holds in the
volume case). -/
lemma cover_blocks {k : ℕ} (ord : 𝓖 ≃ Fin k) {fStar eStar : 𝓖}
    (hfe : (ord fStar : ℕ) ≤ (ord eStar : ℕ)) :
    rankBelow ord fStar ∪ midBlock ord fStar eStar ∪ goodBlock ord eStar = 𝓖 := by
  ext e
  constructor
  · rintro (h | h)
    · rcases h with h | h
      · exact (rankBelow_subset ord fStar) h
      · exact (midBlock_subset ord fStar eStar) h
    · exact (goodBlock_subset ord eStar) h
  · intro he
    by_cases h1 : (ord ⟨e, he⟩ : ℕ) < (ord fStar : ℕ)
    · exact Or.inl (Or.inl ⟨he, h1⟩)
    · rw [not_lt] at h1
      by_cases h2 : (ord ⟨e, he⟩ : ℕ) ≤ (ord eStar : ℕ)
      · exact Or.inl (Or.inr ((mem_midBlock ord fStar eStar he).mpr ⟨h1, h2⟩))
      · rw [not_le] at h2
        exact Or.inr ((mem_goodBlock ord eStar he).mpr h2)

/-- The blocks are pairwise disjoint. -/
lemma disjoint_rankBelow_midBlock {k : ℕ} (ord : 𝓖 ≃ Fin k) (fStar eStar : 𝓖) :
    Disjoint (rankBelow ord fStar) (midBlock ord fStar eStar) := by
  rw [Set.disjoint_left]
  intro e h1 h2
  obtain ⟨he, hlt⟩ := h1
  have hle := ((mem_midBlock ord fStar eStar he).mp h2).1
  exact absurd hle (not_le.mpr hlt)

lemma disjoint_midBlock_goodBlock {k : ℕ} (ord : 𝓖 ≃ Fin k) (fStar eStar : 𝓖) :
    Disjoint (midBlock ord fStar eStar) (goodBlock ord eStar) := by
  rw [Set.disjoint_left]
  intro e h1 h2
  obtain ⟨he, -, hle⟩ := h1
  have hlt := ((mem_goodBlock ord eStar he).mp h2)
  exact absurd hle (not_le.mpr hlt)

lemma disjoint_rankBelow_goodBlock {k : ℕ} (ord : 𝓖 ≃ Fin k) (fStar eStar : 𝓖)
    (hfe : (ord fStar : ℕ) ≤ (ord eStar : ℕ)) :
    Disjoint (rankBelow ord fStar) (goodBlock ord eStar) := by
  rw [Set.disjoint_left]
  intro e h1 h2
  obtain ⟨he, hlt⟩ := h1
  have hlt' := ((mem_goodBlock ord eStar he).mp h2)
  omega

/-- **(O1) for the good block**: every edge of the good block has preceding
degree at most `(1−τ)n`. -/
lemma goodBlock_precedingDegree_le {k : ℕ} {τ : ℝ} (ord : 𝓖 ≃ Fin k) {eStar : 𝓖}
    (hO1 : OrderingGoodness τ ord eStar) {e : Set (Fin n)} (he : e ∈ goodBlock ord eStar) :
    (precedingDegree 𝓖 ord ⟨e, (he.choose : e ∈ 𝓖)⟩ : ℝ) ≤ (1 - τ) * (n : ℝ) := by
  obtain ⟨he𝓖, hlt⟩ := he
  refine hO1 ⟨e, he𝓖⟩ (le_of_lt hlt) ?_
  intro hc
  have : (ord eStar : ℕ) < (ord eStar : ℕ) := by
    have hEq : (⟨e, he𝓖⟩ : 𝓖) = eStar := hc
    rw [hEq] at hlt
    exact hlt
  exact absurd this (lt_irrefl _)

/-- **(O2) for the middle block**: `|e*|` is the minimum size in the middle
block. -/
lemma midBlock_size_ge {k : ℕ} (ord : 𝓖 ≃ Fin k) {fStar eStar : 𝓖}
    (hO2 : OrderingBySize ord eStar) {e : Set (Fin n)} (he : e ∈ midBlock ord fStar eStar) :
    (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize e : ℝ) := by
  obtain ⟨he𝓖, -, h2⟩ := he
  exact hO2 (e := eStar) (f := ⟨e, he𝓖⟩) h2 le_rfl

/-- **One reordering step**: from a volume witness at `(τ, K)` we extract the
distinguished edges `f*` (the first edge of the volume set) and `e*`, the
size bounds on the middle block (`|e*| ≤ |e| ≤ A·|e*|`), the volume bound
`vol([f*, e*]) ≥ volBound τ K`, and `e*`'s membership in the middle block. -/
theorem exists_step_data {k : ℕ} {τ : ℝ} {K : ℕ} (hvol0 : 0 < volBound τ K)
    {ord : 𝓖 ≃ Fin k} (hW : VolumeWitness τ K ord) :
    ∃ fStar eStar : 𝓖,
      (ord fStar : ℕ) ≤ (ord eStar : ℕ) ∧
      (∀ e : 𝓖, (ord fStar : ℕ) ≤ (ord e : ℕ) → (ord e : ℕ) ≤ (ord eStar : ℕ) →
        (edgeSize (e : Set (Fin n)) : ℝ) ≤ sizeFactor τ K * (edgeSize (eStar : Set (Fin n)) : ℝ)) ∧
      (∀ e : 𝓖, (ord e : ℕ) ≤ (ord eStar : ℕ) →
        (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ)) ∧
      (eStar : Set (Fin n)) ∈ midBlock ord fStar eStar ∧
      volBound τ K ≤ volume n (midBlock ord fStar eStar) := by
  classical
  obtain ⟨eStar, W, hWle, hWmax, hWvol, hO1, hO2, heStarW⟩ := hW
  have hWvol' : volBound τ K ≤ Hypergraph.volume 𝓖 W := hWvol
  have hWne : W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have h0 : Hypergraph.volume 𝓖 W = 0 := by simp [hemp, Hypergraph.volume]
    rw [h0] at hWvol'
    linarith
  obtain ⟨fStar, hfStarW, hfStarMin⟩ := Finset.exists_min_image W (fun e : 𝓖 => (ord e : ℕ)) hWne
  refine ⟨fStar, eStar, hfStarMin eStar heStarW, ?_, ?_, ?_, ?_⟩
  · intro e he1 he2
    have h1 : (edgeSize (e : Set (Fin n)) : ℝ) ≤ (edgeSize (fStar : Set (Fin n)) : ℝ) :=
      hO2 (e := e) (f := fStar) he1 he2
    have h2 : (edgeSize (fStar : Set (Fin n)) : ℝ) ≤
        sizeFactor τ K * (edgeSize (eStar : Set (Fin n)) : ℝ) := hWmax hfStarW heStarW
    exact h1.trans h2
  · intro e he
    exact hO2 (e := eStar) (f := e) he le_rfl
  · exact (mem_midBlock ord fStar eStar eStar.2).mpr
      ⟨hfStarMin eStar heStarW, le_rfl⟩
  · have hsub : finFam W ⊆ midBlock ord fStar eStar := by
      intro e he
      obtain ⟨he𝓖, hmem⟩ := mem_finFam.mp he
      have h1 : (ord fStar : ℕ) ≤ (ord ⟨e, he𝓖⟩ : ℕ) := hfStarMin ⟨e, he𝓖⟩ hmem
      have h2 : (ord ⟨e, he𝓖⟩ : ℕ) ≤ (ord eStar : ℕ) := hWle ⟨e, he𝓖⟩ hmem
      exact (mem_midBlock ord fStar eStar he𝓖).mpr ⟨h1, h2⟩
    calc volBound τ K ≤ Hypergraph.volume 𝓖 W := hWvol'
      _ = volume n (finFam W) := volume_finFam W
      _ ≤ volume n (midBlock ord fStar eStar) := volume_subfamily_mono hsub

/-! ## Restricted orderings of a subfamily

Given an ordering of `𝓖` and a subfamily `𝓖' ⊆ 𝓖`, the induced ordering of
`𝓖'` (its rank function) has no larger preceding degrees
(`exists_restricted_ordering`).  This is what turns the "good blocks" of the
loop into families with an ordering satisfying the greedy hypothesis. -/

variable {𝓖 : Hypergraph (Fin n)}

/-- **The induced ordering of a subfamily**: for `𝓖' ⊆ 𝓖` and an ordering
`ord` of `𝓖`, there is an ordering `ord'` of `𝓖'` agreeing with `ord` on the
ranks, and every preceding degree in `𝓖'` is at most the corresponding
preceding degree in `𝓖`. -/
theorem exists_restricted_ordering {k : ℕ} (ord : 𝓖 ≃ Fin k) {𝓖' : Hypergraph (Fin n)}
    (hsub : 𝓖' ⊆ 𝓖) :
    ∃ (m : ℕ) (ord' : 𝓖' ≃ Fin m),
      (∀ e f : 𝓖', (ord' e : ℕ) ≤ (ord' f : ℕ) ↔
        (ord ⟨e.1, hsub e.2⟩ : ℕ) ≤ (ord ⟨f.1, hsub f.2⟩ : ℕ)) ∧
      (∀ e : 𝓖', precedingDegree 𝓖' ord' e ≤
        precedingDegree 𝓖 ord ⟨e.1, hsub e.2⟩) := by
  classical
  haveI : Fintype 𝓖 := Fintype.ofFinite 𝓖
  haveI : Fintype (Set (Fin n)) := Fintype.ofFinite (Set (Fin n))
  set S : Finset 𝓖 := (Finset.univ : Finset 𝓖).filter (fun e => (e : Set (Fin n)) ∈ 𝓖') with hS
  obtain ⟨ordS, hordS⟩ := Commons.Data.Finset.restrict_ordering S ord
  let toFun : ↥S → 𝓖' := fun e => ⟨(e.1 : Set (Fin n)), (Finset.mem_filter.mp e.2).2⟩
  let invFun : 𝓖' → ↥S := fun e => ⟨⟨(e.1 : Set (Fin n)), hsub e.2⟩,
    by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro e; exact Subtype.ext (Subtype.ext rfl)
  have hright : Function.RightInverse invFun toFun := by
    intro e; exact Subtype.ext rfl
  let e1 : 𝓖' ≃ ↥S := ⟨invFun, toFun, hright, hleft⟩
  refine ⟨S.card, e1.trans ordS, ?_, ?_⟩
  · intro e f
    have h1 : (e1.trans ordS) e = ordS (invFun e) := rfl
    have h2 : (e1.trans ordS) f = ordS (invFun f) := rfl
    rw [h1, h2]
    exact hordS (invFun e) (invFun f)
  · intro e
    rw [precedingDegree_eq_natCard, precedingDegree_eq_natCard]
    have hiff : ∀ a b : 𝓖', ((e1.trans ordS) a : ℕ) ≤ ((e1.trans ordS) b : ℕ) ↔
        (ord ⟨a.1, hsub a.2⟩ : ℕ) ≤ (ord ⟨b.1, hsub b.2⟩ : ℕ) := by
      intro a b
      have h1 : (e1.trans ordS) a = ordS (invFun a) := rfl
      have h2 : (e1.trans ordS) b = ordS (invFun b) := rfl
      rw [h1, h2]
      exact hordS (invFun a) (invFun b)
    refine Nat.card_le_card_of_injective (fun f : {f : 𝓖' // f ≠ e ∧ (e1.trans ordS) f ≤
          (e1.trans ordS) e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} =>
        (⟨⟨f.1.1, hsub f.1.2⟩, ?_, ?_, ?_⟩ :
          {g : 𝓖 // g ≠ ⟨e.1, hsub e.2⟩ ∧ ord g ≤ ord ⟨e.1, hsub e.2⟩ ∧
            ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty})) ?_
    · intro hc
      exact f.2.1 (Subtype.ext (by
        have hh := congrArg (fun x : 𝓖 => (x.1 : Set (Fin n))) hc
        simpa using hh))
    · have hle : ((e1.trans ordS) f.1 : ℕ) ≤ ((e1.trans ordS) e : ℕ) := by
        rw [← Fin.le_iff_val_le_val]; exact f.2.2.1
      rw [Fin.le_iff_val_le_val]
      exact (hiff f.1 e).mp hle
    · exact f.2.2.2
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg
        (fun x : {g : 𝓖 // g ≠ ⟨e.1, hsub e.2⟩ ∧ ord g ≤ ord ⟨e.1, hsub e.2⟩ ∧
          ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} => (x.1.1 : Set (Fin n))) hab))

/-! ## The decomposition produced by the stability loop

The output of the loop of Theorem 1.3, as the interface consumed by the
assembly: a list of "bad" blocks (each a subfamily with a distinguished edge
`e*`, of size within the factor `sizeFactor τ K` of every member and of
volume `≥ volBound τ K`), pairwise disjoint and disjoint from the good part,
covering `𝓖`; and the good part with an ordering whose preceding degrees are
at most `(1−τ)n` (so it is colourable by `Prop 6.9`/`prop69Instance`). -/

structure VolumeDecomposition {n : ℕ} (𝓖 : Hypergraph (Fin n)) (τ : ℝ) (K : ℕ) where
  /-- the volume blocks, each with its distinguished edge -/
  blocks : List (Σ W : Hypergraph (Fin n), {e : Set (Fin n) // e ∈ W})
  /-- the good part -/
  good : Hypergraph (Fin n)
  /-- the number of colours of the good ordering -/
  kg : ℕ
  /-- the ordering of the good part -/
  ord : good ≃ Fin kg
  /-- each block is a subfamily of `𝓖` -/
  hBlockSub : ∀ B ∈ blocks, B.1 ⊆ 𝓖
  /-- each block has volume at least `volBound τ K` -/
  hBlockVol : ∀ B ∈ blocks, volBound τ K ≤ volume n B.1
  /-- the distinguished edge is a *smallest* edge of its block -/
  hBlockMin : ∀ B ∈ blocks, ∀ e : Set (Fin n), e ∈ B.1 →
    (edgeSize (B.2 : Set (Fin n)) : ℝ) ≤ (edgeSize e : ℝ)
  /-- every edge of the block is at most `sizeFactor τ K` times the
  distinguished edge -/
  hBlockMax : ∀ B ∈ blocks, ∀ e : Set (Fin n), e ∈ B.1 →
    (edgeSize e : ℝ) ≤ sizeFactor τ K * (edgeSize (B.2 : Set (Fin n)) : ℝ)
  /-- the blocks are pairwise disjoint -/
  hBlocksDisj : blocks.Pairwise (fun B C => Disjoint B.1 C.1)
  /-- the good part is a subfamily of `𝓖` -/
  hGoodSub : good ⊆ 𝓖
  /-- the good part is disjoint from every block -/
  hGoodDisj : ∀ B ∈ blocks, Disjoint good B.1
  /-- good part and blocks cover `𝓖` -/
  hCover : ∀ e : Set (Fin n), e ∈ 𝓖 ↔ e ∈ good ∨ ∃ B ∈ blocks, e ∈ B.1
  /-- the good ordering has preceding degrees at most `(1−τ)n` -/
  hGood : ∀ e : good, (precedingDegree good ord e : ℝ) ≤ (1 - τ) * (n : ℝ)

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The loop of Theorem 1.3: the volume decomposition

The reordering lemma is applied repeatedly: each application either gives a
*good* ordering (and the loop stops) or extracts a volume block
`W_i = [f*, e*]` of volume `≥ volBound τ K`.  The blocks are pairwise
disjoint subfamilies of `𝓖`, so the process terminates after at most
`vol(𝓖)/volBound τ K` steps.  `exists_volumeDecomposition` is the resulting
strong induction on that ratio. -/

/-- The size-similarity factor `1 + 3τ^{1/4}K⁴` is positive. -/
lemma sizeFactor_pos (τ : ℝ) (K : ℕ) : 0 < sizeFactor τ K := by
  have h1 : (0 : ℝ) ≤ tauQuarter τ := tauQuarter_nonneg τ
  have h2 : (0 : ℝ) ≤ (K : ℝ) ^ 4 := by positivity
  rw [sizeFactor]
  nlinarith

/-- The volume bound `q²/A` of the reordering lemma is positive under the
reordering margins. -/
lemma volBound_pos {r₁ : ℕ} {τ : ℝ} {K : ℕ} (hm : ReorderingMargins r₁ τ K) :
    0 < volBound τ K := by
  rw [volBound]
  exact div_pos (pow_pos (rm_q_pos hm) 2) (sizeFactor_pos τ K)

/-- The good block is contained in the `f*`-span. -/
lemma goodBlock_subset_rankAbove {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ} (ord : 𝓖 ≃ Fin k)
    {fStar eStar : 𝓖} (hfe : (ord fStar : ℕ) ≤ (ord eStar : ℕ)) :
    goodBlock ord eStar ⊆ rankAbove ord fStar := by
  rintro e ⟨he, hlt⟩
  exact ⟨he, le_trans hfe (le_of_lt hlt)⟩

/-- **Counting the preceding neighbours of a good-block edge.**  For
`e ∈ goodBlock ord e*`, the preceding neighbours of `e` in `𝓖` comprise the
members of any subfamily `𝓖₁ ⊆ rankBelow ord f*` meeting `e`, together with
the preceding neighbours of `e` inside `goodBlock ord e*`. -/
lemma card_meet_add_precedingDegree_le {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ}
    (ord : 𝓖 ≃ Fin k) {fStar eStar : 𝓖} (hb : goodBlock ord eStar ⊆ 𝓖)
    (hfe : (ord fStar : ℕ) ≤ (ord eStar : ℕ))
    {𝓖₁ : Hypergraph (Fin n)} (hsub₁ : 𝓖₁ ⊆ rankBelow ord fStar)
    {k₂ : ℕ} (ord₂ : goodBlock ord eStar ≃ Fin k₂)
    (hrank₂ : ∀ a b : goodBlock ord eStar, (ord₂ a : ℕ) ≤ (ord₂ b : ℕ) ↔
      (ord ⟨a.1, hb a.2⟩ : ℕ) ≤ (ord ⟨b.1, hb b.2⟩ : ℕ))
    (e : goodBlock ord eStar) :
    Nat.card {f : 𝓖₁ // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} +
      precedingDegree (goodBlock ord eStar) ord₂ e ≤
      precedingDegree 𝓖 ord ⟨e.1, hb e.2⟩ := by
  classical
  have h𝓖₁ : ∀ x : Set (Fin n), x ∈ 𝓖₁ → x ∈ 𝓖 :=
    fun x hx => rankBelow_subset ord fStar (hsub₁ hx)
  have hrankBelow₁ : ∀ a : {f : 𝓖₁ // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty},
      (ord ⟨a.1.1, h𝓖₁ a.1.1 a.1.2⟩ : ℕ) < (ord fStar : ℕ) := fun a =>
    (mem_rankBelow ord fStar (h𝓖₁ a.1.1 a.1.2)).mp (hsub₁ a.1.2)
  have heStar_lt : (ord eStar : ℕ) < (ord ⟨e.1, hb e.2⟩ : ℕ) :=
    (mem_goodBlock ord eStar (hb e.2)).mp e.2
  rw [precedingDegree_eq_natCard (goodBlock ord eStar) ord₂ e,
    precedingDegree_eq_natCard 𝓖 ord ⟨e.1, hb e.2⟩]
  let A : Type := {f : 𝓖₁ // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}
  let B : Type := {g : goodBlock ord eStar // g ≠ e ∧ ord₂ g ≤ ord₂ e ∧
      ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}
  let C : Type := {g : 𝓖 // g ≠ ⟨e.1, hb e.2⟩ ∧ ord g ≤ ord ⟨e.1, hb e.2⟩ ∧
      ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}
  let FA : A → C := fun a => ⟨⟨a.1.1, h𝓖₁ a.1.1 a.1.2⟩, by
      intro hc
      have hr : (ord ⟨a.1.1, h𝓖₁ a.1.1 a.1.2⟩ : ℕ) = (ord ⟨e.1, hb e.2⟩ : ℕ) :=
        congrArg (fun x : 𝓖 => (ord x : ℕ)) hc
      have h1 := hrankBelow₁ a
      omega, by
      rw [Fin.le_iff_val_le_val]
      have h1 := hrankBelow₁ a
      omega, by
      simpa using a.2⟩
  let FB : B → C := fun b => ⟨⟨b.1.1, hb b.1.2⟩, by
      intro hc
      exact b.2.1 (Subtype.ext (congrArg (fun x : 𝓖 => (x.1 : Set (Fin n))) hc)), by
      rw [Fin.le_iff_val_le_val]
      exact (hrank₂ b.1 e).mp b.2.2.1, by
      simpa using b.2.2.2⟩
  have hFA : Function.Injective FA := by
    intro a a' h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : C => ((x.1 : 𝓖) : Set (Fin n))) h))
  have hFB : Function.Injective FB := by
    intro b b' h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : C => ((x.1 : 𝓖) : Set (Fin n))) h))
  have hF : Function.Injective (fun x : A ⊕ B => match x with
      | Sum.inl a => FA a
      | Sum.inr b => FB b) := by
    rintro (a₁ | a₂) (b₁ | b₂) h
    · exact congrArg Sum.inl (hFA h)
    · exfalso
      have hEq : (⟨a₁.1.1, h𝓖₁ a₁.1.1 a₁.1.2⟩ : 𝓖) = ⟨b₂.1.1, hb b₂.1.2⟩ :=
        congrArg (fun x : C => (x.1 : 𝓖)) h
      have hr : (ord ⟨a₁.1.1, h𝓖₁ a₁.1.1 a₁.1.2⟩ : ℕ) = (ord ⟨b₂.1.1, hb b₂.1.2⟩ : ℕ) :=
        congrArg (fun x : 𝓖 => (ord x : ℕ)) hEq
      have h2 : (ord eStar : ℕ) < (ord ⟨b₂.1.1, hb b₂.1.2⟩ : ℕ) :=
        (mem_goodBlock ord eStar (hb b₂.1.2)).mp b₂.1.2
      have h1 := hrankBelow₁ a₁
      omega
    · exfalso
      have hEq : (⟨a₂.1.1, hb a₂.1.2⟩ : 𝓖) = ⟨b₁.1.1, h𝓖₁ b₁.1.1 b₁.1.2⟩ :=
        congrArg (fun x : C => (x.1 : 𝓖)) h
      have hr : (ord ⟨a₂.1.1, hb a₂.1.2⟩ : ℕ) = (ord ⟨b₁.1.1, h𝓖₁ b₁.1.1 b₁.1.2⟩ : ℕ) :=
        congrArg (fun x : 𝓖 => (ord x : ℕ)) hEq
      have h2 : (ord eStar : ℕ) < (ord ⟨a₂.1.1, hb a₂.1.2⟩ : ℕ) :=
        (mem_goodBlock ord eStar (hb a₂.1.2)).mp a₂.1.2
      have h1 := hrankBelow₁ b₁
      omega
    · exact congrArg Sum.inr (hFB h)
  have hcard := Nat.card_le_card_of_injective _ hF
  rw [Nat.card_sum] at hcard
  exact hcard

/-- The step data of one reordering step, with the witness's edge `e*` fixed
(the variant of `exists_step_data` used by the loop, where `e*` is already
known and only `f*` is extracted). -/
theorem exists_step_data_of {n : ℕ} {𝓖 : Hypergraph (Fin n)} {k : ℕ} {τ : ℝ} {K : ℕ}
    (hvol0 : 0 < volBound τ K) {ord : 𝓖 ≃ Fin k} {eStar : 𝓖} {W : Finset 𝓖}
    (hWle : ∀ f ∈ W, (ord f : ℕ) ≤ (ord eStar : ℕ))
    (hWmax : WMaxSize τ K W) (hWvol : WVolume τ K W)
    (hO2 : OrderingBySize ord eStar) (heStarW : eStar ∈ W) :
    ∃ fStar : 𝓖,
      (ord fStar : ℕ) ≤ (ord eStar : ℕ) ∧
      (∀ e : 𝓖, (ord fStar : ℕ) ≤ (ord e : ℕ) → (ord e : ℕ) ≤ (ord eStar : ℕ) →
        (edgeSize (e : Set (Fin n)) : ℝ) ≤
          sizeFactor τ K * (edgeSize (eStar : Set (Fin n)) : ℝ)) ∧
      (∀ e : 𝓖, (ord e : ℕ) ≤ (ord eStar : ℕ) →
        (edgeSize (eStar : Set (Fin n)) : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ)) ∧
      (eStar : Set (Fin n)) ∈ midBlock ord fStar eStar ∧
      volBound τ K ≤ volume n (midBlock ord fStar eStar) := by
  classical
  have hWne : W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have h0 : Hypergraph.volume 𝓖 W = 0 := by simp [hemp, Hypergraph.volume]
    have h1 : volBound τ K ≤ 0 := by simpa [WVolume, h0] using hWvol
    linarith
  obtain ⟨fStar, hfStarW, hfStarMin⟩ :=
    Finset.exists_min_image W (fun e : 𝓖 => (ord e : ℕ)) hWne
  refine ⟨fStar, hfStarMin eStar heStarW, ?_, ?_, ?_, ?_⟩
  · intro e he1 he2
    have h1 : (edgeSize (e : Set (Fin n)) : ℝ) ≤ (edgeSize (fStar : Set (Fin n)) : ℝ) :=
      hO2 (e := e) (f := fStar) he1 he2
    have h2 : (edgeSize (fStar : Set (Fin n)) : ℝ) ≤
        sizeFactor τ K * (edgeSize (eStar : Set (Fin n)) : ℝ) := hWmax hfStarW heStarW
    exact h1.trans h2
  · intro e he
    exact hO2 (e := eStar) (f := e) he le_rfl
  · exact (mem_midBlock ord fStar eStar eStar.2).mpr ⟨hfStarMin eStar heStarW, le_rfl⟩
  · have hsub : finFam W ⊆ midBlock ord fStar eStar := by
      intro e he
      obtain ⟨he𝓖, hmem⟩ := mem_finFam.mp he
      have h1 : (ord fStar : ℕ) ≤ (ord ⟨e, he𝓖⟩ : ℕ) := hfStarMin ⟨e, he𝓖⟩ hmem
      have h2 : (ord ⟨e, he𝓖⟩ : ℕ) ≤ (ord eStar : ℕ) := hWle ⟨e, he𝓖⟩ hmem
      exact (mem_midBlock ord fStar eStar he𝓖).mpr ⟨h1, h2⟩
    calc volBound τ K ≤ Hypergraph.volume 𝓖 W := hWvol
      _ = volume n (finFam W) := volume_finFam W
      _ ≤ volume n (midBlock ord fStar eStar) := volume_subfamily_mono hsub

/-- The trivial decomposition: a good ordering of `𝓖` needs no volume
blocks. -/
def volumeDecompositionOfGood {n : ℕ} {𝓖 : Hypergraph (Fin n)} {τ : ℝ} {K k : ℕ}
    (ord : 𝓖 ≃ Fin k) (h : GoodOrdering τ ord) : VolumeDecomposition 𝓖 τ K where
  blocks := []
  good := 𝓖
  kg := k
  ord := ord
  hBlockSub := by intro B hB; cases hB
  hBlockVol := by intro B hB; cases hB
  hBlockMin := by intro B hB; cases hB
  hBlockMax := by intro B hB; cases hB
  hBlocksDisj := List.Pairwise.nil
  hGoodSub := fun _ he => he
  hGoodDisj := by intro B hB; cases hB
  hCover := by
    intro e
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨B, hB, -⟩)
      · exact h
      · cases hB
  hGood := h

/-- **The loop of Theorem 1.3.**  A linear hypergraph on `Fin n` all of whose
edges have size at least `r₁`, satisfying the reordering margins, and of
volume at most `M · volBound τ K`, decomposes into pairwise disjoint *volume
blocks* (each of volume `≥ volBound τ K` and of sizes within the factor
`sizeFactor τ K` of its distinguished edge) plus a *good part* carrying an
ordering of forward degree at most `(1−τ)n`. -/
theorem exists_volumeDecomposition {r₁ : ℕ} {τ : ℝ} {K : ℕ} (h2n : 2 ≤ n)
    (h2r1 : 2 ≤ r₁) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hK : 1 ≤ K)
    (hmarg : ReorderingMargins r₁ τ K) :
    ∀ (M : ℕ) (𝓕 : Hypergraph (Fin n)), 𝓕.IsLinear →
      (∀ e ∈ 𝓕, (r₁ : ℝ) ≤ (edgeSize e : ℝ)) →
      volume n 𝓕 ≤ (M : ℝ) * volBound τ K →
      Nonempty (VolumeDecomposition 𝓕 τ K) := by
  classical
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro 𝓕 hlin hsize hvol
    rcases Nat.eq_zero_or_pos M with hM | hM
    · -- no volume left at all: the reordering lemma must be in the good case
      subst hM
      have hvol0 : volume n 𝓕 ≤ 0 := by simpa using hvol
      obtain ⟨k, ord, hg | hw⟩ := reorderingLemma_of_subfamily (𝓗 := 𝓕) (𝓖 := 𝓕) τ K
        (fun _ he => he) h2n h2r1 hτ0 hτ1 hK hmarg hlin hsize
      · exact ⟨volumeDecompositionOfGood ord hg⟩
      · obtain ⟨fStar, eStar, -, -, -, -, hvolMid⟩ :=
          exists_step_data (𝓖 := 𝓕) (volBound_pos hmarg) hw
        have hmono := volume_subfamily_mono (𝓖 := midBlock ord fStar eStar) (𝓗 := 𝓕)
          (midBlock_subset ord fStar eStar)
        have hpos := volBound_pos hmarg
        linarith
    · obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
      obtain ⟨k, ord, hg | hw⟩ := reorderingLemma_of_subfamily (𝓗 := 𝓕) (𝓖 := 𝓕) τ K
        (fun _ he => he) h2n h2r1 hτ0 hτ1 hK hmarg hlin hsize
      · exact ⟨volumeDecompositionOfGood ord hg⟩
      · -- the volume alternative: extract the block `[f*, e*]`
        obtain ⟨eStar, W, hWle, hWmax, hWvol, hO1, hO2, heStarW⟩ := hw
        obtain ⟨fStar, hfe, hsizeMax, hsizeMin, heStarMid, hvolMid⟩ :=
          exists_step_data_of (𝓖 := 𝓕) (ord := ord) (eStar := eStar) (W := W)
            (volBound_pos hmarg) hWle hWmax hWvol hO2 heStarW
        have hvol' : volume n 𝓕 ≤ ((m : ℝ) + 1) * volBound τ K := by
          have h : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
          rwa [h] at hvol
        -- the volume of the part before `f*` is at most `m · volBound`
        have hleft_vol : volume n (rankBelow ord fStar) ≤ (m : ℝ) * volBound τ K := by
          have hdisj := disjoint_rankBelow_midBlock ord fStar eStar
          have hunion := volume_subfamily_union (𝓖₁ := rankBelow ord fStar)
            (𝓖₂ := midBlock ord fStar eStar) hdisj
          have hsubU : rankBelow ord fStar ∪ midBlock ord fStar eStar ⊆ 𝓕 := by
            intro e he
            rcases he with he | he
            · exact rankBelow_subset ord fStar he
            · exact midBlock_subset ord fStar eStar he
          have hmono := volume_subfamily_mono hsubU
          rw [hunion] at hmono
          linarith
        obtain ⟨D⟩ := ih m (by omega) (rankBelow ord fStar)
          (hlin.mono (rankBelow_subset ord fStar))
          (fun e he => hsize e (rankBelow_subset ord fStar he)) hleft_vol
        -- the restricted ordering of the good block
        obtain ⟨k₂, ord₂, hrank₂, -⟩ :=
          exists_restricted_ordering (𝓖 := 𝓕) (𝓖' := goodBlock ord eStar) ord
            (goodBlock_subset ord eStar)
        have hb : goodBlock ord eStar ⊆ 𝓕 := goodBlock_subset ord eStar
        -- the (O1) bound for the good block, in the concatenation form
        have h₂ : ∀ e : goodBlock ord eStar,
            ((Nat.card {f : D.good // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℝ) +
              (precedingDegree (goodBlock ord eStar) ord₂ e : ℝ)) ≤ (1 - τ) * (n : ℝ) := by
          intro e
          have hcount := card_meet_add_precedingDegree_le (𝓖 := 𝓕) ord hb hfe
            D.hGoodSub ord₂ hrank₂ e
          have hle : ((precedingDegree 𝓕 ord ⟨e.1, hb e.2⟩ : ℕ) : ℝ) ≤ (1 - τ) * (n : ℝ) :=
            goodBlock_precedingDegree_le (𝓖 := 𝓕) (τ := τ) (eStar := eStar) ord hO1 e.2
          have hcast : ((Nat.card {f : D.good // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} +
              precedingDegree (goodBlock ord eStar) ord₂ e : ℕ) : ℝ) ≤ (1 - τ) * (n : ℝ) := by
            have h1 : ((Nat.card {f : D.good // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} +
                precedingDegree (goodBlock ord eStar) ord₂ e : ℕ) : ℝ) ≤
                ((precedingDegree 𝓕 ord ⟨e.1, hb e.2⟩ : ℕ) : ℝ) := Nat.cast_le.mpr hcount
            linarith
          push_cast at hcast
          linarith
        have hdisj_good : Disjoint D.good (goodBlock ord eStar) :=
          Disjoint.mono D.hGoodSub (goodBlock_subset_rankAbove ord hfe)
            (disjoint_rankAbove_rankBelow ord fStar).symm
        obtain ⟨ordG, hordG⟩ :=
          exists_ordering_of_disjoint_cover (𝓖 := D.good ∪ goodBlock ord eStar)
            (𝓖₁ := D.good) (𝓖₂ := goodBlock ord eStar) rfl hdisj_good D.ord ord₂ D.hGood h₂
        refine ⟨{
          blocks := ⟨midBlock ord fStar eStar,
              ⟨(eStar : Set (Fin n)), heStarMid⟩⟩ :: D.blocks
          good := D.good ∪ goodBlock ord eStar
          kg := D.kg + k₂
          ord := ordG
          hBlockSub := ?_
          hBlockVol := ?_
          hBlockMin := ?_
          hBlockMax := ?_
          hBlocksDisj := ?_
          hGoodSub := ?_
          hGoodDisj := ?_
          hCover := ?_
          hGood := hordG }⟩
        · intro B hB
          rcases List.mem_cons.mp hB with h | h
          · subst h; exact midBlock_subset ord fStar eStar
          · exact fun e he => rankBelow_subset ord fStar (D.hBlockSub B h he)
        · intro B hB
          rcases List.mem_cons.mp hB with h | h
          · subst h; exact hvolMid
          · exact D.hBlockVol B h
        · intro B hB e he
          rcases List.mem_cons.mp hB with h | h
          · subst h
            exact hsizeMin ⟨e, he.choose⟩
              ((mem_midBlock ord fStar eStar he.choose).mp he).2
          · exact D.hBlockMin B h e he
        · intro B hB e he
          rcases List.mem_cons.mp hB with h | h
          · subst h
            exact hsizeMax ⟨e, he.choose⟩
              ((mem_midBlock ord fStar eStar he.choose).mp he).1
              ((mem_midBlock ord fStar eStar he.choose).mp he).2
          · exact D.hBlockMax B h e he
        · refine List.pairwise_cons.mpr ⟨?_, D.hBlocksDisj⟩
          intro B hB
          exact (Disjoint.mono (D.hBlockSub B hB) (le_refl (midBlock ord fStar eStar))
            (disjoint_rankBelow_midBlock ord fStar eStar)).symm
        · intro e he
          rcases he with he | he
          · exact rankBelow_subset ord fStar (D.hGoodSub he)
          · exact goodBlock_subset ord eStar he
        · intro B hB
          rw [Set.disjoint_union_left]
          rcases List.mem_cons.mp hB with h | h
          · subst h
            exact ⟨Disjoint.mono D.hGoodSub (le_refl _)
                (disjoint_rankBelow_midBlock ord fStar eStar),
              (disjoint_midBlock_goodBlock ord fStar eStar).symm⟩
          · exact ⟨D.hGoodDisj B h,
              Disjoint.mono (goodBlock_subset_rankAbove ord hfe) (D.hBlockSub B h)
                (disjoint_rankAbove_rankBelow ord fStar)⟩
        · intro e
          constructor
          · intro he
            have hcb := cover_blocks ord hfe
            have hmem : e ∈ rankBelow ord fStar ∪ midBlock ord fStar eStar ∪
                goodBlock ord eStar := by rw [hcb]; exact he
            rcases hmem with (h | h) | h
            · rcases (D.hCover e).mp h with hg | ⟨B, hB, heB⟩
              · exact Or.inl (Or.inl hg)
              · exact Or.inr ⟨B, List.mem_cons_of_mem _ hB, heB⟩
            · exact Or.inr ⟨_, List.mem_cons_self, h⟩
            · exact Or.inl (Or.inr h)
          · rintro (h | ⟨B, hB, heB⟩)
            · rcases h with h | h
              · exact rankBelow_subset ord fStar (D.hGoodSub h)
              · exact goodBlock_subset ord eStar h
            · rcases List.mem_cons.mp hB with h' | h'
              · subst h'; exact midBlock_subset ord fStar eStar heB
              · exact rankBelow_subset ord fStar (D.hBlockSub B h' heB)

  end

end ErdosFaberLovaszConjecture
