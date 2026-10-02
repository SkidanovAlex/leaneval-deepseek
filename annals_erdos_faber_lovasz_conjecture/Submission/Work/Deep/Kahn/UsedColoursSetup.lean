import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.nibbleSetup
import Submission.Work.Deep.Kahn.chernoff_uniform_prod
import Submission.Work.Deep.Conc.Pi

/-!
# The `usedColours` estimate of the regularised one-round nibble: setup

This module proves `Work.Deep.Kahn.roundUsedColours`: in the *regularised* setting of the
one-round nibble (every edge of `𝓗` has exactly `C` vertices, every list `L e` has exactly
`Λ` colours and every *occurring* colour degree is exactly `D`), for every edge `e` the
probability that `e` is *not* kept and yet more than `Λ (1 - s) + η Λ` colours of its list
are used at `e` (where `s = retention Λ C D K = (1 - 1/(KΛ)) ^ (C (D-1))` is the retention
factor) is at most `exp (-D ^ (1/4))`.

## The structure of the proof

Write `Space := Round.Space K 𝓗 L = ∀ f : 𝓗, Fin K × Fin (L f).card` and let
`clsOf ω := fun f => (ω f).1` (the *activation class*) and `idxOf ω := fun f => (ω f).2`
(the *colour index*) be the two coordinates of an outcome.

* On the event that `e` is not kept, a colour `γ ∈ L e` is used at `e` only through a
  *witness*: an edge `f ≠ e` meeting `e` with `γ ∈ L f` that is activated (`cls f = 0`) with
  colour index naming `γ`.  Hence `|L e ∩ usedColours ω e| ≤ #(keptEvidence e ω)`.
* **Conditioning on the colour indices `σ`.**  Given `σ`, the witness sets
  `witnesses e σ γ = {f ≠ e : f meets e, colour(f) = γ}` are *pairwise disjoint* (every edge
  names one colour), so the events "`witnesses e σ γ` contains an activated edge" are
  independent; `#(keptEvidence) = #{γ : witnesses e σ γ fires}` is a sum of independent
  indicators with mean `condMean K e σ`.  The block Chernoff bound `chernoff_block` bounds the
  probability of a deviation `t` by `exp (-t ^ 2 / (2 (μ + t / 3)))`.
* **Concentration of the conditional mean.**  `condMean K e σ` is not a sum of independent
  indicators, but concavity of `x ↦ 1 - (1-1/K)^x` gives the tangent-line bound
  `condMean ≤ Λ (1 - s) + c (witCount e σ - C (D-1))` with slope `c ≤ 2 / K`, where
  `witCount e σ` counts the edges `f ≠ e` meeting `e` whose colour index names a colour of
  `L e` — a sum of independent single-coordinate indicators of mean `C (D-1)` (double
  counting: `∑_{f ∈ N(e)} |L f ∩ L e| = Λ · C (D-1)`).  The product Chernoff bound
  `chernoff_prod_general` bounds the deviation.
* Fubini for the product of the two coordinate spaces (`Conc.prob_pi_prod`) splits the
  probability of `{θ < #(keptEvidence)}` into the two pieces, and the numeric estimates
  `level1_exp_ge`, `level2_exp_ge` show `exp (-E1) + exp (-E2) ≤ exp (-D ^ (1/4))`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

variable {n c : ℕ}

/-- The colour named by the `i`-th entry of the list `L f`. -/
def idxColour {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (L : 𝓗 → Finset (Fin c)) (f : 𝓗) (i : Fin (L f).card) : Fin c :=
  ((Finset.equivFin (L f)).symm i : L f).1

lemma idxColour_mem {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (L : 𝓗 → Finset (Fin c)) (f : 𝓗) (i : Fin (L f).card) :
    idxColour L f i ∈ L f :=
  ((Finset.equivFin (L f)).symm i : L f).2

lemma idxColour_injective {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (L : 𝓗 → Finset (Fin c)) (f : 𝓗) : Function.Injective (idxColour L f) := by
  intro i j h
  exact (Finset.equivFin (L f)).symm.injective (Subtype.ext h)

variable {K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)}

/-- The colour of a round outcome is the colour named by its index coordinate. -/
lemma round_colour_eq_idxColour (ω : Round.Space K 𝓗 L) (f : 𝓗) :
    Round.colour ω f = idxColour L f (ω f).2 := rfl

/-- The *witnesses* for the colour `γ` at the edge `e`: the edges `f ≠ e` meeting `e` whose
colour index names `γ`.  These are exactly the edges that can block `γ` at `e`. -/
def witnesses (e : 𝓗) (σ : ∀ f : 𝓗, Fin (L f).card) (γ : Fin c) : Finset 𝓗 := by
  classical
  exact Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ idxColour L f (σ f) = γ)

lemma mem_witnesses {e : 𝓗} {σ : ∀ f : 𝓗, Fin (L f).card} {γ : Fin c} {f : 𝓗} :
    f ∈ witnesses (L := L) e σ γ ↔ f ≠ e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ idxColour L f (σ f) = γ := by
  classical
  simp [witnesses]

/-- Distinct colours have disjoint witness sets: every edge names exactly one colour. -/
lemma witnesses_disjoint {e : 𝓗} {σ : ∀ f : 𝓗, Fin (L f).card} {γ γ' : Fin c} (h : γ ≠ γ') :
    Disjoint (witnesses (L := L) e σ γ) (witnesses (L := L) e σ γ') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  rw [mem_witnesses] at hf hf'
  exact h (hf.2.2.symm.trans hf'.2.2)

/-- The number of edges `f ≠ e` meeting `e` whose colour index names a colour of `L e`. -/
def witCount (e : 𝓗) (σ : ∀ f : 𝓗, Fin (L f).card) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ idxColour L f (σ f) ∈ L e)).card

/-- The conditional mean of the number of colours of `L e` that are *used* at `e`, given the
colour indices `σ`. -/
def condMean (K : ℕ) (e : 𝓗) (σ : ∀ f : 𝓗, Fin (L f).card) : ℝ :=
  ∑ γ ∈ L e, (1 - (1 - (1 : ℝ) / (K : ℝ)) ^ (witnesses (L := L) e σ γ).card)

/-- The activation classes of the round, as a single coordinate. -/
def clsOf (ω : Round.Space K 𝓗 L) : ∀ f : 𝓗, Fin K := fun f => (ω f).1

/-- The colour indices of the round, as a single coordinate. -/
def idxOf (ω : Round.Space K 𝓗 L) : ∀ f : 𝓗, Fin (L f).card := fun f => (ω f).2

/-- The colours of `L e` that are used at `e` by a class-`0` witness, as a function of the two
coordinates separately. -/
def classEvidence (K : ℕ) [NeZero K] (e : 𝓗) (cls : ∀ f : 𝓗, Fin K)
    (σ : ∀ f : 𝓗, Fin (L f).card) : Finset (Fin c) := by
  classical
  exact (L e).filter (fun γ : Fin c => ∃ f : 𝓗, f ≠ e ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ cls f = 0 ∧ idxColour L f (σ f) = γ)

lemma mem_classEvidence [NeZero K] {e : 𝓗} {cls : ∀ f : 𝓗, Fin K}
    {σ : ∀ f : 𝓗, Fin (L f).card} {γ : Fin c} :
    γ ∈ classEvidence K e cls σ ↔ γ ∈ L e ∧ ∃ f : 𝓗, f ≠ e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ cls f = 0 ∧ idxColour L f (σ f) = γ := by
  classical
  simp [classEvidence]

/-- The same set, as a function of a complete round outcome. -/
def keptEvidence (K : ℕ) [NeZero K] (e : 𝓗) (ω : Round.Space K 𝓗 L) : Finset (Fin c) :=
  classEvidence K e (clsOf ω) (idxOf ω)

/-- The identity between the class-level count and the disjoint family of witness sets. -/
lemma classEvidence_eq_filter_witnesses [NeZero K] (e : 𝓗) (cls : ∀ f : 𝓗, Fin K)
    (σ : ∀ f : 𝓗, Fin (L f).card) :
    classEvidence K e cls σ
      = (L e).filter (fun γ : Fin c => ∃ f ∈ witnesses (L := L) e σ γ, cls f = 0) := by
  classical
  ext γ
  rw [mem_classEvidence, Finset.mem_filter]
  constructor
  · rintro ⟨hγ, f, hne, hint, hcls, hidx⟩
    exact ⟨hγ, f, mem_witnesses.mpr ⟨hne, hint, hidx⟩, hcls⟩
  · rintro ⟨hγ, f, hf, hcls⟩
    obtain ⟨hne, hint, hidx⟩ := mem_witnesses.mp hf
    exact ⟨hγ, f, hne, hint, hcls, hidx⟩

/-- **The key reduction.**  If `e` is not kept, then every colour of `L e` that is used at `e`
has a class-`0` witness, so the used colours are contained in `keptEvidence`. -/
lemma card_usedColours_le_keptEvidence [NeZero K] {e : 𝓗} {ω : Round.Space K 𝓗 L}
    (hω : ¬ Round.kept ω e) :
    ((L e) ∩ Round.usedColours ω e).card ≤ (keptEvidence K e ω).card := by
  classical
  refine Finset.card_le_card fun γ hγ => ?_
  simp only [Finset.mem_inter] at hγ
  obtain ⟨hγL, hγu⟩ := hγ
  have hmem : γ ∈ Round.usedColours ω e ↔ ∃ f : 𝓗, Round.kept ω f ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ Round.colour ω f = γ := by
    unfold Round.usedColours
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, ⟨hk, hm⟩, hc⟩
      exact ⟨f, hk, hm, hc⟩
    · rintro ⟨f, hk, hm, hc⟩
      exact ⟨f, ⟨hk, hm⟩, hc⟩
  obtain ⟨f, hkf, hmeet, hcol⟩ := hmem.mp hγu
  have hne : f ≠ e := fun hfe => hω (hfe ▸ hkf)
  rw [keptEvidence, mem_classEvidence]
  exact ⟨hγL, f, hne, hmeet, hkf.1, hcol⟩


/-! ## Finsets of neighbours and their cardinalities -/

/-- The edges `≠ e` meeting `e`. -/
def neighFinset (e : 𝓗) : Finset 𝓗 := by
  classical
  exact Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)

/-- The edges `≠ e` meeting `e` whose list contains `γ`. -/
def colWit (e : 𝓗) (γ : Fin c) : Finset 𝓗 := by
  classical
  exact Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ γ ∈ L f)

/-- The edges through a vertex `x` whose list contains `γ`. -/
def colThrough (x : Fin n) (γ : Fin c) : Finset 𝓗 := by
  classical
  exact Finset.univ.filter (fun f : 𝓗 => x ∈ (f : Set (Fin n)) ∧ γ ∈ L f)

/-- The colour-index sets of the "good" edges: the indices naming a colour of `L e`. -/
def goodIdx (e : 𝓗) (f : 𝓗) : Finset (Fin (L f).card) := by
  classical
  exact if f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty then
    Finset.univ.filter (fun i => idxColour L f i ∈ L e) else ∅

lemma mem_colThrough {x : Fin n} {γ : Fin c} {f : 𝓗} :
    f ∈ colThrough (L := L) x γ ↔ x ∈ (f : Set (Fin n)) ∧ γ ∈ L f := by
  classical
  simp [colThrough]

lemma mem_colWit {e : 𝓗} {γ : Fin c} {f : 𝓗} :
    f ∈ colWit (L := L) e γ ↔ f ≠ e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ γ ∈ L f := by
  classical
  simp [colWit]

lemma mem_neighFinset {e f : 𝓗} :
    f ∈ neighFinset e ↔ f ≠ e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := by
  classical
  simp [neighFinset]

lemma mem_goodIdx {e f : 𝓗} {i : Fin (L f).card} :
    i ∈ goodIdx (L := L) e f ↔ f ≠ e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ idxColour L f i ∈ L e := by
  classical
  by_cases h : f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty
  · simp only [goodIdx, if_pos h, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hi => ⟨h.1, h.2, hi⟩, fun hi => hi.2.2⟩
  · simp only [goodIdx, if_neg h, Finset.notMem_empty]
    exact ⟨fun hf => hf.elim, fun hcon => h ⟨hcon.1, hcon.2.1⟩⟩

/-- The number of indices of `L f` naming a colour of `L e` is `|L f ∩ L e|`. -/
lemma card_idxColour_eq_inter (f e : 𝓗) :
    (Finset.univ.filter (fun i : Fin (L f).card => idxColour L f i ∈ L e)).card
      = (L f ∩ L e).card := by
  classical
  refine Finset.card_bij (fun i _ => idxColour L f i) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_inter]
    exact ⟨idxColour_mem L f i, hi.2⟩
  · intro i _ j _ hij
    exact idxColour_injective L f hij
  · intro γ hγ
    rw [Finset.mem_inter] at hγ
    refine ⟨(Finset.equivFin (L f)) ⟨γ, hγ.1⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp [idxColour, hγ.2]⟩
    · simp [idxColour]
/-- **Counting the witnesses of a colour.**  In a linear `C`-uniform hypergraph in which
every occurring colour degree equals `D`, for `γ ∈ L e` the number of edges `f ≠ e` meeting
`e` with `γ ∈ L f` is `C (D - 1)`: these split, according to the vertex of `f ∩ e` (unique by
linearity), into the `C` groups of `D - 1` edges through each vertex of `e`. -/
lemma card_colWit {C D : ℕ} (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (e : 𝓗) {γ : Fin c} (hγ : γ ∈ L e) :
    (colWit (L := L) e γ).card = C * (D - 1) := by
  classical
  set X : Finset (Fin n) := ErdosFaberLovaszConjecture.verts (e : Set (Fin n)) with hX
  have hthrough : ∀ x : Fin n, x ∈ X → (colThrough (L := L) x γ).card = D := by
    intro x hx
    have hxe : x ∈ (e : Set (Fin n)) := by
      rw [hX, ErdosFaberLovaszConjecture.mem_verts] at hx; exact hx
    have hD := hdeg x γ ⟨e, hxe, hγ⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hD
    exact hD
  have hunion : colWit (L := L) e γ
      = X.biUnion (fun x => (colThrough (L := L) x γ).erase e) := by
    ext f
    rw [mem_colWit, Finset.mem_biUnion]
    constructor
    · rintro ⟨hfe, hmeet, hγf⟩
      obtain ⟨x, hxf, hxe⟩ := hmeet
      exact ⟨x, by rw [hX, ErdosFaberLovaszConjecture.mem_verts]; exact hxe,
        by rw [Finset.mem_erase]; exact ⟨hfe, mem_colThrough.mpr ⟨hxf, hγf⟩⟩⟩
    · rintro ⟨x, hx, hf⟩
      rw [Finset.mem_erase] at hf
      obtain ⟨hfe, hfc⟩ := hf
      obtain ⟨hxf, hγf⟩ := mem_colThrough.mp hfc
      exact ⟨hfe, ⟨x, hxf, by rw [hX, ErdosFaberLovaszConjecture.mem_verts] at hx; exact hx⟩, hγf⟩
  have hdisj : Set.PairwiseDisjoint (↑X : Set (Fin n))
      (fun x => (colThrough (L := L) x γ).erase e) := by
    intro x hx x' hx' hne
    show Disjoint ((colThrough (L := L) x γ).erase e) ((colThrough (L := L) x' γ).erase e)
    rw [Finset.disjoint_left]
    intro f hf hf'
    rw [Finset.mem_erase] at hf hf'
    obtain ⟨hfe, hfc⟩ := hf
    obtain ⟨-, hfc'⟩ := hf'
    obtain ⟨hxf, -⟩ := mem_colThrough.mp hfc
    obtain ⟨hxf', -⟩ := mem_colThrough.mp hfc'
    have hxe : x ∈ (e : Set (Fin n)) := by simpa [hX] using hx
    have hx'e : x' ∈ (e : Set (Fin n)) := by simpa [hX] using hx'
    have hsub : (↑f ∩ ↑e : Set (Fin n)).Subsingleton :=
      hlin f.2 e.2 (fun h => hfe (Subtype.ext h))
    exact hne (hsub ⟨hxf, hxe⟩ ⟨hxf', hx'e⟩)
  have hpiece : ∀ x ∈ X, ((colThrough (L := L) x γ).erase e).card = D - 1 := by
    intro x hx
    have hxe : x ∈ (e : Set (Fin n)) := by
      rw [hX, ErdosFaberLovaszConjecture.mem_verts] at hx; exact hx
    rw [Finset.card_erase_of_mem (mem_colThrough.mpr ⟨hxe, hγ⟩), hthrough x hx]
  rw [hunion, Finset.card_biUnion hdisj,
    Finset.sum_congr rfl hpiece, Finset.sum_const, smul_eq_mul, hX]
  change ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) * (D - 1) = C * (D - 1)
  rw [hsize e]

/-- The cardinality of the "good index" set, when `f ≠ e` meets `e`. -/
lemma card_goodIdx_of_mem {e f : 𝓗}
    (h : f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty) :
    (goodIdx (L := L) e f).card = (L f ∩ L e).card := by
  classical
  unfold goodIdx
  rw [if_pos h, card_idxColour_eq_inter]

/-- The "good index" set is empty when `f = e` or `f` does not meet `e`. -/
lemma card_goodIdx_of_notMem {e f : 𝓗}
    (h : ¬(f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)) :
    (goodIdx (L := L) e f).card = 0 := by
  classical
  unfold goodIdx
  rw [if_neg h, Finset.card_empty]

/-- **The mean identity for the level-1 statistic.**  The total number of colour indices of
the "good" edges (edges `≠ e` meeting `e`, indices naming a colour of `L e`) is
`Λ · C · (D - 1)`; dividing by the common list size `Λ` gives the mean `C (D - 1)` of the
witness count. -/
lemma sum_card_goodIdx {C D Λ : ℕ} (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (hlist : ∀ e : 𝓗, (L e).card = Λ) (e : 𝓗) :
    ∑ f : 𝓗, (goodIdx (L := L) e f).card = Λ * (C * (D - 1)) := by
  classical
  have h1 : ∀ f : 𝓗, (goodIdx (L := L) e f).card
      = (if f ∈ neighFinset e then (L f ∩ L e).card else 0) := by
    intro f
    by_cases h : f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty
    · rw [card_goodIdx_of_mem h, if_pos (mem_neighFinset.mpr h)]
    · rw [card_goodIdx_of_notMem h, if_neg (fun hc => h (mem_neighFinset.mp hc))]
  rw [Finset.sum_congr rfl (fun f _ => h1 f)]
  set P : Finset (𝓗 × Fin c) := (Finset.univ : Finset (𝓗 × Fin c)).filter
      (fun p => p.1 ∈ neighFinset e ∧ p.2 ∈ L p.1 ∩ L e) with hP
  have hA : P.card = ∑ f : 𝓗, (if f ∈ neighFinset e then (L f ∩ L e).card else 0) := by
    rw [hP, Finset.card_filter]
    rw [show (Finset.univ : Finset (𝓗 × Fin c))
        = (Finset.univ : Finset 𝓗) ×ˢ (Finset.univ : Finset (Fin c)) from
      Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    by_cases hf : f ∈ neighFinset e
    · rw [if_pos hf]
      have hstep : (∑ γ : Fin c, (if f ∈ neighFinset e ∧ γ ∈ L f ∩ L e then (1 : ℕ) else 0))
          = ∑ γ : Fin c, (if γ ∈ L f ∩ L e then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl (fun γ _ => by simp only [hf, true_and])
      rw [hstep, ← Finset.card_filter]
      congr 1
      ext γ
      simp
    · rw [if_neg hf]
      refine Finset.sum_eq_zero (fun γ _ => ?_)
      simp [Finset.mem_inter, hf]
  have hB : P.card = ∑ γ : Fin c, (if γ ∈ L e then (colWit (L := L) e γ).card else 0) := by
    rw [hP, Finset.card_filter]
    rw [show (Finset.univ : Finset (𝓗 × Fin c))
        = (Finset.univ : Finset 𝓗) ×ˢ (Finset.univ : Finset (Fin c)) from
      Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    by_cases hγ : γ ∈ L e
    · rw [if_pos hγ, ← Finset.card_filter]
      congr 1
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hfN, hγf⟩
        obtain ⟨hne, hmeet⟩ := mem_neighFinset.mp hfN
        obtain ⟨hγf, -⟩ := Finset.mem_inter.mp hγf
        rw [mem_colWit]
        exact ⟨hne, hmeet, hγf⟩
      · intro hf'
        rw [mem_colWit] at hf'
        exact ⟨mem_neighFinset.mpr ⟨hf'.1, hf'.2.1⟩, Finset.mem_inter.mpr ⟨hf'.2.2, hγ⟩⟩
    · rw [if_neg hγ]
      refine Finset.sum_eq_zero (fun f _ => ?_)
      simp [Finset.mem_inter, hγ]
  rw [← hA, hB]
  have h4 : ∀ γ : Fin c, (if γ ∈ L e then (colWit (L := L) e γ).card else 0)
      = (if γ ∈ L e then C * (D - 1) else 0) := by
    intro γ
    by_cases hγ : γ ∈ L e
    · rw [if_pos hγ, if_pos hγ, card_colWit hlin hsize hdeg e hγ]
    · rw [if_neg hγ, if_neg hγ]
  have hsum : (∑ γ : Fin c, (if γ ∈ L e then (colWit (L := L) e γ).card else 0))
      = ∑ γ : Fin c, (if γ ∈ L e then C * (D - 1) else 0) :=
    Finset.sum_congr rfl (fun γ _ => h4 γ)
  rw [hsum, Finset.sum_ite_mem_eq, Finset.sum_const, smul_eq_mul, hlist e]

/-- **The witness count dominates the sum of the witness-set sizes.**  The sets
`witnesses e σ γ` (`γ ∈ L e`) are pairwise disjoint and contained in the set counted by
`witCount e σ`. -/
lemma sum_witnesses_card_le (e : 𝓗) (σ : ∀ f : 𝓗, Fin (L f).card) :
    ∑ γ ∈ L e, (witnesses (L := L) e σ γ).card ≤ witCount (L := L) e σ := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(L e) : Set (Fin c))
      (fun γ => witnesses (L := L) e σ γ) := by
    intro γ _ γ' _ hne
    exact witnesses_disjoint hne
  rw [← Finset.card_biUnion hdisj]
  unfold witCount
  refine Finset.card_le_card ?_
  intro f hf
  rw [Finset.mem_biUnion] at hf
  obtain ⟨γ, hγ, hfγ⟩ := hf
  rw [mem_witnesses] at hfγ
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hfγ.1, hfγ.2.1, hfγ.2.2 ▸ hγ⟩

/-- **The conditional mean is at most the (first-order) witness count divided by `K`.**  Each
summand `1 - (1-1/K)^{|W_γ|}` is at most `|W_γ| / K` by Bernoulli's inequality, and the
witness sets are counted by `witCount`. -/
lemma condMean_le_witCount {K : ℕ} (hK : 1 ≤ K) (e : 𝓗) (σ : ∀ f : 𝓗, Fin (L f).card) :
    condMean (L := L) K e σ ≤ (witCount (L := L) e σ : ℝ) / (K : ℝ) := by
  classical
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hterm : ∀ γ ∈ L e,
      (1 - (1 - (1 : ℝ) / (K : ℝ)) ^ (witnesses (L := L) e σ γ).card)
        ≤ ((witnesses (L := L) e σ γ).card : ℝ) / (K : ℝ) := by
    intro γ _
    have hbern : (1 : ℝ) + ((witnesses (L := L) e σ γ).card : ℝ) * (-(1 / (K : ℝ)))
        ≤ (1 + (-(1 / (K : ℝ)))) ^ (witnesses (L := L) e σ γ).card := by
      refine one_add_mul_le_pow ?_ _
      rw [le_neg]
      have h1 : (1 : ℝ) / (K : ℝ) ≤ 1 := by
        rw [div_le_one hKpos]; exact_mod_cast hK
      linarith
    have hbase : (1 : ℝ) + (-(1 / (K : ℝ))) = 1 - 1 / (K : ℝ) := by ring
    rw [hbase] at hbern
    have h2 : (1 : ℝ) - ((witnesses (L := L) e σ γ).card : ℝ) * (1 / (K : ℝ))
        ≤ (1 - 1 / (K : ℝ)) ^ (witnesses (L := L) e σ γ).card := by
      linarith [hbern]
    have h3 : ((witnesses (L := L) e σ γ).card : ℝ) / (K : ℝ)
        = ((witnesses (L := L) e σ γ).card : ℝ) * (1 / (K : ℝ)) := by ring
    linarith [h2, h3]
  calc condMean (L := L) K e σ
      = ∑ γ ∈ L e, (1 - (1 - (1 : ℝ) / (K : ℝ)) ^ (witnesses (L := L) e σ γ).card) := rfl
    _ ≤ ∑ γ ∈ L e, ((witnesses (L := L) e σ γ).card : ℝ) / (K : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (∑ γ ∈ L e, ((witnesses (L := L) e σ γ).card : ℝ)) / (K : ℝ) := by
        rw [Finset.sum_div]
    _ ≤ ((witCount (L := L) e σ : ℕ) : ℝ) / (K : ℝ) := by
        apply div_le_div_of_nonneg_right _ hKpos.le
        exact_mod_cast sum_witnesses_card_le (L := L) e σ

/-! ## The activated witnesses and their coordinate sets -/

/-- The coordinates of `f` that make it an *activated witness* naming a colour of `L e`: the
class is `0` and the colour index names a colour of `L e` (and `f ≠ e` meets `e`). -/
def witnessCoord [NeZero K] (e : 𝓗) (f : 𝓗) : Finset (Fin K × Fin (L f).card) := by
  classical
  exact if f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty then
    Finset.univ.filter (fun p : Fin K × Fin (L f).card =>
      p.1 = 0 ∧ idxColour L f p.2 ∈ L e) else ∅

/-- The number of edges of `𝓗` that are activated witnesses naming a colour of `L e`. -/
def actWitCount [NeZero K] (e : 𝓗) (ω : Round.Space K 𝓗 L) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : 𝓗 => (ω f) ∈ witnessCoord (L := L) e f)).card

lemma mem_witnessCoord [NeZero K] {e f : 𝓗} {p : Fin K × Fin (L f).card} :
    p ∈ witnessCoord (L := L) e f ↔ f ≠ e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ p.1 = 0 ∧ idxColour L f p.2 ∈ L e := by
  classical
  by_cases h : f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty
  · simp only [witnessCoord, if_pos h, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hp => ⟨h.1, h.2, hp⟩, fun hp => hp.2.2⟩
  · simp only [witnessCoord, if_neg h, Finset.notMem_empty]
    exact ⟨fun hp => hp.elim, fun hp => absurd ⟨hp.1, hp.2.1⟩ h⟩

lemma mem_actWitCount [NeZero K] {e : 𝓗} {ω : Round.Space K 𝓗 L} {f : 𝓗} :
    f ∈ (Finset.univ.filter (fun f : 𝓗 => (ω f) ∈ witnessCoord (L := L) e f)) ↔
      (ω f) ∈ witnessCoord (L := L) e f := by
  classical
  simp

lemma card_witnessCoord_of_mem [NeZero K] {e f : 𝓗}
    (h : f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty) :
    (witnessCoord (L := L) (K := K) e f).card = (L f ∩ L e).card := by
  classical
  unfold witnessCoord
  rw [if_pos h]
  · rw [← card_idxColour_eq_inter (L := L) f e]
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_univ _, hp.2.2⟩
    · intro p hp q hq hpq
      rw [Finset.mem_filter] at hp hq
      exact Prod.ext (by rw [hp.2.1, hq.2.1]) hpq
    · intro i hi
      rw [Finset.mem_filter] at hi
      exact ⟨(0, i), by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, rfl, hi.2⟩, rfl⟩

lemma card_witnessCoord_of_notMem [NeZero K] {e f : 𝓗}
    (h : ¬(f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)) :
    (witnessCoord (L := L) (K := K) e f).card = 0 := by
  classical
  unfold witnessCoord
  rw [if_neg h, Finset.card_empty]

/-- The total number of activated-witness coordinates is `Λ · C · (D - 1)`. -/
lemma sum_card_witnessCoord {C D Λ : ℕ} [NeZero K] (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (hlist : ∀ e : 𝓗, (L e).card = Λ) (e : 𝓗) :
    ∑ f : 𝓗, (witnessCoord (L := L) (K := K) e f).card = Λ * (C * (D - 1)) := by
  classical
  rw [← sum_card_goodIdx (L := L) hlin hsize hdeg hlist e]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  by_cases h : f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty
  · rw [card_witnessCoord_of_mem h, card_goodIdx_of_mem h]
  · rw [card_witnessCoord_of_notMem h, card_goodIdx_of_notMem h]

/-- **The activated witnesses dominate the used colours.**  If `e` is not kept, every used
colour of `L e` has an activated witness, and distinct colours have distinct witnesses, so the
number of used colours is at most the number of activated witnesses. -/
lemma keptEvidence_card_le_actWitCount [NeZero K] {e : 𝓗} {ω : Round.Space K 𝓗 L}
    (hω : ¬ Round.kept ω e) :
    (keptEvidence K e ω).card ≤ actWitCount (L := L) e ω := by
  classical
  set S : Finset 𝓗 := Finset.univ.filter (fun f : 𝓗 => (ω f) ∈ witnessCoord (L := L) e f)
    with hS
  have hmaps : ∀ γ : {γ // γ ∈ keptEvidence K e ω},
      ∃ f ∈ S, idxColour L f ((ω f).2) = γ.1 := by
    intro γ
    have hγ : γ.1 ∈ classEvidence K e (clsOf ω) (idxOf ω) := γ.2
    obtain ⟨hγL, f, hne, hint, hcls, hidx⟩ := mem_classEvidence.mp hγ
    refine ⟨f, ?_, ?_⟩
    · rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, mem_witnessCoord.mpr ⟨hne, hint, ?_, ?_⟩⟩
      · simpa only [clsOf] using hcls
      · simpa [idxOf] using (hidx ▸ hγL)
    · simpa [idxOf] using hidx
  choose ψ hψS hψcol using hmaps
  have hinj : Function.Injective ψ := by
    intro γ γ' heq
    apply Subtype.ext
    rw [← hψcol γ, ← hψcol γ', heq]
  have hcard : (keptEvidence K e ω).card = (((keptEvidence K e ω).attach).image ψ).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  rw [hcard, actWitCount]
  refine Finset.card_le_card ?_
  intro f hf
  obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hf
  exact hψS γ


end

end Work.Deep.Kahn
