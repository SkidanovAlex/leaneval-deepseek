import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.FinishSetup
import Submission.Work.Deep.Prob.Spaces.uniform_prob_ncard

/-!
# Counting facts for the uniform measure on the list space

`Work.Deep.Kahn.ListSpace L = (e : E) → {γ : Fin c // γ ∈ L e}` is the space of
list-respecting colourings of a finite set `E` of edges, and `listProb L hL` is the uniform
probability measure on it.  This module computes the elementary probabilities that the
finishing step of Kahn's theorem needs:

* a single edge receives a prescribed colour from its list, with probability `1 / |L e|`;
* two distinct edges receive the same colour, with probability `|L e ∩ L f| / (|L e| |L f|)`;
* events that only see the coordinates in a set `C` of edges are independent of events that
  only see the coordinates outside `C`.

The proofs are pure counting.  The uniform measure gives an event `A` the probability
`|A| / |Ω|` (`Work.Deep.Prob.Spaces.uniform_prob_ncard`), and every counting statement is
obtained by splitting a colouring into its restriction to `C` and its restriction to the
complement of `C`: this is a bijection `Ω ≃ Pat L C × CoPat L C` (`splitEquiv`), and every
fibre of the restriction map has the same cardinality `∏_{g ∉ C} |L g|`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Kahn

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E] {c : ℕ}

/-- The patterns on a set `C` of coordinates: a choice of a colour from `L g` for every
`g ∈ C`. -/
abbrev Pat (L : E → Finset (Fin c)) (C : Finset E) :=
  (g : {g : E // g ∈ C}) → {γ : Fin c // γ ∈ L g}

/-- The patterns on the complement of `C`. -/
abbrev CoPat (L : E → Finset (Fin c)) (C : Finset E) :=
  (g : {g : E // g ∈ Finset.univ \ C}) → {γ : Fin c // γ ∈ L g}

/-- Restriction of a colouring to the coordinates in `C`. -/
def restrict (L : E → Finset (Fin c)) (C : Finset E) : ListSpace L → Pat L C :=
  fun φ g => φ g.val

/-- Restriction of a colouring to the coordinates outside `C`. -/
def corestrict (L : E → Finset (Fin c)) (C : Finset E) : ListSpace L → CoPat L C :=
  fun φ g => φ g.val

/-- **Splitting a colouring.**  A colouring is determined by its restrictions to `C` and to
the complement of `C`, and conversely any pair of patterns is realised. -/
def splitEquiv (L : E → Finset (Fin c)) (C : Finset E) :
    ListSpace L ≃ Pat L C × CoPat L C where
  toFun φ := (restrict L C φ, corestrict L C φ)
  invFun p := fun g =>
    if h : g ∈ C then p.1 ⟨g, h⟩
    else p.2 ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ g, h⟩⟩
  left_inv φ := by
    funext g
    dsimp only []
    by_cases h : g ∈ C
    · rw [dif_pos h]; rfl
    · rw [dif_neg h]; rfl
  right_inv p := by
    obtain ⟨p₁, p₂⟩ := p
    refine Prod.ext ?_ ?_
    · funext g
      show (if h : (g : E) ∈ C then p₁ ⟨g, h⟩
        else p₂ ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ (g : E), h⟩⟩) = p₁ g
      rw [dif_pos g.2]
    · funext g
      show (if h : (g : E) ∈ C then p₁ ⟨g, h⟩
        else p₂ ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ (g : E), h⟩⟩) = p₂ g
      rw [dif_neg (Finset.mem_sdiff.mp g.2).2]

@[simp] lemma splitEquiv_fst (L : E → Finset (Fin c)) (C : Finset E) (χ : ListSpace L) :
    ((splitEquiv L C) χ).1 = restrict L C χ := rfl

@[simp] lemma splitEquiv_snd (L : E → Finset (Fin c)) (C : Finset E) (χ : ListSpace L) :
    ((splitEquiv L C) χ).2 = corestrict L C χ := rfl

lemma splitEquiv_symm_fst (L : E → Finset (Fin c)) (C : Finset E) (a : Pat L C) (b : CoPat L C) :
    restrict L C ((splitEquiv L C).symm (a, b)) = a := by
  rw [← splitEquiv_fst (L := L) (C := C) (χ := (splitEquiv L C).symm (a, b))]
  exact congrArg Prod.fst (Equiv.apply_symm_apply (splitEquiv L C) (a, b))

lemma splitEquiv_symm_snd (L : E → Finset (Fin c)) (C : Finset E) (a : Pat L C) (b : CoPat L C) :
    corestrict L C ((splitEquiv L C).symm (a, b)) = b := by
  rw [← splitEquiv_snd (L := L) (C := C) (χ := (splitEquiv L C).symm (a, b))]
  exact congrArg Prod.snd (Equiv.apply_symm_apply (splitEquiv L C) (a, b))

/-- Restriction to `C` is injective exactly up to equality of the `C`-coordinates. -/
lemma restrict_eq_iff (L : E → Finset (Fin c)) (C : Finset E) (χ ψ : ListSpace L) :
    restrict L C χ = restrict L C ψ ↔ ∀ g ∈ C, (χ g).val = (ψ g).val := by
  constructor
  · intro h g hg
    have h' := congrFun h ⟨g, hg⟩
    exact congrArg Subtype.val h'
  · intro h
    funext g
    exact Subtype.ext (h g.val g.2)

/-- Restriction to the complement of `C` determines exactly the coordinates outside `C`. -/
lemma corestrict_eq_iff (L : E → Finset (Fin c)) (C : Finset E) (χ ψ : ListSpace L) :
    corestrict L C χ = corestrict L C ψ ↔ ∀ g ∉ C, (χ g).val = (ψ g).val := by
  constructor
  · intro h g hg
    have h' := congrFun h ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ g, hg⟩⟩
    exact congrArg Subtype.val h'
  · intro h
    funext g
    exact Subtype.ext (h g.val (Finset.mem_sdiff.mp g.2).2)

lemma restrict_surjective (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) (C : Finset E) :
    Function.Surjective (restrict L C) := by
  intro p
  refine ⟨fun g => if h : g ∈ C then p ⟨g, h⟩ else ⟨(hL g).choose, (hL g).choose_spec⟩, ?_⟩
  funext g
  simp only [restrict]
  rw [dif_pos g.2]

lemma corestrict_surjective (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) (C : Finset E) :
    Function.Surjective (corestrict L C) := by
  intro q
  refine ⟨fun g => if h : g ∈ C then ⟨(hL g).choose, (hL g).choose_spec⟩
    else q ⟨g, Finset.mem_sdiff.mpr ⟨Finset.mem_univ g, h⟩⟩, ?_⟩
  funext g
  simp only [corestrict]
  rw [dif_neg (Finset.mem_sdiff.mp g.2).2]

lemma restrict_image_univ (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) (C : Finset E) :
    restrict L C '' (Set.univ : Set (ListSpace L)) = Set.univ := by
  rw [Set.image_univ, Set.range_eq_univ]
  exact restrict_surjective L hL C

lemma corestrict_image_univ (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) (C : Finset E) :
    corestrict L C '' (Set.univ : Set (ListSpace L)) = Set.univ := by
  rw [Set.image_univ, Set.range_eq_univ]
  exact corestrict_surjective L hL C

/-- The cardinality of the pattern space on `C` is the product of the list sizes over `C`. -/
lemma card_Pat (L : E → Finset (Fin c)) (C : Finset E) :
    Fintype.card (Pat L C) = ∏ g ∈ C, (L g).card := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_coe]
  rw [Finset.prod_subtype (s := C) (h := fun g => Iff.rfl) (f := fun g : E => (L g).card)]

/-- The cardinality of the pattern space outside `C` is the product of the list sizes over
the complement of `C`. -/
lemma card_CoPat (L : E → Finset (Fin c)) (C : Finset E) :
    Fintype.card (CoPat L C) = ∏ g ∈ Finset.univ \ C, (L g).card := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_coe]
  rw [Finset.prod_subtype (s := Finset.univ \ C) (h := fun g => Iff.rfl)
    (f := fun g : E => (L g).card)]

/-- The cardinality of the list space is the product of the list sizes. -/
lemma card_listSpace (L : E → Finset (Fin c)) :
    Fintype.card (ListSpace L) = ∏ g, (L g).card := by
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl (fun g _ => Fintype.card_coe (L g))

/-- The product over all edges splits as the product over `C` times the product over the
complement of `C`. -/
lemma prod_univ_eq_split (L : E → Finset (Fin c)) (C : Finset E) :
    (∏ g, (L g).card) = (∏ g ∈ C, (L g).card) * (∏ g ∈ Finset.univ \ C, (L g).card) := by
  have h := Finset.prod_sdiff (s₁ := C) (s₂ := Finset.univ) (f := fun g : E => (L g).card)
    (Finset.subset_univ C)
  rw [mul_comm] at h
  exact h.symm

lemma ncard_eq_card {α : Type*} (s : Set α) [Fintype ↥s] : s.ncard = Fintype.card ↥s := by
  rw [Set.ncard_def, ← Set.coe_fintypeCard (s := s)]
  exact ENat.toNat_natCast _

lemma ncard_univ_eq_card (α : Type*) [Fintype α] : (Set.univ : Set α).ncard = Fintype.card α := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]

/-- The bijection underlying the counting: an element of `A ∩ B`, where `A` depends only on
the coordinates in `C` and `B` only on the coordinates outside `C`, is the same thing as a
`C`-pattern arising in `A` together with a complementary pattern arising in `B`. -/
def masterEquiv (L : E → Finset (Fin c)) (C : Finset E) (A B : Set (ListSpace L))
    (hA : ∀ φ ψ : ListSpace L, (∀ g ∈ C, (φ g).val = (ψ g).val) → (φ ∈ A ↔ ψ ∈ A))
    (hB : ∀ φ ψ : ListSpace L, (∀ g ∉ C, (φ g).val = (ψ g).val) → (φ ∈ B ↔ ψ ∈ B)) :
    ↥(A ∩ B) ≃ ↥(restrict L C '' A) × ↥(corestrict L C '' B) where
  toFun φ := (⟨restrict L C φ.1, ⟨φ.1, φ.2.1, rfl⟩⟩,
              ⟨corestrict L C φ.1, ⟨φ.1, φ.2.2, rfl⟩⟩)
  invFun p := by
    refine ⟨(splitEquiv L C).symm (p.1.1, p.2.1), ?_, ?_⟩
    · obtain ⟨ψ, hψA, hψ⟩ := p.1.2
      have hχ : restrict L C ((splitEquiv L C).symm (p.1.1, p.2.1)) = restrict L C ψ := by
        rw [splitEquiv_symm_fst, ← hψ]
      exact (hA _ ψ ((restrict_eq_iff L C _ ψ).mp hχ)).mpr hψA
    · obtain ⟨η, hηB, hη⟩ := p.2.2
      have hχ : corestrict L C ((splitEquiv L C).symm (p.1.1, p.2.1)) = corestrict L C η := by
        rw [splitEquiv_symm_snd, ← hη]
      exact (hB _ η ((corestrict_eq_iff L C _ η).mp hχ)).mpr hηB
  left_inv φ := Subtype.ext (Equiv.symm_apply_apply (splitEquiv L C) φ.1)
  right_inv p := Prod.ext (Subtype.ext (splitEquiv_symm_fst L C p.1.1 p.2.1))
    (Subtype.ext (splitEquiv_symm_snd L C p.1.1 p.2.1))

/-- **The counting lemma.**  If `A` only sees the coordinates in `C` and `B` only sees the
coordinates outside `C`, then `|A ∩ B| = |A|_C · |B|_{∁C}`, where `|A|_C` is the number of
`C`-patterns arising from `A` and `|B|_{∁C}` the number of complementary patterns arising
from `B`. -/
lemma card_inter_of_split (L : E → Finset (Fin c)) (C : Finset E) (A B : Set (ListSpace L))
    (hA : ∀ φ ψ : ListSpace L, (∀ g ∈ C, (φ g).val = (ψ g).val) → (φ ∈ A ↔ ψ ∈ A))
    (hB : ∀ φ ψ : ListSpace L, (∀ g ∉ C, (φ g).val = (ψ g).val) → (φ ∈ B ↔ ψ ∈ B)) :
    (A ∩ B).ncard = (restrict L C '' A).ncard * (corestrict L C '' B).ncard := by
  haveI : Fintype ↥(A ∩ B) := Fintype.ofFinite _
  haveI : Fintype ↥(restrict L C '' A) := Fintype.ofFinite _
  haveI : Fintype ↥(corestrict L C '' B) := Fintype.ofFinite _
  rw [ncard_eq_card (A ∩ B), ncard_eq_card (restrict L C '' A),
    ncard_eq_card (corestrict L C '' B)]
  rw [Fintype.card_congr (masterEquiv L C A B hA hB), Fintype.card_prod]

/-- Counting a set `A` that only sees the coordinates in `C`. -/
lemma card_of_depC (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) (C : Finset E)
    (A : Set (ListSpace L))
    (hA : ∀ φ ψ : ListSpace L, (∀ g ∈ C, (φ g).val = (ψ g).val) → (φ ∈ A ↔ ψ ∈ A)) :
    A.ncard = (restrict L C '' A).ncard * Fintype.card (CoPat L C) := by
  have h := card_inter_of_split L C A Set.univ hA (fun _ _ _ => Iff.rfl)
  rw [Set.inter_univ] at h
  rw [h, corestrict_image_univ L hL C, ncard_univ_eq_card]

/-- Counting a set `B` that only sees the coordinates outside `C`. -/
lemma card_of_depD (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) (C : Finset E)
    (B : Set (ListSpace L))
    (hB : ∀ φ ψ : ListSpace L, (∀ g ∉ C, (φ g).val = (ψ g).val) → (φ ∈ B ↔ ψ ∈ B)) :
    B.ncard = (corestrict L C '' B).ncard * Fintype.card (Pat L C) := by
  have h := card_inter_of_split L C Set.univ B (fun _ _ _ => Iff.rfl) hB
  rw [Set.univ_inter] at h
  rw [h, restrict_image_univ L hL C, ncard_univ_eq_card]
  exact mul_comm _ _

/-- The probability of an event under the uniform measure on the list space, in terms of its
cardinality. -/
lemma listProb_prob_ncard (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty)
    (A : Set (ListSpace L)) :
    (listProb L hL).prob A = (A.ncard : ℝ) / (Fintype.card (ListSpace L) : ℝ) := by
  haveI : Nonempty (ListSpace L) := ⟨fun e => ⟨(hL e).choose, (hL e).choose_spec⟩⟩
  have h : listProb L hL = Work.Deep.Prob.FinProbSpace.uniform (ListSpace L) := rfl
  rw [h, Work.Deep.Prob.Spaces.uniform_prob_ncard A]

/-- The image of the event "edge `e` receives colour `γ`" under the restriction to `{e}` is
the single pattern with value `γ` at `e`. -/
lemma image_restrict_singleton (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) {e : E}
    {γ : Fin c} (hγ : γ ∈ L e) :
    restrict L ({e} : Finset E) '' {φ : ListSpace L | (φ e).val = γ}
      = {fun g : {g : E // g ∈ ({e} : Finset E)} =>
          ⟨γ, by rw [Finset.mem_singleton.mp g.2]; exact hγ⟩} := by
  ext p
  constructor
  · intro hp
    obtain ⟨φ, hφ, rfl⟩ := (Set.mem_image _ _ _).mp hp
    funext g
    refine Subtype.ext ?_
    have hg : g = ⟨e, Finset.mem_singleton_self e⟩ :=
      Subtype.ext (Finset.mem_singleton.mp g.2)
    rw [hg]
    exact hφ
  · intro hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    rw [Set.mem_image]
    refine ⟨fun g : E => if h : g = e then ⟨γ, by rw [h]; exact hγ⟩
      else ⟨(hL g).choose, (hL g).choose_spec⟩, ?_, ?_⟩
    · show ((if h : e = e then ⟨γ, by rw [h]; exact hγ⟩
        else ⟨(hL e).choose, (hL e).choose_spec⟩) : {γ' : Fin c // γ' ∈ L e}).val = γ
      rw [dif_pos rfl]
    · funext g
      refine Subtype.ext ?_
      have hg : g = ⟨e, Finset.mem_singleton_self e⟩ :=
        Subtype.ext (Finset.mem_singleton.mp g.2)
      rw [hg]
      show ((if h : e = e then ⟨γ, by rw [h]; exact hγ⟩
        else ⟨(hL e).choose, (hL e).choose_spec⟩) : {γ' : Fin c // γ' ∈ L e}).val = γ
      rw [dif_pos rfl]

/-- The element `e` of the two-element index type `↥{e, f}`. -/
def pairIdxE (e f : E) : {g : E // g ∈ ({e, f} : Finset E)} :=
  ⟨e, Finset.mem_insert_self e {f}⟩

/-- The element `f` of the two-element index type `↥{e, f}`. -/
def pairIdxF (e f : E) : {g : E // g ∈ ({e, f} : Finset E)} :=
  ⟨f, Finset.mem_insert_of_mem (Finset.mem_singleton_self f)⟩

lemma eq_pairIdxE_or_pairIdxF (e f : E)
    (g : {g : E // g ∈ ({e, f} : Finset E)}) :
    g = pairIdxE e f ∨ g = pairIdxF e f := by
  have hg := g.2
  rw [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with hg | hg
  · exact Or.inl (Subtype.ext hg)
  · exact Or.inr (Subtype.ext hg)

/-- A pattern on `{e, f}` that arises from the event "`e` and `f` are equally coloured" takes
the same value at `e` and at `f`. -/
lemma pair_val_eq_of_mem_image (L : E → Finset (Fin c)) {e f : E}
    {p : Pat L ({e, f} : Finset E)}
    (hp : p ∈ restrict L ({e, f} : Finset E) ''
        {φ : ListSpace L | (φ e).val = (φ f).val}) :
    (p (pairIdxE e f)).val = (p (pairIdxF e f)).val := by
  obtain ⟨φ, hφ, rfl⟩ := (Set.mem_image _ _ _).mp hp
  exact hφ

/-- The pattern on `{e, f}` that assigns the colour `δ` to both coordinates. -/
def pairPat (L : E → Finset (Fin c)) (e f : E) (δ : {γ : Fin c // γ ∈ L e ∩ L f}) :
    Pat L ({e, f} : Finset E) :=
  fun g => ⟨δ.val, by
    have hg := g.2
    rw [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with hg | hg
    · rw [hg]; exact (Finset.mem_inter.mp δ.2).1
    · rw [hg]; exact (Finset.mem_inter.mp δ.2).2⟩

/-- A colouring that uses the colour `δ` on both `e` and `f`, and anything outside `{e, f}`. -/
def pairColouring (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) (e f : E)
    (δ : {γ : Fin c // γ ∈ L e ∩ L f}) : ListSpace L :=
  fun g => if h : g = e then ⟨δ.val, by rw [h]; exact (Finset.mem_inter.mp δ.2).1⟩
    else if h : g = f then ⟨δ.val, by rw [h]; exact (Finset.mem_inter.mp δ.2).2⟩
    else ⟨(hL g).choose, (hL g).choose_spec⟩

lemma pairColouring_e (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) (e f : E)
    (δ : {γ : Fin c // γ ∈ L e ∩ L f}) : (pairColouring L hL e f δ e).val = δ.val := by
  show ((if h : e = e then ⟨δ.val, _⟩ else _) : {γ : Fin c // γ ∈ L e}).val = δ.val
  rw [dif_pos rfl]

lemma pairColouring_f (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) {e f : E}
    (hef : e ≠ f) (δ : {γ : Fin c // γ ∈ L e ∩ L f}) :
    (pairColouring L hL e f δ f).val = δ.val := by
  show ((if h : f = e then ⟨δ.val, _⟩
    else if h : f = f then ⟨δ.val, _⟩ else _) : {γ : Fin c // γ ∈ L f}).val = δ.val
  rw [dif_neg hef.symm, dif_pos rfl]

lemma pairColouring_mem (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) {e f : E}
    (hef : e ≠ f) (δ : {γ : Fin c // γ ∈ L e ∩ L f}) :
    pairColouring L hL e f δ ∈ {φ : ListSpace L | (φ e).val = (φ f).val} := by
  show (pairColouring L hL e f δ e).val = (pairColouring L hL e f δ f).val
  rw [pairColouring_e, pairColouring_f L hL hef]

lemma restrict_pairColouring (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) {e f : E}
    (hef : e ≠ f) (δ : {γ : Fin c // γ ∈ L e ∩ L f}) :
    restrict L ({e, f} : Finset E) (pairColouring L hL e f δ) = pairPat L e f δ := by
  funext g
  refine Subtype.ext ?_
  rcases eq_pairIdxE_or_pairIdxF e f g with hg | hg
  · rw [hg]
    show (pairColouring L hL e f δ e).val = δ.val
    rw [pairColouring_e]
  · rw [hg]
    show (pairColouring L hL e f δ f).val = δ.val
    rw [pairColouring_f L hL hef]

/-- The image of the event "the two edges `e ≠ f` receive the same colour" under the
restriction to `{e, f}` is in bijection with the intersection of the two lists. -/
lemma card_image_restrict_pair (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty)
    {e f : E} (hef : e ≠ f) :
    (restrict L ({e, f} : Finset E) ''
        {φ : ListSpace L | (φ e).val = (φ f).val}).ncard = (L e ∩ L f).card := by
  have hmain : (restrict L ({e, f} : Finset E) ''
        {φ : ListSpace L | (φ e).val = (φ f).val}).ncard
      = (((L e ∩ L f : Finset (Fin c)) : Set (Fin c))).ncard := by
    refine Set.ncard_congr (fun a _ => (a (pairIdxE e f)).val) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_inter]
      exact ⟨(a (pairIdxE e f)).2, by
        rw [pair_val_eq_of_mem_image L ha]
        exact (a (pairIdxF e f)).2⟩
    · intro a b ha hb hab
      funext g
      refine Subtype.ext ?_
      rcases eq_pairIdxE_or_pairIdxF e f g with hg | hg
      · rw [hg]; exact hab
      · rw [hg, ← pair_val_eq_of_mem_image L ha, ← pair_val_eq_of_mem_image L hb, hab]
    · intro δ hδ
      refine ⟨pairPat L e f ⟨δ, by simpa using hδ⟩, ?_, ?_⟩
      · exact (Set.mem_image _ _ _).mpr ⟨pairColouring L hL e f ⟨δ, by simpa using hδ⟩,
          pairColouring_mem L hL hef _, restrict_pairColouring L hL hef _⟩
      · rfl
  rw [hmain, Set.ncard_coe_finset]

/-- The arithmetic of the single-coordinate count. -/
lemma arith_one (X a : ℝ) (ha : a ≠ 0) (hX : X ≠ 0) : X / (a * X) = 1 / a := by
  field_simp

/-- The arithmetic of the two-coordinate count. -/
lemma arith_two (X k a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hX : X ≠ 0) :
    (k * X) / ((a * b) * X) = k / (a * b) := by
  field_simp

/-- The arithmetic of the independence statement. -/
lemma arith_indep (s t a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (s * t) / (a * b) = ((s * b) / (a * b)) * ((a * t) / (a * b)) := by
  field_simp


/-- A product of (cast) list sizes is nonzero, all lists being nonempty. -/
lemma prod_card_ne_zero (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) (C : Finset E) :
    (∏ g ∈ C, ((L g).card : ℝ)) ≠ 0 := by
  refine ne_of_gt (Finset.prod_pos ?_)
  intro g _
  exact_mod_cast (Finset.card_pos.mpr (hL g))

/-- The uniform measure on the list space `(e : E) → {γ : Fin c // γ ∈ L e}` of all
choices of a colour from each list satisfies:

* the probability that one edge receives a prescribed colour `γ` is `1 / |L e|`;
* the probability that two distinct edges receive the same colour is
  `|L e ∩ L f| / (|L e| * |L f|)`;
* events that only see coordinates in a set `C` of edges are independent of events that only
  see the coordinates outside `C`.

Sketch (pure counting).  By `Work.Deep.Prob.Spaces.uniform_prob_ncard` (module
`Submission.Work.Deep.Prob.Spaces.uniform_prob_ncard`),
`prob A = (A.ncard : ℝ) / (Fintype.card Ω : ℝ)`, and
`Fintype.card (ListSpace L) = ∏ e, (L e).card` (`Fintype.card_pi` together with
`Fintype.card_subtype`, as `Fintype.card {γ : Fin c // γ ∈ L e} = (L e).card`).  Count the
functions with prescribed value(s) at one or two coordinates by peeling those coordinates off
with `Equiv.piOptionEquivProd` (composed with `Equiv.piCongrLeft` along the equivalence
`E ≃ Option {g // g ≠ e}` sending `e` to `none`); the number of functions with `φ e = γ` is
`∏_{g ≠ e} (L g).card`, and with `φ e = γ`, `φ f = δ` it is `∏_{g ∉ {e,f}} (L g).card`.  For
the independence statement, split `Ω` into the fibres of the restriction map `φ ↦ φ|_C`: each
fibre over a valid `C`-pattern has cardinality `∏_{g ∉ C} (L g).card`, an event that only sees
the coordinates in `C` is constant on fibres (so it meets exactly
`|X| / ∏_{g ∉ C} (L g).card` of them), while an event that only sees the coordinates outside
`C` has the same cardinality in every fibre; both sides then reduce to `|X| |Y| / |Ω|`. -/
theorem listProb_facts {E : Type*} [Fintype E] [DecidableEq E] {c : ℕ}
    (L : E → Finset (Fin c)) (hL : ∀ e, (L e).Nonempty) :
    (∀ e : E, ∀ γ : Fin c, γ ∈ L e →
      (Work.Deep.Kahn.listProb L hL).prob
        {φ : Work.Deep.Kahn.ListSpace L | (φ e).val = γ} = 1 / ((L e).card : ℝ))
    ∧ (∀ e f : E, e ≠ f →
      (Work.Deep.Kahn.listProb L hL).prob
        {φ : Work.Deep.Kahn.ListSpace L | (φ e).val = (φ f).val}
        = ((L e ∩ L f).card : ℝ) / (((L e).card : ℝ) * ((L f).card : ℝ)))
    ∧ (∀ (C : Finset E) (X Y : Set (Work.Deep.Kahn.ListSpace L)),
      (∀ φ ψ : Work.Deep.Kahn.ListSpace L, (∀ c ∈ C, (φ c).val = (ψ c).val) → (φ ∈ X ↔ ψ ∈ X)) →
      (∀ φ ψ : Work.Deep.Kahn.ListSpace L, (∀ c ∉ C, (φ c).val = (ψ c).val) → (φ ∈ Y ↔ ψ ∈ Y)) →
      (Work.Deep.Kahn.listProb L hL).prob (X ∩ Y)
        = (Work.Deep.Kahn.listProb L hL).prob X * (Work.Deep.Kahn.listProb L hL).prob Y) := by
  refine ⟨?_, ?_, ?_⟩
  · -- one prescribed colour on a single edge
    intro e γ hγ
    have hdep : ∀ φ ψ : ListSpace L,
        (∀ g ∈ ({e} : Finset E), (φ g).val = (ψ g).val) →
        (φ ∈ {φ : ListSpace L | (φ e).val = γ} ↔ ψ ∈ {φ : ListSpace L | (φ e).val = γ}) := by
      intro φ ψ h
      have h1 : (φ e).val = (ψ e).val := h e (Finset.mem_singleton_self e)
      show (φ e).val = γ ↔ (ψ e).val = γ
      rw [h1]
    have hcount : ({φ : ListSpace L | (φ e).val = γ}).ncard
        = ∏ g ∈ Finset.univ \ ({e} : Finset E), (L g).card := by
      rw [card_of_depC L hL ({e} : Finset E) _ hdep, image_restrict_singleton L hL hγ,
        Set.ncard_singleton, one_mul, card_CoPat L ({e} : Finset E)]
    rw [listProb_prob_ncard L hL, hcount, card_listSpace,
      prod_univ_eq_split L ({e} : Finset E), Finset.prod_singleton]
    push_cast
    have ha : ((L e).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr (hL e))
    have hX : (∏ g ∈ Finset.univ \ ({e} : Finset E), ((L g).card : ℝ)) ≠ 0 :=
      prod_card_ne_zero L hL _
    field_simp
  · -- the same colour on two distinct edges
    intro e f hef
    have hdep : ∀ φ ψ : ListSpace L,
        (∀ g ∈ ({e, f} : Finset E), (φ g).val = (ψ g).val) →
        (φ ∈ {φ : ListSpace L | (φ e).val = (φ f).val} ↔
          ψ ∈ {φ : ListSpace L | (φ e).val = (φ f).val}) := by
      intro φ ψ h
      have h1 : (φ e).val = (ψ e).val := h e (Finset.mem_insert_self e {f})
      have h2 : (φ f).val = (ψ f).val :=
        h f (Finset.mem_insert_of_mem (Finset.mem_singleton_self f))
      show (φ e).val = (φ f).val ↔ (ψ e).val = (ψ f).val
      rw [h1, h2]
    have hcount : ({φ : ListSpace L | (φ e).val = (φ f).val}).ncard
        = (L e ∩ L f).card * ∏ g ∈ Finset.univ \ ({e, f} : Finset E), (L g).card := by
      rw [card_of_depC L hL ({e, f} : Finset E) _ hdep, card_image_restrict_pair L hL hef,
        card_CoPat L ({e, f} : Finset E)]
    rw [listProb_prob_ncard L hL, hcount, card_listSpace,
      prod_univ_eq_split L ({e, f} : Finset E), Finset.prod_pair hef]
    push_cast
    have ha : ((L e).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr (hL e))
    have hb : ((L f).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr (hL f))
    have hX : (∏ g ∈ Finset.univ \ ({e, f} : Finset E), ((L g).card : ℝ)) ≠ 0 :=
      prod_card_ne_zero L hL _
    field_simp
  · -- independence of events depending on disjoint coordinate sets
    intro C X Y hX hY
    rw [listProb_prob_ncard L hL (X ∩ Y), card_inter_of_split L C X Y hX hY,
      listProb_prob_ncard L hL X, card_of_depC L hL C X hX,
      listProb_prob_ncard L hL Y, card_of_depD L hL C Y hY,
      card_listSpace, prod_univ_eq_split L C, card_Pat L C, card_CoPat L C]
    push_cast
    have hnC : (∏ g ∈ C, ((L g).card : ℝ)) ≠ 0 := prod_card_ne_zero L hL C
    have hnD : (∏ g ∈ Finset.univ \ C, ((L g).card : ℝ)) ≠ 0 := prod_card_ne_zero L hL _
    field_simp

end

end Work.Deep.Kahn
