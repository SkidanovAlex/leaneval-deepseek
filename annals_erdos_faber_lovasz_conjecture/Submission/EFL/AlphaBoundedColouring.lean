import Submission.EFL.ColourClassSplitHonest
import Submission.EFL.ColourClassCounting

/-!
# α-bounded edge-colourings and the recolouring step

This file proves the honest version of Proposition 6.8(ii)
(`few-large-colour-classes`(ii)) of the paper: every hypergraph that admits
an `n`-colouring admits an *α-bounded* colouring with only a bounded number
of extra colours.

Recall (paper §6.3): a proper edge-colouring `φ` is *α-bounded* if every
colour `c` is either assigned to at most one edge, or the colour class
`φ⁻¹(c)` covers at most `αn` vertices.

The honest recolouring statement (`alpha_bounded_recolour`, proved at the
bottom) differs from the paper's Prop. 6.8(ii) only in the additive
constant of the colour bound: the paper writes `χ′(H) + 2n/(α²r)`; the
margin conventions of `ColourClassSplitHonest.lean` force us to split big
colour classes at the halved parameter `β/2` (see
`SplitPieceOK_half_strict`), costing `(4/β + 1)` pieces per big class and
`|C′| ≤ 2n/(βr)` big classes, i.e. an additive `(4/β + 1)·2n/(βr)` with an
absolute constant that the `≪`-hierarchy absorbs downstream.

## The machinery built here (all machine-checked)

1. `Coloring.AlphaBounded` — host-independent α-boundedness of a proper
   edge-colouring (works for colourings into any colour type; for colour
   host `Fin n` it agrees with the `classVertexCount` formulation,
   `AlphaBounded_iff_classVertexCount`);
2. `FamilyBounded` — the same boundedness for a finite family of vertex sets
   (the form in which colour classes appear in `SplitColourClassHonest`);
3. colour-labelling: from a finite family `Cls` of pairwise edge-disjoint
   matching families covering all the edges of `𝓗`, a proper colouring
   (`colouringOfFamilies`, `colouringOfFamilies_fin_AlphaBounded`) whose
   colour classes are exactly the members of `Cls`
   (`colouringOfFamilies_colorClass`), with the boundedness transfer
   (`AlphaBounded_of_FamilyBounded`, `AlphaBounded_recolor`);
4. **`alpha_bounded_recolour`** — the honest recolouring theorem
   (`few-large-colour-classes`(ii), Prop 6.8(ii)): if `φ` is a proper
   edge-colouring of a linear hypergraph with all edges of size `≥ r+1`,
   using the colours of `C`, then an `β`-bounded proper edge-colouring
   exists using at most `|C| + (2/(β/2) + 1)·n/((β/2)·r)` colours
   (= `|C| + (4/β + 1)·2n/(βr)`).  Big colour classes (covering `> βn/2`)
   are split by `splitColourClassHonest` at the halved parameter `β/2`,
   which absorbs the `+1` margin (`SplitPieceOK_half_strict`); small
   classes are kept.  The `4` (vs the paper's `2`) is an absolute constant
   the `≪`-hierarchy absorbs downstream (e.g. Prop 6.10 needs only
   `additive ≤ γn/2`).
-/


set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- A proper edge-colouring `φ` of a hypergraph on `Fin n` is *α-bounded*
(paper §6.3) if every colour is either assigned to at most one edge, or the
edges of that colour cover at most `αn` vertices.  Host-independent: the
covered-vertex count of a colour class is `FamilyVertexCount` of its
`EdgeSetFamily`. -/
def Hypergraph.Coloring.AlphaBounded {𝓗 : Hypergraph (Fin n)} {α : Type*}
    (β : ℝ) (φ : 𝓗.Coloring α) : Prop :=
  ∀ c : α, (φ.colorClass c).ncard ≤ 1 ∨
    (FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) : ℝ) ≤ β * (n : ℝ)

/-- Boundedness of a finite family of vertex sets: at most one edge or
covering at most `βn` vertices.  (For a colour class family of a proper
edge-colouring, `M.card` is the number of edges of the class and
`FamilyVertexCount M` the number of vertices it covers.) -/
def FamilyBounded (β : ℝ) (M : Finset (Set (Fin n))) : Prop :=
  M.card ≤ 1 ∨ (FamilyVertexCount M : ℝ) ≤ β * (n : ℝ)

/-- For colour host `Fin n` the host-independent boundedness agrees with the
`classVertexCount` formulation. -/
theorem AlphaBounded_iff_classVertexCount {𝓗 : Hypergraph (Fin n)} (β : ℝ)
    (φ : 𝓗.Coloring (Fin n)) :
    φ.AlphaBounded β ↔
      ∀ c : Fin n, (φ.colorClass c).ncard ≤ 1 ∨
        (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ) := by
  constructor
  · intro h c
    rcases h c with hOne | hBdd
    · exact Or.inl hOne
    · right
      have hEq : FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) = φ.classVertexCount c :=
        (classVertexCount_eq_FamilyVertexCount φ c).symm
      rwa [hEq] at hBdd
  · intro h c
    rcases h c with hOne | hBdd
    · exact Or.inl hOne
    · right
      have hEq : FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) = φ.classVertexCount c :=
        (classVertexCount_eq_FamilyVertexCount φ c).symm
      rwa [hEq]

/-! ## Colouring from a family of pairwise-disjoint matching families

The recolouring construction needs the following general device: if `Cls`
is a finite family of pairwise edge-disjoint matching families of vertex
sets which together contain the vertex set of every edge of `𝓗`, then
colouring each edge by the (unique) member of `Cls` containing its vertex
set is a proper edge-colouring (`colouringOfFamilies`).  Its colour classes
are exactly the members of `Cls` (`colouringOfFamilies_colorClass`), and if
every member is `FamilyBounded β` then the colouring is `AlphaBounded β`
(`AlphaBounded_of_FamilyBounded`).  Colourings into `Fin (card Cls)` are
obtained by renaming colours (`colouringOfFamilies_fin`,
`colouringOfFamilies_fin_AlphaBounded`).
-/

/-- The subfamily of edges of `𝓗` whose vertex set lies in a given finite
family `M` of vertex sets. -/
def edgeSetOfFamily (𝓗 : Hypergraph (Fin n)) (M : Finset (Set (Fin n))) : Set 𝓗 :=
  {x : 𝓗 | (x : Set (Fin n)) ∈ M}

/-- A finite family of pairwise edge-disjoint matching families that covers
the vertex set of every edge gives a proper edge-colouring: colour an edge
by (any chosen) member containing its vertex set.  (The colour type is the
set of members itself.) -/
def colouringOfFamilies {𝓗 : Hypergraph (Fin n)} (Cls : Finset (Finset (Set (Fin n))))
    (hmat : ∀ M ∈ Cls, IsMatchingFamily M)
    (hcov : ∀ e : 𝓗, ∃ M : Finset (Set (Fin n)), M ∈ Cls ∧ (e : Set (Fin n)) ∈ M) :
    𝓗.Coloring {M : Finset (Set (Fin n)) // M ∈ Cls} where
  labels e := ⟨Classical.choose (hcov e), (Classical.choose_spec (hcov e)).1⟩
  isColoring := by
    intro e₁ e₂ he hnon hsame
    -- hsame : the chosen members agree
    have hch : Classical.choose (hcov e₁) = Classical.choose (hcov e₂) := by
      exact congrArg Subtype.val hsame
    let M : Finset (Set (Fin n)) := Classical.choose (hcov e₁)
    have he₁' : (e₁ : Set (Fin n)) ∈ M := by
      simpa [M] using (Classical.choose_spec (hcov e₁)).2
    have he₂' : (e₂ : Set (Fin n)) ∈ M := by
      have h₂ : (e₂ : Set (Fin n)) ∈ Classical.choose (hcov e₂) :=
        (Classical.choose_spec (hcov e₂)).2
      simpa [M, ← hch] using h₂
    have hM : M ∈ Cls := by
      simpa [M] using (Classical.choose_spec (hcov e₁)).1
    have hvals : (e₁ : Set (Fin n)) ≠ (e₂ : Set (Fin n)) := by
      intro hv
      apply he
      apply Subtype.ext
      simpa using hv
    have hdisj := hmat M hM he₁' he₂' hvals
    exact (Set.not_disjoint_iff_nonempty_inter.mpr hnon) hdisj

/-- The colour class of a member `M` of `colouringOfFamilies` consists
exactly of the edges whose vertex set lies in `M` — provided the members are
pairwise edge-disjoint (then the chosen member containing an edge is unique,
so the fibre of `M` is `edgeSetOfFamily M`). -/
lemma colouringOfFamilies_colorClass {𝓗 : Hypergraph (Fin n)} {Cls : Finset (Finset (Set (Fin n)))}
    (hmat : ∀ M ∈ Cls, IsMatchingFamily M)
    (hcov : ∀ e : 𝓗, ∃ M : Finset (Set (Fin n)), M ∈ Cls ∧ (e : Set (Fin n)) ∈ M)
    (hdisj : ∀ M₁ ∈ Cls, ∀ M₂ ∈ Cls, M₁ ≠ M₂ → Disjoint M₁ M₂)
    (M : Finset (Set (Fin n))) (hM : M ∈ Cls) :
    (colouringOfFamilies Cls hmat hcov).colorClass ⟨M, hM⟩ = edgeSetOfFamily 𝓗 M := by
  classical
  ext x
  constructor
  · -- x has colour ⟨M, hM⟩: the chosen member is M, so x.val ∈ M
    intro hx
    have hch : Classical.choose (hcov x) = M := by
      exact congrArg Subtype.val hx
    simpa [edgeSetOfFamily, hch] using (Classical.choose_spec (hcov x)).2
  · intro hx
    -- x.val ∈ M: the chosen member N of x contains x.val; disjointness forces N = M
    simp [edgeSetOfFamily] at hx
    rw [mem_colorClass]
    apply Subtype.ext
    let N : Finset (Set (Fin n)) := Classical.choose (hcov x)
    have hN : N ∈ Cls := (Classical.choose_spec (hcov x)).1
    have hxN : (x : Set (Fin n)) ∈ N := (Classical.choose_spec (hcov x)).2
    by_contra hne
    have hd : Disjoint N M := hdisj N hN M hM hne
    have hEq : N ∩ M = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
    have hmem : (x : Set (Fin n)) ∈ N ∩ M := Finset.mem_inter.mpr ⟨hxN, hx⟩
    rw [hEq] at hmem
    simp at hmem

/-- The edges of `𝓗` with vertex set in `M` are at most as many as the
vertex sets of `M` (vertex sets of distinct edges are distinct). -/
lemma ncard_edgeSetOfFamily_le_card {𝓗 : Hypergraph (Fin n)} (M : Finset (Set (Fin n))) :
    (edgeSetOfFamily 𝓗 M).ncard ≤ M.card := by
  classical
  have himg : (fun x : 𝓗 => (x : Set (Fin n))) '' (edgeSetOfFamily 𝓗 M)
      ⊆ (M : Set (Set (Fin n))) := by
    rintro e ⟨x, hx, rfl⟩
    exact hx
  calc
    (edgeSetOfFamily 𝓗 M).ncard
        = ((fun x : 𝓗 => (x : Set (Fin n))) '' (edgeSetOfFamily 𝓗 M)).ncard := by
            rw [Set.ncard_image_of_injective (edgeSetOfFamily 𝓗 M)]
            intro x y hxy
            apply Subtype.ext
            exact hxy
    _ ≤ (M : Set (Set (Fin n))).ncard := Set.ncard_le_ncard himg
    _ = M.card := by simp

/-- If every vertex set of `M` is an edge of `𝓗`, the edges of `𝓗` whose
vertex set lies in `M` have exactly the family `M`. -/
lemma EdgeSetFamily_edgeSetOfFamily {𝓗 : Hypergraph (Fin n)} {M : Finset (Set (Fin n))}
    (hin : FamilyInHypergraph 𝓗 M) : EdgeSetFamily (edgeSetOfFamily 𝓗 M) = M := by
  classical
  ext e
  constructor
  · intro he
    rcases (mem_EdgeSetFamily (edgeSetOfFamily 𝓗 M) e).1 he with ⟨x, hx, hx'⟩
    simpa [edgeSetOfFamily, ← hx'] using hx
  · intro he
    refine (mem_EdgeSetFamily (edgeSetOfFamily 𝓗 M) e).2 ⟨⟨e, hin he⟩, ?_, rfl⟩
    exact he

/-- The colour classes of `colouringOfFamilies` are exactly the members of
`Cls`; if every member is `FamilyBounded β`, the colouring is `AlphaBounded
β`. -/
theorem AlphaBounded_of_FamilyBounded {𝓗 : Hypergraph (Fin n)}
    {Cls : Finset (Finset (Set (Fin n)))} (β : ℝ)
    (hmat : ∀ M ∈ Cls, IsMatchingFamily M)
    (hcov : ∀ e : 𝓗, ∃ M : Finset (Set (Fin n)), M ∈ Cls ∧ (e : Set (Fin n)) ∈ M)
    (hdisj : ∀ M₁ ∈ Cls, ∀ M₂ ∈ Cls, M₁ ≠ M₂ → Disjoint M₁ M₂)
    (hin : ∀ M ∈ Cls, FamilyInHypergraph 𝓗 M)
    (hbdd : ∀ M ∈ Cls, FamilyBounded β M) :
    (colouringOfFamilies Cls hmat hcov).AlphaBounded β := by
  classical
  rintro ⟨M, hM⟩
  have hcl := colouringOfFamilies_colorClass (Cls := Cls) (hmat := hmat) (hcov := hcov)
    (hdisj := hdisj) M hM
  rcases hbdd M hM with hOne | hBdd
  · left
    have hle := ncard_edgeSetOfFamily_le_card (𝓗 := 𝓗) M
    simpa [hcl] using hle.trans hOne
  · right
    have hEq := EdgeSetFamily_edgeSetOfFamily (hin M hM)
    rw [hcl, hEq]
    exact hBdd

/-- Renaming colours by a bijection preserves α-boundedness: the colour
classes are only relabelled. -/
lemma AlphaBounded_recolor {𝓗 : Hypergraph (Fin n)} {α β : Type*} (b : ℝ)
    (ψ : 𝓗.Coloring α) (e : α ≃ β) : (ψ.recolor e).AlphaBounded b ↔ ψ.AlphaBounded b := by
  classical
  constructor
  · intro h γ
    -- boundedness of the class of ψ at colour γ = boundedness of recolor at colour e γ
    have hγ := h (e γ)
    have hcl : (ψ.recolor e).colorClass (e γ) = ψ.colorClass γ := by
      ext x
      simp [mem_colorClass, Hypergraph.Coloring.recolor]
    rw [hcl] at hγ
    exact hγ
  · intro h i
    -- i = e (e.symm i)
    have hγ := h (e.symm i)
    have hcl : (ψ.recolor e).colorClass i = ψ.colorClass (e.symm i) := by
      ext x
      simp [mem_colorClass, Hypergraph.Coloring.recolor]
      constructor
      · intro hx
        -- e (labels x) = i: apply e.symm on both sides
        have hx' := congrArg e.symm hx
        simpa using hx'
      · intro hx
        -- hx : ψ.labels x = e.symm i: apply e and simplify e (e.symm i) = i
        simpa using congrArg e hx
    rw [← hcl] at hγ
    exact hγ

/-- Colouring `𝓗` with one colour per member of `Cls`, renamed to
`Fin (card Cls)`; the colour classes are still the members, so memberwise
`FamilyBounded β` gives an `AlphaBounded β` colouring into `Fin (card Cls)`. -/
theorem colouringOfFamilies_fin_AlphaBounded {𝓗 : Hypergraph (Fin n)}
    {Cls : Finset (Finset (Set (Fin n)))} (β : ℝ)
    (hmat : ∀ M ∈ Cls, IsMatchingFamily M)
    (hcov : ∀ e : 𝓗, ∃ M : Finset (Set (Fin n)), M ∈ Cls ∧ (e : Set (Fin n)) ∈ M)
    (hdisj : ∀ M₁ ∈ Cls, ∀ M₂ ∈ Cls, M₁ ≠ M₂ → Disjoint M₁ M₂)
    (hin : ∀ M ∈ Cls, FamilyInHypergraph 𝓗 M)
    (hbdd : ∀ M ∈ Cls, FamilyBounded β M) :
    ∃ ψ : 𝓗.Coloring (Fin (Cls.card)), ψ.AlphaBounded β := by
  classical
  let ψ₀ := colouringOfFamilies (Cls := Cls) (hmat := hmat) (hcov := hcov)
  have hψ₀ : ψ₀.AlphaBounded β := AlphaBounded_of_FamilyBounded β hmat hcov hdisj hin hbdd
  have hcard : Fintype.card {M : Finset (Set (Fin n)) // M ∈ Cls} = Cls.card := by
    simp
  let e : {M : Finset (Set (Fin n)) // M ∈ Cls} ≃ Fin (Cls.card) :=
    (Fintype.equivFin {M : Finset (Set (Fin n)) // M ∈ Cls}).trans (Equiv.cast (by rw [hcard]))
  refine ⟨ψ₀.recolor e, ?_⟩
  exact (AlphaBounded_recolor β ψ₀ e).mpr hψ₀

/-! ## The recolouring theorem (`few-large-colour-classes` (ii), Prop 6.8(ii))

Fix a proper edge-colouring `φ` of a linear `n`-vertex hypergraph `𝓗` whose
edges all have size `≥ r+1`, with a used-colour set `C`.  Colour classes
whose coverage exceeds `(β/2)·n` are *big*; `few-large-colour-classes`(i)
bounds their number by `n/((β/2)r)`.  Each big colour class is split by
`splitColourClassHonest` at the halved parameter `β/2` into at most
`2/(β/2)+1` pieces (each a single edge or covering `< βn/2 + 1 ≤ βn`
vertices, by `SplitPieceOK_half_strict`); the classes outside `C′` already
cover `< βn/2` vertices and are kept.  Colouring every piece and every kept
class with its own colour yields the honest version of the paper's
`few-large-colour-classes`(ii): an `α`-bounded colouring with
`|C| + (2/(β/2)+1)·|C′|` colours.  (The paper writes `χ′(H) + 2n/(α²r)` for
`α = β/2`; our additive carries the `+1`-margin pieces and uses the bound on
`|C′|` instead of `χ′(H)` — constants the `≪`-hierarchy absorbs.)
-/

/-- Subfamilies of disjoint families are disjoint. -/
lemma disjoint_of_subset_disjoint {α : Type*} [DecidableEq α]
    {A B C D : Finset α} (hAC : A ⊆ C) (hBD : B ⊆ D) (h : Disjoint C D) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  have hxnot : x ∉ D := Finset.disjoint_left.mp h (hAC hxA)
  exact hxnot (hBD hxB)

/-- The pieces of a colour-class split are pairwise edge-disjoint (an edge of
the class lies in a unique piece). -/
lemma splitPieces_disjoint {𝓗 : Hypergraph (Fin n)} (c : Fin n) (φ : 𝓗.Coloring (Fin n))
    (P : Finset (Finset (Set (Fin n))))
    (hsub : ∀ M ∈ P, M ⊆ EdgeSetFamily (φ.colorClass c))
    (hone : ∀ e : Set (Fin n), e ∈ EdgeSetFamily (φ.colorClass c) → ∃! M, M ∈ P ∧ e ∈ M) :
    ∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂ := by
  classical
  intro M₁ hM₁ M₂ hM₂ hne
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  have hec : e ∈ EdgeSetFamily (φ.colorClass c) := hsub M₁ hM₁ he₁
  have huniq := hone e hec
  apply hne
  exact huniq.unique ⟨hM₁, he₁⟩ ⟨hM₂, he₂⟩

/-- Every edge lies in its own colour-class family. -/
lemma edge_mem_colorClass_family {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n))
    (e : 𝓗) : (e : Set (Fin n)) ∈ EdgeSetFamily (φ.colorClass (φ.labels e)) := by
  classical
  exact (mem_EdgeSetFamily (φ.colorClass (φ.labels e)) (e : Set (Fin n))).2 ⟨e, rfl, rfl⟩

/-- Colour classes of distinct colours are edge-disjoint. -/
lemma colorClassFamily_disjoint {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n))
    {c₁ c₂ : Fin n} (hne : c₁ ≠ c₂) :
    Disjoint (EdgeSetFamily (φ.colorClass c₁)) (EdgeSetFamily (φ.colorClass c₂)) := by
  classical
  exact EdgeSetFamily_disjoint (Hypergraph.Coloring.colorClass_disjoint φ hne)

/-- **The recolouring step** (`few-large-colour-classes`(ii), Prop 6.8(ii),
honest form): if `φ` is a proper edge-colouring of a linear `n`-vertex
hypergraph whose edges all have size at least `r + 1`, using the colours of
`C`, then an `β`-bounded proper edge-colouring exists using at most
`|C| + (2/(β/2) + 1)·n/((β/2)r)` colours (the big colour classes — those
covering more than `βn/2` vertices — are split at the halved parameter
`β/2`, which absorbs the `+1` margin of `SplitPieceOK` once `βn ≥ 2`). -/
theorem alpha_bounded_recolour {n r : ℕ} {β : ℝ} (hβ : 0 < β) (h2βn : (2 : ℝ) ≤ β * (n : ℝ))
    (h2n : 2 ≤ n) (hr : 1 ≤ r) {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, (r + 1 : ℕ) ≤ edgeSize (e : Set (Fin n)))
    {C : Finset (Fin n)} (φ : 𝓗.Coloring (Fin n)) (hφC : φ.UsesColourSet C) :
    ∃ (m : ℕ) (ψ : 𝓗.Coloring (Fin m)),
      ψ.AlphaBounded β ∧
      ((m : ℝ) ≤ (C.card : ℝ) +
        ((2 : ℝ) / (β / 2) + 1) * ((n : ℝ) / ((β / 2 : ℝ) * (r : ℝ)))) := by
  classical
  have hβ2 : 0 < β / 2 := half_pos hβ
  have hn1 : 1 ≤ n := by omega
  have hpos : ∀ e ∈ 𝓗, 1 ≤ edgeSize e := by
    intro e he
    have hsz : (r + 1 : ℕ) ≤ edgeSize e := by
      simpa using (hsize ⟨e, he⟩)
    omega
  -- the honest split of every colour class at the halved parameter β/2
  let Pfun : Fin n → Finset (Finset (Set (Fin n))) := fun c =>
    Classical.choose (splitColourClassHonest (α := β / 2) hβ2 hn1 (𝓗 := 𝓗) hpos φ c)
  have hsplit : ∀ c : Fin n,
      (∀ M ∈ Pfun c, M ⊆ EdgeSetFamily (φ.colorClass c)) ∧
      (∀ M ∈ Pfun c, SplitPieceOK (β / 2) M) ∧
      (∀ e : Set (Fin n), e ∈ EdgeSetFamily (φ.colorClass c) →
        ∃! M : Finset (Set (Fin n)), M ∈ Pfun c ∧ e ∈ M) ∧
      (((Pfun c).card : ℝ) ≤ (2 : ℝ) / (β / 2) + 1) := by
    intro c
    exact Classical.choose_spec (splitColourClassHonest (α := β / 2) hβ2 hn1 (𝓗 := 𝓗) hpos φ c)
  let big : Fin n → Prop := fun c => (β / 2 : ℝ) * (n : ℝ) ≤ (φ.classVertexCount c : ℝ)
  let C' : Finset (Fin n) := C.filter big
  -- the final colour classes: kept small classes + pieces of the big classes
  let kept : Finset (Finset (Set (Fin n))) :=
    (C \ C').image (fun c : Fin n => EdgeSetFamily (φ.colorClass c))
  let bigPieces : Finset (Finset (Set (Fin n))) := C'.biUnion Pfun
  let Cls : Finset (Finset (Set (Fin n))) := kept ∪ bigPieces
  -- every member is a family of edges of 𝓗
  have hin : ∀ M ∈ Cls, FamilyInHypergraph 𝓗 M := by
    intro M hM
    dsimp [Cls] at hM
    rcases Finset.mem_union.mp hM with hk | hb
    · rcases Finset.mem_image.mp hk with ⟨c, _hc, hEq⟩
      rw [← hEq]
      exact EdgeSetFamily_subset (φ.colorClass c)
    · rcases Finset.mem_biUnion.mp hb with ⟨c, _hc, hM⟩
      intro e he
      exact EdgeSetFamily_subset (φ.colorClass c) ((hsplit c).1 M hM he)
  -- every member is a matching
  have hmat : ∀ M ∈ Cls, IsMatchingFamily M := by
    intro M hM
    dsimp [Cls] at hM
    rcases Finset.mem_union.mp hM with hk | hb
    · rcases Finset.mem_image.mp hk with ⟨c, _hc, hEq⟩
      rw [← hEq]
      exact IsMatchingFamily_of_IsMatching (Hypergraph.Coloring.colorClass_isMatching φ c)
    · rcases Finset.mem_biUnion.mp hb with ⟨c, _hc, hM⟩
      exact ((hsplit c).2.1 M hM).1
  -- every edge is covered
  have hcov : ∀ e : 𝓗, ∃ M : Finset (Set (Fin n)), M ∈ Cls ∧ (e : Set (Fin n)) ∈ M := by
    intro e
    let c : Fin n := φ.labels e
    have heC : c ∈ C := hφC e
    have heF : (e : Set (Fin n)) ∈ EdgeSetFamily (φ.colorClass c) :=
      edge_mem_colorClass_family φ e
    by_cases hc' : c ∈ C'
    · -- big colour: split class; the edge lies in a piece
      have huniq := (hsplit c).2.2.1 e heF
      rcases huniq with ⟨M, hMmem, _huniq⟩
      rcases hMmem with ⟨hM, heM⟩
      refine ⟨M, ?_, heM⟩
      dsimp [Cls]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨c, hc', hM⟩))
    · -- small colour: the whole class is kept
      have hcCd : c ∈ C \ C' := by
        rw [Finset.mem_sdiff]
        exact ⟨heC, hc'⟩
      refine ⟨EdgeSetFamily (φ.colorClass c), ?_, heF⟩
      dsimp [Cls]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨c, hcCd, rfl⟩))
  -- members are pairwise edge-disjoint
  have hdisj : ∀ M₁ ∈ Cls, ∀ M₂ ∈ Cls, M₁ ≠ M₂ → Disjoint M₁ M₂ := by
    intro M₁ hM₁ M₂ hM₂ hne
    dsimp [Cls] at hM₁ hM₂
    rcases Finset.mem_union.mp hM₁ with hk₁ | hb₁
    · rcases Finset.mem_image.mp hk₁ with ⟨c₁, hc₁, hEq₁⟩
      rcases Finset.mem_union.mp hM₂ with hk₂ | hb₂
      · -- kept vs kept
        rcases Finset.mem_image.mp hk₂ with ⟨c₂, _hc₂, hEq₂⟩
        have hne' : c₁ ≠ c₂ := by
          intro hcc
          apply hne
          rw [← hEq₁, ← hEq₂, hcc]
        rw [← hEq₁, ← hEq₂]
        exact colorClassFamily_disjoint φ hne'
      · -- kept vs big piece
        rcases Finset.mem_biUnion.mp hb₂ with ⟨c₂, hc₂, hM₂⟩
        have hne' : c₁ ≠ c₂ := by
          intro hcc
          have hc1n : c₁ ∉ C' := (Finset.mem_sdiff.mp hc₁).2
          exact hc1n (by simpa [hcc] using hc₂)
        rw [← hEq₁]
        exact disjoint_of_subset_disjoint (by intro x hx; exact hx)
          ((hsplit c₂).1 M₂ hM₂) (colorClassFamily_disjoint φ hne')
    · rcases Finset.mem_biUnion.mp hb₁ with ⟨c₁, hc₁, hM₁⟩
      rcases Finset.mem_union.mp hM₂ with hk₂ | hb₂
      · -- big piece vs kept
        rcases Finset.mem_image.mp hk₂ with ⟨c₂, hc₂, hEq₂⟩
        have hne' : c₁ ≠ c₂ := by
          intro hcc
          have hc2n : c₂ ∉ C' := (Finset.mem_sdiff.mp hc₂).2
          exact hc2n (by simpa [← hcc] using hc₁)
        rw [← hEq₂]
        exact disjoint_of_subset_disjoint ((hsplit c₁).1 M₁ hM₁)
          (by intro x hx; exact hx) (colorClassFamily_disjoint φ hne')
      · -- big piece vs big piece
        rcases Finset.mem_biUnion.mp hb₂ with ⟨c₂, hc₂, hM₂⟩
        by_cases hcc : c₁ = c₂
        · subst c₂
          exact splitPieces_disjoint c₁ φ (Pfun c₁) (hsplit c₁).1 (hsplit c₁).2.2.1 M₁ hM₁ M₂ hM₂ hne
        · exact disjoint_of_subset_disjoint ((hsplit c₁).1 M₁ hM₁)
            ((hsplit c₂).1 M₂ hM₂) (colorClassFamily_disjoint φ hcc)
  -- every member is β-bounded
  have hbdd : ∀ M ∈ Cls, FamilyBounded β M := by
    intro M hM
    dsimp [Cls] at hM
    rcases Finset.mem_union.mp hM with hk | hb
    · rcases Finset.mem_image.mp hk with ⟨c, hc, hEq⟩
      -- kept small class: covers < βn/2 ≤ βn
      have hcnot : c ∉ C' := (Finset.mem_sdiff.mp hc).2
      have hcC : c ∈ C := (Finset.mem_sdiff.mp hc).1
      have hnotbig : ¬ big c := by
        intro hb
        exact hcnot (by simpa [C', big] using (Finset.mem_filter.mpr ⟨hcC, hb⟩))
      have hlt : (φ.classVertexCount c : ℝ) < (β / 2 : ℝ) * (n : ℝ) := by
        exact lt_of_not_ge hnotbig
      right
      have hFVC : FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) = φ.classVertexCount c :=
        (classVertexCount_eq_FamilyVertexCount φ c).symm
      have hFVC' : (FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) : ℝ) =
          (φ.classVertexCount c : ℝ) := by
        exact_mod_cast hFVC
      rw [← hEq]
      rw [hFVC']
      have hhalf : (β / 2 : ℝ) * (n : ℝ) ≤ β * (n : ℝ) := by nlinarith [hβ]
      exact le_of_lt (hlt.trans_le hhalf)
    · rcases Finset.mem_biUnion.mp hb with ⟨c, _hc, hM⟩
      -- piece of a split big class
      have hok := SplitPieceOK_half_strict (β := β) (n := n) h2βn ((hsplit c).2.1 M hM)
      rcases hok with hOne | hBdd
      · left
        omega
      · right
        exact hBdd
  -- the colouring
  rcases colouringOfFamilies_fin_AlphaBounded (Cls := Cls) β hmat hcov hdisj hin hbdd with ⟨ψ, hbddψ⟩
  -- the colour count
  have hA : 0 ≤ (2 : ℝ) / (β / 2) + 1 := by positivity
  have hC'le : ((C'.card : ℕ) : ℝ) ≤ (n : ℝ) / ((β / 2 : ℝ) * (r : ℝ)) := by
    let Cuniv : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter big
    have hsubC : C' ⊆ Cuniv := by
      intro c hc
      exact Finset.mem_filter.mpr ⟨by simp, by simpa [C', big] using (Finset.mem_filter.mp hc).2⟩
    have hcard : ((C'.card : ℕ) : ℝ) ≤ ((Cuniv.card : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsubC)
    have hbig : ((Cuniv.card : ℕ) : ℝ) ≤ (n : ℝ) / ((β / 2 : ℝ) * (r : ℝ)) := by
      simpa [Cuniv, big] using
        (card_bigColourClasses_le (h2n := h2n) (hα := hβ2) (hr := hr) (𝓗 := 𝓗)
          (hlin := hlin) (hbig := hsize) (φ := φ))
    exact hcard.trans hbig
  have hpiecesSum : (C'.sum fun c : Fin n => ((Pfun c).card : ℝ)) ≤
      (((C'.card : ℕ) : ℝ) * ((2 : ℝ) / (β / 2) + 1)) := by
    have hper : ∀ c ∈ C', ((Pfun c).card : ℝ) ≤ (2 : ℝ) / (β / 2) + 1 := by
      intro c _hc
      exact (hsplit c).2.2.2
    calc
      C'.sum (fun c : Fin n => ((Pfun c).card : ℝ))
          ≤ C'.sum (fun _c : Fin n => (2 : ℝ) / (β / 2) + 1) :=
            Finset.sum_le_sum hper
      _ = ((C'.card : ℕ) : ℝ) * ((2 : ℝ) / (β / 2) + 1) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
  have hbigPiecesCard : (bigPieces.card : ℝ) ≤
      ((C'.card : ℕ) : ℝ) * ((2 : ℝ) / (β / 2) + 1) := by
    have hnat : bigPieces.card ≤ C'.sum (fun c : Fin n => (Pfun c).card) := by
      simpa [bigPieces] using (Finset.card_biUnion_le (s := C') (t := Pfun))
    have hcast : (bigPieces.card : ℝ) ≤
        ((C'.sum (fun c : Fin n => (Pfun c).card) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    calc
      (bigPieces.card : ℝ) ≤ ((C'.sum (fun c : Fin n => (Pfun c).card) : ℕ) : ℝ) := hcast
      _ = C'.sum (fun c : Fin n => ((Pfun c).card : ℝ)) := by
          rw [Nat.cast_sum]
      _ ≤ ((C'.card : ℕ) : ℝ) * ((2 : ℝ) / (β / 2) + 1) := hpiecesSum
  have hkeptCard : (kept.card : ℝ) ≤ (C.card : ℝ) := by
    have h1 : kept.card ≤ (C \ C').card := by
      simpa [kept] using
        (Finset.card_image_le (s := C \ C') (f := fun c : Fin n => EdgeSetFamily (φ.colorClass c)))
    have h2 : (C \ C').card ≤ C.card := Finset.card_le_card (by
      intro c hc
      exact (Finset.mem_sdiff.mp hc).1)
    have h3 : (kept.card : ℝ) ≤ ((C \ C').card : ℝ) := by exact_mod_cast h1
    have h4 : ((C \ C').card : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast h2
    exact h3.trans h4
  have hClsCard : ((Cls.card : ℕ) : ℝ) ≤ (C.card : ℝ) +
      (((C'.card : ℕ) : ℝ) * ((2 : ℝ) / (β / 2) + 1)) := by
    have h1 : Cls.card ≤ kept.card + bigPieces.card := by
      dsimp [Cls]
      exact Finset.card_union_le kept bigPieces
    have h2 : ((Cls.card : ℕ) : ℝ) ≤ ((kept.card : ℕ) : ℝ) + (bigPieces.card : ℝ) := by
      have hc : ((Cls.card : ℕ) : ℝ) ≤ (((kept.card + bigPieces.card : ℕ)) : ℝ) := by
        exact_mod_cast h1
      simpa [Nat.cast_add] using hc
    have h3 : ((kept.card : ℕ) : ℝ) + (bigPieces.card : ℝ) ≤
        (C.card : ℝ) + (((C'.card : ℕ) : ℝ) * ((2 : ℝ) / (β / 2) + 1)) := by
      nlinarith [hkeptCard, hbigPiecesCard]
    exact h2.trans h3
  have hClsCard2 : ((Cls.card : ℕ) : ℝ) ≤ (C.card : ℝ) +
      ((2 : ℝ) / (β / 2) + 1) * ((n : ℝ) / ((β / 2 : ℝ) * (r : ℝ))) := by
    have h1 := hClsCard
    have hmul : (((C'.card : ℕ) : ℝ) * ((2 : ℝ) / (β / 2) + 1)) ≤
        ((2 : ℝ) / (β / 2) + 1) * ((n : ℝ) / ((β / 2 : ℝ) * (r : ℝ))) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hC'le hA
    nlinarith
  refine ⟨Cls.card, ψ, hbddψ, ?_⟩
  simpa using hClsCard2
