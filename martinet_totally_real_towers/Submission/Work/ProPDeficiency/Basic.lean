import Mathlib

/-!
# Pro-`p` deficiency theory: generators, presentations, deficiency

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.Basic`.

This is the discrete (no profinite cohomology) setting of the group theory that turns a
"number of generators / number of relations" count into a proof of infinitude.

## Main definitions

* `IsGeneratingSet S` : the finset `S` generates the group;
* `IsMinimalGeneratingSet S` : `S` generates and has minimal cardinality among generating finsets;
* `dGens G` : the minimal cardinality of a finite generating set of `G` (`0` if `G` is not
  finitely generated, by the `sInf` convention);
* `IsPresentation α rel G` : `G` is isomorphic to the quotient of the free group on `α` by the
  normal closure of the finite relator set `rel`;
* `HasMinimalPresentation α rel G` : `IsPresentation α rel G` and `α` is a *minimal* generating
  set of `G`;
* `IsMinimalRelatorSet α G rel` : `rel` presents `G` on `α` with the least possible number of
  relators;
* `relRank α G` : the minimal cardinality of a relator set presenting `G` on `α`;
* `Deficiency d r u` : `r + u ≤ d`, i.e. a presentation with `d` generators and `r` relators has
  deficiency at least `u`;
* `HasPresentation G d r`, `HasDeficiency G u` : the corresponding existential statements.

## Conventions

`dGens` and `relRank` are `sInf`-based (no `Nat.find` existence proofs are needed, and the
"not finitely generated" case degenerates to `0`, which is always a correct lower bound: every
statement that uses `dGens` as a lower bound produces a generating set first).  The generator type
of `IsPresentation` is a `Type` with explicit `Fintype`/`DecidableEq` requirements where they are
needed, and presentations are `Nonempty (G ≃* ...)`-valued, never `FreeGroup.lift`-based data.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ProPDeficiency

variable {G H : Type*}

/-! ## Generators -/

/-- A finset `S` **generates** the group `G`. -/
def IsGeneratingSet [Group G] (S : Finset G) : Prop :=
  Subgroup.closure (S : Set G) = ⊤

/-- A finset `S` is a **minimal generating set** of `G`: it generates `G` and no generating finset
has smaller cardinality. -/
def IsMinimalGeneratingSet [Group G] (S : Finset G) : Prop :=
  IsGeneratingSet S ∧ ∀ T : Finset G, IsGeneratingSet T → S.card ≤ T.card

theorem isGeneratingSet_iff [Group G] (S : Finset G) :
    IsGeneratingSet S ↔ Subgroup.closure (S : Set G) = ⊤ := Iff.rfl

theorem IsMinimalGeneratingSet.isGeneratingSet [Group G] {S : Finset G}
    (h : IsMinimalGeneratingSet S) : IsGeneratingSet S := h.1

theorem IsMinimalGeneratingSet.card_le [Group G] {S T : Finset G}
    (h : IsMinimalGeneratingSet S) (hT : IsGeneratingSet T) : S.card ≤ T.card := h.2 T hT

/-- The **minimal number of generators** `dGens G` of a group `G`: the least cardinality of a
finite generating set.  If `G` has no finite generating set this is `0` (the `sInf` convention). -/
noncomputable def dGens (G : Type*) [Group G] : ℕ :=
  sInf {n : ℕ | ∃ S : Finset G, S.card = n ∧ IsGeneratingSet S}

theorem dGens_le_card [Group G] {S : Finset G} (hS : IsGeneratingSet S) : dGens G ≤ S.card :=
  Nat.sInf_le ⟨S, rfl, hS⟩

/-- A generating set witnessing `dGens G`, given that some finite generating set exists. -/
theorem exists_generatingSet_card_dGens [Group G]
    (h : ∃ S : Finset G, IsGeneratingSet S) :
    ∃ S : Finset G, IsGeneratingSet S ∧ S.card = dGens G := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨T, hTcard, hTgen⟩ :=
    Nat.sInf_mem (s := {n : ℕ | ∃ S : Finset G, S.card = n ∧ IsGeneratingSet S})
      ⟨S.card, S, rfl, hS⟩
  exact ⟨T, hTgen, hTcard⟩

theorem IsMinimalGeneratingSet.dGens_eq [Group G] {S : Finset G}
    (hS : IsMinimalGeneratingSet S) : dGens G = S.card := by
  refine le_antisymm (dGens_le_card hS.isGeneratingSet) ?_
  obtain ⟨T, hTgen, hTcard⟩ := exists_generatingSet_card_dGens ⟨S, hS.isGeneratingSet⟩
  rw [← hTcard]
  exact hS.card_le hTgen

/-- A finitely generated group has a minimal generating set, of cardinality `dGens G`. -/
theorem exists_minimalGeneratingSet [Group G] (hG : Group.FG G) :
    ∃ S : Finset G, IsMinimalGeneratingSet S ∧ S.card = dGens G := by
  obtain ⟨n, S, hn, hSgen⟩ := Group.fg_iff'.mp hG
  obtain ⟨T, hTgen, hTcard⟩ := exists_generatingSet_card_dGens ⟨S, hSgen⟩
  exact ⟨T, ⟨hTgen, fun U hU => by rw [hTcard]; exact Nat.sInf_le ⟨U, rfl, hU⟩⟩, hTcard⟩

/-- `dGens G = n` is characterised by "`n` is realised by a generating set, and every generating
set has at least `n` elements". -/
theorem dGens_eq_of [Group G] {n : ℕ} (hex : ∃ S : Finset G, IsGeneratingSet S ∧ S.card = n)
    (hmin : ∀ S : Finset G, IsGeneratingSet S → n ≤ S.card) : dGens G = n := by
  obtain ⟨S₀, hS₀gen, hS₀card⟩ := hex
  refine le_antisymm ?_ ?_
  · rw [← hS₀card]
    exact dGens_le_card hS₀gen
  · obtain ⟨T, hTgen, hTcard⟩ := exists_generatingSet_card_dGens ⟨S₀, hS₀gen⟩
    rw [← hTcard]
    exact hmin T hTgen

theorem dGens_of_subsingleton [Group G] [Subsingleton G] : dGens G = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine dGens_le_card (S := ∅) ?_
  rw [isGeneratingSet_iff]
  refine eq_top_iff.mpr fun x _ => ?_
  rw [Subsingleton.elim x 1]
  exact Subgroup.one_mem _

theorem dGens_eq_zero_iff_subsingleton [Group G] (hG : Group.FG G) :
    dGens G = 0 ↔ Subsingleton G := by
  constructor
  · intro h
    obtain ⟨S, hS, hcard⟩ := exists_minimalGeneratingSet hG
    rw [h, Finset.card_eq_zero] at hcard
    refine ⟨fun x y => ?_⟩
    have htop : (⊤ : Subgroup G) = ⊥ := by
      rw [← hS.isGeneratingSet, hcard, Finset.coe_empty, Subgroup.closure_empty]
    have hx : x ∈ (⊥ : Subgroup G) := by rw [← htop]; trivial
    have hy : y ∈ (⊥ : Subgroup G) := by rw [← htop]; trivial
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  · intro h
    haveI := h
    exact dGens_of_subsingleton

theorem nontrivial_iff_dGens_pos [Group G] (hG : Group.FG G) :
    Nontrivial G ↔ 0 < dGens G := by
  rw [← not_subsingleton_iff_nontrivial, ← dGens_eq_zero_iff_subsingleton hG, Nat.pos_iff_ne_zero,
    ne_eq]

/-- The minimal number of generators does not increase under a surjective homomorphism. -/
theorem dGens_le_of_surjective [Group G] [Group H] (hG : Group.FG G) (f : G →* H)
    (hf : Function.Surjective f) : dGens H ≤ dGens G := by
  classical
  obtain ⟨S, hS, hcard⟩ := exists_minimalGeneratingSet hG
  have hgen : IsGeneratingSet (S.image f) := by
    rw [isGeneratingSet_iff, show ((S.image f : Finset H) : Set H) = f '' (S : Set G) from
      Finset.coe_image, ← MonoidHom.map_closure f (S : Set G), hS.isGeneratingSet,
      Subgroup.map_top_of_surjective _ hf]
  calc dGens H ≤ (S.image f).card := dGens_le_card hgen
    _ ≤ S.card := Finset.card_image_le
    _ = dGens G := hcard

/-- `dGens` of a quotient group is at most `dGens` of the group. -/
theorem dGens_quotient_le [Group G] (hG : Group.FG G) (N : Subgroup G) [N.Normal] :
    dGens (G ⧸ N) ≤ dGens G :=
  dGens_le_of_surjective hG (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-! ## Presentations and relator rank -/

/-- `IsPresentation α rel G` : `G` is presented by the generator type `α` and the finite relator
set `rel`, i.e. `G ≃* FreeGroup α ⧸ normalClosure rel`. -/
def IsPresentation (α : Type*) (rel : Finset (FreeGroup α)) (G : Type*) [Group G] : Prop :=
  Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α)))

theorem IsPresentation.refl (α : Type*) (rel : Finset (FreeGroup α)) :
    IsPresentation α rel (FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) :=
  ⟨MulEquiv.refl _⟩

theorem IsPresentation.of_mulEquiv {α : Type*} {rel : Finset (FreeGroup α)} {G H : Type*}
    [Group G] [Group H] (h : IsPresentation α rel G) (e : H ≃* G) : IsPresentation α rel H :=
  h.map fun f => e.trans f

/-- If `f : F →* G` is surjective and `S` generates `F`, then `f '' S` generates `G`. -/
theorem closure_image_eq_top_of_surjective {F₀ G₀ : Type*} [Group F₀] [Group G₀] (f : F₀ →* G₀)
    (hf : Function.Surjective f) {S : Set F₀} (hS : Subgroup.closure S = ⊤) :
    Subgroup.closure (f '' S) = ⊤ := by
  rw [← MonoidHom.map_closure f S, hS, Subgroup.map_top_of_surjective _ hf]

/-- A group presented by finitely many generators is finitely generated. -/
theorem IsPresentation.groupFG {α : Type} [Fintype α] {rel : Finset (FreeGroup α)} {G : Type}
    [Group G] (h : IsPresentation α rel G) : Group.FG G := by
  obtain ⟨e⟩ := h
  exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The `α`-generators of a presentation generate `G` on at most `Fintype.card α` elements, hence
`dGens G ≤ Fintype.card α`. -/
theorem dGens_le_card_of_presentation {α : Type*} [Fintype α] {rel : Finset (FreeGroup α)}
    {G : Type*} [Group G]
    (e : G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) :
    dGens G ≤ Fintype.card α := by
  classical
  set g : α → G := fun a =>
    e.symm (QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α)))
      (FreeGroup.of a)) with hgdef
  have hclos : Subgroup.closure (Set.range g) = ⊤ := by
    have hrange : Set.range g = (fun x => e.symm (QuotientGroup.mk'
        (Subgroup.normalClosure (rel : Set (FreeGroup α))) x))
        '' Set.range (FreeGroup.of : α → FreeGroup α) := by
      rw [hgdef]
      exact Set.range_comp' (fun x => e.symm (QuotientGroup.mk'
        (Subgroup.normalClosure (rel : Set (FreeGroup α))) x)) (FreeGroup.of)
    have h1 := closure_image_eq_top_of_surjective
      (((e.symm : _ →* G)).comp (QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α)))))
      (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) (FreeGroup.closure_range_of α)
    rw [hrange]
    exact h1
  have hgen : IsGeneratingSet (Finset.univ.image g) := by
    rw [isGeneratingSet_iff]
    have : ((Finset.univ.image g : Finset G) : Set G) = Set.range g := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [this, hclos]
  calc dGens G ≤ (Finset.univ.image g).card := dGens_le_card hgen
    _ ≤ Fintype.card α := Finset.card_image_le

theorem IsPresentation.dGens_le_card {α : Type*} [Fintype α] {rel : Finset (FreeGroup α)}
    {G : Type*} [Group G] (h : IsPresentation α rel G) : dGens G ≤ Fintype.card α := by
  obtain ⟨e⟩ := h
  exact dGens_le_card_of_presentation e

/-- `HasMinimalPresentation α rel G` : `α` presents `G` (with relators `rel`) and `α` is a
*minimal* generating set: every finite generating set of `G` has at least `Fintype.card α`
elements. -/
def HasMinimalPresentation (α : Type*) [Fintype α] (rel : Finset (FreeGroup α))
    (G : Type*) [Group G] : Prop :=
  IsPresentation α rel G ∧ ∀ S : Finset G, IsGeneratingSet S → Fintype.card α ≤ S.card

theorem HasMinimalPresentation.dGens_eq {α : Type*} [Fintype α] {rel : Finset (FreeGroup α)}
    {G : Type*} [Group G] (h : HasMinimalPresentation α rel G) :
    dGens G = Fintype.card α := by
  classical
  obtain ⟨e⟩ := h.1
  refine le_antisymm (dGens_le_card_of_presentation e) ?_
  set g : α → G := fun a =>
    e.symm (QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α)))
      (FreeGroup.of a)) with hgdef
  have hclos : Subgroup.closure (Set.range g) = ⊤ := by
    have hrange : Set.range g = (fun x => e.symm (QuotientGroup.mk'
        (Subgroup.normalClosure (rel : Set (FreeGroup α))) x))
        '' Set.range (FreeGroup.of : α → FreeGroup α) := by
      rw [hgdef]
      exact Set.range_comp' (fun x => e.symm (QuotientGroup.mk'
        (Subgroup.normalClosure (rel : Set (FreeGroup α))) x)) (FreeGroup.of)
    have h1 := closure_image_eq_top_of_surjective
      (((e.symm : _ →* G)).comp (QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α)))))
      (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) (FreeGroup.closure_range_of α)
    rw [hrange]
    exact h1
  have hgen : IsGeneratingSet (Finset.univ.image g) := by
    rw [isGeneratingSet_iff]
    have : ((Finset.univ.image g : Finset G) : Set G) = Set.range g := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [this, hclos]
  obtain ⟨T, hTgen, hTcard⟩ := exists_generatingSet_card_dGens ⟨Finset.univ.image g, hgen⟩
  rw [← hTcard]
  exact h.2 T hTgen

/-- `IsMinimalRelatorSet α G rel` : `rel` presents `G` on the generator set `α` with the least
possible number of relators. -/
def IsMinimalRelatorSet (α : Type*) (G : Type*) [Group G] (rel : Finset (FreeGroup α)) : Prop :=
  IsPresentation α rel G ∧
    ∀ rel' : Finset (FreeGroup α), IsPresentation α rel' G → rel.card ≤ rel'.card

/-- The **relator rank** of `G` on the fixed generator type `α`: the minimal cardinality of a
relator set presenting `G` on `α` (`0` if no finite relator set presents `G` on `α`). -/
noncomputable def relRank (α : Type*) (G : Type*) [Group G] : ℕ :=
  sInf {r : ℕ | ∃ rel : Finset (FreeGroup α), rel.card = r ∧ IsPresentation α rel G}

theorem relRank_le {α : Type*} {G : Type*} [Group G] {rel : Finset (FreeGroup α)}
    (h : IsPresentation α rel G) : relRank α G ≤ rel.card :=
  Nat.sInf_le ⟨rel, rfl, h⟩

theorem IsMinimalRelatorSet.relRank_eq {α : Type*} {G : Type*} [Group G]
    {rel : Finset (FreeGroup α)} (h : IsMinimalRelatorSet α G rel) :
    relRank α G = rel.card := by
  refine le_antisymm (relRank_le h.1) ?_
  obtain ⟨r, hrcard, hr⟩ := Nat.sInf_mem (s := {r : ℕ | ∃ rel : Finset (FreeGroup α),
    rel.card = r ∧ IsPresentation α rel G}) ⟨rel.card, rel, rfl, h.1⟩
  exact le_trans (h.2 _ hr) (le_of_eq hrcard)

/-! ## The deficiency formalism -/

/-- **Deficiency.**  A presentation with `d` generators and `r` relators has deficiency at least
`u` when `r + u ≤ d` (equivalently `u ≤ d - r`).  Deficiency increases with `u`. -/
def Deficiency (d r : ℕ) (u : ℤ) : Prop := (r : ℤ) + u ≤ (d : ℤ)

theorem Deficiency.mono {d r : ℕ} {u u' : ℤ} (h : Deficiency d r u) (hu : u' ≤ u) :
    Deficiency d r u' := by
  simp only [Deficiency] at h ⊢
  linarith

theorem deficiency_iff {d r : ℕ} {u : ℤ} : Deficiency d r u ↔ u ≤ (d : ℤ) - (r : ℤ) := by
  simp only [Deficiency]
  constructor <;> intro h <;> linarith

theorem Deficiency.zero_iff {d r : ℕ} : Deficiency d r 0 ↔ r ≤ d := by
  simp [Deficiency, Nat.cast_le]

theorem Deficiency.neg_one_iff {d r : ℕ} : Deficiency d r (-1) ↔ r ≤ d + 1 := by
  rw [deficiency_iff]
  constructor <;> intro h <;> omega

theorem Deficiency.of_le {d r : ℕ} (h : r ≤ d) : Deficiency d r 0 := Deficiency.zero_iff.mpr h

theorem Deficiency.of_le_add_one {d r : ℕ} (h : r ≤ d + 1) : Deficiency d r (-1) :=
  Deficiency.neg_one_iff.mpr h

/-- Adding `k` free generators to a presentation does not change its deficiency. -/
theorem Deficiency.add_generators {d r : ℕ} {u : ℤ} (h : Deficiency d r u) (k : ℕ) :
    Deficiency (d + k) r (u + k) := by
  simp only [Deficiency] at h ⊢
  push_cast
  linarith

/-- `HasPresentation G d r` : `G` admits a presentation with `d` generators and `r` relators. -/
def HasPresentation (G : Type*) [Group G] (d r : ℕ) : Prop :=
  ∃ (α : Type) (_ : Fintype α) (rel : Finset (FreeGroup α)),
    Fintype.card α = d ∧ rel.card = r ∧ IsPresentation α rel G

/-- `HasDeficiency G u` : `G` admits a presentation of deficiency at least `u`. -/
def HasDeficiency (G : Type*) [Group G] (u : ℤ) : Prop :=
  ∃ d r : ℕ, HasPresentation G d r ∧ Deficiency d r u

theorem HasDeficiency.mono {G : Type*} [Group G] {u u' : ℤ} (h : HasDeficiency G u)
    (hu : u' ≤ u) : HasDeficiency G u' := by
  obtain ⟨d, r, hp, hd⟩ := h
  exact ⟨d, r, hp, hd.mono hu⟩

theorem HasDeficiency.of_presentation {G : Type*} [Group G] {d r : ℕ}
    (h : HasPresentation G d r) {u : ℤ} (hu : Deficiency d r u) : HasDeficiency G u :=
  ⟨d, r, h, hu⟩

theorem HasPresentation.hasDeficiency {G : Type*} [Group G] {d r : ℕ} (h : HasPresentation G d r)
    (hu : r ≤ d) : HasDeficiency G 0 :=
  ⟨d, r, h, Deficiency.of_le hu⟩

theorem HasPresentation.hasDeficiency_neg_one {G : Type*} [Group G] {d r : ℕ}
    (h : HasPresentation G d r) (hu : r ≤ d + 1) : HasDeficiency G (-1) :=
  ⟨d, r, h, Deficiency.of_le_add_one hu⟩

theorem four_mul_le_sq_of_lt {r d : ℕ} (h : r < d) : 4 * r ≤ d * d := by
  have h1 : (4 * r : ℤ) ≤ 4 * ((d : ℤ) - 1) := by
    have : (r : ℤ) + 1 ≤ (d : ℤ) := by exact_mod_cast h
    linarith
  have hdpos : (1 : ℤ) ≤ (d : ℤ) := by
    have h1 : 1 ≤ d :=
      Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) h))
    exact_mod_cast h1
  have h2 : (4 * ((d : ℤ) - 1)) ≤ (d : ℤ) * d := by
    nlinarith [sq_nonneg ((d : ℤ) - 2)]
  have h3 : (4 * r : ℤ) ≤ ((d * d : ℕ) : ℤ) := by push_cast; linarith
  exact_mod_cast h3

/-- A presentation with `d` generators and `r` relators, with `d ≥ 5` and `r ≤ d + 1` (deficiency
at least `-1`), satisfies the Golod--Shafarevich inequality `4 r ≤ d ^ 2`.  This is the numeric
input of the criterion. -/
theorem four_mul_le_sq_of_deficiency {d r : ℕ} (h : Deficiency d r (-1)) (hd : 5 ≤ d) :
    4 * r ≤ d * d := by
  rw [Deficiency.neg_one_iff] at h
  nlinarith [h, hd]

end Work.ProPDeficiency
