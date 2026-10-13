import Mathlib
import Submission.Work.WilC2.BndDefs

set_option autoImplicit false

namespace Work.WilC2

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]

/-- A boundary point lying in `I` is a lower or an upper bound of `I`.

Indeed, if `c < x < d` with `c, d ∈ I`, convexity puts a whole neighbourhood of `x` inside `I`,
contradicting `IsBnd`. -/
lemma bnd_mem_side {I : Set M} (hI : I.OrdConnected) {x : M} (hx : IsBnd I x) (_hxI : x ∈ I) :
    (∀ c ∈ I, x ≤ c) ∨ (∀ c ∈ I, c ≤ x) := by
  by_contra h
  push Not at h
  obtain ⟨⟨c, hcI, hcx⟩, d, hdI, hxd⟩ := h
  refine hx.1 ⟨min (x - c) (d - x), lt_min (by linarith) (by linarith), ?_⟩
  intro t ht
  simp only [Set.mem_Ioo] at ht
  exact hI.out hcI hdI
    ⟨by linarith [ht.1, min_le_left (x - c) (d - x)],
     by linarith [ht.2, min_le_right (x - c) (d - x)]⟩

/-- A boundary point lying outside `I` is a strict lower or a strict upper bound of `I`. -/
lemma bnd_notMem_side {I : Set M} (hI : I.OrdConnected) {x : M} (_hx : IsBnd I x)
    (hxI : x ∉ I) :
    (∀ c ∈ I, x < c) ∨ (∀ c ∈ I, c < x) := by
  by_contra h
  push Not at h
  obtain ⟨⟨c, hcI, hcx⟩, d, hdI, hxd⟩ := h
  rcases le_total c d with hcd | hdc
  · exact hxI (hI.out hcI hdI ⟨hcx, hxd⟩)
  · exact hxI (hI.out hdI hcI ⟨hdc.trans hcx, hxd.trans hdc⟩)

/-- There is at most one boundary point that is a strict lower bound of `I`. -/
lemma subsingleton_bnd_lower {I : Set M} :
    ({x : M | IsBnd I x} ∩ {x : M | ∀ c ∈ I, x < c}).Subsingleton := by
  rintro x ⟨hx, hxl⟩ y ⟨hy, hyl⟩
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · refine hx.2 ⟨y - x, by linarith, ?_⟩
    intro t ht
    rw [Set.mem_compl_iff]
    intro htI
    have := hyl t htI
    simp only [Set.mem_Ioo] at ht
    linarith [ht.2]
  · refine hy.2 ⟨x - y, by linarith, ?_⟩
    intro t ht
    rw [Set.mem_compl_iff]
    intro htI
    have := hxl t htI
    simp only [Set.mem_Ioo] at ht
    linarith [ht.2]

/-- There is at most one boundary point that is a strict upper bound of `I`. -/
lemma subsingleton_bnd_upper {I : Set M} :
    ({x : M | IsBnd I x} ∩ {x : M | ∀ c ∈ I, c < x}).Subsingleton := by
  rintro x ⟨hx, hxu⟩ y ⟨hy, hyu⟩
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · refine hy.2 ⟨y - x, by linarith, ?_⟩
    intro t ht
    rw [Set.mem_compl_iff]
    intro htI
    have := hxu t htI
    simp only [Set.mem_Ioo] at ht
    linarith [ht.1]
  · refine hx.2 ⟨x - y, by linarith, ?_⟩
    intro t ht
    rw [Set.mem_compl_iff]
    intro htI
    have := hyu t htI
    simp only [Set.mem_Ioo] at ht
    linarith [ht.1]

/-- There is at most one element of `I` that is a lower bound of `I`. -/
lemma subsingleton_mem_lower {I : Set M} :
    {x : M | x ∈ I ∧ ∀ c ∈ I, x ≤ c}.Subsingleton := by
  rintro x ⟨hxI, hxl⟩ y ⟨hyI, hyl⟩
  exact le_antisymm (hxl y hyI) (hyl x hxI)

/-- There is at most one element of `I` that is an upper bound of `I`. -/
lemma subsingleton_mem_upper {I : Set M} :
    {x : M | x ∈ I ∧ ∀ c ∈ I, c ≤ x}.Subsingleton := by
  rintro x ⟨hxI, hxu⟩ y ⟨hyI, hyu⟩
  exact le_antisymm (hyu x hxI) (hxu y hyI)

/-- **An order-convex subset of a linear ordered field has at most two boundary points.** -/
lemma bnd_ordConnected_finite {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {I : Set M} (hI : I.OrdConnected) :
    {x : M | IsBnd I x}.Finite := by
  classical
  have hdecomp :
      {x : M | IsBnd I x} ⊆
        ({x : M | IsBnd I x} ∩ I) ∪
          (({x : M | IsBnd I x} ∩ {x : M | ∀ c ∈ I, x < c}) ∪
            ({x : M | IsBnd I x} ∩ {x : M | ∀ c ∈ I, c < x})) := by
    intro x hx
    rcases em (x ∈ I) with hxI | hxI
    · exact Or.inl ⟨hx, hxI⟩
    · rcases bnd_notMem_side hI hx hxI with h | h
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inr (Or.inr ⟨hx, h⟩)
  refine Set.Finite.subset ?_ hdecomp
  have h1 : ({x : M | IsBnd I x} ∩ I).Finite := by
    refine Set.Finite.subset
      ((subsingleton_mem_lower (I := I)).finite.union (subsingleton_mem_upper (I := I)).finite) ?_
    rintro x ⟨hx, hxI⟩
    rcases bnd_mem_side hI hx hxI with h | h
    · exact Or.inl ⟨hxI, h⟩
    · exact Or.inr ⟨hxI, h⟩
  have h2 : ({x : M | IsBnd I x} ∩ {x : M | ∀ c ∈ I, x < c}).Finite :=
    (subsingleton_bnd_lower (I := I)).finite
  have h3 : ({x : M | IsBnd I x} ∩ {x : M | ∀ c ∈ I, c < x}).Finite :=
    (subsingleton_bnd_upper (I := I)).finite
  exact h1.union (h2.union h3)

end Work.WilC2
