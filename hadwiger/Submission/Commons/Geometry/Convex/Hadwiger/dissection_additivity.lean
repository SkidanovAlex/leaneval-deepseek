import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Body
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Convex.capSequence

open Set Filter Metric
open scoped Topology Classical

namespace Commons.Geometry.Convex.Hadwiger

/-! # Dissection additivity for simple continuous valuations

The main theorem below (`dissection_additivity`) asserts that a *simple*
continuous valuation (vanishing on every convex body with empty interior)
is additive over finite dissections of a convex body into convex pieces with
pairwise empty-interior intersections.

The proof follows Groemer's extension theorem for valuations on convex
bodies (see also R. Schneider, "Valuations on convex bodies", Chapter 1 of
*Tensor Valuations and their Applications*, Thm 1.21 and 1.7, and
H. Groemer, Pacific J. Math. 75 (1978) 397–410).  It proceeds by a
minimal-counterexample argument over *dissections*:

1. (`val_eq_of_set_eq`) an inclusion–exclusion additive function depends only
   on the underlying set of a convex body.
2. (two-piece additivity) a *simple* valuation is additive over a two-piece
   dissection of a convex body along an empty-interior intersection
   (`simple_additive_two_piece`).
3. (hyperplane cuts) cutting a convex body by a closed halfspace preserves
   all the relevant structure (`cutBody`, weak additivity).
4. (main descent) assuming a counterexample dissection `P = ∪ᵢ Aᵢ` with the
   *minimal* number of pieces, one cuts by a hyperplane keeping the first
   piece strictly on one side; the discrepancy `φ P − ∑ᵢ φ (Aᵢ)` passes to
   the sub-dissection on the other side.  Squeezing with a decreasing family
   of halfspace caps whose intersection is exactly the first piece (a
   standard support-hyperplane fact) and invoking continuity shows the
   discrepancy is unchanged when every piece is replaced by its intersection
   with the first piece.  Repeating with `A₁ ∩ A₂`, … collapses the
   dissection to a single convex set (the common intersection, of empty
   interior, where simplicity forces the value to vanish), a contradiction.
-/

/-- The value of an inclusion–exclusion additive `φ` on a convex body depends
only on its underlying set. -/
theorem val_eq_of_set_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    {A B : ConvexBody V} (hAB : (A : Set V) = (B : Set V)) : φ A = φ B := by
  have hU : (A : Set V) = (A : Set V) ∪ (A : Set V) := by ext x; simp
  have hI : (B : Set V) = (A : Set V) ∩ (A : Set V) := by
    rw [hAB]
    ext x; simp
  have h := hadd A B A A hU hI
  linarith


/-! ## Elementary convex geometry in `V` -/

section BasicGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- A continuous real function on `[0,1]` whose endpoint values bracket `c`
attains `c`. -/
lemma level_cross {g : ℝ → ℝ} (hg : Continuous g) {c : ℝ}
    (hbracket : (g 0 ≤ c ∧ c ≤ g 1) ∨ (g 1 ≤ c ∧ c ≤ g 0)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, g t = c := by
  rcases hbracket with ⟨hlo, hhi⟩ | ⟨hhi, hlo⟩
  · have him := intermediate_value_Icc (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) ≤ 1)
      (f := g) (by simpa using hg.continuousOn)
    have hc : c ∈ Set.Icc (g 0) (g 1) := ⟨hlo, hhi⟩
    exact him hc
  · let g' : ℝ → ℝ := fun t => g (1 - t)
    have hg'_cont : Continuous g' := by
      dsimp [g']
      fun_prop
    have him := intermediate_value_Icc (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) ≤ 1)
      (f := g') (by simpa using hg'_cont.continuousOn)
    have hc' : c ∈ Set.Icc (g' 0) (g' 1) := by
      exact ⟨by simpa [g'] using hhi, by simpa [g'] using hlo⟩
    rcases him hc' with ⟨t, ht, hgt⟩
    refine ⟨1 - t, ?_, ?_⟩
    · have hA : 0 ≤ 1 - t := by linarith [ht.2]
      have hB : 1 - t ≤ 1 := by linarith [ht.1]
      exact ⟨hA, hB⟩
    · dsimp [g'] at hgt
      simpa [g'] using hgt

/-- A convex set meeting both open sides of a level hyperplane of a linear
functional meets the hyperplane itself. -/
lemma convex_meets_level_of_crosses
    {X : Set V} (hX : Convex ℝ X) {u : V} {c : ℝ} {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) (hx_gt : c < inner ℝ u x) (hy_lt : inner ℝ u y < c) :
    ∃ z ∈ X, inner ℝ u z = c := by
  let f : ℝ → V := fun t => x + t • (y - x)
  let g : ℝ → ℝ := fun t => inner ℝ u (f t)
  have hg_cont : Continuous g := by
    dsimp [g, f]
    fun_prop
  have hbracket : (g 0 ≤ c ∧ c ≤ g 1) ∨ (g 1 ≤ c ∧ c ≤ g 0) := by
    right
    constructor
    · have : g 1 = inner ℝ u y := by simp [g, f]
      rw [this]
      exact le_of_lt hy_lt
    · have : g 0 = inner ℝ u x := by simp [g, f]
      rw [this]
      exact le_of_lt hx_gt
  rcases level_cross hg_cont hbracket with ⟨t, ht, ht_eq⟩
  refine ⟨f t, ?_, ?_⟩
  · exact Convex.add_smul_sub_mem hX hx hy ht
  · simpa [g] using ht_eq

/-- Two nonempty disjoint compact convex sets cannot have a convex union. -/
lemma not_convex_union_of_disjoint_nonempty_conv
    {C D : Set V} (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hC_cpt : IsCompact C) (hD_cpt : IsCompact D)
    (hC_ne : C.Nonempty) (hD_ne : D.Nonempty) (hdisj : Disjoint C D) :
    ¬ Convex ℝ (C ∪ D) := by
  intro hconvex
  have hpre : IsPreconnected (C ∪ D) := hconvex.isPreconnected
  have hclosedC : IsClosed C := hC_cpt.isClosed
  have hclosedD : IsClosed D := hD_cpt.isClosed
  have hsub : C ∪ D ⊆ C ∪ D := subset_rfl
  rcases hC_ne with ⟨x, hxC⟩
  rcases hD_ne with ⟨y, hyD⟩
  have hCint : ((C ∪ D) ∩ C).Nonempty := ⟨x, ⟨Or.inl hxC, hxC⟩⟩
  have hDint : ((C ∪ D) ∩ D).Nonempty := ⟨y, ⟨Or.inr hyD, hyD⟩⟩
  have hCD : ((C ∪ D) ∩ (C ∩ D)).Nonempty :=
    (isPreconnected_closed_iff.mp hpre) C D hclosedC hclosedD hsub hCint hDint
  have hdisj' : C ∩ D = ∅ := hdisj.inter_eq
  have hsubempty : ((C ∪ D) ∩ (C ∩ D)) = ∅ := by
    apply subset_antisymm
    · simpa [hdisj'] using (inter_subset_right (s := C ∪ D) (t := C ∩ D))
    · simp
  exact (by simpa [hsubempty] using hCD)

/-- If a convex body does not meet the cutting hyperplane then it lies on one
side of it. -/
lemma body_subset_one_side_of_not_mem_level {X : Set V} (hX : Convex ℝ X)
    {u : V} {c : ℝ}
    (hnot : X ∩ {x | inner ℝ u x = c} = ∅) :
    X ⊆ {x | c ≤ inner ℝ u x} ∨ X ⊆ {x | inner ℝ u x ≤ c} := by
  by_contra h
  push_neg at h
  rcases h with ⟨hnot1, hnot2⟩
  have hx : ∃ x ∈ X, ¬ c ≤ inner ℝ u x := by
    simpa [Set.subset_def] using hnot1
  have hy : ∃ y ∈ X, ¬ inner ℝ u y ≤ c := by
    simpa [Set.subset_def] using hnot2
  rcases hx with ⟨x, hxX, hxlt⟩
  rcases hy with ⟨y, hyX, hygt⟩
  have hx_gt : inner ℝ u x < c := lt_of_not_ge hxlt
  have hy_lt : c < inner ℝ u y := lt_of_not_ge hygt
  rcases convex_meets_level_of_crosses hX (x := y) (y := x) hyX hxX hy_lt hx_gt with ⟨z, hzX, hzmid⟩
  have hzmem : z ∈ X ∩ {x | inner ℝ u x = c} := ⟨hzX, hzmid⟩
  have hzempty : z ∈ (∅ : Set V) := by
    simpa [hnot] using hzmem
  exact hzempty

end BasicGeometry

/-! ## Halfspace cuts of convex bodies -/

section Halfspace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- The closed upper halfspace `{inner u · ≥ c}` intersected with a set. -/
def upperCut (S : Set V) (u : V) (c : ℝ) : Set V := S ∩ {x | c ≤ inner ℝ u x}

/-- The closed lower halfspace `{inner u · ≤ c}` intersected with a set. -/
def lowerCut (S : Set V) (u : V) (c : ℝ) : Set V := S ∩ {x | inner ℝ u x ≤ c}

/-- The cutting hyperplane `{inner u · = c}` intersected with a set. -/
def planeCut (S : Set V) (u : V) (c : ℝ) : Set V := S ∩ {x | inner ℝ u x = c}

theorem upperCut_union_lowerCut (S : Set V) (u : V) (c : ℝ) :
    upperCut S u c ∪ lowerCut S u c = S := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx <;> exact hx.1
  · intro hx
    by_cases h : c ≤ inner ℝ u x
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, le_of_lt (lt_of_not_ge h)⟩

theorem upperCut_inter_lowerCut (S : Set V) (u : V) (c : ℝ) :
    upperCut S u c ∩ lowerCut S u c = planeCut S u c := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1.1, le_antisymm hx.2.2 hx.1.2⟩
  · intro hx
    exact ⟨⟨hx.1, hx.2.ge⟩, ⟨hx.1, hx.2.le⟩⟩

theorem isClosed_upperCut (S : Set V) (hS : IsClosed S) (u : V) (c : ℝ) :
    IsClosed (upperCut S u c) := by
  unfold upperCut
  refine hS.inter ?_
  exact isClosed_le (f := fun x : V => c) (g := fun x : V => inner ℝ u x) continuous_const (by fun_prop)

theorem isClosed_lowerCut (S : Set V) (hS : IsClosed S) (u : V) (c : ℝ) :
    IsClosed (lowerCut S u c) := by
  unfold lowerCut
  refine hS.inter ?_
  exact isClosed_le (f := fun x : V => inner ℝ u x) (g := fun x : V => c) (by fun_prop) continuous_const

theorem isClosed_planeCut (S : Set V) (hS : IsClosed S) (u : V) (c : ℝ) :
    IsClosed (planeCut S u c) := by
  unfold planeCut
  refine hS.inter ?_
  exact isClosed_eq (f := fun x : V => inner ℝ u x) (g := fun x : V => c) (by fun_prop) continuous_const

end Halfspace


/-! ## Possibly-empty compact convex sets and the extended valuation -/

section Conv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- A compact convex subset of `V`; possibly empty. -/
structure Conv (V : Type*) [TopologicalSpace V] [AddCommMonoid V] [SMul ℝ V] where
  carrier : Set V
  convex' : Convex ℝ carrier
  isCompact' : IsCompact carrier

namespace Conv

instance : SetLike (Conv V) V where
  coe := Conv.carrier
  coe_injective := by
    intro S T h
    cases S
    cases T
    congr

@[ext]
protected theorem ext {S T : Conv V} (h : (S : Set V) = T) : S = T := SetLike.ext' h

/-- Turn a nonempty compact convex set into a convex body. -/
def toBody (S : Conv V) (h : (S : Set V).Nonempty) : ConvexBody V :=
  ConvexBody.mk (S : Set V) S.convex' S.isCompact' h

/-- The canonical embedding of a convex body into `Conv`. -/
def ofBody (K : ConvexBody V) : Conv V :=
  Conv.mk (K : Set V) K.convex K.isCompact

@[simp] theorem coe_ofBody (K : ConvexBody V) :
    ((ofBody K : Conv V) : Set V) = (K : Set V) := rfl

/-- The empty set, as a compact convex set. -/
def empty : Conv V := Conv.mk ∅ convex_empty isCompact_empty

@[simp] theorem coe_empty : ((empty : Conv V) : Set V) = (∅ : Set V) := rfl

theorem empty_not_nonempty : ¬((empty : Conv V) : Set V).Nonempty := by
  simp

/-- Intersection with a closed convex set. -/
def inter (S : Conv V) (T : Set V) (hT_convex : Convex ℝ T) (hT_closed : IsClosed T) : Conv V :=
  Conv.mk ((S : Set V) ∩ T) (S.convex'.inter hT_convex) (S.isCompact'.inter_right hT_closed)

@[simp] theorem coe_inter (S : Conv V) (T : Set V) (hT_convex : Convex ℝ T) (hT_closed : IsClosed T) :
    ((inter S T hT_convex hT_closed : Conv V) : Set V) = (S : Set V) ∩ T := rfl

/-- Intersection of two `Conv`s as a `Conv`. -/
def ofInter (C D : Conv V) : Conv V :=
  Conv.mk ((C : Set V) ∩ (D : Set V)) (C.convex'.inter D.convex')
    (C.isCompact'.inter_right D.isCompact'.isClosed)

@[simp] theorem coe_ofInter (C D : Conv V) :
    ((ofInter C D : Conv V) : Set V) = (C : Set V) ∩ (D : Set V) := rfl

end Conv

/-- Extend a function on convex bodies to possibly empty compact convex sets by
setting the empty set to zero. -/
noncomputable def val (φ : ConvexBody V → ℝ) (S : Conv V) : ℝ :=
  if h : (S : Set V).Nonempty then φ (Conv.toBody S h) else 0

@[simp] theorem val_empty (φ : ConvexBody V → ℝ) : val φ Conv.empty = 0 := by
  unfold val
  simp

theorem val_ofBody (φ : ConvexBody V → ℝ) (K : ConvexBody V) : val φ (Conv.ofBody K) = φ K := by
  unfold val
  rw [dif_pos (by simpa using K.nonempty)]
  rfl

theorem val_eq_zero_of_not_nonempty (φ : ConvexBody V → ℝ) (S : Conv V)
    (h : ¬(S : Set V).Nonempty) : val φ S = 0 := by
  unfold val
  rw [dif_neg h]

/-- If two convex compact sets have the same underlying set, their `val`s agree:
they give rise to the same convex body (or are both empty). -/
theorem val_eq_of_set_eq_conv (φ : ConvexBody V → ℝ)
    {S T : Conv V} (hST : (S : Set V) = (T : Set V)) : val φ S = val φ T := by
  unfold val
  by_cases hS : (S : Set V).Nonempty
  · rw [dif_pos hS]
    have hT : (T : Set V).Nonempty := by rwa [← hST]
    rw [dif_pos hT]
    congr 1
    apply ConvexBody.ext
    exact hST
  · rw [dif_neg hS]
    have hT : ¬(T : Set V).Nonempty := by
      intro hT
      apply hS
      rwa [hST]
    rw [dif_neg hT]

/-- The inclusion–exclusion law for the extended `val`, with empty sets allowed.
The interesting case where the intersection is empty while both sets are not
cannot occur because the union would then not be convex. -/
theorem val_add
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    {A B C D : Conv V}
    (hA : (A : Set V) = (C : Set V) ∪ (D : Set V))
    (hB : (B : Set V) = (C : Set V) ∩ (D : Set V)) :
    val φ A + val φ B = val φ C + val φ D := by
  by_cases hC : (C : Set V).Nonempty
  · by_cases hD : (D : Set V).Nonempty
    · -- C and D nonempty
      have hBne : (B : Set V).Nonempty := by
        by_contra hBempty
        have hCDne : ¬((C : Set V) ∩ (D : Set V)).Nonempty := by
          intro h
          rcases h with ⟨x, hxC, hxD⟩
          apply hBempty
          refine ⟨x, ?_⟩
          rw [hB]
          exact ⟨hxC, hxD⟩
        have hCDeq : ((C : Set V) ∩ (D : Set V)) = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hCDne
        have hCd : Disjoint (C : Set V) (D : Set V) :=
          Set.disjoint_iff_inter_eq_empty.mpr hCDeq
        have hAconvex : Convex ℝ ((C : Set V) ∪ (D : Set V)) := by
          rw [← hA]
          exact A.convex'
        exact (not_convex_union_of_disjoint_nonempty_conv C.convex' D.convex' C.isCompact' D.isCompact'
          hC hD hCd) hAconvex
      have hAne : (A : Set V).Nonempty := by
        rw [hA]
        rcases hC with ⟨x, hxC⟩
        exact ⟨x, Or.inl hxC⟩
      have hφ : φ (Conv.toBody A hAne) + φ (Conv.toBody B hBne) =
          φ (Conv.toBody C hC) + φ (Conv.toBody D hD) := by
        apply hadd (Conv.toBody A hAne) (Conv.toBody B hBne) (Conv.toBody C hC) (Conv.toBody D hD)
        · exact hA
        · exact hB
      unfold val
      rw [dif_pos hAne, dif_pos hBne, dif_pos hC, dif_pos hD]
      exact hφ
    · -- D empty
      have hDempty : (D : Set V) = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        exact hD
      have hAeqC : (A : Set V) = (C : Set V) := by
        rw [hA, hDempty]
        simp
      have hBeq : (B : Set V) = ∅ := by
        rw [hB, hDempty]
        simp
      have hvalA : val φ A = val φ C := val_eq_of_set_eq_conv φ hAeqC
      have hvalB : val φ B = 0 := by
        apply val_eq_zero_of_not_nonempty
        intro h
        rcases h with ⟨x, hx⟩
        have : x ∈ (∅ : Set V) := by simpa [hBeq] using hx
        exact this
      have hvalD : val φ D = 0 := by
        apply val_eq_zero_of_not_nonempty
        intro h
        rcases h with ⟨x, hx⟩
        have : x ∈ (∅ : Set V) := by simpa [hDempty] using hx
        exact this
      linarith
  · -- C empty
    have hCempty : (C : Set V) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      exact hC
    have hAeqD : (A : Set V) = (D : Set V) := by
      rw [hA, hCempty]
      simp
    have hBeq : (B : Set V) = ∅ := by
      rw [hB, hCempty]
      simp
    have hvalA : val φ A = val φ D := val_eq_of_set_eq_conv φ hAeqD
    have hvalB : val φ B = 0 := by
      apply val_eq_zero_of_not_nonempty
      intro h
      rcases h with ⟨x, hx⟩
      have : x ∈ (∅ : Set V) := by simpa [hBeq] using hx
      exact this
    have hvalC : val φ C = 0 := by
      apply val_eq_zero_of_not_nonempty
      intro h
      rcases h with ⟨x, hx⟩
      have : x ∈ (∅ : Set V) := by simpa [hCempty] using hx
      exact this
    linarith

end Conv


/-! ## Weak additivity along halfspace cuts -/

section WeakAdd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- `{x | c ≤ inner u x}` is convex. -/
lemma convex_hpUpper (u : V) (c : ℝ) : Convex ℝ {x : V | c ≤ inner ℝ u x} := by
  have hlin : IsLinearMap ℝ (fun x : V => inner ℝ u x) := by
    refine IsLinearMap.mk ?_ ?_
    · intro x y
      exact inner_add_right u x y
    · intro r x
      rw [inner_smul_right]
      simp
  convert (convex_Ici (𝕜 := ℝ) c).is_linear_preimage hlin using 1
  ext x
  simp

/-- `{x | inner u x ≤ c}` is convex. -/
lemma convex_hpLower (u : V) (c : ℝ) : Convex ℝ {x : V | inner ℝ u x ≤ c} := by
  have hlin : IsLinearMap ℝ (fun x : V => inner ℝ u x) := by
    refine IsLinearMap.mk ?_ ?_
    · intro x y
      exact inner_add_right u x y
    · intro r x
      rw [inner_smul_right]
      simp
  convert (convex_Iic (𝕜 := ℝ) c).is_linear_preimage hlin using 1
  ext x
  simp

/-- `{x | inner u x = c}` is convex. -/
lemma convex_hpPlane (u : V) (c : ℝ) : Convex ℝ {x : V | inner ℝ u x = c} := by
  have hlin : IsLinearMap ℝ (fun x : V => inner ℝ u x) := by
    refine IsLinearMap.mk ?_ ?_
    · intro x y
      exact inner_add_right u x y
    · intro r x
      rw [inner_smul_right]
      simp
  convert (convex_singleton c).is_linear_preimage hlin using 1
  ext x
  simp

/-- `{x | c ≤ inner u x}` is closed. -/
lemma isClosed_hpUpper (u : V) (c : ℝ) : IsClosed {x : V | c ≤ inner ℝ u x} := by
  refine isClosed_le (f := fun x : V => c) (g := fun x : V => inner ℝ u x) continuous_const ?_
  fun_prop

/-- `{x | inner u x ≤ c}` is closed. -/
lemma isClosed_hpLower (u : V) (c : ℝ) : IsClosed {x : V | inner ℝ u x ≤ c} := by
  refine isClosed_le (f := fun x : V => inner ℝ u x) (g := fun x : V => c) ?_ continuous_const
  fun_prop

/-- `{x | inner u x = c}` is closed. -/
lemma isClosed_hpPlane (u : V) (c : ℝ) : IsClosed {x : V | inner ℝ u x = c} := by
  refine isClosed_eq (f := fun x : V => inner ℝ u x) (g := fun x : V => c) ?_ continuous_const
  fun_prop

/-- The cutting hyperplane has empty interior (for a nonzero functional). -/
lemma interior_hpPlane_empty (u : V) (hu : u ≠ 0) (c : ℝ) :
    interior {x : V | inner ℝ u x = c} = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  intro hne
  rcases hne with ⟨x, hx⟩
  have hx_mem : x ∈ {x : V | inner ℝ u x = c} := interior_subset hx
  have hx_nhds : {x : V | inner ℝ u x = c} ∈ 𝓝 x := (mem_interior_iff_mem_nhds.mp hx)
  rcases (Metric.mem_nhds_iff.mp hx_nhds) with ⟨ε, hε, hball⟩
  have hε2 : 0 < ε / 2 := half_pos hε
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let r : ℝ := (ε / 2) / ‖u‖
  let y : V := x + r • u
  have hr : 0 ≤ r := div_nonneg (le_of_lt hε2) (le_of_lt hnorm)
  have hnormr : ‖r • u‖ = ε / 2 := by
    have hu' : ‖u‖ ≠ 0 := hnorm.ne'
    calc
      ‖r • u‖ = ‖r‖ * ‖u‖ := by rw [norm_smul]
      _ = r * ‖u‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hr]
      _ = ε / 2 := by
        unfold r
        field_simp [hu']
  have hy_mem_ball : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : y - x = r • u := by simp [y]
    calc
      ‖y - x‖ = ‖r • u‖ := by rw [hsub]
      _ = ε / 2 := hnormr
      _ < ε := by linarith
  have hy_mem : y ∈ {x : V | inner ℝ u x = c} := hball hy_mem_ball
  have hyval : inner ℝ u y = inner ℝ u x + r * ‖u‖ ^ 2 := by
    simp [y, inner_add_right, inner_smul_right]
  have hinnerx : inner ℝ u x = c := hx_mem
  have hyval' : inner ℝ u y = c + r * ‖u‖ ^ 2 := by rw [hyval, hinnerx]
  have hneq : inner ℝ u y ≠ c := by
    rw [hyval']
    have hrpos : 0 < r := div_pos hε2 hnorm
    have hpos : 0 < r * ‖u‖ ^ 2 := mul_pos hrpos (sq_pos_of_ne_zero hnorm.ne')
    linarith
  exact hneq hy_mem

/-- An empty-interior `Conv` has `val` zero for a simple valuation. -/
theorem val_zero_of_interior_empty
    (φ : ConvexBody V → ℝ)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0)
    (S : Conv V) (hS : interior (S : Set V) = ∅) : val φ S = 0 := by
  by_cases h : (S : Set V).Nonempty
  · have hb : φ (Conv.toBody S h) = 0 := by
      apply hsimple (Conv.toBody S h)
      simpa [Conv.toBody] using hS
    unfold val
    rw [dif_pos h]
    exact hb
  · exact val_eq_zero_of_not_nonempty φ S h

/-- Weak additivity of `val` along a hyperplane cut. -/
theorem weak_add_cut
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (S : Conv V) (u : V) (c : ℝ) :
    val φ S + val φ (S.inter {x | inner ℝ u x = c} (convex_hpPlane u c) (isClosed_hpPlane u c)) =
      val φ (S.inter {x | c ≤ inner ℝ u x} (convex_hpUpper u c) (isClosed_hpUpper u c)) +
      val φ (S.inter {x | inner ℝ u x ≤ c} (convex_hpLower u c) (isClosed_hpLower u c)) := by
  let Up : Conv V := S.inter {x | c ≤ inner ℝ u x} (convex_hpUpper u c) (isClosed_hpUpper u c)
  let Lo : Conv V := S.inter {x | inner ℝ u x ≤ c} (convex_hpLower u c) (isClosed_hpLower u c)
  let Pl : Conv V := S.inter {x | inner ℝ u x = c} (convex_hpPlane u c) (isClosed_hpPlane u c)
  have hUp : (Up : Set V) = (S : Set V) ∩ {x | c ≤ inner ℝ u x} := by rfl
  have hLo : (Lo : Set V) = (S : Set V) ∩ {x | inner ℝ u x ≤ c} := by rfl
  have hPl' : (Pl : Set V) = (S : Set V) ∩ {x | inner ℝ u x = c} := by rfl
  have hS_union : (S : Set V) = (Up : Set V) ∪ (Lo : Set V) := by
    rw [hUp, hLo]
    ext x
    constructor
    · intro hx
      by_cases h : c ≤ inner ℝ u x
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, le_of_lt (lt_of_not_ge h)⟩
    · intro hx
      rcases hx with hx | hx <;> exact hx.1
  have hPl : (Pl : Set V) = (Up : Set V) ∩ (Lo : Set V) := by
    rw [hPl', hUp, hLo]
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1, hx.2.ge⟩, ⟨hx.1, hx.2.le⟩⟩
    · intro hx
      exact ⟨hx.1.1, le_antisymm hx.2.2 hx.1.2⟩
  have h := val_add φ hadd (A := S) (B := Pl) (C := Up) (D := Lo) hS_union hPl
  simpa [Up, Lo, Pl] using h

/-- For a simple valuation, a hyperplane cut splits the value: `val(S) =
val(S∩upper) + val(S∩lower)`. -/
theorem simple_cut_add
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0)
    (S : Conv V) {u : V} (hu : u ≠ 0) (c : ℝ) :
    val φ S =
      val φ (S.inter {x | c ≤ inner ℝ u x} (convex_hpUpper u c) (isClosed_hpUpper u c)) +
      val φ (S.inter {x | inner ℝ u x ≤ c} (convex_hpLower u c) (isClosed_hpLower u c)) := by
  have hPl0 : val φ (S.inter {x | inner ℝ u x = c} (convex_hpPlane u c) (isClosed_hpPlane u c)) = 0 := by
    refine val_zero_of_interior_empty φ hsimple (S.inter {x | inner ℝ u x = c} (convex_hpPlane u c) (isClosed_hpPlane u c)) ?_
    have hsub : ((S.inter {x | inner ℝ u x = c} (convex_hpPlane u c) (isClosed_hpPlane u c) : Set V)
        ⊆ {x : V | inner ℝ u x = c}) := by
      intro z hz
      exact hz.2
    have hint_mono : interior ((S.inter {x | inner ℝ u x = c} (convex_hpPlane u c) (isClosed_hpPlane u c) : Set V))
        ⊆ interior {x : V | inner ℝ u x = c} := interior_mono hsub
    have hint_plane_empty : interior {x : V | inner ℝ u x = c} = ∅ := interior_hpPlane_empty u hu c
    rw [hint_plane_empty] at hint_mono
    exact Set.subset_empty_iff.mp hint_mono
  have h := weak_add_cut φ hadd S u c
  linarith

/-- Two-piece additivity for a simple valuation. -/
theorem simple_two_piece
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0)
    {A C D : ConvexBody V}
    (hA : (A : Set V) = (C : Set V) ∪ (D : Set V))
    (hint : interior ((C : Set V) ∩ (D : Set V)) = ∅) :
    φ A = φ C + φ D := by
  by_cases hB : ((C : Set V) ∩ (D : Set V)).Nonempty
  · let B : ConvexBody V := ConvexBody.mk ((C : Set V) ∩ (D : Set V))
        (C.convex.inter D.convex) (C.isCompact.inter_right D.isCompact.isClosed) hB
    have hBset : (B : Set V) = (C : Set V) ∩ (D : Set V) := rfl
    have hB0 : φ B = 0 := by
      apply hsimple B
      simpa [hBset] using hint
    have hie := hadd A B C D hA hBset
    linarith
  · exfalso
    have hCDeq : ((C : Set V) ∩ (D : Set V)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    have hCd : Disjoint (C : Set V) (D : Set V) := Set.disjoint_iff_inter_eq_empty.mpr hCDeq
    have hcon : Convex ℝ ((C : Set V) ∪ (D : Set V)) := by
      rw [← hA]
      exact A.convex
    exact (not_convex_union_of_disjoint_nonempty_conv C.convex D.convex C.isCompact D.isCompact
      C.nonempty D.nonempty hCd) hcon

end WeakAdd




/-! ## Families of pieces and the discrepancy functional -/

section Discrepancy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

open scoped BigOperators

/-- Sum of the values of the pieces of a family. -/
noncomputable def famVal (φ : ConvexBody V → ℝ) {ι : Type*} [Fintype ι]
    (F : ι → Conv V) : ℝ := ∑ i, val φ (F i)

/-- The discrepancy of a family covering a convex compact set. -/
noncomputable def discr (φ : ConvexBody V → ℝ) (U : Conv V) {ι : Type*} [Fintype ι]
    (F : ι → Conv V) : ℝ := val φ U - famVal φ F

/-- Restrict a family of pieces to the upper halfspace. -/
def cutUpper {ι : Type*} (F : ι → Conv V) (u : V) (c : ℝ) (i : ι) : Conv V :=
  (F i).inter {x | c ≤ inner ℝ u x} (convex_hpUpper u c) (isClosed_hpUpper u c)

/-- Restrict a family of pieces to the lower halfspace. -/
def cutLower {ι : Type*} (F : ι → Conv V) (u : V) (c : ℝ) (i : ι) : Conv V :=
  (F i).inter {x | inner ℝ u x ≤ c} (convex_hpLower u c) (isClosed_hpLower u c)

/-- Restrict a convex union set to the upper halfspace. -/
def cutUpperU (U : Conv V) (u : V) (c : ℝ) : Conv V :=
  U.inter {x | c ≤ inner ℝ u x} (convex_hpUpper u c) (isClosed_hpUpper u c)

/-- Restrict a convex union set to the lower halfspace. -/
def cutLowerU (U : Conv V) (u : V) (c : ℝ) : Conv V :=
  U.inter {x | inner ℝ u x ≤ c} (convex_hpLower u c) (isClosed_hpLower u c)

theorem famVal_split
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0)
    {ι : Type*} [Fintype ι] (F : ι → Conv V) {u : V} (hu : u ≠ 0) (c : ℝ) :
    famVal φ F = famVal φ (cutUpper F u c) + famVal φ (cutLower F u c) := by
  unfold famVal
  calc
    ∑ i, val φ (F i)
        = ∑ i, (val φ (cutUpper F u c i) + val φ (cutLower F u c i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact simple_cut_add φ hadd hsimple (F i) hu c
    _ = ∑ i, val φ (cutUpper F u c i) + ∑ i, val φ (cutLower F u c i) := by
          rw [Finset.sum_add_distrib]

/-- Restricting the union and the family to a halfspace preserves coverage. -/
theorem cut_coverage
    {ι : Type*} [Fintype ι] (U : Conv V) (F : ι → Conv V)
    (hcov : (U : Set V) = ⋃ i, (F i : Set V)) (u : V) (c : ℝ) :
    (cutUpperU U u c : Set V) = ⋃ i, (cutUpper F u c i : Set V) := by
  ext x
  constructor
  · intro hx
    have hxU : x ∈ (U : Set V) := hx.1
    rw [hcov] at hxU
    rw [Set.mem_iUnion] at hxU
    rcases hxU with ⟨i, hxF⟩
    rw [Set.mem_iUnion]
    exact ⟨i, ⟨hxF, hx.2⟩⟩
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨i, hxF⟩
    have hxU : x ∈ (U : Set V) := by
      rw [hcov]
      rw [Set.mem_iUnion]
      exact ⟨i, hxF.1⟩
    exact ⟨hxU, hxF.2⟩

/-- The discrepancy is additive across a hyperplane cut (for a simple
valuation): `discr = discr⁺ + discr⁻`. -/
theorem discr_cut_split
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0)
    {ι : Type*} [Fintype ι] (U : Conv V) (F : ι → Conv V)
    (hcov : (U : Set V) = ⋃ i, (F i : Set V))
    {u : V} (hu : u ≠ 0) (c : ℝ) :
    discr φ U F = discr φ (cutUpperU U u c) (cutUpper F u c) +
      discr φ (cutLowerU U u c) (cutLower F u c) := by
  have hU : val φ U = val φ (cutUpperU U u c) + val φ (cutLowerU U u c) := by
    exact simple_cut_add φ hadd hsimple U hu c
  have hF : famVal φ F = famVal φ (cutUpper F u c) + famVal φ (cutLower F u c) := by
    exact famVal_split φ hadd hsimple F hu c
  unfold discr
  rw [hU, hF]
  ring

end Discrepancy


/-! ## Continuity along decreasing families of convex bodies -/

section Nested

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- nested decreasing inclusion helper -/
lemma nested_sub_of_le {B : ℕ → Set V} (hdec : ∀ n, B (n + 1) ⊆ B n) {m n : ℕ}
    (hmn : m ≤ n) : B n ⊆ B m := by
  induction hmn with
  | refl => intro x hx; exact hx
  | @step m' hm' ih =>
      intro x hx
      exact ih (hdec m' hx)

/-- Nested compact sets with intersection `L` eventually lie in the
`ε`-neighbourhood `{x | ∃ y ∈ L, dist x y < ε}` of `L`. -/
lemma nested_eventually_subset_thickening
    {B : ℕ → Set V} (L : Set V)
    (hB0 : IsCompact (B 0))
    (hdec : ∀ n, B (n + 1) ⊆ B n)
    (hcl : ∀ n, IsClosed (B n))
    (hlim : L = ⋂ n, B n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, B n ⊆ {x | ∃ y ∈ L, dist x y < ε} := by
  let Vε : Set V := {x | ∃ y ∈ L, dist x y < ε}
  let K : Set V := B 0 \ Vε
  have hVε_open : IsOpen Vε := by
    rw [Metric.isOpen_iff]
    intro x hx
    change x ∈ {x : V | ∃ y ∈ L, dist x y < ε} at hx
    rcases hx with ⟨y, hyL, hd⟩
    let δ : ℝ := (ε - dist x y) / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      exact half_pos (sub_pos.mpr hd)
    refine ⟨δ, hδ, ?_⟩
    intro z hz
    change ∃ y₀ : V, y₀ ∈ L ∧ dist z y₀ < ε
    refine ⟨y, hyL, ?_⟩
    calc
      dist z y ≤ dist z x + dist x y := dist_triangle z x y
      _ < δ + dist x y := by
        have hzx : dist z x < δ := by simpa [dist_comm] using (Metric.mem_ball.mp hz)
        linarith
      _ < ε := by
        dsimp [δ]
        nlinarith [hd]
  have hVε_sub : L ⊆ Vε := by
    intro x hxL
    exact ⟨x, hxL, by simpa using hε⟩
  have hKclosed : IsClosed K := (hcl 0).inter hVε_open.isClosed_compl
  have hKcpt : IsCompact K := hB0.of_isClosed_subset hKclosed (by intro x hx; exact hx.1)
  have hKL : K ∩ L = ∅ := by
    apply subset_antisymm
    · intro x hx
      have hxV : x ∈ Vε := hVε_sub hx.2
      exact hx.1.2 hxV
    · simp
  by_contra hnone
  push_neg at hnone
  -- hnone : ∀ N : ℕ, ∃ n, N ≤ n ∧ ¬B n ⊆ Vε
  have hKne : ∀ n : ℕ, (K ∩ B n).Nonempty := by
    intro n
    rcases hnone n with ⟨m, hnm, hm⟩
    rw [not_subset] at hm
    rcases hm with ⟨x, hxBm, hxnotV⟩
    have hxK : x ∈ K := ⟨nested_sub_of_le hdec (Nat.zero_le m) hxBm, hxnotV⟩
    have hxBn : x ∈ B n := nested_sub_of_le hdec (by omega : n ≤ m) hxBm
    exact ⟨x, hxK, hxBn⟩
  have hcptK0 : IsCompact (K ∩ B 0) := hKcpt.inter_right (hcl 0)
  have hclK : ∀ n, IsClosed (K ∩ B n) := fun n => hKclosed.inter (hcl n)
  have hdecK : ∀ n, (K ∩ B (n + 1)) ⊆ (K ∩ B n) :=
    fun n => inter_subset_inter_right K (hdec n)
  have hcant := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => K ∩ B n) hdecK hKne hcptK0 hclK
  rcases hcant with ⟨x, hx⟩
  have hxK : x ∈ K := (Set.mem_iInter.mp hx 0).1
  have hxall : ∀ n : ℕ, x ∈ B n := fun n => (Set.mem_iInter.mp hx n).2
  have hxL : x ∈ L := by
    rw [hlim]
    rw [Set.mem_iInter]
    exact hxall
  have hbad : x ∈ K ∩ L := ⟨hxK, hxL⟩
  exact (by simpa [hKL] using hbad : False)

/-- Hausdorff distance of nested compact sets to their intersection tends to 0. -/
lemma hausdorffDist_nested_tendsto
    {B : ℕ → Set V} (L : Set V)
    (hB0 : IsCompact (B 0))
    (hdec : ∀ n, B (n + 1) ⊆ B n)
    (hcl : ∀ n, IsClosed (B n))
    (hlim : L = ⋂ n, B n) :
    Tendsto (fun n => hausdorffDist (B n) L) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  rcases nested_eventually_subset_thickening L hB0 hdec hcl hlim hε2 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hsubset : B n ⊆ {x | ∃ y ∈ L, dist x y < ε / 2} := hN n hn
  have hdist_le : hausdorffDist (B n) L ≤ ε / 2 := by
    apply hausdorffDist_le_of_mem_dist (le_of_lt hε2)
    · intro x hx
      rcases hsubset hx with ⟨y, hyL, hlt⟩
      exact ⟨y, hyL, le_of_lt hlt⟩
    · intro x hxL
      refine ⟨x, ?_, ?_⟩
      · have hxIn : x ∈ ⋂ k : ℕ, B k := by
          rw [← hlim]
          exact hxL
        exact (iInter_subset (fun k : ℕ => B k) n) hxIn
      · simpa using (le_of_lt hε2)
  have hnonneg : 0 ≤ hausdorffDist (B n) L := hausdorffDist_nonneg
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  linarith

/-- A decreasing sequence of convex bodies converges (in Hausdorff distance) to
their intersection. -/
lemma tendsto_of_nested_body
    {B : ℕ → ConvexBody V} (L : ConvexBody V)
    (hdec : ∀ n, (B (n + 1) : Set V) ⊆ (B n : Set V))
    (hlim : (L : Set V) = ⋂ n, (B n : Set V)) :
    Tendsto (fun n => B n) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hh := hausdorffDist_nested_tendsto (B := fun n => (B n : Set V)) (L := (L : Set V))
    (B 0).isCompact hdec (fun n => (B n).isCompact.isClosed) hlim
  rcases (Metric.tendsto_atTop.mp hh) ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hd := hN n hn
  have hhd : Metric.hausdorffDist ((B n : ConvexBody V) : Set V) ((L : ConvexBody V) : Set V) < ε := by
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (hausdorffDist_nonneg (s := (B n : Set V)) (t := (L : Set V)))] at hd
    exact hd
  rwa [ConvexBody.hausdorffDist_coe] at hhd

/-- A continuous function sends a decreasing family of convex bodies to a
convergent sequence of values. -/
lemma tendsto_val_nested (φ : ConvexBody V → ℝ) (hcont : Continuous φ)
    {B : ℕ → ConvexBody V} (L : ConvexBody V)
    (hdec : ∀ n, (B (n + 1) : Set V) ⊆ (B n : Set V))
    (hlim : (L : Set V) = ⋂ n, (B n : Set V)) :
    Tendsto (fun n => φ (B n)) atTop (𝓝 (φ L)) :=
  (hcont.tendsto L).comp (tendsto_of_nested_body (B := B) L hdec hlim)

/-- `X ∩ ⋂ₙ Cₙ = ⋂ₙ (X ∩ Cₙ)`. -/
lemma iInter_inter_nested {X : Set V} {C : ℕ → Set V} :
    X ∩ (⋂ n, C n) = ⋂ n, (X ∩ C n) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro n
    exact ⟨hx.1, (Set.mem_iInter.mp hx.2) n⟩
  · intro hx
    have hxall : ∀ n : ℕ, x ∈ X ∩ C n := Set.mem_iInter.mp hx
    refine ⟨(hxall 0).1, ?_⟩
    rw [Set.mem_iInter]
    intro n
    exact (hxall n).2


end Nested


/-! ## Counting nonempty pieces and cut-preservation of the dissection axioms -/

section DescentSupport

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

open scoped BigOperators

/-- Number of nonempty pieces of a family. -/
noncomputable def cnt {ι : Type*} [Fintype ι] (F : ι → Conv V) : ℕ := by
  classical exact (Finset.univ.filter (fun i => (F i : Set V).Nonempty)).card

/-- If every nonempty piece of `G` is a nonempty piece of `F`, then
`cnt G ≤ cnt F`. -/
lemma cnt_le_of_subset {ι : Type*} [Fintype ι] (F G : ι → Conv V)
    (h : ∀ i, (G i : Set V).Nonempty → (F i : Set V).Nonempty) : cnt G ≤ cnt F := by
  classical
  unfold cnt
  exact Finset.card_le_card (by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ i, h i hi.2⟩)

/-- If additionally a nonempty piece of `F` is empty in `G`, then `cnt G < cnt F`. -/
lemma cnt_lt_of_lost {ι : Type*} [Fintype ι] (F G : ι → Conv V) (i₀ : ι)
    (hG : ∀ i, (G i : Set V).Nonempty → (F i : Set V).Nonempty)
    (hF : (F i₀ : Set V).Nonempty) (hG0 : ¬(G i₀ : Set V).Nonempty) :
    cnt G < cnt F := by
  classical
  unfold cnt
  have hsub : (Finset.univ.filter (fun i => (G i : Set V).Nonempty))
      ⊆ (Finset.univ.filter (fun i => (F i : Set V).Nonempty)).erase i₀ := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_erase]
    constructor
    · intro hEq
      subst i
      exact hG0 hi.2
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hG i hi.2⟩
  have hmem : i₀ ∈ Finset.univ.filter (fun i => (F i : Set V).Nonempty) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i₀, hF⟩
  have hcard1 : 1 ≤ (Finset.univ.filter (fun i => (F i : Set V).Nonempty)).card := by
    exact Finset.card_pos.mpr ⟨i₀, hmem⟩
  have hle : (Finset.univ.filter (fun i => (G i : Set V).Nonempty)).card
      ≤ (Finset.univ.filter (fun i => (F i : Set V).Nonempty)).card - 1 := by
    calc
      (Finset.univ.filter (fun i => (G i : Set V).Nonempty)).card
          ≤ ((Finset.univ.filter (fun i => (F i : Set V).Nonempty)).erase i₀).card :=
            Finset.card_le_card hsub
      _ = (Finset.univ.filter (fun i => (F i : Set V).Nonempty)).card - 1 := by
            rw [Finset.card_erase_of_mem hmem]
  omega

/-- Pairwise empty-interior intersections are preserved by the upper cut. -/
lemma cut_pairwise_upper {ι : Type*} [Fintype ι] (F : ι → Conv V) (u : V) (c : ℝ)
    (hpair : ∀ i j, i ≠ j → interior ((F i : Set V) ∩ (F j : Set V)) = ∅) :
    ∀ i j, i ≠ j →
      interior ((cutUpper F u c i : Set V) ∩ (cutUpper F u c j : Set V)) = ∅ := by
  intro i j hij
  have hsub : (cutUpper F u c i : Set V) ∩ (cutUpper F u c j : Set V)
      ⊆ (F i : Set V) ∩ (F j : Set V) := by
    intro x hx
    exact ⟨hx.1.1, hx.2.1⟩
  have hint : interior ((cutUpper F u c i : Set V) ∩ (cutUpper F u c j : Set V))
      ⊆ interior ((F i : Set V) ∩ (F j : Set V)) := interior_mono hsub
  rw [hpair i j hij] at hint
  exact Set.subset_empty_iff.mp hint

/-- Pairwise empty-interior intersections are preserved by the lower cut. -/
lemma cut_pairwise_lower {ι : Type*} [Fintype ι] (F : ι → Conv V) (u : V) (c : ℝ)
    (hpair : ∀ i j, i ≠ j → interior ((F i : Set V) ∩ (F j : Set V)) = ∅) :
    ∀ i j, i ≠ j →
      interior ((cutLower F u c i : Set V) ∩ (cutLower F u c j : Set V)) = ∅ := by
  intro i j hij
  have hsub : (cutLower F u c i : Set V) ∩ (cutLower F u c j : Set V)
      ⊆ (F i : Set V) ∩ (F j : Set V) := by
    intro x hx
    exact ⟨hx.1.1, hx.2.1⟩
  have hint : interior ((cutLower F u c i : Set V) ∩ (cutLower F u c j : Set V))
      ⊆ interior ((F i : Set V) ∩ (F j : Set V)) := interior_mono hsub
  rw [hpair i j hij] at hint
  exact Set.subset_empty_iff.mp hint

/-- Cutting by the upper halfspace can only create empty pieces from empty ones. -/
lemma cutUpper_nonempty_of_nonempty {ι : Type*} (F : ι → Conv V) (u : V) (c : ℝ)
    (i : ι) : (cutUpper F u c i : Set V).Nonempty → (F i : Set V).Nonempty := by
  intro h
  rcases h with ⟨x, hx⟩
  exact ⟨x, hx.1⟩

/-- Cutting by the lower halfspace can only create empty pieces from empty ones. -/
lemma cutLower_nonempty_of_nonempty {ι : Type*} (F : ι → Conv V) (u : V) (c : ℝ)
    (i : ι) : (cutLower F u c i : Set V).Nonempty → (F i : Set V).Nonempty := by
  intro h
  rcases h with ⟨x, hx⟩
  exact ⟨x, hx.1⟩

end DescentSupport


/-! ## Cap sequences and the squeeze -/

section Squeeze

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- The closed upper halfspace `{c ≤ inner u x}` as a set. -/
def halfGe (u : V) (c : ℝ) : Set V := {x | c ≤ inner ℝ u x}

lemma convex_halfGe (u : V) (c : ℝ) : Convex ℝ (halfGe u c) := by
  unfold halfGe
  exact convex_hpUpper u c

lemma isClosed_halfGe (u : V) (c : ℝ) : IsClosed (halfGe u c) := by
  unfold halfGe
  exact isClosed_hpUpper u c

/-- The intersection of the first `m` halfspaces. -/
def capN (u : ℕ → V) (c : ℕ → ℝ) (m : ℕ) : Set V :=
  ⋂ j : {j : ℕ // j < m}, halfGe (u j.1) (c j.1)

lemma convex_capN (u : ℕ → V) (c : ℕ → ℝ) (m : ℕ) : Convex ℝ (capN u c m) := by
  unfold capN
  exact convex_iInter (fun j => convex_halfGe (u j.1) (c j.1))

lemma isClosed_capN (u : ℕ → V) (c : ℕ → ℝ) (m : ℕ) : IsClosed (capN u c m) := by
  unfold capN
  exact isClosed_iInter (fun j => isClosed_halfGe (u j.1) (c j.1))

lemma capN_zero (u : ℕ → V) (c : ℕ → ℝ) : capN u c 0 = Set.univ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    dsimp [capN]
    rw [Set.mem_iInter]
    intro j
    exfalso
    omega

lemma capN_mono (u : ℕ → V) (c : ℕ → ℝ) (m : ℕ) : capN u c (m + 1) ⊆ capN u c m := by
  intro x hx
  dsimp [capN] at hx ⊢
  rw [Set.mem_iInter] at hx ⊢
  intro j
  exact hx ⟨j.1, lt_trans j.2 (Nat.lt_succ_self m)⟩

/-- `capN (m+1) = capN m ∩ H_m`. -/
lemma capN_succ (u : ℕ → V) (c : ℕ → ℝ) (m : ℕ) :
    capN u c (m + 1) = capN u c m ∩ halfGe (u m) (c m) := by
  ext x
  constructor
  · intro hx
    have hx' : ∀ j : {j : ℕ // j < m + 1}, x ∈ halfGe (u j.1) (c j.1) := by
      dsimp [capN] at hx
      exact Set.mem_iInter.mp hx
    constructor
    · dsimp [capN]
      rw [Set.mem_iInter]
      intro j
      exact hx' ⟨j.1, lt_trans j.2 (Nat.lt_succ_self m)⟩
    · exact hx' ⟨m, Nat.lt_succ_self m⟩
  · intro hx
    rcases hx with ⟨hxcap, hxHm⟩
    dsimp [capN]
    rw [Set.mem_iInter]
    intro j
    by_cases hjm : j.1 < m
    · dsimp [capN] at hxcap
      rw [Set.mem_iInter] at hxcap
      exact hxcap ⟨j.1, hjm⟩
    · have hjm' : j.1 = m := by omega
      simpa [hjm'] using hxHm

/-- The intersection of all finite caps is the intersection of all halfspaces. -/
lemma iInter_capN (u : ℕ → V) (c : ℕ → ℝ) :
    (⋂ m : ℕ, capN u c m) = ⋂ j : ℕ, halfGe (u j) (c j) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro j
    have hm : x ∈ capN u c (j + 1) := (Set.mem_iInter.mp hx) (j + 1)
    dsimp [capN] at hm
    rw [Set.mem_iInter] at hm
    exact hm ⟨j, Nat.lt_succ_self j⟩
  · intro hx
    rw [Set.mem_iInter]
    intro m
    dsimp [capN]
    rw [Set.mem_iInter]
    intro j
    exact (Set.mem_iInter.mp hx) j.1

/-- Intersect a compact convex set with the first `m` halfspaces. -/
def convInterCaps (S : Conv V) (u : ℕ → V) (c : ℕ → ℝ) (m : ℕ) : Conv V :=
  Conv.mk ((S : Set V) ∩ capN u c m)
    (S.convex'.inter (convex_capN u c m))
    (S.isCompact'.inter_right (isClosed_capN u c m))

@[simp] theorem coe_convInterCaps (S : Conv V) (u : ℕ → V) (c : ℕ → ℝ) (m : ℕ) :
    ((convInterCaps S u c m : Conv V) : Set V) = (S : Set V) ∩ capN u c m := rfl

lemma coe_cutUpperU (U : Conv V) (u : V) (c : ℝ) :
    ((cutUpperU U u c : Conv V) : Set V) = (U : Set V) ∩ halfGe u c := by rfl
lemma coe_cutUpper {ι : Type*} (F : ι → Conv V) (u : V) (c : ℝ) (i : ι) :
    ((cutUpper F u c i : Conv V) : Set V) = (F i : Set V) ∩ halfGe u c := by rfl



/-- The discrepancy only depends on the underlying sets. -/
lemma discr_congr (φ : ConvexBody V → ℝ)
    {U U' : Conv V} {ι : Type*} [Fintype ι] {F F' : ι → Conv V}
    (hU : (U : Set V) = (U' : Set V))
    (hF : ∀ i, (F i : Set V) = (F' i : Set V)) :
    discr φ U F = discr φ U' F' := by
  unfold discr famVal
  congr 1
  · apply val_eq_of_set_eq_conv
    exact hU
  · apply Finset.sum_congr rfl
    intro i hi
    apply val_eq_of_set_eq_conv
    exact hF i

end Squeeze



/-! ## Stage families for the squeeze -/

section StageFamily

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

open scoped BigOperators

/-- Coverage is preserved when intersecting everything with the first `r` caps. -/
lemma cap_coverage {ι : Type*} [Fintype ι] (U : Conv V) (F : ι → Conv V)
    (hcov : (U : Set V) = ⋃ i, (F i : Set V)) (u : ℕ → V) (c : ℕ → ℝ) (r : ℕ) :
    ((convInterCaps U u c r : Conv V) : Set V) = ⋃ i, (convInterCaps (F i) u c r : Set V) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion]
    rcases hx with ⟨hxU, hxcap⟩
    rw [hcov] at hxU
    rcases (Set.mem_iUnion.mp hxU) with ⟨i, hxi⟩
    exact ⟨i, ⟨hxi, hxcap⟩⟩
  · intro hx
    rcases (Set.mem_iUnion.mp hx) with ⟨i, hxi⟩
    exact ⟨(by
      rw [hcov]
      rw [Set.mem_iUnion]
      exact ⟨i, hxi.1⟩), hxi.2⟩

/-- Pairwise empty interior is preserved under intersecting with the first `r` caps. -/
lemma cap_pairwise {ι : Type*} [Fintype ι] (F : ι → Conv V)
    (hpair : ∀ i j, i ≠ j → interior ((F i : Set V) ∩ (F j : Set V)) = ∅)
    (u : ℕ → V) (c : ℕ → ℝ) (r : ℕ) :
    ∀ i j, i ≠ j →
      interior ((convInterCaps (F i) u c r : Set V) ∩ (convInterCaps (F j) u c r : Set V)) = ∅ := by
  intro i j hij
  have hsub : (convInterCaps (F i) u c r : Set V) ∩ (convInterCaps (F j) u c r : Set V)
      ⊆ (F i : Set V) ∩ (F j : Set V) := by
    intro x hx
    exact ⟨hx.1.1, hx.2.1⟩
  have hint : interior ((convInterCaps (F i) u c r : Set V) ∩ (convInterCaps (F j) u c r : Set V))
      ⊆ interior ((F i : Set V) ∩ (F j : Set V)) := interior_mono hsub
  rw [hpair i j hij] at hint
  exact Set.subset_empty_iff.mp hint

/-- The count of a capped family is at most the original count. -/
lemma cnt_cap_le {ι : Type*} [Fintype ι] (F : ι → Conv V) (u : ℕ → V) (c : ℕ → ℝ) (r : ℕ) :
    cnt (fun i => convInterCaps (F i) u c r) ≤ cnt F := by
  apply cnt_le_of_subset F (fun i => convInterCaps (F i) u c r)
  intro i hi
  rcases hi with ⟨x, hx⟩
  exact ⟨x, hx.1⟩

/-- The designated piece survives the caps: `F i₀ ∩ capN r = F i₀` when
`F i₀ ⊆ capN r`. -/
lemma convInterCaps_eq_of_subset (S : Conv V) (u : ℕ → V) (c : ℕ → ℝ) (r : ℕ)
    (hsub : (S : Set V) ⊆ capN u c r) :
    ((convInterCaps S u c r : Conv V) : Set V) = (S : Set V) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, hsub hx⟩

/-- A degenerate halfspace `{x | c ≤ inner 0 x}` with `c ≤ 0` is everything. -/
lemma halfGe_zero_univ {c : ℝ} (hc : c ≤ 0) : halfGe (0 : V) c = Set.univ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    unfold halfGe
    simp [hc]

/-- The lower-cut family covers the lower-cut union. -/
lemma cut_coverage_lower {ι : Type*} [Fintype ι] (U : Conv V) (F : ι → Conv V)
    (hcov : (U : Set V) = ⋃ i, (F i : Set V)) (u : V) (c : ℝ) :
    ((cutLowerU U u c : Set V) = ⋃ i, (cutLower F u c i : Set V)) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion]
    rcases hx with ⟨hxU, hxlow⟩
    rw [hcov] at hxU
    rcases (Set.mem_iUnion.mp hxU) with ⟨i, hxi⟩
    exact ⟨i, ⟨hxi, hxlow⟩⟩
  · intro hx
    rcases (Set.mem_iUnion.mp hx) with ⟨i, hxi⟩
    exact ⟨(by
      rw [hcov]
      rw [Set.mem_iUnion]
      exact ⟨i, hxi.1⟩), hxi.2⟩

end StageFamily


/-! ## Body conversion and compactness for the squeeze limit -/

section SqueezeLim

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- Value of a nonempty `Conv` is the value of the corresponding body. -/
lemma val_eq_body_of_nonempty (φ : ConvexBody V → ℝ) (S : Conv V)
    (h : (S : Set V).Nonempty) : val φ S = φ (Conv.toBody S h) := by
  unfold val
  rw [dif_pos h]

/-- A decreasing sequence of compact sets with empty total intersection is
eventually empty. -/
lemma decreasing_compact_eventually_empty {B : ℕ → Set V}
    (hB0 : IsCompact (B 0)) (hdec : ∀ n, B (n + 1) ⊆ B n) (hcl : ∀ n, IsClosed (B n))
    (hinter : (⋂ n, B n) = ∅) : ∃ n, B n = ∅ := by
  by_contra hnone
  have hne : ∀ n, (B n).Nonempty := by
    intro n
    by_contra hempty
    apply hnone
    exact ⟨n, Set.not_nonempty_iff_eq_empty.mp hempty⟩
  have hcpt : ∀ n, IsCompact (B n) := fun n =>
    hB0.of_isClosed_subset (hcl n) (by
      intro x hx
      revert hx
      induction n with
      | zero => intro hx; exact hx
      | succ n ih =>
          intro hx
          exact ih (hdec n hx))
  have hcant := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed B hdec hne hB0 hcl
  exact (by simpa [hinter] using hcant)

/-- Intersection of a Conv with another Conv's carrier: the limit Conv. -/
def interConvOf (S T : Conv V) : Conv V :=
  Conv.mk ((S : Set V) ∩ (T : Set V)) (S.convex'.inter T.convex')
    (S.isCompact'.inter_right T.isCompact'.isClosed)

@[simp] theorem coe_interConvOf (S T : Conv V) :
    ((interConvOf S T : Conv V) : Set V) = (S : Set V) ∩ (T : Set V) := rfl

/-- Decreasing Conv chain with nonempty carriers gives bodies; the set
intersection identity needed by `tendsto_val_nested`. -/
lemma cap_body_chain_limit (φ : ConvexBody V → ℝ) (hcont : Continuous φ)
    {S : Conv V} (u : ℕ → V) (c : ℕ → ℝ) (T : Conv V)
    (hcap1T : ∀ n, ∀ x ∈ (T : Set V), c n < inner ℝ (u n) x)
    (hcap2T : (⋂ n, halfGe (u n) (c n)) ⊆ (T : Set V))
    (hne_chain : ∀ r : ℕ, ((convInterCaps S u c r : Conv V) : Set V).Nonempty)
    (hne_lim : ((interConvOf S T : Conv V) : Set V).Nonempty) :
    Tendsto (fun r => val φ (convInterCaps S u c r)) atTop (𝓝 (val φ (interConvOf S T))) := by
  classical
  -- bodies along the chain
  let B : ℕ → ConvexBody V := fun r => Conv.toBody (convInterCaps S u c r) (hne_chain r)
  let L : ConvexBody V := Conv.toBody (interConvOf S T) hne_lim
  have hdec : ∀ r, (B (r + 1) : Set V) ⊆ (B r : Set V) := by
    intro r x hx
    -- x ∈ S ∩ capN(r+1) ⊆ S ∩ capN r
    exact ⟨hx.1, (capN_mono u c r) hx.2⟩
  have hT_capN : ∀ r, (T : Set V) ⊆ capN u c r := by
    intro r x hx
    dsimp [capN]
    rw [Set.mem_iInter]
    intro j
    exact le_of_lt (hcap1T j x hx)
  have hlim : (L : Set V) = ⋂ r, (B r : Set V) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iInter]
      intro r
      exact ⟨hx.1, hT_capN r hx.2⟩
    · intro hx
      have hxS : x ∈ (S : Set V) := ((Set.mem_iInter.mp hx) 0).1
      have hxcapAll : x ∈ ⋂ n : ℕ, halfGe (u n) (c n) := by
        rw [Set.mem_iInter]
        intro n
        have hxcap : x ∈ capN u c (n + 1) := ((Set.mem_iInter.mp hx) (n + 1)).2
        dsimp [capN] at hxcap
        rw [Set.mem_iInter] at hxcap
        exact hxcap ⟨n, Nat.lt_succ_self n⟩
      refine ⟨hxS, hcap2T hxcapAll⟩
  have ht := tendsto_val_nested φ hcont (B := B) L hdec hlim
  -- ht : Tendsto (fun r => φ (B r)) atTop (𝓝 (φ L)) ; convert to val
  -- val φ (convInterCaps S u c r) = φ (B r)
  have hvalseq : (fun r => val φ (convInterCaps S u c r)) = fun r => φ (B r) := by
    funext r
    dsimp [B]
    exact val_eq_body_of_nonempty φ (convInterCaps S u c r) (hne_chain r)
  have hvalL : val φ (interConvOf S T) = φ L := by
    dsimp [L]
    exact val_eq_body_of_nonempty φ (interConvOf S T) hne_lim
  rwa [hvalseq, hvalL]

end SqueezeLim

/-! ## The main descent: strong induction on the number of nonempty pieces -/

section MainDescent

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

open scoped BigOperators

/-- A family with a positive count has a nonempty piece. -/
lemma exists_nonempty_of_cnt_pos {ι : Type*} [Fintype ι] (F : ι → Conv V)
    (h : 0 < cnt F) : ∃ i, (F i : Set V).Nonempty := by
  classical
  unfold cnt at h
  have hf : (Finset.univ.filter (fun i => (F i : Set V).Nonempty)).Nonempty := by
    exact Finset.card_pos.mp h
  rcases hf with ⟨i, hi⟩
  rw [Finset.mem_filter] at hi
  exact ⟨i, hi.2⟩

/-- The squeeze: under `discr ≠ 0` the induction hypothesis leads to a
contradiction.  Squeezing with the caps of the designated piece `i₀` preserves
the discrepancy at every stage; in the limit the discrepancy equals
`val(D) − (val(D) + Σ_{i≠i₀} 0) = 0`, contradicting `hd`. -/
theorem squeeze_step
    (φ : ConvexBody V → ℝ)
    (hcont : Continuous φ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0)
    {ι : Type*} [Fintype ι] (U : Conv V) (F : ι → Conv V) (i₀ : ι)
    (hne₀ : (F i₀ : Set V).Nonempty)
    (hcov : (U : Set V) = ⋃ i, (F i : Set V))
    (hpair : ∀ i j, i ≠ j → interior ((F i : Set V) ∩ (F j : Set V)) = ∅)
    (hd : discr φ U F ≠ 0)
    {m : ℕ} (hcntm : cnt F ≤ m)
    (ihn : ∀ k < m, ∀ (U' : Conv V) (F' : ι → Conv V),
      cnt F' ≤ k → ((U' : Set V) = ⋃ i, (F' i : Set V)) →
      (∀ i j, i ≠ j → interior ((F' i : Set V) ∩ (F' j : Set V)) = ∅) →
      discr φ U' F' = 0) :
    False := by
  classical
  -- cap data for the designated piece
  rcases Commons.Analysis.Convex.capSequence (V := V) (D := (F i₀ : Set V))
    (F i₀).convex' (F i₀).isCompact' hne₀ with ⟨u, c, hcap1, hcap2⟩
  let Um : ℕ → Conv V := fun r => convInterCaps U u c r
  let Fm : ℕ → ι → Conv V := fun r i => convInterCaps (F i) u c r
  -- D ⊆ every cap
  have hD_capN : ∀ r, (F i₀ : Set V) ⊆ capN u c r := by
    intro r x hx
    dsimp [capN]
    rw [Set.mem_iInter]
    intro j
    exact le_of_lt (hcap1 j x hx)
  have hD_halflt : ∀ r, (F i₀ : Set V) ∩ {x | inner ℝ (u r) x ≤ c r} = ∅ := by
    intro r
    ext x
    constructor
    · intro hx
      have hlt : c r < inner ℝ (u r) x := hcap1 r x hx.1
      exact (not_le_of_gt hlt) hx.2
    · intro hx
      simp at hx
  -- nonemptiness of the designated piece at every stage
  have hneD : ∀ r, (Fm r i₀ : Set V).Nonempty := by
    intro r
    have hcar : (Fm r i₀ : Set V) = (F i₀ : Set V) := by
      dsimp [Fm]
      exact convInterCaps_eq_of_subset (F i₀) u c r (hD_capN r)
    rcases hne₀ with ⟨x, hx⟩
    exact ⟨x, by rw [hcar]; exact hx⟩
  -- coverage and pairwise at each stage
  have hcovr : ∀ r, (Um r : Set V) = ⋃ i, (Fm r i : Set V) := by
    intro r
    dsimp [Um, Fm]
    exact cap_coverage U F hcov u c r
  have hpairr : ∀ r, ∀ i j, i ≠ j →
      interior ((Fm r i : Set V) ∩ (Fm r j : Set V)) = ∅ := by
    intro r
    dsimp [Fm]
    exact cap_pairwise F hpair u c r
  have hcntm' : ∀ r, cnt (Fm r) ≤ m := by
    intro r
    exact le_trans (cnt_cap_le F u c r) hcntm
  -- one-step preservation of the discrepancy (u ≠ 0 case and degenerate case)
  have hpres : ∀ r, discr φ (Um r) (Fm r) = discr φ (Um (r + 1)) (Fm (r + 1)) := by
    intro r
    by_cases huz : u r ≠ 0
    · -- genuine cut at stage r
      have hcut := discr_cut_split φ hadd hsimple (Um r) (Fm r) (hcovr r) huz (c r)
      let Gl : ι → Conv V := fun i => cutLower (Fm r) (u r) (c r) i
      let Ul : Conv V := cutLowerU (Um r) (u r) (c r)
      have hcGl : cnt Gl < m := by
        have hlt1 : cnt Gl < cnt (Fm r) := by
          apply cnt_lt_of_lost (Fm r) Gl i₀
          · intro i hi
            exact cutLower_nonempty_of_nonempty (Fm r) (u r) (c r) i hi
          · exact hneD r
          · intro hg
            rcases hg with ⟨x, hx⟩
            change x ∈ ((Fm r i₀ : Set V) ∩ {x : V | inner ℝ (u r) x ≤ c r}) at hx
            have hDempty : ((Fm r i₀ : Set V) ∩ {x | inner ℝ (u r) x ≤ c r}) = ∅ := by
              have hcar : (Fm r i₀ : Set V) = (F i₀ : Set V) := by
                dsimp [Fm]
                exact convInterCaps_eq_of_subset (F i₀) u c r (hD_capN r)
              rw [hcar]
              exact hD_halflt r
            exact (by simpa [hDempty] using hx : False)
        exact lt_of_lt_of_le hlt1 (hcntm' r)
      have hcovGl : (Ul : Set V) = ⋃ i, (Gl i : Set V) := by
        dsimp [Ul, Gl]
        exact cut_coverage_lower (Um r) (Fm r) (hcovr r) (u r) (c r)
      have hpairGl : ∀ i j, i ≠ j → interior ((Gl i : Set V) ∩ (Gl j : Set V)) = ∅ := by
        dsimp [Gl]
        exact cut_pairwise_lower (Fm r) (u r) (c r) (hpairr r)
      have hzero : discr φ Ul Gl = 0 := by
        exact ihn (cnt Gl) hcGl Ul Gl le_rfl hcovGl hpairGl
      -- upper part carriers equal the next stage
      have hcarU : ((cutUpperU (Um r) (u r) (c r) : Conv V) : Set V) = (Um (r + 1) : Set V) := by
        rw [coe_cutUpperU, coe_convInterCaps, coe_convInterCaps]
        rw [capN_succ]
        ext x
        simp [and_assoc]
      have hcarF : ∀ i, ((cutUpper (Fm r) (u r) (c r) i : Conv V) : Set V) = (Fm (r + 1) i : Set V) := by
        intro i
        rw [coe_cutUpper, coe_convInterCaps, coe_convInterCaps]
        rw [capN_succ]
        ext x
        simp [and_assoc]
      have hcong := discr_congr φ hcarU hcarF
      -- discr(Um r)(Fm r) = discr(upper) + 0 = discr(next)
      calc
        discr φ (Um r) (Fm r) = discr φ (cutUpperU (Um r) (u r) (c r)) (cutUpper (Fm r) (u r) (c r)) +
            discr φ Ul Gl := by simpa [Ul, Gl] using hcut
        _ = discr φ (Um (r + 1)) (Fm (r + 1)) := by
            rw [hzero]
            simpa using hcong
    · -- degenerate halfspace u r = 0
      have hu0 : u r = 0 := by simpa using (not_ne_iff.mp huz)
      have hcap : capN u c (r + 1) = capN u c r := by
        rw [capN_succ, hu0]
        rcases hne₀ with ⟨x0, hx0⟩
        have hlt0 : c r < inner ℝ (0 : V) x0 := by simpa [hu0] using hcap1 r x0 hx0
        have hlt : c r < 0 := by simpa using hlt0
        have huniv : halfGe (0 : V) (c r) = Set.univ := halfGe_zero_univ (le_of_lt hlt)
        rw [huniv]
        simp
      have hcarU2 : (Um (r + 1) : Set V) = (Um r : Set V) := by
        ext x
        simp [Um, convInterCaps, hcap]
      have hcarF2 : ∀ i, (Fm (r + 1) i : Set V) = (Fm r i : Set V) := by
        intro i
        ext x
        simp [Fm, convInterCaps, hcap]
      exact discr_congr φ hcarU2.symm (fun i => (hcarF2 i).symm)
  -- constancy of the discrepancy along the squeeze
  have hconst : ∀ r, discr φ (Um r) (Fm r) = discr φ U F := by
    intro r
    induction r with
    | zero =>
        have hcar0 : (Um 0 : Set V) = (U : Set V) := by
          rw [coe_convInterCaps]
          rw [capN_zero]
          ext x
          simp
        have hcarF0 : ∀ i, (Fm 0 i : Set V) = (F i : Set V) := by
          intro i
          rw [coe_convInterCaps]
          rw [capN_zero]
          ext x
          simp
        exact discr_congr φ hcar0 hcarF0
    | succ r ih =>
        rw [← hpres r]
        exact ih
  -- the count never drops
  have hcnt_eq : ∀ r, cnt (Fm r) = cnt F := by
    intro r
    by_contra hne
    have hle : cnt (Fm r) ≤ cnt F := cnt_cap_le F u c r
    have hlt : cnt (Fm r) < cnt F := lt_of_le_of_ne hle hne
    have hltm : cnt (Fm r) < m := lt_of_lt_of_le hlt hcntm
    have hz := ihn (cnt (Fm r)) hltm (Um r) (Fm r) le_rfl (hcovr r) (hpairr r)
    exact hd (by rw [← hconst r, hz])
  -- every originally nonempty piece stays nonempty along the squeeze
  have hne_piece : ∀ r i, (F i : Set V).Nonempty → (Fm r i : Set V).Nonempty := by
    intro r i hFi
    by_contra hempty
    have hlt : cnt (Fm r) < cnt F := by
      apply cnt_lt_of_lost F (Fm r) i
      · intro j hj
        rcases hj with ⟨x, hx⟩
        exact ⟨x, hx.1⟩
      · exact hFi
      · exact hempty
    have hltm : cnt (Fm r) < m := lt_of_lt_of_le hlt hcntm
    have hz := ihn (cnt (Fm r)) hltm (Um r) (Fm r) le_rfl (hcovr r) (hpairr r)
    exact hd (by rw [← hconst r, hz])
  -- limit pieces are nonempty when the originals are
  have hcap_inter : (⋂ r : ℕ, capN u c r) = (F i₀ : Set V) := by
    rw [iInter_capN]
    apply subset_antisymm
    · exact hcap2
    · intro x hx
      rw [Set.mem_iInter]
      intro n
      unfold halfGe
      exact le_of_lt (hcap1 n x hx)
  have hne_lim : ∀ i, (F i : Set V).Nonempty → ((interConvOf (F i) (F i₀) : Conv V) : Set V).Nonempty := by
    intro i hFi
    classical
    let C : ℕ → Set V := fun r => (Fm r i : Set V)
    have hdec : ∀ r, C (r + 1) ⊆ C r := by
      intro r x hx
      exact ⟨hx.1, capN_mono u c r hx.2⟩
    have hneC : ∀ r, (C r).Nonempty := by
      intro r
      exact hne_piece r i hFi
    have hcl : ∀ r, IsClosed (C r) := by
      intro r
      dsimp [C, Fm]
      exact (F i).isCompact'.isClosed.inter (isClosed_capN u c r)
    have hcpt0 : IsCompact (C 0) := by
      dsimp [C, Fm]
      exact (F i).isCompact'.inter_right (isClosed_capN u c 0)
    have hcant := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hneC hcpt0 hcl
    have hid : (⋂ r, C r) = ((interConvOf (F i) (F i₀) : Conv V) : Set V) := by
      calc
        (⋂ r, C r) = (⋂ r, (F i : Set V) ∩ capN u c r) := by simp [C, Fm]
        _ = (F i : Set V) ∩ (⋂ r, capN u c r) := by
            exact (iInter_inter_nested (X := (F i : Set V)) (C := capN u c)).symm
        _ = (F i : Set V) ∩ (F i₀ : Set V) := by rw [hcap_inter]
        _ = ((interConvOf (F i) (F i₀) : Conv V) : Set V) := rfl
    simpa [hid] using hcant
  -- value of the union tends to the value of the designated piece
  have hUm_ne : ∀ r, (convInterCaps U u c r : Set V).Nonempty := by
    intro r
    rcases hne₀ with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact ⟨(by
      rw [hcov]
      rw [Set.mem_iUnion]
      exact ⟨i₀, hx⟩), hD_capN r hx⟩
  have hUlim_ne : ((interConvOf U (F i₀) : Conv V) : Set V).Nonempty := by
    rcases hne₀ with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact ⟨(by
      rw [hcov]
      rw [Set.mem_iUnion]
      exact ⟨i₀, hx⟩), hx⟩
  have hT := cap_body_chain_limit φ hcont (S := U) u c (F i₀) hcap1 hcap2 hUm_ne hUlim_ne
  have hval_eq : val φ (interConvOf U (F i₀)) = val φ (F i₀) := by
    apply val_eq_of_set_eq_conv
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨(by rw [hcov]; rw [Set.mem_iUnion]; exact ⟨i₀, hx⟩), hx⟩
  have hunt : Tendsto (fun r => val φ (Um r)) atTop (𝓝 (val φ (F i₀))) := by
    simpa [Um, hval_eq] using hT
  -- values of the pieces tend to the values of the limit pieces
  have hpiece_lim : ∀ i, Tendsto (fun r => val φ (Fm r i)) atTop (𝓝 (val φ (interConvOf (F i) (F i₀)))) := by
    intro i
    by_cases hFi : (F i : Set V).Nonempty
    · have hT := cap_body_chain_limit φ hcont (S := F i) u c (F i₀) hcap1 hcap2
          (fun r => hne_piece r i hFi) (hne_lim i hFi)
      simpa [Fm] using hT
    · have hseq : (fun r => val φ (Fm r i)) = fun _ : ℕ => (0 : ℝ) := by
        funext r
        apply val_eq_zero_of_not_nonempty
        intro h
        rcases h with ⟨x, hx⟩
        exact hFi ⟨x, hx.1⟩
      have hlim0 : val φ (interConvOf (F i) (F i₀)) = 0 := by
        apply val_eq_zero_of_not_nonempty
        intro h
        rcases h with ⟨x, hx⟩
        exact hFi ⟨x, hx.1⟩
      rw [hseq, hlim0]
      exact tendsto_const_nhds
  -- discrepancy tends to the limit discrepancy, but the sequence is constant hd ≠ 0
  have hlim_discr : Tendsto (fun r => discr φ (Um r) (Fm r)) atTop
      (𝓝 (discr φ (F i₀) (fun i => interConvOf (F i) (F i₀)))) := by
    have hfamT : Tendsto (fun r => famVal φ (Fm r)) atTop
        (𝓝 (famVal φ (fun i => interConvOf (F i) (F i₀)))) := by
      have hsum := tendsto_finset_sum (s := (Finset.univ : Finset ι))
          (f := fun i r => val φ (Fm r i)) (x := Filter.atTop)
          (a := fun i => val φ (interConvOf (F i) (F i₀))) (by
            intro i hi
            exact hpiece_lim i)
      simpa [famVal] using hsum
    have hT := Filter.Tendsto.sub hunt hfamT
    simpa [discr] using hT
  have heq : discr φ U F = discr φ (F i₀) (fun i => interConvOf (F i) (F i₀)) := by
    have hcq : (fun r => discr φ (Um r) (Fm r)) = fun _ : ℕ => discr φ U F := by
      funext r
      exact hconst r
    have hcT : Tendsto (fun r => discr φ (Um r) (Fm r)) atTop (𝓝 (discr φ U F)) := by
      rw [hcq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hcT hlim_discr
  -- the limit discrepancy is zero: designated piece contributes val D, others are zero
  have hfinal : discr φ (F i₀) (fun i => interConvOf (F i) (F i₀)) = 0 := by
    unfold discr famVal
    have hsum : (∑ i, val φ (interConvOf (F i) (F i₀))) = val φ (F i₀) := by
      rw [Finset.sum_eq_single i₀]
      · apply val_eq_of_set_eq_conv
        rw [coe_interConvOf]
        ext x
        constructor
        · intro hx
          exact hx.1
        · intro hx
          exact ⟨hx, hx⟩
      · intro b hb hbne
        apply val_zero_of_interior_empty φ hsimple (interConvOf (F b) (F i₀))
        rw [coe_interConvOf]
        exact hpair b i₀ hbne
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ i₀))
    rw [hsum]
    ring
  exact hd (by rw [heq, hfinal])

/-- For a simple valuation the discrepancy vanishes over any dissection, by
strong induction on the number of nonempty pieces. -/
theorem discr_eq_zero
    (φ : ConvexBody V → ℝ)
    (hcont : Continuous φ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0) :
    ∀ {ι : Type*} [Fintype ι] (U : Conv V) (F : ι → Conv V),
      ((U : Set V) = ⋃ i, (F i : Set V)) →
      (∀ i j, i ≠ j → interior ((F i : Set V) ∩ (F j : Set V)) = ∅) →
      discr φ U F = 0 := by
  classical
  intro ι _ι U F hcov hpair
  have step : ∀ (m : ℕ),
      (∀ k < m, ∀ (U' : Conv V) (F' : ι → Conv V),
        cnt F' ≤ k → ((U' : Set V) = ⋃ i, (F' i : Set V)) →
        (∀ i j, i ≠ j → interior ((F' i : Set V) ∩ (F' j : Set V)) = ∅) →
        discr φ U' F' = 0) →
      ∀ (U' : Conv V) (F' : ι → Conv V),
        cnt F' ≤ m → ((U' : Set V) = ⋃ i, (F' i : Set V)) →
        (∀ i j, i ≠ j → interior ((F' i : Set V) ∩ (F' j : Set V)) = ∅) →
        discr φ U' F' = 0 := by
    intro m ihn U' F' hcnt hcov' hpair'
    by_cases hz : cnt F' = 0
    · -- base: all pieces empty, so U' = ∅
      have hU : (U' : Set V) = ∅ := by
        apply subset_antisymm
        · intro x hx
          rw [hcov'] at hx
          rcases (Set.mem_iUnion.mp hx) with ⟨i, hxi⟩
          have hfi : (F' i : Set V).Nonempty := ⟨x, hxi⟩
          have : 1 ≤ cnt F' := by
            unfold cnt
            have hmem : i ∈ Finset.univ.filter (fun j => (F' j : Set V).Nonempty) := by
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ i, hfi⟩
            have hcard : 0 < (Finset.univ.filter (fun j => (F' j : Set V).Nonempty)).card :=
              Finset.card_pos.mpr ⟨i, hmem⟩
            omega
          omega
        · simp
      have hvalU : val φ U' = 0 := by
        apply val_eq_zero_of_not_nonempty
        rw [hU]
        exact Set.not_nonempty_empty
      have hfam : famVal φ F' = 0 := by
        unfold famVal
        apply Finset.sum_eq_zero
        intro i hi
        have hempty : ¬(F' i : Set V).Nonempty := by
          intro hne
          have : 1 ≤ cnt F' := by
            unfold cnt
            have hmem : i ∈ Finset.univ.filter (fun j => (F' j : Set V).Nonempty) := by
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ i, hne⟩
            have hcard : 0 < (Finset.univ.filter (fun j => (F' j : Set V).Nonempty)).card :=
              Finset.card_pos.mpr ⟨i, hmem⟩
            omega
          omega
        exact val_eq_zero_of_not_nonempty φ (F' i) hempty
      unfold discr
      rw [hvalU, hfam]
      simp
    · -- inductive step: squeeze to one piece
      have hnpos : 0 < cnt F' := by omega
      rcases exists_nonempty_of_cnt_pos F' hnpos with ⟨i₀, hne₀⟩
      by_contra hd
      exact squeeze_step φ hcont hadd hsimple U' F' i₀ hne₀ hcov' hpair' hd hcnt ihn

  have hall : ∀ (m : ℕ) (U' : Conv V) (F' : ι → Conv V),
      cnt F' ≤ m → ((U' : Set V) = ⋃ i, (F' i : Set V)) →
      (∀ i j, i ≠ j → interior ((F' i : Set V) ∩ (F' j : Set V)) = ∅) →
      discr φ U' F' = 0 := fun m => Nat.strong_induction_on m step
  exact hall (cnt F) U F le_rfl hcov hpair

end MainDescent

theorem dissection_additivity
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V]
    (φ : ConvexBody V → ℝ)
    (hcont : Continuous φ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0)
    {ι : Type*} [Fintype ι] (P : ConvexBody V) (A : ι → ConvexBody V)
    (hcover : (P : Set V) = ⋃ i : ι, (A i : Set V))
    (hpair : ∀ i j : ι, i ≠ j → interior ((A i : Set V) ∩ (A j : Set V)) = ∅) :
    φ P = ∑ i : ι, φ (A i) := by
  -- view the dissection as a family of `Conv` pieces and apply the main theorem
  have hcov' : ((Conv.ofBody P : Conv V) : Set V) = ⋃ i, ((Conv.ofBody (A i) : Conv V) : Set V) := by
    rw [Conv.coe_ofBody]
    exact hcover
  have hpair' : ∀ i j : ι, i ≠ j →
      interior (((Conv.ofBody (A i) : Conv V) : Set V) ∩ ((Conv.ofBody (A j) : Conv V) : Set V)) = ∅ := by
    intro i j hij
    rw [Conv.coe_ofBody, Conv.coe_ofBody]
    exact hpair i j hij
  have hdiscr : discr φ (Conv.ofBody P) (fun i => Conv.ofBody (A i)) = 0 := by
    exact discr_eq_zero φ hcont hadd hsimple (U := Conv.ofBody P) (F := fun i => Conv.ofBody (A i))
      hcov' hpair'
  unfold discr famVal at hdiscr
  have hvalP : val φ (Conv.ofBody P) = φ P := val_ofBody φ P
  have hvalA : (∑ i, val φ (Conv.ofBody (A i))) = ∑ i, φ (A i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact val_ofBody φ (A i)
  rw [hvalP, hvalA] at hdiscr
  linarith

end Commons.Geometry.Convex.Hadwiger