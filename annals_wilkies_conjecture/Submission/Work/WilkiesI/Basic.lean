/-
Area I, part 1: the semialgebraicity toolbox.

`IsSemialgebraic X` (defined in `ChallengeDeps`, frozen) is definability in the language of
rings over `ℝ` with all of `ℝ` as parameters.  This file collects the closure properties and
the concrete examples (polynomial (in)equalities, coordinate boxes) that area I -- and any
other area that needs to produce a semialgebraic set -- consumes.

The main results are
* `definable_eval_eq`, `definable_eval_pos`, `definable_eval_lt`, `definable_eval_le`
  (`Set.Definable`-flavoured, for an arbitrary index type `σ`), with `IsSemialgebraic`
  corollaries `isSemialgebraic_eval_*` for `σ = Fin n`;
* `isSemialgebraic_box` and `isSemialgebraic_eBox`:  coordinate boxes are semialgebraic.
-/
import Submission.Work.Wilkies.Defs
import Mathlib.ModelTheory.Algebra.Ring.Definability

set_option autoImplicit false
noncomputable section
open Classical
open FirstOrder FirstOrder.Language

namespace Work.WilkiesI

open WilkiesConjecture

variable {n : ℕ}

/-! ## 1. Boolean closure -/

theorem isSemialgebraic_empty : IsSemialgebraic (∅ : Set (Fin n → ℝ)) := Set.definable_empty

theorem isSemialgebraic_univ : IsSemialgebraic (Set.univ : Set (Fin n → ℝ)) :=
  Set.definable_univ

theorem isSemialgebraic_inter {s t : Set (Fin n → ℝ)} (hs : IsSemialgebraic s)
    (ht : IsSemialgebraic t) : IsSemialgebraic (s ∩ t) := Set.Definable.inter hs ht

theorem isSemialgebraic_union {s t : Set (Fin n → ℝ)} (hs : IsSemialgebraic s)
    (ht : IsSemialgebraic t) : IsSemialgebraic (s ∪ t) := Set.Definable.union hs ht

theorem isSemialgebraic_compl {s : Set (Fin n → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic sᶜ := Set.Definable.compl hs

theorem isSemialgebraic_sdiff {s t : Set (Fin n → ℝ)} (hs : IsSemialgebraic s)
    (ht : IsSemialgebraic t) : IsSemialgebraic (s \ t) := Set.Definable.sdiff hs ht

theorem isSemialgebraic_iInter {ι : Type*} [Finite ι] {s : ι → Set (Fin n → ℝ)}
    (h : ∀ i, IsSemialgebraic (s i)) : IsSemialgebraic (⋂ i, s i) :=
  Set.definable_iInter_of_finite h

theorem isSemialgebraic_iUnion {ι : Type*} [Finite ι] {s : ι → Set (Fin n → ℝ)}
    (h : ∀ i, IsSemialgebraic (s i)) : IsSemialgebraic (⋃ i, s i) :=
  Set.definable_iUnion_of_finite h

/-! ## 2. Polynomials: zero sets and inequalities

The key point is that the language of rings has *no* relation symbols, but over `ℝ` order is
already definable from `=`,`+`,`*`:  `0 < a ↔ ∃ b, a * b * b = 1`.  This gives strict
inequalities with a single existential quantifier, hence every polynomial inequality set is
semialgebraic. -/

/-- `0 < a` is expressed in the language of rings by `∃ b, a * b * b = 1`.  (Taking
`b = √a⁻¹` for `a > 0`; for `a ≤ 0` the equation `a * b * b = 1` has no solution because
`b ≠ 0` would force `b * b > 0`.)  This is what makes order available without adding a
relation symbol to the language. -/
theorem lt_iff_exists_mul_self_eq_one {a : ℝ} : 0 < a ↔ ∃ b : ℝ, a * b * b = 1 := by
  constructor
  · intro ha
    refine ⟨Real.sqrt a⁻¹, ?_⟩
    have h1 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
    have h2 : Real.sqrt a⁻¹ * Real.sqrt a⁻¹ = a⁻¹ := by rw [← pow_two, Real.sq_sqrt h1]
    calc a * Real.sqrt a⁻¹ * Real.sqrt a⁻¹
        = a * (Real.sqrt a⁻¹ * Real.sqrt a⁻¹) := by ring
      _ = a * a⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel₀ (ne_of_gt ha)
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by rintro rfl; norm_num at hb
    have hb2 : 0 < b * b := mul_self_pos.mpr hb0
    have h : a * (b * b) = 1 := by rw [← mul_assoc]; exact hb
    have ha : a = 1 / (b * b) := (eq_div_iff hb2.ne').mpr h
    rw [ha]
    exact div_pos one_pos hb2

/-- Every polynomial equation `P x = c` defines a semialgebraic set. -/
theorem definable_eval_eq {σ : Type*} (P : MvPolynomial σ ℝ) (c : ℝ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring
      {x : σ → ℝ | (MvPolynomial.eval x) P = c} := by
  have h := FirstOrder.Ring.mvPolynomial_zeroLocus_definable (K := ℝ)
    ({P - MvPolynomial.C c} : Finset (MvPolynomial σ ℝ))
  have h' := h.mono (Set.subset_univ _)
  have hset : {x : σ → ℝ |
        ∀ p ∈ (↑({P - MvPolynomial.C c} : Finset (MvPolynomial σ ℝ)) : Set (MvPolynomial σ ℝ)),
          (MvPolynomial.aeval x) p = 0}
      = {x : σ → ℝ | (MvPolynomial.eval x) P = c} := by
    ext x
    simp [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_C, sub_eq_zero]
  rw [MvPolynomial.zeroLocus_span, hset] at h'
  exact h'

/-- Every polynomial inequality `0 < P x` defines a semialgebraic set. -/
theorem definable_eval_pos {σ : Type*} (Q : MvPolynomial σ ℝ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring
      {x : σ → ℝ | 0 < (MvPolynomial.eval x) Q} := by
  have hset : {x : σ → ℝ | 0 < (MvPolynomial.eval x) Q}
      = {v : σ → ℝ | ∃ u : Fin 1 → ℝ, (MvPolynomial.eval v) Q * u 0 * u 0 = 1} := by
    ext v
    constructor
    · intro hv
      obtain ⟨b, hb⟩ := lt_iff_exists_mul_self_eq_one.mp hv
      exact ⟨fun _ => b, hb⟩
    · rintro ⟨u, hu⟩
      exact lt_iff_exists_mul_self_eq_one.mpr ⟨u 0, hu⟩
  rw [hset]
  have hS : Set.Definable (Set.univ : Set ℝ) Language.ring
      {w : (σ ⊕ Fin 1) → ℝ | (MvPolynomial.eval w)
        (MvPolynomial.rename Sum.inl Q * MvPolynomial.X (Sum.inr (0 : Fin 1)) *
          MvPolynomial.X (Sum.inr (0 : Fin 1))) = 1} :=
    definable_eval_eq _ 1
  have h2 := Set.Definable.exists_of_finite hS
  convert h2 using 1
  ext v
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by simpa [MvPolynomial.eval_rename, MvPolynomial.eval_X, Sum.elim_inr,
      Sum.elim_comp_inl] using hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, by simpa [MvPolynomial.eval_rename, MvPolynomial.eval_X, Sum.elim_inr,
      Sum.elim_comp_inl] using hu⟩

/-- Every polynomial inequality `P x < c` defines a semialgebraic set. -/
theorem definable_eval_lt {σ : Type*} (P : MvPolynomial σ ℝ) (c : ℝ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring
      {x : σ → ℝ | (MvPolynomial.eval x) P < c} := by
  have hset : {x : σ → ℝ | (MvPolynomial.eval x) P < c}
      = {x : σ → ℝ | 0 < (MvPolynomial.eval x) (MvPolynomial.C c - P)} := by
    ext x
    simp [MvPolynomial.eval_C, sub_pos]
  rw [hset]
  exact definable_eval_pos _

/-- Every polynomial inequality `c < P x` defines a semialgebraic set. -/
theorem definable_eval_gt {σ : Type*} (P : MvPolynomial σ ℝ) (c : ℝ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring
      {x : σ → ℝ | c < (MvPolynomial.eval x) P} := by
  have hset : {x : σ → ℝ | c < (MvPolynomial.eval x) P}
      = {x : σ → ℝ | 0 < (MvPolynomial.eval x) (P - MvPolynomial.C c)} := by
    ext x
    simp [MvPolynomial.eval_C, sub_pos]
  rw [hset]
  exact definable_eval_pos _

/-- Every polynomial inequality `P x ≤ c` defines a semialgebraic set. -/
theorem definable_eval_le {σ : Type*} (P : MvPolynomial σ ℝ) (c : ℝ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring
      {x : σ → ℝ | (MvPolynomial.eval x) P ≤ c} := by
  have hset : {x : σ → ℝ | (MvPolynomial.eval x) P ≤ c}
      = ({x : σ → ℝ | c < (MvPolynomial.eval x) P})ᶜ := by
    ext x
    simp [not_lt]
  rw [hset]
  exact (definable_eval_gt P c).compl

/-- Every polynomial inequality `c ≤ P x` defines a semialgebraic set. -/
theorem definable_eval_ge {σ : Type*} (P : MvPolynomial σ ℝ) (c : ℝ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring
      {x : σ → ℝ | c ≤ (MvPolynomial.eval x) P} := by
  have hset : {x : σ → ℝ | c ≤ (MvPolynomial.eval x) P}
      = ({x : σ → ℝ | (MvPolynomial.eval x) P < c})ᶜ := by
    ext x
    simp [not_lt]
  rw [hset]
  exact (definable_eval_lt P c).compl

/-- The complement of a polynomial hypersurface is semialgebraic. -/
theorem definable_eval_ne {σ : Type*} (P : MvPolynomial σ ℝ) (c : ℝ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring
      {x : σ → ℝ | (MvPolynomial.eval x) P ≠ c} :=
  (definable_eval_eq P c).compl

/-! ### `IsSemialgebraic` corollaries -/

theorem isSemialgebraic_eval_eq (P : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | (MvPolynomial.eval x) P = c} := definable_eval_eq P c

theorem isSemialgebraic_eval_pos (Q : MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | 0 < (MvPolynomial.eval x) Q} := definable_eval_pos Q

theorem isSemialgebraic_eval_lt (P : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | (MvPolynomial.eval x) P < c} := definable_eval_lt P c

theorem isSemialgebraic_eval_gt (P : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | c < (MvPolynomial.eval x) P} := definable_eval_gt P c

theorem isSemialgebraic_eval_le (P : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | (MvPolynomial.eval x) P ≤ c} := definable_eval_le P c

theorem isSemialgebraic_eval_ge (P : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | c ≤ (MvPolynomial.eval x) P} := definable_eval_ge P c

theorem isSemialgebraic_eval_ne (P : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | (MvPolynomial.eval x) P ≠ c} := definable_eval_ne P c

/-! ## 3. Coordinate half-spaces, boxes -/

theorem isSemialgebraic_coord_lt (i : Fin n) (a : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | x i < a} := by
  have h : {x : Fin n → ℝ | x i < a}
      = {x : Fin n → ℝ | (MvPolynomial.eval x) (MvPolynomial.X i) < a} := by
    ext x
    simp
  rw [h]
  exact definable_eval_lt _ _

theorem isSemialgebraic_coord_eq (i : Fin n) (a : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | x i = a} := by
  have h : {x : Fin n → ℝ | x i = a}
      = {x : Fin n → ℝ | (MvPolynomial.eval x) (MvPolynomial.X i) = a} := by
    ext x
    simp
  rw [h]
  exact definable_eval_eq _ _

theorem isSemialgebraic_coord_gt (i : Fin n) (a : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | a < x i} := by
  have h : {x : Fin n → ℝ | a < x i}
      = {x : Fin n → ℝ | 0 < (MvPolynomial.eval x) (MvPolynomial.X i - MvPolynomial.C a)} := by
    ext x
    simp [MvPolynomial.eval_C, sub_pos]
  rw [h]
  exact definable_eval_pos _

theorem isSemialgebraic_coord_le (i : Fin n) (a : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | x i ≤ a} := by
  have h : {x : Fin n → ℝ | x i ≤ a}
      = ({x : Fin n → ℝ | a < x i})ᶜ := by
    ext x
    simp [not_lt]
  rw [h]
  exact (isSemialgebraic_coord_gt i a).compl

theorem isSemialgebraic_coord_ge (i : Fin n) (a : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | a ≤ x i} := by
  have h : {x : Fin n → ℝ | a ≤ x i}
      = ({x : Fin n → ℝ | x i < a})ᶜ := by
    ext x
    simp [not_lt]
  rw [h]
  exact (isSemialgebraic_coord_lt i a).compl

/-- The coordinate slab `|x i - b| < a`. -/
theorem isSemialgebraic_abs_sub_lt (i : Fin n) (b a : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | |x i - b| < a} := by
  have h : {x : Fin n → ℝ | |x i - b| < a}
      = ({x : Fin n → ℝ | b - a < x i} ∩ {x : Fin n → ℝ | x i < b + a}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  rw [h]
  exact isSemialgebraic_inter (isSemialgebraic_coord_gt i (b - a))
    (isSemialgebraic_coord_lt i (b + a))

/-- The coordinate slab `|x i - b| ≤ a`. -/
theorem isSemialgebraic_abs_sub_le (i : Fin n) (b a : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | |x i - b| ≤ a} := by
  have h : {x : Fin n → ℝ | |x i - b| ≤ a}
      = ({x : Fin n → ℝ | b - a ≤ x i} ∩ {x : Fin n → ℝ | x i ≤ b + a}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  rw [h]
  exact isSemialgebraic_inter (isSemialgebraic_coord_ge i (b - a))
    (isSemialgebraic_coord_le i (b + a))

/-- The open coordinate box of radius `δ` around `p`.  This is the set called
`{x | ∀ i, |x i - p i| < δ}` in the area I statement. -/
def boxAt (p : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) := {x | ∀ i, |x i - p i| < δ}

theorem mem_boxAt {p x : Fin n → ℝ} {δ : ℝ} : x ∈ boxAt p δ ↔ ∀ i, |x i - p i| < δ :=
  Iff.rfl

theorem isSemialgebraic_boxAt (p : Fin n → ℝ) (δ : ℝ) :
    IsSemialgebraic (boxAt p δ) := by
  have h : boxAt p δ = ⋂ i, {x : Fin n → ℝ | |x i - p i| < δ} := by
    ext x
    simp [boxAt]
  rw [h]
  exact isSemialgebraic_iInter fun i => isSemialgebraic_abs_sub_lt i (p i) δ

/-- The open coordinate box `{x | ∀ i, |x i - p i| < δ}` is indeed the area I box. -/
theorem isSemialgebraic_box (p : Fin n → ℝ) (δ : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | ∀ i, |x i - p i| < δ} := isSemialgebraic_boxAt p δ

/-- The `e`-slice box: the set of `x` whose `e`-coordinates form a box of radius `η` around
those of `p`.  This is the intersection of the box condition with the (semialgebraic)
preimage of a box under the coordinate projection. -/
theorem isSemialgebraic_eBox {μ : ℕ} (e : Fin μ ↪ Fin n) (p : Fin n → ℝ) (η : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | ∀ j, |x (e j) - p (e j)| < η} := by
  have h : {x : Fin n → ℝ | ∀ j, |x (e j) - p (e j)| < η}
      = ⋂ j, {x : Fin n → ℝ | |x (e j) - p (e j)| < η} := by
    ext x
    simp
  rw [h]
  exact isSemialgebraic_iInter fun j => isSemialgebraic_abs_sub_lt (e j) (p (e j)) η

/-- The finite unit cube `[0,1]^n` (the frozen `WilkiesDesign.cube01`) is semialgebraic. -/
theorem isSemialgebraic_cube01 (n : ℕ) : IsSemialgebraic (WilkiesDesign.cube01 n) := by
  have h : WilkiesDesign.cube01 n
      = ⋂ i, {x : Fin n → ℝ | x i ∈ Set.Icc (0 : ℝ) 1} := by
    ext x
    simp [WilkiesDesign.cube01, Set.mem_Icc]
  rw [h]
  refine isSemialgebraic_iInter fun i => ?_
  have h2 : {x : Fin n → ℝ | x i ∈ Set.Icc (0 : ℝ) 1}
      = ({x : Fin n → ℝ | 0 ≤ x i} ∩ {x : Fin n → ℝ | x i ≤ 1}) := by
    ext x
    simp [Set.mem_Icc]
  rw [h2]
  exact isSemialgebraic_inter (isSemialgebraic_coord_ge i 0) (isSemialgebraic_coord_le i 1)

/-! ## 4. Images and preimages along coordinate maps -/

/-- Pulling a definable set back along a coordinate projection preserves definability.  If
`s ⊆ ℝ^α` is definable and `f : α → β`, then `{g : β → ℝ | g ∘ f ∈ s}` is definable. -/
theorem definable_preimage_comp {α β : Type*} {s : Set (α → ℝ)}
    (hs : Set.Definable (Set.univ : Set ℝ) Language.ring s) (f : α → β) :
    Set.Definable (Set.univ : Set ℝ) Language.ring ((fun g : β → ℝ => g ∘ f) ⁻¹' s) :=
  hs.preimage_comp f

/-- Pushing a definable set forward along a coordinate projection (finite index types)
preserves definability.  If `s ⊆ ℝ^β` is definable and `f : α → β` with `α`, `β` finite,
then `{g ∘ f | g ∈ s} ⊆ ℝ^α` is definable. -/
theorem definable_image_comp {α β : Type*} [Finite α] [Finite β] {s : Set (β → ℝ)}
    (hs : Set.Definable (Set.univ : Set ℝ) Language.ring s) (f : α → β) :
    Set.Definable (Set.univ : Set ℝ) Language.ring ((fun g : β → ℝ => g ∘ f) '' s) :=
  hs.image_comp f

/-- The projection throwing away the last coordinate of a semialgebraic set is
semialgebraic. -/
theorem isSemialgebraic_image_init {m : ℕ} {s : Set (Fin (m + 1) → ℝ)}
    (hs : IsSemialgebraic s) : IsSemialgebraic (Fin.init '' s) :=
  hs.image_comp Fin.castSucc

/-! ## 5. Further shapes: closed boxes, cylinders, graphs, projections -/

/-- The common zero set of a finite family of polynomials is semialgebraic. -/
theorem isSemialgebraic_zeroLocus {ι : Type*} [Finite ι] (P : ι → MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | ∀ i, (MvPolynomial.eval x) (P i) = 0} := by
  have h : {x : Fin n → ℝ | ∀ i, (MvPolynomial.eval x) (P i) = 0}
      = ⋂ i, {x : Fin n → ℝ | (MvPolynomial.eval x) (P i) = 0} := by
    ext x
    simp
  rw [h]
  exact isSemialgebraic_iInter fun i => isSemialgebraic_eval_eq (P i) 0

/-- The closed coordinate box `{x | ∀ i, |x i - p i| ≤ δ}` is semialgebraic. -/
theorem isSemialgebraic_closedBox (p : Fin n → ℝ) (δ : ℝ) :
    IsSemialgebraic {x : Fin n → ℝ | ∀ i, |x i - p i| ≤ δ} := by
  have h : {x : Fin n → ℝ | ∀ i, |x i - p i| ≤ δ}
      = ⋂ i, {x : Fin n → ℝ | |x i - p i| ≤ δ} := by
    ext x
    simp
  rw [h]
  exact isSemialgebraic_iInter fun i => isSemialgebraic_abs_sub_le i (p i) δ

/-- A cylinder over a definable set of `e`-coordinates is semialgebraic. -/
theorem isSemialgebraic_cylinder {μ : ℕ} (e : Fin μ ↪ Fin n) {T : Set (Fin μ → ℝ)}
    (hT : Set.Definable (Set.univ : Set ℝ) Language.ring T) :
    IsSemialgebraic {x : Fin n → ℝ | x ∘ e ∈ T} :=
  hT.preimage_comp e

/-- The graph of a polynomial function is semialgebraic. -/
theorem isSemialgebraic_graphOf_eval {m : ℕ} (P : MvPolynomial (Fin m) ℝ) :
    IsSemialgebraic (WilkiesDesign.graphOf (fun x : Fin m → ℝ => (MvPolynomial.eval x) P)) := by
  have h : WilkiesDesign.graphOf (fun x : Fin m → ℝ => (MvPolynomial.eval x) P)
      = {z : Fin (m + 1) → ℝ | (MvPolynomial.eval z)
          (MvPolynomial.X (Fin.last m) - MvPolynomial.rename Fin.castSucc P) = 0} := by
    ext z
    simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq]
    rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_rename, sub_eq_zero]
    rfl
  rw [h]
  exact definable_eval_eq _ 0

/-- The projection dropping the last coordinate of a semialgebraic set is semialgebraic
(`WilkiesDesign.projLast`, with an existential quantifier over the dropped coordinate). -/
theorem isSemialgebraic_projLast {m : ℕ} {A : Set (Fin (m + 1) → ℝ)} (hA : IsSemialgebraic A) :
    IsSemialgebraic (WilkiesDesign.projLast A) := by
  have hsnoc : ∀ g : Fin (m + 1) → ℝ, Fin.snoc (g ∘ Fin.castSucc) (g (Fin.last m)) = g := by
    intro g
    have h := Fin.snoc_init_self g
    rwa [Fin.init_def] at h
  have h : WilkiesDesign.projLast A
      = (fun g : Fin (m + 1) → ℝ => g ∘ Fin.castSucc) '' A := by
    ext x
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨Fin.snoc x t, ht, Fin.snoc_comp_castSucc (f := x) (a := t)⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g (Fin.last m), by rw [hsnoc g]; exact hg⟩
  rw [h]
  exact hA.image_comp Fin.castSucc

/-- The section of a semialgebraic set at a prescribed value of the last coordinate is
semialgebraic (as a subset of `ℝ^m`).  This is the shape of the boundary functions of
cylindrical cells. -/
theorem isSemialgebraic_section_last {m : ℕ} {A : Set (Fin (m + 1) → ℝ)}
    (hA : IsSemialgebraic A) (a : ℝ) :
    IsSemialgebraic {t : Fin m → ℝ | Fin.snoc t a ∈ A} := by
  have h : {t : Fin m → ℝ | Fin.snoc t a ∈ A}
      = Fin.init '' (A ∩ {x : Fin (m + 1) → ℝ | x (Fin.last m) = a}) := by
    ext t
    constructor
    · intro ht
      refine ⟨(Fin.snoc (α := fun _ => ℝ) t a),
        ⟨by simpa using ht, by simp [Fin.snoc_last]⟩, ?_⟩
      funext i
      simp
    · rintro ⟨x, ⟨hxA, hxa⟩, hxt⟩
      have hx : x = Fin.snoc t a := by
        rw [← hxt, ← hxa]
        exact (Fin.snoc_init_self x).symm
      rw [hx] at hxA
      exact hxA
  rw [h]
  exact isSemialgebraic_image_init (isSemialgebraic_inter hA
    (isSemialgebraic_coord_eq (Fin.last m) a))

end Work.WilkiesI
