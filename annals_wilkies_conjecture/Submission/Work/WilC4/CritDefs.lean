/-
  WilC4/CritDefs : the vocabulary of `Work.WilC4.ulpm_crit`.

  `ulpm_crit` (see `Submission/Work/WilC4/ulpm_crit.lean`) needs a `∅`-definable breakpoint
  family `B ⊆ ℝ^{k+1}` for a `∅`-definable family of graphs `Y ⊆ ℝ^{k+2}` such that on every
  interval `(a,b)` avoiding `B_c`:

  * the domain `{x | ∃y, (x,y) ∈ Y_c}` is all of `(a,b)` or disjoint from it,
  * the zero set `{x | (x,0) ∈ Y_c}` is all of `(a,b)` or disjoint from it,
  * the fibre map `x ↦ y` is continuous on `(a,b)`.

  The natural choice is `B := BndDom ∪ BndZero ∪ Bad`, where

  * `BndDom`, `BndZero` are the families of topological boundary points (`Work.WilC2.IsBnd`) of
    the domain and of the zero set of the fibre;
  * `Bad` collects the points at which the fibre map is *one-sidedly far* from its value: either
    all values on a right neighbourhood exceed `f x + ε`, or all fall below `f x - ε`, or the same
    on a left neighbourhood.  Every point at which `f` fails to be continuous (and at which `f` is
    defined on a neighbourhood) is of one of those four types, and conversely the four types are
    finite on every fibre: an interval of one type would force the fibre map to be monotone there
    (via the o-minimal germ analysis) with a "jump" at every point, producing arbitrarily long
    `AltChain`s in the image of the restriction of `f` to that interval, contradicting the uniform
    finiteness of the image family.

  This file only *defines* the objects and proves the elementary order-theoretic/o-minimality
  lemmas about them (the covering dichotomy for finite unions of order convex sets, the
  accumulation dichotomy, and the elementary "boundary dichotomy" for the domain).  All the
  definability/finiteness statements about the families above are proved in sibling files.

  Conventions.  A point of `ℝ^{k+1}` is a tuple `v` with `v 0 = x` (the point of the line) and
  `v (i+1) = c i` (the parameters); `tup v` extracts the parameter tuple.  A point of `ℝ^{k+2}` is
  a tuple `(x, y, c)` written `Fin.cons x (Fin.cons y c)`.
-/
import Mathlib
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC2.BndDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-! ## 1. The value relation and the fibre -/

/-- The value relation of the family `Y` at the parameter tuple `c`: `y` is a value of the fibre
of `Y` at `(c, x)`. -/
def CGr (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x y : ℝ) : Prop :=
  Fin.cons x (Fin.cons y c) ∈ Y

/-- The fibre of the family at `c`, in the two-variable shape used by the monotonicity library
(`MonoDom`, `MonoW`, `MonoLm`, …). -/
def Cfib (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : Set (Fin 2 → ℝ) :=
  {w | CGr Y c (w 0) (w 1)}

/-- The parameter tuple carried by a point of `ℝ^{k+1}`. -/
def tup (v : Fin (k + 1) → ℝ) : Fin k → ℝ := fun i => v i.succ

/-- The domain of the fibre at `c`. -/
def DomFib (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : Set ℝ :=
  {x | ∃ y : ℝ, CGr Y c x y}

/-- The zero set of the fibre at `c`. -/
def ZeroFib (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : Set ℝ :=
  {x | CGr Y c x 0}

/-- The image of the fibre over the interval `(a,b)`. -/
def ImFib (Y : Set (Fin (k + 2) → ℝ)) (a b : ℝ) (c : Fin k → ℝ) : Set ℝ :=
  {y | ∃ x : ℝ, a < x ∧ x < b ∧ CGr Y c x y}

@[simp] lemma mem_cfib {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {w : Fin 2 → ℝ} :
    w ∈ Cfib Y c ↔ CGr Y c (w 0) (w 1) := Iff.rfl

lemma mem_cfib_cons {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x y : ℝ} :
    ![x, y] ∈ Cfib Y c ↔ CGr Y c x y := by
  simp [Cfib, CGr]

@[simp] lemma tup_cons (x : ℝ) (c : Fin k → ℝ) :
    tup (Fin.cons x c) = c := by
  funext i
  simp [tup]

@[simp] lemma cons_tup (v : Fin (k + 1) → ℝ) : Fin.cons (v 0) (tup v) = v := by
  funext i
  induction i using Fin.cases with
  | zero => simp [tup]
  | succ j => simp [tup]

/-! ## 2. The boundary families -/

/-- The family of boundary points of the domains of the fibres. -/
def BndDom (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | WilC2.IsBnd (DomFib Y (tup v)) (v 0)}

/-- The family of boundary points of the zero sets of the fibres. -/
def BndZero (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | WilC2.IsBnd (ZeroFib Y (tup v)) (v 0)}

@[simp] lemma mem_bndDom {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 1) → ℝ} :
    v ∈ BndDom Y ↔ WilC2.IsBnd (DomFib Y (tup v)) (v 0) := Iff.rfl

@[simp] lemma mem_bndZero {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 1) → ℝ} :
    v ∈ BndZero Y ↔ WilC2.IsBnd (ZeroFib Y (tup v)) (v 0) := Iff.rfl

/-! ## 3. The one-sided bad families -/

/-- `IntDom Y c x`: the fibre of `Y` at `c` is defined on a neighbourhood of `x`. -/
def IntDom (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, x - δ < t → t < x + δ → ∃ w : ℝ, CGr Y c t w

/-- The family of points at which the fibre is defined on a neighbourhood. -/
def IntDomFam (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | IntDom Y (tup v) (v 0)}

/-- `BadRU`: to the right of `x`, every value of the fibre exceeds the value at `x`. -/
def BadRU (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | IntDom Y (tup v) (v 0) ∧ ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y (tup v) (v 0) y ∧
    ∀ t : ℝ, v 0 < t → t < v 0 + δ → ∀ w : ℝ, CGr Y (tup v) t w → y + ε ≤ w}

/-- `BadRD`: to the right of `x`, every value of the fibre is below the value at `x`. -/
def BadRD (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | IntDom Y (tup v) (v 0) ∧ ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y (tup v) (v 0) y ∧
    ∀ t : ℝ, v 0 < t → t < v 0 + δ → ∀ w : ℝ, CGr Y (tup v) t w → w + ε ≤ y}

/-- `BadLU`: to the left of `x`, every value of the fibre exceeds the value at `x`. -/
def BadLU (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | IntDom Y (tup v) (v 0) ∧ ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y (tup v) (v 0) y ∧
    ∀ t : ℝ, v 0 - δ < t → t < v 0 → ∀ w : ℝ, CGr Y (tup v) t w → y + ε ≤ w}

/-- `BadLD`: to the left of `x`, every value of the fibre is below the value at `x`. -/
def BadLD (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | IntDom Y (tup v) (v 0) ∧ ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y (tup v) (v 0) y ∧
    ∀ t : ℝ, v 0 - δ < t → t < v 0 → ∀ w : ℝ, CGr Y (tup v) t w → w + ε ≤ y}

/-- The family of one-sidedly bad points. -/
def Bad (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  BadRU Y ∪ BadRD Y ∪ BadLU Y ∪ BadLD Y

/-- The image family, as a subset of `ℝ^{k+3}` with coordinates `(y, a, b, c)`. -/
def ImFam (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 3) → ℝ) :=
  {v | ∃ x : ℝ, v 1 < x ∧ x < v 2 ∧ CGr Y (fun i => v i.succ.succ.succ) x (v 0)}

/-- The image family, as an `ℝ^{k+3}`-family in the parameters `(a, b, c)`. -/
def ImFam2 (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 3) → ℝ) :=
  {w | ∃ x : ℝ, w 1 < x ∧ x < w 2 ∧ CGr Y (fun i => w i.succ.succ.succ) x (w 0)}

/-! ## 4. The parametric germ families -/

/-- The parametric `MonoDom` family. -/
def PMonoDom (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | v 0 ∈ MonoDom (Cfib Y (tup v))}

/-- The parametric `MonoW` family. -/
def PMonoW (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | v 0 ∈ MonoW (Cfib Y (tup v))}

/-- The parametric `MonoLm` family. -/
def PMonoLm (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | v 0 ∈ MonoLm (Cfib Y (tup v))}

/-- The parametric `MonoHm` family. -/
def PMonoHm (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | v 0 ∈ MonoHm (Cfib Y (tup v))}

/-- The parametric `MonoLp` family. -/
def PMonoLp (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | v 0 ∈ MonoLp (Cfib Y (tup v))}

/-- The parametric `MonoHp` family. -/
def PMonoHp (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | v 0 ∈ MonoHp (Cfib Y (tup v))}

/-- The parametric `MonoLA` family, a subset of `ℝ^{k+2}` with coordinates `(x, w, c)`. -/
def PMonoLA (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 2) → ℝ) :=
  {v | ![v 0, v 1] ∈ MonoLA (Cfib Y (fun i => v i.succ.succ))}

/-- The parametric `MonoHA` family, a subset of `ℝ^{k+2}` with coordinates `(x, w, c)`. -/
def PMonoHA (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 2) → ℝ) :=
  {v | ![v 0, v 1] ∈ MonoHA (Cfib Y (fun i => v i.succ.succ))}

@[simp] lemma mem_pMonoLm {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 1) → ℝ} :
    v ∈ PMonoLm Y ↔ v 0 ∈ MonoLm (Cfib Y (tup v)) := Iff.rfl

@[simp] lemma mem_pMonoHm {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 1) → ℝ} :
    v ∈ PMonoHm Y ↔ v 0 ∈ MonoHm (Cfib Y (tup v)) := Iff.rfl

@[simp] lemma mem_badRU {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 1) → ℝ} :
    v ∈ BadRU Y ↔ IntDom Y (tup v) (v 0) ∧ ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧
      CGr Y (tup v) (v 0) y ∧
      ∀ t : ℝ, v 0 < t → t < v 0 + δ → ∀ w : ℝ, CGr Y (tup v) t w → y + ε ≤ w := Iff.rfl

@[simp] lemma mem_badRD {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 1) → ℝ} :
    v ∈ BadRD Y ↔ IntDom Y (tup v) (v 0) ∧ ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧
      CGr Y (tup v) (v 0) y ∧
      ∀ t : ℝ, v 0 < t → t < v 0 + δ → ∀ w : ℝ, CGr Y (tup v) t w → w + ε ≤ y := Iff.rfl

@[simp] lemma mem_badLU {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 1) → ℝ} :
    v ∈ BadLU Y ↔ IntDom Y (tup v) (v 0) ∧ ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧
      CGr Y (tup v) (v 0) y ∧
      ∀ t : ℝ, v 0 - δ < t → t < v 0 → ∀ w : ℝ, CGr Y (tup v) t w → y + ε ≤ w := Iff.rfl

@[simp] lemma mem_badLD {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 1) → ℝ} :
    v ∈ BadLD Y ↔ IntDom Y (tup v) (v 0) ∧ ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧
      CGr Y (tup v) (v 0) y ∧
      ∀ t : ℝ, v 0 - δ < t → t < v 0 → ∀ w : ℝ, CGr Y (tup v) t w → w + ε ≤ y := Iff.rfl

@[simp] lemma mem_bad {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 1) → ℝ} :
    v ∈ Bad Y ↔ v ∈ BadRU Y ∨ v ∈ BadRD Y ∨ v ∈ BadLU Y ∨ v ∈ BadLD Y := by
  simp only [Bad, Set.mem_union]
  tauto

/-! ## 5. Elementary order-theoretic and o-minimality lemmas -/

/-- **Covering dichotomy.**  If the interval `(a,b)` is covered by a finite union of order convex
sets, then one of the pieces contains a nondegenerate subinterval of `(a,b)`. -/
theorem ordConnected_cover_subinterval {s : Finset (Set ℝ)} (hs : ∀ I ∈ s, I.OrdConnected)
    {a b : ℝ} (hab : a < b) (hsub : Set.Ioo a b ⊆ ⋃₀ (s : Set (Set ℝ))) :
    ∃ I ∈ s, ∃ u v : ℝ, a ≤ u ∧ u < v ∧ v ≤ b ∧ Set.Ioo u v ⊆ I := by
  by_contra hcon
  push_neg at hcon
  have hpt : ∀ I ∈ s, (I ∩ Set.Ioo a b).Subsingleton := by
    intro I hI
    intro x hx y hy
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · refine hcon I hI x y (le_of_lt hx.2.1) hlt (le_of_lt hy.2.2) fun t ht => ?_
      apply (hs I hI).out' hx.1 hy.1
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    · refine hcon I hI y x (le_of_lt hy.2.1) hlt (le_of_lt hx.2.2) fun t ht => ?_
      apply (hs I hI).out' hy.1 hx.1
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hfin : (Set.Ioo a b).Finite := by
    refine (s.finite_toSet.biUnion fun I hI => (hpt I hI).finite).subset ?_
    intro t ht
    obtain ⟨I, hI, htI⟩ := Set.mem_sUnion.mp (hsub ht)
    exact Set.mem_biUnion hI ⟨htI, ht⟩
  exact Set.Ioo_infinite hab hfin

/-- **Accumulation from the right.**  If a finite union `S` of order convex sets contains points
arbitrarily close to `x` on the right, then it contains a whole right neighbourhood of `x`. -/
theorem right_subinterval_of_accumulate {S : Set ℝ} {s : Finset (Set ℝ)}
    (hs : ∀ I ∈ s, I.OrdConnected) (hS : S = ⋃₀ (s : Set (Set ℝ))) {x : ℝ}
    (hacc : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, x < t ∧ t < x + δ ∧ t ∈ S) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ioo x (x + δ) ⊆ S := by
  by_cases hne : s.Nonempty
  swap
  · obtain ⟨t, -, -, ht⟩ := hacc 1 zero_lt_one
    rw [hS, Finset.not_nonempty_iff_eq_empty.mp hne] at ht
    simp at ht
  by_cases hacc' : ∃ I ∈ s, ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, x < t ∧ t < x + δ ∧ t ∈ I
  · obtain ⟨I, hI, hIacc⟩ := hacc'
    obtain ⟨t₀, hxt₀, -, ht₀I⟩ := hIacc 1 zero_lt_one
    refine ⟨t₀ - x, by linarith, fun t ht => ?_⟩
    rw [Set.mem_Ioo] at ht
    obtain ⟨t₁, hxt₁, ht₁t, ht₁I⟩ := hIacc (t - x) (by linarith)
    have hmem : t ∈ I := by
      apply (hs I hI).out' ht₁I ht₀I
      exact ⟨le_of_lt (by linarith [ht₁t]), le_of_lt (by linarith [ht.2])⟩
    rw [hS]
    exact Set.subset_sUnion_of_mem hI hmem
  · push_neg at hacc'
    have hex : ∀ I ∈ s, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, x < t → t < x + δ → t ∉ I := by
      intro I hI
      obtain ⟨δ, hδ, hδ'⟩ := hacc' I hI
      refine ⟨δ, hδ, ?_⟩
      intro t ht1 ht2 hmem
      exact hδ' t ht1 ht2 hmem
    let e : Set ℝ → ℝ := fun I => if hI : I ∈ s then Classical.choose (hex I hI) else 1
    have he : ∀ I ∈ s, 0 < e I ∧ ∀ t : ℝ, x < t → t < x + e I → t ∉ I := by
      intro I hI
      have h1 : e I = Classical.choose (hex I hI) := dif_pos hI
      rw [h1]
      exact Classical.choose_spec (hex I hI)
    have hne' : (s.image e).Nonempty := hne.image e
    set δ₀ : ℝ := (s.image e).min' hne' with hδ₀
    have hpos : 0 < δ₀ := by
      obtain ⟨I, hI, hIe⟩ := Finset.mem_image.mp (Finset.min'_mem (s.image e) hne')
      rw [hδ₀, ← hIe]
      exact (he I hI).1
    have hle : ∀ I ∈ s, δ₀ ≤ e I := by
      intro I hI
      rw [hδ₀]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨I, hI, rfl⟩)
    obtain ⟨t, hxt, htδ, htS⟩ := hacc δ₀ hpos
    rw [hS] at htS
    obtain ⟨I, hI, htI⟩ := Set.mem_sUnion.mp htS
    exact absurd htI ((he I hI).2 t hxt (by linarith [hle I hI, htδ]))

/-- **Accumulation from the left** (mirror of `right_subinterval_of_accumulate`). -/
theorem left_subinterval_of_accumulate {S : Set ℝ} {s : Finset (Set ℝ)}
    (hs : ∀ I ∈ s, I.OrdConnected) (hS : S = ⋃₀ (s : Set (Set ℝ))) {x : ℝ}
    (hacc : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, x - δ < t ∧ t < x ∧ t ∈ S) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (x - δ) x ⊆ S := by
  by_cases hne : s.Nonempty
  swap
  · obtain ⟨t, -, -, ht⟩ := hacc 1 zero_lt_one
    rw [hS, Finset.not_nonempty_iff_eq_empty.mp hne] at ht
    simp at ht
  by_cases hacc' : ∃ I ∈ s, ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, x - δ < t ∧ t < x ∧ t ∈ I
  · obtain ⟨I, hI, hIacc⟩ := hacc'
    obtain ⟨t₀, -, ht₀x, ht₀I⟩ := hIacc 1 zero_lt_one
    refine ⟨x - t₀, by linarith, fun t ht => ?_⟩
    rw [Set.mem_Ioo] at ht
    obtain ⟨t₁, ht₁t, ht₁x, ht₁I⟩ := hIacc (x - t) (by linarith)
    have hmem : t ∈ I := by
      apply (hs I hI).out' ht₀I ht₁I
      exact ⟨le_of_lt (by linarith [ht.1]), le_of_lt (by linarith [ht₁t])⟩
    rw [hS]
    exact Set.subset_sUnion_of_mem hI hmem
  · push_neg at hacc'
    have hex : ∀ I ∈ s, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, x - δ < t → t < x → t ∉ I := by
      intro I hI
      obtain ⟨δ, hδ, hδ'⟩ := hacc' I hI
      refine ⟨δ, hδ, ?_⟩
      intro t ht1 ht2 hmem
      exact hδ' t ht1 ht2 hmem
    let e : Set ℝ → ℝ := fun I => if hI : I ∈ s then Classical.choose (hex I hI) else 1
    have he : ∀ I ∈ s, 0 < e I ∧ ∀ t : ℝ, x - e I < t → t < x → t ∉ I := by
      intro I hI
      have h1 : e I = Classical.choose (hex I hI) := dif_pos hI
      rw [h1]
      exact Classical.choose_spec (hex I hI)
    have hne' : (s.image e).Nonempty := hne.image e
    set δ₀ : ℝ := (s.image e).min' hne' with hδ₀
    have hpos : 0 < δ₀ := by
      obtain ⟨I, hI, hIe⟩ := Finset.mem_image.mp (Finset.min'_mem (s.image e) hne')
      rw [hδ₀, ← hIe]
      exact (he I hI).1
    have hle : ∀ I ∈ s, δ₀ ≤ e I := by
      intro I hI
      rw [hδ₀]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨I, hI, rfl⟩)
    obtain ⟨t, htδ, htx, htS⟩ := hacc δ₀ hpos
    rw [hS] at htS
    obtain ⟨I, hI, htI⟩ := Set.mem_sUnion.mp htS
    exact absurd htI ((he I hI).2 t (by linarith [hle I hI, htδ]) htx)

/-- **Accumulation dichotomy.**  If a finite union `S` of order convex sets accumulates strictly
at `x` (from one side or the other), then it contains a one-sided neighbourhood of `x`. -/
theorem subinterval_of_accumulate {S : Set ℝ}
    (hS : ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧ S = ⋃₀ (s : Set (Set ℝ))) {x : ℝ}
    (hacc : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, 0 < |t - x| ∧ |t - x| < δ ∧ t ∈ S) :
    (∃ δ : ℝ, 0 < δ ∧ Set.Ioo x (x + δ) ⊆ S) ∨
      (∃ δ : ℝ, 0 < δ ∧ Set.Ioo (x - δ) x ⊆ S) := by
  obtain ⟨s, hs, hS⟩ := hS
  by_cases hr : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, x < t ∧ t < x + δ ∧ t ∈ S
  · exact Or.inl (right_subinterval_of_accumulate hs hS hr)
  · push_neg at hr
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hr
    refine Or.inr (left_subinterval_of_accumulate hs hS fun δ hδ => ?_)
    obtain ⟨t, hne0, htδ, htS⟩ := hacc (min δ δ₀) (lt_min hδ hδ₀)
    rw [abs_sub_lt_iff] at htδ
    have htx : t < x := by
      by_contra h
      push_neg at h
      have hne1 : x ≠ t := by
        intro hx
        rw [hx] at hne0
        simp at hne0
      exact hδ₀' t (lt_of_le_of_ne h hne1) (by linarith [htδ.2, min_le_right δ δ₀]) htS
    exact ⟨t, by linarith [htδ.1, min_le_left δ δ₀], htx, htS⟩

/-- `IsBnd` is insensitive to complementation. -/
lemma isBnd_compl {D : Set ℝ} {x : ℝ} : WilC2.IsBnd Dᶜ x ↔ WilC2.IsBnd D x := by
  constructor <;> intro h <;> exact ⟨by simpa using h.2, by simpa using h.1⟩

/-- **Transition lemma, right case.**  If `y ∈ D`, `y' ∉ D` and `y < y'`, there is a boundary
point of `D` in `[y, y']`. -/
lemma exists_isBnd_between_of_lt {D : Set ℝ} {y y' : ℝ} (hlt : y < y') (hy : y ∈ D)
    (hy' : y' ∉ D) : ∃ u : ℝ, y ≤ u ∧ u ≤ y' ∧ WilC2.IsBnd D u := by
  set A : Set ℝ := {d | y ≤ d ∧ d ≤ y' ∧ Set.Icc y d ⊆ D} with hA
  have hyA : y ∈ A := by
    refine ⟨le_rfl, le_of_lt hlt, ?_⟩
    intro t ht
    rw [Set.mem_Icc] at ht
    rw [le_antisymm ht.2 ht.1]
    exact hy
  have hbdd : BddAbove A := ⟨y', fun d hd => hd.2.1⟩
  have hsup_le : sSup A ≤ y' := csSup_le ⟨y, hyA⟩ fun d hd => hd.2.1
  have hle_sup : y ≤ sSup A := le_csSup hbdd hyA
  have hmemA : ∀ d ∈ A, d ∈ D := fun d hd => hd.2.2 (Set.mem_Icc.mpr ⟨hd.1, le_rfl⟩)
  refine ⟨sSup A, hle_sup, hsup_le, ?_, ?_⟩
  · by_cases hs : sSup A ∈ D
    · rintro ⟨ε, hε, hsub⟩
      have hsA : sSup A ∈ A := by
        refine ⟨hle_sup, hsup_le, ?_⟩
        intro t ht
        rw [Set.mem_Icc] at ht
        rcases eq_or_lt_of_le ht.2 with h | h
        · rw [h]; exact hs
        · obtain ⟨d', hd'A, hd'⟩ := exists_lt_of_lt_csSup ⟨y, hyA⟩ h
          exact hd'A.2.2 (Set.mem_Icc.mpr ⟨ht.1, le_of_lt hd'⟩)
      have hslt : sSup A < y' := lt_of_le_of_ne hsup_le fun h => hy' (h ▸ hs)
      set d : ℝ := min y' (sSup A + ε / 2) with hd
      have hsd : sSup A < d := lt_min hslt (by linarith)
      have hdA : d ∈ A := by
        refine ⟨le_trans hle_sup (le_of_lt hsd), min_le_left _ _, ?_⟩
        intro t ht
        rw [Set.mem_Icc] at ht
        rcases le_or_gt t (sSup A) with hle | hgt
        · exact hsA.2.2 (Set.mem_Icc.mpr ⟨ht.1, hle⟩)
        · exact hsub ⟨by linarith,
            by linarith [ht.2, min_le_right y' (sSup A + ε / 2), hε]⟩
      exact absurd (le_csSup hbdd hdA) (not_le.mpr hsd)
    · rintro ⟨ε, hε, hsub⟩
      exact hs (hsub (Work.WilC2.mem_Ioo_self hε))
  · rintro ⟨ε, hε, hsub⟩
    obtain ⟨d, hdA, hd⟩ := exists_lt_of_lt_csSup ⟨y, hyA⟩ (show sSup A - ε < sSup A by linarith)
    exact hsub ⟨hd, by linarith [le_csSup hbdd hdA]⟩ (hmemA d hdA)

/-- **Transition lemma.**  If `y ∈ D` and `y' ∉ D`, there is a boundary point of `D` between
them. -/
lemma exists_isBnd_between {D : Set ℝ} {y y' : ℝ} (hy : y ∈ D) (hy' : y' ∉ D) :
    ∃ u : ℝ, u ∈ Set.uIcc y y' ∧ WilC2.IsBnd D u := by
  rcases lt_trichotomy y y' with h | h | h
  · obtain ⟨u, h1, h2, hu⟩ := exists_isBnd_between_of_lt h hy hy'
    exact ⟨u, Set.mem_uIcc.mpr (Or.inl ⟨h1, h2⟩), hu⟩
  · exact absurd h fun hh => hy' (hh ▸ hy)
  · obtain ⟨u, h1, h2, hu⟩ :=
      exists_isBnd_between_of_lt h (D := Dᶜ) (by simpa using hy') (by simpa using hy)
    exact ⟨u, Set.mem_uIcc.mpr (Or.inr ⟨h1, h2⟩), isBnd_compl.mp hu⟩

/-- **Boundary dichotomy.**  If an interval contains no boundary point of `D` and meets `D`, then
it is contained in `D`. -/
theorem Ioo_subset_of_no_bnd {D : Set ℝ} {a b : ℝ}
    (hbnd : ∀ x ∈ Set.Ioo a b, ¬ WilC2.IsBnd D x) {x : ℝ} (hx : x ∈ Set.Ioo a b) (hxD : x ∈ D) :
    Set.Ioo a b ⊆ D := by
  by_contra hcon
  rw [Set.not_subset] at hcon
  obtain ⟨z, hz, hzD⟩ := hcon
  obtain ⟨u, hu, huB⟩ := exists_isBnd_between hxD hzD
  rw [Set.mem_uIcc] at hu
  have hau : a < u := by
    rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_of_lt_of_le hx.1 h1
    · exact lt_of_lt_of_le hz.1 h1
  have hub : u < b := by
    rcases hu with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact lt_of_le_of_lt h2 hz.2
    · exact lt_of_le_of_lt h2 hx.2
  exact hbnd u ⟨hau, hub⟩ huB

end Work.WilC4
