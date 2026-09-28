import Submission.Work.Surgery.Surgery
import Submission.Work.OrientedBordism8.Bordism

/-!
# The `3`-connected reduction, and the surgical route to the dimension-`8` congruence

The classical (surgery-theoretic) proof of the dimension-`8` Hirzebruch congruence proceeds in two
steps.

**Step 1 (surgery below the middle dimension).**  Every closed oriented smooth `8`-manifold is
bordant to a `3`-connected one: one kills `H₁`, `H₂`, `H₃` in turn by surgery on embedded spheres
(Morse theory for the handle decomposition, triviality of their normal bundles because the codimension
is `≥ 3` in the relevant range, and the Whitney trick to make the spheres disjoint).

**Step 2 (the classification of `3`-connected `8`-manifolds).**  A `3`-connected closed oriented
smooth `8`-manifold is built from one `0`-handle, `r` `4`-handles and one `8`-handle; its bordism
class is governed by its middle intersection form `Q` together with the framings
`π₃(SO(4)) ≅ ℤ²` of the attaching spheres of the `4`-handles.  Killing a hyperbolic pair of `Q` by
surgery realises `Q ↦ Q ⊖ ℍ` (`Work.Surgery.SurgeryMove`, `Work.Surgery.sigma_eq_of_surgeryMove`),
so the bordism invariant of `Q` is its stable class under `⊖ ℍ`.

## What is here

* `Work.Surgery.IsConnectedUpTo`, `Work.Surgery.IsThreeConnected` — the connectivity of a closed
  oriented manifold in the workspace's model (`TopCat` + fundamental class);
* `Work.Surgery.ThreeConnectedReduction` — **Step 1**, as a named proposition: every manifold of a
  family of honest `8`-manifolds is bordant to a `3`-connected one;
* `Work.Surgery.ThreeConnectedInSpan` — **Step 2**, as a named proposition: for a `3`-connected
  member of the family the number triple `(σ, p₁², p₂)` lies in the rational span of the two
  generator triples `(1,25,10)`, `(1,18,9)`;
* `Work.Surgery.hirzebruchEight_of_span` — the algebra: a triple in that span satisfies the
  Hirzebruch identity `45σ = 7p₂ − p₁²` (`Work.OrientedBordism8.mem_span_iff_hirzebruchEight`);
* `Work.Surgery.rankOne_slice_restriction` — the honest warning about the rank-`1` pieces: their
  numbers lie in the span exactly when `k² ≡ 1 (mod 7)`, so the `r ≥ 2` handles are genuinely part
  of the crux.

Filling in `ThreeConnectedReduction` and `ThreeConnectedInSpan` (with the bordism invariance of
`Work.Bordism`) is exactly what remains of the surgical proof of the dimension-`8` congruence; see
`README.md` for the precise statement.
-/

open scoped Manifold Topology ContDiff
open CategoryTheory CategoryTheory.Limits

namespace Work.Surgery

open Work.Bordism Work.Cohomology Work.SignatureBordism

noncomputable section

/-! ## Connectivity -/

/-- A closed oriented `n`-manifold is **`k`-connected up to degree `k`** if its homology vanishes
in degrees `1, …, k` (equivalently, by Hurewicz, if it is simply connected with trivial homotopy
groups up to degree `k`, in the range where this is meaningful). -/
def IsConnectedUpTo (k : ℕ) {n : ℕ} (M : ClosedOriented n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ k → IsZero ((chainC ℤ (TopCat.toSSet.obj M.X)).homology i)

/-- **`3`-connected**: the connectivity to which the surgical proof of the dimension-`8`
congruence reduces a general closed oriented `8`-manifold. -/
def IsThreeConnected (M : ClosedOriented 8) : Prop := IsConnectedUpTo 3 M

theorem isThreeConnected_iff (M : ClosedOriented 8) :
    IsThreeConnected M ↔ ∀ i, 1 ≤ i → i ≤ 3 →
      IsZero ((chainC ℤ (TopCat.toSSet.obj M.X)).homology i) := Iff.rfl

/-! ## The two steps of the surgical route -/

/-- **Step 1 of the surgical route**: every member of a family of honest closed oriented smooth
`8`-manifolds is bordant to a `3`-connected one.

This is the "surgery below the middle dimension" theorem.  It is *not* proved here: it needs a
handle decomposition (Morse theory), the triviality of the normal bundle of an embedded sphere of
codimension `≥ 3`, and the Whitney trick to make the spheres disjoint. -/
def ThreeConnectedReduction (Man : Type) (X : Man → TopCat.{0})
    (c : (m : Man) → (chainC ℤ (TopCat.toSSet.obj (X m))).homology 8) : Prop :=
  ∀ m : Man, ∃ m' : Man,
    Bordant ⟨X m, c m⟩ ⟨X m', c m'⟩ ∧ IsThreeConnected ⟨X m', c m'⟩

/-- **Step 2 of the surgical route**: for a `3`-connected closed oriented smooth `8`-manifold of the
family, the number triple `(σ, p₁², p₂)` lies in the rational span of the two generator triples
`(1, 25, 10)` (for `ℂP⁴`) and `(1, 18, 9)` (for `ℂP² × ℂP²`); equivalently, by
`Work.OrientedBordism8.mem_span_iff_hirzebruchEight`, the identity `45σ = 7p₂ − p₁²` holds for it.

This is the statement that a `3`-connected `8`-manifold is governed by its middle intersection form
and the `π₃(SO(4)) = ℤ²` framings of its `4`-handles.  It is *not* proved here. -/
def ThreeConnectedInSpan (Man : Type) (X : Man → TopCat.{0})
    (c : (m : Man) → (chainC ℤ (TopCat.toSSet.obj (X m))).homology 8)
    (p₁ : (m : Man) → (cochainC ℤ (TopCat.toSSet.obj (X m))).homology 4)
    (p₂ : (m : Man) → (cochainC ℤ (TopCat.toSSet.obj (X m))).homology 8) : Prop :=
  ∀ m : Man, IsThreeConnected ⟨X m, c m⟩ →
    (((sigma 4 (TopCat.toSSet.obj (X m)) (c m) : ℤ) : ℚ),
      ((p₁SqNumber (TopCat.toSSet.obj (X m)) (c m) (p₁ m) : ℤ) : ℚ),
      ((p₂Number (TopCat.toSSet.obj (X m)) (c m) (p₂ m) : ℤ) : ℚ))
    ∈ Submodule.span ℚ
        ({Work.SignatureBordism.cp4Tuple, Work.SignatureBordism.cp2cp2Tuple} :
          Set (ℚ × ℚ × ℚ))

/-! ## The algebra: a triple in the span satisfies the Hirzebruch identity -/

/-- **The algebra of the generation statement**: the number triple of a manifold lies in the span of
the two generator triples if and only if the Hirzebruch identity `45σ = 7p₂ − p₁²` holds. -/
theorem hirzebruchEight_iff_mem_span (σ p₁sq p₂ : ℤ) :
    Work.SignatureBordism.HirzebruchEight σ p₁sq p₂ ↔
      (((σ : ℚ), ((p₁sq : ℤ) : ℚ), ((p₂ : ℤ) : ℚ)) ∈ Submodule.span ℚ
        ({Work.SignatureBordism.cp4Tuple, Work.SignatureBordism.cp2cp2Tuple} :
          Set (ℚ × ℚ × ℚ))) :=
  (Work.SignatureBordism.mem_span_iff_hirzebruchEight σ p₁sq p₂).symm

/-- **The identity from the span**: a number triple in the span of the generators satisfies the
Hirzebruch identity `45σ = 7p₂ − p₁²`. -/
theorem hirzebruchEight_of_span (σ p₁sq p₂ : ℤ)
    (h : (((σ : ℚ), ((p₁sq : ℤ) : ℚ), ((p₂ : ℤ) : ℚ)) ∈ Submodule.span ℚ
        ({Work.SignatureBordism.cp4Tuple, Work.SignatureBordism.cp2cp2Tuple} :
          Set (ℚ × ℚ × ℚ)))) :
    Work.SignatureBordism.HirzebruchEight σ p₁sq p₂ :=
  (hirzebruchEight_iff_mem_span σ p₁sq p₂).mpr h

/-- **The congruence from the span**: a number triple in the span satisfies
`p₁² ≡ 4σ (mod 7)`. -/
theorem congruence_of_span (σ p₁sq p₂ : ℤ)
    (h : (((σ : ℚ), ((p₁sq : ℤ) : ℚ), ((p₂ : ℤ) : ℚ)) ∈ Submodule.span ℚ
        ({Work.SignatureBordism.cp4Tuple, Work.SignatureBordism.cp2cp2Tuple} :
          Set (ℚ × ℚ × ℚ)))) :
    (7 : ℤ) ∣ p₁sq - 4 * σ := by
  have hh := hirzebruchEight_of_span σ p₁sq p₂ h
  unfold Work.SignatureBordism.HirzebruchEight at hh
  exact ⟨p₂ - 7 * σ, by linarith⟩

/-! ## The rank-`1` slice, and why the `r ≥ 2` handles are needed -/

/-- **The rank-`1` slice of the generation statement, exactly.**  For a rank-`1` piece
`W(ξ) = D(ξ) ∪ D⁸` with `σ = ±1` and `p₁ = 2k·x` (so `p₁² = 4k²σ`), the numbers can be completed to
a triple in the span of the generator triples **iff** `k² ≡ 1 (mod 7)`.

So the rank-`1` pieces (which are the ones the `k`-handle picture first produces) contribute only the
one-dimensional slice `k ≡ ±1 (mod 7)` of `Ω^SO_8 ⊗ ℚ`; the `r ≥ 2` handles and the
middle-dimensional surgery are genuinely part of the crux, not a shortcut. -/
theorem rankOne_slice_restriction (k σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (k ^ 2 ≡ 1 [ZMOD 7]) ↔
      ∃ p₂ : ℤ, (((σ : ℚ), ((4 * k ^ 2 * σ : ℤ) : ℚ), ((p₂ : ℤ) : ℚ)) ∈
        Submodule.span ℚ ({Work.SignatureBordism.cp4Tuple, Work.SignatureBordism.cp2cp2Tuple} :
          Set (ℚ × ℚ × ℚ))) :=
  Work.OrientedBordism8.rankOne_mem_span_iff k σ hσ

end

end Work.Surgery
