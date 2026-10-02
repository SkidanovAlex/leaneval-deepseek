import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.relCohPreimageAux
import Submission.Work.Serre.cylCollarShrink

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The collar neighbourhood of the pair `(cylBot q, q⁻¹{b})` inside `CMid q b`

For a continuous map `q : C(X, B)` and a point `b : B`, let

* `Mid q b = range (cylIncl q) ∪ (cylRetract q) ⁻¹' {b}` — the bottom copy together with the fibre
  cone over `b`; this is `Work.Serre.CMid q b` (a *copy* of the definition, so that this file does
  not have to import `Submission.Work.Serre.fibreNonvanishing`; the two are definitionally equal
  because `CMid` is an `abbrev`);
* `A₀ = cylBot q = range (cylIncl q)` — the bottom copy, and `A q b = A₀ ∩ (cylRetract q) ⁻¹' {b}`
  the copy of the fibre `q ⁻¹' {b}` inside it;
* `U q b = Mid q b ∩ cylCollar q` — the collar of the mapping cylinder, cut down to `Mid q b`, and
  `Ub q b = U q b ∩ (cylRetract q) ⁻¹' {b}`.

The geometric facts recorded here are

* `interior_union_eq_univ`: the interiors of `M` and of `U` cover `Mid q b` — so the pair
  `(U, Ub) → (Mid, M)` is an excision (Eilenberg–Steenrod, in the "interiors cover" form);
* `cylShrink_mem_Mid`, `cylShrink_mem_fibre`: the collar shrink `cylShrink q s` preserves both
  `Mid q b` and `(cylRetract q) ⁻¹' {b}`, and fixes `cylBot q` (`cylShrink_fixes_bot`), so that
  `(inclAU) : (A₀, A) → (U, Ub)` is a homotopy equivalence of pairs (`cylShrink` at time `1` is the
  homotopy inverse).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre
namespace CMidCollar

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-- The middle set of `Work.Serre.fibreNonvanishing`: the bottom copy together with the fibre cone
over `b`.  (Definitionally equal to `Work.Serre.CMid q b`.) -/
abbrev Mid (q : C(X, B)) (b : B) : Set (cyl q) :=
  (Set.range (cylIncl q) ∪ (cylRetract q) ⁻¹' ({b} : Set B) : Set (cyl q))

/-- The bottom copy is contained in the middle set. -/
theorem Mid_subset (q : C(X, B)) (b : B) : (Set.range (cylIncl q) : Set (cyl q)) ⊆ Mid q b :=
  Set.subset_union_left

/-- The fibre cone `(cylRetract q) ⁻¹' {b}` inside the middle set. -/
def M (q : C(X, B)) (b : B) : Set ↥(Mid q b) :=
  {x | (x : cyl q) ∈ (cylRetract q) ⁻¹' ({b} : Set B)}

/-- The collar `cylCollar q` inside the middle set. -/
def U (q : C(X, B)) (b : B) : Set ↥(Mid q b) :=
  {x | (x : cyl q) ∈ cylCollar q}

/-- The fibre `q ⁻¹' {b}`, as seen inside the bottom copy `cylBot q`. -/
def A (q : C(X, B)) (b : B) : Set ↥(cylBot q) :=
  {x | (x : cyl q) ∈ (cylRetract q) ⁻¹' ({b} : Set B)}

/-- The fibre inside the collar part `U q b` of the middle set. -/
def Ub (q : C(X, B)) (b : B) : Set ↥(U q b) :=
  {x | ((x : ↥(Mid q b)) : cyl q) ∈ (cylRetract q) ⁻¹' ({b} : Set B)}

/-- Membership in the fibre cone inside the middle set. -/
@[simp] theorem mem_M_iff (q : C(X, B)) (b : B) (x : ↥(Mid q b)) :
    x ∈ M q b ↔ (cylRetract q) (x : cyl q) = b := Iff.rfl

/-- Membership in the fibre inside the bottom copy. -/
@[simp] theorem mem_A_iff (q : C(X, B)) (b : B) (x : ↥(cylBot q)) :
    x ∈ A q b ↔ (cylRetract q) (x : cyl q) = b := Iff.rfl

/-- Membership in the fibre part of the collar. -/
@[simp] theorem mem_Ub_iff (q : C(X, B)) (b : B) (x : ↥(U q b)) :
    x ∈ Ub q b ↔ (cylRetract q) ((x : ↥(Mid q b)) : cyl q) = b := Iff.rfl

/-- The collar part of the middle set is open in the middle set. -/
theorem isOpen_U (q : C(X, B)) (b : B) : IsOpen (U q b) :=
  (isOpen_cylCollar q).preimage continuous_subtype_val

/-- **The fibre cone is a neighbourhood of the points of `Mid` above the collar**: the open part
`{collar coordinate > 1/2}` is contained in `M`. -/
theorem half_lt_lam_subset_M (q : C(X, B)) (b : B) :
    {x : ↥(Mid q b) | (1/2 : ℝ) < (cylLam q (x : cyl q) : ℝ)} ⊆ M q b := by
  intro x hx
  rcases x.2 with h | h
  · have h' : (x : cyl q) ∈ cylBot q := h
    rw [cylBot_eq_cylLam_eq_zero q] at h'
    simp only [Set.mem_setOf_eq] at h'
    have hx' : (1/2 : ℝ) < (cylLam q (x : cyl q) : ℝ) := hx
    rw [h'] at hx'
    norm_num at hx'
  · exact h

/-- The half-collar part of the middle set is open in the middle set. -/
theorem isOpen_halfLam (q : C(X, B)) (b : B) :
    IsOpen {x : ↥(Mid q b) | (1/2 : ℝ) < (cylLam q (x : cyl q) : ℝ)} :=
  isOpen_Ioi.preimage
    (continuous_subtype_val.comp ((cylLam q).continuous.comp continuous_subtype_val))

/-- **The interiors of the fibre cone and of the collar cover the middle set.**  This is the
hypothesis of Eilenberg–Steenrod excision for the pair `(Mid, M)`. -/
theorem interior_union_eq_univ (q : C(X, B)) (b : B) :
    interior (M q b) ∪ interior (U q b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : (cylLam q (x : cyl q) : ℝ) < 1
  · exact Or.inr ((isOpen_U q b).interior_eq.symm ▸ hx)
  · have hx1 : (cylLam q (x : cyl q) : ℝ) = 1 := by
      have h := (cylLam q (x : cyl q)).2.2
      linarith
    have hmem : x ∈ {y : ↥(Mid q b) | (1/2 : ℝ) < (cylLam q (y : cyl q) : ℝ)} := by
      show (1/2 : ℝ) < (cylLam q (x : cyl q) : ℝ)
      rw [hx1]; norm_num
    exact Or.inl (interior_maximal (half_lt_lam_subset_M q b) (isOpen_halfLam q b) hmem)

/-- The bottom copy, included into the collar part of the middle set. -/
def inclAU (q : C(X, B)) (b : B) : C(↥(cylBot q), ↥(U q b)) where
  toFun x := ⟨⟨(x : cyl q), Or.inl x.2⟩, cylBot_subset_cylCollar q x.2⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-- The collar part of the middle set, included into the middle set. -/
def inclUC (q : C(X, B)) (b : B) : C(↥(U q b), ↥(Mid q b)) where
  toFun x := (x : ↥(Mid q b))
  continuous_toFun := continuous_subtype_val

/-- The bottom copy, included into the middle set. -/
def inclAC (q : C(X, B)) (b : B) : C(↥(cylBot q), ↥(Mid q b)) where
  toFun x := ⟨(x : cyl q), Or.inl x.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

@[simp] theorem inclAU_apply (q : C(X, B)) (b : B) (x : ↥(cylBot q)) :
    ((inclAU q b x : ↥(Mid q b)) : cyl q) = (x : cyl q) := rfl

@[simp] theorem inclUC_apply (q : C(X, B)) (b : B) (x : ↥(U q b)) :
    (inclUC q b x : cyl q) = (x : cyl q) := rfl

@[simp] theorem inclAC_apply (q : C(X, B)) (b : B) (x : ↥(cylBot q)) :
    (inclAC q b x : cyl q) = (x : cyl q) := rfl

theorem mapsTo_inclAU (q : C(X, B)) (b : B) : Set.MapsTo (inclAU q b) (A q b) (Ub q b) :=
  fun _ hx => hx

theorem mapsTo_inclUC (q : C(X, B)) (b : B) : Set.MapsTo (inclUC q b) (Ub q b) (M q b) :=
  fun _ hx => hx

theorem mapsTo_inclAC (q : C(X, B)) (b : B) : Set.MapsTo (inclAC q b) (A q b) (M q b) :=
  fun _ hx => hx

theorem inclUC_comp_inclAU (q : C(X, B)) (b : B) :
    (inclUC q b).comp (inclAU q b) = inclAC q b := by
  ext x
  rfl

/-! ## The collar shrink -/

/-- The collar shrink preserves the middle set. -/
theorem cylShrink_mem_Mid (q : C(X, B)) (b : B) (s : unitInterval) {y : ↥(cylCollar q)}
    (hy : (y : cyl q) ∈ Mid q b) : (cylShrink q s y : cyl q) ∈ Mid q b := by
  rcases hy with h | h
  · exact Or.inl (by rw [cylShrink_fixes_bot q s h]; exact h)
  · exact Or.inr ((cylRetract_cylShrink q s y).trans h)

/-- The collar shrink preserves the fibre `(cylRetract q) ⁻¹' {b}`. -/
theorem cylShrink_mem_fibre (q : C(X, B)) (b : B) (s : unitInterval) {y : ↥(cylCollar q)}
    (hy : (y : cyl q) ∈ (cylRetract q) ⁻¹' ({b} : Set B)) :
    (cylShrink q s y : cyl q) ∈ (cylRetract q) ⁻¹' ({b} : Set B) :=
  (cylRetract_cylShrink q s y).trans hy

/-- The collar shrink at time `0` is the identity. -/
theorem cylShrink_zero (q : C(X, B)) (y : ↥(cylCollar q)) : cylShrink q 0 y = y := by
  rw [← cylShrinkHomotopy_apply q 0 y]
  exact (cylShrinkHomotopy q).map_zero_left y

end

end CMidCollar
end Work.Serre
