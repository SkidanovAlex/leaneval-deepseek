import Submission.Work.Clifford.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.Classes`: conjugacy classes, inverse classes, real classes

The class side of Brauer's permutation lemma (FT 3.12–3.14): the conjugacy classes of `G` as
elements of `ConjClasses G`, the inverse-class map `C ↦ C⁻¹` on them, the fixed points of the
action of an automorphism (`IsFixedClass`), the fixed irreducible characters (`IsFixedIrr`), and
the notion of a *real* conjugacy class (a class closed under inversion, i.e. one containing `g⁻¹`
for some — equivalently every — `g` in it).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

universe u

variable {G : Type u} [Group G]

/-- Conjugation classes are mapped by a homomorphism of groups. -/
theorem conjClasses_map_mk (f : G →* G) (g : G) :
    ConjClasses.map f (ConjClasses.mk g) = ConjClasses.mk (f g) := rfl

/-- The inverse class `C⁻¹ = {g⁻¹ : g ∈ C}` of a conjugacy class.  (Inversion is an
anti-automorphism, so this is not of the form `ConjClasses.map f`.) -/
noncomputable def conjClassesInv (C : ConjClasses G) : ConjClasses G :=
  ConjClasses.mk (Classical.choose (ConjClasses.exists_rep C))⁻¹

theorem conjClassesInv_mk (g : G) : conjClassesInv (ConjClasses.mk g) = ConjClasses.mk g⁻¹ := by
  have h : ConjClasses.mk (Classical.choose (ConjClasses.exists_rep (ConjClasses.mk g))) =
      ConjClasses.mk g := Classical.choose_spec (ConjClasses.exists_rep (ConjClasses.mk g))
  have h2 : IsConj (Classical.choose (ConjClasses.exists_rep (ConjClasses.mk g))) g :=
    ConjClasses.mk_eq_mk_iff_isConj.mp h
  have h3 : IsConj (Classical.choose (ConjClasses.exists_rep (ConjClasses.mk g)))⁻¹ g⁻¹ := by
    obtain ⟨x, hx⟩ := (isConj_iff (a := Classical.choose (ConjClasses.exists_rep
      (ConjClasses.mk g))) (b := g)).mp h2
    exact (isConj_iff (a := (Classical.choose (ConjClasses.exists_rep
      (ConjClasses.mk g)))⁻¹) (b := g⁻¹)).mpr ⟨x, (conj_inv (a := Classical.choose
        (ConjClasses.exists_rep (ConjClasses.mk g))) (b := x)).symm.trans (congrArg Inv.inv hx)⟩
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr h3

theorem conjClassesInv_involutive : Function.Involutive (conjClassesInv (G := G)) := by
  intro C
  obtain ⟨g, hg⟩ := (ConjClasses.mk_surjective C : ∃ g : G, ConjClasses.mk g = C)
  rw [← hg, conjClassesInv_mk, conjClassesInv_mk, inv_inv]

/-- A conjugacy class is *real* if it is closed under inversion, `C⁻¹ = C`. -/
def IsRealClass (C : ConjClasses G) : Prop := conjClassesInv C = C

theorem isRealClass_mk_iff {g : G} : IsRealClass (ConjClasses.mk g) ↔ IsConj g g⁻¹ := by
  rw [IsRealClass, conjClassesInv_mk, ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_comm

theorem isRealClass_inv_mk {g : G} : IsRealClass (ConjClasses.mk g⁻¹) ↔ IsConj g g⁻¹ := by
  rw [isRealClass_mk_iff, inv_inv, isConj_comm]

/-- The conjugacy class of `1` is real. -/
theorem isRealClass_one : IsRealClass (ConjClasses.mk (1 : G)) := by
  rw [isRealClass_mk_iff]
  simp

/-- A conjugacy class fixed by the automorphism `e` (its image under `ConjClasses.map e` is
itself). -/
def IsFixedClass (e : G ≃* G) (C : ConjClasses G) : Prop := ConjClasses.map (e : G →* G) C = C

/-- An irreducible character fixed by the automorphism `e` (`χ ∘ e⁻¹ = χ`). -/
def IsFixedIrr (e : G ≃* G) (χ : G → ℂ) : Prop := autChar e χ = χ

/-- The inversion twist `χ ↦ (g ↦ χ g⁻¹)` of a function on `G`. -/
def invChar (χ : G → ℂ) : G → ℂ := fun g => χ g⁻¹

/-- A real valued function on `G`. -/
def IsRealChar (χ : G → ℂ) : Prop := ∀ g : G, starRingEnd ℂ (χ g) = χ g

@[simp] theorem invChar_apply (χ : G → ℂ) (g : G) : invChar χ g = χ g⁻¹ := rfl

theorem invChar_involutive : Function.Involutive (invChar (G := G)) := by
  intro χ
  ext g
  simp [invChar]

/-- For an irreducible character, being real valued is the same as being fixed by the
inversion twist (using `χ g⁻¹ = conj (χ g)`). -/
theorem invChar_eq_iff_isRealChar {χ : G → ℂ} (h : ∀ g : G, starRingEnd ℂ (χ g) = χ g⁻¹) :
    invChar χ = χ ↔ IsRealChar χ := by
  constructor
  · intro hfix g
    have hg := congrFun hfix g
    simp only [invChar_apply] at hg
    rw [h g, hg]
  · intro hreal
    ext g
    rw [invChar_apply, ← h g]
    exact hreal g

end Work.Clifford
