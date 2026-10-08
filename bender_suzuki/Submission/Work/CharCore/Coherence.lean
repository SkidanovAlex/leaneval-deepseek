import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs
import Submission.Work.Coherence.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Alignment of `Work.CharCore` with `Work.Coherence`

The areas `Work.CharCore` (A5, the character-theory core) and `Work.Coherence` (A11) use two
parallel vocabularies for the same objects; this module records that they agree, so that results
proved in one area can be used in the other.

* `Work.CharCore.cfInner` and `Work.Coherence.cfInner` are *definitionally* the same function
  (`cfInner_eq_coherence`); likewise `IsClassFun`.
* `Work.CharCore.Irr G` is a `Finset`, `Work.Coherence.Irr G` a `Set`; the coercion of the
  finset is exactly the set (`Irr_coe_eq_coherence`), so `χ ∈ Irr G ↔ χ ∈ Coherence.Irr G`.
* Consequently `IsChar` and `IsVChar` agree (`IsChar_iff_coherence`, `IsVChar_iff_coherence`),
  and `Work.CharCore.IsVChar` is membership in `Work.Coherence.ZSpan (Irr G)`.
* `Irr G` is an orthonormal set in the sense of `Work.Coherence.Orthonormal`.
-/

noncomputable section

open Classical

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- The two inner products are the same function. -/
theorem cfInner_eq_coherence (f g : G → ℂ) : cfInner f g = Work.Coherence.cfInner f g := rfl

@[simp] theorem cfInner_coherence (f g : G → ℂ) :
    Work.Coherence.cfInner f g = cfInner f g := rfl

/-- The two notions of class function agree. -/
theorem IsClassFun_iff_coherence (f : G → ℂ) : IsClassFun f ↔ Work.Coherence.IsClassFun f :=
  Iff.rfl

/-- `Work.CharCore.Irr G` is the `Set` version `Work.Coherence.Irr G`. -/
theorem Irr_coe_eq_coherence :
    ((Irr G : Finset (G → ℂ)) : Set (G → ℂ)) = Work.Coherence.Irr G := by
  ext f
  rw [Finset.mem_coe, mem_Irr_iff_fdrep, Work.Coherence.mem_Irr]

theorem mem_Irr_iff_coherence {f : G → ℂ} : f ∈ Irr G ↔ f ∈ Work.Coherence.Irr G := by
  rw [← Irr_coe_eq_coherence, Finset.mem_coe]

/-- The two notions of character agree. -/
theorem IsChar_iff_coherence (f : G → ℂ) : IsChar f ↔ Work.Coherence.IsChar f := by
  simp only [IsChar, Work.Coherence.IsChar, Irr_coe_eq_coherence]

/-- The two notions of virtual character agree. -/
theorem IsVChar_iff_coherence (f : G → ℂ) : IsVChar f ↔ Work.Coherence.IsVChar f := by
  simp only [IsVChar, Work.Coherence.IsVChar, Irr_coe_eq_coherence]

/-- `Irr G` is an orthonormal set of class functions in the sense of area A11. -/
theorem Orthonormal_Irr : Work.Coherence.Orthonormal (Irr G) := by
  intro x hx y hy
  rw [cfInner_coherence]
  exact irr_orthonormal x y hx hy

/-- The integral lattice spanned by `Irr G` (in the vocabulary of area A11) is exactly the set
of virtual characters. -/
theorem IsVChar_iff_mem_zSpan_Irr (f : G → ℂ) :
    IsVChar f ↔ f ∈ Work.Coherence.ZSpan (Irr G) := by
  rw [isVChar_iff_exists_int_coeffs]
  rfl

end Work.CharCore
