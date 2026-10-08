import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.isVChar_iff`

A class function `f` on a finite group is a virtual character if and only if all of its
inner products against irreducible characters are integers.

## Proof

* (⇒) Writing `f` as an integral combination of irreducible characters
  (`Work.CharCore.isVChar_iff_exists_int_coeffs`) and using bilinearity of `cfInner`
  (`Work.CharCore.cfInner_sum_smul_left`) together with the orthonormality of the
  irreducible characters (`Work.CharCore.irr_orthonormal`), the inner product
  `cfInner f χ` collapses to the single integral coefficient of `χ`.
* (⇐) If every `cfInner f χ` is an integer, then the expansion of the class function `f`
  in the basis of irreducible characters
  (`Work.CharCore.classFun_eq_sum_irr`) `f = ∑ χ, cfInner f χ • χ` exhibits `f` as an
  integral linear combination of irreducible characters, so `f` lies in the additive group
  they generate, i.e. `IsVChar f`.
-/

noncomputable section

open Classical Finset

namespace Work.CharCore

theorem isVChar_iff {G : Type*} [Group G] [Fintype G] {f : G → ℂ} (hf : IsClassFun f) :
    IsVChar f ↔ ∀ χ ∈ Irr G, ∃ n : ℤ, cfInner f χ = n := by
  constructor
  · -- a virtual character is an integral combination of irreducibles, and `Irr G` is
    -- orthonormal, so the coefficients are recovered as the inner products
    intro hV χ hχ
    obtain ⟨c, hc⟩ := (isVChar_iff_exists_int_coeffs (G := G)).mp hV
    refine ⟨c ⟨χ, hχ⟩, ?_⟩
    rw [hc, cfInner_sum_smul_left]
    rw [Finset.sum_eq_single (⟨χ, hχ⟩ : ↥(Irr G))]
    · rw [irr_orthonormal χ χ hχ hχ, if_pos rfl, mul_one]
    · intro b _ hb
      rw [irr_orthonormal (b : G → ℂ) χ b.2 hχ]
      have hne : ¬ ((b : G → ℂ) = χ) := fun hh => hb (Subtype.ext hh)
      rw [if_neg hne, mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ (⟨χ, hχ⟩ : ↥(Irr G))) hmem
  · -- conversely the class function `f` expands as `∑ χ, cfInner f χ • χ`, an integral
    -- combination as soon as all the coefficients `cfInner f χ` are integers
    intro h
    rw [classFun_eq_sum_irr hf]
    refine AddSubgroup.sum_mem _ (fun χ hχ => ?_)
    obtain ⟨n, hn⟩ := h χ hχ
    rw [hn, Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hχ) n

end Work.CharCore
