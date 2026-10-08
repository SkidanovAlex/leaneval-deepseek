import Mathlib
import Submission.Work.Frobenius.Pair
import Submission.Work.Frobenius.ClassFun
import Submission.Work.Frobenius.Irr.charPair_irr_eq_ite
import Submission.Work.Frobenius.Irr.isIrr_one
import Submission.Work.Frobenius.Induction.charPair_eq_finrank_intertwiningMap
import Submission.Work.Frobenius.Induction.charPair_indFun_resFun
import Submission.Work.Frobenius.Induction.isClassFun_indFun
import Submission.Work.Frobenius.CharZero.mem_span_Irr_of_isClassFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Integrality of pairings and virtual characters obtained by induction

This module contains the passage from "integral pairings + membership in the span of the
irreducible characters" to `IsVChar`, and its application to induced class functions:
if `φ` is a virtual character of a subgroup then `indFun H φ` is a virtual character of `G`.

The key input is `charPair_eq_finrank_intertwiningMap`: the pairing of an irreducible
character with the character of *any* finite-dimensional representation is a natural number
(the dimension of the space of intertwining maps), so by Frobenius reciprocity
`charPair (indFun H χ) ψ ∈ ℕ` for `χ ∈ Irr H` and `ψ ∈ Irr G`.
-/

@[expose] public section

noncomputable section

open Classical

open scoped Pointwise

namespace Work.Frobenius

variable {G : Type*} [Group G] [Fintype G]

section LocalFintype

local instance instFintypeSubgroupVChar (H : Subgroup G) : Fintype H := Fintype.ofFinite H

section Linearity

variable {H : Subgroup G}

theorem indFun_add (f g : H → ℂ) : indFun H (f + g) = indFun H f + indFun H g := by
  funext x
  have key : (∑ y : G, (if hy : y * x * y⁻¹ ∈ H then
        f ⟨y * x * y⁻¹, hy⟩ + g ⟨y * x * y⁻¹, hy⟩ else 0))
      = (∑ y : G, (if hy : y * x * y⁻¹ ∈ H then f ⟨y * x * y⁻¹, hy⟩ else 0))
        + (∑ y : G, (if hy : y * x * y⁻¹ ∈ H then g ⟨y * x * y⁻¹, hy⟩ else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y * x * y⁻¹ ∈ H <;> simp [hy]
  simp only [indFun, Pi.add_apply]
  rw [key]
  ring

theorem indFun_zero : indFun H (0 : H → ℂ) = 0 := by
  funext x
  simp [indFun]

theorem indFun_neg (f : H → ℂ) : indFun H (-f) = -indFun H f := by
  funext x
  have key : (∑ y : G, (if hy : y * x * y⁻¹ ∈ H then -f ⟨y * x * y⁻¹, hy⟩ else 0))
      = -(∑ y : G, (if hy : y * x * y⁻¹ ∈ H then f ⟨y * x * y⁻¹, hy⟩ else 0)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y * x * y⁻¹ ∈ H <;> simp [hy]
  simp only [indFun, Pi.neg_apply]
  rw [key]
  ring

end Linearity

/-- If a class function lies in the span of the irreducible characters and its pairings with
them are integers, then it is a virtual character. -/
theorem isVChar_of_mem_span_of_pairing_int {f : G → ℂ}
    (hspan : f ∈ Submodule.span ℂ (Irr G))
    (hint : ∀ χ ∈ Irr G, ∃ n : ℤ, charPair f χ = n) : IsVChar f := by
  classical
  obtain ⟨c, t, hts, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hspan
  have hcoeff : ∀ a ∈ t, ∃ n : ℤ, c a = (n : ℂ) := by
    intro a ha
    obtain ⟨n, hn⟩ := hint a (hts ha)
    refine ⟨n, ?_⟩
    have hca : charPair f a = c a := by
      rw [← hsum, charPair_sum_smul_left]
      have hsingle : (∑ b ∈ t, c b * charPair b a) = c a * charPair a a := by
        refine Finset.sum_eq_single a ?_ ?_
        · intro b hb hba
          rw [Work.Frobenius.Irr.charPair_irr_eq_ite (hts hb) (hts ha), ite_eq_right hba]
          ring
        · intro hnot; exact absurd ha hnot
      rw [hsingle, Work.Frobenius.Irr.charPair_irr_eq_ite (hts ha) (hts ha), ite_eq_left rfl, mul_one]
    rw [← hca, hn]
  have hmem : ∀ a ∈ t, c a • a ∈ AddSubgroup.closure (Irr G) := by
    intro a ha
    obtain ⟨n, hn⟩ := hcoeff a ha
    rw [hn, Int.cast_smul_eq_zsmul ℂ n a]
    exact AddSubgroup.zsmul_mem _
      (AddSubgroup.subset_closure (show a ∈ Irr G from hts ha)) n
  rw [← hsum]
  exact AddSubgroup.sum_mem _ fun a ha => hmem a ha

/-- The induction of an irreducible character is a virtual character. -/
theorem isVChar_indFun_irr {H : Subgroup G} {χ : H → ℂ} (hχ : χ ∈ Irr H) :
    IsVChar (indFun H χ) := by
  classical
  refine isVChar_of_mem_span_of_pairing_int
    (CharZero.mem_span_Irr_of_isClassFun (Induction.isClassFun_indFun χ)) ?_
  intro ψ hψ
  obtain ⟨dχ, hdχ⟩ := mem_Irr_iff.mp hχ
  obtain ⟨dψ, hdψ⟩ := mem_Irr_iff.mp hψ
  let ρH : Representation ℂ H dψ.V := dψ.ρ.comp H.subtype
  have hreschar : ρH.character = resFun H ψ := by
    funext h
    simp only [resFun]
    rw [← hdψ]
    rfl
  refine ⟨(Module.finrank ℂ (Representation.IntertwiningMap ρH dχ.ρ) : ℤ), ?_⟩
  rw [Induction.charPair_indFun_resFun (φ := χ) (ψ := ψ) (irr_isClassFun hψ)]
  rw [← hdχ, ← hreschar]
  rw [Induction.charPair_eq_finrank_intertwiningMap]
  simp

/-- Induction preserves virtual characters. -/
theorem isVChar_indFun {H : Subgroup G} {φ : H → ℂ} (hφ : IsVChar φ) :
    IsVChar (indFun H φ) := by
  classical
  refine AddSubgroup.closure_induction (p := fun x (_ : x ∈ AddSubgroup.closure (Irr H)) =>
    IsVChar (indFun H x)) ?_ ?_ ?_ ?_ hφ
  · intro χ hχ
    exact isVChar_indFun_irr hχ
  · rw [indFun_zero]; exact AddSubgroup.zero_mem _
  · intro f g _ _ hf hg
    rw [indFun_add]; exact AddSubgroup.add_mem _ hf hg
  · intro f _ hf
    rw [indFun_neg]; exact AddSubgroup.neg_mem _ hf

end LocalFintype

end Work.Frobenius
