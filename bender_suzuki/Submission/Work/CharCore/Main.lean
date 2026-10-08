import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.Coherence
import Submission.Work.CharCore.CharLib
import Submission.Work.CharCore.star_trace_eq_trace_pow
import Submission.Work.CharCore.star_char
import Submission.Work.CharCore.star_Irr
import Submission.Work.CharCore.irreducible_character_mem_Irr
import Submission.Work.CharCore.fdRep_simple_iff
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.classFun_eq_zero_of_orthogonal
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.CharCore.sum_irr_degree_sq
import Submission.Work.CharCore.finrank_classFun_eq_card_Irr
import Submission.Work.CharCore.finrank_classFun_eq_card_conjClasses
import Submission.Work.CharCore.isChar_iff
import Submission.Work.CharCore.isChar_iff_exists_nat_coeffs
import Submission.Work.CharCore.isVChar_iff
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.CharCore.norm_char_le
import Submission.Work.CharCore.norm_char_eq_iff_isScalar
import Submission.Work.CharCore.irr_degree_dvd_card
import Submission.Work.CharCore.charKernel_subgroup
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.CharCore.exists_irr_of_monoidHom
import Submission.Work.CharCore.irrDeg_eq_one_of_commutative
import Submission.Work.CharCore.column_orthogonality_conj
import Submission.Work.CharCore.column_orthogonality_not_conj
import Submission.Work.CharCore.linear_char_iff_deg_one
import Submission.Work.CharCore.cfInner_int_vchar
import Submission.Work.CharCore.card_irr_deg_one
import Submission.Work.CharCore.cfInner_regularChar
import Submission.Work.CharCore.isChar_regularChar
import Submission.Work.CharCore.eq_one_of_character_eq_degree
import Submission.Work.CharCore.cfInner_character_nat
import Submission.Work.CharCore.isChar_character
import Submission.Work.CharCore.isChar_mul
import Submission.Work.CharCore.isVChar_mul
import Submission.Work.CharCore.cfInner_self_vchar_nat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.Main`: the public interface of the character-theory core (area A5)

This module imports every component of `Work.CharCore` and records the composite statements of
the area in one place.  Import this (rather than the individual component modules) to use the
character theory of finite groups.

## Main results

* `Irr_orthonormal` : `cfInner χ ψ = if χ = ψ then 1 else 0` for `χ, ψ ∈ Irr G`;
* `classFun_eq_zero_of_orthogonal`, `classFun_eq_sum_irr` : the class functions are spanned by
  `Irr G` (with coefficients `cfInner f χ`);
* `card_irr` : the number of irreducible characters equals the number of conjugacy classes;
* `sum_irr_degree_sq` : `∑ χ ∈ Irr G, χ 1 ^ 2 = |G|`;
* `column_orthogonality` (in `column_orthogonality_conj` / `column_orthogonality_not_conj`);
* `isChar_iff`, `isVChar_iff` : characters and virtual characters via their multiplicities;
* `vchar_norm_one` : a virtual character of norm `1` is `±` an irreducible character;
* `norm_char_le` : `‖χ g‖ ≤ χ 1`, with `norm_char_eq_iff_isScalar` for the equality case;
* `irr_degree_dvd` : the degree of an irreducible character divides `|G|`;
* `charKernel_subgroup` : `{g | χ g = χ 1}` is a normal subgroup;
* `principalChar_mem_Irr`, `exists_irr_of_monoidHom`, `linear_char_iff_deg_one`,
  `irrDeg_eq_one_of_commutative`, `card_irr_deg_one` : linear characters.
-/

noncomputable section

open Classical Finset

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- **The number of irreducible complex characters of `G` equals the number of conjugacy
classes of `G`.** -/
theorem card_irr : (Irr G).card = Nat.card (ConjClasses G) := by
  rw [← finrank_classFun_eq_card_Irr, finrank_classFun_eq_card_conjClasses]




/-- **The decomposition of the regular character**: it is `∑ χ ∈ Irr G, χ 1 • χ`, i.e. each
irreducible character occurs in the regular representation with multiplicity its degree. -/
theorem regularChar_eq_sum :
    regularChar G = ∑ χ ∈ Irr G, (irrDeg χ : ℂ) • χ := by
  rw [classFun_eq_sum_irr (isClassFun_regularChar G)]
  exact Finset.sum_congr rfl fun χ hχ => by rw [cfInner_regularChar hχ]

/-- **Column orthogonality**: the columns of the character table of `G` are orthogonal, with
squared norm `|C_G(g)|` for the column of `g`. -/
theorem column_orthogonality (g h : G) :
    ∑ χ ∈ Irr G, χ g * starRingEnd ℂ (χ h) =
      if IsConj g h then ((Nat.card (Subgroup.centralizer ({g} : Set G)) : ℕ) : ℂ) else 0 := by
  by_cases hh : IsConj g h
  · rw [if_pos hh]; exact column_orthogonality_conj hh
  · rw [if_neg hh]; exact column_orthogonality_not_conj hh

/-- The kernel of an irreducible character, as a normal subgroup. -/
noncomputable def irrKer (χ : G → ℂ) (hχ : χ ∈ Irr G) : Subgroup G :=
  Classical.choose (charKernel_subgroup hχ)

theorem irrKer_normal (χ : G → ℂ) (hχ : χ ∈ Irr G) : (irrKer χ hχ).Normal :=
  (Classical.choose_spec (charKernel_subgroup hχ)).1

theorem coe_irrKer (χ : G → ℂ) (hχ : χ ∈ Irr G) : (irrKer χ hχ : Set G) = charKernel χ :=
  (Classical.choose_spec (charKernel_subgroup hχ)).2

/-- `g` lies in the kernel of the irreducible character `χ` exactly when `χ g = χ 1`. -/
theorem mem_irrKer {χ : G → ℂ} (hχ : χ ∈ Irr G) {g : G} : g ∈ irrKer χ hχ ↔ χ g = χ 1 := by
  rw [← SetLike.mem_coe, coe_irrKer]
  rfl

/-- The degree of an irreducible character divides the order of the group (Frobenius), in the
form used by the odd-order proof: `χ 1 = d` for some natural number `d` dividing `|G|`. -/
theorem irr_degree_dvd {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ d : ℕ, χ 1 = (d : ℂ) ∧ d ∣ Nat.card G :=
  ⟨irrDeg χ, irrDeg_spec hχ, irr_degree_dvd_card hχ⟩

/-- `Irr G` is nonempty. -/
theorem Irr_nonempty : (Irr G).Nonempty := ⟨_, principalChar_mem_Irr⟩

/-- The inner product of an irreducible character with itself is `1`. -/
theorem cfInner_self_mem_Irr {χ : G → ℂ} (hχ : χ ∈ Irr G) : cfInner χ χ = 1 := by
  rw [irr_orthonormal χ χ hχ hχ, if_pos rfl]

end Work.CharCore
