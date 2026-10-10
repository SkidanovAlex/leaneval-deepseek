import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.GroupWithZero.Action.Units
import Submission.InducedModules
import Submission.Work.GroupCohomology.Classification
import Submission.Work.GroupCohomology.Z1_le_B1_of_card_smul_bijective
import Submission.Work.GroupCohomology.Z2_le_B2_of_card_smul_bijective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- **`H¹(G, A) = 0` when `|G|` is invertible in `A`.** -/
theorem H1_subsingleton_of_card_smul_bijective [Fintype G]
    (hA : Function.Bijective (fun a : A => Fintype.card G • a)) : Subsingleton (H1 G A) :=
  Submission.subsingleton_H1_of_le (Z1_le_B1_of_card_smul_bijective hA)

/-- **`H²(G, A) = 0` when `|G|` is invertible in `A`.** -/
theorem H2_subsingleton_of_card_smul_bijective [Fintype G]
    (hA : Function.Bijective (fun a : A => Fintype.card G • a)) : Subsingleton (H2 G A) :=
  Submission.subsingleton_H2_of_le (Z2_le_B2_of_card_smul_bijective hA)

/-- Multiplication by `|G|` is a bijection on a `ℚ`-vector space: it is inverted by
multiplication by `(|G| : ℚ)⁻¹`. -/
theorem bijective_card_smul_of_module_rat (G : Type u) (A : Type v) [Group G] [Fintype G]
    [AddCommGroup A] [Module ℚ A] :
    Function.Bijective (fun a : A => Fintype.card G • a) := by
  have hn : (Fintype.card G : ℚ) ≠ 0 := by
    have hpos : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun a => (Fintype.card G : ℚ)⁻¹ • a, ?_, ?_⟩
  · intro a
    show (Fintype.card G : ℚ)⁻¹ • (Fintype.card G • a) = a
    rw [← Nat.cast_smul_eq_nsmul (R := ℚ)]
    exact inv_smul_smul₀ hn a
  · intro a
    show Fintype.card G • ((Fintype.card G : ℚ)⁻¹ • a) = a
    rw [← Nat.cast_smul_eq_nsmul (R := ℚ)]
    exact smul_inv_smul₀ hn a

/-- **`H¹` of a finite group with coefficients in a `ℚ`-vector space vanishes.** -/
theorem H1_subsingleton_of_module_rat [Fintype G] [Module ℚ A] : Subsingleton (H1 G A) :=
  H1_subsingleton_of_card_smul_bijective (bijective_card_smul_of_module_rat G A)

/-- **`H²` of a finite group with coefficients in a `ℚ`-vector space vanishes.** -/
theorem H2_subsingleton_of_module_rat [Fintype G] [Module ℚ A] : Subsingleton (H2 G A) :=
  H2_subsingleton_of_card_smul_bijective (bijective_card_smul_of_module_rat G A)

section Extensions

variable {Q : Type u} {B : Type v} [Group Q] [Fintype Q] [AddCommGroup B]
variable [DistribMulAction Q B] [Module ℚ B]

/-- **Every extension of a finite group by a `ℚ`-vector space splits**, since
`H²(Q, B) = 0`. -/
theorem nonempty_splitting_of_module_rat (X : Extension Q B) :
    Nonempty (Extension.Splitting X) := by
  haveI := H2_subsingleton_of_module_rat (G := Q) (A := B)
  exact exists_splitting_of_subsingleton_H2 X

end Extensions

end Work.GroupCohomology
