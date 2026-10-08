import Mathlib
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.NSM.c4powFourHom

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.NSM

open scoped commutatorElement

/-- **Fibres of a homomorphism out of `↥C` are the cosets of the image of its kernel.**

For *any* group homomorphism `f : ↥C →* K` (with `C ≤ P` a subgroup) and any `x y ∈ ↥C`, two
elements have the same image under `f` exactly when `x y⁻¹` lies in the image of the kernel of
`f` inside `P`.  This is the general reason why the fourth-power homomorphism of
`powFourHomLocal` has the kernel-condition asked for there. -/
theorem eq_iff_mul_inv_mem_ker_map {P K : Type} [Group P] [Group K] {C : Subgroup P}
    (f : ↥C →* K) (x y : ↥C) :
    f x = f y ↔ (x : P) * (y : P)⁻¹ ∈ f.ker.map C.subtype := by
  have hval : (C.subtype (x * y⁻¹) : P) = (x : P) * (y : P)⁻¹ := rfl
  rw [← hval, Subgroup.mem_map_iff_mem (Subgroup.subtype_injective C), MonoidHom.mem_ker,
    map_mul, map_inv, mul_inv_eq_one]

/-- **The fourth-power map of a class-two subgroup covering `A ^ (2)`, with its fibres.**

If `A ≤ C` are subgroups of a group `P` with `C` centralising `A`, `C ^ (2) ≤ A`,
`⁅C, C⁆ = A ^ (2)` and `A` of exponent dividing `4`, then the fourth-power map `x ↦ x ^ 4` is a
homomorphism `↥C →* ↥(A ^ (2))`, and its fibres are the cosets of the image of its kernel inside
`P`: two elements of `C` have the same fourth power exactly when their quotient lies in
`f.ker.map C.subtype`.

The existence of the homomorphism is `c4powFourHom`; the description of the fibres is the
general fact `eq_iff_mul_inv_mem_ker_map` about the homomorphism so obtained. -/
theorem powFourHomLocal {P : Type} [Group P] [Finite P] {A C : Subgroup P}
    (hAC : A ≤ C) (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hexp : ∀ a ∈ A, a ^ 4 = 1) :
    ∃ f : ↥C →* ↥(Work.Higman.powSub A 2),
      (∀ x : ↥C, (f x : P) = (x : P) ^ 4) ∧
      (∀ x y : ↥C, f x = f y ↔ (x : P) * (y : P)⁻¹ ∈ f.ker.map C.subtype) := by
  obtain ⟨f, hf⟩ := c4powFourHom hAC hZ hC2 hCd hexp
  exact ⟨f, hf, eq_iff_mul_inv_mem_ker_map f⟩

end Work.Higman.NSM
