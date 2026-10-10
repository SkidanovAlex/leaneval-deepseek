import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotT.AM2_descent
import Submission.Work.MotT.coeffAut_conj_trans

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotT

/-!
# The coefficient action commutes with the negation `[-1]` of the function field

Let `K` be a field, `L = KummerField2 K h₁ h₂ hk` the two-root Kummer field and
`M = ML2 D h₁ h₂ hk = L(E)` the function field of the Klein model base changed to `L`.  The
coefficient action `AM2_coeffAut D hD h₁ h₂ hk γ` of `γ ∈ Aut_K(L)` acts on the constants `L` by
`γ` and fixes the coordinates `x = genX E` and `y = genY E` of the generic point.

This file shows that it commutes with the negation `[-1]`
(`Work.MotC2.negAlgEquiv E`), the `L`-algebra automorphism of `L(E)` sending `x ↦ x` and
`y ↦ -y - a₁x - a₃`: both sides are `K`-algebra endomorphisms of `M` agreeing on the constants
`L` and on `x`, `y`, and `M = L(x, y)`, so they are equal
(`Work.MotT.ext_of_genX_genY_algebraMap`).  The three verifications are: `[-1]` fixes `L` and the
coefficient action fixes the two coordinates, while the coefficient action carries the
coefficients `a₁`, `a₃` of the base-changed curve (which come from `K`) to themselves, so that it
carries the expression `-y - a₁x - a₃` to itself.
-/

/-- The coefficient action of `γ ∈ Aut_K(L)` on `M = L(E)` commutes with the negation `[-1]` of the
function field. -/
theorem coeffAut_neg_comm {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    (γ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk))
    (x : ML2 D h₁ h₂ hk) :
    AM2_coeffAut D hD h₁ h₂ hk γ
        (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) x) =
      Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))
        (AM2_coeffAut D hD h₁ h₂ hk γ x) := by
  have key : (Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ).toAlgHom.comp
        ((Work.MotC2.negAlgEquiv
          (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))).restrictScalars K).toAlgHom =
      ((Work.MotC2.negAlgEquiv
        (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))).restrictScalars K).toAlgHom.comp
        (Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ).toAlgHom := by
    refine Work.MotT.ext_of_genX_genY_algebraMap (K := K)
      (L := ↥(Work.MotT.KummerField2 K h₁ h₂ hk)) D.E ?_ ?_ ?_
    · intro l
      show (Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ)
          ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)))
            ((algebraMap ↥(Work.MotT.KummerField2 K h₁ h₂ hk)
              (Work.MotT.ML2 D h₁ h₂ hk)) l)) =
        (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)))
          ((Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ)
            ((algebraMap ↥(Work.MotT.KummerField2 K h₁ h₂ hk)
              (Work.MotT.ML2 D h₁ h₂ hk)) l))
      rw [(Work.MotC2.negAlgEquiv _).commutes l,
        (Work.MotT.AM2_coeffAut_spec D hD h₁ h₂ hk γ).1 l,
        (Work.MotC2.negAlgEquiv _).commutes (γ l)]
    · show (Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ)
          ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)))
            (Work.MotC2.genX (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)))) =
        (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)))
          ((Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ)
            (Work.MotC2.genX (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))))
      rw [Work.MotC2.negAlgEquiv_genX,
        show (Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ)
            (Work.MotC2.genX (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))) =
          Work.MotC2.genX (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))
          from (Work.MotT.AM2_coeffAut_spec D hD h₁ h₂ hk γ).2.1,
        Work.MotC2.negAlgEquiv_genX]
    · show (Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ)
          ((Work.MotC2.negAlgEquiv (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)))
            (Work.MotC2.genY (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)))) =
        (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)))
          ((Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ)
            (Work.MotC2.genY (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))))
      rw [Work.MotC2.negAlgEquiv_genY]
      rw [map_sub, map_sub, map_mul, map_neg,
        show (Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ)
            (Work.MotC2.genY (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))) =
          Work.MotC2.genY (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))
          from (Work.MotT.AM2_coeffAut_spec D hD h₁ h₂ hk γ).2.2,
        show (Work.MotT.AM2_coeffAut D hD h₁ h₂ hk γ)
            (Work.MotC2.genX (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))) =
          Work.MotC2.genX (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk))
          from (Work.MotT.AM2_coeffAut_spec D hD h₁ h₂ hk γ).2.1,
        (Work.MotT.AM2_coeffAut_spec D hD h₁ h₂ hk γ).1
          (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)).a₁,
        (Work.MotT.AM2_coeffAut_spec D hD h₁ h₂ hk γ).1
          (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)).a₃,
        show γ ((D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)).a₁) =
            (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)).a₁ from γ.commutes D.E.a₁,
        show γ ((D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)).a₃) =
            (D.E.baseChange ↥(Work.MotT.KummerField2 K h₁ h₂ hk)).a₃ from γ.commutes D.E.a₃,
        Work.MotC2.negAlgEquiv_genY]
  simpa using AlgHom.congr_fun key x

end Work.MotT
