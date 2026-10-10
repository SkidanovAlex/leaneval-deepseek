import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotT.AM2_descent
import Submission.Work.MotT.T4Extend

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.MotT

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type} [Field K]

/-! ## The twisted Galois action fixes the twist field

The twisted action `ρ^{(h)}_γ = Δ_{c(γ)} ∘ γ̃` of `Aut_K(L)` on `M = L(E)` (`AM2_rhoFun`) is built so
as to fix, pointwise, the `K`-twist field `K(C_h) = adjoin K (range (AM2_yM w))` when `w ^ 5 = h`
(`AM2_rhoFun_yM`).  Here we record the resulting *elementwise* statement for an arbitrary element of
that `K`-subfield: it is the form in which the comparison `Θ ρ^{(h₁)}_γ = ρ^{(h₂)}_γ Θ` is checked
on the generators. -/

/-- **The twisted action fixes its twist field.**  Every element of
`adjoin K (range (AM2_yM D h₁ h₂ hk w))` is fixed by `AM2_rhoFun D hD h₁ h₂ hk h hh w hw γ`. -/
theorem AM2_rhoFun_self_of_mem (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (hk : ringChar K ≠ 5) (h : K) (hh : h ≠ 0)
    (w : ↥(KummerField2 K h₁ h₂ hk)) (hw : w ^ 5 = algebraMap K ↥(KummerField2 K h₁ h₂ hk) h)
    (γ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk))
    {x : ML2 D h₁ h₂ hk}
    (hx : x ∈ IntermediateField.adjoin K (Set.range (AM2_yM D h₁ h₂ hk w))) :
    AM2_rhoFun D hD h₁ h₂ hk h hh w hw γ x = x := by
  have hx' := (AM2_le_fixedField D hD h₁ h₂ hk h hh w hw) hx
  exact (IntermediateField.mem_fixedField_iff _ x).mp hx' _
    (MonoidHom.mem_range.mpr ⟨⟨γ, Subgroup.mem_top γ⟩, rfl⟩)

/-- The twisted action for the twist parameter `h₂` fixes the twist field `AM22 = K(C_{h₂})`
pointwise. -/
theorem AM2_rhoFun_fixes_AM22 (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (h₂0 : h₂ ≠ 0) (hk : ringChar K ≠ 5)
    (γ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk))
    (x : ↥(AM22 D h₁ h₂ hk)) :
    AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) γ
      (x : ML2 D h₁ h₂ hk) = (x : ML2 D h₁ h₂ hk) := by
  apply AM2_rhoFun_self_of_mem D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) γ
  exact x.2

/-- **T4, comparison step.**  An `L`-algebra automorphism `Θ` of `M = L(E)` carrying the twist field
`AM21 = K(C_{h₁})` onto `AM22 = K(C_{h₂})` (the hypothesis `hΘ`, the conclusion of
`Work.MotT.exists_algEquiv_ML2`) conjugates the twisted Galois action for `h₁` into the twisted
Galois action for `h₂`:

`Θ (ρ^{(h₁)}_γ x) = ρ^{(h₂)}_γ (Θ x)`.

Indeed, the twisted action `ρ^{(h)}_γ` is, by construction, the unique `K`-automorphism of `M` acting
as `γ` on the constants `L` and trivially on the `K`-twist field `K(C_h)`; as `M` is generated over
`K` by `L` and by the twisted coordinates `y_i = w^{-i} κ_i/κ_0` (`AM2_hgen`), two `K`-algebra
automorphisms agreeing there are equal (`AM2_algEquiv_ext`).  The two composites
`Θ ∘ ρ^{(h₁)}_γ` and `ρ^{(h₂)}_γ ∘ Θ` therefore coincide: on the constants both are `γ`, and on the
twisted coordinates `y_i` both are `Θ y_i`, since `ρ^{(h₁)}_γ` fixes `y_i` (`AM2_rhoFun_yM`),
`Θ y_i ∈ AM22` and `ρ^{(h₂)}_γ` fixes `AM22` (`AM2_rhoFun_fixes_AM22`). -/
theorem T4_compare {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic]
    (θ : twistFieldTK D h₁ ≃ₐ[K] twistFieldTK D h₂)
    (Θ : ML2 D h₁ h₂ hk ≃ₐ[↥(KummerField2 K h₁ h₂ hk)] ML2 D h₁ h₂ hk)
    (hΘ : ∀ x : ↥(AM21 D h₁ h₂ hk),
      (Θ (x : ML2 D h₁ h₂ hk) : ML2 D h₁ h₂ hk) =
        ((thetaL D hk θ x : ↥(AM22 D h₁ h₂ hk)) : ML2 D h₁ h₂ hk))
    (γ : ↥(KummerField2 K h₁ h₂ hk) ≃ₐ[K] ↥(KummerField2 K h₁ h₂ hk)) :
    ∀ x : ML2 D h₁ h₂ hk,
      Θ (AM2_rhoFun D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) γ x) =
        AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) γ
          (Θ x) := by
  intro x
  -- The two composites `Θ ∘ ρ^{(h₁)}_γ` and `ρ^{(h₂)}_γ ∘ Θ` agree on the `K`-generators of `M`.
  have hFG : (Θ.restrictScalars K) *
        (AM2_rhoFun D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) γ)
      = (AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) γ) *
        (Θ.restrictScalars K) := by
    refine AM2_algEquiv_ext D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk)
      _ _ ?_ ?_
    · -- On the constants `L`: both sides act by `γ`.
      intro l
      simp only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
      rw [AM2_rhoFun_algebraMap D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk)
            (wL1_pow_five K h₁ h₂ hk) γ l,
        Θ.commutes (γ l), Θ.commutes l,
        AM2_rhoFun_algebraMap D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk)
            (wL2_pow_five K h₁ h₂ hk) γ l]
    · -- On the twisted coordinates `y_i = AM2_yM (wL1) i`: both sides send them to `Θ y_i`.
      intro i
      simp only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
      rw [AM2_rhoFun_yM D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) γ i]
      have hy : AM2_yM D h₁ h₂ hk (wL1 K h₁ h₂ hk) i = yM21 D h₁ h₂ hk i := rfl
      rw [hy]
      -- `Θ y_i` lies in `AM22 = K(C_{h₂})`, which is fixed by `ρ^{(h₂)}_γ`.
      have htheta : Θ (yM21 D h₁ h₂ hk i) =
          ((thetaL D hk θ ⟨yM21 D h₁ h₂ hk i,
            IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩ : ↥(AM22 D h₁ h₂ hk)) :
              ML2 D h₁ h₂ hk) :=
        hΘ ⟨yM21 D h₁ h₂ hk i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
      rw [htheta]
      exact (AM2_rhoFun_fixes_AM22 D hD h₁ h₂ h₂0 hk γ _).symm
  -- Hence the composites are equal as automorphisms, and the claim follows by evaluation at `x`.
  calc Θ (AM2_rhoFun D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk) (wL1_pow_five K h₁ h₂ hk) γ x)
      = ((Θ.restrictScalars K) * (AM2_rhoFun D hD h₁ h₂ hk h₁ h₁0 (wL1 K h₁ h₂ hk)
          (wL1_pow_five K h₁ h₂ hk) γ)) x := rfl
    _ = ((AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk)
          (wL2_pow_five K h₁ h₂ hk) γ) * (Θ.restrictScalars K)) x := by rw [hFG]
    _ = AM2_rhoFun D hD h₁ h₂ hk h₂ h₂0 (wL2 K h₁ h₂ hk) (wL2_pow_five K h₁ h₂ hk) γ
          (Θ x) := rfl

end Work.MotT
