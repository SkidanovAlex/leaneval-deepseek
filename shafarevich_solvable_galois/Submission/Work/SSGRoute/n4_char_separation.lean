import Mathlib
import Submission.Work.SSGRoute.EscapeCoreLib.charSeparation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Characters separate points of a finite quotient of exponent `p`

The logical step which turns "every character of `C_K ⧸ U'` killing `N_{N/K}C_N` kills the class of
`𝔡`" into the membership `[𝔡] ∈ U' ⊔ N_{N/K}C_N` in the orthogonality computation of the
escape-form Grünwald theorem (node N4's contribution; the `δ`-free/idele-idèle half is in
`n4_idele_factor.lean`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open Work.SSGRoute.EscapeCoreLib

/-- **Characters separate points of a finite quotient of exponent `p`.** -/
theorem charSeparation_exponent_p {p : ℕ} [Fact p.Prime] {C : Type*} [CommGroup C]
    (U W : Subgroup C) (hU : pPowSubgroup p C ≤ U)
    [Finite (C ⧸ (U ⊔ W))] (x : C) :
    x ∈ U ⊔ W ↔ ∀ χ : C →* Multiplicative (ZMod p),
      (∀ u ∈ U ⊔ W, χ u = 1) → χ x = 1 := by
  classical
  -- the quotient `C ⧸ (U ⊔ W)` has exponent dividing `p`
  have hpow : ∀ g : C ⧸ (U ⊔ W), g ^ p = 1 := by
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (U ⊔ W) g
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (c ^ p)).mpr
      (Subgroup.mem_sup_left (hU (pow_mem_pPowSubgroup c)))
  -- the `ZMod p`-module structure on the additive group of the quotient
  letI : Module (ZMod p) (Additive (C ⧸ (U ⊔ W))) :=
    AddCommGroup.zmodModule (fun a => by
      refine Additive.ext ?_
      have h1 : Additive.toMul (p • a) = Additive.toMul a ^ p := by simp
      rw [h1, hpow a.toMul]
      rfl)
  constructor
  · intro hx χ hχ
    exact hχ x hx
  · intro h
    -- every linear functional of the quotient vanishes at the class of `x`
    have hkey : ∀ f : Additive (C ⧸ (U ⊔ W)) →ₗ[ZMod p] ZMod p,
        f.toAddMonoidHom (Additive.ofMul (QuotientGroup.mk' (U ⊔ W) x)) = 0 := by
      intro f
      have hχ := h (MonoidHom.mk' (fun u : C => Multiplicative.ofAdd
        (f.toAddMonoidHom (Additive.ofMul (QuotientGroup.mk' (U ⊔ W) u)))) (by
          intro a b
          simp only [map_mul, map_add, ofMul_mul, ofAdd_add])) (by
          intro u hu
          show Multiplicative.ofAdd (f.toAddMonoidHom
            (Additive.ofMul (QuotientGroup.mk' (U ⊔ W) u))) = 1
          rw [show QuotientGroup.mk' (U ⊔ W) u = 1 from (QuotientGroup.eq_one_iff u).mpr hu]
          simp)
      simpa using hχ
    have hmem := mem_of_forall_linearMap_eq_zero (p := p) (A := Additive (C ⧸ (U ⊔ W)))
      (H := ⊥) (x := Additive.ofMul (QuotientGroup.mk' (U ⊔ W) x)) (fun f _ => hkey f)
    rw [Submodule.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp (Additive.ext hmem)

end Work.SSGRoute
