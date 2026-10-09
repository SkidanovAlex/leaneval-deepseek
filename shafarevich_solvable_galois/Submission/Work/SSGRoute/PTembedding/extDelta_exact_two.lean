import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace Work.SSGRoute.PTembedding

/-- Auxiliary vanishing: for any short exact sequence `S` of `Coeff`-representations and any
`x ∈ Ext^r_G(·, S.X₃)`, the composite of the connecting class `hS.extClass` with `S.f` is zero, so
the `S.f`-pushforward of `x ⋔ hS.extClass` dies.  Everything is phrased in the vocabulary of `S`
itself, so that no reduction of the concrete class formation is needed. -/
theorem extToIdeles_extDelta_aux (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K]
    {S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))} (hS : S.ShortExact)
    {X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (x : CategoryTheory.Abelian.Ext X S.X₃ r) :
    (x.comp hS.extClass rfl).comp
      (CategoryTheory.Abelian.Ext.mk₀ S.f) (Nat.add_zero _) = 0 := by
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [ShortComplex.ShortExact.extClass_comp]
  simp

/-- **Exactness of the class formation at `Ext²(M, Kˣ)`**: a class of `Ext²(M, Kˣ)` is the image
under the connecting map `extDelta` of a class of `Ext¹(M, C_K)` if and only if it dies under
`extToIdeles : Ext²(M,Kˣ) → Ext²(M,𝕀_K)`, i.e. `im extDelta = ker extToIdeles`.  This is the
degree-two companion of the proved `SSGRoute.PTExt.exists_extToClasses_iff_extDelta_eq_zero`
(`ker extDelta = im extToClasses`).  The `←` direction is already available in the workspace as
`Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` (general degree), so this
node is the `↔` packaging in the `PTembedding` namespace; import that file if it helps. -/
lemma extDelta_exact_two
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (y : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.unitsK k K) 2) :
    (∃ x : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.classesK k K) 1,
        SSGRoute.PTExt.extDelta x = y) ↔ SSGRoute.PTExt.extToIdeles y = 0 := by
  have hS := NK.HassePrinciple.ideleShortComplex_shortExact k K
  constructor
  · -- `→`: the image of `extDelta` dies under `extToIdeles`.
    rintro ⟨x, rfl⟩
    exact extToIdeles_extDelta_aux (k := k) (K := K)
      (S := NK.HassePrinciple.ideleShortComplex k K)
      (hS := NK.HassePrinciple.ideleShortComplex_shortExact k K) (X := M) (r := 1) x
  · -- `←`: the connecting-map preimage supplied by the long exact sequence of `Ext`.
    intro hy
    obtain ⟨x, hx⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ (X := M)
      (S := SSGRoute.PTExt.sesK k K) hS y (n₁ := 2) hy (n₀ := 1) (hn₀ := rfl)
    exact ⟨x, hx⟩

end Work.SSGRoute.PTembedding
