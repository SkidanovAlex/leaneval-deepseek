import Mathlib
import Submission.Work.SSGRoute.ext_continuous_descent_fg
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.ext_level_lift
import Submission.Work.SSGRoute.PT.e1a_chain
import Submission.Work.SSGRoute.homCoind_H1_free_conj_v2
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact_H2
import Submission.Work.SSGRoute.local_ext_h1_bridge
import Submission.Work.SSGRoute.h1_equiv_of_equiv
import Submission.Work.SSGRoute.PT.h2_equiv_of_equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

namespace Work.SSGRoute.PT.e1aBetaLocalChain

open CategoryTheory

universe u

/-! ## `Module.Finite` transfers between `ℤ` and `Coeff = ULift ℤ` -/

/-- For the underlying type of a `Rep Coeff G`, finiteness over `ℤ` implies finiteness over
`Coeff = ULift ℤ`. -/
lemma module_finite_ulift_of_repFG {G : Type} [Group G]
    (R : Rep.{0} SSGRoute.PTExt.Coeff G) (h : Module.Finite ℤ R.V) :
    Module.Finite (ULift.{u} ℤ) R.V := by
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := ℤ) (M := R.V))
  refine Module.Finite.of_fg_top ⟨hSfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x ∈ Submodule.span ℤ S := by rw [hSspan]; exact Submodule.mem_top
  refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (ULift.{u} ℤ) S)
    (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _)
    (fun y z _ _ hy hz => Submodule.add_mem _ hy hz) ?_ hx
  intro c y _ hy
  rw [← Work.SSGRoute.ulift_up_smul_eq_zsmul (V := R.V) c y]
  exact Submodule.smul_mem _ _ hy

/-- Finiteness over `Coeff = ULift ℤ` implies finiteness over `ℤ`. -/
lemma repFG_of_module_finite_ulift {M : Type} [AddCommGroup M] [Module (ULift.{u} ℤ) M]
    [Module.Finite (ULift.{u} ℤ) M] : Module.Finite ℤ M := by
  obtain ⟨S, hSfin, hSspan⟩ :=
    Submodule.fg_def.mp (Module.Finite.fg_top (R := ULift.{u} ℤ) (M := M))
  have hclos : AddSubgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Work.SSGRoute.mem_addSubgroup_closure_of_mem_span S
      (by rw [hSspan]; exact Submodule.mem_top)
  refine Module.Finite.of_fg_top ⟨hSfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  rw [← AddSubgroup.toIntSubmodule_closure S, hclos]
  exact AddSubgroup.toIntSubmodule.map_top

theorem ext_two_local_descent_injective
    (p : ℕ) [Fact p.Prime] {L M : Type} [Field L] [CharZero L] [Field M] [Algebra L M]
    [IsAlgClosure L M] (K : IntermediateField L M) [FiniteDimensional L K] [IsGalois L K]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[L] K)) [Module.Finite (ULift ℤ) X.V] :
    ∃ Λ : CategoryTheory.Abelian.Ext X (Work.SSGRoute.SSGDescent.ssgCoeffK L M K) 2 →+
        Work.AbsoluteKummer.H2 (M ≃ₐ[L] M) (Work.SSGRoute.SSGDescent.ssgHom L M K X),
      Function.Injective Λ := by
  classical
  -- ## (1) a finite free cover `0 → R → F → X → 0` of `X`
  haveI hXZ : Module.Finite ℤ X.V := repFG_of_module_finite_ulift
  obtain ⟨n, pic, hpic⟩ := Work.SSGRoute.repFG_free_cover (G := K ≃ₐ[L] K) X hXZ
  have hfsurj : Function.Surjective (Rep.Hom.hom pic) := (Rep.epi_iff_surjective pic).mp hpic
  let S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[L] K)) :=
    ShortComplex.mk (Limits.kernel.ι pic) pic (Limits.kernel.condition pic)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel pic) inferInstance hpic
  -- ## (2) the syzygy `R = S.X₁` is finitely generated over `ℤ` and over `Coeff`
  haveI hfgZ : Module.Finite ℤ S.X₁.V := Work.SSGRoute.repFG_kernel (G := K ≃ₐ[L] K) X pic
  haveI hfgU : Module.Finite (ULift.{0} ℤ) S.X₁.V := module_finite_ulift_of_repFG S.X₁ hfgZ
  -- ## (3) the chain `Ext²(X,Kˣ) ≃ Ext¹(R,Kˣ) ≃ H¹(G, Hom_ℤ(infl R, Mˣ))` of the descent
  obtain ⟨eShift⟩ := Work.SSGRoute.ext_shift_of_projective_presentation (K ≃ₐ[L] K) S hS
    (Work.SSGRoute.SSGDescent.ssgCoeffK L M K) 1 le_rfl
  obtain ⟨eDesc⟩ := Work.SSGRoute.ext_continuous_descent_fg (L := L) (M := M) K S.X₁
  -- ## (4) the two spellings of the coefficient module
  obtain ⟨eH1⟩ := Work.SSGRoute.h1_equiv_of_equiv (Work.SSGRoute.ssgHomEquiv L M K S.X₁)
    (fun σ f => Work.SSGRoute.ssgHomEquiv_equivariant L M K S.X₁ σ f)
  obtain ⟨eH2⟩ := Work.SSGRoute.PT.h2_equiv_of_equiv (Work.SSGRoute.ssgHomEquiv L M K X)
    (fun σ f => Work.SSGRoute.ssgHomEquiv_equivariant L M K X σ f)
  -- ## (5) the injective connecting map `δ : H¹(G, Hom_ℤ(R,Mˣ)) → H²(G, Hom_ℤ(X,Mˣ))`
  obtain ⟨-, δ, -, hδinj, -⟩ :=
    Work.SSGRoute.PT.e1a_deltaH2 (k := L) (Ω := M) (K := K) X n pic hfsurj
  -- ## assembly: `Λ = eH2⁻¹ ∘ δ ∘ eH1 ∘ eDesc ∘ eShift⁻¹`
  refine ⟨AddMonoidHom.comp (eH2.symm.toAddMonoidHom)
    (AddMonoidHom.comp δ (AddMonoidHom.comp eH1.toAddMonoidHom
      ((eShift.symm.trans eDesc).toAddMonoidHom))), ?_⟩
  intro a b hab
  have hab' : (eH2.symm) (δ (eH1 (eDesc (eShift.symm a))))
      = (eH2.symm) (δ (eH1 (eDesc (eShift.symm b)))) := hab
  exact (eShift.symm.trans eDesc).injective (eH1.injective (hδinj (eH2.symm.injective hab')))

end Work.SSGRoute.PT.e1aBetaLocalChain
