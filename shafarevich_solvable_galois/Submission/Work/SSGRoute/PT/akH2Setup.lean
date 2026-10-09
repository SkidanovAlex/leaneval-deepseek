/-
# Setup for `ak_h2_finite_of_openNormal`

Shared vocabulary for the Hochschild–Serre finiteness step: for a topological group `Γ`, an open
normal subgroup `N` of finite index, and a finite discrete `Γ`-module `M` on which `N` acts
trivially, finiteness of `H²(N,M)` and of `H¹(N,M)` implies finiteness of `H²(Γ,M)`.

This file builds the *coind module* `C = Coind_N^Γ M` (the model of the induced module the Shapiro
isomorphisms are proved for) together with

* the `Γ`-equivariant injection `iotaMap : M →+ C`, `m ↦ (g ↦ g⁻¹ • m)`;
* the quotient `QuotMod = C ⧸ iotaMap.range`, with its `Γ`-action, `π = piMap : C →+ QuotMod`;
* the discreteness of the actions on `C` and on `QuotMod`;
* the restriction map `resH1 : H¹(Γ,P) →+ H¹(N,P)` for a `Γ`-module `P`;
* `H¹`/`H²` transfer along an equivariant additive equivalence of coefficients.

The remaining pieces (the connecting map of the short exact sequence and its exactness, Shapiro's
lemma, and the two finiteness arguments) are assembled in
`Submission/Work/SSGRoute/PT/ak_h2_finite_of_openNormal.lean`.
-/
import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.PT.shapiro_H1_coind
import Submission.Work.SSGRoute.PT.shapiro_H2_coind
import Submission.Work.SSGRoute.H2locFin.coind_isFinite
import Submission.Work.SSGRoute.PT.isDiscreteModule_coind
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact_H2
import Submission.Work.GroupCohomology.Inflation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical

namespace Work.SSGRoute.PT
namespace H2Fin

universe u w w'

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-! ## 1. The action of a subgroup is discrete when the ambient action is -/

theorem isDiscreteModule_subgroup {A : Type w} [AddCommGroup A] [DistribMulAction Γ A]
    (N : Subgroup Γ) (h : Work.AbsoluteKummer.IsDiscreteModule Γ A) :
    Work.AbsoluteKummer.IsDiscreteModule N A := by
  intro a
  have hset : (MulAction.stabilizer N a : Set N) =
      (fun n : N => (n : Γ)) ⁻¹' (MulAction.stabilizer Γ a : Set Γ) := by
    ext n
    simp only [Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  rw [hset]
  exact (h a).preimage continuous_subtype_val

/-! ## 2. Transfer of `H¹` and `H²` along an equivariant additive equivalence -/

section Transfer

variable {A : Type w} {B : Type w'} [AddCommGroup A] [AddCommGroup B]
variable [DistribMulAction Γ A] [DistribMulAction Γ B]

theorem mapZ1_symm_comp (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (f : Work.AbsoluteKummer.Z1 Γ A) :
    Work.AbsoluteKummer.mapZ1 Φ.symm.toAddMonoidHom hΨ
        (Work.AbsoluteKummer.mapZ1 Φ.toAddMonoidHom hΦ f) = f := by
  ext g
  simp

theorem mapZ1_comp_symm (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (f : Work.AbsoluteKummer.Z1 Γ B) :
    Work.AbsoluteKummer.mapZ1 Φ.toAddMonoidHom hΦ
        (Work.AbsoluteKummer.mapZ1 Φ.symm.toAddMonoidHom hΨ f) = f := by
  ext g
  simp

theorem mapH1_symm_comp (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (x : Work.AbsoluteKummer.H1 Γ A) :
    Work.AbsoluteKummer.mapH1 Φ.symm.toAddMonoidHom hΨ
        (Work.AbsoluteKummer.mapH1 Φ.toAddMonoidHom hΦ x) = x := by
  refine QuotientAddGroup.induction_on x ?_
  intro f
  change Work.AbsoluteKummer.mapH1 Φ.symm.toAddMonoidHom hΨ
      (Work.AbsoluteKummer.mapH1 Φ.toAddMonoidHom hΦ
        (Work.AbsoluteKummer.H1π Γ A f)) = Work.AbsoluteKummer.H1π Γ A f
  rw [Work.AbsoluteKummer.mapH1_H1π, Work.AbsoluteKummer.mapH1_H1π,
    mapZ1_symm_comp Φ hΦ hΨ f]

theorem mapH1_comp_symm (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (x : Work.AbsoluteKummer.H1 Γ B) :
    Work.AbsoluteKummer.mapH1 Φ.toAddMonoidHom hΦ
        (Work.AbsoluteKummer.mapH1 Φ.symm.toAddMonoidHom hΨ x) = x := by
  refine QuotientAddGroup.induction_on x ?_
  intro f
  change Work.AbsoluteKummer.mapH1 Φ.toAddMonoidHom hΦ
      (Work.AbsoluteKummer.mapH1 Φ.symm.toAddMonoidHom hΨ
        (Work.AbsoluteKummer.H1π Γ B f)) = Work.AbsoluteKummer.H1π Γ B f
  rw [Work.AbsoluteKummer.mapH1_H1π, Work.AbsoluteKummer.mapH1_H1π,
    mapZ1_comp_symm Φ hΦ hΨ f]

/-- An equivariant additive isomorphism of coefficients induces an additive equivalence on `H¹`. -/
noncomputable def h1AddEquivOfEquiv (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom) :
    Work.AbsoluteKummer.H1 Γ A ≃+ Work.AbsoluteKummer.H1 Γ B :=
  AddMonoidHom.toAddEquiv
    (Work.AbsoluteKummer.mapH1 Φ.toAddMonoidHom hΦ)
    (Work.AbsoluteKummer.mapH1 Φ.symm.toAddMonoidHom hΨ)
    (AddMonoidHom.ext fun x => mapH1_symm_comp Φ hΦ hΨ x)
    (AddMonoidHom.ext fun x => mapH1_comp_symm Φ hΦ hΨ x)

theorem h1_equiv_of_equiv (Φ : A ≃+ B)
    (h : ∀ (g : Γ) (a : A), Φ (g • a) = g • Φ a) :
    Nonempty (Work.AbsoluteKummer.H1 Γ A ≃+ Work.AbsoluteKummer.H1 Γ B) := by
  have hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom := fun g m => h g m
  have hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom := by
    intro g n
    change Φ.symm (g • n) = g • Φ.symm n
    rw [AddEquiv.symm_apply_eq, h g (Φ.symm n), Φ.apply_symm_apply]
  exact ⟨h1AddEquivOfEquiv Φ hΦ hΨ⟩

/-- `mapZ2` for `Φ.symm` is a left inverse of `mapZ2` for `Φ`. -/
theorem mapZ2_symm_comp (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (f : Work.AbsoluteKummer.Z2 Γ A) :
    Work.AbsoluteKummer.mapZ2 Φ.symm.toAddMonoidHom hΨ
        (Work.AbsoluteKummer.mapZ2 Φ.toAddMonoidHom hΦ f) = f := by
  ext p
  simp

/-- `mapZ2` for `Φ.symm` is a right inverse of `mapZ2` for `Φ`. -/
theorem mapZ2_comp_symm (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (f : Work.AbsoluteKummer.Z2 Γ B) :
    Work.AbsoluteKummer.mapZ2 Φ.toAddMonoidHom hΦ
        (Work.AbsoluteKummer.mapZ2 Φ.symm.toAddMonoidHom hΨ f) = f := by
  ext p
  simp

theorem mapH2_symm_comp (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (x : Work.AbsoluteKummer.H2 Γ A) :
    Work.AbsoluteKummer.mapH2 Φ.symm.toAddMonoidHom hΨ
        (Work.AbsoluteKummer.mapH2 Φ.toAddMonoidHom hΦ x) = x := by
  refine QuotientAddGroup.induction_on x ?_
  intro f
  change Work.AbsoluteKummer.mapH2 Φ.symm.toAddMonoidHom hΨ
      (Work.AbsoluteKummer.mapH2 Φ.toAddMonoidHom hΦ
        (Work.AbsoluteKummer.H2π Γ A f)) = Work.AbsoluteKummer.H2π Γ A f
  rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π,
    mapZ2_symm_comp Φ hΦ hΨ f]

theorem mapH2_comp_symm (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (x : Work.AbsoluteKummer.H2 Γ B) :
    Work.AbsoluteKummer.mapH2 Φ.toAddMonoidHom hΦ
        (Work.AbsoluteKummer.mapH2 Φ.symm.toAddMonoidHom hΨ x) = x := by
  refine QuotientAddGroup.induction_on x ?_
  intro f
  change Work.AbsoluteKummer.mapH2 Φ.toAddMonoidHom hΦ
      (Work.AbsoluteKummer.mapH2 Φ.symm.toAddMonoidHom hΨ
        (Work.AbsoluteKummer.H2π Γ B f)) = Work.AbsoluteKummer.H2π Γ B f
  rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π,
    mapZ2_comp_symm Φ hΦ hΨ f]

/-- An equivariant additive isomorphism of coefficients induces an additive equivalence on `H²`. -/
noncomputable def h2AddEquivOfEquiv (Φ : A ≃+ B)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom) :
    Work.AbsoluteKummer.H2 Γ A ≃+ Work.AbsoluteKummer.H2 Γ B :=
  AddMonoidHom.toAddEquiv
    (Work.AbsoluteKummer.mapH2 Φ.toAddMonoidHom hΦ)
    (Work.AbsoluteKummer.mapH2 Φ.symm.toAddMonoidHom hΨ)
    (AddMonoidHom.ext fun x => mapH2_symm_comp Φ hΦ hΨ x)
    (AddMonoidHom.ext fun x => mapH2_comp_symm Φ hΦ hΨ x)

theorem h2_equiv_of_equiv (Φ : A ≃+ B)
    (h : ∀ (g : Γ) (a : A), Φ (g • a) = g • Φ a) :
    Nonempty (Work.AbsoluteKummer.H2 Γ A ≃+ Work.AbsoluteKummer.H2 Γ B) := by
  have hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom := fun g m => h g m
  have hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom := by
    intro g n
    change Φ.symm (g • n) = g • Φ.symm n
    rw [AddEquiv.symm_apply_eq, h g (Φ.symm n), Φ.apply_symm_apply]
  exact ⟨h2AddEquivOfEquiv Φ hΦ hΨ⟩

end Transfer

/-! ## 3. The coind module: the `N`-action is trivial -/

variable {M : Type w} [AddCommGroup M] [DistribMulAction Γ M]

theorem coind_smul_eq_self (N : Subgroup Γ) [N.Normal]
    (htriv : ∀ (n : N) (m : M), n • m = m) (n : N) (f : Coind Γ N M) : n • f = f := by
  apply Subtype.ext
  funext x
  show f ((n : Γ)⁻¹ * x) = f x
  have hmem : x⁻¹ * (n : Γ)⁻¹ * x ∈ N :=
    (inferInstance : N.Normal).conj_mem' (n : Γ)⁻¹ (n⁻¹).2 x
  have hidx : (n : Γ)⁻¹ * x = x * ((⟨x⁻¹ * (n : Γ)⁻¹ * x, hmem⟩ : N) : Γ) := by
    simp only [Subgroup.coe_mk]
    group
  rw [hidx, Coind.coe_mul]
  exact htriv _ _

/-! ## 4. The equivariant injection `M → Coind_N^Γ M` -/

noncomputable def iotaFun (N : Subgroup Γ) (m : M) : Coind Γ N M :=
  ⟨fun g => g⁻¹ • m, by
    intro g u
    show (g * (u : Γ))⁻¹ • m = u⁻¹ • (g⁻¹ • m)
    simp only [mul_inv_rev, mul_smul, Subgroup.smul_def, Subgroup.coe_inv]⟩

noncomputable def iotaMap (N : Subgroup Γ) : M →+ Coind Γ N M where
  toFun := iotaFun N
  map_zero' := by
    apply Subtype.ext
    funext g
    simp [iotaFun]
  map_add' m m' := by
    apply Subtype.ext
    funext g
    simp [iotaFun, smul_add]

theorem iotaMap_equivariant (N : Subgroup Γ) :
    Work.GroupCohomology.IsEquivariant Γ (iotaMap (M := M) N) := by
  intro g m
  apply Subtype.ext
  funext x
  have h1 : ((iotaMap (M := M) N) (g • m) : Γ → M) x = x⁻¹ • (g • m) := rfl
  have h2 : ((g • (iotaMap (M := M) N) m : Coind Γ N M) : Γ → M) x = (g⁻¹ * x)⁻¹ • m := by
    rw [Coind.smul_apply]
    rfl
  rw [h1, h2, mul_inv_rev, mul_smul, inv_inv]

theorem iotaMap_injective (N : Subgroup Γ) : Function.Injective (iotaMap (M := M) N) := by
  intro m m' h
  have h1 := congrFun (congrArg (fun f : Coind Γ N M => (f : Γ → M)) h) 1
  simpa [iotaMap, iotaFun] using h1

/-! ## 5. The quotient `C ⧸ ι(M)` as a `Γ`-module -/

/-- The quotient `Coind_N^Γ M ⧸ ι(M)`, the cokernel of the injection `ι : M ↪ Coind_N^Γ M`. -/
abbrev QuotMod (N : Subgroup Γ) : Type _ :=
  (Coind Γ N M) ⧸ (iotaMap (M := M) N).range

noncomputable def smulHom (N : Subgroup Γ) (g : Γ) : Coind Γ N M →+ Coind Γ N M where
  toFun f := g • f
  map_zero' := smul_zero g
  map_add' f f' := smul_add g f f'

theorem smul_mem_range_iotaMap (N : Subgroup Γ) (g : Γ) {a : Coind Γ N M}
    (ha : a ∈ (iotaMap (M := M) N).range) :
    (smulHom (M := M) N g) a ∈ (iotaMap (M := M) N).range := by
  obtain ⟨m, rfl⟩ := ha
  refine ⟨g • m, ?_⟩
  show iotaMap (M := M) N (g • m) = g • iotaMap (M := M) N m
  exact iotaMap_equivariant (M := M) N g m

theorem range_le_ker_comp (N : Subgroup Γ) (g : Γ) :
    (iotaMap (M := M) N).range ≤
      ((QuotientAddGroup.mk' (iotaMap (M := M) N).range).comp
        (smulHom (M := M) N g)).ker := by
  intro a ha
  rw [AddMonoidHom.mem_ker]
  have h1 : ((QuotientAddGroup.mk' (iotaMap (M := M) N).range).comp
      (smulHom (M := M) N g)) a =
      (((smulHom (M := M) N g) a : Coind Γ N M) : QuotMod (M := M) N) := rfl
  rw [h1, QuotientAddGroup.eq_zero_iff (N := (iotaMap (M := M) N).range)]
  exact smul_mem_range_iotaMap (M := M) N g ha

noncomputable def actHom (N : Subgroup Γ) (g : Γ) : QuotMod (M := M) N →+ QuotMod (M := M) N :=
  QuotientAddGroup.lift (iotaMap (M := M) N).range
    ((QuotientAddGroup.mk' (iotaMap (M := M) N).range).comp (smulHom (M := M) N g))
    (range_le_ker_comp (M := M) N g)

theorem actHom_coe (N : Subgroup Γ) (g : Γ) (a : Coind Γ N M) :
    actHom (M := M) N g ((a : Coind Γ N M) : QuotMod (M := M) N) =
      ((g • a : Coind Γ N M) : QuotMod (M := M) N) :=
  QuotientAddGroup.lift_mk' (iotaMap (M := M) N).range (range_le_ker_comp (M := M) N g) a

noncomputable instance instSMulQuotMod (N : Subgroup Γ) : SMul Γ (QuotMod (M := M) N) where
  smul g q := actHom (M := M) N g q

theorem smulQuotMod_coe (N : Subgroup Γ) (g : Γ) (a : Coind Γ N M) :
    g • ((a : Coind Γ N M) : QuotMod (M := M) N) =
      ((g • a : Coind Γ N M) : QuotMod (M := M) N) :=
  actHom_coe N g a

noncomputable instance instDistribMulActionQuotMod (N : Subgroup Γ) :
    DistribMulAction Γ (QuotMod (M := M) N) where
  one_smul q := by
    refine QuotientAddGroup.induction_on q ?_
    intro a
    rw [smulQuotMod_coe]
    simp
  mul_smul g h q := by
    refine QuotientAddGroup.induction_on q ?_
    intro a
    rw [smulQuotMod_coe, smulQuotMod_coe, smulQuotMod_coe]
    simp only [mul_smul]
  smul_zero g := map_zero (actHom (M := M) N g)
  smul_add g q q' := map_add (actHom (M := M) N g) q q'

/-! ## 6. The projection `π : Coind_N^Γ M → C ⧸ ι(M)` -/

noncomputable def piMap (N : Subgroup Γ) : Coind Γ N M →+ QuotMod (M := M) N :=
  QuotientAddGroup.mk' (iotaMap (M := M) N).range

theorem piMap_equivariant (N : Subgroup Γ) :
    Work.GroupCohomology.IsEquivariant Γ (piMap (M := M) N) := by
  intro g a
  rw [show piMap (M := M) N (g • a) =
      ((g • a : Coind Γ N M) : QuotMod (M := M) N) from rfl,
    show piMap (M := M) N a = ((a : Coind Γ N M) : QuotMod (M := M) N) from rfl,
    smulQuotMod_coe]

theorem piMap_surjective (N : Subgroup Γ) : Function.Surjective (piMap (M := M) N) :=
  QuotientAddGroup.mk'_surjective _

theorem range_iotaMap_eq_ker_piMap (N : Subgroup Γ) :
    (iotaMap (M := M) N).range = (piMap (M := M) N).ker := by
  ext a
  rw [AddMonoidHom.mem_ker, show piMap (M := M) N a = ((a : Coind Γ N M) : QuotMod (M := M) N)
    from rfl]
  exact (QuotientAddGroup.eq_zero_iff (N := (iotaMap (M := M) N).range) a).symm

/-! ## 7. Discreteness of the action on the quotient -/

theorem isDiscreteModule_quotMod (N : Subgroup Γ)
    (hC : Work.AbsoluteKummer.IsDiscreteModule Γ (Coind Γ N M)) :
    Work.AbsoluteKummer.IsDiscreteModule Γ (QuotMod (M := M) N) := by
  intro q
  rw [isOpen_iff_mem_nhds]
  intro g₀ hg₀
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (iotaMap (M := M) N).range q
  have hlc : Work.AbsoluteKummer.IsLocallyConstant
      (fun g : Γ => g • (QuotientAddGroup.mk' (iotaMap (M := M) N).range a :
        QuotMod (M := M) N)) :=
    (Work.AbsoluteKummer.isLocallyConstant_smul_of_isDiscreteModule hC a).map
      (fun c : Coind Γ N M => (QuotientAddGroup.mk' (iotaMap (M := M) N).range c :
        QuotMod (M := M) N))
  obtain ⟨U, hU, hgU, hUconst⟩ := hlc g₀
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hg₀
  refine Filter.mem_of_superset (hU.mem_nhds hgU) ?_
  intro g hg
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  exact (hUconst g hg).trans hg₀


/-! ## 6b. The same equivariance for the restricted action of the subgroup `N` -/

theorem iotaMap_equivariant_sub (N : Subgroup Γ) :
    Work.GroupCohomology.IsEquivariant N (iotaMap (M := M) N) := by
  intro n m
  simpa only [Subgroup.smul_def] using iotaMap_equivariant (M := M) N (n : Γ) m

theorem piMap_equivariant_sub (N : Subgroup Γ) :
    Work.GroupCohomology.IsEquivariant N (piMap (M := M) N) := by
  intro n a
  simpa only [Subgroup.smul_def] using piMap_equivariant (M := M) N (n : Γ) a

/-! ## 7b. Finiteness of the range of a map with finite domain -/

theorem finite_range_of_finite {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hA : Finite A) : Finite f.range := by
  haveI := hA
  refine Finite.of_surjective (fun a : A => (⟨f a, ⟨a, rfl⟩⟩ : f.range)) ?_
  rintro ⟨b, a, rfl⟩
  exact ⟨a, rfl⟩

theorem finite_subtype {α : Type*} (p : α → Prop) [Finite α] : Finite {x // p x} :=
  Finite.of_injective (Subtype.val) Subtype.coe_injective

/-! ## 8. The restriction map `H¹(Γ,P) → H¹(N,P)` -/

theorem isCrossedHom_restrict (N : Subgroup Γ) {P : Type w} [AddCommGroup P]
    [DistribMulAction Γ P] {f : Γ → P} (hf : Work.GroupCohomology.IsCrossedHom Γ P f) :
    Work.GroupCohomology.IsCrossedHom N P (fun n : N => f (n : Γ)) := by
  intro n m
  show f (↑n * ↑m) = n • f ↑m + f ↑n
  rw [hf (n : Γ) (m : Γ), Subgroup.smul_def]

noncomputable def resZ1 (N : Subgroup Γ) (P : Type w) [AddCommGroup P] [DistribMulAction Γ P] :
    Work.AbsoluteKummer.Z1 Γ P →+ Work.AbsoluteKummer.Z1 N P where
  toFun f := ⟨fun n : N => (f : Γ → P) (n : Γ), by
    rw [Work.AbsoluteKummer.mem_Z1_iff]
    exact ⟨isCrossedHom_restrict N ((Work.AbsoluteKummer.mem_Z1_iff (G := Γ) (M := P) _).mp f.2).1,
      ((Work.AbsoluteKummer.mem_Z1_iff (G := Γ) (M := P) _).mp f.2).2.comp continuous_subtype_val⟩⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    rfl
  map_add' f g := by
    apply Subtype.ext
    funext n
    rfl

/-- Restriction of continuous `1`-cocycles to a subgroup, on cohomology. -/
noncomputable def resH1 (N : Subgroup Γ) (P : Type w) [AddCommGroup P] [DistribMulAction Γ P] :
    Work.AbsoluteKummer.H1 Γ P →+ Work.AbsoluteKummer.H1 N P :=
  QuotientAddGroup.lift ((Work.AbsoluteKummer.B1 Γ P).comap (Work.AbsoluteKummer.Z1 Γ P).subtype)
    ((Work.AbsoluteKummer.H1π N P).comp (resZ1 N P))
    (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.AbsoluteKummer.H1π_eq_zero_iff]
      rw [AddSubgroup.mem_comap] at hx
      obtain ⟨a, ha⟩ := (Work.AbsoluteKummer.mem_B1_iff (G := Γ) (M := P) _).mp hx
      refine (Work.AbsoluteKummer.mem_B1_iff (G := N) (M := P) _).mpr ⟨a, ?_⟩
      funext n
      have h2 := congrFun ha (n : Γ)
      rw [Work.GroupCohomology.d0_apply] at h2
      rw [Work.GroupCohomology.d0_apply, Subgroup.smul_def]
      exact h2)

theorem resH1_H1π (N : Subgroup Γ) (P : Type w) [AddCommGroup P] [DistribMulAction Γ P]
    (f : Work.AbsoluteKummer.Z1 Γ P) :
    resH1 N P (Work.AbsoluteKummer.H1π Γ P f) = Work.AbsoluteKummer.H1π N P (resZ1 N P f) :=
  QuotientAddGroup.lift_mk' _ _ _

/-! ## 9. Finiteness from finiteness of kernel and range -/

theorem finite_of_finite_ker_range {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hk : Finite f.ker) (hr : Finite f.range) : Finite A := by
  classical
  haveI := hk
  haveI := hr
  have hsec : ∀ y : f.range, ∃ a : A, f a = (y : B) := fun y => y.2
  let s : f.range → A := fun y => Classical.choose (hsec y)
  have hs : ∀ y : f.range, f (s y) = (y : B) := fun y => Classical.choose_spec (hsec y)
  have hmem : ∀ x : A, x - s ⟨f x, x, rfl⟩ ∈ f.ker := by
    intro x
    rw [AddMonoidHom.mem_ker, map_sub, hs ⟨f x, x, rfl⟩, sub_self]
  let g : A → f.ker × f.range := fun x =>
    (⟨x - s ⟨f x, x, rfl⟩, hmem x⟩, ⟨f x, x, rfl⟩)
  have hinj : Function.Injective g := by
    intro x y hxy
    have h2 : (⟨f x, x, rfl⟩ : f.range) = ⟨f y, y, rfl⟩ := congrArg Prod.snd hxy
    have h1 : (⟨x - s ⟨f x, x, rfl⟩, hmem x⟩ : f.ker) = ⟨y - s ⟨f y, y, rfl⟩, hmem y⟩ :=
      congrArg Prod.fst hxy
    have h1' : x - s ⟨f x, x, rfl⟩ = y - s ⟨f y, y, rfl⟩ := congrArg Subtype.val h1
    rw [h2] at h1'
    have h5 := congrArg (fun z => z + s ⟨f y, y, rfl⟩) h1'
    simpa [sub_add_cancel] using h5
  exact Finite.of_injective g hinj

end H2Fin
end Work.SSGRoute.PT
