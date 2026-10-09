import Submission.Work.SSGRoute.PT.shapiro_defs
import Submission.Work.SSGRoute.PT.coindCocycle_crossed
import Submission.Work.SSGRoute.PT.coindCocycle_eventually_zero
import Submission.Work.SSGRoute.PT.mem_B1_of_val_one_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.SSGRoute.PT

open Work.AbsoluteKummer

noncomputable section

/-! ## Pointwise descriptions of the `Coind`- and `Z¹`-operations -/

section Ops

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]

theorem z1_coe_add (f g : Z1 G A) (x : G) :
    (((f + g : Z1 G A) : G → A) x) = (f : G → A) x + (g : G → A) x := rfl

theorem z1_coe_sub (f g : Z1 G A) (x : G) :
    (((f - g : Z1 G A) : G → A) x) = (f : G → A) x - (g : G → A) x := rfl

theorem z1_coe_zero (x : G) : (((0 : Z1 G A) : G → A) x) = 0 := rfl

end Ops

section CoindOps

variable {G : Type*} [Group G] (U : Subgroup G)
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

@[simp] theorem coind_add_apply (f g : Coind G U M) (x : G) :
    ((f + g : Coind G U M) : G → M) x = (f : G → M) x + (g : G → M) x := rfl

@[simp] theorem coind_sub_apply (f g : Coind G U M) (x : G) :
    ((f - g : Coind G U M) : G → M) x = (f : G → M) x - (g : G → M) x := rfl

@[simp] theorem coind_zero_apply (x : G) :
    ((0 : Coind G U M) : G → M) x = 0 := rfl

end CoindOps

/-! ## Local constancy of the Shapiro cochain -/

theorem coindCocycle_isLocallyConstant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] (φ : U → M)
    (hφ : Work.GroupCohomology.IsCrossedHom U M φ)
    (hφc : Work.AbsoluteKummer.IsLocallyConstant φ) :
    Work.AbsoluteKummer.IsLocallyConstant (coindCocycle U φ) := by
  obtain ⟨V, hVopen, hV1, hV0⟩ := coindCocycle_eventually_zero U hU φ hφ hφc
  intro g₀
  refine ⟨{g : G | g₀⁻¹ * g ∈ V}, hVopen.preimage (continuous_const.mul continuous_id),
    by simpa using hV1, ?_⟩
  intro g hg
  have hg' : g₀ * (g₀⁻¹ * g) = g := by group
  rw [← hg', coindCocycle_crossed U φ hφ g₀ (g₀⁻¹ * g), hV0 (g₀⁻¹ * g) hg, smul_zero, zero_add]

/-! ## The coboundary attached to `m : M` -/

section Const

variable {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

/-- The element `x ↦ coord U x • m` of the coinduced module. -/
def coindConst (m : M) : Coind G U M :=
  ⟨fun x => coord U x • m, by
    intro x u
    show coord U (x * (u : G)) • m = u⁻¹ • (coord U x • m)
    rw [coord_mul U x u, mul_smul]⟩

@[simp] theorem coindConst_apply (m : M) (x : G) :
    (coindConst U m : G → M) x = coord U x • m := rfl

theorem coindCocycle_d0 (m : M) :
    coindCocycle U (fun u : U => u • m - m) =
      Work.GroupCohomology.d0 G (Coind G U M) (coindConst U m) := by
  funext g
  apply Subtype.ext
  funext x
  show coord U x • ((Shapiro.A 0 G U g (x : G ⧸ U)) • m - m)
      = (((g • coindConst U m - coindConst U m : Coind G U M)) : G → M) x
  rw [coind_sub_apply, Coind.smul_apply, coindConst_apply, coindConst_apply]
  rw [smul_sub, ← mul_smul, coord_smul U g x]

theorem coindCocycle_mem_B1 (m : M) :
    (coindCocycle U (fun u : U => u • m - m)) ∈ B1 G (Coind G U M) :=
  (mem_B1_iff (coindCocycle U (fun u : U => u • m - m))).mpr
    ⟨coindConst U m, (coindCocycle_d0 U m).symm⟩

/-! ## Additivity of the Shapiro cochain in `φ` -/

theorem coindCocycle_zero :
    coindCocycle U (0 : U → M) = 0 := by
  funext g
  apply Subtype.ext
  funext x
  show coord U x • ((0 : U → M) (Shapiro.A 0 G U g (x : G ⧸ U)))
      = (((0 : Coind G U M)) : G → M) x
  rw [coind_zero_apply, Pi.zero_apply, smul_zero]

theorem coindCocycle_add (φ ψ : U → M) :
    coindCocycle U (φ + ψ) = coindCocycle U φ + coindCocycle U ψ := by
  funext g
  apply Subtype.ext
  funext x
  show coord U x • ((φ + ψ) (Shapiro.A 0 G U g (x : G ⧸ U)))
      = (((coindCocycle U φ g + coindCocycle U ψ g : Coind G U M)) : G → M) x
  rw [coind_add_apply, coindCocycle_apply, coindCocycle_apply, Pi.add_apply, smul_add]

end Const

/-! ## The Shapiro cochain as a map `Z¹(U,M) → Z¹(G, Coind)` -/

def coindZ1 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] :
    Z1 U M →+ Z1 G (Coind G U M) where
  toFun φ := ⟨coindCocycle U (φ : U → M), by
    rw [mem_Z1_iff (coindCocycle U (φ : U → M))]
    exact ⟨coindCocycle_crossed U (φ : U → M) ((mem_Z1_iff (φ : U → M)).mp φ.2).1,
      coindCocycle_isLocallyConstant U hU (φ : U → M) ((mem_Z1_iff (φ : U → M)).mp φ.2).1
        ((mem_Z1_iff (φ : U → M)).mp φ.2).2⟩⟩
  map_zero' := by
    apply Subtype.ext
    exact coindCocycle_zero U
  map_add' φ ψ := by
    apply Subtype.ext
    exact coindCocycle_add U (φ : U → M) (ψ : U → M)

/-! ## The restriction/evaluation map on cochains -/

section Alpha

variable {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

def alphaCochain (f : G → Coind G U M) : U → M := fun u => (f (u : G) : G → M) (1 : G)

@[simp] theorem alphaCochain_apply (f : G → Coind G U M) (u : U) :
    alphaCochain U f u = (f (u : G) : G → M) (1 : G) := rfl

theorem alphaCochain_crossed (f : G → Coind G U M)
    (hf : Work.GroupCohomology.IsCrossedHom G (Coind G U M) f) :
    Work.GroupCohomology.IsCrossedHom U M (alphaCochain U f) := by
  intro u v
  show ((f ((u : G) * (v : G)) : Coind G U M) : G → M) (1 : G)
      = u • (((f (v : G) : Coind G U M) : G → M) (1 : G))
        + ((f (u : G) : Coind G U M) : G → M) (1 : G)
  rw [hf (u : G) (v : G), coind_add_apply, Coind.smul_apply]
  have h3 := Coind.coe_mul (f (v : G)) (1 : G) u⁻¹
  simpa using h3

theorem alphaCochain_isLocallyConstant (f : G → Coind G U M)
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    Work.AbsoluteKummer.IsLocallyConstant (alphaCochain U f) := by
  intro u₀
  obtain ⟨V, hVopen, hu₀V, hVconst⟩ := hf (u₀ : G)
  refine ⟨Subtype.val ⁻¹' V, hVopen.preimage continuous_subtype_val, hu₀V, ?_⟩
  intro u hu
  show ((f (u : G) : Coind G U M) : G → M) (1 : G)
      = ((f (u₀ : G) : Coind G U M) : G → M) (1 : G)
  exact congrArg (fun z : Coind G U M => (z : G → M) (1 : G)) (hVconst (u : G) hu)

theorem alphaCochain_d0 (a : Coind G U M) :
    alphaCochain U (Work.GroupCohomology.d0 G (Coind G U M) a) =
      Work.GroupCohomology.d0 U M ((a : G → M) (1 : G)) := by
  funext u
  show (((u : G) • a - a : Coind G U M) : G → M) (1 : G)
      = u • ((a : G → M) (1 : G)) - ((a : G → M) (1 : G))
  rw [coind_sub_apply, Coind.smul_apply]
  have h := Coind.coe_mul a (1 : G) u⁻¹
  rw [show ((a : G → M) ((u : G)⁻¹ * 1)) = u • ((a : G → M) 1) from by simpa using h]

end Alpha

def alphaZ1 {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] :
    Z1 G (Coind G U M) →+ Z1 U M where
  toFun f := ⟨alphaCochain U (f : G → Coind G U M), by
    rw [mem_Z1_iff (alphaCochain U (f : G → Coind G U M))]
    exact ⟨alphaCochain_crossed U (f : G → Coind G U M)
        ((mem_Z1_iff (f : G → Coind G U M)).mp f.2).1,
      alphaCochain_isLocallyConstant U (f : G → Coind G U M)
        ((mem_Z1_iff (f : G → Coind G U M)).mp f.2).2⟩⟩
  map_zero' := by
    apply Subtype.ext
    funext u
    simp only [alphaCochain_apply, z1_coe_zero, coind_zero_apply]
  map_add' f g := by
    apply Subtype.ext
    funext u
    simp only [alphaCochain_apply, z1_coe_add, coind_add_apply]

theorem alphaZ1_coindZ1 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] (φ : Z1 U M) :
    alphaZ1 U (coindZ1 U hU φ) = φ := by
  apply Subtype.ext
  funext u
  show ((coindCocycle U (φ : U → M) (u : G) : Coind G U M) : G → M) (1 : G) = (φ : U → M) u
  exact coindCocycle_one_apply U (φ : U → M) u

theorem alphaZ1_mem_B1 {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] {f : Z1 G (Coind G U M)}
    (hf : (f : G → Coind G U M) ∈ B1 G (Coind G U M)) :
    ((alphaZ1 U f : Z1 U M) : U → M) ∈ B1 U M := by
  have hcoe : ((alphaZ1 U f : Z1 U M) : U → M) = alphaCochain U (f : G → Coind G U M) := rfl
  rw [hcoe]
  obtain ⟨a, ha⟩ := (mem_B1_iff (f : G → Coind G U M)).mp hf
  refine (mem_B1_iff (alphaCochain U (f : G → Coind G U M))).mpr ⟨(a : G → M) (1 : G), ?_⟩
  rw [← ha, alphaCochain_d0]

theorem coindZ1_mem_B1 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] {φ : Z1 U M}
    (hφ : (φ : U → M) ∈ B1 U M) :
    ((coindZ1 U hU φ : Z1 G (Coind G U M)) : G → Coind G U M) ∈ B1 G (Coind G U M) := by
  obtain ⟨m, hm⟩ := (mem_B1_iff (φ : U → M)).mp hφ
  have hcoe : ((coindZ1 U hU φ : Z1 G (Coind G U M)) : G → Coind G U M)
      = coindCocycle U (φ : U → M) := rfl
  rw [hcoe, ← hm]
  exact coindCocycle_mem_B1 U m

/-! ## The two maps on `H¹` -/

def alphaHom {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] :
    H1 G (Coind G U M) →+ H1 U M :=
  QuotientAddGroup.lift ((B1 G (Coind G U M)).comap (Z1 G (Coind G U M)).subtype)
    ((H1π U M).comp (alphaZ1 U)) (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H1π_eq_zero_iff]
      exact alphaZ1_mem_B1 U (AddSubgroup.mem_comap.mp hx))

def betaHom {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] :
    H1 U M →+ H1 G (Coind G U M) :=
  QuotientAddGroup.lift ((B1 U M).comap (Z1 U M).subtype)
    ((H1π G (Coind G U M)).comp (coindZ1 U hU)) (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H1π_eq_zero_iff]
      exact coindZ1_mem_B1 U hU (AddSubgroup.mem_comap.mp hx))

theorem alphaHom_mk {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] (f : Z1 G (Coind G U M)) :
    alphaHom U (H1π G (Coind G U M) f) = H1π U M (alphaZ1 U f) :=
  QuotientAddGroup.lift_mk' _ _ f

theorem betaHom_mk {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] (φ : Z1 U M) :
    betaHom U hU (H1π U M φ) = H1π G (Coind G U M) (coindZ1 U hU φ) :=
  QuotientAddGroup.lift_mk' _ _ φ

theorem betaHom_alphaHom {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] (x : H1 U M) :
    alphaHom U (betaHom U hU x) = x := by
  obtain ⟨φ, hφ⟩ := QuotientAddGroup.mk'_surjective ((B1 U M).comap (Z1 U M).subtype) x
  rw [← hφ]
  change alphaHom U (betaHom U hU (H1π U M φ)) = H1π U M φ
  rw [betaHom_mk, alphaHom_mk, alphaZ1_coindZ1]

theorem alphaHom_betaHom {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] (y : H1 G (Coind G U M)) :
    betaHom U hU (alphaHom U y) = y := by
  obtain ⟨f, hf⟩ := QuotientAddGroup.mk'_surjective
    ((B1 G (Coind G U M)).comap (Z1 G (Coind G U M)).subtype) y
  rw [← hf]
  change betaHom U hU (alphaHom U (H1π G (Coind G U M) f)) = H1π G (Coind G U M) f
  rw [alphaHom_mk, betaHom_mk, H1π_eq_iff]
  have hval : ∀ u : U,
      (((coindZ1 U hU (alphaZ1 U f) - f : Z1 G (Coind G U M)) : G → Coind G U M)
        (u : G) : G → M) (1 : G) = 0 := by
    intro u
    rw [z1_coe_sub]
    rw [show ((coindZ1 U hU (alphaZ1 U f) : Z1 G (Coind G U M)) : G → Coind G U M)
        = coindCocycle U ((alphaZ1 U f) : U → M) from rfl]
    rw [coind_sub_apply, coindCocycle_one_apply]
    exact sub_self _
  exact mem_B1_of_val_one_eq_zero U _ hval

def shapiroH1AddEquiv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] :
    H1 G (Coind G U M) ≃+ H1 U M :=
  AddMonoidHom.toAddEquiv (alphaHom U) (betaHom U hU)
    (AddMonoidHom.ext fun x => alphaHom_betaHom U hU x)
    (AddMonoidHom.ext fun y => betaHom_alphaHom U hU y)

/-- **Shapiro's lemma for `H¹` of the coinduced module.**  For a topological group `G`, an open
subgroup `U ≤ G` of finite index and a discrete `U`-module `M`, the evaluation at `1` of a
`1`-cocycle of `G` with values in the coinduced module `Coind G U M`, restricted to `U`, is an
isomorphism on cohomology. -/
theorem shapiro_H1_coind {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (hM : Work.AbsoluteKummer.IsDiscreteModule U M) :
    Nonempty (Work.AbsoluteKummer.H1 G (Work.SSGRoute.PT.Coind G U M) ≃+
      Work.AbsoluteKummer.H1 U M) :=
  ⟨shapiroH1AddEquiv U hU⟩

end

end Work.SSGRoute.PT
