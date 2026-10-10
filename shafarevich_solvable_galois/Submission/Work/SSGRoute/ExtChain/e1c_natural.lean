import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.PT.e1a_E1c_steps
import Submission.Work.SSGRoute.h1_ssgHom_free_subsingleton

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000


/-- Build-speed: `IsAlgClosure k Ω` in the `variable` lines below needs
`Module.IsTorsionFree k Ω`, and the variables are re-elaborated for every declaration (about 2 s of
instance search each time). This file-local instance answers it directly. -/
private theorem e1cNatural_isTorsionFree_fast {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] :
    Module.IsTorsionFree k Ω :=
  inferInstance

attribute [local instance] e1cNatural_isTorsionFree_fast


namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- The free module on the underlying set of `R`: the middle term of the canonical cover. -/
abbrev E1cF (R : Rep.{0} Coeff (K ≃ₐ[k] K)) : Rep.{0} Coeff (K ≃ₐ[k] K) :=
  Rep.free Coeff (K ≃ₐ[k] K) R.V

/-- The middle coefficient `Hom_ℤ(F, Ωˣ)` of the dualised canonical resolution, wrapped (as
`homCoindFreeT`) so that instance search terminates and finds the conjugation action. -/
abbrev E1cN (R : Rep.{0} Coeff (K ≃ₐ[k] K)) : Type := homCoindFreeT k Ω K R.V

/-- The canonical syzygy of `R`. -/
abbrev E1cR1 (R : Rep.{0} Coeff (K ≃ₐ[k] K)) : Rep.{0} Coeff (K ≃ₐ[k] K) :=
  Limits.kernel (freeCover R)

/-- The underlying additive map of the canonical syzygy inclusion `R₁ → F`. -/
def kappa (R : Rep.{0} Coeff (K ≃ₐ[k] K)) : (E1cR1 R).V →+ (E1cF R).V :=
  (Rep.Hom.hom (Limits.kernel.ι (freeCover R))).toAddMonoidHom

/-- The underlying additive map of the canonical cover `F → R`. -/
def coverMap (R : Rep.{0} Coeff (K ≃ₐ[k] K)) : (E1cF R).V →+ R.V :=
  (Rep.Hom.hom (freeCover R)).toAddMonoidHom

/-- `ι : Hom_ℤ(R, Ωˣ) → Hom_ℤ(F, Ωˣ)`, precomposition with the canonical cover. -/
def iotaH (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Work.SSGRoute.homCoind k Ω K R →+ E1cN (k := k) (Ω := Ω) (K := K) R :=
  precompAddHom (coverMap R)

/-- `π : Hom_ℤ(F, Ωˣ) → Hom_ℤ(R₁, Ωˣ)`, precomposition with the kernel inclusion. -/
def piH (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    E1cN (k := k) (Ω := Ω) (K := K) R →+
      Work.SSGRoute.homCoind k Ω K (E1cR1 R) :=
  precompAddHom (kappa R)

@[simp] theorem coverMap_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (x : (E1cF R).V) :
    coverMap R x = Rep.Hom.hom (freeCover R) x := rfl

@[simp] theorem kappa_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (x : (E1cR1 R).V) :
    kappa R x = Rep.Hom.hom (Limits.kernel.ι (freeCover R)) x := rfl

@[simp] theorem iotaH_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (ψ : Work.SSGRoute.homCoind k Ω K R) : iotaH (k := k) (Ω := Ω) (K := K) R ψ = ψ.comp (coverMap R) :=
  rfl

@[simp] theorem piH_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (ψ : E1cN (k := k) (Ω := Ω) (K := K) R) : piH (k := k) (Ω := Ω) (K := K) R ψ = ψ.comp (kappa R) :=
  rfl

theorem coverMap_comm (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ : K ≃ₐ[k] K) (v : (E1cF R).V) :
    coverMap R ((E1cF R).ρ γ v) = R.ρ γ (coverMap R v) :=
  Rep.hom_comm_apply (freeCover R) γ v

theorem kappa_comm (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ : K ≃ₐ[k] K) (v : (E1cR1 R).V) :
    kappa R ((E1cR1 R).ρ γ v) = (E1cF R).ρ γ (kappa R v) :=
  Rep.hom_comm_apply (Limits.kernel.ι (freeCover R)) γ v

theorem precompAddHom_equivariant {M N : Rep.{0} Coeff (K ≃ₐ[k] K)} (u : M ⟶ N) :
    Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (precompAddHom (Rep.Hom.hom u).toAddMonoidHom :
        Work.SSGRoute.homCoind k Ω K N →+ Work.SSGRoute.homCoind k Ω K M) := by
  intro σ ψ
  apply AddMonoidHom.ext
  intro v
  rw [precompAddHom_apply, AddMonoidHom.comp_apply]
  simp only [Work.SSGRoute.homCoind.smul_apply]
  rw [precompAddHom_apply, AddMonoidHom.comp_apply]
  congr 1
  exact congrArg ψ (Rep.hom_comm_apply u ((SSGRoute.res k K) σ)⁻¹ v).symm

theorem iotaH_equivariant (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    @Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K R) (E1cN (k := k) (Ω := Ω) (K := K) R)
      _ (Work.SSGRoute.homCoind.instAddCommGroup R)
      (Work.SSGRoute.homCoind.instAddCommGroup (E1cF R))
      (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv R)
      (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (E1cF R))
      (iotaH (k := k) (Ω := Ω) (K := K) R) :=
  precompAddHom_equivariant (freeCover R)

theorem piH_equivariant (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    @Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (E1cN (k := k) (Ω := Ω) (K := K) R)
      (Work.SSGRoute.homCoind k Ω K (E1cR1 R))
      _ (Work.SSGRoute.homCoind.instAddCommGroup (E1cF R))
      (Work.SSGRoute.homCoind.instAddCommGroup (E1cR1 R))
      (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (E1cF R))
      (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (E1cR1 R))
      (piH (k := k) (Ω := Ω) (K := K) R) :=
  precompAddHom_equivariant (Limits.kernel.ι (freeCover R))

theorem iotaH_injective (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Function.Injective (iotaH (k := k) (Ω := Ω) (K := K) R) := by
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  exact precompAddHom_injective _ (freeCover_surjective R)

theorem piH_surjective (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Function.Surjective (piH (k := k) (Ω := Ω) (K := K) R) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  exact precompAddHom_surjective_addUnits _
    (by
      haveI : Mono (Limits.kernel.ι (freeCover R)) := inferInstance
      simpa [kappa] using
        (Rep.mono_iff_injective (Limits.kernel.ι (freeCover R))).mp inferInstance)

theorem kappa_coverMap (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (v : (E1cR1 R).V) :
    coverMap R (kappa R v) = 0 := by
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  have hcond : Limits.kernel.ι (freeCover R) ≫ freeCover R = 0 := Limits.kernel.condition _
  have h := congrArg (fun (m : E1cR1 R ⟶ R) => m v) hcond
  rw [Rep.comp_apply] at h
  simpa [kappa, coverMap] using h

theorem iotaH_range_eq_piH_ker (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    (iotaH (k := k) (Ω := Ω) (K := K) R).range
      = (piH (k := k) (Ω := Ω) (K := K) R).ker := by
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  have hkerF : (coverMap R).ker = (kappa R).range := by
    simpa [coverMap, kappa] using ker_hom_eq_range_kernel_iota (K := K) (freeCover R)
  apply le_antisymm
  · rintro _ ⟨ψ, rfl⟩
    rw [AddMonoidHom.mem_ker]
    apply AddMonoidHom.ext
    intro v
    show ψ (coverMap R (kappa R v)) = 0
    rw [kappa_coverMap R v]
    exact map_zero ψ
  · intro ψ hψ
    rw [AddMonoidHom.mem_ker] at hψ
    have hψv : ∀ v : (E1cR1 R).V, ψ (kappa R v) = 0 := by
      intro v
      have h := congrArg (fun (w : (E1cR1 R).V →+ Additive Ωˣ) => w v) hψ
      simpa [piH_apply, precompAddHom_apply, AddMonoidHom.comp_apply] using h
    have hle : (coverMap R).ker ≤ ψ.ker := by
      rw [hkerF]
      intro x hx
      rw [AddMonoidHom.mem_ker]
      obtain ⟨v, rfl⟩ := hx
      exact hψv v
    exact ⟨(AddMonoidHom.liftOfSurjective (coverMap R) (freeCover_surjective R))
        ⟨ψ, hle⟩, by
      apply AddMonoidHom.ext
      intro x
      show (AddMonoidHom.liftOfSurjective (coverMap R) (freeCover_surjective R))
        ⟨ψ, hle⟩ (coverMap R x) = ψ x
      exact AddMonoidHom.liftOfRightInverse_comp_apply (coverMap R)
        (Function.surjInv (freeCover_surjective R))
        (Function.rightInverse_surjInv (freeCover_surjective R)) ⟨ψ, hle⟩ x⟩

theorem piH_iotaH (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (m : Work.SSGRoute.homCoind k Ω K R) :
    piH (k := k) (Ω := Ω) (K := K) R (iotaH (k := k) (Ω := Ω) (K := K) R m) = 0 := by
  have h : iotaH (k := k) (Ω := Ω) (K := K) R m
      ∈ (piH (k := k) (Ω := Ω) (K := K) R).ker := by
    rw [← iotaH_range_eq_piH_ker]
    exact AddMonoidHom.mem_range.mpr ⟨m, rfl⟩
  simpa using h

/-- `H¹(Γ, Hom_ℤ(F,Ωˣ)) = 0` for the canonical cover (Shapiro + Hilbert 90). -/
theorem subsingleton_H1_E1cN (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R)) :=
  homCoind_H1_free_conj_inf (k := k) (Ω := Ω) (K := K) R.V

end

end Work.SSGRoute.ExtChain

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

theorem d0_eq_zero_iff {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    (n : M) : Work.GroupCohomology.d0 G M n = 0 ↔ n ∈ Work.GroupCohomology.invariants G M := by
  constructor
  · intro h
    exact (Work.GroupCohomology.mem_invariants G M n).mpr (by
      intro g
      have h1 := congrFun h g
      rw [Work.GroupCohomology.d0_apply, Pi.zero_apply] at h1
      exact sub_eq_zero.mp h1)
  · intro h
    funext g
    rw [Work.GroupCohomology.d0_apply, Pi.zero_apply, sub_eq_zero]
    exact (Work.GroupCohomology.mem_invariants G M n).mp h g

/-- `π` on the invariants. -/
def piH0 (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R)) →+
      ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K (E1cR1 R))) :=
  Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω) (piH (k := k) (Ω := Ω) (K := K) R)
    (piH_equivariant (k := k) (Ω := Ω) (K := K) R)

/-- The cokernel through which the `E1c` dictionary factors. -/
abbrev cokerH (R : Rep.{0} Coeff (K ≃ₐ[k] K)) : Type :=
  ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (E1cR1 R))) ⧸
    (piH0 (k := k) (Ω := Ω) (K := K) R).range

theorem exists_lift_spec (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))) :
    ∃ n : E1cN (k := k) (Ω := Ω) (K := K) R,
      Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R) n =
        ((Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
            (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) c :
          ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R))) :
            (Ω ≃ₐ[k] Ω) → E1cN (k := k) (Ω := Ω) (K := K) R) := by
  haveI : Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (E1cN (k := k) (Ω := Ω) (K := K) R)) := subsingleton_H1_E1cN (k := k) (Ω := Ω) (K := K) R
  have h0 : Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R)
      (Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
        (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) c) = 0 :=
    Subsingleton.elim _ _
  rw [Work.AbsoluteKummer.H1π_eq_zero_iff] at h0
  rw [Work.AbsoluteKummer.mem_B1_iff] at h0
  exact h0

/-- A lift of the cocycle `c` to the middle coefficient. -/
noncomputable def liftOf (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))) :
    E1cN (k := k) (Ω := Ω) (K := K) R :=
  Classical.choose (exists_lift_spec (k := k) (Ω := Ω) (K := K) R c)

theorem liftOf_spec (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))) :
    Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R)
        (liftOf (k := k) (Ω := Ω) (K := K) R c) =
      ((Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
          (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) c :
        ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R))) :
          (Ω ≃ₐ[k] Ω) → E1cN (k := k) (Ω := Ω) (K := K) R) :=
  Classical.choose_spec (exists_lift_spec (k := k) (Ω := Ω) (K := K) R c)

theorem d0_piH (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (n : E1cN (k := k) (Ω := Ω) (K := K) R) :
    Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (E1cR1 R))
        (piH (k := k) (Ω := Ω) (K := K) R n)
      = fun g => piH (k := k) (Ω := Ω) (K := K) R
          ((Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R) n) g) := by
  funext g
  rw [Work.GroupCohomology.d0_apply, Work.GroupCohomology.d0_apply, map_sub,
    piH_equivariant (k := k) (Ω := Ω) (K := K) R g n]

theorem piH_mem_of_d0_eq (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)))
    (n : E1cN (k := k) (Ω := Ω) (K := K) R)
    (hn : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R) n =
      ((Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
          (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) c :
        ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R))) :
          (Ω ≃ₐ[k] Ω) → E1cN (k := k) (Ω := Ω) (K := K) R)) :
    piH (k := k) (Ω := Ω) (K := K) R n
      ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (E1cR1 R)) := by
  rw [← d0_eq_zero_iff]
  rw [d0_piH]
  funext g
  rw [hn, Work.AbsoluteKummer.mapZ1_apply]
  exact piH_iotaH (k := k) (Ω := Ω) (K := K) R
    ((c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R) g)

/-- The raw class attached to a cocycle: `π` of a lift of the coboundary. -/
noncomputable def betaRaw (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))) :
    ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (E1cR1 R))) :=
  ⟨piH (k := k) (Ω := Ω) (K := K) R (liftOf (k := k) (Ω := Ω) (K := K) R c),
    piH_mem_of_d0_eq (k := k) (Ω := Ω) (K := K) R c _
      (liftOf_spec (k := k) (Ω := Ω) (K := K) R c)⟩

theorem betaRaw_congr (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)))
    (n : E1cN (k := k) (Ω := Ω) (K := K) R)
    (hn : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R) n =
      ((Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
          (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) c :
        ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R))) :
          (Ω ≃ₐ[k] Ω) → E1cN (k := k) (Ω := Ω) (K := K) R)) :
    QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
        ⟨piH (k := k) (Ω := Ω) (K := K) R n,
          piH_mem_of_d0_eq (k := k) (Ω := Ω) (K := K) R c n hn⟩
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (betaRaw (k := k) (Ω := Ω) (K := K) R c) := by
  have hmem : (⟨piH (k := k) (Ω := Ω) (K := K) R n,
        piH_mem_of_d0_eq (k := k) (Ω := Ω) (K := K) R c n hn⟩ :
        ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.homCoind k Ω K (E1cR1 R))))
      - betaRaw (k := k) (Ω := Ω) (K := K) R c
      ∈ (piH0 (k := k) (Ω := Ω) (K := K) R).range := by
    rw [AddMonoidHom.mem_range]
    refine ⟨⟨n - liftOf (k := k) (Ω := Ω) (K := K) R c, ?_⟩, ?_⟩
    · rw [← d0_eq_zero_iff, map_sub, hn, liftOf_spec, sub_self]
    · apply Subtype.ext
      show piH (k := k) (Ω := Ω) (K := K) R (n - liftOf (k := k) (Ω := Ω) (K := K) R c)
        = piH (k := k) (Ω := Ω) (K := K) R n
          - piH (k := k) (Ω := Ω) (K := K) R (liftOf (k := k) (Ω := Ω) (K := K) R c)
      rw [map_sub]
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem]
  exact hmem

theorem betaRaw_add (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (c c' : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))) :
    (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
        (betaRaw (k := k) (Ω := Ω) (K := K) R (c + c'))
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (betaRaw (k := k) (Ω := Ω) (K := K) R c)
        + QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
            (betaRaw (k := k) (Ω := Ω) (K := K) R c')) := by
  have hd : (betaRaw (k := k) (Ω := Ω) (K := K) R (c + c')
        - (betaRaw (k := k) (Ω := Ω) (K := K) R c
          + betaRaw (k := k) (Ω := Ω) (K := K) R c'))
      ∈ (piH0 (k := k) (Ω := Ω) (K := K) R).range := by
    rw [AddMonoidHom.mem_range]
    refine ⟨⟨liftOf (k := k) (Ω := Ω) (K := K) R (c + c')
      - (liftOf (k := k) (Ω := Ω) (K := K) R c
        + liftOf (k := k) (Ω := Ω) (K := K) R c'), ?_⟩, ?_⟩
    · rw [← d0_eq_zero_iff, map_sub, map_add, liftOf_spec, liftOf_spec, liftOf_spec]
      simp only [map_add, AddSubgroup.coe_add]
      abel
    · apply Subtype.ext
      show piH (k := k) (Ω := Ω) (K := K) R
          (liftOf (k := k) (Ω := Ω) (K := K) R (c + c')
            - (liftOf (k := k) (Ω := Ω) (K := K) R c
              + liftOf (k := k) (Ω := Ω) (K := K) R c'))
        = piH (k := k) (Ω := Ω) (K := K) R (liftOf (k := k) (Ω := Ω) (K := K) R (c + c'))
          - (piH (k := k) (Ω := Ω) (K := K) R (liftOf (k := k) (Ω := Ω) (K := K) R c)
            + piH (k := k) (Ω := Ω) (K := K) R (liftOf (k := k) (Ω := Ω) (K := K) R c'))
      simp only [map_sub, map_add]
  have hsum := (map_add (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range)
    (betaRaw (k := k) (Ω := Ω) (K := K) R c)
    (betaRaw (k := k) (Ω := Ω) (K := K) R c')).symm
  rw [hsum, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem]
  exact hd

noncomputable def betaOnZ1 (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)) →+
      cokerH (k := k) (Ω := Ω) (K := K) R :=
  AddMonoidHom.mk' (fun c => QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
      (betaRaw (k := k) (Ω := Ω) (K := K) R c))
    (fun c c' => betaRaw_add (k := k) (Ω := Ω) (K := K) R c c')

theorem betaOnZ1_eq_zero (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)))
    (hc : (c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R) ∈
      Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)) :
    betaOnZ1 (k := k) (Ω := Ω) (K := K) R c = 0 := by
  obtain ⟨m, hm⟩ := (Work.AbsoluteKummer.mem_B1_iff _).mp hc
  show QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
      (betaRaw (k := k) (Ω := Ω) (K := K) R c) = 0
  have h := betaRaw_congr (k := k) (Ω := Ω) (K := K) R c
    (iotaH (k := k) (Ω := Ω) (K := K) R m) (by
      funext g
      rw [Work.GroupCohomology.d0_apply]
      rw [← iotaH_equivariant (k := k) (Ω := Ω) (K := K) R g m, ← map_sub,
        ← Work.GroupCohomology.d0_apply, hm, Work.AbsoluteKummer.mapZ1_apply])
  rw [← h, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  refine ⟨0, ?_⟩
  apply Subtype.ext
  show piH (k := k) (Ω := Ω) (K := K) R (0 : E1cN (k := k) (Ω := Ω) (K := K) R)
    = piH (k := k) (Ω := Ω) (K := K) R (iotaH (k := k) (Ω := Ω) (K := K) R m)
  rw [map_zero, piH_iotaH]

/-- **The pull-back map** `H¹(Γ, Hom(R,Ωˣ)) → H⁰(Γ,Hom(R₁,Ωˣ)) ⧸ π(H⁰(Γ,Hom(F,Ωˣ)))`. -/
noncomputable def betaH (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) →+
      cokerH (k := k) (Ω := Ω) (K := K) R :=
  QuotientAddGroup.lift
    ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)).comap
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)).subtype)
    (betaOnZ1 (k := k) (Ω := Ω) (K := K) R)
    (fun c hc => betaOnZ1_eq_zero (k := k) (Ω := Ω) (K := K) R c hc)

theorem betaH_mk (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))) :
    betaH (k := k) (Ω := Ω) (K := K) R
        (QuotientAddGroup.mk' _ c)
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (betaRaw (k := k) (Ω := Ω) (K := K) R c) := rfl

theorem betaH_injective (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Function.Injective (betaH (k := k) (Ω := Ω) (K := K) R) := by
  intro x y hxy
  have h : betaH (k := k) (Ω := Ω) (K := K) R (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)).comap
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)).subtype) (x - y)
  rw [← hc, betaH_mk] at h
  -- h : mk (betaRaw c) = 0  →  betaRaw c ∈ range piH0
  have hmem : betaRaw (k := k) (Ω := Ω) (K := K) R c
      ∈ (piH0 (k := k) (Ω := Ω) (K := K) R).range := by
    have h' : QuotientAddGroup.mk (betaRaw (k := k) (Ω := Ω) (K := K) R c)
        = (0 : cokerH (k := k) (Ω := Ω) (K := K) R) := by
      rw [← QuotientAddGroup.mk'_apply]
      exact h
    rw [QuotientAddGroup.eq_zero_iff] at h'
    exact h'
  rw [AddMonoidHom.mem_range] at hmem
  obtain ⟨z, hz⟩ := hmem
  -- piH (liftOf c - z) = 0, so liftOf c - z = iotaH m
  have hker : liftOf (k := k) (Ω := Ω) (K := K) R c - (z : E1cN (k := k) (Ω := Ω) (K := K) R)
      ∈ (piH (k := k) (Ω := Ω) (K := K) R).ker := by
    rw [AddMonoidHom.mem_ker, map_sub]
    have hz' : piH (k := k) (Ω := Ω) (K := K) R
        (z : E1cN (k := k) (Ω := Ω) (K := K) R)
        = piH (k := k) (Ω := Ω) (K := K) R (liftOf (k := k) (Ω := Ω) (K := K) R c) := by
      have := Subtype.ext_iff.mp hz
      simpa [piH0, betaRaw, Work.GroupCohomology.mapH0] using this
    rw [hz', sub_self]
  rw [← iotaH_range_eq_piH_ker (k := k) (Ω := Ω) (K := K) R] at hker
  rw [AddMonoidHom.mem_range] at hker
  obtain ⟨m, hm⟩ := hker
  -- d0 m = c
  have hd0 : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) m
      = (c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R) := by
    funext g
    apply iotaH_injective (k := k) (Ω := Ω) (K := K) R
    have h1 : iotaH (k := k) (Ω := Ω) (K := K) R
        ((Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) m) g)
        = (Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R)
            (iotaH (k := k) (Ω := Ω) (K := K) R m)) g := by
      rw [Work.GroupCohomology.d0_apply, Work.GroupCohomology.d0_apply, map_sub,
        iotaH_equivariant (k := k) (Ω := Ω) (K := K) R g m]
    rw [h1, hm, ← Work.AbsoluteKummer.mapZ1_apply, map_sub, liftOf_spec]
    have hz0 : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R)
        (z : E1cN (k := k) (Ω := Ω) (K := K) R) = 0 := (d0_eq_zero_iff _).mpr z.2
    rw [hz0, sub_zero]
  have hcB : (c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R) ∈
      Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) :=
    (Work.AbsoluteKummer.mem_B1_iff _).mpr ⟨m, hd0⟩
  have : x - y = 0 := by
    rw [← hc, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact hcB
  exact sub_eq_zero.mp this

end

end Work.SSGRoute.ExtChain
namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

theorem intSpan_le_closure {V : Type} [AddCommGroup V] (s : Set V) :
    (Submodule.span ℤ s : Set V) ⊆ AddSubgroup.closure s := by
  intro x hx
  let P : Submodule ℤ V :=
    { carrier := AddSubgroup.closure s
      add_mem' := fun ha hb => AddSubgroup.add_mem _ ha hb
      zero_mem' := AddSubgroup.zero_mem _
      smul_mem' := fun c x hx => AddSubgroup.zsmul_mem _ hx c }
  have hle : Submodule.span ℤ s ≤ P :=
    Submodule.span_le.mpr (fun y hy => AddSubgroup.subset_closure hy)
  exact hle hx

theorem exists_finset_closure_top (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] :
    ∃ s : Finset R.V, AddSubgroup.closure (s : Set R.V) = ⊤ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := R.V)
  refine ⟨s, ?_⟩
  apply eq_top_iff.mpr
  intro x _
  exact intSpan_le_closure (s : Set R.V) (by rw [hs]; trivial)

theorem exists_good_lift (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (p : Work.SSGRoute.homCoind k Ω K (E1cR1 R))
    (hp : p ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (E1cR1 R))) :
    ∃ n : E1cN (k := k) (Ω := Ω) (K := K) R,
      piH (k := k) (Ω := Ω) (K := K) R n = p ∧
      ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
        ∀ σ ∈ U, (Work.SSGRoute.homCoind.smulHom σ).comp
          (n.comp (((E1cF R).ρ (SSGRoute.res k K σ)⁻¹).toAddMonoidHom)) = n := by
  classical
  haveI hFintype : Fintype (K ≃ₐ[k] K) := inferInstance
  haveI hAlgCl : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  obtain ⟨s, hs⟩ := exists_finset_closure_top (k := k) (Ω := Ω) (K := K) R
  let gy : R.V → (E1cF R).V := fun y => Classical.choose (freeCover_surjective R y)
  have hgy : ∀ y, coverMap R (gy y) = y := fun y => Classical.choose_spec (freeCover_surjective R y)
  let M : AddSubgroup (E1cF R).V := AddSubgroup.closure (Set.range (fun y : ↥s => gy y.1))
  have hMsub : ∀ y : ↥s, gy y.1 ∈ M := fun y => AddSubgroup.subset_closure ⟨y, rfl⟩
  have hdec : ∀ x : (E1cF R).V, ∃ z : (E1cR1 R).V × ↥M, x = kappa R z.1 + ↑z.2 := by
    intro x
    have hx : coverMap R x ∈ AddSubgroup.closure (s : Set R.V) := by rw [hs]; trivial
    have hle : AddSubgroup.closure (s : Set R.V) ≤ M.map (coverMap R) :=
      (AddSubgroup.closure_le _).mpr (fun y hy =>
        AddSubgroup.mem_map.mpr ⟨gy y, hMsub ⟨y, by simpa using hy⟩, hgy y⟩)
    obtain ⟨m, hmM, hmx⟩ := AddSubgroup.mem_map.mp (hle hx)
    have hkerF : (coverMap R).ker = (kappa R).range := by
      simpa [coverMap, kappa] using ker_hom_eq_range_kernel_iota (K := K) (freeCover R)
    have hker : x - m ∈ (coverMap R).ker := by
      rw [AddMonoidHom.mem_ker, map_sub, hmx, sub_self]
    rw [hkerF] at hker
    obtain ⟨r, hr⟩ := AddMonoidHom.mem_range.mp hker
    exact ⟨(r, ⟨m, hmM⟩), by rw [hr]; abel⟩
  let B : AddSubgroup (E1cR1 R).V := M.comap (kappa R)
  let kappaB : ↥B →+ ↥M :=
    { toFun := fun b => ⟨kappa R b.1, b.2⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hkappa_inj : Function.Injective (kappa R) := by
    haveI : Mono (Limits.kernel.ι (freeCover R)) := inferInstance
    simpa [kappa] using
      (Rep.mono_iff_injective (Limits.kernel.ι (freeCover R))).mp inferInstance
  have hkappaB_inj : Function.Injective kappaB := by
    intro a b hab
    apply Subtype.ext
    exact hkappa_inj (Subtype.ext_iff.mp hab)
  let pB : ↥B →+ Additive Ωˣ := p.comp B.subtype
  obtain ⟨q, hq⟩ := addUnits_injective kappaB hkappaB_inj pB
  have hq_spec : ∀ b : ↥B, q ⟨kappa R b.1, b.2⟩ = p b.1 := fun b => hq b
  have huniq : ∀ (x : (E1cF R).V) (r r' : (E1cR1 R).V) (m m' : ↥M),
      x = kappa R r + ↑m → x = kappa R r' + ↑m' → p r + q m = p r' + q m' := by
    intro x r r' m m' h1 h2
    have h4 : kappa R r + ↑m = kappa R r' + ↑m' := by rw [← h1, ← h2]
    have h3 : kappa R (r - r') = ↑m' - ↑m := by
      rw [map_sub]
      calc kappa R r - kappa R r' = (kappa R r + ↑m) - (kappa R r' + ↑m') + (↑m' - ↑m) := by abel
        _ = ↑m' - ↑m := by rw [h4]; abel
    have hb : (r - r') ∈ B := by
      show kappa R (r - r') ∈ M
      rw [h3]
      exact sub_mem m'.2 m.2
    have hsub : (⟨kappa R (r - r'), hb⟩ : ↥M) = m' - m := by
      apply Subtype.ext
      simpa using h3
    have hkey : q (m' - m) = p (r - r') := by
      rw [← hsub]
      exact hq_spec ⟨r - r', hb⟩
    rw [map_sub] at hkey
    rw [map_sub] at hkey
    have hgoal : p r + q m - (p r' + q m') = 0 := by
      have : p r + q m - (p r' + q m') = (p r - p r') - (q m' - q m) := by abel
      rw [this, ← hkey, sub_self]
    exact sub_eq_zero.mp hgoal
  let dec : (E1cF R).V → (E1cR1 R).V × ↥M := fun x => Classical.choose (hdec x)
  have hdec_spec : ∀ x, x = kappa R (dec x).1 + ↑(dec x).2 := fun x =>
    Classical.choose_spec (hdec x)
  let nfun : (E1cF R).V → Additive Ωˣ := fun x => p (dec x).1 + q (dec x).2
  have hnfun_add : ∀ x y, nfun (x + y) = nfun x + nfun y := by
    intro x y
    have h : x + y = kappa R ((dec x).1 + (dec y).1) + ↑((dec x).2 + (dec y).2) := by
      calc x + y = (kappa R (dec x).1 + ↑(dec x).2) + (kappa R (dec y).1 + ↑(dec y).2) := by
            conv_lhs => rw [hdec_spec x, hdec_spec y]
        _ = kappa R ((dec x).1 + (dec y).1) + ↑((dec x).2 + (dec y).2) := by
            rw [map_add, AddSubgroup.coe_add]; abel
    have h2 := huniq (x + y) (dec (x + y)).1 ((dec x).1 + (dec y).1) (dec (x + y)).2
      ((dec x).2 + (dec y).2) (hdec_spec (x + y)) h
    show p (dec (x + y)).1 + q (dec (x + y)).2
      = (p (dec x).1 + q (dec x).2) + (p (dec y).1 + q (dec y).2)
    rw [h2, map_add, map_add]
    abel
  let n : E1cN (k := k) (Ω := Ω) (K := K) R := AddMonoidHom.mk' nfun hnfun_add
  have hn_apply : ∀ x, n x = p (dec x).1 + q (dec x).2 := fun x => rfl
  have hn_kappa : ∀ r, n (kappa R r) = p r := by
    intro r
    have h2 := huniq (kappa R r) (dec (kappa R r)).1 r (dec (kappa R r)).2 0
      (hdec_spec (kappa R r)) (by rw [AddSubgroup.coe_zero, add_zero])
    rw [hn_apply, h2, map_zero, add_zero]
  have hpiH : piH (k := k) (Ω := Ω) (K := K) R n = p := by
    apply AddMonoidHom.ext
    intro r
    rw [piH_apply, AddMonoidHom.comp_apply]
    exact hn_kappa r
  refine ⟨n, hpiH, ?_⟩
  obtain ⟨Φ, hΦspec⟩ := homRep_unitsK_formula (k := k) (Ω := Ω) (K := K) (E1cR1 R)
  obtain ⟨f, hf⟩ := Φ.surjective ⟨p, hp⟩
  have hpval : ∀ r : (E1cR1 R).V, p r = Additive.ofMul (Units.map
      (algebraMap ↥K Ω).toMonoidWithZeroHom (Additive.toMul (Rep.Hom.hom f r))) := by
    intro r
    have hval : p = (↑(Φ f) : Work.SSGRoute.homCoind k Ω K (E1cR1 R)) :=
      (Subtype.ext_iff.mp hf).symm
    rw [hval]
    exact hΦspec f r
  let gyM : ↥s → ↥M := fun y => ⟨gy y.1, hMsub y⟩
  have hgyM : ∀ y : ↥s, ((gyM y : ↥M) : (E1cF R).V) = gy y.1 := fun y => rfl
  let U : Subgroup (Ω ≃ₐ[k] Ω) :=
    K.fixingSubgroup ⊓ ⨅ y : ↥s, MulAction.stabilizer (Ω ≃ₐ[k] Ω) (q (gyM y))
  have hUopen : IsOpen ((U : Set (Ω ≃ₐ[k] Ω))) := by
    have hcoe : (U : Set (Ω ≃ₐ[k] Ω))
        = (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω))
          ∩ ⋂ y : ↥s, (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (q (gyM y)) :
              Set (Ω ≃ₐ[k] Ω)) := by
      ext σ
      simp only [U, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_iInf,
        Set.mem_inter_iff, Set.mem_iInter]
    rw [hcoe]
    exact (IntermediateField.fixingSubgroup_isOpen K).inter
      (isOpen_iInter_of_finite (fun y : ↥s =>
        isDiscreteModule_addUnitsΩ k Ω (q (gyM y))))
  refine ⟨U, hUopen, ?_⟩
  intro σ hσ
  have hσK : σ ∈ K.fixingSubgroup := hσ.1
  have hσq : ∀ y : ↥s, σ ∈ MulAction.stabilizer (Ω ≃ₐ[k] Ω) (q (gyM y)) :=
    fun y => (Subgroup.mem_iInf.mp hσ.2) y
  have hres : SSGRoute.res k K σ = 1 := by
    have hker : σ ∈ (SSGRoute.res k K).ker := by
      rw [IntermediateField.restrictNormalHom_ker K]
      exact hσK
    exact MonoidHom.mem_ker.mp hker
  have hσK' : ∀ u : ↥K, σ (algebraMap ↥K Ω u) = algebraMap ↥K Ω u := by
    intro u
    have h := AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K σ u
    rw [hres] at h
    have h1 : ((1 : K ≃ₐ[k] K) u : Ω) = algebraMap ↥K Ω u := rfl
    rw [h1] at h
    exact h.symm
  have hqmem : ∀ m : ↥M, q m ∈ AddSubgroup.closure
      (Set.range (fun y : ↥s => q (gyM y))) := by
    have key : ∀ z : (E1cF R).V, z ∈ M → (∀ hz : z ∈ M,
        q (⟨z, hz⟩ : ↥M) ∈ AddSubgroup.closure (Set.range (fun y : ↥s => q (gyM y)))) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem w hw =>
          intro _
          obtain ⟨y, rfl⟩ := hw
          refine AddSubgroup.subset_closure ⟨y, ?_⟩
          show q (gyM y) = q (gyM y)
          rfl
      | zero => intro _; show q (0 : ↥M) ∈ AddSubgroup.closure (Set.range (fun y : ↥s => q (gyM y))); rw [map_zero]; exact AddSubgroup.zero_mem _
      | add a b ha hb ia ib =>
          intro hab
          have hqadd : q (⟨a + b, hab⟩ : ↥M) = q (⟨a, ha⟩ : ↥M) + q (⟨b, hb⟩ : ↥M) := by
            rw [show (⟨a + b, hab⟩ : ↥M) = ⟨a, ha⟩ + ⟨b, hb⟩ from Subtype.ext rfl, map_add]
          rw [hqadd]
          exact add_mem (ia ha) (ib hb)
      | neg a ha ia =>
          intro hna
          have hqneg : q (⟨-a, hna⟩ : ↥M) = -q (⟨a, ha⟩ : ↥M) := by
            rw [show (⟨-a, hna⟩ : ↥M) = -⟨a, ha⟩ from Subtype.ext rfl, map_neg]
          rw [hqneg]
          exact neg_mem (ia ha)
    intro m
    exact key m.1 m.2 m.2
  have hfixq : ∀ u ∈ AddSubgroup.closure (Set.range (fun y : ↥s => q (gyM y))),
      σ • u = u := by
    intro u hu
    induction hu using AddSubgroup.closure_induction with
    | mem z hz => obtain ⟨y, rfl⟩ := hz; exact MulAction.mem_stabilizer_iff.mp (hσq y)
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add, ha, hb]
    | neg a _ ha => rw [smul_neg, ha]
  apply AddMonoidHom.ext
  intro x
  have hresinv : (SSGRoute.res k K σ)⁻¹ = 1 := by rw [hres, inv_one]
  have hrho1 : ((E1cF R).ρ ((SSGRoute.res k K σ)⁻¹)) = LinearMap.id := by
    rw [hresinv, map_one]
    ext v
    rfl
  show (Work.SSGRoute.homCoind.smulHom σ)
    (n (((E1cF R).ρ (SSGRoute.res k K σ)⁻¹) x)) = n x
  rw [show ((E1cF R).ρ (SSGRoute.res k K σ)⁻¹) x = x from by rw [hrho1]; rfl]
  rw [hn_apply x, map_add]
  have h1 : (Work.SSGRoute.homCoind.smulHom σ) (p (dec x).1) = p (dec x).1 := by
    rw [hpval (dec x).1]
    apply Additive.ext
    apply Units.ext
    change (σ (algebraMap ↥K Ω
        ((Additive.toMul (Rep.Hom.hom f (dec x).1) : (↥K)ˣ) : ↥K)) : Ω)
      = (algebraMap ↥K Ω
        ((Additive.toMul (Rep.Hom.hom f (dec x).1) : (↥K)ˣ) : ↥K) : Ω)
    exact hσK' ((Additive.toMul (Rep.Hom.hom f (dec x).1) : (↥K)ˣ) : ↥K)
  have h2 : (Work.SSGRoute.homCoind.smulHom σ) (q (dec x).2) = q (dec x).2 :=
    hfixq (q (dec x).2) (hqmem (dec x).2)
  rw [h1, h2]

end

end Work.SSGRoute.ExtChain

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- The conjugation action of `Γ` on `Hom_ℤ(F,Ωˣ)`, written with an explicit formula (avoiding the
ambiguity of the `•`-notation on the free-based coefficient). -/
def cnj (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ : Ω ≃ₐ[k] Ω)
    (n : E1cN (k := k) (Ω := Ω) (K := K) R) : E1cN (k := k) (Ω := Ω) (K := K) R :=
  (Work.SSGRoute.homCoind.smulHom γ).comp
    (n.comp (((E1cF R).ρ (SSGRoute.res k K γ)⁻¹).toAddMonoidHom))

/-- `d0` on the free-based coefficient, in terms of the explicit formula `cnj`. -/
theorem d0_cnj (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (n : E1cN (k := k) (Ω := Ω) (K := K) R) :
    Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R) n
      = fun γ => cnj (k := k) (Ω := Ω) (K := K) R γ n - n := rfl

theorem cnj_sub (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ : Ω ≃ₐ[k] Ω)
    (x y : E1cN (k := k) (Ω := Ω) (K := K) R) :
    cnj (k := k) (Ω := Ω) (K := K) R γ (x - y)
      = cnj (k := k) (Ω := Ω) (K := K) R γ x - cnj (k := k) (Ω := Ω) (K := K) R γ y := by
  refine AddMonoidHom.ext (fun v => ?_)
  show (Work.SSGRoute.homCoind.smulHom γ) ((x - y) (((E1cF R).ρ (SSGRoute.res k K γ)⁻¹) v))
    = (Work.SSGRoute.homCoind.smulHom γ) (x (((E1cF R).ρ (SSGRoute.res k K γ)⁻¹) v))
      - (Work.SSGRoute.homCoind.smulHom γ) (y (((E1cF R).ρ (SSGRoute.res k K γ)⁻¹) v))
  rw [AddMonoidHom.sub_apply, map_sub]

theorem smulHom_comp (γ δ : Ω ≃ₐ[k] Ω) (a : Additive Ωˣ) :
    (Work.SSGRoute.homCoind.smulHom γ) ((Work.SSGRoute.homCoind.smulHom δ) a)
      = (Work.SSGRoute.homCoind.smulHom (γ * δ)) a := by
  rw [Work.SSGRoute.homCoind.smulHom_apply, Work.SSGRoute.homCoind.smulHom_apply,
    Work.SSGRoute.homCoind.smulHom_apply]
  show Additive.ofMul (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ
      (Work.SSGRoute.algEquivUnitsMapΩ k Ω δ (Additive.toMul a)))
    = Additive.ofMul (Work.SSGRoute.algEquivUnitsMapΩ k Ω (γ * δ) (Additive.toMul a))
  rw [Work.SSGRoute.algEquivUnitsMapΩ_mul]

/-- The comparison maps `v ↦ ρ((res γ)⁻¹) v` compose as `u_δ ∘ u_γ = u_{γδ}`. -/
theorem u_comp (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ δ : Ω ≃ₐ[k] Ω)
    (v : (E1cF R).V) :
    (E1cF R).ρ (SSGRoute.res k K δ)⁻¹ ((E1cF R).ρ (SSGRoute.res k K γ)⁻¹ v)
      = (E1cF R).ρ (SSGRoute.res k K (γ * δ))⁻¹ v := by
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]

theorem cnj_cnj (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ δ : Ω ≃ₐ[k] Ω)
    (n : E1cN (k := k) (Ω := Ω) (K := K) R) :
    cnj (k := k) (Ω := Ω) (K := K) R γ (cnj (k := k) (Ω := Ω) (K := K) R δ n)
      = cnj (k := k) (Ω := Ω) (K := K) R (γ * δ) n := by
  refine AddMonoidHom.ext (fun v => ?_)
  show (Work.SSGRoute.homCoind.smulHom γ)
      ((Work.SSGRoute.homCoind.smulHom δ)
        (n (((E1cF R).ρ (SSGRoute.res k K δ)⁻¹) (((E1cF R).ρ (SSGRoute.res k K γ)⁻¹) v))))
    = (Work.SSGRoute.homCoind.smulHom (γ * δ))
        (n (((E1cF R).ρ (SSGRoute.res k K (γ * δ))⁻¹) v))
  rw [smulHom_comp]
  congr 1
  congr 1
  exact u_comp (k := k) (Ω := Ω) (K := K) R γ δ v

theorem iotaH_smul (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ : Ω ≃ₐ[k] Ω)
    (m : Work.SSGRoute.homCoind k Ω K R) :
    iotaH (k := k) (Ω := Ω) (K := K) R (γ • m)
      = cnj (k := k) (Ω := Ω) (K := K) R γ (iotaH (k := k) (Ω := Ω) (K := K) R m) := by
  refine AddMonoidHom.ext (fun v => ?_)
  show (Work.SSGRoute.homCoind.smulHom γ)
      (m ((R.ρ (SSGRoute.res k K γ)⁻¹) (coverMap R v)))
    = (Work.SSGRoute.homCoind.smulHom γ)
      (m (coverMap R (((E1cF R).ρ (SSGRoute.res k K γ)⁻¹) v)))
  rw [coverMap_comm]

theorem piH_cnj (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ : Ω ≃ₐ[k] Ω)
    (n : E1cN (k := k) (Ω := Ω) (K := K) R) :
    piH (k := k) (Ω := Ω) (K := K) R (cnj (k := k) (Ω := Ω) (K := K) R γ n)
      = γ • piH (k := k) (Ω := Ω) (K := K) R n := by
  refine AddMonoidHom.ext (fun v => ?_)
  show (Work.SSGRoute.homCoind.smulHom γ)
      (n (((E1cF R).ρ (SSGRoute.res k K γ)⁻¹) (kappa R v)))
    = (Work.SSGRoute.homCoind.smulHom γ)
      (n (kappa R (((E1cR1 R).ρ (SSGRoute.res k K γ)⁻¹) v)))
  rw [kappa_comm R ((SSGRoute.res k K γ)⁻¹) v]

theorem betaH_surjective (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] :
    Function.Surjective (betaH (k := k) (Ω := Ω) (K := K) R) := by
  classical
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (piH0 (k := k) (Ω := Ω) (K := K) R).range z
  obtain ⟨n, hn, U, hUopen, hUn⟩ := exists_good_lift (k := k) (Ω := Ω) (K := K) R w.1 w.2
  have hmem : ∀ γ : Ω ≃ₐ[k] Ω,
      cnj (k := k) (Ω := Ω) (K := K) R γ n - n
        ∈ (iotaH (k := k) (Ω := Ω) (K := K) R).range := by
    intro γ
    rw [iotaH_range_eq_piH_ker (k := k) (Ω := Ω) (K := K) R]
    rw [AddMonoidHom.mem_ker, map_sub, piH_cnj, hn, w.2 γ, sub_self]
  let c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R := fun γ => Classical.choose (hmem γ)
  have hc : ∀ γ, iotaH (k := k) (Ω := Ω) (K := K) R (c γ)
      = cnj (k := k) (Ω := Ω) (K := K) R γ n - n := fun γ =>
    Classical.choose_spec (hmem γ)
  have hcross : Work.GroupCohomology.IsCrossedHom (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K R) c := by
    intro γ δ
    apply iotaH_injective (k := k) (Ω := Ω) (K := K) R
    rw [map_add, hc (γ * δ), iotaH_smul, hc δ, hc γ, cnj_sub, cnj_cnj]
    abel
  have hloc : Work.AbsoluteKummer.IsLocallyConstant c := by
    intro γ₀
    refine ⟨(fun y => γ₀⁻¹ * y) ⁻¹' U, hUopen.preimage
      (continuous_const.mul continuous_id), ?_, ?_⟩
    · show γ₀⁻¹ * γ₀ ∈ U
      rw [inv_mul_cancel]
      exact Subgroup.one_mem U
    · intro y hy
      rw [Set.mem_preimage] at hy
      have hy' : y = γ₀ * (γ₀⁻¹ * y) := by group
      have htau : c (γ₀⁻¹ * y) = 0 := by
        apply iotaH_injective (k := k) (Ω := Ω) (K := K) R
        rw [map_zero, hc]
        rw [show cnj (k := k) (Ω := Ω) (K := K) R (γ₀⁻¹ * y) n = n
          from hUn (γ₀⁻¹ * y) hy, sub_self]
      rw [hy', hcross γ₀ (γ₀⁻¹ * y), htau]
      rw [show (γ₀ • (0 : Work.SSGRoute.homCoind k Ω K R)) = 0 from by
        show (Work.SSGRoute.homCoind.smulHom γ₀).comp ((0 : Work.SSGRoute.homCoind k Ω K R).comp
          ((R.ρ (SSGRoute.res k K γ₀)⁻¹).toAddMonoidHom)) = 0
        rw [AddMonoidHom.zero_comp, AddMonoidHom.comp_zero], zero_add]
  have hz1 : c ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) :=
    (Work.AbsoluteKummer.mem_Z1_iff c).mpr ⟨hcross, hloc⟩
  let cZ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)) := ⟨c, hz1⟩
  refine ⟨QuotientAddGroup.mk' _ cZ, ?_⟩
  rw [betaH_mk]
  have hdn : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R) n =
      ((Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
          (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) cZ :
        ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R))) :
          (Ω ≃ₐ[k] Ω) → E1cN (k := k) (Ω := Ω) (K := K) R) := by
    funext γ
    rw [Work.AbsoluteKummer.mapZ1_apply, d0_cnj]
    exact (hc γ).symm
  have hcongr := betaRaw_congr (k := k) (Ω := Ω) (K := K) R cZ n hdn
  rw [← hcongr]
  congr 1
  apply Subtype.ext
  exact hn

/-- The pull-back map `betaH` as an additive equivalence. -/
noncomputable def betaEquiv (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] :
    Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) ≃+
      cokerH (k := k) (Ω := Ω) (K := K) R :=
  AddEquiv.ofBijective (betaH (k := k) (Ω := Ω) (K := K) R)
    ⟨betaH_injective (k := k) (Ω := Ω) (K := K) R,
      betaH_surjective (k := k) (Ω := Ω) (K := K) R⟩

@[simp] theorem betaEquiv_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (x : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)) :
    betaEquiv (k := k) (Ω := Ω) (K := K) R x = betaH (k := k) (Ω := Ω) (K := K) R x := rfl
/-! ## Naturality of the `E1c` dictionary -/

/-- `freeMap` is compatible with the canonical covers `F_X → X`. -/
theorem coverMap_freeMap (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) (g : R ⟶ R₂)
    (v : (E1cF R).V) :
    coverMap R₂ (Rep.Hom.hom (freeMap g) v) = Rep.Hom.hom g (coverMap R v) :=
  congrArg (fun (φ : E1cF R ⟶ R₂) => Rep.Hom.hom φ v) (freeMap_freeCover g)

/-- `freeMapKernel` is compatible with the canonical syzygy inclusions `R_X → F_X`. -/
theorem kappa_freeMapKernel (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) (g : R ⟶ R₂)
    (v : (E1cR1 R).V) :
    kappa R₂ (Rep.Hom.hom (freeMapKernel g) v) = Rep.Hom.hom (freeMap g) (kappa R v) :=
  congrArg (fun (φ : E1cR1 R ⟶ E1cF R₂) => Rep.Hom.hom φ v) (freeMapKernel_ι g)

/-- `mapH0` does not depend on the equivariance proof. -/
theorem mapH0_proof_irrel {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction (Ω ≃ₐ[k] Ω) M] [DistribMulAction (Ω ≃ₐ[k] Ω) N] (φ : M →+ N)
    (h₁ h₂ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) φ) :
    Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω) φ h₁
      = Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω) φ h₂ :=
  AddMonoidHom.ext (fun _ => Subtype.ext rfl)

/-- The `π`-square of the canonical covers. -/
theorem piH_natural (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) (g : R ⟶ R₂) :
    (precompAddHom (Rep.Hom.hom (freeMapKernel g)).toAddMonoidHom).comp
        (piH (k := k) (Ω := Ω) (K := K) R₂)
      = (piH (k := k) (Ω := Ω) (K := K) R).comp
        (precompAddHom (Rep.Hom.hom (freeMap g)).toAddMonoidHom) :=
  AddMonoidHom.ext (fun ψ => AddMonoidHom.ext (fun v =>
    congrArg ψ (kappa_freeMapKernel (k := k) (Ω := Ω) (K := K) R R₂ g v)))

/-- The `π`-square on the `Γ`-invariants. -/
theorem piH0_natural (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) (g : R ⟶ R₂) :
    (Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
        (precompAddHom (Rep.Hom.hom (freeMapKernel g)).toAddMonoidHom)
        (precompAddHom_equivariant (freeMapKernel g))).comp
        (piH0 (k := k) (Ω := Ω) (K := K) R₂)
      = (piH0 (k := k) (Ω := Ω) (K := K) R).comp
        (Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
          (precompAddHom (Rep.Hom.hom (freeMap g)).toAddMonoidHom)
          (precompAddHom_equivariant (freeMap g))) :=
  AddMonoidHom.ext (fun w => Subtype.ext
    (DFunLike.congr_fun (piH_natural (k := k) (Ω := Ω) (K := K) R R₂ g) w.1))

/-- The map on the `π`-cokernels induced by a morphism of coefficients. -/
noncomputable def cokerMap (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) (g : R ⟶ R₂) :
    cokerH (k := k) (Ω := Ω) (K := K) R₂ →+ cokerH (k := k) (Ω := Ω) (K := K) R :=
  QuotientAddGroup.lift (piH0 (k := k) (Ω := Ω) (K := K) R₂).range
    ((QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range).comp
      (Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
        (precompAddHom (Rep.Hom.hom (freeMapKernel g)).toAddMonoidHom)
        (precompAddHom_equivariant (freeMapKernel g))))
    (fun z hz => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp hz
      rw [← hw, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact AddMonoidHom.mem_range.mpr
        ⟨(Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
            (precompAddHom (Rep.Hom.hom (freeMap g)).toAddMonoidHom)
            (precompAddHom_equivariant (freeMap g))) w,
          (DFunLike.congr_fun (piH0_natural (k := k) (Ω := Ω) (K := K) R R₂ g) w).symm⟩)

theorem cokerMap_mk (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) (g : R ⟶ R₂)
    (y : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (E1cR1 R₂)))) :
    cokerMap (k := k) (Ω := Ω) (K := K) R R₂ g
        (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R₂).range y)
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
            (precompAddHom (Rep.Hom.hom (freeMapKernel g)).toAddMonoidHom)
            (precompAddHom_equivariant (freeMapKernel g)) y) :=
  QuotientAddGroup.lift_mk' _ _ y

/-- **The `Ext`-side map**: the connecting map of the canonical presentation. -/
noncomputable def PhiE (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0 →+
      Abelian.Ext.{0} R (unitsK k K) 1 :=
  (freeCoverSES_shortExact R).extClass.precomp (unitsK k K) (by norm_num : 1 + 0 = 1)

theorem PhiE_surjective (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Function.Surjective (PhiE (k := k) (Ω := Ω) (K := K) R) :=
  (AddMonoidHom.range_eq_top).mp
    (ext_connecting_range_ker (freeCoverSES_shortExact R) (unitsK k K)).1

theorem PhiE_ker (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    (PhiE (k := k) (Ω := Ω) (K := K) R).ker =
      ((Abelian.Ext.mk₀ (Limits.kernel.ι (freeCover R))).precomp (unitsK k K)
        (by norm_num : 0 + 0 = 0)).range :=
  (ext_connecting_range_ker (freeCoverSES_shortExact R) (unitsK k K)).2

/-- The canonical identification `Ext⁰(M,Kˣ) ≃+ H⁰(Γ, Hom_ℤ(M,Ωˣ))`. -/
noncomputable def PsiE (X : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Abelian.Ext.{0} X (unitsK k K) 0 ≃+
      ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X)) :=
  (Abelian.Ext.addEquiv₀).trans
    (AddEquiv.ofBijective (Work.SSGRoute.toCoindH0 X) (Work.SSGRoute.toCoindH0_bijective X))

/-- `PsiE` as an additive map. -/
noncomputable def PsiEMap (X : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Abelian.Ext.{0} X (unitsK k K) 0 →+
      ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X)) :=
  (PsiE (k := k) (Ω := Ω) (K := K) X).toAddMonoidHom

theorem PsiEMap_apply_toCoindH0 (X : Rep.{0} Coeff (K ≃ₐ[k] K))
    (x : Abelian.Ext.{0} X (unitsK k K) 0) :
    PsiEMap (k := k) (Ω := Ω) (K := K) X x
      = Work.SSGRoute.toCoindH0 X (Abelian.Ext.addEquiv₀ x) := rfl

theorem PsiEMap_injective (X : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Function.Injective (PsiEMap (k := k) (Ω := Ω) (K := K) X) :=
  (PsiE (k := k) (Ω := Ω) (K := K) X).injective

theorem PsiEMap_surjective (X : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Function.Surjective (PsiEMap (k := k) (Ω := Ω) (K := K) X) :=
  (PsiE (k := k) (Ω := Ω) (K := K) X).surjective

/-- The coefficient identification is compatible with the `π`'s of the canonical resolution. -/
theorem coeff_piH0 (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (y : Abelian.Ext.{0} (E1cF R) (unitsK k K) 0) :
    PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R)
        ((Abelian.Ext.mk₀ (Limits.kernel.ι (freeCover R))).precomp (unitsK k K)
          (by norm_num : 0 + 0 = 0) y)
      = piH0 (k := k) (Ω := Ω) (K := K) R
          (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cF R) y) := by
  rw [PsiEMap_apply_toCoindH0, PsiEMap_apply_toCoindH0]
  exact Work.SSGRoute.PT.e1aE1c_step_coeff (k := k) (Ω := Ω) (K := K)
    (E1cR1 R) (E1cF R) (Limits.kernel.ι (freeCover R))
    (precompAddHom_equivariant (Limits.kernel.ι (freeCover R))) y

/-- The image of the kernel of the `Ext`-side map is the range of `piH0`. -/
theorem map_PsiE_ker (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    AddSubgroup.map (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R))
        (PhiE (k := k) (Ω := Ω) (K := K) R).ker
      = (piH0 (k := k) (Ω := Ω) (K := K) R).range := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := AddSubgroup.mem_map.mp hz
    rw [← hyz]
    rw [PhiE_ker (k := k) (Ω := Ω) (K := K) R] at hy
    obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp hy
    rw [← hw, coeff_piH0 (k := k) (Ω := Ω) (K := K) R w]
    exact AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
  · intro z hz
    obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp hz
    obtain ⟨f, hf⟩ := (Work.SSGRoute.toCoindH0_bijective (E1cF R)).2 w
    refine AddSubgroup.mem_map.mpr ⟨
      (Abelian.Ext.mk₀ (Limits.kernel.ι (freeCover R))).precomp (unitsK k K)
        (by norm_num : 0 + 0 = 0) (Abelian.Ext.addEquiv₀.symm f), ?_, ?_⟩
    · rw [PhiE_ker (k := k) (Ω := Ω) (K := K) R]
      exact AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
    · rw [coeff_piH0 (k := k) (Ω := Ω) (K := K) R (Abelian.Ext.addEquiv₀.symm f), ← hw]
      congr 1
      rw [PsiEMap_apply_toCoindH0, AddEquiv.apply_symm_apply]
      exact hf

/-- Membership form of `map_PsiE_ker`. -/
theorem psiE_mem_range_iff (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (y : Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0) :
    PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y
        ∈ (piH0 (k := k) (Ω := Ω) (K := K) R).range
      ↔ y ∈ (PhiE (k := k) (Ω := Ω) (K := K) R).ker := by
  constructor
  · intro hy
    have h2 : PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y
        ∈ AddSubgroup.map (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R))
            (PhiE (k := k) (Ω := Ω) (K := K) R).ker := by
      rw [map_PsiE_ker (k := k) (Ω := Ω) (K := K) R]
      exact hy
    obtain ⟨y', hy', hyy'⟩ := AddSubgroup.mem_map.mp h2
    have hy'' : y' = y := PsiEMap_injective (k := k) (Ω := Ω) (K := K) (E1cR1 R) hyy'
    rw [hy''] at hy'
    exact hy'
  · intro hy
    rw [← map_PsiE_ker (k := k) (Ω := Ω) (K := K) R]
    exact AddSubgroup.mem_map.mpr ⟨y, hy, rfl⟩

/-- The `Ext`-side localisation of the `E1c` dictionary. -/
noncomputable def e1Loc (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Abelian.Ext.{0} R (unitsK k K) 1 ≃+
      Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0 ⧸
        (PhiE (k := k) (Ω := Ω) (K := K) R).ker :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (PhiE (k := k) (Ω := Ω) (K := K) R)
    (PhiE_surjective (k := k) (Ω := Ω) (K := K) R)).symm

theorem e1Loc_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (y : Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0) :
    e1Loc (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R y)
      = QuotientAddGroup.mk' (PhiE (k := k) (Ω := Ω) (K := K) R).ker y := by
  rw [show e1Loc (k := k) (Ω := Ω) (K := K) R
      = (QuotientAddGroup.quotientKerEquivOfSurjective
          (PhiE (k := k) (Ω := Ω) (K := K) R)
          (PhiE_surjective (k := k) (Ω := Ω) (K := K) R)).symm from rfl]
  rw [AddEquiv.symm_apply_eq]
  exact QuotientAddGroup.kerLift_mk (PhiE (k := k) (Ω := Ω) (K := K) R) y

/-- The `π`-cokernel comparison. -/
noncomputable def e2LocMap (R : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0 ⧸
        (PhiE (k := k) (Ω := Ω) (K := K) R).ker →+
      cokerH (k := k) (Ω := Ω) (K := K) R :=
  QuotientAddGroup.lift (PhiE (k := k) (Ω := Ω) (K := K) R).ker
    ((QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range).comp
      (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R)))
    (fun y hy => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff]
      exact (psiE_mem_range_iff (k := k) (Ω := Ω) (K := K) R y).mpr hy)

theorem e2LocMap_mk (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (y : Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0) :
    e2LocMap (k := k) (Ω := Ω) (K := K) R
        (QuotientAddGroup.mk' (PhiE (k := k) (Ω := Ω) (K := K) R).ker y)
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y) :=
  QuotientAddGroup.lift_mk' _ _ y

/-- The `E1c` dictionary, as an additive map. -/
noncomputable def e1cMap (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] :
    Abelian.Ext.{0} R (unitsK k K) 1 →+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) :=
  (betaEquiv (k := k) (Ω := Ω) (K := K) R).symm.toAddMonoidHom.comp
    ((e2LocMap (k := k) (Ω := Ω) (K := K) R).comp
      (e1Loc (k := k) (Ω := Ω) (K := K) R).toAddMonoidHom)

theorem e1cMap_Phi (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (y : Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0) :
    e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R y)
      = (betaEquiv (k := k) (Ω := Ω) (K := K) R).symm
          (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
            (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y)) := by
  rw [show e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R y)
      = (betaEquiv (k := k) (Ω := Ω) (K := K) R).symm
          (e2LocMap (k := k) (Ω := Ω) (K := K) R
            (e1Loc (k := k) (Ω := Ω) (K := K) R
              (PhiE (k := k) (Ω := Ω) (K := K) R y))) from rfl]
  rw [e1Loc_apply, e2LocMap_mk]

theorem e1cMap_injective (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] :
    Function.Injective (e1cMap (k := k) (Ω := Ω) (K := K) R) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  obtain ⟨y, hy⟩ := PhiE_surjective (k := k) (Ω := Ω) (K := K) R x
  rw [← hy] at hx ⊢
  rw [e1cMap_Phi (k := k) (Ω := Ω) (K := K) R y] at hx
  have h2 : QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
      (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y) = 0 := by
    have h := congrArg (fun z : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K R) =>
      (betaEquiv (k := k) (Ω := Ω) (K := K) R) z) hx
    rwa [AddEquiv.apply_symm_apply, map_zero] at h
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h2
  exact AddMonoidHom.mem_ker.mp ((psiE_mem_range_iff (k := k) (Ω := Ω) (K := K) R y).mp h2)

theorem e1cMap_surjective (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] :
    Function.Surjective (e1cMap (k := k) (Ω := Ω) (K := K) R) := by
  intro u
  obtain ⟨w, hw⟩ := QuotientAddGroup.mk'_surjective (piH0 (k := k) (Ω := Ω) (K := K) R).range
    (betaEquiv (k := k) (Ω := Ω) (K := K) R u)
  obtain ⟨v, hv⟩ := PsiEMap_surjective (k := k) (Ω := Ω) (K := K) (E1cR1 R) w
  refine ⟨PhiE (k := k) (Ω := Ω) (K := K) R v, ?_⟩
  rw [e1cMap_Phi (k := k) (Ω := Ω) (K := K) R v, hv, hw, AddEquiv.symm_apply_apply]

/-- Compatibility of `PhiE` with the comparison of canonical covers. -/
theorem PhiE_freeMapKernel (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) (g : R ⟶ R₂)
    (x : Abelian.Ext.{0} (E1cR1 R₂) (unitsK k K) 0) :
    PhiE (k := k) (Ω := Ω) (K := K) R
        ((Abelian.Ext.mk₀ (freeMapKernel g)).precomp (unitsK k K)
          (by norm_num : 0 + 0 = 0) x)
      = (Abelian.Ext.mk₀ g).comp (PhiE (k := k) (Ω := Ω) (K := K) R₂ x) (zero_add 1) := by
  rw [show (Abelian.Ext.mk₀ (freeMapKernel g)).precomp (unitsK k K)
        (by norm_num : 0 + 0 = 0) x
      = (Abelian.Ext.mk₀ (freeMapKernel g)).comp x (zero_add 0) from rfl]
  exact Work.SSGRoute.PT.e1aE1c_step_ext (unitsK k K) R R₂ g x

/-- The coefficient square for `freeMapKernel`. -/
theorem coeff_freeMapKernel (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) (g : R ⟶ R₂)
    (y : Abelian.Ext.{0} (E1cR1 R₂) (unitsK k K) 0) :
    PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R)
        ((Abelian.Ext.mk₀ (freeMapKernel g)).precomp (unitsK k K)
          (by norm_num : 0 + 0 = 0) y)
      = Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
          (precompAddHom (Rep.Hom.hom (freeMapKernel g)).toAddMonoidHom)
          (precompAddHom_equivariant (freeMapKernel g))
          (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R₂) y) := by
  rw [PsiEMap_apply_toCoindH0, PsiEMap_apply_toCoindH0]
  exact Work.SSGRoute.PT.e1aE1c_step_coeff (k := k) (Ω := Ω) (K := K)
    (E1cR1 R) (E1cR1 R₂) (freeMapKernel g)
    (precompAddHom_equivariant (freeMapKernel g)) y

/-- **Naturality of the pull-back map `betaH`** in the coefficient. -/
theorem betaH_natural (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) (g : R ⟶ R₂)
    (hg : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom))
    (y : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R₂)) :
    betaH (k := k) (Ω := Ω) (K := K) R
        (Work.AbsoluteKummer.mapH1
          (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg y)
      = cokerMap (k := k) (Ω := Ω) (K := K) R R₂ g
          (betaH (k := k) (Ω := Ω) (K := K) R₂ y) := by
  obtain ⟨c₂, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R₂)).comap
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R₂)).subtype) y
  have hmap1 : Work.AbsoluteKummer.mapH1
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg
        (QuotientAddGroup.mk' ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.homCoind k Ω K R₂)).comap
          (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.homCoind k Ω K R₂)).subtype) c₂)
      = QuotientAddGroup.mk' ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.homCoind k Ω K R)).comap
          (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.homCoind k Ω K R)).subtype)
        (Work.AbsoluteKummer.mapZ1
          (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg c₂) :=
    QuotientAddGroup.lift_mk' _ _ c₂
  have hb1 := betaH_mk (k := k) (Ω := Ω) (K := K) R
    (Work.AbsoluteKummer.mapZ1
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg c₂)
  have hb2 := betaH_mk (k := k) (Ω := Ω) (K := K) R₂ c₂
  rw [hmap1, hb1, hb2, cokerMap_mk]
  have hcomp : ∀ γ : Ω ≃ₐ[k] Ω,
      Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R)
          ((precompAddHom (Rep.Hom.hom (freeMap g)).toAddMonoidHom)
            (liftOf (k := k) (Ω := Ω) (K := K) R₂ c₂)) γ
        = (precompAddHom (Rep.Hom.hom (freeMap g)).toAddMonoidHom)
            ((Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R₂)
              (liftOf (k := k) (Ω := Ω) (K := K) R₂ c₂)) γ) := by
    intro γ
    rw [Work.GroupCohomology.d0_apply, Work.GroupCohomology.d0_apply, map_sub,
      precompAddHom_equivariant (freeMap g) γ (liftOf (k := k) (Ω := Ω) (K := K) R₂ c₂)]
  have hn : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R)
      ((precompAddHom (Rep.Hom.hom (freeMap g)).toAddMonoidHom)
        (liftOf (k := k) (Ω := Ω) (K := K) R₂ c₂))
      = ((Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
            (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R)
            (Work.AbsoluteKummer.mapZ1
              (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg c₂) :
          ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R))) :
            (Ω ≃ₐ[k] Ω) → E1cN (k := k) (Ω := Ω) (K := K) R) := by
    funext γ
    rw [hcomp γ, liftOf_spec (k := k) (Ω := Ω) (K := K) R₂ c₂]
    simp only [Work.AbsoluteKummer.mapZ1_apply, iotaH_apply,
      Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
    refine AddMonoidHom.ext (fun v => ?_)
    simp only [AddMonoidHom.comp_apply]
    exact congrArg (fun w => (c₂ : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R₂) γ w)
      (coverMap_freeMap (k := k) (Ω := Ω) (K := K) R R₂ g v)
  rw [← betaRaw_congr (k := k) (Ω := Ω) (K := K) R
      (Work.AbsoluteKummer.mapZ1
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg c₂)
      ((precompAddHom (Rep.Hom.hom (freeMap g)).toAddMonoidHom)
        (liftOf (k := k) (Ω := Ω) (K := K) R₂ c₂)) hn]
  congr 1
  apply Subtype.ext
  exact (DFunLike.congr_fun (piH_natural (k := k) (Ω := Ω) (K := K) R R₂ g)
    (liftOf (k := k) (Ω := Ω) (K := K) R₂ c₂)).symm


theorem e1cMap_natural (R R₂ : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    [Module.Finite ℤ R₂.V] (g : R ⟶ R₂)
    (hg : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom))
    (x : Abelian.Ext.{0} R₂ (unitsK k K) 1) :
    e1cMap (k := k) (Ω := Ω) (K := K) R
        ((Abelian.Ext.mk₀ g).comp x (zero_add 1))
      = Work.AbsoluteKummer.mapH1
          (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg
          (e1cMap (k := k) (Ω := Ω) (K := K) R₂ x) := by
  obtain ⟨y, hy⟩ := PhiE_surjective (k := k) (Ω := Ω) (K := K) R₂ x
  rw [← hy, ← PhiE_freeMapKernel (k := k) (Ω := Ω) (K := K) R R₂ g y]
  rw [e1cMap_Phi (k := k) (Ω := Ω) (K := K) R
      ((Abelian.Ext.mk₀ (freeMapKernel g)).precomp (unitsK k K)
        (by norm_num : 0 + 0 = 0) y),
    e1cMap_Phi (k := k) (Ω := Ω) (K := K) R₂ y]
  rw [coeff_freeMapKernel (k := k) (Ω := Ω) (K := K) R R₂ g y]
  rw [← cokerMap_mk (k := k) (Ω := Ω) (K := K) R R₂ g
      (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R₂) y)]
  have hkey : betaH (k := k) (Ω := Ω) (K := K) R
      (Work.AbsoluteKummer.mapH1
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg
        ((betaEquiv (k := k) (Ω := Ω) (K := K) R₂).symm
          (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R₂).range
            (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R₂) y))))
      = cokerMap (k := k) (Ω := Ω) (K := K) R R₂ g
          (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R₂).range
            (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R₂) y)) := by
    have h := betaH_natural (k := k) (Ω := Ω) (K := K) R R₂ g hg
      ((betaEquiv (k := k) (Ω := Ω) (K := K) R₂).symm
        (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R₂).range
          (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R₂) y)))
    rwa [show betaH (k := k) (Ω := Ω) (K := K) R₂
        ((betaEquiv (k := k) (Ω := Ω) (K := K) R₂).symm
          (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R₂).range
            (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R₂) y)))
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R₂).range
          (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R₂) y) from by
        rw [← betaEquiv_apply, AddEquiv.apply_symm_apply]] at h
  rw [← hkey, ← betaEquiv_apply, AddEquiv.symm_apply_apply]

/-- **The `E1c` dictionary**: `Ext¹_G(R,Kˣ) ≃+ H¹(Γ, Hom_ℤ(R,Ωˣ))`. -/
noncomputable def e1cEquiv (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] :
    Abelian.Ext.{0} R (unitsK k K) 1 ≃+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) :=
  AddEquiv.ofBijective (e1cMap (k := k) (Ω := Ω) (K := K) R)
    ⟨e1cMap_injective (k := k) (Ω := Ω) (K := K) R,
      e1cMap_surjective (k := k) (Ω := Ω) (K := K) R⟩


theorem e1c_natural {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] :
    ∃ e : ∀ (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V],
        CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1 ≃+
          Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R),
      ∀ (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
        (R₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R₂.V]
        (g : R ⟶ R₂) (hg : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom))
        (x : CategoryTheory.Abelian.Ext.{0} R₂ (SSGRoute.PTExt.unitsK k K) 1),
        e R ((CategoryTheory.Abelian.Ext.mk₀ g).comp x (zero_add 1)) =
          Work.AbsoluteKummer.mapH1
            (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg
            (e R₂ x) := by
  refine ⟨fun R hR => letI := hR; e1cEquiv (k := k) (Ω := Ω) (K := K) R, ?_⟩
  intro R hR R₂ hR₂ g hg x
  haveI := hR
  haveI := hR₂
  exact e1cMap_natural (k := k) (Ω := Ω) (K := K) R R₂ g hg x


