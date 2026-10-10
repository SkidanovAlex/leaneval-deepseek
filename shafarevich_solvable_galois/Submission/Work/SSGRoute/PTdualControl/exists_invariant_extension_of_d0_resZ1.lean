import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.PT.akH2Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTdualControl

open Work.SSGRoute.ExtChain.E1cGeneric

/-- The restriction of a `1`-cocycle to a subgroup, at a point. -/
theorem resZ1_apply {Γ : Type} [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ]
    (N : Subgroup Γ) (P : Type) [AddCommGroup P] [DistribMulAction Γ P]
    (f : ↥(Work.AbsoluteKummer.Z1 Γ P)) (n : ↥N) :
    ((Work.SSGRoute.PT.H2Fin.resZ1 N P f : Work.AbsoluteKummer.Z1 ↥N P) : ↥N → P) n
      = (f : Γ → P) (n : Γ) := rfl

theorem exists_invariant_extension_of_d0_resZ1
    {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (p : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R))))
    (n : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R)
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)))
    (hn : Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) R n
      = (p : Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R)))
    (hc : ∀ γ : Ω ≃ₐ[k] Ω,
        Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) R
            ((c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R) γ)
          = Work.SSGRoute.ExtChain.E1cGeneric.cnj (k := k) (Ω := Ω) (K := K) R γ n - n)
    (m : Work.SSGRoute.homCoind k Ω K R)
    (hm : Work.GroupCohomology.d0 ↥D (Work.SSGRoute.homCoind k Ω K R) m
      = ((Work.SSGRoute.PT.H2Fin.resZ1 D (Work.SSGRoute.homCoind k Ω K R) c :
          Work.AbsoluteKummer.Z1 ↥D (Work.SSGRoute.homCoind k Ω K R)) : ↥D → Work.SSGRoute.homCoind k Ω K R)) :
    ∃ Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R,
      Φ ∈ Work.AbsoluteKummer.H0 ↥D
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R) ∧
      Φ.comp (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) R)
        = (p : Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R)) := by
  -- The witness is `Φ = n - ι(m)`.
  refine ⟨n - iotaH (k := k) (Ω := Ω) (K := K) R m, ?_, ?_⟩
  · -- `Φ` is `D`-invariant: `ι(γ • m - m) = ι(c γ) = cnj γ n - n`.
    rw [Work.GroupCohomology.mem_invariants]
    intro δ
    have hmδ : (δ : Ω ≃ₐ[k] Ω) • m - m
        = (c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R) (δ : Ω ≃ₐ[k] Ω) := by
      have h := congrFun hm δ
      rw [resZ1_apply] at h
      simpa [Work.GroupCohomology.d0_apply, Subgroup.smul_def] using h
    have h2 : cnj (k := k) (Ω := Ω) (K := K) R (δ : Ω ≃ₐ[k] Ω)
          (iotaH (k := k) (Ω := Ω) (K := K) R m) - iotaH (k := k) (Ω := Ω) (K := K) R m
        = cnj (k := k) (Ω := Ω) (K := K) R (δ : Ω ≃ₐ[k] Ω) n - n := by
      have h := congrArg (iotaH (k := k) (Ω := Ω) (K := K) R) hmδ
      rw [map_sub, iotaH_smul, hc (δ : Ω ≃ₐ[k] Ω)] at h
      exact h
    rw [Subgroup.smul_def]
    change cnj (k := k) (Ω := Ω) (K := K) R (δ : Ω ≃ₐ[k] Ω)
        (n - iotaH (k := k) (Ω := Ω) (K := K) R m)
      = n - iotaH (k := k) (Ω := Ω) (K := K) R m
    rw [cnj_sub]
    have h4 : cnj (k := k) (Ω := Ω) (K := K) R (δ : Ω ≃ₐ[k] Ω) n
        = cnj (k := k) (Ω := Ω) (K := K) R (δ : Ω ≃ₐ[k] Ω)
            (iotaH (k := k) (Ω := Ω) (K := K) R m)
          - iotaH (k := k) (Ω := Ω) (K := K) R m + n := by
      rw [h2]; abel
    rw [h4]; abel
  · -- `π Φ = π n - π (ι m) = p`.
    rw [← Work.SSGRoute.ExtChain.E1cGeneric.piH_apply (k := k) (Ω := Ω) (K := K) R
      (n - iotaH (k := k) (Ω := Ω) (K := K) R m)]
    rw [map_sub, Work.SSGRoute.ExtChain.E1cGeneric.piH_iotaH, hn, sub_zero]

end Work.SSGRoute.PTdualControl
