import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LTDDefs.H2locAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LTDDefs.H2loc

open scoped Classical

/-- The extension by `0` off `H` of a `1`-cochain `f` of `↥H`. -/
noncomputable def extendFun1 {Γ : Type*} [Group Γ] {M : Type*} [Zero M] (H : Subgroup Γ) (f : ↥H → M) :
    Γ → M :=
  fun g => if hg : g ∈ H then f ⟨g, hg⟩ else 0

@[simp] lemma extendFun1_apply_mem {Γ : Type*} [Group Γ] {M : Type*} [Zero M]
    (H : Subgroup Γ) (f : ↥H → M) {g : Γ} (hg : g ∈ H) :
    extendFun1 H f g = f ⟨g, hg⟩ := dif_pos hg

lemma extendFun1_apply_not_mem {Γ : Type*} [Group Γ] {M : Type*} [Zero M]
    (H : Subgroup Γ) (f : ↥H → M) {g : Γ} (hg : g ∉ H) :
    extendFun1 H f g = 0 := dif_neg hg

theorem extendFun2_mem_coboundaries2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {c : ↥H × ↥H → M} (hc : c ∈ Work.AbsoluteKummer.Z2 ↥H M)
    (hb : c ∈ Work.AbsoluteKummer.B2 ↥H M) :
    extendFun2 H c ∈ coboundaries2 p k Ω K M H := by
  change SSGRoute.IsCoboundary2On (SSGRoute.res k K) H (extendFun2 H c)
  rw [Work.AbsoluteKummer.mem_B2_iff] at hb
  obtain ⟨f, hfC, hfd⟩ := hb
  have hflc : Work.AbsoluteKummer.IsLocallyConstant f := hfC
  obtain ⟨U, hUo, hU⟩ :=
    Work.SSGRoute.exists_openSubgroup_mul_eq_of_isLocallyConstant k Ω H hH hflc
  refine ⟨extendFun1 H f, ⟨U, hUo, ?_⟩, ?_⟩
  · intro g hg u hu huH
    have hgu : g * u ∈ H := H.mul_mem hg huH
    rw [extendFun1_apply_mem H f hgu, extendFun1_apply_mem H f hg]
    have h1 := hU ⟨g, hg⟩ u huH hu
    simpa using h1
  · intro g hg h hh
    have hgh : g * h ∈ H := H.mul_mem hg hh
    rw [Work.SSGRoute.extendFun2_apply H c hg hh,
      extendFun1_apply_mem H f hh, extendFun1_apply_mem H f hgh,
      extendFun1_apply_mem H f hg]
    have h1 : c (⟨g, hg⟩, ⟨h, hh⟩) =
        Work.GroupCohomology.d1 ↥H M f (⟨g, hg⟩, ⟨h, hh⟩) := by rw [hfd]
    rw [h1]
    rw [Work.GroupCohomology.d1_apply]
    have hc' := hcompat ⟨g, hg⟩ (f ⟨h, hh⟩)
    simp only [Subtype.coe_mk] at hc'
    rw [← hc']
    rw [show (⟨g, hg⟩ * ⟨h, hh⟩ : ↥H) = ⟨g * h, hgh⟩ from Subtype.ext rfl]

end Work.SSGRoute.LTDDefs.H2loc
