import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.InvAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option linter.unusedVariables false

/-- The decomposition group of the place linked to an involution.  For an involution `c ≠ 1` of
`Ω/k` and an embedding `φ : Ω →+* ℂ` with `φ ∘ c = conj ∘ φ`, the infinite place `w = mk (φ|_K)` of
any finite Galois `K/k` inside `Ω` has `D_w = ⟨res c⟩` (trivial when `w` is real).

Route.  `res c ∈ D_w`: `φ|_K ∘ c = conj ∘ φ|_K`, and `mk` identifies an embedding with its conjugate
(`NumberField.InfinitePlace.mk_conjugate_eq`).  Conversely, `σ • w = w` means
`mk (φ|_K ∘ σ⁻¹) = mk (φ|_K)`, so `φ|_K ∘ σ⁻¹` is `φ|_K` or `conj ∘ φ|_K = φ|_K ∘ res c`
(`NumberField.InfinitePlace.mk_eq_iff`); injectivity of `φ` gives `σ = 1` or `σ = res c`.  This is
the last clause of `ArchPlace.linkedPlaceOfInvolution` for a GIVEN `φ`; prove it once here and let
that node use it. -/
theorem decompK_linked (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) :
    SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) =
      (Subgroup.zpowers c).map (SSGRoute.res k K) := by
  let f : ↥K →+* ℂ := φ.comp (algebraMap (↥K) Ω)
  let r : ↥K ≃ₐ[k] ↥K := SSGRoute.res k K c
  change SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk f)) =
    (Subgroup.zpowers c).map (SSGRoute.res k K)
  have hf_apply : ∀ y : ↥K, f y = φ (y : Ω) := fun y => rfl
  have hcoe_r : ∀ y : ↥K, (r y : Ω) = c (y : Ω) :=
    fun y => AlgEquiv.restrictNormalHom_apply K c y
  have hc2' : c * c = 1 := by simpa [pow_two] using hc2
  have hr2 : r * r = 1 := by
    have h := map_mul (SSGRoute.res k K) c c
    rw [hc2', map_one] at h
    exact h.symm
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hrsymm : r.symm = r := by rw [← AlgEquiv.aut_inv r]; exact hrinv
  -- `res c` fixes the place: the embedding `f` becomes its conjugate.
  have hfconj : f.comp (r : ↥K →+* ↥K) = NumberField.ComplexEmbedding.conjugate f := by
    ext x
    calc (f.comp (r : ↥K →+* ↥K)) x
        = f (r x) := rfl
      _ = φ ((r x : ↥K) : Ω) := hf_apply (r x)
      _ = φ (c (x : Ω)) := by rw [hcoe_r x]
      _ = starRingEnd ℂ (φ (x : Ω)) := hφ (x : Ω)
      _ = starRingEnd ℂ (f x) := by rw [hf_apply]
      _ = (NumberField.ComplexEmbedding.conjugate f) x := rfl
  have hrD : r ∈ SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk f)) := by
    rw [MulAction.mem_stabilizer_iff]
    rw [NK.GlobalCFT.Place.smul_ofInfinite, NumberField.InfinitePlace.smul_mk, hrsymm, hfconj,
      NumberField.InfinitePlace.mk_conjugate_eq]
  refine le_antisymm ?_ ?_
  · -- conversely, a stabiliser element is `1` or `res c`: an embedding of a place is only
    -- ambiguous up to complex conjugation
    intro σ hσ
    have hσ'' : σ • NumberField.InfinitePlace.mk f = NumberField.InfinitePlace.mk f := by
      have h := hσ
      rw [MulAction.mem_stabilizer_iff] at h
      rwa [NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj] at h
    rw [NumberField.InfinitePlace.smul_mk, NumberField.InfinitePlace.mk_eq_iff] at hσ''
    rcases hσ'' with h1 | h1
    · have hpt : ∀ x : ↥K, σ.symm x = x := fun x => f.injective (by
        have hx := congrArg (fun g : ↥K →+* ℂ => g x) h1
        exact hx)
      have hsymm1 : σ.symm = 1 := AlgEquiv.ext hpt
      have hσ1 : σ = 1 := by
        have : σ⁻¹ = 1 := by rw [AlgEquiv.aut_inv]; exact hsymm1
        exact inv_eq_one.mp this
      rw [Subgroup.mem_map]
      exact ⟨1, Subgroup.one_mem _, by rw [map_one, hσ1]⟩
    · have hcomp : f.comp (↑σ.symm : ↥K →+* ↥K) = NumberField.ComplexEmbedding.conjugate f := by
        have hcongr := congrArg NumberField.ComplexEmbedding.conjugate h1
        rwa [show NumberField.ComplexEmbedding.conjugate
            (NumberField.ComplexEmbedding.conjugate (f.comp (↑σ.symm : ↥K →+* ↥K))) =
            f.comp (↑σ.symm : ↥K →+* ↥K) from
          NumberField.ComplexEmbedding.involutive_conjugate ↥K _] at hcongr
      have hpt : ∀ x : ↥K, σ.symm x = r x := fun x => f.injective (by
        have hx1 := congrArg (fun g : ↥K →+* ℂ => g x) hcomp
        have hx2 := congrArg (fun g : ↥K →+* ℂ => g x) hfconj
        calc f (σ.symm x) = (NumberField.ComplexEmbedding.conjugate f) x := hx1
          _ = f (r x) := hx2.symm)
      have hsymm : σ.symm = r := AlgEquiv.ext hpt
      have hσr : σ = r := by
        rw [← hrsymm, ← hsymm]
        exact (AlgEquiv.symm_symm σ).symm
      rw [Subgroup.mem_map]
      exact ⟨c, Subgroup.mem_zpowers c, hσr.symm⟩
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
    exact hrD

end Work.SSGRoute.PT
