import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq

namespace Commons.RingTheory.Valuation

open scoped Pointwise

/-- **A totally decomposed place has at least two prolongations to a finite separable extension.**

Let `E / F` be a Galois extension and `A` a valuation subring of `E` whose decomposition group
`MulAction.stabilizer (E ≃ₐ[F] E) A` is trivial, so that the place of `F` cut out by `A` splits
completely in `E`.  Then for any finite separable extension `F' / F` of degree `> 1` that embeds
into `E` (via `ι : F' →ₐ[F] E`), the place `A ∩ F` has at least two distinct prolongations to
`F'`: there are two distinct valuation subrings `B₁ ≠ B₂` of `F'` with
`Bᵢ.comap (algebraMap F F') = A.comap (algebraMap F E)`.

The proof is by contradiction.  Write `L = ι(F') ⊆ E`.  The extension `E / L` is again Galois and
`A` still has trivial stabiliser in `Gal(E/L)`, so the prolongations of `Ã = A ∩ L` to `E` are
exactly the `Gal(E/L)`-conjugates of `A`.  If the place `A ∩ F` had only one prolongation to `L`,
then *every* conjugate `σ • A` (`σ ∈ Gal(E/F)`) would restrict to `Ã` on `L`, hence would be a
`Gal(E/L)`-conjugate of `A`.  Since the stabiliser of `A` is trivial, this forces
`Gal(E/F) = Gal(E/L)`, i.e. `L = F` by the Galois correspondence, contradicting `[F' : F] > 1`. -/
theorem exists_two_prolongations_of_stabilizer_eq_bot {F F' E : Type*} [Field F] [Field F'] [Field E]
    [Algebra F F'] [Algebra F E] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    [IsGalois F E] (A : ValuationSubring E)
    (hD : MulAction.stabilizer (E ≃ₐ[F] E) A = ⊥) (hdim : 1 < Module.finrank F F')
    (ι : F' →ₐ[F] E) :
    ∃ B₁ B₂ : ValuationSubring F', B₁ ≠ B₂ ∧
      B₁.comap (algebraMap F F') = A.comap (algebraMap F E) ∧
      B₂.comap (algebraMap F F') = A.comap (algebraMap F E) := by
  let L : IntermediateField F E := ι.fieldRange
  let e : F' ≃ₐ[F] ↥L := ι.equivFieldRange
  have hcomap_eq : ∀ (C : ValuationSubring E),
      C.comap (algebraMap F E) = (C.comap (algebraMap ↥L E)).comap (algebraMap F ↥L) := by
    intro C
    rw [ValuationSubring.comap_comap, IsScalarTower.algebraMap_eq F ↥L E]
  have hL_ne_bot : L ≠ ⊥ := by
    intro h
    have hfin : Module.finrank F ↥L = Module.finrank F F' := e.toLinearEquiv.finrank_eq.symm
    rw [h, IntermediateField.finrank_bot] at hfin
    omega
  have hH : L.fixingSubgroup ≠ ⊤ := by
    intro hHt
    have h1 : IntermediateField.fixedField L.fixingSubgroup = L :=
      InfiniteGalois.fixedField_fixingSubgroup L
    rw [hHt, InfiniteGalois.fixedField_bot] at h1
    exact hL_ne_bot h1.symm
  obtain ⟨σ, hσ⟩ : ∃ σ : E ≃ₐ[F] E, σ ∉ L.fixingSubgroup := by
    by_contra h
    push Not at h
    exact hH (Subgroup.ext fun x => ⟨fun _ => trivial, fun _ => h x⟩)
  have hfix : (σ • A).comap (algebraMap F E) = A.comap (algebraMap F E) := by
    ext f
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_comap]
    change (σ⁻¹ : E ≃ₐ[F] E) (algebraMap F E f) ∈ A ↔ (algebraMap F E) f ∈ A
    rw [(σ⁻¹).commutes]
  set B : ValuationSubring ↥L := (σ • A).comap (algebraMap ↥L E) with hBdef
  have hBcomap : B.comap (algebraMap F ↥L) =
      (A.comap (algebraMap ↥L E)).comap (algebraMap F ↥L) := by
    rw [hBdef, ← hcomap_eq (σ • A), hfix, hcomap_eq A]
  have hBne : B ≠ A.comap (algebraMap ↥L E) := by
    intro hBA
    have hcomap : (σ • A).comap (algebraMap ↥L E) =
        A.comap (algebraMap ↥L E) := by
      rw [← hBA, hBdef]
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_comap_eq (F := ↥L) (E := E) A (σ • A) hcomap.symm
    have hτF : (τ.restrictScalars F) • A = σ • A := by
      rw [← hτ]; rfl
    have hmem : (σ⁻¹ * (τ.restrictScalars F)) ∈
        MulAction.stabilizer (E ≃ₐ[F] E) A := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hτF, inv_smul_smul]
    rw [hD, Subgroup.mem_bot] at hmem
    have hσeq : σ = τ.restrictScalars F := by
      have h2 := congrArg (fun g => σ * g) hmem
      simp only [mul_one] at h2
      rw [← mul_assoc, mul_inv_cancel, one_mul] at h2
      exact h2.symm
    apply hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hσeq]
    show τ (x : E) = (x : E)
    have : (x : E) = algebraMap ↥L E ⟨x, hx⟩ := rfl
    rw [this]
    exact τ.commutes ⟨x, hx⟩
  refine ⟨B.comap (e : F' →+* ↥L), (A.comap (algebraMap ↥L E)).comap (e : F' →+* ↥L),
    ?_, ?_, ?_⟩
  · intro heq
    apply hBne
    apply ValuationSubring.ext
    intro y
    have h1 : e.symm y ∈ B.comap (e : F' →+* ↥L) ↔ y ∈ B := by
      rw [ValuationSubring.mem_comap]; simp
    have h2 : e.symm y ∈ (A.comap (algebraMap ↥L E)).comap (e : F' →+* ↥L) ↔
        y ∈ A.comap (algebraMap ↥L E) := by
      rw [ValuationSubring.mem_comap]; simp
    rw [← h1, heq, h2]
  · rw [ValuationSubring.comap_comap]
    have hcomp : ((e : F' →+* ↥L).comp (algebraMap F F')) = (algebraMap F ↥L) := by
      ext f
      exact congrArg (fun z : ↥L => (z : E)) (e.commutes f)
    rw [hcomp, hBcomap]
    exact (hcomap_eq A).symm
  · rw [ValuationSubring.comap_comap]
    have hcomp : ((e : F' →+* ↥L).comp (algebraMap F F')) = (algebraMap F ↥L) := by
      ext f
      exact congrArg (fun z : ↥L => (z : E)) (e.commutes f)
    rw [hcomp]
    exact (hcomap_eq A).symm

end Commons.RingTheory.Valuation
