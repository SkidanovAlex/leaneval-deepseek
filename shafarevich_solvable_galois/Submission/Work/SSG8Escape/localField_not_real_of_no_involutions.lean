import Mathlib
import Submission.Work.SSGRoute.ssg8Chebotarev
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.ArchDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSG8Escape

open NumberField

noncomputable section

/-! ## Two auxiliary facts about archimedean places

The target lemma `localField_not_real_of_no_involutions` says that the completion `K_v` of a number
field `K` at an infinite place `v` is never isomorphic to a subfield of `ℝ`, granted that `K`
contains a primitive `p`-th root of unity `ζ` and that, for `p = 2`, `Gal(Ω/K)` has no involution.
Two independent inputs produce this.

* If `p ≠ 2` then `m = p ≥ 3` and a primitive `m`-th root of unity is not real; hence `K` is
  totally complex and `K_v ≅ ℂ`, which does not embed in `ℝ`.
* If `p = 2` then `ζ = -1` carries no information, and one argues by contraposition: a ring
  homomorphism `K_v →+* ℝ` gives a real place of `K`, hence (Artin–Schreier) a non-trivial
  involution in `Gal(Ω/K)`.
-/

/-- There is no unital ring homomorphism from `ℂ` to `ℝ`: such a map would send `I` to a real
square root of `-1`. -/
theorem not_exists_ringHom_complex_real : ¬ ∃ φ : ℂ →+* ℝ, True := by
  rintro ⟨φ, -⟩
  have h : (φ Complex.I) ^ 2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hnn : 0 ≤ (φ Complex.I) ^ 2 := sq_nonneg _
  linarith

/-- **The completion of a number field at an infinite place is not real when the field contains a
primitive `m`-th root of unity with `m ≥ 3`.**

If `ζ : L` is primitive of order `m ≥ 3`, then `L` has no real place, so `w` is a complex place and
`w.Completion ≃+* ℂ` does not map to `ℝ`. -/
theorem completion_not_real_of_primitiveRoot_odd (m : ℕ) (hm : 3 ≤ m) {L : Type} [Field L]
    [NumberField L] (ζ : L) (hζ : IsPrimitiveRoot ζ m) (w : NumberField.InfinitePlace L) :
    ¬ ∃ φ : w.Completion →+* ℝ, True := by
  classical
  haveI : IsEmpty {w : NumberField.InfinitePlace L // w.IsReal} :=
    Fintype.card_eq_zero_iff.mp
      (NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by omega) hζ)
  have hwC : w.IsComplex := by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
    intro hwR
    exact isEmptyElim (⟨w, hwR⟩ : {w : NumberField.InfinitePlace L // w.IsReal})
  rintro ⟨φ, -⟩
  exact not_exists_ringHom_complex_real
    ⟨φ.comp
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).symm.toRingHom,
      trivial⟩

/-- **A real-valued ring homomorphism out of the completion at an infinite place of `K` produces a
non-trivial involution fixing `K`.**

Indeed, `w.Completion →+* ℝ` composed with `K →+* w.Completion` is a real embedding of `K`;
complex conjugation at the corresponding real place of `K`, transported into the algebraic closure
`Ω`, is an order-two automorphism of `Ω` over `K`, hence an element of `K.fixingSubgroup`. -/
theorem involution_of_ringHom_to_real
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    (w : NumberField.InfinitePlace ↥K) (φ : w.Completion →+* ℝ) :
    ∃ c ∈ K.fixingSubgroup, c ^ 2 = 1 ∧ c ≠ 1 := by
  classical
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  -- the real embedding `ρ` of `K` induced by `φ`, and the real place `w'` it defines
  let ρ : ↥K →+* ℝ := φ.comp (algebraMap ↥K w.Completion)
  let ψ : ↥K →+* ℂ := (algebraMap ℝ ℂ).comp ρ
  have hψ : NumberField.ComplexEmbedding.IsReal ψ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    show (starRingEnd ℂ) (ψ x) = ψ x
    rw [show ψ x = ((ρ x : ℝ) : ℂ) from rfl, starRingEnd_apply]
    exact Complex.conj_ofReal _
  let w' : NumberField.InfinitePlace ↥K := NumberField.InfinitePlace.mk ψ
  have hw' : w'.IsReal := ⟨ψ, hψ, rfl⟩
  -- complex conjugation at `w'`, inside `Gal(Ω/K)`
  haveI : CharP ↥K 0 := CharP.ofCharZero ↥K
  obtain ⟨c, hc2, hc1, -⟩ :=
    Work.SSGRoute.ZDataTwo.exists_conjInv_kummerChar_eq_zero_iff (k := ↥K) (Ω := Ω)
      (-1) (IsPrimitiveRoot.neg_one 0 (by norm_num)) w' hw'
  -- `c` is `↥K`-linear, hence fixes `K` pointwise when regarded as a `k`-automorphism of `Ω`
  have hcc : ∀ y : Ω, c (c y) = y := by
    intro y
    have h1 : (c ^ 2) y = (1 : Ω ≃ₐ[↥K] Ω) y := by rw [hc2]
    simpa [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] using h1
  refine ⟨c.restrictScalars k, ?_, ?_, ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact c.commutes ⟨x, hx⟩
  · apply AlgEquiv.ext
    intro x
    simpa [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] using hcc x
  · intro h1
    apply hc1
    ext x
    simpa [AlgEquiv.one_apply] using congrArg (fun e : Ω ≃ₐ[k] Ω => e x) h1

/-- **Shafarevich, prime-`2` correction: the local field at an archimedean place is not real.**

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K` an intermediate field finite over
`k` and `ζ ∈ K` a primitive `p`-th root of unity.  If for `p = 2` the group `Gal(Ω/K)` has no
involution, then the completion of `K` at any archimedean place admits no ring homomorphism to
`ℝ` — i.e. that completion is `ℂ`, not `ℝ`. -/
theorem localField_not_real_of_no_involutions
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (v : NK.GlobalCFT.Place ↥K) (hv : ¬ v.IsFinite) :
    ¬ ∃ φ : NK.GlobalCFT.Place.localField ↥K v →+* ℝ, True := by
  rintro ⟨φ, -⟩
  cases v with
  | inl w =>
    -- `v` is the archimedean place attached to `w`
    have φ' : w.Completion →+* ℝ := φ
    rcases eq_or_ne p 2 with hp2 | hp2
    · -- for `p = 2` the hypothesis on involutions rules out a real place
      obtain ⟨c, hcK, hc2, hc1⟩ := involution_of_ringHom_to_real K w φ'
      exact hc1 (hKimag hp2 c hcK hc2)
    · -- for `p ≠ 2` the prime `p` is at least `3`, so `K` is totally complex
      exact completion_not_real_of_primitiveRoot_odd p (by have := (Fact.out : p.Prime).two_le; omega)
        ζ hζ w ⟨φ', trivial⟩
  | inr q => exact absurd (NK.GlobalCFT.Place.isFinite_ofFinite q) hv

end

end Work.SSG8Escape
