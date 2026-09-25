import Mathlib
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Reconstruct.splitFrobeniusBase
import Submission.NK.Chebotarev.FrobRestriction
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHomType
import Submission.NK.Chebotarev.GalRestrictCompat
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.NK.Reconstruct.NumFieldIn

/-!
# The base change of a Frobenius element, with no hypothesis on the ramification

Let `K ⊆ L` be finite normal levels of `Ω/ℚ` (`NK.Reconstruct.FrobLevel`), `𝔭` a prime of `L`
whose residue degree over `K` is one (`𝔭.asIdeal.inertiaDeg (𝓞 K) = 1`), and `σ ∈ Gal(Ω/L)` a
Frobenius element at `𝔭` in the sense of `NK.Reconstruct.IsFrobElementAt`.  Then the restriction
`σ|_K ∈ Gal(Ω/K)` is a Frobenius element at the prime `𝔭 ∩ 𝓞 K`.

This is the point of Proposition 4f.3 of Shimizu (arXiv:2009.10431, §4) at which the naive
statement fails (the inclusion `G_L ↪ G_K` carries `Frob_𝔭` to `Frob_{𝔭|K}^{f}`, with `f` the
residue degree; README §19.8 records the counterexample `ℚ ⊆ ℚ(i)`, `𝔭 = (3)`); the residue degree
one hypothesis is exactly what makes the two Frobenius conditions agree, since the exponents
`#(𝓞 K ⧸ 𝔭 ∩ 𝓞 K)` and `#(𝓞 L ⧸ 𝔭)` then coincide.

The proof applies the hypothesis at the level `N · L` (the compositum of an arbitrary finite normal
level `N/K` with `L`), which is a finite normal level of `Ω/L`; the Frobenius condition there is
transported to the base field `K` by
`NK.Reconstruct.isFrobAt_of_isFrobAt_of_inertiaDeg_eq_one`, and then restricted to the normal
subfield `N/K` by `NK.Chebotarev.IsFrobAtRestrictNormalHomType`.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4;
J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. XII §12.2.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField


open scoped NumberField
open NK.Chebotarev

theorem isFrobElementAt_restrictScalars_of_inertiaDeg_eq_one {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (K : NK.Reconstruct.NumFieldIn ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω) (hKL : K.L ≤ L.L)
    [Algebra ↥K.L ↥L.L] [IsScalarTower ↥K.L ↥L.L Ω]
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L)
    (hdeg : 𝔭.asIdeal.inertiaDeg (NumberField.RingOfIntegers ↥K.L) = 1)
    (σ : Gal(Ω/↥L.L)) (hσ : NK.Reconstruct.IsFrobElementAt 𝔭 σ) :
    NK.Reconstruct.IsFrobElementAt (𝔭.under (NumberField.RingOfIntegers ↥K.L))
      (σ.restrictScalars ↥K.L) := by
  unfold NK.Reconstruct.IsFrobElementAt
  intro N FinN NormN NFN
  haveI : FiniteDimensional ↥K.L N := FinN
  haveI : Normal ↥K.L N := NormN
  haveI : NumberField ↥N := NFN
  -- The level `L.L` viewed over `K.L`.
  let LLsub : IntermediateField ↥K.L Ω := IntermediateField.extendScalars hKL
  haveI hLLfin : FiniteDimensional ↥K.L LLsub := by
    haveI : Module.Finite ℚ ↥LLsub := L.finite
    exact Module.Finite.of_restrictScalars_finite ℚ ↥K.L ↥LLsub
  haveI hLLnorm : Normal ↥K.L LLsub := by
    letI : Algebra ℚ ↥LLsub := IntermediateField.algebra' (R' := ℚ) LLsub
    have hNQ : Normal ℚ ↥LLsub := L.normal
    exact Normal.tower_top_of_normal (F := ℚ) (K := ↥K.L) (E := ↥LLsub) (h := hNQ)
  haveI hLLnf : NumberField ↥LLsub := inferInstanceAs (NumberField ↥L.L)
  -- The compositum `N · L.L`, as a level over `K.L`.
  let M : IntermediateField ↥K.L Ω := N ⊔ LLsub
  haveI hMfin : FiniteDimensional ↥K.L M := IntermediateField.finiteDimensional_sup N LLsub
  haveI hMnorm : Normal ↥K.L M := IntermediateField.normal_sup ↥K.L Ω N LLsub
  haveI hMnf : NumberField ↥M := Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  haveI hMgal : IsGalois ↥K.L M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- The same level, viewed over `L.L` (this is the level at which `hσ` is applied).
  let M' : IntermediateField ↥L.L Ω :=
    Subfield.toIntermediateField M.toSubfield fun x =>
      le_sup_right (a := N) (b := LLsub) (show (algebraMap ↥L.L Ω x) ∈ LLsub from x.2)
  haveI hM'nf : NumberField ↥M' := inferInstanceAs (NumberField ↥M)
  -- The scalar tower `K.L → L.L → M'`.
  have hst : IsScalarTower ↥K.L ↥L.L ↥M' := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply ↥K.L ↥L.L Ω x
  haveI : IsScalarTower ↥K.L ↥L.L ↥M' := hst
  haveI hSTKMΩ : IsScalarTower ↥K.L ↥M' Ω := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    rfl
  haveI hM'fin : FiniteDimensional ↥L.L M' := by
    haveI : Module.Finite ↥K.L ↥M' := inferInstanceAs (Module.Finite ↥K.L ↥M)
    exact Module.Finite.of_restrictScalars_finite ↥K.L ↥L.L ↥M'
  haveI hM'norm : Normal ↥L.L M' := by
    have hNM : Normal ↥K.L ↥M' := inferInstanceAs (Normal ↥K.L ↥M)
    exact Normal.tower_top_of_normal (F := ↥K.L) (K := ↥L.L) (E := ↥M') (h := hNM)
  haveI hM'gal : IsGalois ↥K.L ↥M' := inferInstanceAs (IsGalois ↥K.L ↥M)
  -- Apply the hypothesis at this level.
  obtain ⟨P, hPover, hPfrob⟩ := hσ M'
  -- The `↥K.L`-algebra structure making `N` a subfield of `M'`.
  letI hAlgNM : Algebra ↥N ↥M' :=
    (IntermediateField.inclusion (show N ≤ M from le_sup_left)).toRingHom.toAlgebra
  haveI hSTNM : IsScalarTower ↥K.L ↥N ↥M' := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply ↥K.L ↥N Ω x
  haveI hSTNMΩ : IsScalarTower ↥N ↥M' Ω := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    rfl
  -- Base change of the Frobenius element from `L.L` to `K.L`.
  have hbase : IsFrobAt (K := ↥K.L) (L := ↥M') P
      ((AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) M' σ).restrictScalars ↥K.L) :=
    isFrobAt_of_isFrobAt_of_inertiaDeg_eq_one (K := ↥K.L) (L := ↥L.L) (M := ↥M') P
      (AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) M' σ)
      (by rw [← hPover.over, hdeg]) hPfrob
  -- The two forms of the base-changed restriction of `σ` to `M'` agree.
  have hρ : (AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) M' σ).restrictScalars ↥K.L
      = AlgEquiv.restrictNormalHom (F := ↥K.L) (K₁ := Ω) M' (σ.restrictScalars ↥K.L) := by
    ext x
    show (algebraMap ↥M' Ω) ((σ.restrictNormal ↥M') x)
        = (algebraMap ↥M' Ω) (((σ.restrictScalars ↥K.L).restrictNormal ↥M') x)
    rw [AlgEquiv.restrictNormal_commutes (χ := σ) (E := ↥M') x,
        AlgEquiv.restrictNormal_commutes (χ := σ.restrictScalars ↥K.L) (E := ↥M') x,
        AlgEquiv.restrictScalars_apply]
  -- Base change, in the form adapted to the restriction to `N`.
  have hbase' : IsFrobAt (K := ↥K.L) (L := ↥M') P
      (AlgEquiv.restrictNormalHom (F := ↥K.L) (K₁ := Ω) M' (σ.restrictScalars ↥K.L)) := by
    rw [← hρ]
    exact hbase
  -- Restrict from the compositum to `N`.
  have hres : IsFrobAt (K := ↥K.L) (L := ↥N) (P.under (NumberField.RingOfIntegers ↥N))
      (AlgEquiv.restrictNormalHom (F := ↥K.L) (K₁ := ↥M') N
        (AlgEquiv.restrictNormalHom (F := ↥K.L) (K₁ := Ω) M' (σ.restrictScalars ↥K.L))) :=
    IsFrobAtRestrictNormalHomType (K := ↥K.L) (E := ↥N) (M := ↥M') P
      (AlgEquiv.restrictNormalHom (F := ↥K.L) (K₁ := Ω) M' (σ.restrictScalars ↥K.L)) hbase'
  refine ⟨P.under (NumberField.RingOfIntegers ↥N), ?_, ?_⟩
  · refine Ideal.LiesOver.mk ?_
    show Ideal.under (𝓞 ↥K.L) 𝔭.asIdeal
      = Ideal.under (𝓞 ↥K.L) (Ideal.under (𝓞 ↥N) P.asIdeal)
    rw [Ideal.under_under (A := 𝓞 ↥K.L) (B := 𝓞 ↥N) P.asIdeal,
        hPover.over, Ideal.under_under (A := 𝓞 ↥K.L) (B := 𝓞 ↥L.L) P.asIdeal]
  · rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (F := ↥K.L) ↥N ↥M' (K₃ := Ω)
      (σ.restrictScalars ↥K.L)]
    exact hres

end NK.Reconstruct
