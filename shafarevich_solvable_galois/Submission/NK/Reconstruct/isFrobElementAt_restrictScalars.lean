import Mathlib
import Submission.NK.Reconstruct.splitFrobeniusBase
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.Chebotarev.GalRestrictCompat
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.NK.Reconstruct.NumFieldIn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField


open NK.Chebotarev
open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **Restriction of a Frobenius element to a smaller base field, at a completely split prime.**
Let `K ⊆ L` be finite Galois number-field levels of `Ω/ℚ`, `𝔭` a prime of `L` which is completely
split over `ℚ` (`NK.Reconstruct.SplitsCompletelyOverRat 𝔭`), and `σ ∈ Gal(Ω/L)` which is a
Frobenius element at `𝔭` over the base field `L` at every finite normal level over `L`
(`NK.Reconstruct.IsFrobElementAt 𝔭 σ`).  Then `σ|_K ∈ Gal(Ω/K)` is a Frobenius element at
`𝔭 ∩ K` over the base field `K`.

This is the point of Proposition 4f.3 of Shimizu, arXiv:2009.10431 that fails without the splitting
hypothesis (the inclusion `G_L ↪ G_K` carries `Frob_𝔭` to `Frob_{𝔭|K}^{f}`; README §19.8 records the
counterexample `ℚ ⊆ ℚ(i)`, `𝔭 = (3)`). -/
theorem isFrobElementAt_restrictScalars {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (K : NK.Reconstruct.NumFieldIn ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω) (hKL : K.L ≤ L.L)
    [Algebra ↥K.L ↥L.L] [IsScalarTower ↥K.L ↥L.L Ω]
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (hsplit : NK.Reconstruct.SplitsCompletelyOverRat 𝔭)
    (σ : Gal(Ω/↥L.L)) (hσ : NK.Reconstruct.IsFrobElementAt 𝔭 σ) :
    NK.Reconstruct.IsFrobElementAt (𝔭.under (𝓞 ↥K.L)) (σ.restrictScalars ↥K.L) := by
  rw [NK.Reconstruct.IsFrobElementAt]
  intro N hNfin hNnorm hNnf
  -- ## The compositum `N·L`, viewed as a finite normal level over `L`
  let E : IntermediateField ℚ Ω := N.restrictScalars ℚ ⊔ L.L
  have hLE : L.L ≤ E := le_sup_right
  let ML : IntermediateField ↥L.L Ω := IntermediateField.extendScalars hLE
  haveI hNfinQ : FiniteDimensional ℚ ↥(N.restrictScalars ℚ) := by
    have h1 : FiniteDimensional ℚ ↥N := FiniteDimensional.trans ℚ ↥K.L ↥N
    exact h1
  haveI hLfinQ : FiniteDimensional ℚ ↥L.L := L.finite
  haveI hEfinQ : FiniteDimensional ℚ ↥E := inferInstance
  haveI hMLfin : FiniteDimensional ↥L.L ↥ML := by
    haveI : Module.Finite ℚ ↥ML := hEfinQ
    exact Module.Finite.of_restrictScalars_finite ℚ ↥L.L ↥ML
  haveI hLnf : NumberField ↥L.L := L.numberField
  haveI hMLnf : NumberField ↥ML :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥L.L) (K' := Ω) ML
  have hNML : (N : Set Ω) ⊆ (ML : Set Ω) := by
    intro x hx
    show x ∈ E
    exact SetLike.le_def.mp le_sup_left (by simpa using hx)
  let f : ↥N →+* ↥ML := (algebraMap ↥N Ω).codRestrict ML (fun z => hNML z.2)
  letI hAlgN_ML : Algebra ↥N ↥ML := f.toAlgebra
  have hfield : ∀ y : ↥N, ((algebraMap ↥N ↥ML y : ↥ML) : Ω) = (y : Ω) := by
    intro y
    rw [show (algebraMap ↥N ↥ML y : ↥ML) = f y from rfl]
    exact RingHom.codRestrict_apply (algebraMap ↥N Ω) ML (fun z => hNML z.2) y
  have hf : f.comp (algebraMap ↥K.L ↥N) = algebraMap ↥K.L ↥ML := by
    ext x
    simp only [RingHom.comp_apply, RingHom.codRestrict_apply]
    rfl
  -- normality of `ML` over `↥L.L`
  have hML_adjoin : (ML : Set Ω) ⊆ (IntermediateField.adjoin ↥L.L (N : Set Ω) : Set Ω) := by
    have h1 : E ≤ (IntermediateField.adjoin ↥L.L (N : Set Ω)).restrictScalars ℚ := by
      refine sup_le ?_ ?_
      · intro x hx
        exact IntermediateField.subset_adjoin ↥L.L (N : Set Ω) hx
      · intro x hx
        simpa using IntermediateField.algebraMap_mem (IntermediateField.adjoin ↥L.L (N : Set Ω))
          (⟨x, hx⟩ : ↥L.L)
    intro x hx
    exact h1 hx
  haveI hMLnorm : Normal ↥L.L ML := by
    refine Normal.mk fun x => ?_
    have hx : (x : Ω) ∈ IntermediateField.adjoin ↥L.L (N : Set Ω) := hML_adjoin x.2
    have hkey : ∀ y ∈ (N : Set Ω), IsIntegral ↥L.L y ∧
        ((minpoly ↥L.L y).map (algebraMap ↥L.L ↥ML)).Splits := by
      intro y hy
      have hIntK : IsIntegral ↥K.L y :=
        IsIntegral.map N.val (IsIntegral.of_finite ↥K.L (⟨y, hy⟩ : ↥N))
      refine ⟨hIntK.tower_top, ?_⟩
      have hdvd : minpoly ↥L.L y ∣ (minpoly ↥K.L y).map (algebraMap ↥K.L ↥L.L) :=
        minpoly.dvd_map_of_isScalarTower ↥K.L ↥L.L y
      have hspl : ((minpoly ↥K.L y).map (algebraMap ↥K.L ↥ML)).Splits := by
        have h1 : ((minpoly ↥K.L (⟨y, hy⟩ : ↥N)).map (algebraMap ↥K.L ↥N)).Splits :=
          Normal.splits hNnorm ⟨y, hy⟩
        have h2 := h1.map f
        rw [Polynomial.map_map, hf] at h2
        rwa [IntermediateField.minpoly_eq (S := N) ⟨y, hy⟩] at h2
      have hdvd' : ((minpoly ↥L.L y).map (algebraMap ↥L.L ↥ML)) ∣
          ((minpoly ↥K.L y).map (algebraMap ↥K.L ↥ML)) := by
        have h := Polynomial.map_dvd (algebraMap ↥L.L ↥ML) hdvd
        rw [Polynomial.map_map] at h
        rwa [← IsScalarTower.algebraMap_eq ↥K.L ↥L.L ↥ML] at h
      exact Polynomial.Splits.of_dvd hspl (Polynomial.map_ne_zero (minpoly.ne_zero hIntK)) hdvd'
    have h3 := IntermediateField.splits_of_mem_adjoin ↥L.L Ω (L := ↥ML) (S := (N : Set Ω)) hkey hx
    rwa [← IntermediateField.minpoly_eq (S := ML) x] at h3
  -- ## Apply `hσ` at the level `ML`
  obtain ⟨P, hPover, hPfrob⟩ := hσ ML
  haveI hstK : IsScalarTower ↥K.L ↥N ↥ML := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    apply Subtype.ext
    rw [show ((algebraMap ↥N ↥ML) (algebraMap ↥K.L ↥N x) : ↥ML) = f (algebraMap ↥K.L ↥N x) from rfl]
    rw [RingHom.codRestrict_apply, ← hf]
    rfl
  letI hAlgROI : Algebra (𝓞 ↥N) (𝓞 ↥ML) :=
    (NumberField.RingOfIntegers.mapRingHom f).toAlgebra
  have hROI : ∀ y : 𝓞 ↥N, ((algebraMap (𝓞 ↥N) (𝓞 ↥ML) y : 𝓞 ↥ML) : Ω) = (y : Ω) := by
    intro y
    rw [show (algebraMap (𝓞 ↥N) (𝓞 ↥ML) y)
        = NumberField.RingOfIntegers.mapRingHom f y from rfl]
    rw [NumberField.RingOfIntegers.mapRingHom_apply]
    exact hfield (y : ↥N)
  refine ⟨P.under (𝓞 ↥N), ?_, ?_⟩
  · -- the prime lies over `𝔭 ∩ 𝓞 ↥K.L`
    refine ⟨?_⟩
    rw [show (P.under (𝓞 ↥N)).asIdeal = Ideal.under (𝓞 ↥N) P.asIdeal from rfl,
      show (𝔭.under (𝓞 ↥K.L)).asIdeal = Ideal.under (𝓞 ↥K.L) 𝔭.asIdeal from rfl]
    rw [Ideal.under_under, ← Ideal.under_under (A := 𝓞 ↥K.L) (B := 𝓞 ↥L.L) (C := 𝓞 ↥ML) P.asIdeal,
      hPover.over]
  · -- the Frobenius congruence
    intro x
    have hInertia : ((P.asIdeal.under (𝓞 ↥L.L)).under (𝓞 ↥K.L)).inertiaDeg (𝓞 ℚ) = 1 := by
      rw [← hPover.over]
      have ht := Ideal.inertiaDeg_tower (R := 𝓞 ℚ) (S := 𝓞 ↥K.L) (T := 𝓞 ↥L.L)
        (q := 𝔭.asIdeal.under (𝓞 ↥K.L)) (r := 𝔭.asIdeal)
      rw [hsplit.1] at ht
      exact (mul_eq_one.mp ht.symm).1
    have hexp : Nat.card (𝓞 ↥K.L ⧸ (P.asIdeal.under (𝓞 ↥N)).under (𝓞 ↥K.L))
        = Nat.card (𝓞 ↥L.L ⧸ P.asIdeal.under (𝓞 ↥L.L)) := by
      have h1 : (P.asIdeal.under (𝓞 ↥N)).under (𝓞 ↥K.L)
          = (P.asIdeal.under (𝓞 ↥L.L)).under (𝓞 ↥K.L) := by
        rw [Ideal.under_under,
          ← Ideal.under_under (A := 𝓞 ↥K.L) (B := 𝓞 ↥L.L) (C := 𝓞 ↥ML) P.asIdeal]
      rw [h1]
      have hk : Nat.card (𝓞 ↥K.L ⧸ (P.asIdeal.under (𝓞 ↥L.L)).under (𝓞 ↥K.L))
          = Nat.card (NumberField.RingOfIntegers ℚ ⧸
              ((P.asIdeal.under (𝓞 ↥L.L)).under (𝓞 ↥K.L)).under (NumberField.RingOfIntegers ℚ)) :=
        (natCard_quot_eq_of_inertiaDeg_eq_one (A := NumberField.RingOfIntegers ℚ) (B := 𝓞 ↥K.L)
          (q := (P.asIdeal.under (𝓞 ↥L.L)).under (𝓞 ↥K.L)) hInertia).symm
      have hl : Nat.card (𝓞 ↥L.L ⧸ P.asIdeal.under (𝓞 ↥L.L))
          = Nat.card (NumberField.RingOfIntegers ℚ ⧸
              (P.asIdeal.under (𝓞 ↥L.L)).under (NumberField.RingOfIntegers ℚ)) := by
        have : (P.asIdeal.under (𝓞 ↥L.L)).inertiaDeg (NumberField.RingOfIntegers ℚ) = 1 := by
          rw [← hPover.over]
          exact hsplit.1
        exact (natCard_quot_eq_of_inertiaDeg_eq_one (A := NumberField.RingOfIntegers ℚ)
          (B := 𝓞 ↥L.L) (q := P.asIdeal.under (𝓞 ↥L.L)) this).symm
      rw [hk, hl]
      congr 1
      rw [Ideal.under_under (A := NumberField.RingOfIntegers ℚ) (B := 𝓞 ↥K.L) (C := 𝓞 ↥L.L)]
    rw [show (P.under (𝓞 ↥N)).asIdeal = Ideal.under (𝓞 ↥N) P.asIdeal from rfl]
    rw [hexp, Ideal.mem_under]
    rw [map_sub, map_pow]
    -- compare with the Frobenius congruence at the level `ML`
    let v : 𝓞 ↥N := (galRestrict (𝓞 ↥K.L) ↥K.L ↥N (𝓞 ↥N))
      (AlgEquiv.restrictNormalHom N (σ.restrictScalars ↥K.L)) x
    let z : 𝓞 ↥ML := algebraMap (𝓞 ↥N) (𝓞 ↥ML) x
    have hz : (galRestrict (𝓞 ↥L.L) ↥L.L ↥ML (𝓞 ↥ML)) (AlgEquiv.restrictNormalHom ML σ) z
        - z ^ Nat.card (𝓞 ↥L.L ⧸ P.asIdeal.under (𝓞 ↥L.L)) ∈ P.asIdeal :=
      (isFrobAt_def P (AlgEquiv.restrictNormalHom ML σ)).mp hPfrob z
    have hLHS : ((algebraMap (𝓞 ↥N) (𝓞 ↥ML) v : 𝓞 ↥ML) : Ω) = (σ ((x : 𝓞 ↥N) : Ω)) := by
      rw [hROI v]
      rw [NumberField.RingOfIntegers.coe_eq_algebraMap, algebraMap_galRestrict_apply,
        AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictScalars_apply]
    have hRHS : (((galRestrict (𝓞 ↥L.L) ↥L.L ↥ML (𝓞 ↥ML)) (AlgEquiv.restrictNormalHom ML σ) z :
        𝓞 ↥ML) : Ω) = (σ ((x : 𝓞 ↥N) : Ω)) := by
      rw [NumberField.RingOfIntegers.coe_eq_algebraMap, algebraMap_galRestrict_apply,
        AlgEquiv.restrictNormalHom_apply]
      rw [show (z : 𝓞 ↥ML) = algebraMap (𝓞 ↥N) (𝓞 ↥ML) x from rfl]
      rw [← NumberField.RingOfIntegers.coe_eq_algebraMap, hROI x]
    have hA : algebraMap (𝓞 ↥N) (𝓞 ↥ML) v
        = (galRestrict (𝓞 ↥L.L) ↥L.L ↥ML (𝓞 ↥ML)) (AlgEquiv.restrictNormalHom ML σ) z :=
      NumberField.RingOfIntegers.ext (Subtype.ext (hLHS.trans hRHS.symm))
    convert hz using 1
    show algebraMap (𝓞 ↥N) (𝓞 ↥ML) v
        - (algebraMap (𝓞 ↥N) (𝓞 ↥ML) x) ^ Nat.card (𝓞 ↥L.L ⧸ P.asIdeal.under (𝓞 ↥L.L))
        = (galRestrict (𝓞 ↥L.L) ↥L.L ↥ML (𝓞 ↥ML)) (AlgEquiv.restrictNormalHom ML σ) z
          - z ^ Nat.card (𝓞 ↥L.L ⧸ P.asIdeal.under (𝓞 ↥L.L))
    rw [hA]

end NK.Reconstruct
