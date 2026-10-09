import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.ArchKummer
import Submission.Work.SSGRoute.ZDataTwo.ArithCore
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.NK.ResidueFrob.primeOfLevel_liesOver
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Work.SSGRoute.ZDataTwo.odd_log_of_not_sq_val
import Submission.Work.SSGRoute.ZDataTwo.two_dvd_ramificationIdx_of_odd_valuation
import Submission.Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The arithmetic core of clause (D) of the `p = 2` Kummer node

`Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq` is the *converse* of the inertia
dictionary `Work.SSGRoute.kummerCochar_eq_zero_of_isInertia_of_even_valuation`: if the
`A`-valuation of `b ∈ Kˣ` is not the square of the `A`-valuation of any element of `Kˣ`, then the
Kummer cochain of `b` does *not* vanish on the whole inertia subgroup of `A`: some inertia element
of `A` lying in `Gal(Ω/K)` sees `b` as a non-square.

Equivalently (by the local Kummer dichotomy at the prime `𝔭` of `K` below `A`), the Kummer
extension `K(√b)/K` is ramified at `𝔭`, and tameness (`A ∤ 2`, hypothesis `h2`) makes the inertia
of the ramified quadratic extension act non-trivially on `√b`.

The arithmetic content is the implication "odd valuation ⟹ ramified", carried by the two auxiliary
lemmas imported above:

* `odd_log_of_not_sq_val` — the hypothesis `hodd` (phrased with the value group of `A`) is
  equivalent to the oddness of the `𝔭`-adic valuation of `b` (a `ℤ`-exponent, `WithZero.log`);
* `two_dvd_ramificationIdx_of_odd_valuation` — the extension `L = K⟮√b⟯` has even ramification
  index at every prime over `𝔭` (from `β ^ 2 = b` and `(valuation of β) ^ 2 = valuation of b ^ e`).

The rest is Galois bookkeeping: an even ramification index makes the inertia subgroup of the finite
level `L/↥K` non-trivial (`inertia_eq_bot_iff_ramificationIdx_eq_one`), the place inertia of the
infinite extension surjects onto it (`inertiaSub_image_eq_levelInertia`), and a place inertia
element that does not fix `L` moves `√b`, i.e. is not killed by the Kummer cochain
(`Work.SSGRoute.kummerChar_eq_zero_iff_apply_sqrt`).
-/

open scoped Pointwise NumberField IntermediateField

namespace Work.SSGRoute.ZDataTwo

theorem kummerCochar_ne_zero_of_val_not_sq
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hodd : ¬ ∃ d : (↥K)ˣ,
      A.valuation (algebraMap ↥K Ω (b : ↥K)) =
        A.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2) :
    ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup ∧ SSGRoute.IsInertia k A σ ∧
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ ≠ 0 := by
  haveI : NumberField ↥K := Commons.NumberTheory.NumberField.numberField_of_intermediateField K
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSep : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- `A` is a finite place over `↥K`
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := NK.Reconstruct.comap_level_ne_top hA K
  -- the chosen square root of `b` in `Ω`
  set β : Ω := Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b with hβdef
  have hβ : β ^ 2 = algebraMap ↥K Ω (b : ↥K) :=
    Work.SSGRoute.kummerSqrtVal_pow (K := ↥K) (Ω := Ω) b
  -- `b` is not a square in `↥K`
  have hbnsq : b ∉ NK.LocalAnabelian.powSubgroup 2 ↥K := by
    intro hb
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hb
    refine hodd ⟨d, ?_⟩
    have hdv : (d : ↥K) ^ 2 = (b : ↥K) := by
      rw [← hd]
      simp
    rw [← hdv, map_pow, Valuation.map_pow]
  -- the primitive root of unity in `↥K`
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 := isPrimitiveRoot_subtype_of_mem hζK hζ
  -- the Kummer field `L = ↥K⟮β⟯`
  set L : IntermediateField ↥K Ω := NK.LocalAnabelian.kummerField (K' := Ω) 2 b with hLdef
  have hgalL : IsGalois ↥K ↥L :=
    (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) 2 Nat.prime_two
      hζ' b hbnsq).1
  haveI : FiniteDimensional ↥K L :=
    NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (K' := Ω) (k := ↥K)
      (p := 2) Nat.prime_two hζ' b
  haveI : IsGalois ↥K ↥L := hgalL
  haveI : Normal ↥K ↥L := hgalL.to_normal
  haveI : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  have hLβ : L = (↥K)⟮β⟯ :=
    NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple 2 Nat.prime_two hζ' b hβ
  have hβL : β ∈ L := by
    rw [hLβ]
    exact IntermediateField.mem_adjoin_simple_self ↥K β
  -- the prime `𝔭` of `↥K` below `A`, and the prime `P` of `↥L` below `A`
  have h𝔭spec : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
        (Submission.NeukirchUchida.primeOf A hAK) :=
    Submission.NeukirchUchida.primeOf_spec A hAK
  set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) :=
    NK.Reconstruct.primeOfLevel A L (NK.Reconstruct.comap_level_ne_top hAK L) with hPdef
  have hLies : P.asIdeal.LiesOver (Submission.NeukirchUchida.primeOf A hAK).asIdeal :=
    NK.ResidueFrob.primeOfLevel_liesOver (K := ↥K) (K' := Ω) ⟨A, hAK⟩ L
  -- the oddness of the valuation of `b`
  have hoddn : Odd (-((Submission.NeukirchUchida.primeOf A hAK).valuation ↥K (b : ↥K)).log) :=
    odd_log_of_not_sq_val ↥K Ω A hAK (Submission.NeukirchUchida.primeOf A hAK) h𝔭spec b hodd
  -- `2` divides the ramification index
  have hβLpow : (⟨β, hβL⟩ : ↥L) ^ 2 = algebraMap ↥K ↥L (b : ↥K) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    change β ^ 2 = (algebraMap ↥K Ω) (b : ↥K)
    exact hβ
  have h2dvd : 2 ∣ P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) := by
    haveI : P.asIdeal.LiesOver (Submission.NeukirchUchida.primeOf A hAK).asIdeal := hLies
    exact two_dvd_ramificationIdx_of_odd_valuation ↥K ↥L b ⟨β, hβL⟩ hβLpow
      (Submission.NeukirchUchida.primeOf A hAK) P hoddn
  -- the level inertia at `P` is non-trivial
  have hinertia_ne : Ideal.inertia (↥L ≃ₐ[↥K] ↥L) P.asIdeal ≠ ⊥ := by
    intro hbot
    haveI : P.asIdeal.LiesOver (Submission.NeukirchUchida.primeOf A hAK).asIdeal := hLies
    have he1 : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) = 1 :=
      (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
        (Submission.NeukirchUchida.primeOf A hAK).asIdeal P.asIdeal).mp hbot
    rw [he1] at h2dvd
    norm_num at h2dvd
  -- a non-trivial element of the level inertia, lifted to the place inertia over `↥K`
  obtain ⟨τ, hτmem, hτne⟩ :
      ∃ τ : ↥L ≃ₐ[↥K] ↥L, τ ∈ Ideal.inertia (↥L ≃ₐ[↥K] ↥L) P.asIdeal ∧ τ ≠ 1 := by
    by_contra h
    apply hinertia_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have hmap := Work.SSGRoute.inertiaSub_image_eq_levelInertia ↥K Ω A hAK L
  have hτmem' : τ ∈ (Work.SSGRoute.inertiaSub ↥K Ω A).map (AlgEquiv.restrictNormalHom L) := by
    rw [hmap]
    exact hτmem
  obtain ⟨σ', hσ'mem, hσ'res⟩ := Subgroup.mem_map.mp hτmem'
  have hσ'notfix : σ' ∉ L.fixingSubgroup := by
    intro hfix
    have h1 : AlgEquiv.restrictNormalHom L σ' = 1 := by
      rw [show AlgEquiv.restrictNormalHom L σ' = σ'.restrictNormal ↥L from rfl,
        AlgEquiv.restrictNormal_eq_one_iff]
      exact fun x hx => (IntermediateField.mem_fixingSubgroup_iff L σ').mp hfix x hx
    rw [hσ'res] at h1
    exact hτne h1
  have hσ'β : σ' β ≠ β := by
    intro h
    have : σ' ∈ L.fixingSubgroup := by
      rw [hLβ]
      exact mem_fixingSubgroup_adjoin_simple β σ' h
    exact hσ'notfix this
  -- the transfer to `k`-algebra automorphisms
  have hσK : (σ'.restrictScalars k) ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ'.commutes (⟨x, hx⟩ : ↥K)
  have hsmul : (σ'.restrictScalars k) • A = σ' • A := by
    apply SetLike.coe_injective
    ext x
    simp only [ValuationSubring.coe_pointwise_smul, Set.mem_smul_set]
    constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩
  have hInertia : SSGRoute.IsInertia k A (σ'.restrictScalars k) := by
    obtain ⟨hσ'D, hσ'v⟩ := (Work.SSGRoute.mem_inertiaSub ↥K Ω A σ').mp hσ'mem
    refine ⟨?_, hσ'v⟩
    rw [MulAction.mem_stabilizer_iff] at hσ'D ⊢
    rw [hsmul, hσ'D]
  have hcoch : Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b (σ'.restrictScalars k) ≠ 0 := by
    intro hzero
    rw [Work.SSGRoute.nodeKummerCochar, Work.SSGRoute.kummerCochar_apply _ _ _ _ hσK] at hzero
    have heq : (((K.fixingSubgroupEquiv) ⟨σ'.restrictScalars k, hσK⟩) : Ω ≃ₐ[↥K] Ω) = σ' := by
      ext x
      rfl
    rw [heq] at hzero
    have h := (Work.SSGRoute.kummerChar_eq_zero_iff_apply_sqrt (K := ↥K) (Ω := Ω)
      ⟨ζ, hζK⟩ hζ' b σ').mp hzero
    exact hσ'β (by simpa only [hβdef, Work.SSGRoute.kummerSqrt, Units.val_mk0] using h)
  exact ⟨σ'.restrictScalars k, hσK, hInertia, hcoch⟩

end Work.SSGRoute.ZDataTwo
