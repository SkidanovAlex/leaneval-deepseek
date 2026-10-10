import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.crossTwoChainCore
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.not_gesKConj_swap_sibling
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup
open Work.SSGRoute.ZDataMup.OddForm

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-! ## Two bookkeeping lemmas for the `conjUnit` of a chosen lift -/

/-- The `conjUnit` of `galLift K τ` is the image of the unit under `τ`.  (A local copy of the
private helper of `NodeS37/crossedValue.lean`.) -/
private lemma conjUnit_galLift_eq_map {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (τ : K ≃ₐ[k] K) (x : (↥K)ˣ) :
    Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) x
      = Units.map τ.toRingEquiv.toMonoidHom x := by
  rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]
  rfl

/-- `τ` followed by `τ⁻¹` is the identity on `Kˣ`. -/
private lemma map_mul_map_inv {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (τ : K ≃ₐ[k] K) (x : (↥K)ˣ) :
    Units.map τ.toRingEquiv.toMonoidHom (Units.map τ⁻¹.toRingEquiv.toMonoidHom x) = x := by
  ext
  simp [Units.coe_map, AlgEquiv.apply_symm_apply]

theorem pinValue_cross_two {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (Qs Qt : ValuationSubring Ω) (hQsfin : SSGRoute.IsFinPlace k Qs)
    (hQtfin : SSGRoute.IsFinPlace k Qt) (bs bt : (↥K)ˣ)
    (hsep : ∀ σ : K ≃ₐ[k] K, σ ≠ 1 →
      ¬ Work.SSGRoute.gesKConj K Qs (Work.SSGRoute.ZDataMup.galLift K σ • Qt))
    (hconfs : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Qs B) →
      ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs u = 0)
    (hconft : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Qt B) →
      ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt u = 0)
    (hcounts : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qs hQsfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bs : ↥K))))
    (hcountt : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Qt hQtfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bt : ↥K))))
    (hinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs c = 0) :
    ∀ σ : K ≃ₐ[k] K,
      Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => (Qt, bs)) (fun _ => hQtfin) 0 σ
        = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => (Qs, bt)) (fun _ => hQsfin) 0 σ⁻¹ := by
  intro σ
  by_cases hσ1 : σ = 1
  · -- the trivial index: both pinned values are `0` by definition
    rw [hσ1, inv_one]
    simp only [Work.SSGRoute.NodeS35.pinValue, dif_pos]
  · have hσinv : σ⁻¹ ≠ 1 := fun h => hσ1 (inv_eq_one.mp h)
    have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
      Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
    -- the two sibling places are finite
    have hAtfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ Qt) :=
      (Work.SSGRoute.isFinPlace_smul_iff (k := k) Qt
        (Work.SSGRoute.ZDataMup.galLift K σ)).mpr hQtfin
    have hAsfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Qs) :=
      (Work.SSGRoute.isFinPlace_smul_iff (k := k) Qs
        (Work.SSGRoute.ZDataMup.galLift K σ⁻¹)).mpr hQsfin
    -- `χ_{b_s}` kills the inertia at the sibling of `Q_t` (hypothesis `hsep` at `σ`)
    have hkillbsAt : ∀ τ ∈ K.fixingSubgroup,
        SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K σ Qt) τ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs τ = 0 :=
      fun τ hτ hI =>
        hconfs (Work.SSGRoute.ZDataMup.siblingPlace K σ Qt) hAtfin (hsep σ hσ1) τ hτ hI
    -- `Q_t` is not `K`-conjugate to the sibling of `Q_s` (the `σ⁻¹`-translate of `hsep σ`)
    have hPtAs : ¬ Work.SSGRoute.gesKConj K Qt (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Qs) :=
      not_gesKConj_swap_sibling (K := K) Qs Qt σ (hsep σ hσ1)
    have hkillbtAs : ∀ τ ∈ K.fixingSubgroup,
        SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Qs) τ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0 :=
      fun τ hτ hI =>
        hconft (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Qs) hAsfin hPtAs τ hτ hI
    -- the three Kummer levels
    haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs) :=
      hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bs
    haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs) :=
      hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bs
    haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs) :=
      hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bs
    haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt) :=
      hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bt
    haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt) :=
      hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bt
    haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt) :=
      hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bt
    -- the two pinned Frobenius elements
    obtain ⟨⟨ψt, hψt⟩, hpint⟩ :=
      Work.SSGRoute.NodeS35.exists_pinned_at (K := K) (Ω := Ω)
        (M := hLevel (Ω := Ω) (K := K) (p := 2) bs)
        (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bs)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Qt) hAtfin
        (Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (p := 2) ζ hζ hζK bs
          (Work.SSGRoute.ZDataMup.siblingPlace K σ Qt) hAtfin hkillbsAt)
    obtain ⟨⟨ψs, hψs⟩, hpins⟩ :=
      Work.SSGRoute.NodeS35.exists_pinned_at (K := K) (Ω := Ω)
        (M := hLevel (Ω := Ω) (K := K) (p := 2) bt)
        (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' bt)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Qs) hAsfin
        (Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (p := 2) ζ hζ hζK bt
          (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Qs) hAsfin hkillbtAs)
    -- the conjugate class `a = b_s^{σ⁻¹}`, whose Kummer cochain is `χ_{b_s} ∘ conj (σ⁻¹)`
    set a : (↥K)ˣ := Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ⁻¹) bs
      with hadef
    haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) a) :=
      hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' a
    haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) a) :=
      hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' a
    haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) a) :=
      hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' a
    -- `a` is the `σ`-conjugate of `b_s`: `conjUnit (galLift K σ) a = b_s`
    have ha : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) a = bs := by
      rw [hadef, conjUnit_galLift_eq_map (K := K) σ⁻¹ bs,
        conjUnit_galLift_eq_map (K := K) σ (Units.map (σ⁻¹).toRingEquiv.toMonoidHom bs)]
      exact map_mul_map_inv (K := K) σ bs
    -- confinement of the conjugate class (the `σ⁻¹`-transport of `hconfs`)
    have hconfα : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Qs) B) →
        ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a τ = 0 := by
      intro B hB hnc τ hI
      by_cases hτK : τ ∈ K.fixingSubgroup
      · have h := Work.SSGRoute.NodeS35.kills_inertia_conjUnit (p := 2) ζ hζ hζK bs σ⁻¹ Qs
          hconfs B hB hnc τ hτK hI
        rw [hadef]
        exact h
      · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem hτK
    have hconfβ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (¬ Work.SSGRoute.gesKConj K Qt B) →
        ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0 := by
      intro B hB hnc τ hI
      by_cases hτK : τ ∈ K.fixingSubgroup
      · exact hconft B hB hnc τ hτK hI
      · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem hτK
    -- the involutions still kill the conjugate class (the `σ⁻¹`-transport of `hinf`)
    have hinfα : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a c = 0 := by
      intro c hc hc2
      rw [hadef, conjUnit_galLift_eq_map (K := K) σ⁻¹ bs]
      exact Work.SSGRoute.H9.CV2.hinf_conjUnit (K := K) ζ hζ hζK bs σ⁻¹ hinf c hc hc2
    -- the escape normalisation at the two sibling primes
    have hcounta : Odd (FractionalIdeal.count ↥K
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Qs) hAsfin)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (a : ↥K))) := by
      simp only [Work.SSGRoute.ZDataMup.siblingPlace]
      rw [hadef]
      rw [Work.SSGRoute.H9.swCount_conjUnit (K := K) bs σ⁻¹ Qs hQsfin hAsfin]
      exact hcounts
    have hcountβ : Odd (FractionalIdeal.count ↥K
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.siblingPlace K σ Qt) hAtfin)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((Units.map σ.toRingEquiv.toMonoidHom bt : (↥K)ˣ) : ↥K))) := by
      simp only [Work.SSGRoute.ZDataMup.siblingPlace]
      rw [← conjUnit_galLift_eq_map (K := K) σ bt]
      rw [Work.SSGRoute.H9.swCount_conjUnit (K := K) bt σ Qt hQtfin hAtfin]
      exact hcountt
    -- the four-step crossed two-place chain at the two pinned elements
    have hchain := crossTwoChainCore (K := K) ζ hζ hζK bs bt a σ hσ1 Qs Qt hQtfin hAtfin hAsfin
      hPtAs hconfα hconfβ hinfα ha hcounta hcountβ hkillbsAt hkillbtAs
      ψt hψt hpint ψs hψs hpins
    -- the values at the pinned elements are the pinned values of the two families
    have hvalT : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψt
        = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
            (fun _ => (Qt, bs)) (fun _ => hQtfin) 0 σ :=
      Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK
        (fun _ => (Qt, bs)) (fun _ => hQtfin) 0 σ hσ1 ψt hψt hpint
    have hvalS : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs
        = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
            (fun _ => (Qs, bt)) (fun _ => hQsfin) 0 σ⁻¹ :=
      Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK
        (fun _ => (Qs, bt)) (fun _ => hQsfin) 0 σ⁻¹ hσinv ψs hψs hpins
    rw [← hvalT, ← hvalS]
    exact hchain

end Work.SSGRoute.ZDataTwo.TwoRec
