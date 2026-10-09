import Mathlib
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
import Submission.Work.SSGRoute.NodeS37.oddCountAtEscape
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

theorem countSiblingOddNoTame {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (bt : (↥K)ˣ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (Pt : ValuationSubring Ω) (hPtfin : SSGRoute.IsFinPlace k Pt)
    (hPtsplit : SSGRoute.IsSplitIn k K Pt)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔮 : (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt).comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮)
    (hnorm_t : ∃ x : (↥K)ˣ,
      Pt.valuation (algebraMap ↥K Ω (x : ↥K)) < 1 ∧
      (∀ y : ↥K, Pt.valuation (algebraMap ↥K Ω y) < 1 →
        Pt.valuation (algebraMap ↥K Ω y) ≤ Pt.valuation (algebraMap ↥K Ω (x : ↥K))) ∧
      (∀ τ ∈ SSGRoute.decomp k Pt ⊓ K.fixingSubgroup, SSGRoute.IsInertia k Pt τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ
          = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ)) :
    Odd (FractionalIdeal.count ↥K 𝔮
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((Units.map σ.toRingEquiv.toMonoidHom bt : (↥K)ˣ) : ↥K))) := by
  classical
  -- `Ω` is a separable closure of the number field `↥K`, needed for the place/prime vocabulary.
  haveI hSepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  -- Step 1: `bt` has odd `𝔭`-adic count at the prime `𝔭` of `↥K` below `Pt`.  This is
  -- `oddCountAtEscape` at the place `Pt`: the normalisation condition (1) forces `χ_b = -χ_x` on
  -- the inertia, hence `χ_{b·x⁻¹}` kills it, and the *tame-free* Kummer criterion makes
  -- `v_Pt(b·x⁻¹)` a square, so the count of `b·x⁻¹` is even while that of the uniformiser `x`
  -- is odd.  No tameness hypothesis is needed.
  have hoddbt : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Pt hPtfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bt : ↥K))) :=
    oddCountAtEscape (k := k) (Ω := Ω) (K := K) ζ hζ hζK bt Pt hPtfin hnorm_t
  -- Step 2: transport the count from `𝔭` (at `Pt`) to the sibling prime `𝔮` (at `galLift K σ • Pt`).
  have hPtsibfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) :=
    (Work.SSGRoute.isFinPlace_smul_iff Pt (Work.SSGRoute.ZDataMup.galLift K σ)).mpr hPtfin
  have hbridge : Work.SSGRoute.H9.conjUnit (K := K) (Work.SSGRoute.ZDataMup.galLift K σ) bt
      = Units.map σ.toRingEquiv.toMonoidHom bt := by
    rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]
    rfl
  have hconj := Work.SSGRoute.H9.swCount_conjUnit (K := K) bt σ Pt hPtfin hPtsibfin
  have hprime : Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
      (Work.SSGRoute.ZDataMup.galLift K σ • Pt) hPtsibfin = 𝔮 :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      ((Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hPtsibfin).symm.trans h𝔮)
  have hcount : FractionalIdeal.count ↥K 𝔮
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((Units.map σ.toRingEquiv.toMonoidHom bt : (↥K)ˣ) : ↥K)) =
      FractionalIdeal.count ↥K
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Pt hPtfin)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (bt : ↥K)) := by
    rw [← hprime, ← hbridge]
    exact hconj
  rw [hcount]
  exact hoddbt

end Work.SSGRoute.NodeS37
