import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.swCount_conjUnit
import Submission.Work.SSGRoute.ZDataTwo.InertiaCriterion
import Submission.Work.SSGRoute.ZDataTwo.TotallyPositive
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness
import Submission.Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Helper lemmas of the `p = 2` crossed two-place value identity (clean copy)

These are the *proved* helper lemmas of the decomposed proof of
`Work.SSGRoute.H9.swCrossedValueTwo` (the `p = 2` crossed two-place value identity of
Schmidt--Wingberg §4, p. 17, in its corrected form carrying the archimedean/total-positivity
hypotheses `hinf_s`, `hinf_t`); see `Submission/Work/SSGRoute/H9/swCrossedValueTwo.lean` for the
statement and for the record of the correction.

They are re-namespaced to `Work.SSGRoute.H9.CV2` so that a consumer can use them **without**
importing the module that carries the still-`sorry` statement (importing it would make the target
closable by the imported `sorry`, which the axiom check rejects, and which the reviewers of the
re-stated target flagged).  The two declarations of the original module that were *not* proved
(`swCountSibling_odd`, whose proof route is recorded in the original file, and the target itself)
are deliberately omitted, so this module is `sorry`-free.
-/

namespace Work.SSGRoute.H9.CV2


open _root_.SSGRoute
open Work.SSGRoute.ZDataMup
open Work.SSGRoute.ZDataMup.OddForm
open Work.SSGRoute.ZDataMup.LTRecFamHonest

set_option maxHeartbeats 800000

/-- **The dictionary of the crossed two-place chain, with the count normalisation (`p = 2`).**
At a finite place `A` at which the Kummer level `K(α^{1/2})` is unramified and at which the
`β`-count is *odd* (exactly the `hnorm_*` normalisation of the target, transported to the sibling
place), the local pairing of the two Kummer cochains equals the *value* of `χ_α` at any Frobenius
element `ψ` pinned to the canonical Frobenius of `A`:

    oPairAt_A (χ_α) (χ_β) = χ_α ψ.

This is the `count ≡ 1` refinement of `swPairingValueFrob`; it is the step which turns
Schmidt--Wingberg's condition (1) into the equalities of the §4 chain. -/
lemma oPairAt_eq_value_of_odd_count {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ K.fixingSubgroup)
    [FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) α)]
    (hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := 2) α))
      (oddPrime (K := K) A hA))
    (hpinning : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := 2) α)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, hψ⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := 2) α))
        (oddPrime (K := K) A hA))
    (hcount : Odd (FractionalIdeal.count ↥K (oddPrime (K := K) A hA)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (β : ↥K)))) :
    oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) (ζ := (⟨ζ, hζK⟩ : ↥K))
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α ψ := by
  rw [swPairingValueFrob (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) A hA α β ψ hψ hunr hpinning]
  have hc : (FractionalIdeal.count ↥K (oddPrime (K := K) A hA)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (β : ↥K)) : ZMod 2) = 1 := by
    obtain ⟨m, hm⟩ := hcount
    rw [hm]
    push_cast
    rw [show ((2 : ZMod 2) * (m : ZMod 2) + 1) = 1 by
      rw [show ((2 : ZMod 2)) = 0 by decide, zero_mul, zero_add]]
  rw [zsmul_eq_mul, hc, one_mul]

/-- **Well-definedness of a Kummer cochain on a local group through a finite level `L`.**
If the level-`K` Kummer cochain `χ_b = nodeKummerCocharZMod K ζ hζK hζ b` kills the kernel of the
restriction to a finite normal level `L` on a subgroup `H ≤ G_K`, then `χ_b|_H` depends only on
`res k L`.  This is the step that makes the two Frobenius values in the crossed two-place identity
well defined from `res k L (g_*)` (the `hker_*` hypotheses of the target). -/
lemma nodeKummerCocharZMod_eq_of_res_eq {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {L : IntermediateField k Ω} [Normal k L]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hHK : H ≤ K.fixingSubgroup)
    (hker : ∀ u ∈ H, _root_.SSGRoute.res k L u = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0)
    {u v : Ω ≃ₐ[k] Ω} (hu : u ∈ H) (hv : v ∈ H)
    (hres : _root_.SSGRoute.res k L u = _root_.SSGRoute.res k L v) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b v := by
  have huv : u * v⁻¹ ∈ H := H.mul_mem hu (H.inv_mem hv)
  have hres1 : _root_.SSGRoute.res k L (u * v⁻¹) = 1 := by
    rw [map_mul, map_inv, hres, mul_inv_cancel]
  have h0 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b (u * v⁻¹) = 0 :=
    hker _ huv hres1
  have hadd := Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b (u * v⁻¹)
    (hHK huv) v (hHK hv)
  rw [mul_assoc, inv_mul_cancel, mul_one, h0, zero_add] at hadd
  exact hadd

/-- The Galois (`σ`-twist) equivariance of the level-`K` Kummer cochains at `p = 2`, in the
`conjUnit` form of `Work.SSGRoute.H9.swConjElemZero`: the Kummer cochain of the conjugate class is
the conjugate of the Kummer cochain.  At `p = 2` the cyclotomic character is trivial, so the
zero-set equivalence of `swConjElemZero` upgrades to an equality of `ZMod 2`-valued cochains. -/
lemma nodeKummerCocharZMod_conjUnit {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (b : (↥K)ˣ) (σ : K ≃ₐ[k] K) :
    ∀ x : Ω ≃ₐ[k] Ω,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (conjUnit (K := K) (Work.SSGRoute.ZDataMup.galLift K σ) b) x
        = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b
            ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * x * (Work.SSGRoute.ZDataMup.galLift K σ)) := by
  intro x
  have h := swConjElemZero (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) b (Work.SSGRoute.ZDataMup.galLift K σ) x
  revert h
  generalize Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
    (conjUnit (K := K) (Work.SSGRoute.ZDataMup.galLift K σ) b) x = A
  generalize Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b
    ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * x * (Work.SSGRoute.ZDataMup.galLift K σ)) = B
  intro h
  rcases eq_or_ne A 0 with h0 | h0
  · rw [h0, h.mp h0]
  · have hB : B ≠ 0 := fun hB => h0 (h.mpr hB)
    have hA1 : A = 1 := by fin_cases A; exact absurd rfl h0; rfl
    have hB1 : B = 1 := by fin_cases B; exact absurd rfl hB; rfl
    rw [hA1, hB1]

/-- **The Galois (`σ`-twist) equivariance of the level-`K` Kummer cochains at `p = 2`**, in the
`σ : K ≃ₐ[k] K` form used by the crossed two-place chain: the Kummer cochain of the conjugate
element `σ b` is the conjugate of the Kummer cochain of `b`. -/
lemma swKummerCocharZMod_conj_equiv {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (b : (↥K)ˣ) (σ : K ≃ₐ[k] K) :
    ∀ x : Ω ≃ₐ[k] Ω,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Units.map σ.toRingEquiv.toMonoidHom b) x
        = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b
            ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * x * (Work.SSGRoute.ZDataMup.galLift K σ)) := by
  intro x
  have h := nodeKummerCocharZMod_conjUnit (K := K) ζ hζ hζK b σ x
  have hbridge : conjUnit (K := K) (Work.SSGRoute.ZDataMup.galLift K σ) b = Units.map σ.toRingEquiv.toMonoidHom b := by
    rw [conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]
    rfl
  rwa [hbridge] at h

/-- **The two `p = 2` Kummer characters agree.**  The `kummerSqrt`-based `Work.SSGRoute.kummerChar`
and the `kummerSqrtUnitZMod`-based `Work.SSGRoute.kummerCharZMod` are both the Kummer index of the
chosen square root, and `kummerIdx_congr` makes the choice of root irrelevant.  This is the inline
step `hchar_eq` of `Work.SSGRoute.local_kummer_dictionary_two`, extracted so that the
ZMod-language tools (`nodeKummerCocharZMod`) and the `kummerSqrt`-language tools
(`kills_inertia_iff_even_valuation`) can be used together at `p = 2`. -/
lemma kummerChar_eq_kummerCharZMod_two {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (ζ : K) (hζ : IsPrimitiveRoot ζ 2) (a : Kˣ) :
    ∀ σ : Ω ≃ₐ[K] Ω,
      Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ a σ =
        Work.SSGRoute.kummerCharZMod (Ω := Ω) 2 (ζ := ζ) hζ a σ := by
  intro σ
  show Work.SSGRoute.kummerIdx 2 hζ a (Work.SSGRoute.kummerSqrt (Ω := Ω) a)
      (Work.SSGRoute.kummerSqrt_pow (Ω := Ω) a) σ =
    Work.SSGRoute.kummerIdx 2 hζ a (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) 2 a)
      (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) 2 a) σ
  exact Work.SSGRoute.kummerIdx_congr 2 hζ a _ _ σ

/-- **The `p = 2` cochain bridge, at the level of the two global cochains (`K` a subfield of `Ω`).**
`Work.SSGRoute.nodeKummerCochar` (built from `kummerCochar`, the `kummerSqrt`-based character) and
`Work.SSGRoute.ZSplit.nodeKummerCocharZMod` (built from `kummerCharZMod`) coincide; off
`K.fixingSubgroup` both are `0`, and on it this is
`kummerChar_eq_kummerCharZMod_two`.  This is what lets the `kummerSqrt`-side criterion
`kills_inertia_iff_even_valuation` be applied to hypotheses stated with the `ZMod` cochain. -/
lemma nodeKummerCochar_eq_nodeKummerCocharZMod_two {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (b : (↥K)ˣ) :
    ∀ σ : Ω ≃ₐ[k] Ω,
      nodeKummerCochar K ζ hζK hζ b σ = ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ := by
  intro σ
  by_cases hσ : σ ∈ K.fixingSubgroup
  · simp only [nodeKummerCochar, kummerCochar, dif_pos hσ,
      ZSplit.nodeKummerCocharZMod, dif_pos hσ]
    rw [show Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
        = isPrimitiveRoot_subtype_of_mem hζK hζ from Subsingleton.elim _ _]
    exact kummerChar_eq_kummerCharZMod_two (K := ↥K) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K)
      (isPrimitiveRoot_subtype_of_mem hζK hζ) b
      ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩)
  · simp only [nodeKummerCochar, kummerCochar, dif_neg hσ,
      ZSplit.nodeKummerCocharZMod, dif_neg hσ]

/-- **The `𝔭`-adic valuation of a number field is surjective onto `ℤ` (the generator of the value
group is attained in `K`).**  For a height-one prime `𝔭` of `𝓞 K` there is `y ∈ Kˣ` with
`count_𝔭 (y) = 1`; equivalently `(𝔭.valuation K (y:K)).log = -1`.  This is the elementary
Dedekind-domain fact behind every "the count of the maximal-below-`1` element is odd" argument: it is
the two-line corollary of Mathlib's `valuation_exists_uniformizer` and
`Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log`. -/
lemma exists_count_eq_one {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ y : Kˣ, FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (y : K)) = 1 := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K 𝔭
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 π hπ0, ?_⟩
  rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log 𝔭
      (Units.ne_zero (Units.mk0 π hπ0)),
    Units.val_mk0, hπ, WithZero.log_exp]
  ring

/-- **Step 1 of the count-transport: `χ_{b·x⁻¹}` kills the inertia of `P_t`.**  If on the inertia of
`Pt` the cochain of `b` is the negative of the cochain of `x` (`hnorm_*`), then the cochain of
`b·x⁻¹` vanishes there: in `ZMod 2` the minus sign is invisible, so both summands are equal and
`a + a = 0`. -/
lemma chi_mul_inv_kills_inertia {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (bt x : (↥K)ˣ) (Pt : ValuationSubring Ω)
    (hchar : ∀ τ ∈ _root_.SSGRoute.decomp k Pt ⊓ K.fixingSubgroup,
      _root_.SSGRoute.IsInertia k Pt τ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ
        = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ) :
    ∀ τ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k Pt τ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (bt * x⁻¹) τ = 0 := by
  intro τ hτK hτI
  rw [Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK bt x⁻¹,
    Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_inv K ζ hζ hζK x]
  simp only [Pi.add_apply, Pi.neg_apply]
  have hmem : τ ∈ _root_.SSGRoute.decomp k Pt ⊓ K.fixingSubgroup :=
    Subgroup.mem_inf.mpr ⟨hτI.1, hτK⟩
  rw [hchar τ hmem hτI]
  have h2 : (-(Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ))
      + (-(Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ)) = 0 := by
    rw [← neg_add]
    have h22 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ
        = (2 : ZMod 2) * Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ := by
      ring
    rw [h22, show (2 : ZMod 2) = 0 by decide, zero_mul, neg_zero]
  exact h2

/-- **Step 2 of the count-transport: the valuation of `b·x⁻¹` at `P_t` is a square.**  Step 1
gives that the cochain of `b·x⁻¹` kills the inertia of `Pt`; reading that vanishing in the
`kummerSqrt` language through the `p = 2` cochain bridge, the even-valuation criterion
`kills_inertia_iff_even_valuation` (valid because `Pt ∤ 2`) yields a witness `d` with
`v_{Pt}(b·x⁻¹) = v_{Pt}(d)²`, i.e. `v_{Pt}(b·x⁻¹)` is even. -/
lemma exists_sq_val_mul_inv {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (bt x : (↥K)ˣ) (Pt : ValuationSubring Ω) (hPtfin : _root_.SSGRoute.IsFinPlace k Pt)
    (hPt2 : ¬ Pt.valuation (2 : Ω) < 1)
    (hkill : ∀ τ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k Pt τ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (bt * x⁻¹) τ = 0) :
    ∃ d : (↥K)ˣ, Pt.valuation (algebraMap ↥K Ω ((bt * x⁻¹ : (↥K)ˣ) : ↥K))
      = (Pt.valuation (algebraMap ↥K Ω (d : ↥K))) ^ 2 := by
  refine (Work.SSGRoute.ZDataTwo.kills_inertia_iff_even_valuation k Ω K ζ hζ hζK
    (bt * x⁻¹) Pt hPtfin hPt2).mp ?_
  intro σ hσK hσI
  rw [nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK (bt * x⁻¹) σ]
  exact hkill σ hσK hσI

/-- **`Valuation.IsEquiv` is an order isomorphism of the value groups.**  An equivalence of
valuations (same valuation ring) preserves the *elementwise* order, not only the comparison with `1`:
`v x ≤ v y ↔ w x ≤ w y`.  This is Mathlib's `Valuation.IsEquiv` unfolded (it is stated as
`∀ x y, v x ≤ v y ↔ w x ≤ w y`), recorded here under the name used by the count-transport so that
the maximality clause of `hnorm_*` can be read on the prime valuation where
`count_spanSingleton_eq_neg_log` lives. -/
lemma valuation_isEquiv_le_iff_le {R : Type*} [Ring R]
    {Γ₀ Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']
    {v : Valuation R Γ₀} {w : Valuation R Γ₀'} (h : Valuation.IsEquiv v w) (x y : R) :
    v x ≤ v y ↔ w x ≤ w y :=
  h x y

/-- **The valuation subring of a pulled-back valuation is the pullback of the valuation subring.**
For a place `W` of `L` and `K ⊆ L`, the valuation of `Valuation.comap W.valuation (algebraMap K L)`
has valuation subring `W.comap (algebraMap K L)`.  This is the compatibility that turns the
comap-equation of the count-transport into a `Valuation.IsEquiv` of the place and prime valuations.
(Note the API: `ValuationSubring.valuation.comp` consumes a `→*₀`, which `algebraMap` does not
coerce to in this toolchain, so the pullback is taken through `Valuation.comap`, which consumes a
`→+*`.) -/
lemma valuationSubring_comap_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ValuationSubring L) :
    (W.valuation.comap (algebraMap K L)).valuationSubring
      = W.comap (algebraMap K L) := by
  ext z
  show W.valuation ((algebraMap K L) z) ≤ 1 ↔ ((algebraMap K L) z) ∈ W
  rw [ValuationSubring.valuation_le_one_iff]

/-- **Step 3 of the count-transport: the maximal-below-`1` element has odd count.**  If `x ∈ Kˣ` has
`𝔭`-adic value `< 1` and is *maximal* with that property (the `hnorm_*` normalisation read on the
prime valuation, i.e. `x` is a uniformiser at `𝔭`), then its `𝔭`-adic count is odd.  Squeeze:
`exists_count_eq_one` supplies a uniformiser `y` with `(𝔭.valuation (y:↥K)).log = -1`
(`count_spanSingleton_eq_neg_log`), hence `v_𝔭(y) < 1`; maximality gives `v_𝔭(y) ≤ v_𝔭(x)`, i.e.
`log(v_𝔭 x) ≥ -1`; and `v_𝔭(x) < 1` gives `log(v_𝔭 x) ≤ -1`.  So `log(v_𝔭 x) = -1` and
`count_𝔭 x = 1`.  (The caller transfers the place-language `hnorm_*` data to the prime language with
`valuation_lt_one_algebraMap_iff` and `valuation_isEquiv_le_iff_le`.) -/
lemma odd_count_of_maximal_lt_one {K : Type} [Field K] [NumberField K]
    (x : Kˣ) (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hxlt : 𝔭.valuation K (x : K) < 1)
    (hxmax : ∀ y : K, 𝔭.valuation K y < 1 → 𝔭.valuation K y ≤ 𝔭.valuation K (x : K)) :
    Odd (FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (x : K))) := by
  have hxne : (x : K) ≠ 0 := Units.ne_zero x
  have hvx : 𝔭.valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hxne
  obtain ⟨y, hy⟩ := exists_count_eq_one (K := K) 𝔭
  have hyne : ((y : Kˣ) : K) ≠ 0 := Units.ne_zero y
  have hvy : 𝔭.valuation K ((y : Kˣ) : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hyne
  -- the uniformiser's log is `-1`
  have hylog : (𝔭.valuation K ((y : Kˣ) : K)).log = -1 := by
    have h := hy
    rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := K) 𝔭 hyne] at h
    omega
  have hylt : 𝔭.valuation K ((y : Kˣ) : K) < 1 := by
    have h : (𝔭.valuation K ((y : Kˣ) : K)).log < (0 : ℤ) := by omega
    have h' : WithZero.exp ((𝔭.valuation K ((y : Kˣ) : K)).log) < WithZero.exp (0 : ℤ) :=
      WithZero.exp_lt_exp.mpr h
    rwa [WithZero.exp_log hvy, WithZero.exp_zero] at h'
  -- maximality, and the squeeze
  have hle : 𝔭.valuation K ((y : Kˣ) : K) ≤ 𝔭.valuation K (x : K) := hxmax _ hylt
  have hlog_ge : (-1 : ℤ) ≤ (𝔭.valuation K (x : K)).log := by
    rw [← hylog]
    exact (WithZero.log_le_log hvy hvx).mpr hle
  have hxlog_lt : (𝔭.valuation K (x : K)).log < (0 : ℤ) := by
    have h' : WithZero.exp ((𝔭.valuation K (x : K)).log) < WithZero.exp (0 : ℤ) := by
      rwa [WithZero.exp_log hvx, WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mp h'
  have hlog : (𝔭.valuation K (x : K)).log = -1 := by omega
  have hcount : FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (x : K)) = 1 := by
    rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := K) 𝔭 hxne, hlog]
    norm_num
  exact ⟨0, by rw [hcount]; norm_num⟩

/-- **Step 4(a) of the count-transport: the count of `b·x⁻¹` is even.**  Step 2 produces a *place*
witness `v_{Pt}(b·x⁻¹) = (v_{Pt} d)²`; contraposing the converse criterion
`Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count` (which turns an odd count into the
nonexistence of such a witness) gives evenness of the `𝔭`-adic count — no place↔prime transfer
needed, since the criterion is stated on the place valuation. -/
lemma even_count_mul_inv_of_sq_val {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (bt x : (↥K)ˣ) (Pt : ValuationSubring Ω) (hPtfin : _root_.SSGRoute.IsFinPlace k Pt)
    (hPtne : Pt.comap (algebraMap ↥K Ω) ≠ ⊤)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : Pt.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hsq : ∃ d : (↥K)ˣ, Pt.valuation (algebraMap ↥K Ω ((bt * x⁻¹ : (↥K)ˣ) : ↥K))
      = (Pt.valuation (algebraMap ↥K Ω (d : ↥K))) ^ 2) :
    Even (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((bt * x⁻¹ : (↥K)ˣ) : ↥K))) := by
  by_contra hnot
  have hodd : Odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((bt * x⁻¹ : (↥K)ˣ) : ↥K))) := by
    rcases Int.even_or_odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((bt * x⁻¹ : (↥K)ˣ) : ↥K))) with h | h
    · exact absurd h hnot
    · exact h
  exact (Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count ↥K Ω Pt hPtne 𝔭 h𝔭
    (bt * x⁻¹) hodd) hsq

/-- **Step 4(b) of the count-transport: oddness of the count of `b` from the even/odd split.**
`b = (b·x⁻¹)·x`, so the `𝔭`-adic counts add (`FractionalIdeal.count_mul`); even + odd = odd. -/
lemma odd_count_of_even_count_mul_inv {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (bt x : Kˣ)
    (heven : Even (FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (((bt * x⁻¹ : Kˣ) : K)))))
    (hodd : Odd (FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (x : K)))) :
    Odd (FractionalIdeal.count K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (bt : K))) := by
  have hval : (bt : K) = (((bt * x⁻¹ : Kˣ) : K)) * (x : K) := by
    rw [← Units.val_mul]
    congr 1
    group
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
      (((bt * x⁻¹ : Kˣ) : K)) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff]; exact Units.ne_zero _
  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
      (x : K) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff]; exact Units.ne_zero _
  rw [hval, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K 𝔭 h1 h2]
  rcases heven with ⟨k, hk⟩
  rcases hodd with ⟨m, hm⟩
  exact ⟨k + m, by rw [hk, hm]; ring⟩


/-- **The `σ`-transport of the escape normalisation at `p = 2`.**  If `bt` is uniformised at `Pt`
(the paper's condition (1) at the escape prime, in the `hnorm_t` form) and `Pt ∤ 2`, then the
conjugate element `σ bt` has odd `𝔮`-adic count at the prime `𝔮` below the sibling place
`siblingPlace K σ Pt` — the step that makes the local symbol `(b_s, σb_t)_{σP_t}` of the `p = 2`
chain to be `χ_{b_s}` at a Frobenius.  (A copy of `Work.SSGRoute.ZDataTwo.swCountSiblingOdd`,
re-pointed to the helpers of this module so that it can be used *without* importing the module that
carries the refuted first form of the crossed value identity.) -/
lemma swCountSibling_odd {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (bt : (↥K)ˣ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (Pt : ValuationSubring Ω) (hPtfin : SSGRoute.IsFinPlace k Pt)
    (hPtsplit : SSGRoute.IsSplitIn k K Pt)
    (hPt2 : ¬ Pt.valuation (2 : Ω) < 1)
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
  -- `Ω` is a separable closure of `↥K`, needed for the place/prime vocabulary below.
  have hSepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  obtain ⟨x, hxlt, hxmax, hchar⟩ := hnorm_t
  -- the prime of `↥K` below `Pt`
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Pt hPtfin
  have hspec : Pt.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hPtfin
  have hptne : Pt.comap (algebraMap ↥K Ω) ≠ ⊤ :=
    Work.SSGRoute.ZDataMup.OddForm.oddFinPlace (K := K) hPtfin
  -- the two valuations on `↥K` (the trace of `Pt` and the prime valuation at `𝔭`) are equivalent
  have heq : (Pt.valuation.comap (algebraMap ↥K Ω)).IsEquiv (𝔭.valuation ↥K) := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    rw [Work.SSGRoute.H9.CV2.valuationSubring_comap_algebraMap Pt, hspec,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  -- step 1: `χ_{bt·x⁻¹}` kills the inertia of `Pt`
  have hkill : ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k Pt τ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (bt * x⁻¹) τ = 0 :=
    Work.SSGRoute.H9.CV2.chi_mul_inv_kills_inertia (K := K) ζ hζ hζK bt x Pt hchar
  -- step 2: the `Pt`-value of `bt·x⁻¹` is a square
  have hsq : ∃ d : (↥K)ˣ, Pt.valuation (algebraMap ↥K Ω ((bt * x⁻¹ : (↥K)ˣ) : ↥K)) =
      (Pt.valuation (algebraMap ↥K Ω (d : ↥K))) ^ 2 :=
    Work.SSGRoute.H9.CV2.exists_sq_val_mul_inv (K := K) ζ hζ hζK bt x Pt hPtfin hPt2 hkill
  -- step 3: hence the `𝔭`-count of `bt·x⁻¹` is even
  have heven : Even (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((bt * x⁻¹ : (↥K)ˣ) : ↥K))) :=
    Work.SSGRoute.H9.CV2.even_count_mul_inv_of_sq_val (K := K) bt x Pt hPtfin hptne 𝔭 hspec hsq
  -- step 4: `x` is a uniformiser at `𝔭`, so its `𝔭`-count is odd
  have hxlt' : (𝔭.valuation ↥K) (x : ↥K) < 1 :=
    (Valuation.IsEquiv.lt_one_iff_lt_one heq).mp (by simpa using hxlt)
  have hxmax' : ∀ y : ↥K, (𝔭.valuation ↥K) y < 1 →
      (𝔭.valuation ↥K) y ≤ (𝔭.valuation ↥K) (x : ↥K) := by
    intro y hy
    rw [← Work.SSGRoute.H9.CV2.valuation_isEquiv_le_iff_le heq]
    exact hxmax y ((Valuation.IsEquiv.lt_one_iff_lt_one heq).mpr hy)
  have hoddx : Odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (x : ↥K))) :=
    Work.SSGRoute.H9.CV2.odd_count_of_maximal_lt_one x 𝔭 hxlt' hxmax'
  -- step 5: even + odd = odd
  have hoddbt : Odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bt : ↥K))) :=
    Work.SSGRoute.H9.CV2.odd_count_of_even_count_mul_inv 𝔭 bt x heven hoddx
  -- step 6: transport the count from `𝔭` to the sibling prime `𝔮`
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
      FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bt : ↥K)) := by
    rw [← hprime, ← hbridge]
    exact hconj
  rw [hcount]
  exact hoddbt


/-! ## The `σ`-transport lemmas (usable in both orientations)

The three lemmas below are the transports of the involution and confinement hypotheses along the
`σ`-twist (`χ_{σ b}(x) = χ_b(galLift K σ⁻¹ · x · galLift K σ)`), with the marked place moved along
`siblingPlace K σ`.  They are consumed by *both* orientations of the crossed two-place value
identity (in either orientation one of the two dictionary steps pairs the *conjugate* of one class
with the other), and they were proved while attacking the (wrong) forward-`σ` orientation — see
`H9/NOTE_swCrossedValueTwoFixed_verdict.md` §5. -/

/-- **`G_k`-conjugates of elements of the fixing subgroup lie in the fixing subgroup** (normality of
`K.fixingSubgroup` in `G_k`), in the raw form used below. -/
lemma galLift_inv_conj_mem_fixingSubgroup {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ρ : Ω ≃ₐ[k] Ω) {u : Ω ≃ₐ[k] Ω} (hu : u ∈ K.fixingSubgroup) :
    ρ⁻¹ * u * ρ ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hu ⊢
  intro x hx
  have hmem : ρ x ∈ K := by
    have h := Work.SSGRoute.algebraMap_restrictNormalHom (K := K) ρ ⟨x, hx⟩
    rw [show ρ x = ((AlgEquiv.restrictNormalHom K ρ ⟨x, hx⟩ : ↥K) : Ω) from h.symm]
    exact (AlgEquiv.restrictNormalHom K ρ ⟨x, hx⟩).2
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu _ hmem]
  exact AlgEquiv.symm_apply_apply ρ x

/-- **The involution hypothesis is preserved by the `σ`-twist.**  If the Kummer cochain of `b`
kills every involution of `G_K`, then so does the cochain of the conjugate class
`σ b = Units.map σ.toRingEquiv.toMonoidHom b`; this is what lets the `p = 2` two-place product
formula be applied to the pair `(σ b_s, b_t)`. -/
lemma hinf_conjUnit {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (σ : K ≃ₐ[k] K)
    (hinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b c = 0) :
    ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
        (Units.map σ.toRingEquiv.toMonoidHom b) c = 0 := by
  intro c hc hc2
  rw [swKummerCocharZMod_conj_equiv (K := K) ζ hζ hζK b σ c]
  refine hinf _ (galLift_inv_conj_mem_fixingSubgroup (K := K)
    (Work.SSGRoute.ZDataMup.galLift K σ) hc) ?_
  have h2 : ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * c * (Work.SSGRoute.ZDataMup.galLift K σ))
      ^ 2 = 1 := by
    have hmid : ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * c * (Work.SSGRoute.ZDataMup.galLift K σ))
        * ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * c * (Work.SSGRoute.ZDataMup.galLift K σ))
        = (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * (c * c)
          * (Work.SSGRoute.ZDataMup.galLift K σ) := by group
    rw [pow_two, hmid]
    have hc2' : c * c = 1 := by rw [← sq, hc2]
    rw [hc2', mul_one, inv_mul_cancel]
  exact h2

/-- **The confinement hypothesis is preserved by the `σ`-twist, with the marked place moved along.**
If the Kummer cochain of `b` kills the inertia at every finite place which is not
`G_K`-conjugate to `Q`, then the cochain of `σ b` kills the inertia at every finite place which is
not `G_K`-conjugate to the sibling `siblingPlace K σ Q`. -/
lemma hconf_conjUnit {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (σ : K ≃ₐ[k] K) (Q : ValuationSubring Ω)
    (hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Q B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K σ Q) B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Units.map σ.toRingEquiv.toMonoidHom b) u = 0 := by
  intro B hB hnc u hI
  rw [swKummerCocharZMod_conj_equiv (K := K) ζ hζ hζK b σ u]
  refine hconf ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ • B) ?_ ?_ _ ?_
  · exact (Work.SSGRoute.isFinPlace_smul_iff (k := k) B
      (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹).mpr hB
  · intro hconj
    refine hnc ?_
    have h := (Work.SSGRoute.H9.swGesKConj_galLift_smul_iff (K := K) σ Q B).mpr hconj
    simpa only [Work.SSGRoute.ZDataMup.siblingPlace] using h
  · exact (Work.SSGRoute.isInertia_conj (k := k) B (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ u).mpr hI


end Work.SSGRoute.H9.CV2
