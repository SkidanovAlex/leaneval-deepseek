import Mathlib
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
import Submission.Work.SSGRoute.H9.swTwoPlacePairingTwo
import Submission.Work.SSGRoute.H9.oPairAt_swapTwo
import Submission.Work.SSGRoute.H9.lPinnedFrobValue_eq
import Submission.Work.SSGRoute.H9.swPinnedFrob_exists
import Submission.Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia
import Submission.Work.SSGRoute.H9.crossed_two_place_p2
import Submission.Work.SSGRoute.NodeS35.swPinFamily
import Submission.Work.SSGRoute.NodeS35.swPinBasic
import Submission.Work.SSGRoute.NodeS35.kills_inertia_conjUnit
import Submission.Work.SSGRoute.NodeS35.isUnramifiedIn_sup_hLevel
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness
import Submission.Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count
import Submission.Work.SSGRoute.NodeS35.swHchainBasic
import Submission.Work.SSGRoute.NodeS37.oddCountAtEscape
import Submission.Work.SSGRoute.NodeS37.evenCountOfKillsInertia
import Submission.Work.SSGRoute.NodeS37.countSiblingOddNoTame
import Submission.Work.SSGRoute.NodeS37.value_eq_of_pinned
import Submission.Work.SSGRoute.NodeS37.oPairAt_smul_conj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup.OddForm

open scoped Pointwise

/-! ## Reduction of the value at an `L`-pinned Frobenius element

The hypotheses of the target `hker_*` make the Kummer cochain constant on the fibres of the
restriction `res k L` on the local group; combined with the fact that the restriction of an
`L`-pinned element generates the cyclic `L`-decomposition group, the *vanishing* of the cochain at
the pinned element is equivalent to its vanishing on the whole local group.  This is the step which
turns the two `L`-pinned values of the target into `0/1`-valued statements about the vanishing of
`χ_bs`, resp. `χ_bt`, on the two local groups. -/

/-- **Vanishing at an `L`-pinned element is vanishing on the local group.** -/
theorem value_eq_zero_iff_localGroup_zero {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α : (↥K)ˣ)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭)
    (hunrL : ¬ SSGRoute.IsRamifiedIn k L A)
    (hker : ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      SSGRoute.res k L u = 1 → Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α u = 0)
    (gt : Ω ≃ₐ[k] Ω) (hgt : gt ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (SSGRoute.res k L gt)) :
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α gt = 0) ↔
      (∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α u = 0) := by
  constructor
  · intro h0 u hu
    have hpram : (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers k) = 1 :=
      Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn k Ω L A hA hunrL
    have hmap : (SSGRoute.decomp k A).map (SSGRoute.res k L) =
        Subgroup.zpowers (SSGRoute.res k L gt) :=
      Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime k Ω L A hA 𝔭 h𝔭 hpram gt
        (Subgroup.mem_inf.mp hgt).1 hfrob
    have hmem : SSGRoute.res k L u ∈ (SSGRoute.decomp k A).map (SSGRoute.res k L) :=
      Subgroup.mem_map.mpr ⟨u, (Subgroup.mem_inf.mp hu).1, rfl⟩
    rw [hmap] at hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hzadd := Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ α
    have hval := Work.SSGRoute.ZSplit.localValue_eq_zsmul_of_res_eq_zpow K L A
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α) hzadd gt hgt u hu m hm.symm hker
    rw [hval, h0]
    simp
  · intro h
    exact h gt hgt

/-! ## Two bookkeeping bricks

`confinementOfHunr` removes the escape-class qualifier from a
"vanishing off `T` and off the class of `Q`" hypothesis, using the `T`-clause and the
conjugation-invariance of the Kummer cochain.  `notGesKConjOfHnorm` is the contrapositive of the
parity brick `evenCountOfKillsInertia`: the normalisation at `B` forces an inertia element of `B`
with non-vanishing cochain, which cannot be transported to `A` when the cochain of `A` kills the
level-`L` kernel. -/

/-- The `conjUnit` of `galLift K τ` is the image of the unit under `τ`. -/
private lemma conjUnit_galLift_eq_map {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (τ : K ≃ₐ[k] K) (a : (↥K)ˣ) :
    Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K τ) a
      = Units.map τ.toRingEquiv.toMonoidHom a := by
  rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]
  rfl

/-- `τ` followed by `τ⁻¹` is the identity on `Kˣ`. -/
private lemma map_mul_map_inv {F K : Type} [Field F] [Field K] [Algebra F K] (τ : K ≃ₐ[F] K) (a : Kˣ) :
    Units.map τ.toRingEquiv.toMonoidHom (Units.map τ⁻¹.toRingEquiv.toMonoidHom a) = a := by
  ext
  simp [Units.coe_map, AlgEquiv.apply_symm_apply]

private lemma zmod_two_neg_eq_self (x : ZMod 2) : -x = x := by
  revert x
  decide

/-- **Confinement away from `T` and the class of `Q` is confinement away from the class of `Q`.** -/
theorem confinementOfHunr {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    (Q : ValuationSubring Ω) (T : Finset (ValuationSubring Ω))
    (hT : ∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A τ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0)
    (hunr : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → (¬ Work.SSGRoute.gesKConj K Q B) →
      ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (¬ Work.SSGRoute.gesKConj K Q B) →
      ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0 := by
  intro B hB hQ τ hτI
  by_cases hτK : τ ∈ K.fixingSubgroup
  · by_cases hTc : ∃ A ∈ T, Work.SSGRoute.gesKConj K A B
    · obtain ⟨A, hA, w, hwK, hwA⟩ := hTc
      have hmem : w⁻¹ * τ * w ∈ K.fixingSubgroup :=
        K.fixingSubgroup.mul_mem
          (K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hwK) hτK) hwK
      have hI : SSGRoute.IsInertia k A (w⁻¹ * τ * w) := by
        refine (SSGRoute.isInertia_conj A w (w⁻¹ * τ * w)).mp ?_
        rw [show w * (w⁻¹ * τ * w) * w⁻¹ = τ from by group, hwA]
        exact hτI
      have h0 := hT A hA (w⁻¹ * τ * w) hmem hI
      have hconj : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b (w⁻¹ * τ * w)
          = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ :=
        Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK b
          (K.fixingSubgroup.inv_mem hwK) τ
      exact hconj ▸ h0
    · exact hunr B hB (fun A hA hc => hTc ⟨A, hA, hc⟩) hQ τ hτK hτI
  · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem hτK

/-- **The normalisation at `B` forces `B` to be outside the `K`-class of `A`.** -/
theorem notGesKConjOfHnorm {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    (B A : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hnorm : ∃ x : (↥K)ˣ,
      B.valuation (algebraMap ↥K Ω (x : ↥K)) < 1 ∧
      (∀ y : ↥K, B.valuation (algebraMap ↥K Ω y) < 1 →
        B.valuation (algebraMap ↥K Ω y) ≤ B.valuation (algebraMap ↥K Ω (x : ↥K))) ∧
      (∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ
          = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ))
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (hker : ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      SSGRoute.res k L u = 1 → Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0)
    (hunrL : ¬ SSGRoute.IsRamifiedIn k L A) :
    ¬ Work.SSGRoute.gesKConj K B A := by
  intro hBA
  -- the count of `b` at the prime of `↥K` below `B` is odd
  have hodd : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))) :=
    oddCountAtEscape (K := K) ζ hζ hζK b B hB hnorm
  -- so some inertia element of `B` sees `b` as a non-square
  have hex : ∃ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u ∧
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u ≠ 0 := by
    by_contra h
    push_neg at h
    have hev : Even (FractionalIdeal.count ↥K
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (b : ↥K))) :=
      evenCountOfKillsInertia (K := K) ζ hζ hζK b B hB
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hB) h
    exact (Int.not_even_iff_odd.mpr hodd) hev
  obtain ⟨u, huK, huI, hune⟩ := hex
  obtain ⟨w, hwK, hwA⟩ := hBA
  -- transport to `A`
  have hvK : w * u * w⁻¹ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hwK huK) (K.fixingSubgroup.inv_mem hwK)
  have hvI : SSGRoute.IsInertia k A (w * u * w⁻¹) := by
    have h := (SSGRoute.isInertia_conj B w u).mpr huI
    rw [hwA] at h
    exact h
  have hvres : SSGRoute.res k L (w * u * w⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker L]
    by_contra hnot
    exact hunrL ⟨w * u * w⁻¹, hvI, hnot⟩
  have hv0 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b (w * u * w⁻¹) = 0 :=
    hker (w * u * w⁻¹) (Subgroup.mem_inf.mpr ⟨hvI.1, hvK⟩) hvres
  have hconj : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b (w * u * w⁻¹)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u :=
    Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK b hwK u
  exact hune (hconj ▸ hv0)

/-! ## The four-step chain

With `A_t := siblingPlace K σ Pt` and `A_s := siblingPlace K σ⁻¹ Ps`, and `a := (σ⁻¹)b_s`, the chain

    χ_{b_s}(ψ_t) = ⟨χ_{b_s}, χ_{σ b_t}⟩_{A_t}      (dictionary at `A_t`)
                = ⟨χ_a, χ_{b_t}⟩_{Pt}              (Galois invariance of the pairing)
                = −⟨χ_a, χ_{b_t}⟩_{A_s}            (two-place product formula at `(A_s, Pt)`)
                = χ_{b_t}(ψ_s)                     (dictionary at `A_s`)

gives the crossed identity at the two pinned elements. -/

section Chain

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

set_option maxHeartbeats 4000000 in
theorem crossedValueAtPinned [NumberField ↥K] [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (bs bt a : (↥K)ˣ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (Ps Pt : ValuationSubring Ω) (hPtfin : SSGRoute.IsFinPlace k Pt)
    (hPtsplit : SSGRoute.IsSplitIn k K Pt)
    (hAtfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt))
    (hAsfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps))
    (hPtAs : ¬ Work.SSGRoute.gesKConj K Pt (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps))
    (hconfα : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) B) →
      ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a τ = 0)
    (hconfβ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Pt B) →
      ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0)
    (hinfα : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a c = 0)
    (hnorm_t : ∃ x : (↥K)ˣ,
      Pt.valuation (algebraMap ↥K Ω (x : ↥K)) < 1 ∧
      (∀ y : ↥K, Pt.valuation (algebraMap ↥K Ω y) < 1 →
        Pt.valuation (algebraMap ↥K Ω y) ≤ Pt.valuation (algebraMap ↥K Ω (x : ↥K))) ∧
      (∀ τ ∈ SSGRoute.decomp k Pt ⊓ K.fixingSubgroup, SSGRoute.IsInertia k Pt τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ
          = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ))
    (ha : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) a = bs)
    (hcounta : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (a : ↥K))))
    (hkillbsAt : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs τ = 0)
    (hkillbtAs : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) a)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) a)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) a)]
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs)]
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt)]
    (ψt : Ω ≃ₐ[k] Ω)
    (hψt : ψt ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) ⊓ K.fixingSubgroup)
    (hpint : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := 2) bs)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψt, (Subgroup.mem_inf.mp hψt).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin))
    (ψs : Ω ≃ₐ[k] Ω)
    (hψs : ψs ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) ⊓ K.fixingSubgroup)
    (hpins : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (hLevel (Ω := Ω) (K := K) (p := 2) bt)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψs, (Subgroup.mem_inf.mp hψs).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin))
    :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψt
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs := by
  classical
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- the conjugate unit `σ b_t`
  set bsig : (↥K)ˣ := Units.map σ.toRingEquiv.toMonoidHom bt with hbsigdef
  -- instances for the `hLevel` of the conjugate of `a`
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) a)) := by
    rw [ha]; infer_instance
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) a)) := by
    rw [ha]; infer_instance
  haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2)
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) a)) := by
    rw [ha]; infer_instance
  -- the odd count of `σ b_t` at the prime below `A_t`
  have hcountβ : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bsig : ↥K))) := by
    rw [hbsigdef]
    exact countSiblingOddNoTame (K := K) ζ hζ hζK bt σ hσ Pt hPtfin hPtsplit
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hAtfin) hnorm_t
  -- step 1: the dictionary at `A_t`
  have hstep1 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bsig)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψt :=
    Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count (K := K) (k := k) (Ω := Ω)
      ζ hζ hζK bs bsig (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin ψt
      (Subgroup.mem_inf.mp hψt).2
      (Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (p := 2) ζ hζ hζK bs
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin hkillbsAt)
      hpint hcountβ
  -- step 2: Galois invariance of the pairing
  have hstep2 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bsig)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' Pt hPtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) := by
    have h := Work.SSGRoute.NodeS37.oPairAt_smul_conj (K := K) (k := k) (Ω := Ω)
      ζ hζ hζK a bt σ Pt hPtfin hAtfin
    rw [ha, conjUnit_galLift_eq_map, ← hbsigdef] at h
    exact h
  -- step 3: the two-place product formula at `(A_s, Pt)`
  have hstep3 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt)
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' Pt hPtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) = 0 :=
    Work.SSGRoute.H9.swTwoPlacePairingTwo (K := K) (k := k) (Ω := Ω) ζ hζ hζK a bt
      (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) Pt hAsfin hPtfin
      (fun h => hPtAs (Work.SSGRoute.H9.gesKConj_symm'' h)) hconfα hconfβ hinfα
  have hstep3' : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' Pt hPtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt)
      = - Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hstep3
  -- step 4: the transpose dictionary at `A_s`
  have hstep4 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs :=
    Work.SSGRoute.H9.oPairAt_swapTwo (K := K) (k := k) (Ω := Ω) ζ hζ hζK a bt
      (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin ψs
      (Subgroup.mem_inf.mp hψs).2 hkillbtAs hpins hcounta
  calc Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψt
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bsig) := hstep1.symm
    _ = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' Pt hPtfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) := hstep2
    _ = - Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ'
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt) := hstep3'
    _ = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs := by rw [hstep4]
    _ = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs := zmod_two_neg_eq_self _

end Chain

theorem crossedValue {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (bs bt : (↥K)ˣ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (Ps Pt : ValuationSubring Ω) (hPsfin : SSGRoute.IsFinPlace k Ps)
    (hPtfin : SSGRoute.IsFinPlace k Pt) (hPsPt : ¬ Work.SSGRoute.gesKConj K Ps Pt)
    (hPssplit : SSGRoute.IsSplitIn k K Ps) (hPtsplit : SSGRoute.IsSplitIn k K Pt)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTstab : ∀ A ∈ T, ∀ τ : Ω ≃ₐ[k] Ω, τ • A ∈ T)
    (hT_s : ∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A τ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs τ = 0)
    (hT_t : ∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A τ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0)
    (hunr_s : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → (¬ Work.SSGRoute.gesKConj K Ps B) →
      ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs τ = 0)
    (hunr_t : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → (¬ Work.SSGRoute.gesKConj K Pt B) →
      ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0)
    (hnorm_s : ∃ x : (↥K)ˣ,
      Ps.valuation (algebraMap ↥K Ω (x : ↥K)) < 1 ∧
      (∀ y : ↥K, Ps.valuation (algebraMap ↥K Ω y) < 1 →
        Ps.valuation (algebraMap ↥K Ω y) ≤ Ps.valuation (algebraMap ↥K Ω (x : ↥K))) ∧
      (∀ τ ∈ SSGRoute.decomp k Ps ⊓ K.fixingSubgroup, SSGRoute.IsInertia k Ps τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs τ
          = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ))
    (hnorm_t : ∃ x : (↥K)ˣ,
      Pt.valuation (algebraMap ↥K Ω (x : ↥K)) < 1 ∧
      (∀ y : ↥K, Pt.valuation (algebraMap ↥K Ω y) < 1 →
        Pt.valuation (algebraMap ↥K Ω y) ≤ Pt.valuation (algebraMap ↥K Ω (x : ↥K))) ∧
      (∀ τ ∈ SSGRoute.decomp k Pt ⊓ K.fixingSubgroup, SSGRoute.IsInertia k Pt τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ
          = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ))
    (hinf_s : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs c = 0)
    (hinf_t : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt c = 0)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (hker_ss : ∀ u ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) ⊓ K.fixingSubgroup,
      SSGRoute.res k L u = 1 → Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs u = 0)
    (hker_st : ∀ u ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) ⊓ K.fixingSubgroup,
      SSGRoute.res k L u = 1 → Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs u = 0)
    (hker_ts : ∀ u ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) ⊓ K.fixingSubgroup,
      SSGRoute.res k L u = 1 → Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt u = 0)
    (hker_tt : ∀ u ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) ⊓ K.fixingSubgroup,
      SSGRoute.res k L u = 1 → Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt u = 0)
    (gs gt : Ω ≃ₐ[k] Ω)
    (hgs : gs ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) ⊓ K.fixingSubgroup)
    (hgt : gt ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) ⊓ K.fixingSubgroup)
    (hunrLs : ¬ SSGRoute.IsRamifiedIn k L (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps))
    (hunrLt : ¬ SSGRoute.IsRamifiedIn k L (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt))
    (𝔭s 𝔭t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭s : (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps).comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭s)
    (h𝔭t : (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt).comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭t)
    (hfrobs : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭s (SSGRoute.res k L gs))
    (hfrobt : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭t (SSGRoute.res k L gt)) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs gt
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt gs := by
  classical
  haveI hNFK : NumberField ↥K := inferInstance
  haveI hSepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  -- the two sibling places are finite
  have hAtfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) :=
    (SSGRoute.isFinPlace_smul_iff Pt (Work.SSGRoute.ZDataMup.galLift K σ)).mpr hPtfin
  have hAsfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) :=
    (SSGRoute.isFinPlace_smul_iff Ps (Work.SSGRoute.ZDataMup.galLift K σ⁻¹)).mpr hPsfin
  -- the unconditional confinements
  have hconf_s : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Ps B) → ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs τ = 0 :=
    confinementOfHunr ζ hζ hζK bs Ps T hT_s hunr_s
  have hconf_t : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Pt B) → ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0 :=
    confinementOfHunr ζ hζ hζK bt Pt T hT_t hunr_t
  -- the two places are not `K`-conjugate: the crossed kernel hypotheses
  have hPsAt : ¬ Work.SSGRoute.gesKConj K Ps
      (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) :=
    notGesKConjOfHnorm ζ hζ hζK bs Ps (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hPsfin
      hnorm_s L hker_st hunrLt
  have hPtAs : ¬ Work.SSGRoute.gesKConj K Pt
      (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) :=
    notGesKConjOfHnorm ζ hζ hζK bt Pt (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hPtfin
      hnorm_t L hker_ts hunrLs
  -- the two classes kill the inertia of the sibling of the *other* escape prime
  have hkillbsAt : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs τ = 0 :=
    fun τ _ hI => hconf_s _ hAtfin hPsAt τ hI
  have hkillbtAs : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt τ = 0 :=
    fun τ _ hI => hconf_t _ hAsfin hPtAs τ hI
  -- the conjugate unit `a := (σ⁻¹) b_s`
  let cbs : (↥K)ˣ := Units.map (σ⁻¹).toRingEquiv.toMonoidHom bs
  -- the `hLevel` instances consumed by the two dictionaries
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) bs
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) bs
  haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) bs) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) bs
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) bt
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) bt
  haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) bt) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) bt
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) cbs) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) cbs
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) cbs) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) cbs
  haveI : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) cbs) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) cbs
  -- the two pinned Frobenius elements
  obtain ⟨⟨ψt, hψt⟩, hpint⟩ :=
    Work.SSGRoute.NodeS35.exists_pinned_at (K := K) (Ω := Ω)
      (M := hLevel (Ω := Ω) (K := K) (p := 2) bs)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) bs)
      (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin
      (Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (p := 2) ζ hζ hζK bs
        (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin hkillbsAt)
  obtain ⟨⟨ψs, hψs⟩, hpins⟩ :=
    Work.SSGRoute.NodeS35.exists_pinned_at (K := K) (Ω := Ω)
      (M := hLevel (Ω := Ω) (K := K) (p := 2) bt)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K)
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) bt)
      (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin
      (Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (p := 2) ζ hζ hζK bt
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin hkillbtAs)
  -- the values at the two `L`-pinned Frobenius elements
  have hgtval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs gt
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψt :=
    value_eq_of_pinned ζ hζ hζK bs L (Work.SSGRoute.ZDataMup.siblingPlace K σ Pt) hAtfin 𝔭t h𝔭t
      hunrLt hker_st hkillbsAt gt hgt hfrobt ψt hψt hpint
  have hgsval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt gs
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs :=
    value_eq_of_pinned ζ hζ hζK bt L (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin 𝔭s h𝔭s
      hunrLs hker_ts hkillbtAs gs hgs hfrobs ψs hψs hpins
  -- the data of the chain at the conjugate class
  have hconfα : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) B) →
      ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ cbs τ = 0 := by
    intro B hB hnc τ hI
    have h := Work.SSGRoute.NodeS35.kills_inertia_conjUnit (p := 2) ζ hζ hζK bs σ⁻¹ Ps
      (fun B hB hnc u _ hI => hconf_s B hB hnc u hI) B hB hnc τ
    by_cases hτK : τ ∈ K.fixingSubgroup
    · have h' := h hτK hI
      rw [conjUnit_galLift_eq_map] at h'
      exact h'
    · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem hτK
  have hinfα : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ cbs c = 0 := by
    intro c hc hc2
    have h := Work.SSGRoute.H9.CV2.hinf_conjUnit (K := K) ζ hζ hζK bs σ⁻¹ hinf_s c hc hc2
    exact h
  have ha : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) cbs = bs := by
    rw [conjUnit_galLift_eq_map]
    exact map_mul_map_inv σ bs
  have hσinv : σ⁻¹ ≠ 1 := fun h => hσ (inv_eq_one.mp h)
  have hcounta : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (cbs : ↥K))) :=
    countSiblingOddNoTame (K := K) ζ hζ hζK bs σ⁻¹ hσinv Ps hPsfin hPssplit
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K σ⁻¹ Ps) hAsfin)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hAsfin) hnorm_s
  -- the chain, and the two value comparisons
  have hchain : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψt
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψs :=
    crossedValueAtPinned (k := k) (Ω := Ω) (K := K) ζ hζ hζK bs bt cbs σ hσ Ps Pt hPtfin
      hPtsplit hAtfin hAsfin hPtAs hconfα hconf_t hinfα hnorm_t ha hcounta hkillbsAt
      hkillbtAs ψt hψt hpint ψs hψs hpins
  rw [hgtval, hgsval]
  exact hchain

end Work.SSGRoute.NodeS37
