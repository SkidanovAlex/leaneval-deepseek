import Mathlib
import Submission.Work.SSGRoute.E1aClean.phiUnrU1
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.U2auxImports
import Submission.NeukirchUchida.Local.InfiniteDecomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (U2) of the lead's design `_lead_design/ssg_phiunr_1120`: Kummer at the henselian level

The main theorem is `henselUnit_pow_mul_localUnits_of_inertiaFixedRoot`.  The auxiliary lemmas
used in its proof are:

* `e1aU2_pow_eq_one_of_pow_eq_one` — in a linearly ordered commutative group with zero, `x ^ p = 1`
  forces `x = 1`;
* `e1aU2_valuation_finset_sum_lt_one` / `e1aU2_valuation_finset_sum_le_one` — finite sums of
  elements of value `< 1` (resp. `≤ 1`) have value `< 1` (resp. `≤ 1`);
* `e1aU2_mem_henselField_iff_mem_fixedField_stabilizer` — the henselisation `K^h = Ω^{D_A ⊓ G_K}` is
  the fixed field of the stabiliser of `A` in `Gal(Ω/K)`;
* `e1aU2_exists_base_val_eq_of_mem_henselField` — `K^h` is an immediate extension of `K`, hence
  every unit of `K^h` has the same `A`-value as some element of `K`;
* `e1aU2_isInertia_smul_pow_root_eq_self` — tameness: an inertia element fixing a unit fixes its
  `p`-th root;
* `e1aU2_kummerCharZMod_eq_zero_of_fixes_pow_root` — a Kummer character vanishes at `τ` as soon as
  `τ` fixes some `p`-th root.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

open Work.SSGRoute.E1aClean

/-! ## Elementary auxiliary facts -/

/-- In a linearly ordered commutative group with zero, `x ^ p = 1` forces `x = 1`. -/
private lemma e1aU2_pow_eq_one_of_pow_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {x : Γ} {p : ℕ} (hp : 0 < p) (h : x ^ p = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le h1 hp.ne'))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 hp.ne'))

/-- A finite sum of elements of `A`-value `< 1` has `A`-value `< 1`. -/
private lemma e1aU2_valuation_finset_sum_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {ι : Type*} (s : Finset ι) (f : ι → Ω)
    (h : ∀ i ∈ s, A.valuation (f i) < 1) : A.valuation (∑ i ∈ s, f i) < 1 := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _)
      (max_lt (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

/-- A finite sum of elements of `A`-value `≤ 1` has `A`-value `≤ 1`. -/
private lemma e1aU2_valuation_finset_sum_le_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {ι : Type*} (s : Finset ι) (f : ι → Ω)
    (h : ∀ i ∈ s, A.valuation (f i) ≤ 1) : A.valuation (∑ i ∈ s, f i) ≤ 1 := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact le_trans (Valuation.map_add _ _ _)
      (max_le (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

/-! ## The henselisation is the decomposition field over `K` -/

/-- **The henselisation `K^h = Ω^{D_A ⊓ G_K}` is the fixed field of the stabiliser of `A` in
`Gal(Ω/K)`.**  This transports between the two descriptions of `K^h` as a subset of `Ω`. -/
private lemma e1aU2_mem_henselField_iff_mem_fixedField_stabilizer
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (A : ValuationSubring Ω) (x : Ω) :
    x ∈ henselField k Ω K A ↔
      x ∈ IntermediateField.fixedField (MulAction.stabilizer (Ω ≃ₐ[↥K] Ω) A) := by
  have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  rw [henselField, hker]
  constructor
  · intro hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro τ hτ
    have hτ' :=
      (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubring_iff A τ).mp hτ
    have hmem : τ.restrictScalars k ∈
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) := by
      refine ⟨?_, ?_⟩
      · exact (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubring_iff A
          (τ.restrictScalars k)).mpr (fun y => hτ' y)
      · exact (IntermediateField.mem_fixingSubgroup_iff K (τ.restrictScalars k)).mpr
          (fun z hz => τ.commutes ⟨z, hz⟩)
    exact hx (τ.restrictScalars k) hmem
  · intro hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro σ hσ
    obtain ⟨hσD, hσK⟩ := hσ
    have hσ' := (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubring_iff A σ).mp hσD
    set τ : Ω ≃ₐ[↥K] Ω := (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ with hτdef
    have hτmem : τ ∈ MulAction.stabilizer (Ω ≃ₐ[↥K] Ω) A :=
      (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubring_iff A τ).mpr
        (fun y => by rw [hτdef]; exact hσ' y)
    exact hx τ hτmem

/-- **The henselisation is an immediate extension of `K`**: every element of `K^h` has the same
`A`-value as some element of `K`. -/
private lemma e1aU2_exists_base_val_eq_of_mem_henselField
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (A : ValuationSubring Ω) (x : Ω) (hx : x ∈ henselField k Ω K A) :
    ∃ β : ↥K, A.valuation x = A.valuation (algebraMap ↥K Ω β) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : IsSepClosure ↥K Ω := ⟨inferInstance, inferInstance⟩
  have hx' : x ∈ IntermediateField.fixedField (MulAction.stabilizer (Ω ≃ₐ[↥K] Ω) A) :=
    (e1aU2_mem_henselField_iff_mem_fixedField_stabilizer k Ω K A x).mp hx
  exact Commons.RingTheory.Valuation.valuation_mem_range_of_mem_decompositionField
    (F := ↥K) (E := Ω) A ⟨x, hx'⟩

/-! ## Tameness: inertia elements fix the `p`-th root of a unit they fix -/

/-- **An inertia element fixes a `p`-th root of a unit when it fixes the unit.**  If `w ^ p = w₀`
with `A.valuation w₀ = 1` and `σ ∈ I_A` fixes `w₀`, then `σ w = w`: the ratio `ξ = σ w / w` is a
`p`-th root of unity with `ξ ≡ 1 mod 𝔪`, and `p ∉ 𝔪` rules this out (the geometric sum
`1 + ξ + ⋯ + ξ^{p-1} = 0` reduces to `p` in the residue field). -/
private lemma e1aU2_isInertia_smul_pow_root_eq_self {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (p : ℕ) [Fact p.Prime] (hp : ¬ A.valuation (p : Ω) < 1)
    (σ : Ω ≃ₐ[k] Ω) (hσ : SSGRoute.IsInertia k A σ)
    {w₀ w : Ω} (hw : w ^ p = w₀) (hw₀ : A.valuation w₀ = 1) (hfix : σ w₀ = w₀) :
    σ w = w := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hpne] at hw
    subst hw
    simp at hw₀
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw₀
    exact zero_ne_one hw₀
  -- `w` is a unit of `A`
  have hvalw : A.valuation w = 1 :=
    e1aU2_pow_eq_one_of_pow_eq_one hp0 (by rw [← map_pow, hw, hw₀])
  obtain ⟨hσstab, hσinertia⟩ := hσ
  have hσA : σ • A = A := MulAction.mem_stabilizer_iff.mp hσstab
  by_contra hne
  have hwA : w ∈ A := (ValuationSubring.valuation_le_one_iff A w).mp hvalw.le
  have hσwA : σ w ∈ A := by
    have h1 : σ • w ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ w A hwA
    rwa [hσA] at h1
  -- the ratio `ξ = σ w / w`
  set ξ : Ω := σ w / w with hξdef
  have hξmul : ξ * w = σ w := by rw [hξdef, div_mul_cancel₀ _ hw0]
  have hξpow : ξ ^ p = 1 := by
    have h1 : ξ ^ p = σ w ^ p / w ^ p := by rw [hξdef, div_pow]
    rw [h1, ← map_pow, hw, hfix]
    exact div_self hw₀ne
  have hξne : ξ ≠ 1 := by
    intro h1
    exact hne (by rw [← hξmul, h1, one_mul])
  -- `ξ - 1` is a nonzero element of the maximal ideal
  have hξ1A : ξ - 1 ∈ A := by
    have h1 : σ w - w ∈ A := sub_mem hσwA hwA
    have h2 : w⁻¹ ∈ A := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hvalw, inv_one]
    have h3 : (σ w - w) * w⁻¹ ∈ A := mul_mem h1 h2
    have h4 : (σ w - w) * w⁻¹ = ξ - 1 := by
      rw [hξdef, div_eq_mul_inv, sub_mul, mul_inv_cancel₀ hw0]
    rwa [h4] at h3
  have hvalξ1 : A.valuation (ξ - 1) < 1 := by
    have h4 : (σ w - w) * w⁻¹ = ξ - 1 := by
      rw [hξdef, div_eq_mul_inv, sub_mul, mul_inv_cancel₀ hw0]
    have h5 : A.valuation ((σ w - w) * w⁻¹) = A.valuation (σ w - w) := by
      rw [map_mul, map_inv₀, hvalw, inv_one, mul_one]
    rw [← h4, h5]
    exact hσinertia w hwA
  have hval1ξ : A.valuation (1 - ξ) < 1 := by
    rw [show (1 : Ω) - ξ = -(ξ - 1) by ring, Valuation.map_neg]
    exact hvalξ1
  -- contradiction: `p ∈ 𝔪`
  have hξA : ξ ∈ A := by
    have := add_mem hξ1A (one_mem A)
    simpa using this
  have hS : ∑ i ∈ Finset.range p, ξ ^ i = 0 := by
    have h := mul_neg_geom_sum ξ p
    rw [hξpow, sub_self] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (sub_ne_zero.mpr (Ne.symm hξne))
    · exact h1
  have hT : ∀ i ∈ Finset.range p, A.valuation (1 - ξ ^ i) < 1 := by
    intro i _
    have hfac : 1 - ξ ^ i = (1 - ξ) * ∑ j ∈ Finset.range i, ξ ^ j := by
      rw [mul_neg_geom_sum]
    rw [hfac, map_mul]
    have hTle : A.valuation (∑ j ∈ Finset.range i, ξ ^ j) ≤ 1 :=
      e1aU2_valuation_finset_sum_le_one A _ _
        (fun j _ => (ValuationSubring.valuation_le_one_iff A _).mpr (pow_mem hξA j))
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hval1ξ hTle
  have hpn : (p : Ω) = ∑ i ∈ Finset.range p, (1 - ξ ^ i) := by
    rw [Finset.sum_sub_distrib, hS, sub_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hlt : A.valuation (p : Ω) < 1 := by
    rw [hpn]
    exact e1aU2_valuation_finset_sum_lt_one A _ _ hT
  exact hp hlt

/-! ## The Kummer character vanishes at an automorphism fixing some root -/

/-- **The Kummer character vanishes as soon as some `p`-th root is fixed** (the Kummer index does
not depend on the choice of root). -/
private lemma e1aU2_kummerCharZMod_eq_zero_of_fixes_pow_root {K Ω : Type} [Field K] [Field Ω]
    [Algebra K Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (β : Kˣ) (τ : Ω ≃ₐ[K] Ω) {γ : Ω} (hγ : γ ^ p = algebraMap K Ω (β : K)) (hτ : τ γ = γ) :
    Work.SSGRoute.kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β τ = 0 := by
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hγ
    exact (map_ne_zero (algebraMap K Ω)).mpr β.ne_zero hγ.symm
  set γu : Ωˣ := Units.mk0 γ hγ0 with hγudef
  have hγupow : γu ^ p = Units.map (algebraMap K Ω) β := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.coe_map, hγudef, Units.val_mk0]
    exact hγ
  have hτu : (τ : Ω → Ω) (γu : Ω) = γu := by
    rw [hγudef, Units.val_mk0]
    exact hτ
  have h1 : Work.SSGRoute.kummerIdx p hζ β γu hγupow τ = 0 :=
    Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq p hζ β γu hγupow τ hτu
  have h2 := Work.SSGRoute.kummerIdx_congr (E := Ω) p hζ β
    (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p β) hγupow τ
  rw [Work.SSGRoute.kummerCharZMod_apply, h2, h1]

end Work.SSGRoute.E1aClean.LeadPhiUnr

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

/-- **(U2) Kummer at the henselian level.**  A unit `u` of `K^h = Ω^{D_A ⊓ G_K}` having a `p`-th
root `y ∈ Ω` fixed by every inertia element of `G_K` has `p`-divisible valuation:
`φ u = b^p · w` with `w ∈ 𝒪_qˣ`.  (Tame: `q ∤ p` is used only to see that a `p`-th root of a unit
is inertia-fixed.)  Lead design `_lead_design/ssg_phiunr_1120.md` (b)4. -/
theorem henselUnit_pow_mul_localUnits_of_inertiaFixedRoot (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    (hp : ¬ A.valuation (p : Ω) < 1)
    (φ : ↥(henselOverDecomp k Ω K A) →+*
        NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q))
    (hφ : ∀ x : ↥K, φ ⟨(x : Ω), le_henselField k Ω K A x.2⟩ =
        algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) x)
    (hφint : ∀ x : (↥(henselOverDecomp k Ω K A))ˣ,
        Units.map φ.toMonoidHom x ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite q)
          ↔ A.valuation (((x : ↥(henselOverDecomp k Ω K A)) : Ω)) = 1)
    (u : (↥(henselOverDecomp k Ω K A))ˣ) (y : Ω)
    (hy : y ^ p = ((u : ↥(henselOverDecomp k Ω K A)) : Ω))
    (hI : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup → SSGRoute.IsInertia k A σ → σ y = y) :
    ∃ b : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q))ˣ,
      ∃ w ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite q),
        Units.map φ.toMonoidHom u = b ^ p * w := by
  classical
  haveI hAlgClosedΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  have h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q :=
    Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  -- `ζ` as an element of `K`
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK p := by
    refine (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap ↥K Ω)
      (algebraMap ↥K Ω).injective).mp ?_
    simpa [hζKdef] using hζ
  -- `u` as an element of `Ω`
  set uΩ : Ω := ((u : ↥(henselOverDecomp k Ω K A)) : Ω) with huΩdef
  have huΩmem : uΩ ∈ henselField k Ω K A := by
    rw [huΩdef]
    exact (u : ↥(henselOverDecomp k Ω K A)).2
  have huΩmem' : uΩ ∈ IntermediateField.fixedField
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by rwa [henselField, hker] at huΩmem
  have huΩne : uΩ ≠ 0 := by
    rw [huΩdef]
    intro h
    exact u.ne_zero (Subtype.ext h)
  -- an element of `K` with the same value as `u`
  obtain ⟨β, hβval⟩ := e1aU2_exists_base_val_eq_of_mem_henselField k Ω K A uΩ huΩmem
  have hβne : β ≠ 0 := by
    intro h
    have h1 : A.valuation (algebraMap ↥K Ω β) = 0 := by simp [h]
    rw [← hβval] at h1
    exact (Valuation.ne_zero_iff A.valuation).mpr huΩne h1
  have hβΩne : algebraMap ↥K Ω β ≠ 0 := fun h => hβne ((algebraMap ↥K Ω).injective h)
  have hβmem : algebraMap ↥K Ω β ∈ IntermediateField.fixedField
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    have h2 := le_henselField k Ω K A β.2
    rwa [henselField, hker] at h2
  -- the unit part of `u` at the place, an element of `K^h`
  set w₀Ω : Ω := uΩ / algebraMap ↥K Ω β with hw₀Ωdef
  have hw₀Ωne : w₀Ω ≠ 0 := by rw [hw₀Ωdef]; exact div_ne_zero huΩne hβΩne
  have hw₀val : A.valuation w₀Ω = 1 := by
    have h : w₀Ω = uΩ * (algebraMap ↥K Ω β)⁻¹ := by rw [hw₀Ωdef, div_eq_mul_inv]
    rw [h, Valuation.map_mul, Valuation.map_inv, ← hβval]
    exact mul_inv_cancel₀ ((Valuation.ne_zero_iff A.valuation).mpr huΩne)
  have hw₀mem : w₀Ω ∈ henselField k Ω K A := by
    rw [hw₀Ωdef]
    exact div_mem huΩmem (le_henselField k Ω K A β.2)
  -- a `p`-th root of `w₀Ω`
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq w₀Ω (Fact.out : p.Prime).pos
  -- every inertia element of `G_K` fixes `w`
  have hfix_w : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup → SSGRoute.IsInertia k A σ →
      σ w = w := by
    intro σ hσK hσI
    refine e1aU2_isInertia_smul_pow_root_eq_self A p hp σ hσI hw hw₀val ?_
    have hmem : σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup := ⟨hσI.1, hσK⟩
    have hσu : σ uΩ = uΩ :=
      (IntermediateField.mem_fixedField_iff _ uΩ).mp huΩmem' σ hmem
    have hσβ : σ (algebraMap ↥K Ω β) = algebraMap ↥K Ω β :=
      (IntermediateField.mem_fixedField_iff _ _).mp hβmem σ hmem
    show σ w₀Ω = w₀Ω
    rw [hw₀Ωdef, map_div₀, hσu, hσβ]
  -- the Kummer character of `β` vanishes on inertia
  have hchar : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      SSGRoute.IsInertia k A σ →
      Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p hζK' (Units.mk0 β hβne)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) = 0 := by
    intro σ hσ hσI
    have hσw : σ w = w := hfix_w σ hσ hσI
    have hσy : σ y = y := hI σ hσ hσI
    have hdiv : (y / w) ^ p = algebraMap ↥K Ω ((Units.mk0 β hβne : (↥K)ˣ) : ↥K) := by
      rw [div_pow, hy, hw, hw₀Ωdef, Units.val_mk0, div_div_eq_mul_div]
      exact mul_div_cancel_left₀ _ huΩne
    have hτw : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) (y / w) = y / w := by
      show σ (y / w) = y / w
      rw [map_div₀, hσy, hσw]
    exact e1aU2_kummerCharZMod_eq_zero_of_fixes_pow_root p hζK' (Units.mk0 β hβne) _ hdiv hτw
  -- the global Kummer lemma
  obtain ⟨γ, u', hu'mem, hKum⟩ :=
    Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
      (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζK) (hζ := hζK') (A := A) (hA := hA)
      (𝔭 := q) (h𝔭 := h𝔭) (β := Units.mk0 β hβne) (h := hchar)
  have hKum_val : algebraMap ↥K
        (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) β =
      (γ : NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) ^ p *
        (u' : NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) := by
    have h := congrArg (fun z : (q.adicCompletion ↥K)ˣ => (z : q.adicCompletion ↥K)) hKum
    simpa [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0] using h
  -- the corresponding elements of `K^h`
  let βelem : ↥(henselOverDecomp k Ω K A) :=
    ⟨algebraMap ↥K Ω β, le_henselField k Ω K A β.2⟩
  have hβelemne : βelem ≠ 0 := by
    intro h
    exact hβΩne (congrArg Subtype.val h)
  let βunit : (↥(henselOverDecomp k Ω K A))ˣ := Units.mk0 βelem hβelemne
  have hw₀ne : (⟨w₀Ω, hw₀mem⟩ : ↥(henselOverDecomp k Ω K A)) ≠ 0 := by
    intro h
    exact hw₀Ωne (congrArg Subtype.val h)
  let w₀unit : (↥(henselOverDecomp k Ω K A))ˣ := Units.mk0 ⟨w₀Ω, hw₀mem⟩ hw₀ne
  have hunitelt : (u : ↥(henselOverDecomp k Ω K A)) = βelem * ⟨w₀Ω, hw₀mem⟩ := by
    apply Subtype.ext
    show uΩ = algebraMap ↥K Ω β * w₀Ω
    rw [hw₀Ωdef]
    exact (mul_div_cancel₀ uΩ hβΩne).symm
  have hunit : u = βunit * w₀unit := by
    refine Units.ext ?_
    show (u : ↥(henselOverDecomp k Ω K A)) = βelem * ⟨w₀Ω, hw₀mem⟩
    exact hunitelt
  have hφβ : φ βelem = algebraMap ↥K
      (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) β :=
    hφ β
  have hφw₀ : Units.map φ.toMonoidHom w₀unit ∈
      NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite q) := by
    rw [hφint w₀unit]
    show A.valuation w₀Ω = 1
    exact hw₀val
  have hβmap : Units.map φ.toMonoidHom βunit =
      Units.map (algebraMap ↥K
        (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)))
        (Units.mk0 β hβne) := by
    refine Units.ext ?_
    show φ βelem = algebraMap ↥K
      (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) β
    exact hφβ
  refine ⟨γ, u' * Units.map φ.toMonoidHom w₀unit, mul_mem hu'mem hφw₀, ?_⟩
  calc Units.map φ.toMonoidHom u
      = Units.map φ.toMonoidHom (βunit * w₀unit) := by rw [hunit]
    _ = Units.map φ.toMonoidHom βunit * Units.map φ.toMonoidHom w₀unit :=
          map_mul (Units.map φ.toMonoidHom) βunit w₀unit
    _ = Units.map (algebraMap ↥K
          (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)))
          (Units.mk0 β hβne) * Units.map φ.toMonoidHom w₀unit := by rw [hβmap]
    _ = (γ ^ p * u') * Units.map φ.toMonoidHom w₀unit := by rw [hKum]
    _ = γ ^ p * (u' * Units.map φ.toMonoidHom w₀unit) := mul_assoc _ _ _

end Work.SSGRoute.E1aClean.LeadPhiUnr
