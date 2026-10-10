import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.exists_isFrobAtPrime_split
import Submission.Work.SSGRoute.ZDataMup.swOddStep
import Submission.Work.SSGRoute.z_data_mup_arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
-- TF-FAST (IsTorsionFree local instance)
/-- Build-speed: `IsAlgClosure k Ω` needs `Module.IsTorsionFree k Ω`, which is otherwise
re-synthesized (about 2 s) at every occurrence. File-local, Prop-valued. -/
private theorem tfFast_isTorsionFree {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] :
    Module.IsTorsionFree k Ω :=
  inferInstance

attribute [local instance] tfFast_isTorsionFree
-- TF-FAST-END

namespace Work.SSGRoute.ZDataMup

/-! ## Two bookkeeping lemmas for the assembly (clause 1 at the `k`-conjugates of `cs(S)`)

Clause 1 of the target is stated at *every* place `B` `k`-conjugate to an element of `S`, but the
Schmidt--Wingberg construction prescribes the datum only at one representative of each `K`-class
above a `k`-class of `S`.  The two lemmas below transport the agreement along `G_K`-conjugation:
the Kummer cochain of `b ∈ Kˣ` is invariant under conjugation by `K.fixingSubgroup` (because it is
*additive* there and lands in the additive group `ZMod p`), and `y` is invariant for the same
reason.  No arithmetic is used. -/

/-- **The level-`K` Kummer cochain is invariant under conjugation by `K.fixingSubgroup`.** -/
theorem nodeKummerCocharZMod_conj {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    {τ : Ω ≃ₐ[k] Ω} (hτ : τ ∈ K.fixingSubgroup) (σ : Ω ≃ₐ[k] Ω) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b (τ * σ * τ⁻¹)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ := by
  classical
  have hzero : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b 1 = 0 := by
    have h := Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b 1
      K.fixingSubgroup.one_mem 1 K.fixingSubgroup.one_mem
    rw [one_mul] at h
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  have hinv : ∀ g ∈ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b g⁻¹
        = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b g := by
    intro g hg
    have h := Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b g hg g⁻¹
      (K.fixingSubgroup.inv_mem hg)
    rw [mul_inv_cancel, hzero] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  by_cases hσ : σ ∈ K.fixingSubgroup
  · have hτσ : τ * σ ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hτ hσ
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b (τ * σ) hτσ τ⁻¹
      (K.fixingSubgroup.inv_mem hτ),
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b τ hτ σ hσ,
      hinv τ hτ]
    abel
  · have hmem : τ * σ * τ⁻¹ ∉ K.fixingSubgroup := by
      intro hconj
      have hσ' : σ = τ⁻¹ * (τ * σ * τ⁻¹) * τ := by group
      rw [hσ'] at hσ
      exact hσ (K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem
        (K.fixingSubgroup.inv_mem hτ) hconj) hτ)
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem hmem,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem hσ]

/-- **An additive function on `K.fixingSubgroup` is invariant under conjugation by
`K.fixingSubgroup`.** -/
theorem additive_conj_invariant {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    {τ : Ω ≃ₐ[k] Ω} (hτ : τ ∈ K.fixingSubgroup)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    y (τ * σ * τ⁻¹) = y σ := by
  have hzero : y 1 = 0 := by
    have h := hy 1 K.fixingSubgroup.one_mem 1 K.fixingSubgroup.one_mem
    rw [one_mul] at h
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  have hinv : y τ⁻¹ = - y τ := by
    have h := hy τ hτ τ⁻¹ (K.fixingSubgroup.inv_mem hτ)
    rw [mul_inv_cancel, hzero] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hτσ : τ * σ ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hτ hσ
  rw [hy (τ * σ) hτσ τ⁻¹ (K.fixingSubgroup.inv_mem hτ), hy τ hτ σ hσ, hinv]
  abel

/-- **The local agreement transports to the `K`-conjugates of a place.**  If `χ_b` agrees with `y`
on the level-`K` local group of `A`, and `B = τ • A` with `τ ∈ K.fixingSubgroup`, then it agrees on
the level-`K` local group of `B` as well. -/
theorem localAgreement_conj {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    {A B : ValuationSubring Ω} {τ : Ω ≃ₐ[k] Ω} (hτ : τ ∈ K.fixingSubgroup)
    (hAB : τ • A = B)
    (hA : ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k A →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ) :
    ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ := by
  intro σ hσK hσB
  have hτi : τ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hτ
  set σ' : Ω ≃ₐ[k] Ω := τ⁻¹ * σ * τ with hσ'def
  have hσ'K : σ' ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hτi hσK) hτ
  have hσ'A : σ' ∈ SSGRoute.decomp k A := by
    have hBA : τ⁻¹ • B = A := by rw [← hAB, inv_smul_smul]
    have hσB' : σ • B = B := hσB
    have : σ' • A = A := by
      rw [hσ'def, mul_smul, mul_smul, hAB, hσB', hBA]
    exact this
  have hconj : τ * σ' * τ⁻¹ = σ := by
    rw [hσ'def]; group
  calc Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b (τ * σ' * τ⁻¹) := by
        rw [hconj]
    _ = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ' :=
        nodeKummerCocharZMod_conj K ζ hζ hζK b hτ σ'
    _ = y σ' := hA σ' hσ'K hσ'A
    _ = y (τ * σ' * τ⁻¹) := (additive_conj_invariant K y hy hτ hσ'K).symm
    _ = y σ := by rw [hconj]

/-- **Clause 1 of the target from the agreement at a covering set of `K`-classes.**  The
construction prescribes the datum at one representative per `K`-class above the `k`-classes of `S`;
this lemma converts that into clause 1 for *every* place of `cs(S)`. -/
theorem clause_one_of_covering {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (S T : Finset (ValuationSubring Ω))
    (hcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
    (hT : ∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k A →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ := by
  intro B hB hS σ hσK hσB
  obtain ⟨A, hA, τ, hτ, hτA⟩ := hcov B hB hS
  exact localAgreement_conj K ζ hζ hζK b y hy hτ hτA (hT A hA) σ hσK hσB

/-- **Clause 2 of the target from the oracle's confinement.**  If `z = χ_b` is unramified outside
the `K`-classes of `T` and of the escape prime `Q`, if every `K`-class of `T` lies above a place of
`S`, and if `Q` is split in `N`, then `z` kills the inertia at every finite place outside `cs(S)`
which is not split in `N` (the escape prime and its conjugates being `N`-split). -/
theorem clause_two_of_confinement {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    (S T : Finset (ValuationSubring Ω)) (Q : ValuationSubring Ω)
    (hQsplit : SSGRoute.IsSplitIn k N Q)
    (hTS : ∀ A ∈ T, ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A)
    (hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → (¬ Work.SSGRoute.gesKConj K Q B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0 := by
  have hnorm : (N.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  intro B hB hS hns σ hσK hσI
  refine hconf B hB (fun A hA hconj => ?_) (fun hconj => ?_) σ hσK hσI
  · -- `B` is `k`-conjugate to a place of `S` through that of `T`
    obtain ⟨A₀, hA₀, hconj₀⟩ := hTS A hA
    obtain ⟨τ, hτ, hτA⟩ := hconj
    exact hS A₀ hA₀ (SSGRoute.isConjPlace_trans hconj₀ ⟨τ, hτA⟩)
  · -- the escape prime is `N`-split, and so are its `K`-conjugates
    obtain ⟨τ, hτK, hτQ⟩ := hconj
    have hBsplit : SSGRoute.IsSplitIn k N B := by
      rw [← hτQ]
      exact (SSGRoute.isSplitIn_conj N hnorm Q τ).mpr hQsplit
    exact hns hBsplit

/-- **A chosen lift of `σ ∈ Gal(K/k)` to `G_k`.** -/
noncomputable def galLift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) : Ω ≃ₐ[k] Ω :=
  Classical.choose (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥K) (E := Ω) σ)

/-- The defining property of `galLift`. -/
theorem galLift_spec {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) :
    AlgEquiv.restrictNormalHom K (galLift K σ) = σ :=
  Classical.choose_spec (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥K) (E := Ω) σ)

/-- **One representative per `K`-class above the places of `S`** (the set called `T₀` in the design
note): the `k`-images of the places of `S` under the chosen lifts of `Gal(K/k)`. -/
noncomputable def kleadReps {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) : Finset (ValuationSubring Ω) := by
  classical
  exact (S.product (Finset.univ : Finset (K ≃ₐ[k] K))).image
    (fun p : ValuationSubring Ω × (K ≃ₐ[k] K) => galLift K p.2 • p.1)

/-- **Every `k`-conjugate of a place of `S` is `K`-conjugate to a representative.**  This is the
covering property consumed by `clause_one_of_covering` (and by the recursion's place set). -/
theorem kleadReps_covers {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) {A B : ValuationSubring Ω} (hA : A ∈ S)
    (hAB : SSGRoute.IsConjPlace k A B) :
    ∃ A' ∈ kleadReps K S, Work.SSGRoute.gesKConj K A' B := by
  classical
  obtain ⟨ρ, hρ⟩ := hAB
  refine ⟨galLift K (AlgEquiv.restrictNormalHom K ρ) • A, ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨(A, AlgEquiv.restrictNormalHom K ρ), ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨hA, Finset.mem_univ (AlgEquiv.restrictNormalHom K ρ)⟩
  · have hres : AlgEquiv.restrictNormalHom K
        (ρ * (galLift K (AlgEquiv.restrictNormalHom K ρ))⁻¹) = 1 := by
      rw [map_mul, map_inv, galLift_spec]
      simp
    have hmemK : ρ * (galLift K (AlgEquiv.restrictNormalHom K ρ))⁻¹ ∈ K.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker K]
      exact hres
    exact ⟨ρ * (galLift K (AlgEquiv.restrictNormalHom K ρ))⁻¹, hmemK, by
      rw [mul_smul, inv_smul_smul, hρ]⟩

/-- **The correction datum attached to an escape prime.**  Fix a global datum `g` (in the
construction, `g = ½y`).  At the `K`-classes above the `k`-place of an escape prime `Q` the datum is
chosen so that the *total* class realised by the oracle there is

* `g + (−g) = 0` at the `K`-class of `Q` itself, and
* `g + (−z − g) = −z` at every other `K`-class above the same `k`-place,

where `z` is the previous class; off the `k`-place of `Q` the datum is `0`.  This is
Schmidt--Wingberg's condition (3) with the corrected sign, *shifted by the global datum*: it makes the
final class `z_i + z_N` vanish on the local groups at the older escape primes (they are unramified
there) and at the siblings of the last escape prime (this is the chain), while leaving the escape
primes themselves as the only places at which the final class can be ramified.  (Without the shift by
`−g` the total class at the added blocks would be `g`, not `0`, and clause 3 would be violated
whenever `y` is ramified at an escape prime.) -/
noncomputable def correctionDatum {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω) :
    ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p := by
  classical
  exact fun A τ => if Work.SSGRoute.gesKConj K Q A then - g τ
    else if SSGRoute.IsConjPlace k Q A then - z τ - g τ else 0

/-- **The correction datum is additive on every local group.** -/
theorem correctionDatum_add {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (g z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (Q A : ValuationSubring Ω)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hz : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) :
    ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        correctionDatum K g z Q A (x * y)
          = correctionDatum K g z Q A x + correctionDatum K g z Q A y := by
  intro x hx y hy
  have hx' : x ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hx).2
  have hy' : y ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hy).2
  by_cases h1 : Work.SSGRoute.gesKConj K Q A
  · simp only [correctionDatum, if_pos h1, hg x hx' y hy']; ring
  · by_cases h2 : SSGRoute.IsConjPlace k Q A
    · simp only [correctionDatum, if_neg h1, if_pos h2, hz x hx' y hy', hg x hx' y hy']; ring
    · simp only [correctionDatum, if_neg h1, if_neg h2]; ring

/-- **The correction datum is locally constant on every local group.** -/
theorem correctionDatum_locConst {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (g z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (Q A : ValuationSubring Ω) (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hg1 : g 1 = 0) (hzc : SSGRoute.IsLocConstOn K.fixingSubgroup z) (hz1 : z 1 = 0) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup →
        correctionDatum K g z Q A x = 0 := by
  obtain ⟨U₁, hU₁o, hU₁⟩ := hgc
  obtain ⟨U₂, hU₂o, hU₂⟩ := hzc
  refine ⟨U₁ ⊓ U₂, hU₁o.inter hU₂o, ?_⟩
  intro x hxU hxA
  rw [Subgroup.mem_inf] at hxU
  have hxK : x ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hxA).2
  have hg' : g x = 0 := by
    have h1 : g x = g 1 := by
      have h1' := hU₁ 1 K.fixingSubgroup.one_mem x hxU.1 hxK
      simpa using h1'
    rw [h1, hg1]
  have hz' : z x = 0 := by
    have h1 : z x = z 1 := by
      have h1' := hU₂ 1 K.fixingSubgroup.one_mem x hxU.2 hxK
      simpa using h1'
    rw [h1, hz1]
  by_cases h1 : Work.SSGRoute.gesKConj K Q A
  · simp only [correctionDatum, if_pos h1, hg', neg_zero]
  · by_cases h2 : SSGRoute.IsConjPlace k Q A
    · simp only [correctionDatum, if_neg h1, if_pos h2, hz', hg', neg_zero, sub_zero]
    · simp only [correctionDatum, if_neg h1, if_neg h2]

/-- **The correction datum vanishes off the `k`-class of the escape prime** (in particular on the
`T₀`-blocks, whose `k`-places are the `k`-classes of `S`, disjoint from the escape prime's). -/
theorem correctionDatum_eq_zero_of_not_conjPlace {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) (g z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (Q A : ValuationSubring Ω) (h : ¬ SSGRoute.IsConjPlace k Q A) :
    correctionDatum K g z Q A = 0 := by
  have h1 : ¬ Work.SSGRoute.gesKConj K Q A :=
    fun hc => h ⟨hc.choose, hc.choose_spec.2⟩
  funext τ
  unfold correctionDatum
  rw [if_neg h1, if_neg h]
  simp

/-- **Every representative of a `K`-class above an `N`-split `k`-place is itself `N`-split.** -/
theorem kleadReps_splitIn {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (Q : ValuationSubring Ω)
    (hQ : SSGRoute.IsSplitIn k N Q) :
    ∀ A ∈ kleadReps K ({Q} : Finset (ValuationSubring Ω)), SSGRoute.IsSplitIn k N A := by
  classical
  have hnorm : (N.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  intro A hA
  obtain ⟨p', hp'mem, hp'eq⟩ := Finset.mem_image.mp hA
  obtain ⟨hQmem, -⟩ := Finset.mem_product.mp hp'mem
  have hQ' : (p'.1 : ValuationSubring Ω) = Q := Finset.mem_singleton.mp hQmem
  rw [← hp'eq, hQ']
  exact (SSGRoute.isSplitIn_conj N hnorm Q (galLift K p'.2)).mpr hQ

/-- **The correction datum satisfies the oracle's orthogonality condition on the classes above the
escape prime**: every such class is `N`-split (it is a `k`-conjugate of the `N`-split `Q`), so the
second disjunct holds at all of them. -/
theorem correctionDatum_orth {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (g z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω) (hQsplit : SSGRoute.IsSplitIn k N Q) :
    ∀ A ∈ kleadReps K ({Q} : Finset (ValuationSubring Ω)),
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
          correctionDatum K g z Q A σ = 0) ∨ SSGRoute.IsSplitIn k N A :=
  fun A hA => Or.inr (kleadReps_splitIn (p := p) K N Q hQsplit A hA)

/-- **Clause 3 of the target from the two escape primes.**  The final class `χ_{b_i b_N}` is the
*sum* of the two escape classes (`Work.SSGRoute.nodeKummerCocharZMod_mul`); its ramification is
confined to the `K`-classes of `P_i` and `P_N` (the two confinements), it vanishes on the local group
of every `k`-conjugate of `P_i` that is not `K`-conjugate (the prescription, condition (3) with the
corrected sign) and likewise at the siblings of `P_N` (the chain); hence it satisfies Schmidt--Wingberg's
sharpened condition (b), by `Work.SSGRoute.ZSplit.sw_conjuncts_five_six`. -/
theorem clause_three_of_two_escapes {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (bi bN : (↥K)ˣ) (Ai AN : ValuationSubring Ω)
    (hAifin : SSGRoute.IsFinPlace k Ai) (hANfin : SSGRoute.IsFinPlace k AN)
    (hAi_split : SSGRoute.IsSplitIn k N Ai) (hAN_split : SSGRoute.IsSplitIn k N AN)
    (S : Finset (ValuationSubring Ω))
    (hconf_i : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • Ai = B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi σ = 0)
    (hconf_N : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • AN = B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN σ = 0)
    (hpresc : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k Ai Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • Ai = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN τ
            = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi τ)
    (hchain : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k AN Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • AN = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi τ
            = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN τ) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
      (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (bi * bN) σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (bi * bN) τ = 0 := by
  have hmul : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (bi * bN)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN :=
    Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK bi bN
  obtain ⟨-, h6⟩ := Work.SSGRoute.ZSplit.sw_conjuncts_five_six K N S Ai AN hAifin hANfin
    hAi_split hAN_split
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN)
    (fun B hB hnotAi hnotAN σ hσK hσI => by
      rw [_root_.Pi.add_apply, hconf_i B hB hnotAi σ hσK hσI,
        hconf_N B hB hnotAN σ hσK hσI, add_zero])
    (fun Q hQ hnot τ hτ => by
      rw [_root_.Pi.add_apply, hpresc Q hQ hnot τ hτ, add_neg_cancel])
    (fun Q hQ hnot τ hτ => by
      rw [_root_.Pi.add_apply, hchain Q hQ hnot τ hτ, neg_add_cancel])
  intro B hB hS hns hram Q hBQ hnot τ hτ
  have h0 := h6 B hB hS hns
    (by
      obtain ⟨σ, hσI, hσK, hσne⟩ := hram
      exact ⟨σ, hσI, hσK, fun hzero => hσne (by rw [← hmul] at hzero; exact hzero)⟩)
    Q hBQ hnot τ hτ
  rw [hmul]
  exact h0

/-- **The place set `T_n` of the recursion**: `T₀ = kleadReps K S` (one representative per `K`-class
above the places of `S`) together with, for each of the first `n` escape primes, one representative
per `K`-class above its `k`-place. -/
noncomputable def histPlaces {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) {n : ℕ}
    (f : Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p))) : Finset (ValuationSubring Ω) := by
  classical
  exact kleadReps K S ∪ Finset.univ.biUnion (fun j : Fin n => kleadReps K {((f j).1)})

/-- **The datum used at stage `n`**: the sum of the corrections `correctionDatum K ½y (z_j) Q_j` over
the escape primes of the history (with the global datum `½y` subtracted, so that the total class
realised by the oracle is `0` at each escape prime's own `K`-class and `−z_j` at the siblings). -/
noncomputable def histDatum {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (y : (Ω ≃ₐ[k] Ω) → ZMod p) {n : ℕ}
    (f : Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p))) :
    ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p := by
  classical
  exact fun A τ => Finset.univ.sum (fun j : Fin n =>
    correctionDatum K (fun σ => (2 : ZMod p)⁻¹ * y σ) ((f j).2) ((f j).1) A τ)

/-- **The invariants of a history of the Schmidt--Wingberg recursion** (the place set and the datum of
stage `m` are read off the prefix `f 0, …, f (m-1)`): every escape prime is finite, split in `N`, not
`K`-conjugate to any earlier one and not `K`-conjugate to any element of its own place set; every class
is locally constant and additive on `K.fixingSubgroup`; the `m`-th class realises
`½y + (the datum of stage `m`)` on every local group of `T_m`; and it kills the inertia outside
`cs(T_m)` and outside the `K`-class of its own escape prime.  The exclusion clause is what forces the
escape prime's `k`-place outside the `k`-classes of `S` (since `T₀` carries *all* the `K`-classes
above them), hence makes every correction vanish on the `T₀`-blocks, so the prescribed datum there is
exactly `½y`. -/
def HistInv {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p))) : Prop :=
  (∀ m : ℕ, SSGRoute.IsFinPlace k ((f m).1)) ∧
  (∀ m : ℕ, SSGRoute.IsSplitIn k N ((f m).1)) ∧
  (∀ m l : ℕ, m < l → ¬ Work.SSGRoute.gesKConj K ((f m).1) ((f l).1)) ∧
  (∀ m : ℕ, ∀ A ∈ histPlaces K S (fun j : Fin m => f j),
      ¬ Work.SSGRoute.gesKConj K A ((f m).1)) ∧
  (∀ m : ℕ, SSGRoute.IsLocConstOn K.fixingSubgroup ((f m).2)) ∧
  (∀ m : ℕ, ∀ x ∈ K.fixingSubgroup, ∀ z ∈ K.fixingSubgroup,
      ((f m).2) (x * z) = ((f m).2) x + ((f m).2) z) ∧
  (∀ m : ℕ, ∀ A ∈ histPlaces K S (fun j : Fin m => f j),
      ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        ((f m).2) σ = (2 : ZMod p)⁻¹ * y σ + histDatum K y (fun j : Fin m => f j) A σ) ∧
  (∀ m : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ histPlaces K S (fun j : Fin m => f j), ¬ Work.SSGRoute.gesKConj K A B) →
      (¬ Work.SSGRoute.gesKConj K ((f m).1) B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ((f m).2) σ = 0)

/-- **The Kummer form of a history of the recursion.**  Every class of the sequence is the Kummer
cochain of a global element `b ∈ Kˣ`, and at its own escape prime the element is *normalised*: it
agrees with the inverse Kummer character of a *uniformiser* on the inertia of the local group
(Schmidt--Wingberg's condition (1): the local class at the escape prime is the class of a
uniformiser, i.e. its "Frobenius part" is `1`).  This is the extra structure which the two-place
reciprocity `Work.SSGRoute.ZDataMup.swZTwoPlaceReciprocity` consumes, and it is exactly the extra
output of the uniformised oracle `Work.SSGRoute.ZDataMup.escape_uniformised`. -/
def HistKummer {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p))) : Prop :=
  (∀ m : ℕ, ∃ b : (↥K)ˣ, ∀ σ ∈ K.fixingSubgroup,
      ((f m).2) σ = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ) ∧
  (∀ m : ℕ, ∃ x : (↥K)ˣ,
      (∀ σ ∈ SSGRoute.decomp k ((f m).1) ⊓ K.fixingSubgroup,
        SSGRoute.IsInertia k ((f m).1) σ →
          ((f m).2) σ
            = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x σ) ∧
      ((f m).1).valuation (algebraMap ↥K Ω (x : ↥K)) < 1 ∧
      (∀ y : ↥K, ((f m).1).valuation (algebraMap ↥K Ω y) < 1 →
        ((f m).1).valuation (algebraMap ↥K Ω y)
          ≤ ((f m).1).valuation (algebraMap ↥K Ω (x : ↥K))))

/-! **The recursion exists** (Schmidt--Wingberg §4, pp. 14--15), in the *uniformised Kummer form*
needed by the assembly: delegated to `Work.SSGRoute.ZDataMup.swRecursionExists` in
`Submission/Work/SSGRoute/ZDataMup/swRecursionExists.lean` (which imports this module, so that the
recursion can be built on the definitions above without an import cycle).  (Kept as a *plain* comment:
a doc comment with no declaration after it does not parse, and this one blocked the whole `H9`
assembly -- node lane, session 30.) -/

/-- `IsConjPlace` is symmetric (the inverse of a conjugating element conjugates back). -/
theorem isConjPlace_symm {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {A B : ValuationSubring Ω} (h : SSGRoute.IsConjPlace k A B) :
    SSGRoute.IsConjPlace k B A := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩

/-- **Every element of `kleadReps K S` is a `k`-conjugate of an element of `S`.** -/
theorem kleadReps_mem_conjPlace {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] {S : Finset (ValuationSubring Ω)} {A : ValuationSubring Ω}
    (hA : A ∈ kleadReps K S) : ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A := by
  classical
  obtain ⟨p', hp'mem, hp'eq⟩ := Finset.mem_image.mp hA
  obtain ⟨hA₀, -⟩ := Finset.mem_product.mp hp'mem
  exact ⟨p'.1, hA₀, galLift K p'.2, hp'eq⟩

/-- **No escape prime is `k`-conjugate to a representative of a `K`-class above `S`.**  This is the
usable content of the oracle-exclusion conjunct of `HistInv`: since `T₀` carries *all* the `K`-classes
above the `k`-classes of `S`, a `k`-conjugate of an element of `S` would have a representative in `T₀`
`K`-conjugate to it, which the exclusion forbids. -/
theorem hist_no_conjPlace_T0 {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p) (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) (j : ℕ) :
    ∀ A ∈ kleadReps K S, ¬ SSGRoute.IsConjPlace k ((f j).1) A := by
  classical
  intro A hA hconj
  obtain ⟨A₀, hA₀, hA₀A⟩ := kleadReps_mem_conjPlace (p := p) K hA
  have hQA₀ : SSGRoute.IsConjPlace k ((f j).1) A₀ :=
    SSGRoute.isConjPlace_trans hconj (isConjPlace_symm hA₀A)
  obtain ⟨A'', hA'', hKconj⟩ := kleadReps_covers K S hA₀ (isConjPlace_symm hQA₀)
  have hmem : A'' ∈ histPlaces K S (fun l : Fin j => f l) :=
    Finset.mem_union_left _ hA''
  exact (hf.2.2.2.1 j A'' hmem) hKconj

/-- **The accumulated datum vanishes on `T₀`.**  Every correction of the history is confined to the
`k`-place of its escape prime, which — by `hist_no_conjPlace_T0` — is disjoint from the `k`-classes of
`S`; hence the total datum used at any stage is `0` on the `T₀`-blocks and the prescribed datum there
is exactly `½y`. -/
theorem histDatum_eq_zero_on_T0 {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) (m : ℕ) :
    ∀ A ∈ kleadReps K S, histDatum K y (fun j : Fin m => f j) A = 0 := by
  intro A hA
  funext τ
  unfold histDatum
  refine Finset.sum_eq_zero (fun j _ => ?_)
  exact congrFun (correctionDatum_eq_zero_of_not_conjPlace K (fun σ => (2 : ZMod p)⁻¹ * y σ)
    ((f j).2) ((f j).1) A (hist_no_conjPlace_T0 K N S y f hf j A hA)) τ

/-- **The place sets of the recursion are monotone in the prefix.** -/
theorem histPlaces_mono {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) {i m : ℕ} (him : i ≤ m)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p))) :
    histPlaces K S (fun j : Fin i => f j) ⊆ histPlaces K S (fun j : Fin m => f j) := by
  classical
  intro A hA
  simp only [histPlaces, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at hA ⊢
  rcases hA with hA | ⟨j, hj⟩
  · exact Or.inl hA
  · exact Or.inr ⟨Fin.castLE him j, hj⟩

/-- **The confinement of a sum of two classes.**  If `z_i` kills the inertia outside the `K`-classes
of `T_i` and of `Q_i`, and `z_N` likewise with `T_N ⊇ T_i` and `Q_N`, then `z_i + z_N` kills the
inertia outside the `K`-classes of `T_N`, `Q_i` and `Q_N`.  (For the final class this is clause 2's
input with `T_N` the terminal place set and the two live escape primes.) -/
theorem sum_confinement {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (zi zN : (Ω ≃ₐ[k] Ω) → ZMod p) (Ti TN : Finset (ValuationSubring Ω))
    (Qi QN : ValuationSubring Ω) (hsub : Ti ⊆ TN)
    (hconf_i : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ Ti, ¬ Work.SSGRoute.gesKConj K A B) → (¬ Work.SSGRoute.gesKConj K Qi B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → zi σ = 0)
    (hconf_N : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ TN, ¬ Work.SSGRoute.gesKConj K A B) → (¬ Work.SSGRoute.gesKConj K QN B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → zN σ = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ TN, ¬ Work.SSGRoute.gesKConj K A B) →
      (¬ Work.SSGRoute.gesKConj K Qi B) → (¬ Work.SSGRoute.gesKConj K QN B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → (zi + zN) σ = 0 := by
  intro B hB hT hQi hQN σ hσK hσI
  rw [_root_.Pi.add_apply, hconf_i B hB (fun A hA hc => hT A (hsub hA) hc) hQi σ hσK hσI,
    hconf_N B hB hT hQN σ hσK hσI, add_zero]

/-- **Clause 2 with two live escape primes.**  The same argument as `clause_two_of_confinement`, with
the second escape prime excluded as well: for `B ∉ cs(S)` not split in `N`, `B` is outside `cs(T)`
(every `K`-class of `T` lies above a place of `S`), and outside the `K`-classes of both escape primes
(each is `N`-split, and splitness transports along `k`-conjugation). -/
theorem clause_two_of_two_confinement {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (S T : Finset (ValuationSubring Ω)) (Qi QN : ValuationSubring Ω)
    (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hQi_split : SSGRoute.IsSplitIn k N Qi) (hQN_split : SSGRoute.IsSplitIn k N QN)
    (hTS : ∀ A ∈ T, ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A)
    (hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
      (¬ Work.SSGRoute.gesKConj K Qi B) → (¬ Work.SSGRoute.gesKConj K QN B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0 := by
  have hnorm : (N.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  intro B hB hS hns σ hσK hσI
  refine hconf B hB (fun A hA hconj => ?_) (fun hconj => ?_) (fun hconj => ?_) σ hσK hσI
  · obtain ⟨A₀, hA₀, hconj₀⟩ := hTS A hA
    obtain ⟨τ, hτ, hτA⟩ := hconj
    exact hS A₀ hA₀ (SSGRoute.isConjPlace_trans hconj₀ ⟨τ, hτA⟩)
  · obtain ⟨τ, -, hτQ⟩ := hconj
    exact hns (by
      rw [← hτQ]
      exact (SSGRoute.isSplitIn_conj N hnorm Qi τ).mpr hQi_split)
  · obtain ⟨τ, -, hτQ⟩ := hconj
    exact hns (by
      rw [← hτQ]
      exact (SSGRoute.isSplitIn_conj N hnorm QN τ).mpr hQN_split)

/-- **The shoe box** (Schmidt--Wingberg's `Ψ_N(z_i) = Ψ_N(z_N)`).  For any family of classes `z` and
any family `G` of "Frobenius elements" (one for each index `m` and each `σ ∈ Gal(K/k)`, i.e. one for
each sibling of the `m`-th escape prime), there are indices `i < N` at which the **unweighted** vectors
`(z m (G m σ))_σ` agree.  The weighting by the ramification indices is unnecessary here because the
escape construction is uniform: `v_{Q_m}(b_m) ≡ −1 (mod p)` at *every* escape prime (the escape element
always has a simple pole there), so the ratios that the chain produces are `1`. -/
theorem shoe_box_matching {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {ι : Type} [Fintype ι]
    (z : ℕ → (Ω ≃ₐ[k] Ω) → ZMod p) (G : ℕ → ι → (Ω ≃ₐ[k] Ω)) :
    ∃ i N : ℕ, i < N ∧ ∀ σ : ι, z N (G N σ) = z i (G i σ) := by
  classical
  obtain ⟨i, N, hlt, heq⟩ :=
    Work.SSGRoute.pigeonhole_two_eq (fun m : ℕ => fun σ : ι => z m (G m σ))
  exact ⟨i, N, hlt, fun σ => (congrFun heq σ).symm⟩

/-- **The value form of the one-sided vanishing at the last escape prime.**  With the shoe-box matching
`χ_{b_N}(g_N) = χ_{b_i}(g_i)`, the prescription `χ_{b_N}(g_i) = −χ_{b_i}(g_i)` and the chain
`χ_{b_i}(g_N) = χ_{b_N}(g_i)`, the sum vanishes at `g_N`:
`χ_{b_i}(g_N) + χ_{b_N}(g_N) = χ_{b_N}(g_i) + χ_{b_i}(g_i) = 0`.
Combined with `ZSplit.localValue_eq_zero_of_frob_eq_zero` (both classes being unramified at the
sibling) this yields the vanishing on the whole local group there, i.e. the last clause-3 input. -/
theorem sibling_value_vanishing {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (bi bN : (↥K)ˣ) (gi gN : Ω ≃ₐ[k] Ω)
    (hmatch : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN gN
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi gi)
    (hpresc : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN gi
      = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi gi)
    (hchain : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi gN
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN gi) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi gN
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN gN = 0 := by
  rw [hchain, hmatch, hpresc, neg_add_cancel]

/-- **The sibling place of an escape prime at the index `σ`**: the representative of the `σ`-th
`K`-class above the `k`-place of `Q`, obtained by conjugating with the chosen lift of `σ`.  For
`σ = 1` this is the `K`-class of `Q` itself; for `σ ≠ 1` it is a *sibling* of `Q` (not
`K`-conjugate to it, as soon as `Q` is completely split in `K`). -/
noncomputable def siblingPlace {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) (Q : ValuationSubring Ω) : ValuationSubring Ω :=
  galLift K σ • Q

/-- **The alignment consumed by `chain_lastPrime`'s `halign_i`/`halign_N` is `rfl`-level**: the
sibling place of `Q` at the index `σ` is the `1`-translate of the `galLift K σ`-image of `Q`. -/
theorem siblingPlace_align {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) (Q : ValuationSubring Ω) :
    ∃ τ ∈ K.fixingSubgroup, siblingPlace K σ Q = τ • (galLift K σ • Q) :=
  ⟨1, K.fixingSubgroup.one_mem, by simp [siblingPlace]⟩

/-- **The shoe box, instantiated at the recursion's sibling places.**  `G m σ` is a Frobenius element
of the local group at the sibling place of the `m`-th escape prime at the index `σ` (produced by
`exists_isFrobAtPrime_split` at the places above an `N`-split prime, where the decomposition group is
already inside `K.fixingSubgroup`).  The conclusion bundles the matching with the two alignments the
chain consumes, so that the selection step is a single object. -/
theorem selection_matching {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)]
    (z : ℕ → (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ℕ → ValuationSubring Ω)
    (G : ℕ → (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω))
    (hG : ∀ m σ, G m σ ∈ SSGRoute.decomp k (siblingPlace K σ (Q m)) ⊓ K.fixingSubgroup) :
    ∃ i N : ℕ, i < N ∧
      (∀ σ : K ≃ₐ[k] K, z N (G N σ) = z i (G i σ)) ∧
      (∀ σ : K ≃ₐ[k] K, ∃ τ ∈ K.fixingSubgroup,
        siblingPlace K σ (Q N) = τ • (galLift K σ • Q N)) ∧
      (∀ σ : K ≃ₐ[k] K, ∃ τ ∈ K.fixingSubgroup,
        siblingPlace K σ (Q i) = τ • (galLift K σ • Q i)) := by
  obtain ⟨i, N, hlt, hmatch⟩ := shoe_box_matching z G
  exact ⟨i, N, hlt, hmatch, fun σ => siblingPlace_align K σ (Q N),
    fun σ => siblingPlace_align K σ (Q i)⟩

/-- **A sibling of an escape prime at an index `σ ≠ 1` is not `K`-conjugate to it**, as soon as the
escape prime is completely split in `K`.  If `τ Q = (galLift σ) Q` with `τ ∈ K.fixingSubgroup`, then
`(galLift σ)⁻¹ τ` stabilises `Q` while restricting to `σ⁻¹ ≠ 1`; but the stabiliser of `Q` lies in
`K.fixingSubgroup` (complete splitting), a contradiction.  This is what makes both escape classes
*unramified* at each sibling, and it supplies the `hsep_*` hypotheses of `chain_lastPrime`. -/
theorem siblingPlace_not_gesKConj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    {σ : K ≃ₐ[k] K} (hσ : σ ≠ 1) {Q : ValuationSubring Ω}
    (hQ : SSGRoute.IsSplitIn k K Q) :
    ¬ Work.SSGRoute.gesKConj K Q (siblingPlace K σ Q) := by
  intro hconj
  obtain ⟨τ, hτK, hτQ⟩ := hconj
  have hstab : (galLift K σ)⁻¹ * τ ∈ SSGRoute.decomp k Q := by
    show ((galLift K σ)⁻¹ * τ) • Q = Q
    rw [mul_smul, hτQ, siblingPlace, inv_smul_smul]
  have hfixker : (galLift K σ)⁻¹ * τ ∈ (SSGRoute.res k K).ker := by
    rw [IntermediateField.restrictNormalHom_ker K]
    exact hQ hstab
  have hτker : τ ∈ (SSGRoute.res k K).ker := by
    rw [IntermediateField.restrictNormalHom_ker K]
    exact hτK
  have hres1 : SSGRoute.res k K ((galLift K σ)⁻¹ * τ) = 1 := hfixker
  have hres2 : SSGRoute.res k K ((galLift K σ)⁻¹ * τ) = σ⁻¹ := by
    have hτ1 : SSGRoute.res k K τ = 1 := hτker
    rw [map_mul, map_inv, galLift_spec, hτ1, mul_one]
  have hinv : σ⁻¹ = 1 := by rw [← hres2, hres1]
  exact hσ (inv_eq_one.mp hinv)

/-- **The Frobenius family `G` of the selection step.**  For every index `m` and every `σ : Gal(K/k)`,
a Frobenius element of the local group at the sibling place `galLift K σ • Q m`, produced by
`exists_isFrobAtPrime_split` (which is where the complete splitting in `K` and the unramifiedness in
the auxiliary level `L` are used: the former makes the `K.fixingSubgroup` conjunct free, the latter
makes "the Frobenius" well defined).  The two side conditions `hQfin'` (finiteness transports along
conjugation) and `hQKsplit'` (splitness transports, `isSplitIn_conj`) are the caller's to discharge —
in the recursion they come from `HistInv`'s first and second conjuncts. -/
theorem exists_frobFamily {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L] (Q : ℕ → ValuationSubring Ω)
    (𝔭 : ℕ → (K ≃ₐ[k] K) → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQfin' : ∀ m σ, SSGRoute.IsFinPlace k (siblingPlace K σ (Q m)))
    (hQKsplit' : ∀ m σ, SSGRoute.IsSplitIn k K (siblingPlace K σ (Q m)))
    (hunrL' : ∀ m σ, ¬ SSGRoute.IsRamifiedIn k L (siblingPlace K σ (Q m)))
    (h𝔭 : ∀ m σ, (siblingPlace K σ (Q m)).comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k (𝔭 m σ)) :
    ∃ G : ℕ → (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω),
      ∀ m σ, G m σ ∈ SSGRoute.decomp k (siblingPlace K σ (Q m)) ⊓ K.fixingSubgroup ∧
        NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) (𝔭 m σ) (SSGRoute.res k L (G m σ)) := by
  choose G hG using fun m σ =>
    Work.SSGRoute.ZDataMup.exists_isFrobAtPrime_split K L (siblingPlace K σ (Q m))
      (hQfin' m σ) (hQKsplit' m σ) (hunrL' m σ) (𝔭 m σ) (h𝔭 m σ)
  exact ⟨G, hG⟩

/-- **The Kummer cochain of an inverse is the negative of the cochain.**  From the additivity
`χ_{ab} = χ_a + χ_b` at `a = b`, `b = b⁻¹` together with `χ_1 = 0`. -/
theorem nodeKummerCocharZMod_inv {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b⁻¹
      = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b := by
  have hone : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (1 : (↥K)ˣ) = 0 := by
    funext σ
    have h := congrFun
      (Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK (1 : (↥K)ˣ) 1) σ
    rw [_root_.Pi.add_apply, one_mul] at h
    have h2 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (1 : (↥K)ˣ) σ
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (1 : (↥K)ˣ) σ
        = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (1 : (↥K)ˣ) σ + 0 := by
      rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  funext σ
  have h := congrFun (Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK b b⁻¹) σ
  rw [_root_.Pi.add_apply, mul_inv_cancel, hone, _root_.Pi.zero_apply] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **The `hnorm_*` slot of `chain_lastPrime` is discharged by taking `x := b⁻¹`**: with
`χ_{b⁻¹} = −χ_b`, the required identity `χ_b τ = −χ_{b⁻¹} τ` is `χ_b τ = −(−χ_b τ)`, i.e. a
tautology.  (This is why the uniformiser lemma is not needed here: no unramifiedness, and no
inertia criterion, enters.)  It also makes the two uniformiser conditions of the chain true whenever
`b` has a simple *pole* at the escape prime — which is exactly the normalisation the escape
construction produces (`v_{Q}(b) ≡ −1 (mod p)`). -/
theorem hnorm_slot_discharge {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ) (A : ValuationSubring Ω) :
    ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ
        = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b⁻¹ σ := by
  intro σ _ _
  rw [nodeKummerCocharZMod_inv]
  simp

/-! ## Reading off the output of the recursion

The lemmas below use only the invariants `HistInv` and the proved bookkeeping of this module; they do
not depend on the arithmetic of the escape oracle (only `half_add_half` needs `p` odd). -/

/-- **The escape primes of a history are pairwise not `k`-conjugate.**  If `Q_m ~ Q_l` with `m < l`,
then the covering `kleadReps K {Q_m}` supplies a block of `histPlaces K S (f|l)` that is
`K`-conjugate to `Q_l`, contradicting the exclusion clause of the history. -/
theorem hist_escapes_not_conj {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) {m l : ℕ} (hml : m < l) :
    ¬ SSGRoute.IsConjPlace k ((f m).1) ((f l).1) := by
  classical
  intro hconj
  obtain ⟨A', hA', hKA'⟩ :=
    kleadReps_covers K (S := {((f m).1)}) (Finset.mem_singleton.mpr rfl) hconj
  have hA'mem : A' ∈ histPlaces K S (fun j : Fin l => f j) :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨m, hml⟩, Finset.mem_univ _, hA'⟩)
  exact hf.2.2.2.1 l A' hA'mem hKA'

/-- `½y + ½y = y` in `ZMod p` for odd `p`. -/
theorem half_add_half {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) :
    (2 : ZMod p)⁻¹ * a + (2 : ZMod p)⁻¹ * a = a := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp h2'
  rw [← add_mul]
  have hh : (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ = 1 := by
    rw [← two_mul]
    exact mul_inv_cancel₀ h2
  rw [hh, one_mul]

/-- **Every element of `histPlaces K S f` is `k`-conjugate to an element of `S` or to one of the
escape primes of the prefix.** -/
theorem histPlaces_mem_conjPlace {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (S : Finset (ValuationSubring Ω)) {n : ℕ}
    (f : Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    {A : ValuationSubring Ω} (hA : A ∈ histPlaces K S f) :
    (∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A) ∨
      ∃ l : Fin n, SSGRoute.IsConjPlace k ((f l).1) A := by
  classical
  unfold histPlaces at hA
  rcases Finset.mem_union.mp hA with h | h
  · exact Or.inl (kleadReps_mem_conjPlace (p := p) K h)
  · obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.mp h
    obtain ⟨A₀, hA₀, hA₀A⟩ := kleadReps_mem_conjPlace (p := p) K hl
    rw [Finset.mem_singleton.mp hA₀] at hA₀A
    exact Or.inr ⟨l, hA₀A⟩

/-- **The classes of a history are prescribed at the blocks above `S`**: at every representative of a
`K`-class above a `k`-class of `S` the class of stage `m` equals `½y`. -/
theorem hist_prescribed_at_T0 {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) (m : ℕ) :
    ∀ A ∈ kleadReps K S, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ((f m).2) σ = (2 : ZMod p)⁻¹ * y σ := by
  intro A hA σ hσ
  classical
  have hpres := hf.2.2.2.2.2.2.1 m A (Finset.mem_union_left _ hA) σ hσ
  have hzero : histDatum K y (fun j : Fin m => f j) A σ = 0 :=
    congrFun (histDatum_eq_zero_on_T0 K N S y f hf m A hA) σ
  rw [hpres, hzero, add_zero]

/-- **The sum of two stages of the recursion kills the inertia outside the escape primes.**  If `B`
is a finite place that is not `k`-conjugate to any element of `S` and not `k`-conjugate to any of the
escape primes `Q_l` with `l < N`, then `z_i + z_N` kills the inertia at `B`: the invariants of the
history confine the ramification of each class to the `K`-classes of the blocks and of its own escape
prime. -/
theorem hist_sum_kills_inertia {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) {i j : ℕ} (hij : i < j) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      (∀ l : ℕ, l ≤ j → ¬ SSGRoute.IsConjPlace k ((f l).1) B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        ((f i).2) σ + ((f j).2) σ = 0 := by
  classical
  intro B hB hS hQ σ hσK hσI
  have hTi : ∀ A ∈ histPlaces K S (fun l : Fin i => f l), ¬ Work.SSGRoute.gesKConj K A B := by
    intro A hA hconj
    obtain ⟨ρ, hρK, hρ⟩ := hconj
    have hconj' : SSGRoute.IsConjPlace k A B := ⟨ρ, hρ⟩
    rcases histPlaces_mem_conjPlace (p := p) K S (fun l : Fin i => f l) hA with
      ⟨A₀, hA₀, hA₀A⟩ | ⟨l, hl⟩
    · exact hS A₀ hA₀ (SSGRoute.isConjPlace_trans hA₀A hconj')
    · exact hQ l (le_of_lt (lt_trans l.2 hij)) (SSGRoute.isConjPlace_trans hl hconj')
  have hQi : ¬ Work.SSGRoute.gesKConj K ((f i).1) B := by
    intro hconj
    obtain ⟨ρ, hρK, hρ⟩ := hconj
    exact hQ i (le_of_lt hij) ⟨ρ, hρ⟩
  have hTj : ∀ A ∈ histPlaces K S (fun l : Fin j => f l), ¬ Work.SSGRoute.gesKConj K A B := by
    intro A hA hconj
    obtain ⟨ρ, hρK, hρ⟩ := hconj
    have hconj' : SSGRoute.IsConjPlace k A B := ⟨ρ, hρ⟩
    rcases histPlaces_mem_conjPlace (p := p) K S (fun l : Fin j => f l) hA with
      ⟨A₀, hA₀, hA₀A⟩ | ⟨l, hl⟩
    · exact hS A₀ hA₀ (SSGRoute.isConjPlace_trans hA₀A hconj')
    · exact hQ l (le_of_lt l.2) (SSGRoute.isConjPlace_trans hl hconj')
  have hQj : ¬ Work.SSGRoute.gesKConj K ((f j).1) B := by
    intro hconj
    obtain ⟨ρ, hρK, hρ⟩ := hconj
    exact hQ j le_rfl ⟨ρ, hρ⟩
  rw [hf.2.2.2.2.2.2.2 i B hB hTi hQi σ hσK hσI,
    hf.2.2.2.2.2.2.2 j B hB hTj hQj σ hσK hσI, add_zero]

/-- **Clause 1 of the target, in class form**: the sum of the two stages of the recursion agrees with
`y` on the local groups of every place `k`-conjugate to an element of `S`. -/
theorem hist_clause_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) {i j : ℕ} :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
        ((f i).2) σ + ((f j).2) σ = y σ := by
  intro B hB hconj σ hσK hσB
  obtain ⟨A, hA, hAB⟩ := hconj
  obtain ⟨A', hA', ρ, hρK, hρ⟩ := kleadReps_covers K S hA hAB
  have hρiK : ρ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hρK
  have hσB' : σ • B = B := hσB
  have hdecomp : ρ⁻¹ * σ * ρ ∈ SSGRoute.decomp k A' ⊓ K.fixingSubgroup := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · show (ρ⁻¹ * σ * ρ) • A' = A'
      rw [mul_smul, mul_smul, hρ, hσB', ← hρ, inv_smul_smul]
    · exact K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hρiK hσK) hρK
  have hσ'K : ρ⁻¹ * σ * ρ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hdecomp).2
  have hτi := hist_prescribed_at_T0 K N S y f hf i A' hA' (ρ⁻¹ * σ * ρ) hdecomp
  have hτj := hist_prescribed_at_T0 K N S y f hf j A' hA' (ρ⁻¹ * σ * ρ) hdecomp
  have hconj_i : ((f i).2) σ = ((f i).2) (ρ⁻¹ * σ * ρ) :=
    (additive_conj_invariant K ((f i).2) (hf.2.2.2.2.2.1 i) hρiK hσK).symm
  have hconj_j : ((f j).2) σ = ((f j).2) (ρ⁻¹ * σ * ρ) :=
    (additive_conj_invariant K ((f j).2) (hf.2.2.2.2.2.1 j) hρiK hσK).symm
  have hyconj : y (ρ⁻¹ * σ * ρ) = y σ :=
    additive_conj_invariant K y hy hρiK hσK
  rw [hconj_i, hconj_j, hτi, hτj,
    half_add_half (p := p) hp (y (ρ⁻¹ * σ * ρ)), hyconj]

/-- **Clause 2 of the target, in class form**: the sum of the two stages of the recursion kills the
inertia of every finite place outside `cs(S)` which is not split in `N`. -/
theorem hist_clause_two {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) {i j : ℕ} (hij : i < j) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        ((f i).2) σ + ((f j).2) σ = 0 := by
  have hnorm : (N.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  intro B hB hS hns σ hσK hσI
  refine hist_sum_kills_inertia K N S y f hf hij B hB hS (fun l _ hconj => ?_) σ hσK hσI
  obtain ⟨τ, hτ⟩ := hconj
  have hsl : SSGRoute.IsSplitIn k N ((f l).1) := hf.2.1 l
  exact hns (by
    rw [← hτ]
    exact (SSGRoute.isSplitIn_conj N hnorm ((f l).1) τ).mpr hsl)

/-- **The sum of the two live classes vanishes at the `k`-conjugates of the earlier escape prime that
are not `K`-conjugate to it** (Schmidt--Wingberg's condition (3) at the pair `(i,j)`, the half of
clause 3 at `Q_i`): at every sibling `K`-prime of `Q_i` the class `z_j` is prescribed to be `-z_i` on
the whole local group, because the correction datum of the history at such a block reduces to the
single `i`-th term by `hist_escapes_not_conj`. -/
theorem hist_sum_zero_at_sibling_of_i {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)))
    (hf : HistInv K N S y f) {i j : ℕ} (hij : i < j) :
    ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k ((f i).1) Q →
      (¬ Work.SSGRoute.gesKConj K ((f i).1) Q) →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        ((f i).2) τ + ((f j).2) τ = 0 := by
  classical
  intro Q hQconj hQnotK τ hτ
  obtain ⟨ρ, hρ⟩ := hQconj
  set σ : K ≃ₐ[k] K := SSGRoute.res k K ρ with hσdef
  set τ₀ : Ω ≃ₐ[k] Ω := ρ * (galLift K σ)⁻¹ with hτ₀def
  have hτ₀K : τ₀ ∈ K.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker K]
    rw [hτ₀def]
    exact MonoidHom.mem_ker.mpr (by
      rw [map_mul, map_inv, galLift_spec, hσdef, mul_inv_cancel])
  have hρeq : ρ = τ₀ * galLift K σ := by
    rw [hτ₀def, mul_assoc, inv_mul_cancel, mul_one]
  set A : ValuationSubring Ω := galLift K σ • ((f i).1) with hAdef
  have hQeq : Q = τ₀ • A := by
    rw [← hρ, hρeq, mul_smul, hAdef]
  have hAmem : A ∈ histPlaces K S (fun l : Fin j => f l) :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨i, hij⟩, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨((f i).1, σ),
        Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr rfl, Finset.mem_univ σ⟩,
        hAdef.symm⟩⟩)
  have hQinotK : ¬ Work.SSGRoute.gesKConj K ((f i).1) A := by
    intro hconj
    obtain ⟨μ, hμK, hμ⟩ := hconj
    exact hQnotK ⟨τ₀ * μ, K.fixingSubgroup.mul_mem hτ₀K hμK, by
      rw [mul_smul, hμ, ← hQeq]⟩
  have hQiconj : SSGRoute.IsConjPlace k ((f i).1) A := ⟨galLift K σ, hAdef.symm⟩
  have hzero : ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ((f i).2) x + ((f j).2) x = 0 := by
    intro x hx
    have hpres := hf.2.2.2.2.2.2.1 j A hAmem x hx
    have hdatum : histDatum K y (fun l : Fin j => f l) A x
        = - ((f i).2) x - (2 : ZMod p)⁻¹ * y x := by
      unfold histDatum
      rw [Finset.sum_eq_single (⟨i, hij⟩ : Fin j) ?_ ?_]
      · simp only [correctionDatum, if_neg hQinotK, if_pos hQiconj]
      · intro m _ hm
        have hmval : (m : ℕ) ≠ i := fun h => hm (Fin.ext h)
        have hmnc : ¬ SSGRoute.IsConjPlace k ((f m).1) A := by
          intro hc
          have h1 : SSGRoute.IsConjPlace k ((f m).1) ((f i).1) :=
            SSGRoute.isConjPlace_trans hc (SSGRoute.isConjPlace_symm hQiconj)
          rcases lt_or_gt_of_ne hmval with hlt | hgt
          · exact hist_escapes_not_conj K N S y f hf hlt h1
          · exact hist_escapes_not_conj K N S y f hf hgt (SSGRoute.isConjPlace_symm h1)
        simp only [correctionDatum]
        rw [if_neg (by rintro ⟨μ, hμK, hμ⟩; exact hmnc ⟨μ, hμ⟩), if_neg hmnc]
      · intro hnot
        exact absurd (Finset.mem_univ (⟨i, hij⟩ : Fin j)) hnot
    rw [hpres, hdatum]
    ring
  have hxi : τ₀⁻¹ * τ * τ₀ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hτQ : τ • Q = Q := hτ.1
      show (τ₀⁻¹ * τ * τ₀) • A = A
      calc (τ₀⁻¹ * τ * τ₀) • A = τ₀⁻¹ • (τ • (τ₀ • A)) := by rw [mul_smul, mul_smul]
        _ = τ₀⁻¹ • (τ • Q) := by rw [hQeq]
        _ = τ₀⁻¹ • Q := by rw [hτQ]
        _ = A := by rw [hQeq, inv_smul_smul]
    · exact K.fixingSubgroup.mul_mem
        (K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hτ₀K) hτ.2) hτ₀K
  have hsum0 := hzero _ hxi
  have hi_conj : ((f i).2) τ = ((f i).2) (τ₀⁻¹ * τ * τ₀) :=
    (additive_conj_invariant K ((f i).2) (hf.2.2.2.2.2.1 i)
      (K.fixingSubgroup.inv_mem hτ₀K) hτ.2).symm
  have hj_conj : ((f j).2) τ = ((f j).2) (τ₀⁻¹ * τ * τ₀) :=
    (additive_conj_invariant K ((f j).2) (hf.2.2.2.2.2.1 j)
      (K.fixingSubgroup.inv_mem hτ₀K) hτ.2).symm
  rw [hi_conj, hj_conj, hsum0]

end Work.SSGRoute.ZDataMup
