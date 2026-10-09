import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
import Submission.NK.Ramification.exists_ramificationSubgroup_eq_bot
import Submission.NK.RamificationDeep.ramificationSubgroup_inf_fixingSubgroup
import Submission.NK.Ramification.ramificationSubgroup_succ_eq_of_uniformizer
import Submission.NK.RamificationDeep.lowerIndex_eq_mul_herbrand_of_tower_of_image
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The index identity in tower form: audit and vocabulary

This file is the audit companion of `NK.RamificationDeep.towerImage_card`.  It supplies

* the vocabulary in which the classical proof of Serre's index identity (Serre, *Local Fields*,
  IV §3, Props. 3, 7, 8, 9; equivalently Dalawat, arXiv:0903.2615, Lectures 15–16) is phrased in
  this workspace: the base valuation ring `𝔬 = A ∩ K = A.comap (algebraMap K L)`, the generating
  predicate `Generates K A ω` (`A = 𝔬[ω]`, Serre IV §2 Prop. 4), and the ramification level
  `auditLevel K A σ = min {n | σ ∉ G_n}` of an element of the decomposition subgroup;
* the *counting half* of the index identity, i.e. the derivation of the requested cardinality
  statement from the classical image identity `#π(G_n(L/K)) = #G_{⌊φ_{L/M}(n)⌋}(M/K)`.

The image identity itself needs the two classical inputs (`A = 𝔬[ω]`, `B = 𝔬[η]` — Serre IV §2
Prop. 4 — and the sum formula `i_{G/H}(s) = e_{L/M}^{-1} ∑_{σ ↦ s} i_G(σ)`, loc. cit. IV §3
Prop. 3), which are isolated as
`NK.RamificationAudit.card_map_restrictNormalHom_eq`.
-/

open scoped Pointwise

namespace NK.RamificationAudit

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The base valuation ring** `𝔬 = A ∩ K` of a valuation subring `A` of `L` over `K`. -/
def baseRing (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]
    (A : ValuationSubring L) : ValuationSubring K :=
  A.comap (algebraMap K L)

@[simp]
theorem mem_baseRing {A : ValuationSubring L} {x : K} :
    x ∈ baseRing K A ↔ algebraMap K L x ∈ A :=
  ValuationSubring.mem_comap

/-- The canonical ring homomorphism `𝔬 = A ∩ K → A`. -/
def baseToA (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]
    (A : ValuationSubring L) : ↥(baseRing K A) →+* ↥A where
  toFun k := ⟨algebraMap K L (k : K), (mem_baseRing.mp k.2)⟩
  map_one' := by ext; simp
  map_mul' := by intro a b; ext; simp
  map_zero' := by ext; simp
  map_add' := by intro a b; ext; simp

@[simp]
theorem baseToA_coe (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]
    (A : ValuationSubring L) (k : ↥(baseRing K A)) :
    ((baseToA K A k : ↥A) : L) = algebraMap K L (k : K) := rfl

/-- **Monogenicity predicate**: `A` is generated as a ring over `𝔬 = A ∩ K` by the single
element `ω` (Serre, *Local Fields*, IV §2 Prop. 4: `A = 𝔬[ω]`). -/
def Generates (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]
    (A : ValuationSubring L) (ω : ↥A) : Prop :=
  Subring.closure (Set.range (baseToA K A) ∪ {ω}) = ⊤

/-- **Monogenicity in polynomial form**: every element of `A` is a polynomial in `ω` with
coefficients in `𝔬 = A ∩ K`.  This is the form in which the classical argument
(Serre, *Local Fields*, IV §3, Cor. of Prop. 4) uses monogenicity. -/
def Generates' (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]
    (A : ValuationSubring L) (ω : ↥A) : Prop :=
  ∀ x : ↥A, ∃ p : Polynomial ↥(baseRing K A), p.eval₂ (baseToA K A) ω = x

/-- The closure form of monogenicity implies the polynomial form. -/
theorem Generates.generates' {A : ValuationSubring L} {ω : ↥A} (h : Generates K A ω) :
    Generates' K A ω := by
  intro x
  have hx : x ∈ Subring.closure (Set.range (baseToA K A) ∪ {ω}) := by rw [h]; trivial
  have hsub : Subring.closure (Set.range (baseToA K A) ∪ {ω}) ≤
      (Polynomial.eval₂RingHom (baseToA K A) ω).range := by
    apply Subring.closure_le.mpr
    intro y hy
    rcases hy with ⟨k, rfl⟩ | rfl
    · exact ⟨Polynomial.C k, by simp⟩
    · exact ⟨Polynomial.X, by simp⟩
  obtain ⟨p, hp⟩ := hsub hx
  exact ⟨p, hp⟩

/-- **The ramification level** of an element of the decomposition subgroup: the least `n` with
`σ ∉ G_n`; it is Serre's invariant `i_G(σ)` (so that `σ ∈ G_n ↔ n < auditLevel K A σ`). -/
noncomputable def auditLevel (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : ↥(A.decompositionSubgroup K)) : ℕ :=
  sInf {n : ℕ | σ ∉ NK.Ramification.ramificationSubgroup (K := K) A n}

variable {A : ValuationSubring L}

theorem auditLevel_spec (σ : ↥(A.decompositionSubgroup K))
    (h : ({n : ℕ | σ ∉ NK.Ramification.ramificationSubgroup (K := K) A n}).Nonempty) :
    σ ∉ NK.Ramification.ramificationSubgroup (K := K) A (auditLevel K A σ) :=
  Nat.sInf_mem h

/-- The defining property of the level: `σ ∈ G_n ↔ n < auditLevel K A σ`. -/
theorem mem_ramificationSubgroup_iff_lt_auditLevel
    (σ : ↥(A.decompositionSubgroup K))
    (h : ({n : ℕ | σ ∉ NK.Ramification.ramificationSubgroup (K := K) A n}).Nonempty) (n : ℕ) :
    σ ∈ NK.Ramification.ramificationSubgroup (K := K) A n ↔ n < auditLevel K A σ := by
  constructor
  · intro hn
    by_contra hcon
    simp only [not_lt] at hcon
    exact auditLevel_spec σ h
      (NK.Ramification.ramificationSubgroup_antitone A hcon hn)
  · intro hn
    by_contra hcon
    have hle : auditLevel K A σ ≤ n :=
      csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ hcon
    omega

/-- The level of `σ ≠ 1` is a genuine level when the filtration is eventually trivial. -/
theorem levelSet_nonempty
    (hN : ∃ N : ℕ, NK.Ramification.ramificationSubgroup (K := K) A N = ⊥)
    (σ : ↥(A.decompositionSubgroup K)) (hσ : σ ≠ 1) :
    ({n : ℕ | σ ∉ NK.Ramification.ramificationSubgroup (K := K) A n}).Nonempty := by
  obtain ⟨N, hN⟩ := hN
  exact ⟨N, by simpa [hN] using hσ⟩

/-- The eventual triviality of the filtration for a discrete valuation ring with finite
decomposition subgroup. -/
theorem exists_ramificationSubgroup_eq_bot_of_isDiscreteValuationRing
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [Finite ↥(A.decompositionSubgroup K)] :
    ∃ N : ℕ, NK.Ramification.ramificationSubgroup (K := K) A N = ⊥ :=
  NK.Ramification.exists_ramificationSubgroup_eq_bot (K := K) A


/-- **The `addVal` dictionary**: an element of a discrete valuation ring lies in the `n`-th power
of the maximal ideal exactly when its `addVal` is at least `n`.  This turns divisibility
statements about powers of `𝔪` into arithmetic in `ℕ∞`. -/
theorem mem_maximalIdeal_pow_iff_le_addVal (A : ValuationSubring L) [IsDiscreteValuationRing A]
    {n : ℕ} {x : ↥A} :
    x ∈ IsLocalRing.maximalIdeal A ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal A x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_eq_mul, mul_one]


/-! ## Structural consequences of the hypotheses of the index identity -/

/-- `hA : A.decompositionSubgroup K = ⊤` together with `[Finite]` and `[IsGalois K L]` forces
`L/K` to be finite-dimensional. -/
theorem finiteDimensional_of_decompositionSubgroup_eq_top (A : ValuationSubring L)
    [IsDiscreteValuationRing A] [IsGalois K L] [Finite ↥(A.decompositionSubgroup K)]
    (hA : A.decompositionSubgroup K = ⊤) : FiniteDimensional K L := by
  have h : Finite ↥(A.decompositionSubgroup K) := inferInstance
  rw [hA] at h
  haveI : Finite (L ≃ₐ[K] L) := Finite.of_equiv _ Subgroup.topEquiv.toEquiv
  exact IsGalois.finiteDimensional_of_finite K L

/-- An intermediate Galois subfield of a finite Galois extension is finite-dimensional over the
base field. -/
theorem finiteDimensional_intermediateField [IsGalois K L] (hfin : Finite (L ≃ₐ[K] L))
    (M : IntermediateField K L) [IsGalois K ↥M] : FiniteDimensional K ↥M := by
  haveI : Finite (↥M ≃ₐ[K] ↥M) :=
    Finite.of_surjective (AlgEquiv.restrictNormalHom (K₁ := L) ↥M)
      (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥M) L)
  exact IsGalois.finiteDimensional_of_finite K ↥M

end NK.RamificationAudit
