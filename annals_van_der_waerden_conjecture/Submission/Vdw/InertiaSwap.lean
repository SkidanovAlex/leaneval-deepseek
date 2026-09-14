import Mathlib
import Submission.Vdw.Contraction
import Submission.Vdw.GaloisTower
import Submission.Vdw.GaloisAction

open Polynomial
open scoped NumberField Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open Lean.Parser.Tactic in
macro "push_neg" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| push $cfg:optConfig Not $[$loc]?)

/-!
# The inertia-group transposition (step (c) of Case I)

This module proves, for an irreducible `p : ℚ[X]` whose root field
`K = AdjoinRoot p` has a rational prime `p₀` factoring with a *unique*
ramified prime `P` of ramification index `2` and inertia degree `1` (all
other primes over `p₀` unramified), that the Galois group `p.Gal` of the
splitting field contains an element acting on the roots as a transposition.

The mathematical content is the classical *cycle-type theorem of Hilbert
theory* (used in the proof of Proposition `valindcon` of Bhargava's paper):
for a prime `𝔓` of the splitting field `L` over `P`, the inertia group
`I(𝔓 | p₀)` acts on the `n` embeddings `σ : K ↪ L` with orbit sizes equal
to the ramification indices `e(σ⁻¹𝔓 | p₀)`; for the local structure above,
this gives two roots in one 2-orbit and all others fixed, so any nontrivial
inertia element is a transposition.

**Status: PROVED (0 sorries).**  Structure of the proof:

1. **`hilbertCore`** (via the relative-vs-absolute inertia cardinality):
   with `H := embStabilizer p ≅ Gal(L/K)`, the inertia subgroup of `H` at
   `𝔓` (relative to the intermediate field `K`) has the same cardinality as
   the full inertia subgroup of `p.Gal` exactly when the contraction
   `Q = 𝔓 ∩ 𝒪 K` is *unramified* over `p₀` (ramification indices equal by
   the tower formula `e(𝔓|p₀) = e(Q|p₀)·e(𝔓|Q)`).
2. **`hilbertCore`** — unramified contractions are fixed: if
   `e(Q | p₀) = 1`, then every element of `I(𝔓 | p₀)` fixes `K` (embedded
   canonically) pointwise, i.e. `𝔓.inertia p.Gal ≤ embStabilizer p`.
3. **`inertia_fixes_emb_of_unramified`** — by conjugation (`σ = g₀ ∘ ι`,
   `g₀⁻¹ I(𝔓) g₀ = I(g₀⁻¹𝔓)`), every `τ ∈ I(𝔓 | p₀)` fixes every
   embedding `σ` whose contraction `Q(σ) = σ⁻¹𝔓` is unramified.
4. The fiber `F_P = {σ | σ⁻¹𝔓 = P}` has `e_P·f_P = 2` elements
   (`Contraction.fiberCard`), is invariant under `I(𝔓|p₀)`, and any
   nontrivial `τ ∈ I(𝔓|p₀)` (which exists since `|I(𝔓|p₀)| = e(𝔓|p₀) ≥
   e(P|p₀) = 2`) must swap them (else it fixes every embedding, hence every
   root, hence is trivial by `Polynomial.Gal.ext`).
5. The Fin-level conclusion transports the embedding swap through the three
   conjugacies of the canonical root representation: `galFinHom` is built
   from `galRootPerm`, which by Mathlib `smul_def` is the conjugation of the
   *plain* action `auxRootPerm` (application) by `rootsEquivRoots`, which
   itself is the conjugation of the embedding permutation by
   `embEquivRootSet`; `permCongr_swap` carries the swap along each step, so
   `galFinHom p hsep τ` is an explicit swap of two indices (see the
   discussion of the canonical action at step (10) of the main theorem).
-/

namespace Submission.Vdw

noncomputable section

open Polynomial

/-- The local structure hypothesis of step (c), for an irreducible
`p : ℚ[X]`: the rational prime `p₀` has in the root field
`K = AdjoinRoot p` exactly one ramified prime `P`, with ramification index
`2` and inertia degree `1`, and every other prime of `K` over `p₀` is
unramified (`ramificationIdx = 1`).  (This is the `padicValNat = 1` local
structure produced by
`DifferentValuation.ramified_prime_of_padicValNat_eq_one`, instantiated in
`CaseI.fieldDisc_val_one_local_structure`.) -/
def RamifiedPrimeStructure (p : ℚ[X]) [Fact (Irreducible p)] (p0 : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 (AdjoinRoot p)), P.IsMaximal ∧
    P.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)) ∧
    P.ramificationIdx ℤ = 2 ∧ P.inertiaDeg ℤ = 1 ∧
    ∀ Q : Ideal (𝓞 (AdjoinRoot p)), Q.IsMaximal →
      Q.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)) → Q ≠ P →
      Q.ramificationIdx ℤ = 1

/-- Two subgroups of a finite group, one contained in the other with the same
(finite) cardinality, are equal. -/
private lemma subgroup_eq_of_le_of_card_eq {G : Type*} [Group G] [Fintype G]
    {H K : Subgroup G} (hle : H ≤ K) (hcard : Nat.card H = Nat.card K) : H = K := by
  classical
  apply le_antisymm hle
  intro k hk
  let i : H → K := fun h => ⟨(h : G), hle h.2⟩
  have hinj : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : K => (z : G)) h
  have hF : Fintype.card H = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hsurj : Function.Surjective i := by
    intro b
    by_contra hb
    have hlt := Fintype.card_lt_of_injective_of_notMem i hinj hb
    have : Fintype.card H < Fintype.card H := by
      calc
        Fintype.card H < Fintype.card K := hlt
        _ = Fintype.card H := hF.symm
    omega
  rcases hsurj ⟨k, hk⟩ with ⟨h, hh⟩
  have hk' : (h : G) = k := congrArg (fun z : K => (z : G)) hh
  exact hk'.symm ▸ h.2

section HilbertCore

/-- An inertia element stabilizes the prime ideal: if `g` acts trivially
modulo `𝔓`, then `g • 𝔓 = 𝔓`. -/
lemma inertia_smul_eq (p : ℚ[X]) [Fact (Irreducible p)]
    (𝔓 : Ideal (𝓞 p.SplittingField)) (g : p.Gal)
    (hg : g ∈ 𝔓.inertia p.Gal) : g • 𝔓 = 𝔓 := by
  classical
  let C := 𝓞 p.SplittingField
  apply le_antisymm
  · -- g • 𝔓 ≤ 𝔓
    intro x hx
    have hx' : g⁻¹ • x ∈ 𝔓 := (Ideal.mem_pointwise_smul_iff_inv_smul_mem (a := g)).mp hx
    have hdiff : g • (g⁻¹ • x) - g⁻¹ • x ∈ 𝔓 := hg (g⁻¹ • x)
    have hdiff' : x - g⁻¹ • x ∈ 𝔓 := by simpa using hdiff
    have hsum : (x - g⁻¹ • x) + g⁻¹ • x ∈ 𝔓 := add_mem hdiff' hx'
    rw [← sub_add_cancel x (g⁻¹ • x)]
    exact hsum
  · -- 𝔓 ≤ g • 𝔓
    intro x hx
    have hginv : g⁻¹ ∈ 𝔓.inertia p.Gal := (𝔓.inertia p.Gal).inv_mem hg
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hdiff : g⁻¹ • x - x ∈ 𝔓 := hginv x
    have hsum : (g⁻¹ • x - x) + x ∈ 𝔓 := add_mem hdiff hx
    rw [← sub_add_cancel (g⁻¹ • x) x]
    exact hsum

/-- **Hilbert core lemma.**  Let `p` be irreducible, `𝔓` a prime of the
splitting-field integers over `p₀`, whose contraction to the root field
`K` (through the canonical embedding) is the prime `Q`.  If `Q` is
*unramified* over `p₀` (`ramificationIdx ℤ = 1`), then the inertia group of
`𝔓` over `ℚ` fixes the canonically embedded `K` pointwise — equivalently
`𝔓.inertia p.Gal ≤ embStabilizer p`.

Proof: `|𝔓.inertia p.Gal| = e(𝔓|p₀) = e(Q|p₀)·e(𝔓|Q) = e(𝔓|Q)` (Mathlib
`card_inertia_eq_ramificationIdxIn` + the tower
`ramificationIdx_tower_intRing`), and the relative inertia inside
`embStabilizer p ≅ Gal(L/K)` has the same order `e(𝔓|Q)` (same theorem
with base `𝓞K`, transported through the automorphism bijection); with the
containment `𝔓.inertia (embStabilizer p) ⊆ 𝔓.inertia p.Gal` this forces
equality, so `𝔓.inertia p.Gal ⊆ embStabilizer p`. -/
theorem hilbertCore (p : ℚ[X]) [Fact (Irreducible p)]
    (p0 : ℕ) (hp0 : Nat.Prime p0)
    (𝔓 : Ideal (𝓞 p.SplittingField)) (h𝔓1 : 𝔓.IsPrime)
    (h𝔓2 : 𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)))
    (Q : Ideal (𝓞 (AdjoinRoot p))) (hQ1 : Q.IsPrime)
    (hQ2 : Q.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)))
    (h𝔓Q : pullbackIdeal p (kpolyAlgEmb p) 𝔓 = Q)
    (he1 : Q.ramificationIdx ℤ = 1) :
    𝔓.inertia p.Gal ≤ embStabilizer p := by
  classical
  let K : Type := AdjoinRoot p
  let L : Type := p.SplittingField
  let B : Type := 𝓞 (AdjoinRoot p)
  let C : Type := 𝓞 p.SplittingField
  let pZ : Ideal ℤ := Ideal.span ({(p0 : ℤ)} : Set ℤ)
  letI : Algebra K L := kpolyAlgebra p
  haveI : IsScalarTower ℚ K L := kpoly_tower p
  haveI : IsGalois K L := kpoly_isGalois p
  haveI : IsGalois ℚ L := spl_galois p
  haveI hQZp : pZ.IsPrime := by
    simpa [pZ] using Commons.RingTheory.Ideal.span_singleton_prime_int hp0
  haveI : Q.IsPrime := hQ1
  haveI : Q.LiesOver pZ := hQ2
  haveI : 𝔓.IsPrime := h𝔓1
  haveI : 𝔓.LiesOver pZ := h𝔓2
  have halg : (algebraMap B C) = intRingMap p (kpolyAlgEmb p) := by rfl
  have hunder : 𝔓.under B = Q := (pullbackIdeal_eq_iff_under p halg 𝔓 Q).mp h𝔓Q
  haveI : 𝔓.LiesOver Q := ⟨hunder.symm⟩
  haveI : IsGaloisGroup p.Gal ℤ C :=
    Commons.NumberTheory.NumberField.ringOfIntegers_isGaloisGroup L
  haveI : IsGaloisGroup Gal(L/K) B C := inferInstance
  -- (1) order of the absolute inertia = e(𝔓 | p₀)
  have hcardG : Nat.card (𝔓.inertia p.Gal) = 𝔓.ramificationIdx ℤ := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (R := ℤ) (S := C) (G := p.Gal)
      (p := pZ) (P := 𝔓)]
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p := pZ) (P := 𝔓) (G := p.Gal)]
  -- (2) order of the relative inertia over K = e(𝔓 | Q)
  have hcardK : Nat.card (𝔓.inertia Gal(L/K)) = 𝔓.ramificationIdx B := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (R := B) (S := C) (G := Gal(L/K))
      (p := Q) (P := 𝔓)]
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p := Q) (P := 𝔓) (G := Gal(L/K))]
  -- (3) tower: e(𝔓|p₀) = e(Q|p₀)·e(𝔓|Q)
  have hT : 𝔓.ramificationIdx ℤ = Q.ramificationIdx ℤ * 𝔓.ramificationIdx B := by
    exact ramificationIdx_tower_intRing p p0 hp0 Q 𝔓
  -- (4) transport: |𝔓.inertia (embStabilizer p)| = |𝔓.inertia Gal(L/K)|,
  --     via the automorphism bijection prom/restr (embStabilizer ≅ Gal(L/K))
  have htrans : Nat.card (𝔓.inertia (embStabilizer p)) =
      Nat.card (𝔓.inertia Gal(L/K)) := by
    -- promotion: an automorphism over ℚ fixing K pointwise is one over K
    let prom : embStabilizer p → (L ≃ₐ[K] L) := fun g => by
      let φ := g.1
      have hιk (x : K) : kpolyAlgEmb p x = kpolyEmb p x := by
        have hk : (kpolyAlgEmb p).toRingHom = kpolyEmb p := by
          dsimp [kpolyAlgEmb, kpolyEmb]
        exact (congrArg (fun f : K →+* L => f x) hk)
      have hfix : ∀ k : K, φ (algebraMap K L k) = algebraMap K L k := by
        intro k
        have hh : φ (kpolyAlgEmb p k) = kpolyAlgEmb p k := by
          have hh0 := congrArg (fun f : K →ₐ[ℚ] L => f k) g.2
          change ((g.1).toAlgHom.comp (kpolyAlgEmb p)) k = (kpolyAlgEmb p) k
          exact hh0
        change φ (kpolyEmb p k) = kpolyEmb p k
        rw [← hιk k]
        exact hh
      refine {
        toEquiv := (φ : L ≃ L)
        map_mul' := φ.map_mul'
        map_add' := φ.map_add'
        commutes' := hfix }
    -- restriction: an automorphism over K is one over ℚ fixing K pointwise
    have hιk' (x : K) : kpolyAlgEmb p x = kpolyEmb p x := by
      have hk : (kpolyAlgEmb p).toRingHom = kpolyEmb p := by
        dsimp [kpolyAlgEmb, kpolyEmb]
      exact (congrArg (fun f : K →+* L => f x) hk)
    let restr : (L ≃ₐ[K] L) → embStabilizer p := fun e => ⟨e.restrictScalars ℚ, by
      apply AlgHom.ext
      intro k
      change (e.restrictScalars ℚ) (kpolyAlgEmb p k) = kpolyAlgEmb p k
      rw [hιk' k]
      change (e.restrictScalars ℚ) (algebraMap K L k) = algebraMap K L k
      simpa using (e.commutes k)⟩
    have hpinv : Function.LeftInverse restr prom := by
      intro g
      apply Subtype.ext
      apply AlgEquiv.ext
      intro x
      rfl
    have hrinv : Function.RightInverse restr prom := by
      intro e
      apply AlgEquiv.ext
      intro x
      rfl
    -- membership transport: h ∈ inertia(H) iff prom h ∈ inertia(Gal(L/K)),
    -- since prom h acts on the integers exactly as h does.
    have hmem (h : embStabilizer p) :
        h ∈ 𝔓.inertia (embStabilizer p) ↔ prom h ∈ 𝔓.inertia Gal(L/K) := by
      constructor
      · intro hh x
        -- prom h • x - x ∈ 𝔓; equals h • x - x
        have : (prom h • x : C) = h • x := by
          apply Subtype.ext
          rfl
        rw [this]
        exact hh x
      · intro hh x
        have : (h • x : C) = prom h • x := by
          apply Subtype.ext
          rfl
        rw [this]
        exact hh x
    -- equivalence of the subtype types
    apply Nat.card_congr
    refine {
      toFun := fun h => ⟨prom h.1, (hmem h.1).mp h.2⟩
      invFun := fun g => ⟨restr g.1, (hmem (restr g.1)).mpr g.2⟩
      left_inv := by
        intro h
        apply Subtype.ext
        exact hpinv h.1
      right_inv := by
        intro g
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        rfl }
  -- (5) containment: image of 𝔓.inertia (embStabilizer p) ⊆ 𝔓.inertia p.Gal
  have hIncl : ((𝔓.inertia (embStabilizer p)).map (embStabilizer p).subtype : Set p.Gal) ⊆
      (𝔓.inertia p.Gal : Set p.Gal) := by
    intro g hg
    rcases hg with ⟨h, hh, rfl⟩
    exact (Ideal.coe_mem_inertia (I := 𝔓) (H := embStabilizer p) (σ := h)).mp hh
  -- (6) orders equal
  have hcardEq : Nat.card (𝔓.inertia p.Gal) = Nat.card (𝔓.inertia (embStabilizer p)) := by
    calc
      Nat.card (𝔓.inertia p.Gal) = 𝔓.ramificationIdx ℤ := hcardG
      _ = Q.ramificationIdx ℤ * 𝔓.ramificationIdx B := hT
      _ = 𝔓.ramificationIdx B := by rw [he1, one_mul]
      _ = Nat.card (𝔓.inertia Gal(L/K)) := hcardK.symm
      _ = Nat.card (𝔓.inertia (embStabilizer p)) := htrans.symm
  -- (7) equality of the subgroups of p.Gal: I_G = map(I_H)
  haveI : Fintype p.Gal := inferInstance
  have hcardMap : Fintype.card ((𝔓.inertia (embStabilizer p)).map (embStabilizer p).subtype) =
      Fintype.card (𝔓.inertia (embStabilizer p)) := by
    rw [← Nat.card_eq_fintype_card]
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.equivMapOfInjective (𝔓.inertia (embStabilizer p))
      (embStabilizer p).subtype (by intro a b h; exact Subtype.ext h)).toEquiv.symm
  have hcardEqF : Fintype.card (𝔓.inertia p.Gal) =
      Fintype.card ((𝔓.inertia (embStabilizer p)).map (embStabilizer p).subtype) := by
    calc
      Fintype.card (𝔓.inertia p.Gal) = Nat.card (𝔓.inertia p.Gal) :=
        (Nat.card_eq_fintype_card (α := 𝔓.inertia p.Gal)).symm
      _ = Nat.card (𝔓.inertia (embStabilizer p)) := hcardEq
      _ = Fintype.card (𝔓.inertia (embStabilizer p)) :=
        Nat.card_eq_fintype_card (α := 𝔓.inertia (embStabilizer p))
      _ = Fintype.card ((𝔓.inertia (embStabilizer p)).map (embStabilizer p).subtype) :=
        hcardMap.symm
  have hle' : (𝔓.inertia (embStabilizer p)).map (embStabilizer p).subtype ≤
      𝔓.inertia p.Gal := by
    exact hIncl
  have hcardNat : Nat.card ((𝔓.inertia (embStabilizer p)).map (embStabilizer p).subtype) =
      Nat.card (𝔓.inertia p.Gal) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hcardEqF.symm
  have hEqSub : 𝔓.inertia p.Gal =
      (𝔓.inertia (embStabilizer p)).map (embStabilizer p).subtype := by
    exact (subgroup_eq_of_le_of_card_eq (G := p.Gal)
      (H := (𝔓.inertia (embStabilizer p)).map (embStabilizer p).subtype)
      (K := 𝔓.inertia p.Gal) hle' hcardNat).symm
  -- (8) conclusion: inertia fixes ι(K) pointwise
  intro g hg
  rw [hEqSub] at hg
  rcases (Subgroup.mem_map.mp hg) with ⟨h, hh, rfl⟩
  exact h.2

end HilbertCore

section ConjugationFacts

/-- Conjugating an inertia element by `g` gives an inertia element at the
conjugate prime: `g⁻¹·τ·g ∈ I(g⁻¹𝔓 | p₀)` whenever `τ ∈ I(𝔓 | p₀)`. -/
lemma mem_inertia_conj (p : ℚ[X]) [Fact (Irreducible p)]
    (𝔓 : Ideal (𝓞 p.SplittingField)) (g τ : p.Gal)
    (hτ : τ ∈ 𝔓.inertia p.Gal) :
    g⁻¹ * τ * g ∈ (g⁻¹ • 𝔓).inertia p.Gal := by
  classical
  intro x
  -- goal: (g⁻¹τg) • x - x ∈ g⁻¹ • 𝔓; equivalently g • ((g⁻¹τg)•x - x) ∈ 𝔓
  have hiff : (g⁻¹ * τ * g) • x - x ∈ g⁻¹ • 𝔓 ↔ g • ((g⁻¹ * τ * g) • x - x) ∈ 𝔓 := by
    simpa [inv_inv] using (Ideal.mem_pointwise_smul_iff_inv_smul_mem (a := g⁻¹)
      (S := 𝔓) (x := (g⁻¹ * τ * g) • x - x))
  exact hiff.mpr (by
    have h₁ : g • ((g⁻¹ * τ * g) • x) = τ • (g • x) := by
      calc
        g • ((g⁻¹ * τ * g) • x) = (g * (g⁻¹ * τ * g)) • x := (mul_smul g (g⁻¹ * τ * g) x).symm
        _ = (τ * g) • x := by
          congr 1
          simp [mul_assoc]
        _ = τ • (g • x) := mul_smul τ g x
    rw [smul_sub, h₁]
    exact hτ (g • x))

theorem inertia_fixes_emb_of_unramified (p : ℚ[X]) [Fact (Irreducible p)]
    (p0 : ℕ) (hp0 : Nat.Prime p0)
    (𝔓 : Ideal (𝓞 p.SplittingField)) (h𝔓1 : 𝔓.IsPrime)
    (h𝔓2 : 𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)))
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField)
    (τ : p.Gal) (hτ : τ ∈ 𝔓.inertia p.Gal)
    (hQ1 : (pullbackIdeal p σ 𝔓).IsPrime)
    (hQ2 : (pullbackIdeal p σ 𝔓).LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)))
    (he1 : (pullbackIdeal p σ 𝔓).ramificationIdx ℤ = 1) :
    galSmulEmb p τ σ = σ := by
  classical
  -- σ = g₀ ∘ ι
  obtain ⟨g₀, hg₀⟩ := exists_gal_of_embedding p σ
  -- τ' := g₀⁻¹ τ g₀ ∈ I(g₀⁻¹𝔓 | p₀)
  let τ' : p.Gal := g₀⁻¹ * τ * g₀
  have hτ' : τ' ∈ (g₀⁻¹ • 𝔓).inertia p.Gal := by
    simpa [τ'] using mem_inertia_conj p 𝔓 g₀ τ hτ
  -- contraction of g₀⁻¹𝔓 through ι is Q = pullback σ 𝔓
  have hcontr : pullbackIdeal p (kpolyAlgEmb p) (g₀⁻¹ • 𝔓) = pullbackIdeal p σ 𝔓 := by
    calc
      pullbackIdeal p (kpolyAlgEmb p) (g₀⁻¹ • 𝔓)
          = pullbackIdeal p (galSmulEmb p g₀ (kpolyAlgEmb p)) 𝔓 := by
            rw [pullbackIdeal_galSmulEmb p g₀ 𝔓]
            rw [comap_galIntMap_eq_smul_inv p g₀ 𝔓]
      _ = pullbackIdeal p σ 𝔓 := by rw [hg₀]
  haveI h𝔓1' : 𝔓.IsPrime := h𝔓1
  have h𝔓'1 : (g₀⁻¹ • 𝔓).IsPrime := by
    infer_instance
  have h𝔓'2 : (g₀⁻¹ • 𝔓).LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)) := by
    haveI h𝔓2' : 𝔓.LiesOver (Ideal.span ({(p0 : ℤ)} : Set ℤ)) := h𝔓2
    constructor
    calc
      (Ideal.span ({(p0 : ℤ)} : Set ℤ)) = 𝔓.under ℤ := by
        exact Ideal.over_def 𝔓 (Ideal.span ({(p0 : ℤ)} : Set ℤ))
      _ = (g₀⁻¹ • 𝔓).under ℤ := by
        exact (Ideal.under_smul (g := g₀⁻¹) (A := ℤ) (B := 𝓞 p.SplittingField)
          (P := 𝔓)).symm
  -- hilbertCore at g₀⁻¹𝔓
  have hcore := hilbertCore p p0 hp0 (g₀⁻¹ • 𝔓) h𝔓'1 h𝔓'2 (pullbackIdeal p σ 𝔓) hQ1 hQ2
    hcontr he1
  have hτ'H : τ' ∈ embStabilizer p := hcore hτ'
  -- τ'∘ι = ι, i.e. g₀⁻¹τg₀ fixes ι: hence τ fixes g₀∘ι = σ
  have hgt : τ * g₀ = g₀ * τ' := by
    dsimp [τ']
    simp [mul_assoc]
  apply emb_ext
  calc
    embRoot p (galSmulEmb p τ σ) =
        embRoot p (galSmulEmb p τ (galSmulEmb p g₀ (kpolyAlgEmb p))) := by rw [hg₀]
    _ = embRoot p (galSmulEmb p (τ * g₀) (kpolyAlgEmb p)) := by
      rw [galSmulEmb_mul p τ g₀ (kpolyAlgEmb p)]
    _ = embRoot p (galSmulEmb p (g₀ * τ') (kpolyAlgEmb p)) := by rw [hgt]
    _ = embRoot p (galSmulEmb p g₀ (galSmulEmb p τ' (kpolyAlgEmb p))) := by
      rw [galSmulEmb_mul p g₀ τ' (kpolyAlgEmb p)]
    _ = embRoot p (galSmulEmb p g₀ (kpolyAlgEmb p)) := by
      rw [(mem_embStabilizer p τ').mp hτ'H]
    _ = embRoot p σ := by rw [hg₀]

end ConjugationFacts

section AssemblyHelpers

/-- A type of cardinality two contains two distinct points covering it. -/
lemma two_of_card_two {α : Type*} [Fintype α] (hα : Fintype.card α = 2) :
    ∃ a b : α, a ≠ b ∧ ∀ x : α, x = a ∨ x = b := by
  classical
  let e : α ≃ Fin 2 := Fintype.equivFinOfCardEq hα
  let a : α := e.symm (0 : Fin 2)
  let b : α := e.symm (1 : Fin 2)
  refine ⟨a, b, ?_, ?_⟩
  · intro hab
    have h01 : (0 : Fin 2) = 1 := e.symm.injective hab
    norm_num at h01
  · intro x
    have hx : (e x : Fin 2) = 0 ∨ (e x : Fin 2) = 1 := by
      have hv : (e x : Fin 2).val = 0 ∨ (e x : Fin 2).val = 1 := by omega
      rcases hv with hv0 | hv1
      · left; apply Fin.ext; exact hv0
      · right; apply Fin.ext; exact hv1
    rcases hx with h | h
    · left
      calc
        x = e.symm (e x) := (Equiv.symm_apply_apply e x).symm
        _ = e.symm (0 : Fin 2) := by rw [h]
        _ = a := rfl
    · right
      calc
        x = e.symm (e x) := (Equiv.symm_apply_apply e x).symm
        _ = e.symm (1 : Fin 2) := by rw [h]
        _ = b := rfl

/-- A finite set of cardinality two consists of two distinct points and
contains nothing else. -/
lemma set_pair_of_ncard_two {α : Type*} [Fintype α] (F : Set α) (hF : F.ncard = 2) :
    ∃ a b : α, a ∈ F ∧ b ∈ F ∧ a ≠ b ∧ ∀ x : α, x ∈ F → x = a ∨ x = b := by
  classical
  haveI : Fintype {x : α // x ∈ F} := inferInstance
  have hcard : Fintype.card {x : α // x ∈ F} = 2 := by
    rw [← Nat.card_eq_fintype_card]
    rw [← Commons.Data.Set.ncard_eq_natCard F]
    exact hF
  obtain ⟨a0, b0, hab, hcov⟩ := two_of_card_two (α := {x : α // x ∈ F}) hcard
  refine ⟨a0.1, b0.1, a0.2, b0.2, ?_, ?_⟩
  · intro h; exact hab (by apply Subtype.ext; exact h)
  · intro x hx
    rcases hcov ⟨x, hx⟩ with h | h
    · left; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val h

/-- An embedding's contraction through the composed embedding:
`pullback (τ∘σ) 𝔓 = pullback σ (comap (galIntMap τ) 𝔓)`. -/
theorem pullbackIdeal_comp (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) (τ : p.Gal)
    (𝔓 : Ideal (𝓞 p.SplittingField)) :
    pullbackIdeal p (galSmulEmb p τ σ) 𝔓 =
      pullbackIdeal p σ (Ideal.comap (galIntMap p τ) 𝔓) := by
  classical
  rw [pullbackIdeal, pullbackIdeal, Ideal.comap_comap]
  apply congrArg (fun f : (𝓞 (AdjoinRoot p)) →+* (𝓞 p.SplittingField) => Ideal.comap f 𝔓)
  ext x
  rfl

theorem pullbackIdeal_comp_smul (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) (τ : p.Gal)
    (𝔓 : Ideal (𝓞 p.SplittingField)) :
    pullbackIdeal p (galSmulEmb p τ σ) 𝔓 = pullbackIdeal p σ (τ⁻¹ • 𝔓) := by
  rw [pullbackIdeal_comp p σ τ 𝔓]
  rw [comap_galIntMap_eq_smul_inv p τ 𝔓]

/-- The action of a Galois element on embeddings is injective. -/
theorem galSmulEmb_injective (p : ℚ[X]) [Fact (Irreducible p)] (τ : p.Gal) :
    Function.Injective (galSmulEmb p τ) := by
  intro σ₁ σ₂ h
  have hL : galSmulEmb p τ⁻¹ (galSmulEmb p τ σ₁) = σ₁ := by
    calc
      galSmulEmb p τ⁻¹ (galSmulEmb p τ σ₁) = galSmulEmb p (τ⁻¹ * τ) σ₁ := by
        rw [galSmulEmb_mul p τ⁻¹ τ σ₁]
      _ = galSmulEmb p 1 σ₁ := by simp
      _ = σ₁ := galSmulEmb_one p σ₁
  have hR : galSmulEmb p τ⁻¹ (galSmulEmb p τ σ₂) = σ₂ := by
    calc
      galSmulEmb p τ⁻¹ (galSmulEmb p τ σ₂) = galSmulEmb p (τ⁻¹ * τ) σ₂ := by
        rw [galSmulEmb_mul p τ⁻¹ τ σ₂]
      _ = galSmulEmb p 1 σ₂ := by simp
      _ = σ₂ := galSmulEmb_one p σ₂
  calc
    σ₁ = galSmulEmb p τ⁻¹ (galSmulEmb p τ σ₁) := hL.symm
    _ = galSmulEmb p τ⁻¹ (galSmulEmb p τ σ₂) := by rw [h]
    _ = σ₂ := hR

theorem smul_fix_all_eq_one (p : ℚ[X]) [Fact (Irreducible p)] (τ : p.Gal)
    (hfix : ∀ σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField, galSmulEmb p τ σ = σ) : τ = 1 := by
  classical
  -- two Galois elements are equal iff they agree on all roots (Gal.ext)
  apply Polynomial.Gal.ext
  intro x hx
  -- build the embedding of the root x and apply hfix
  have hx' : aeval (x : p.SplittingField) p = 0 := (Polynomial.mem_rootSet.mp hx).2
  let σₓ : AdjoinRoot p →ₐ[ℚ] p.SplittingField := rootEmb p (x : p.SplittingField) hx'
  have hroot : embRoot p σₓ = (x : p.SplittingField) := embRoot_rootEmb p (x : p.SplittingField) hx'
  have hτσ : galSmulEmb p τ σₓ = σₓ := hfix σₓ
  calc
    τ (x : p.SplittingField) = τ (embRoot p σₓ) := by rw [hroot]
    _ = embRoot p (galSmulEmb p τ σₓ) := by rw [embRoot_galSmulEmb]
    _ = embRoot p σₓ := by rw [hτσ]
    _ = (x : p.SplittingField) := hroot

end AssemblyHelpers

/-- The plain (value-application) action of a Galois element on the roots,
as a permutation of the root set. -/
noncomputable def auxRootPerm (p : ℚ[X]) (τ : p.Gal) : Equiv.Perm (p.rootSet p.SplittingField) :=
  @MulAction.toPermHom p.Gal (p.rootSet p.SplittingField) _ (Polynomial.Gal.galActionAux p) τ

/-- The plain action applies the field automorphism to the root value. -/
lemma auxRootPerm_apply_val (p : ℚ[X]) [Fact (Irreducible p)] (τ : p.Gal)
    (x : p.rootSet p.SplittingField) :
    (((auxRootPerm p τ) x : p.rootSet p.SplittingField) : p.SplittingField) = τ (x : p.SplittingField) := by
  dsimp [auxRootPerm]
  rfl

/-- The canonical Galois action on the roots is the conjugation of the plain
action by the (possibly nontrivial) reindexing equivalence `rootsEquivRoots`
between the splitting field and itself (definitional, Mathlib `smul_def`). -/
lemma galRootPerm_eq_conj (p : ℚ[X]) [Fact (Irreducible p)]
    (hF : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)) (τ : p.Gal) :
    galRootPerm p τ = Equiv.permCongr (Polynomial.Gal.rootsEquivRoots p p.SplittingField)
      (auxRootPerm p τ) := by
  classical
  letI := hF
  ext x
  rfl

/-- The plain action agrees with the embedding action under the root-set
identification. -/
lemma auxRootPerm_eq_emb (p : ℚ[X]) [Fact (Irreducible p)] (τ : p.Gal)
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) :
    auxRootPerm p τ (embEquivRootSet p σ) = embEquivRootSet p (galSmulEmb p τ σ) := by
  apply Subtype.ext
  calc
    (((auxRootPerm p τ (embEquivRootSet p σ) : p.rootSet p.SplittingField) : p.SplittingField))
        = τ ((embEquivRootSet p σ : p.rootSet p.SplittingField) : p.SplittingField) :=
          auxRootPerm_apply_val p τ (embEquivRootSet p σ)
    _ = τ (embRoot p σ) := by rfl
    _ = embRoot p (galSmulEmb p τ σ) := by rw [embRoot_galSmulEmb]
    _ = ((embEquivRootSet p (galSmulEmb p τ σ) : p.rootSet p.SplittingField) : p.SplittingField) := by rfl

section MainTheorem

/-- **Main theorem (step (c), generic form).**  For an irreducible `p : ℚ[X]`
whose root field has the `RamifiedPrimeStructure` at a prime `p₀` (a unique
ramified prime `P` over `p₀`, with `e = 2`, `f = 1`, all other primes
unramified), the Galois group of the splitting field contains an element
acting on the roots (`galFinHom p`) as a transposition. -/
theorem exists_isSwap_of_ramifiedPrimeStructure (p : ℚ[X]) [Fact (Irreducible p)]
    (p0 : ℕ) (hp0 : Nat.Prime p0) (hR : RamifiedPrimeStructure p p0) :
    ∃ τ : p.Gal, ((galFinHom p (separable_of_irreducible_rat Fact.out)) τ).IsSwap := by
  classical
  rcases hR with ⟨P, hPmax, hPover, heP, hfP, hQrest⟩
  let K : Type := AdjoinRoot p
  let L : Type := p.SplittingField
  let B : Type := 𝓞 (AdjoinRoot p)
  let C : Type := 𝓞 p.SplittingField
  let pZ : Ideal ℤ := Ideal.span ({(p0 : ℤ)} : Set ℤ)
  letI : Algebra K L := kpolyAlgebra p
  haveI : IsScalarTower ℚ K L := kpoly_tower p
  haveI : IsGalois K L := kpoly_isGalois p
  haveI : IsGalois ℚ L := spl_galois p
  haveI hPZp : pZ.IsPrime := by
    simpa [pZ] using Commons.RingTheory.Ideal.span_singleton_prime_int hp0
  haveI : P.IsMaximal := hPmax
  haveI : P.LiesOver pZ := hPover
  haveI : Algebra.IsIntegral B C := inferInstance
  haveI : FaithfulSMul B C := inferInstance
  -- a prime 𝔓 of the splitting-field integers over P
  have hnonempty : Nonempty (P.primesOver C) := by infer_instance
  let 𝔓0 : P.primesOver C := Classical.choice hnonempty
  let 𝔓 : Ideal C := 𝔓0.1
  have h𝔓1 : 𝔓.IsPrime := 𝔓0.2.1
  have h𝔓rel : 𝔓.LiesOver P := 𝔓0.2.2
  haveI h𝔓1' : 𝔓.IsPrime := h𝔓1
  haveI h𝔓rel' : 𝔓.LiesOver P := h𝔓rel
  haveI h𝔓2 : 𝔓.LiesOver pZ := by
    exact Ideal.LiesOver.trans (𝔓 := 𝔓) (P := P) (p := pZ)
  have halg : (algebraMap B C) = intRingMap p (kpolyAlgEmb p) := by rfl
  have h𝔓Q : pullbackIdeal p (kpolyAlgEmb p) 𝔓 = P := by
    apply (pullbackIdeal_eq_iff_under p halg 𝔓 P).mpr
    exact h𝔓rel.over.symm
  haveI : IsGaloisGroup p.Gal ℤ C :=
    Commons.NumberTheory.NumberField.ringOfIntegers_isGaloisGroup L
  haveI : IsGaloisGroup Gal(L/K) B C := inferInstance
  -- (1) the inertia group at 𝔓 over p₀ is nontrivial
  have hcardI : 2 ≤ Nat.card (𝔓.inertia p.Gal) := by
    have hcardG : Nat.card (𝔓.inertia p.Gal) = 𝔓.ramificationIdx ℤ := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (R := ℤ) (S := C) (G := p.Gal)
        (p := pZ) (P := 𝔓)]
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p := pZ) (P := 𝔓) (G := p.Gal)]
    have hT : 𝔓.ramificationIdx ℤ = P.ramificationIdx ℤ * 𝔓.ramificationIdx B := by
      exact ramificationIdx_tower_intRing p p0 hp0 P 𝔓
    have hpos : 0 < 𝔓.ramificationIdx B := by
      exact Ideal.ramificationIdx_pos 𝔓 B
    rw [hcardG, hT, heP]
    omega
  haveI : Fintype (𝔓.inertia p.Gal) := inferInstance
  have hbig : ∃ g : (𝔓.inertia p.Gal), g ≠ 1 := by
    by_contra h
    push_neg at h
    haveI : Subsingleton (𝔓.inertia p.Gal) := ⟨fun a b => by rw [h a, h b]⟩
    have hle1 : Fintype.card (𝔓.inertia p.Gal) ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr (by infer_instance)
    have : 2 ≤ Fintype.card (𝔓.inertia p.Gal) := by
      simpa [Nat.card_eq_fintype_card] using hcardI
    omega
  rcases hbig with ⟨τ0, hτ0ne⟩
  let τ : p.Gal := τ0.1
  have hτmem : τ ∈ 𝔓.inertia p.Gal := τ0.2
  have hτne : τ ≠ 1 := by
    intro h
    apply hτ0ne
    apply Subtype.ext
    simpa [τ] using h
  -- (2) the fiber F over P has exactly two elements
  let X : Type := AdjoinRoot p →ₐ[ℚ] p.SplittingField
  letI : Fintype X := Fintype.ofEquiv (Fin p.natDegree) (embEquivFin p).symm
  let F : Set X := {σ | pullbackIdeal p σ 𝔓 = P}
  have hFcard : F.ncard = 2 := by
    have hfib := fiberCard p p0 hp0 𝔓 h𝔓1 h𝔓2 P hPmax.isPrime hPover h𝔓Q
    rw [heP, hfP] at hfib
    norm_num at hfib
    simpa [F] using hfib
  -- (3) τ fixes every embedding whose contraction is not P
  have hQmaxOf (Q : Ideal (𝓞 (AdjoinRoot p))) (hQ1 : Q.IsPrime)
      (hQ2 : Q.LiesOver pZ) : Q.IsMaximal := by
    haveI : Q.IsPrime := hQ1
    haveI : Q.LiesOver pZ := hQ2
    apply Ideal.IsPrime.isMaximal hQ1
    exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := pZ) (P := Q) (by
      intro h
      exact (Nat.Prime.ne_zero hp0) (by exact_mod_cast (Ideal.span_singleton_eq_bot.mp h)))
  have hfix_out : ∀ σ : X, σ ∉ F → galSmulEmb p τ σ = σ := by
    intro σ hσnot
    have hQ1 : (pullbackIdeal p σ 𝔓).IsPrime := pullbackIdeal_isPrime p σ h𝔓1
    have hQ2 : (pullbackIdeal p σ 𝔓).LiesOver pZ := pullbackIdeal_liesOver p σ p0 hp0 h𝔓2
    have hQne : pullbackIdeal p σ 𝔓 ≠ P := by
      intro h
      exact hσnot (by simpa [F] using h)
    have hQmax : (pullbackIdeal p σ 𝔓).IsMaximal :=
      hQmaxOf (pullbackIdeal p σ 𝔓) hQ1 hQ2
    have he1 : (pullbackIdeal p σ 𝔓).ramificationIdx ℤ = 1 :=
      hQrest (pullbackIdeal p σ 𝔓) hQmax hQ2 hQne
    exact inertia_fixes_emb_of_unramified p p0 hp0 𝔓 h𝔓1 h𝔓2 σ τ hτmem hQ1 hQ2 he1
  -- (4) F is invariant under τ
  have hF_inv : ∀ σ : X, σ ∈ F → galSmulEmb p τ σ ∈ F := by
    intro σ hσ
    have hτinv : τ⁻¹ ∈ 𝔓.inertia p.Gal := (𝔓.inertia p.Gal).inv_mem hτmem
    have hstab : τ⁻¹ • 𝔓 = 𝔓 := inertia_smul_eq p 𝔓 τ⁻¹ hτinv
    change pullbackIdeal p (galSmulEmb p τ σ) 𝔓 = P
    rw [pullbackIdeal_comp_smul p σ τ 𝔓, hstab]
    simpa [F] using hσ
  -- (5) τ is nontrivial on the embedding set
  have hτ_moves : ∃ σ : X, galSmulEmb p τ σ ≠ σ := by
    by_contra hnot
    push_neg at hnot
    exact hτne (smul_fix_all_eq_one p τ hnot)
  -- (6) two elements of F
  obtain ⟨a, b, haF, hbF, hab, hcover⟩ := set_pair_of_ncard_two (α := X) F hFcard
  -- (7) τ moves a
  have hτa_ne : galSmulEmb p τ a ≠ a := by
    intro hτa
    have hall : ∀ σ : X, galSmulEmb p τ σ = σ := by
      intro σ
      by_cases hσF : σ ∈ F
      · rcases hcover σ hσF with hσa | hσb
        · subst σ
          exact hτa
        · subst σ
          -- τ b = b: τ b ∈ F; if τ b = a then injectivity gives b = a
          have hτbF : galSmulEmb p τ b ∈ F := hF_inv b hbF
          rcases hcover (galSmulEmb p τ b) hτbF with hτb | hτb
          · -- τ b = a and τ a = a: injectivity gives b = a
            have hb_eq : b = a := galSmulEmb_injective p τ (by
              rw [hτb, hτa])
            exact (hab hb_eq.symm).elim
          · exact hτb
      · exact hfix_out σ hσF
    rcases hτ_moves with ⟨σ0, hσ0⟩
    exact hσ0 (hall σ0)
  -- (8) the swap on the fiber
  have hτb_eq : galSmulEmb p τ b = a := by
    have hτbF : galSmulEmb p τ b ∈ F := hF_inv b hbF
    have hτaF : galSmulEmb p τ a ∈ F := hF_inv a haF
    have hτa_b : galSmulEmb p τ a = b := by
      rcases hcover (galSmulEmb p τ a) hτaF with h | h
      · exact (hτa_ne h).elim
      · exact h
    have hτb_mem : galSmulEmb p τ b ∈ F := hF_inv b hbF
    rcases hcover (galSmulEmb p τ b) hτb_mem with h | h
    · exact h
    · -- τ b = b = τ a: injectivity gives b = a
      have hb_eq : b = a := galSmulEmb_injective p τ (by
        rw [h, hτa_b])
      exact (hab hb_eq.symm).elim
  have hτa_b_glob : galSmulEmb p τ a = b := by
    have hτaF : galSmulEmb p τ a ∈ F := hF_inv a haF
    rcases hcover (galSmulEmb p τ a) hτaF with h | h
    · exact (hτa_ne h).elim
    · exact h
  -- (9) τ fixes every embedding outside {a, b}
  have hfix_all_but : ∀ σ : X, σ ≠ a → σ ≠ b → galSmulEmb p τ σ = σ := by
    intro σ hσa hσb
    by_cases hσF : σ ∈ F
    · rcases hcover σ hσF with h | h
      · exact (hσa h).elim
      · exact (hσb h).elim
    · exact hfix_out σ hσF
  -- (10) the canonical Fin-representation is a conjugate (by an equiv we need
  --     not spell out) of the embedding permutation; a swap transports to a
  --     swap.  Concretely: `galRootPerm = permCongr rootsEquivRoots aux`
  --     (Mathlib `smul_def`, definitional), `aux` (application) agrees with
  --     the embedding permutation under `embEquivRootSet`, and
  --     `galFinHom = permCongr rootFinEquiv galRootPerm`; chaining
  --     `permCongr_swap` through the three conjugacies yields the swap.
  let hsep : p.Separable := separable_of_irreducible_rat Fact.out
  let Φ : Equiv.Perm X := {
    toFun := fun σ => galSmulEmb p τ σ
    invFun := fun σ => galSmulEmb p τ⁻¹ σ
    left_inv := by
      intro σ
      calc
        galSmulEmb p τ⁻¹ (galSmulEmb p τ σ) = galSmulEmb p (τ⁻¹ * τ) σ := by
          rw [galSmulEmb_mul p τ⁻¹ τ σ]
        _ = σ := by simp [galSmulEmb_one]
    right_inv := by
      intro σ
      calc
        galSmulEmb p τ (galSmulEmb p τ⁻¹ σ) = galSmulEmb p (τ * τ⁻¹) σ := by
          rw [galSmulEmb_mul p τ τ⁻¹ σ]
        _ = σ := by simp [galSmulEmb_one] }
  have hΦswap : Φ = Equiv.swap a b := by
    apply Equiv.ext
    intro σ
    by_cases hσa : σ = a
    · subst σ
      simpa [Φ] using hτa_b_glob
    · by_cases hσb : σ = b
      · subst σ
        simpa [Φ] using hτb_eq
      · simp [Φ, Equiv.swap_apply_of_ne_of_ne hσa hσb, hfix_all_but σ hσa hσb]
  -- (11) aux: application = conjugate of Φ by embEquivRootSet
  have h_aux_eq : auxRootPerm p τ = Equiv.permCongr (embEquivRootSet p) Φ := by
    ext x
    rw [← Equiv.apply_symm_apply (embEquivRootSet p) x]
    rw [auxRootPerm_eq_emb p τ ((embEquivRootSet p).symm x)]
    -- reduce (e.permCongr Φ)(e (e.symm x)) = e (Φ (e.symm x))
    rw [Equiv.permCongr_apply]
    rw [Equiv.symm_apply_apply]
    rfl
  have hFacts : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits p⟩
  -- (12) transport the swap through the three conjugacies
  have hB : galRootPerm p τ = Equiv.swap
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) (embEquivRootSet p a))
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) (embEquivRootSet p b)) := by
    rw [galRootPerm_eq_conj p hFacts τ]
    rw [h_aux_eq, hΦswap]
    rw [permCongr_swap (embEquivRootSet p) a b]
    exact permCongr_swap (Polynomial.Gal.rootsEquivRoots p p.SplittingField)
      (embEquivRootSet p a) (embEquivRootSet p b)
  have hπ : galFinHom p hsep τ = Equiv.swap
      ((rootFinEquiv p hsep) ((Polynomial.Gal.rootsEquivRoots p p.SplittingField)
        (embEquivRootSet p a)))
      ((rootFinEquiv p hsep) ((Polynomial.Gal.rootsEquivRoots p p.SplittingField)
        (embEquivRootSet p b))) := by
    have hπ0 : galFinHom p hsep τ = (rootFinEquiv p hsep).permCongr (galRootPerm p τ) := by
      simp [galFinHom, permCongrHom]
    rw [hπ0, hB]
    exact permCongr_swap (rootFinEquiv p hsep)
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) (embEquivRootSet p a))
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) (embEquivRootSet p b))
  -- (13) distinctness of the two swapped indices
  have hne : (rootFinEquiv p hsep)
        ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) (embEquivRootSet p a)) ≠
      (rootFinEquiv p hsep)
        ((Polynomial.Gal.rootsEquivRoots p p.SplittingField) (embEquivRootSet p b)) := by
    intro h
    exact hab ((embEquivRootSet p).injective
      ((Polynomial.Gal.rootsEquivRoots p p.SplittingField).injective
        ((rootFinEquiv p hsep).injective h)))
  -- (14) conclusion: the Fin-permutation is the swap of those two indices
  refine ⟨τ, ?_⟩
  rw [hπ]
  exact ⟨(rootFinEquiv p hsep) ((Polynomial.Gal.rootsEquivRoots p p.SplittingField)
      (embEquivRootSet p a)),
    (rootFinEquiv p hsep) ((Polynomial.Gal.rootsEquivRoots p p.SplittingField)
      (embEquivRootSet p b)), hne, rfl⟩
end MainTheorem

end
end Submission.Vdw

