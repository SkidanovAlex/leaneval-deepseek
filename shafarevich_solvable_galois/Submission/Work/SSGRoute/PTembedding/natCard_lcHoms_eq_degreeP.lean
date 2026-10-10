import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.LocallyConstant.Basic
import Submission.Work.SSGRoute.PTembedding.natCard_mid_eq_quotientHoms
import Submission.Work.SSGRoute.PTembedding.natCard_nontrivHoms_primeCard
import Submission.Work.SSGRoute.localKummerReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Counting the locally constant characters `Gal(K'/K) → 𝔽_p`

For a separable closure `F'` of a field `K` and a prime `p`, the number of locally constant
(= continuous, for the Krull topology) characters `Gal(F'/K) →* Multiplicative (ZMod p)` is

`1 + (p - 1) * #{L ≤ F' : L/K Galois of degree p}`,

the `1` accounting for the trivial character and each degree-`p` Galois subextension contributing
the `p - 1` nontrivial characters of the quotient `Gal(F'/K) ⧸ Gal(F'/L) ≅ ℤ/p`.

The file contains the elementary bridge `IsLocallyConstant χ ↔ IsOpen χ.ker` for characters of a
topological group, together with the bookkeeping (a decomposition of the nontrivial characters
according to the fixed field of their kernel) reducing the count to the per-subextension
cardinality `Work.SSGRoute.PTembedding.natCard_mid_eq_quotientHoms` and the general count
`Work.SSGRoute.PTembedding.natCard_nontrivHoms_primeCard`.
-/

namespace Work.SSGRoute.PTembedding

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- For a character `χ` of a topological group with values in a group, local constancy is the same
as openness of the kernel.  The forward direction is `IsLocallyConstant.isOpen_fiber`; for the
converse one uses that the fibres of `χ` are translates of `ker χ` by group elements, and that
translations are homeomorphisms. -/
theorem isLocallyConstant_iff_isOpen_ker {G M : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group M] (χ : G →* M) :
    IsLocallyConstant χ ↔ IsOpen (χ.ker : Set G) := by
  constructor
  · intro h
    have h' := h.isOpen_fiber 1
    convert h' using 2
    ext x
    simp [MonoidHom.mem_ker]
  · intro h
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    by_cases hy : ∃ g, χ g = y
    · obtain ⟨g, rfl⟩ := hy
      have hset : χ ⁻¹' {χ g} = (fun z => z * g) '' (χ.ker : Set G) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, SetLike.mem_coe,
          MonoidHom.mem_ker]
        constructor
        · intro hh
          exact ⟨z * g⁻¹, by rw [map_mul, map_inv, hh, mul_inv_cancel], by group⟩
        · rintro ⟨k, hk, rfl⟩
          rw [map_mul, hk, one_mul]
      rw [hset]
      exact isOpenMap_mul_right g _ h
    · push Not at hy
      have hset : χ ⁻¹' {y} = ∅ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact hy z
      rw [hset]
      exact isOpen_empty

/-- A nontrivial homomorphism from a group of prime order `p` into a group of order `p` is
injective: its kernel is a subgroup whose cardinality divides `p`, and it cannot be `p`. -/
theorem ker_eq_bot_of_ne_one_of_card_prime {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hQ : Nat.card Q = p) (φ : Q →* Multiplicative (ZMod p)) (hφ : φ ≠ 1) :
    φ.ker = ⊥ := by
  rw [← Subgroup.card_eq_one]
  have hdvd : Nat.card ↥φ.ker ∣ p := hQ ▸ Subgroup.card_subgroup_dvd_card φ.ker
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact h
  · exfalso
    have htop : φ.ker = ⊤ := Subgroup.eq_top_of_card_eq φ.ker (by rw [h, ← hQ])
    exact hφ (MonoidHom.ker_eq_top_iff.mp htop)

/-- For a character with open kernel, the fixed field of the kernel determines the kernel
completely: `fixedField (ker χ) = L` is equivalent to `ker χ = Gal(F'/L)`. -/
theorem fixedField_ker_eq_iff {p : ℕ} [Fact p.Prime] {K F' : Type*} [Field K] [Field F']
    [Algebra K F'] [IsSepClosure K F'] (χ : (F' ≃ₐ[K] F') →* Multiplicative (ZMod p))
    (hχ : IsOpen (χ.ker : Set (F' ≃ₐ[K] F'))) (L : IntermediateField K F') [IsGalois K L] :
    IntermediateField.fixedField χ.ker = L ↔ χ.ker = L.fixingSubgroup := by
  constructor
  · intro h
    have hfix := InfiniteGalois.fixingSubgroup_fixedField
      (⟨χ.ker, χ.ker.isClosed_of_isOpen hχ⟩ : ClosedSubgroup (F' ≃ₐ[K] F'))
    rw [h] at hfix
    exact hfix.symm
  · intro h
    rw [h]
    exact InfiniteGalois.fixedField_fixingSubgroup L

/-- The degree-`p` Galois intermediate fields of `F'/K`. -/
abbrev GalExtDegP (p : ℕ) (K F' : Type*) [Field K] [Field F'] [Algebra K F'] : Type _ :=
  {L : IntermediateField K F' // IsGalois K L ∧ Module.finrank K L = p}

/-- The nontrivial locally constant characters `F' ≃ₐ[K] F' →* 𝔽_p`. -/
abbrev NontrivLc (p : ℕ) [Fact p.Prime] (K F' : Type*) [Field K] [Field F']
    [Algebra K F'] : Type _ :=
  {χ : (F' ≃ₐ[K] F') →* Multiplicative (ZMod p) // IsLocallyConstant χ ∧ χ ≠ 1}

/-- A nontrivial locally constant character determines a degree-`p` Galois subextension, namely
the fixed field of its (open, hence closed) kernel. -/
noncomputable def lcFixedFieldMap (p : ℕ) [Fact p.Prime] {K F' : Type*} [Field K] [Field F']
    [Algebra K F'] [IsSepClosure K F'] : NontrivLc p K F' → GalExtDegP p K F' := fun χ =>
  ⟨IntermediateField.fixedField χ.1.ker, isGalois_fixedField_ker p χ.1,
    finrank_fixedField_ker_eq_prime p Fact.out χ.1
      ((isLocallyConstant_iff_isOpen_ker χ.1).mp χ.2.1) χ.2.2⟩

/-- Regrouping the nontrivial locally constant characters out of the subgroup `lcHoms`. -/
noncomputable def regroupHoms (p : ℕ) [Fact p.Prime] {K F' : Type*} [Field K] [Field F']
    [Algebra K F'] :
    {χ : ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F')) // χ ≠ 1} ≃ NontrivLc p K F' where
  toFun x := ⟨x.1.1, x.1.2, fun h => x.2 (Subtype.ext h)⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, fun h => y.2.2 (by simpa using Subtype.ext_iff.mp h)⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl

/-- Regrouping a character together with the equation `ker χ = N`. -/
noncomputable def regroupKer (p : ℕ) [Fact p.Prime] {K F' : Type*} [Field K] [Field F']
    [Algebra K F'] (N : Subgroup (F' ≃ₐ[K] F')) :
    {χ : NontrivLc p K F' // χ.1.ker = N} ≃
      {χ : (F' ≃ₐ[K] F') →* Multiplicative (ZMod p) //
        IsLocallyConstant χ ∧ χ ≠ 1 ∧ χ.ker = N} where
  toFun x := ⟨x.1.1, x.1.2.1, x.1.2.2, x.2⟩
  invFun y := ⟨⟨y.1, y.2.1, y.2.2.1⟩, y.2.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl

/-- The fibre over a degree-`p` Galois subextension `L` consists of the nontrivial locally constant
characters with kernel exactly `Gal(F'/L)`. -/
noncomputable def fiberEquivMid (p : ℕ) [Fact p.Prime] {K F' : Type*} [Field K] [Field F']
    [Algebra K F'] [IsSepClosure K F'] (L : GalExtDegP p K F') :
    {χ : NontrivLc p K F' // lcFixedFieldMap p χ = L} ≃
      {χ : (F' ≃ₐ[K] F') →* Multiplicative (ZMod p) //
        IsLocallyConstant χ ∧ χ ≠ 1 ∧ χ.ker = L.1.fixingSubgroup} := by
  haveI : IsGalois K L.1 := L.2.1
  refine (Equiv.subtypeEquivRight
      (p := fun x : NontrivLc p K F' => lcFixedFieldMap p x = L)
      (q := fun x : NontrivLc p K F' => IntermediateField.fixedField x.1.ker = L.1)
      (fun x => Subtype.ext_iff.trans Iff.rfl)).trans ?_
  refine (Equiv.subtypeEquivRight
      (p := fun x : NontrivLc p K F' => IntermediateField.fixedField x.1.ker = L.1)
      (q := fun x : NontrivLc p K F' => x.1.ker = L.1.fixingSubgroup)
      (fun x => fixedField_ker_eq_iff x.1
        ((isLocallyConstant_iff_isOpen_ker x.1).mp x.2.1) L.1)).trans ?_
  exact regroupKer p (L.1.fixingSubgroup)

/-- Each fibre of the fixed-field map has `p - 1` elements. -/
theorem fiber_card (p : ℕ) [Fact p.Prime] {K F' : Type*} [Field K] [Field F']
    [Algebra K F'] [IsSepClosure K F'] (L : GalExtDegP p K F') :
    Nat.card {χ : NontrivLc p K F' // lcFixedFieldMap p χ = L} = p - 1 := by
  haveI : IsGalois K L.1 := L.2.1
  have hcard : Nat.card ((F' ≃ₐ[K] F') ⧸ L.1.fixingSubgroup) = p := by
    rw [natCard_quotient_fixingSubgroup_eq_finrank (K := F') L.1, L.2.2]
  rw [Nat.card_congr (fiberEquivMid p L),
    natCard_mid_eq_quotientHoms p L.1 L.2.2,
    natCard_nontrivHoms_primeCard p ((F' ≃ₐ[K] F') ⧸ L.1.fixingSubgroup) hcard]

theorem natCard_lcHoms_eq_degreeP (p : ℕ) [Fact p.Prime] {K F' : Type*} [Field K] [Field F']
    [Algebra K F'] [IsSepClosure K F']
    (hfin : Finite {L : IntermediateField K F' // IsGalois K L ∧ Module.finrank K L = p}) :
    Nat.card ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F'))
      = 1 + (p - 1) * Nat.card {L : IntermediateField K F' // IsGalois K L ∧ Module.finrank K L = p} := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Finite (GalExtDegP p K F') := hfin
  haveI : Fintype (GalExtDegP p K F') := Fintype.ofFinite _
  haveI hfib : ∀ L : GalExtDegP p K F', Finite {χ : NontrivLc p K F' // lcFixedFieldMap p χ = L} :=
    fun L => Nat.finite_of_card_ne_zero
      (by rw [fiber_card p L]; exact Nat.sub_ne_zero_of_lt hp.one_lt)
  haveI hsig : Finite (Σ L : GalExtDegP p K F',
      {χ : NontrivLc p K F' // lcFixedFieldMap p χ = L}) := inferInstance
  haveI hN : Finite (NontrivLc p K F') :=
    (Equiv.sigmaFiberEquiv (lcFixedFieldMap p)).finite_iff.mp hsig
  haveI hSub : Finite {χ : ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F')) // χ ≠ 1} :=
    Finite.of_injective (regroupHoms p) (regroupHoms p).injective
  have hsum : Nat.card (NontrivLc p K F') = (p - 1) * Nat.card (GalExtDegP p K F') := by
    have h1 : Nat.card (NontrivLc p K F') = Nat.card (Σ L : GalExtDegP p K F',
        {χ : NontrivLc p K F' // lcFixedFieldMap p χ = L}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv (lcFixedFieldMap p)).symm
    rw [h1, Nat.card_sigma, Finset.sum_congr rfl (fun L _ => fiber_card p L)]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.mul_comm]
  rw [← Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F')))),
    Finite.card_option, Nat.card_congr (regroupHoms p), hsum, Nat.add_comm]

end Work.SSGRoute.PTembedding
