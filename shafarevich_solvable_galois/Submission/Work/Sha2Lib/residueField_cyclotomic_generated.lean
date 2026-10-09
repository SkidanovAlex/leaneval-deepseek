import Mathlib
import Submission.NK.NumberTheory.NumberField.Completion.exists_galois_unramified_extension_of_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.exists_frobenius_galRestrict
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_unramified_extension_tower
import Submission.Commons.NumberTheory.NumberField.frobenius_eq_of_commute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace Work.Sha2Lib

/-- **An algebra automorphism fixing a generator is the identity.**

If `ζ` generates the `L`-algebra `L'` (`Algebra.adjoin L {ζ} = ⊤`) and `σ : L' ≃ₐ[L] L'` fixes `ζ`,
then `σ = 1`.  The fixed points of `σ` form an `L`-subalgebra containing `ζ`, hence contain
`Algebra.adjoin L {ζ} = ⊤`.

Used in `residueField_cyclotomic_generated`: `L(ζ_m) = L[ζ]` for a primitive `m`-th root of unity
`ζ`, so an `L`-automorphism of `L(ζ_m)` fixing `ζ` is trivial. -/
theorem algEquiv_eq_one_of_apply_eq_self_of_adjoin_eq_top {L L' : Type*} [Field L] [Field L']
    [Algebra L L'] {ζ : L'} (hgen : Algebra.adjoin L ({ζ} : Set L') = ⊤)
    (σ : L' ≃ₐ[L] L') (h : σ ζ = ζ) : σ = 1 := by
  refine AlgEquiv.ext fun x => ?_
  show σ x = x
  have hx : x ∈ Algebra.adjoin L ({ζ} : Set L') := by rw [hgen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h
  | algebraMap r => simp
  | add y z hy hz ihy ihz => simp [map_add, ihy, ihz]
  | mul y z hy hz ihy ihz => simp [map_mul, ihy, ihz]

/-- **Finite-field degree identity for a primitive `m`-th root of unity.**

Let `k` be a finite field, `K` a finite field extension of `k` and `x ∈ K` a primitive `m`-th root
of unity.  If `m ∣ #k ^ D - 1` only for `D ≥ [K : k]` (contrapositive form: every `D ≥ 1` with
`m ∣ #k ^ D - 1` satisfies `[K : k] ≤ D` — i.e. the Frobenius `y ↦ y ^ #k` has order `[K : k]` on
`x`), then `k[x] = K`.

Indeed, `E := k⟮x⟯ ⊆ K` has `#E = #k ^ [E : k]`, so `x ^ (#k ^ [E : k]) = x`, whence
`m ∣ #k ^ [E : k] - 1` and `[K : k] ≤ [E : k]`; as `[E : k] ≤ [K : k]` this gives `E = K`.

The field structures on `k` and `K` enter only through the propositional hypotheses `IsField k`,
`IsField K`; this keeps the statement free of the `Field`/`Ring` instance-coherence problems of a
pair of *unrelated* `Field` and `Algebra` instances (essential for applying it to residue fields of
quotients, where the `Algebra` structure is the canonical `Ideal.Quotient` one). -/
theorem adjoin_eq_top_of_isPrimitiveRoot_isField (k : Type*) (K : Type*) [CommRing k] [CommRing K]
    [Algebra k K] [Fintype k] [Fintype K] (hk : IsField k) (hK : IsField K) {m : ℕ} [NeZero m]
    {x : K} (hx : IsPrimitiveRoot x m)
    (hleast : ∀ D : ℕ, 1 ≤ D → m ∣ (Fintype.card k) ^ D - 1 → Module.finrank k K ≤ D) :
    Algebra.adjoin k ({x} : Set K) = ⊤ := by
  letI : Field k := hk.toField
  letI : Field K := hK.toField
  haveI hAlgExt : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let E : IntermediateField k K := IntermediateField.adjoin k ({x} : Set K)
  have hxE : x ∈ E := IntermediateField.subset_adjoin k ({x} : Set K) (Set.mem_singleton x)
  haveI hFinE : Finite ↥E := Finite.of_injective Subtype.val Subtype.val_injective
  haveI hFtE : Fintype ↥E := Fintype.ofFinite _
  -- `E` is a finite field with `#E = #k ^ [E : k]`
  have hcard : Fintype.card ↥E = (Fintype.card k) ^ (Module.finrank k ↥E) :=
    Module.card_eq_pow_finrank
  have hpow : x ^ (Fintype.card ↥E) = x := by
    have h1 : (⟨x, hxE⟩ : ↥E) ^ (Fintype.card ↥E) = ⟨x, hxE⟩ := FiniteField.pow_card _
    simpa using congrArg (Subtype.val) h1
  have hdiv : m ∣ (Fintype.card k) ^ (Module.finrank k ↥E) - 1 := by
    have hcardpos : 1 ≤ Fintype.card ↥E := Fintype.card_pos_iff.mpr ⟨⟨x, hxE⟩⟩
    have hone : x ^ (Fintype.card ↥E - 1) = 1 := by
      have h2 : x ^ (Fintype.card ↥E - 1) * x = x := by
        rw [← pow_succ, Nat.sub_add_cancel hcardpos]
        exact hpow
      exact mul_right_cancel₀ (hx.ne_zero (NeZero.ne m)) (by rw [h2, one_mul])
    rw [hcard] at hone
    exact (hx.pow_eq_one_iff_dvd _).mp hone
  have hd : 1 ≤ Module.finrank k ↥E :=
    Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos_iff.mpr inferInstance).ne'
  have hle1 : Module.finrank k K ≤ Module.finrank k ↥E := hleast _ hd hdiv
  have hle2 : Module.finrank k ↥E ≤ Module.finrank k K := E.toSubmodule.finrank_le
  have hEtop : E = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_le le_top ?_
    have h1 : Module.finrank k ↥(⊤ : IntermediateField k K) = Module.finrank k K :=
      finrank_top k K
    rw [h1]
    exact hle1
  have h2 : IntermediateField.adjoin k ({x} : Set K) = ⊤ := hEtop
  rw [← IntermediateField.adjoin_toSubalgebra (F := k) ({x} : Set K), h2,
    IntermediateField.top_toSubalgebra]

/-- **Gap A of `exists_galois_unramified_extension_of_inertiaDeg`: the residue field of `L(ζ_m)` at `q'` over `q` is generated by the reduction of a primitive `m`-th root of unity.**

`L` a number field, `q` a prime of `𝓞 L` with `m ∉ q`, `q'` a prime of `𝓞 (L(ζ_m))` lying over `q`. Then for every primitive `m`-th root of unity `ζ` of `L(ζ_m)` (taken in `𝓞 (L(ζ_m))`), the image of `ζ` in the residue field `𝓞 (L(ζ_m)) ⧸ q'` generates that residue field over the residue field `𝓞 L ⧸ q`.

This is the third -- and only unproved -- conjunct of `cyclotomic_unramified_and_residue` in
`Submission/NK/NumberTheory/NumberField/Completion/exists_galois_unramified_extension_of_inertiaDeg.lean` (lines 502-537, module `Submission.NK.NumberTheory.NumberField.Completion.exists_galois_unramified_extension_of_inertiaDeg`). The first two conjuncts are already proved there (`ramificationIdx_cyclotomic_eq_one`, `isPrimitiveRoot_reduction`), as is the auxiliary `natCast_mem_of_one_sub_isPrimitiveRoot_mem` (line 204); you may import that module and use those proved, `sorry`-free lemmas. The present statement is the *first* unproved sub-piece of that file's remaining two `sorry`s (the other one, line 606, is `f(q'|q) = n` for `m = q₀^n - 1`, which follows from this statement together with the proved arithmetic lemma `pow_sub_one_dvd_pow_sub_one_iff`). Equivalent `inertiaDeg` form: `q'.asIdeal.inertiaDeg (𝓞 L) = orderOf (#(𝓞 L ⧸ q) : (ZMod m)ˣ)`, i.e. the residue degree of the cyclotomic extension at `q` is the multiplicative order of the residue-field cardinality `#(𝓞 L ⧸ q) = N q` modulo `m`.

Route and warnings (from two reviews): `L(ζ_m)/L` is abelian Galois and unramified at `q` (proved on disk), so all `q' | q` have the same residue degree, equal to `ord_m(Nq)`; the Frobenius at `q'` acts on `μ_m` by `ζ ↦ ζ^(Nq)` (Teichmüller/root-of-unity specific!). Do **not** route through the plausible general claim "unramified at q + α integral generating `L'/L` implies `k(q')(ᾱ) = k(q')`" -- it is false (`K = ℚ_p`, `L` unramified of degree 2, `α = c + pζ`). The finite-field degree identity for a primitive `m`-th root of unity general `m` (`[k(ζ_m) : k] = ord_m(#k)`, `m` coprime to `#k`) is *not* on disk in that generality (`natDegree_minpoly_isPrimitiveRoot_card_pow_sub_one` covers only `m = #k ^ n - 1`) and will have to be proved here. -/
theorem residueField_cyclotomic_generated {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {m : ℕ} [NeZero m]
    (hq : ((m : ℕ) : NumberField.RingOfIntegers L) ∉ q.asIdeal)
    (q' : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers (CyclotomicField m L)))
    (hqq' : q'.asIdeal.LiesOver q.asIdeal) :
    ∀ ζ : NumberField.RingOfIntegers (CyclotomicField m L),
      IsPrimitiveRoot (ζ : CyclotomicField m L) m →
      Algebra.adjoin (NumberField.RingOfIntegers L ⧸ q.asIdeal)
        ({Ideal.Quotient.mk q'.asIdeal ζ} : Set
          (NumberField.RingOfIntegers (CyclotomicField m L) ⧸ q'.asIdeal)) = ⊤ := by
  classical
  intro ζ hζ
  haveI hcyc : IsCyclotomicExtension {m} L (CyclotomicField m L) :=
    CyclotomicField.isCyclotomicExtension m L
  haveI hgal : IsGalois L (CyclotomicField m L) :=
    IsCyclotomicExtension.isGalois {m} L (CyclotomicField m L)
  haveI hfin : FiniteDimensional L (CyclotomicField m L) :=
    IsCyclotomicExtension.finiteDimensional {m} L (CyclotomicField m L)
  haveI hlies : q'.asIdeal.LiesOver q.asIdeal := hqq'
  haveI hfinq : Finite (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
  haveI hfinq' : Finite (NumberField.RingOfIntegers (CyclotomicField m L) ⧸ q'.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q'
  haveI : Fintype (NumberField.RingOfIntegers L ⧸ q.asIdeal) := Fintype.ofFinite _
  haveI : Fintype (NumberField.RingOfIntegers (CyclotomicField m L) ⧸ q'.asIdeal) :=
    Fintype.ofFinite _
  -- the extension is unramified at `q`, and the reduction of `ζ` is again primitive
  have he : q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1 :=
    Commons.NumberTheory.NumberField.Completion.ramificationIdx_cyclotomic_eq_one q hq q' hqq'
  have hprim : IsPrimitiveRoot (Ideal.Quotient.mk q'.asIdeal ζ) m :=
    Commons.NumberTheory.NumberField.Completion.isPrimitiveRoot_reduction q hq q' hqq' hζ
  -- `m` is a unit at `q'`
  have hmq' : ((m : ℕ) : NumberField.RingOfIntegers (CyclotomicField m L)) ∉ q'.asIdeal := by
    intro hmem
    refine hq ?_
    rw [Ideal.LiesOver.over (p := q.asIdeal) (P := q'.asIdeal), Ideal.mem_under]
    simpa using hmem
  -- the Frobenius automorphism at `q'`
  obtain ⟨σ, hσmap, hσres⟩ :=
    Commons.NumberTheory.NumberField.exists_frobenius_galRestrict (K := L)
      (L := CyclotomicField m L) q q' hqq'
  have hζm : ζ ^ m = 1 := by
    apply IsIntegralClosure.algebraMap_injective (NumberField.RingOfIntegers (CyclotomicField m L))
      ℤ (CyclotomicField m L)
    rw [map_pow, map_one]
    exact hζ.pow_eq_one
  -- the Frobenius acts on `ζ` by `ζ ↦ ζ ^ #k`, where `k = 𝓞 L ⧸ q`
  have hsub : galRestrict (NumberField.RingOfIntegers L) L (CyclotomicField m L)
      (NumberField.RingOfIntegers (CyclotomicField m L)) σ ζ
      - ζ ^ Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal) ∈ q'.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hσres ζ, map_pow, sub_self]
  have hθm : (galRestrict (NumberField.RingOfIntegers L) L (CyclotomicField m L)
      (NumberField.RingOfIntegers (CyclotomicField m L)) σ ζ) ^ m = 1 := by
    rw [← map_pow, hζm, map_one]
  have hζqm : (ζ ^ Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal)) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζm, one_pow]
  have hσζ : galRestrict (NumberField.RingOfIntegers L) L (CyclotomicField m L)
      (NumberField.RingOfIntegers (CyclotomicField m L)) σ ζ
      = ζ ^ Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    Commons.NumberTheory.NumberField.Completion.eq_of_sub_mem_of_pow_eq_one hθm hζqm hsub hmq'
  have hσζL : σ (ζ : CyclotomicField m L)
      = (ζ : CyclotomicField m L) ^ Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal) := by
    have h1 : (((galRestrict (NumberField.RingOfIntegers L) L (CyclotomicField m L)
        (NumberField.RingOfIntegers (CyclotomicField m L)) σ ζ :
        NumberField.RingOfIntegers (CyclotomicField m L)) : CyclotomicField m L))
        = σ (ζ : CyclotomicField m L) :=
      algebraMap_galRestrict_apply (NumberField.RingOfIntegers L) σ ζ
    rw [← h1, hσζ]
    exact map_pow (algebraMap (NumberField.RingOfIntegers (CyclotomicField m L))
      (CyclotomicField m L)) ζ (Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal))
  -- `ζ` generates `L(ζ_m)` over `L`, so an `L`-automorphism fixing `ζ` is trivial
  have hgen : Algebra.adjoin L ({(ζ : CyclotomicField m L)} : Set (CyclotomicField m L)) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := L) (B := CyclotomicField m L) hζ
  have hfaith : ∀ τ : CyclotomicField m L ≃ₐ[L] CyclotomicField m L,
      τ (ζ : CyclotomicField m L) = (ζ : CyclotomicField m L) → τ = 1 :=
    fun τ hτ => algEquiv_eq_one_of_apply_eq_self_of_adjoin_eq_top hgen τ hτ
  -- the `#k`-th power Frobenius, iterated
  have hpow : ∀ j : ℕ, (σ ^ j) (ζ : CyclotomicField m L)
      = (ζ : CyclotomicField m L) ^ ((Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal)) ^ j) :=
    by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih]
        rw [show σ ((ζ : CyclotomicField m L)
              ^ ((Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal)) ^ j))
            = (σ (ζ : CyclotomicField m L))
              ^ ((Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal)) ^ j) from
          map_pow (σ : CyclotomicField m L →+* CyclotomicField m L) _ _]
        rw [hσζL, ← pow_mul, ← pow_succ']
  -- the order of the Frobenius is the residue degree `f(q'|q)`
  have hordσ : orderOf σ = q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) :=
    Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg q q' hqq' he σ hσmap hσres
  -- `f(q'|q)` is the least positive `D` with `m ∣ #k ^ D - 1`
  have hkey : ∀ D : ℕ, 1 ≤ D → m ∣ (Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal)) ^ D - 1 →
      q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) ≤ D := by
    intro D hD hdiv
    have hfix : (σ ^ D) (ζ : CyclotomicField m L) = (ζ : CyclotomicField m L) := by
      rw [hpow D]
      have h1 : (Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal)) ^ D
          = ((Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal)) ^ D - 1) + 1 := by
        have hq0pos : 0 < Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal) := by
          rw [Nat.card_eq_fintype_card]
          exact lt_trans Nat.zero_lt_one Fintype.one_lt_card
        exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_pos hq0pos D).ne')).symm
      rw [h1, pow_succ]
      have hpow1 : (ζ : CyclotomicField m L)
          ^ ((Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal)) ^ D - 1) = 1 :=
        (hζ.pow_eq_one_iff_dvd _).mpr hdiv
      rw [hpow1, one_mul]
    have hσD : σ ^ D = 1 := hfaith (σ ^ D) hfix
    have hdvd : q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) ∣ D := by
      rw [← hordσ]
      exact orderOf_dvd_iff_pow_eq_one.mpr hσD
    exact Nat.le_of_dvd hD hdvd
  -- the residue degree of `q'` over `q` is the `k`-dimension of the residue field `k'`
  have hff : Module.finrank (NumberField.RingOfIntegers L ⧸ q.asIdeal)
      (NumberField.RingOfIntegers (CyclotomicField m L) ⧸ q'.asIdeal)
      = q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) :=
    (Ideal.inertiaDeg_eq_of_isMaximal q.asIdeal q'.asIdeal).symm
  -- the residue fields are fields
  have hfieldk : IsField (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient q.asIdeal).mp
      (inferInstance : q.asIdeal.IsMaximal)
  have hfieldK : IsField (NumberField.RingOfIntegers (CyclotomicField m L) ⧸ q'.asIdeal) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient q'.asIdeal).mp
      (inferInstance : q'.asIdeal.IsMaximal)
  -- `k[x] = k'` by the finite-field degree identity
  refine adjoin_eq_top_of_isPrimitiveRoot_isField
    (NumberField.RingOfIntegers L ⧸ q.asIdeal)
    (NumberField.RingOfIntegers (CyclotomicField m L) ⧸ q'.asIdeal)
    hfieldk hfieldK hprim ?_
  intro D hD hdiv
  rw [hff]
  rw [← Nat.card_eq_fintype_card] at hdiv
  exact hkey D hD hdiv

end Work.Sha2Lib
