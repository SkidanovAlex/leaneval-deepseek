import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_of_commute
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base
import Submission.NK.NumberTheory.NumberField.Completion.normIndex_val_splitting
import Submission.NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

/-- **The valuation formula for the local norm index, in arbitrary universes.**

For `L/K` a finite Galois extension of number fields and `q | Q` a prime, writing
`N = N_{L_q/K_Q}(L_qˣ) ≤ (K_Q)ˣ` for the norm group and `U = O_{K_Q}ˣ` for the units of the
valuation ring,

`#((K_Q)ˣ ⧸ N) = f(q|Q) · [U : U ⊓ N]`.

This is the universe-polymorphic form of
`Commons.NumberTheory.NumberField.Completion.NormIndexUnits.natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux`
(which is stated for `Type 0` fields only); the proof is the same valuation computation via
`Commons.GroupTheory.index_range_eq_mul_relIndex_ker_of_comm`. -/
theorem natCard_quotient_units_range_norm_eq_mul_relIndex_adicUnitsVal
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K))) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) *
        (MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K))).relIndex
          (Commons.NumberTheory.NumberField.Completion.adicUnitsVal K Q) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have key := Commons.GroupTheory.index_range_eq_mul_relIndex_ker_of_comm
    (A := (Q.adicCompletion K)ˣ) (B := (q.adicCompletion L)ˣ)
    (v := Commons.NumberTheory.NumberField.Completion.unitsValLog (Q.adicCompletion K))
    (Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective K Q)
    (w := Commons.NumberTheory.NumberField.Completion.unitsValLog (q.adicCompletion L))
    (Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective L q)
    (N := Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K))
    (f := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))
    (Ideal.inertiaDeg_pos q.asIdeal (NumberField.RingOfIntegers K))
    (fun u => Commons.NumberTheory.NumberField.Completion.unitsValLog_norm Q q hq u)
  have hker : (Commons.NumberTheory.NumberField.Completion.unitsValLog
      (Q.adicCompletion K)).ker = Commons.NumberTheory.NumberField.Completion.adicUnitsVal K Q := rfl
  rw [Subgroup.index_eq_card, hker] at key
  rw [key]
  congr 1
  rw [inf_comm]
  exact Subgroup.inf_relIndex_right _ _

/-- **The `ℓ`-part of the ramification index of a prime of residue characteristic `p ≠ ℓ` in an
abelian extension of number fields divides the `ℓ`-part of `q - 1`**, where `q` is the cardinality
of the residue field of the base prime.

Let `L/K` be a finite Galois extension of number fields whose Galois group is commutative, `Q` a
finite prime of `K` of residue characteristic `p`, `q` a prime of `L` lying over `Q`, and `ℓ ≠ p`
a prime.  Then `v_ℓ(e(q|Q)) ≤ v_ℓ(q_res - 1)`.

Proof sketch.  Work over the completions `F = Q.adicCompletion K`, `E = q.adicCompletion L` (with
the algebra structure `RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)`;
the local Galois group is commutative, being isomorphic to the decomposition subgroup of the
commutative `Gal(L/K)` — use e.g.
`Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois` together
with `localCommute_of_commute` from
`Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute`).
Then

* the local norm index theorem
  `Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_abelian_local`
  gives `#(Fˣ ⧸ N_{E/F}Eˣ) = #(E ≃ₐ[F] E) = [E : F]`;
* the valuation formula
  `Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux`
  gives `#(Fˣ ⧸ N) = f · [U : U ⊓ N]` where `U = Commons.NumberTheory.NumberField.Completion.adicUnitsVal K Q`
  is the unit group of the valuation ring and `f = q.asIdeal.inertiaDeg (𝓞 K)`;
* `Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg` gives
  `[E : F] = e · f` with `e = q.asIdeal.ramificationIdx (𝓞 K)`.

Combining: `[U : U ⊓ N_{E/F}Eˣ] = e`, and since `f ≠ 0` this also gives `e = (range N).relIndex U`
in the notation of the commons.  Then `U ⧸ (U ⊓ N)` is a finite abelian group of order `e`; its
`ℓ`-Sylow is a finite `ℓ`-group quotient of `U` of order `ℓ ^ v_ℓ(e)`, and
`NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits` (already proved, import
`Submission.NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits`) says every finite
`ℓ`-group quotient of `(Q.adicCompletionIntegers K)ˣ` has order dividing
`#(𝓞 K ⧸ Q) - 1`.  Henc
`ℓ ^ v_ℓ(e) ∣ #(𝓞 K ⧸ Q) - 1`, i.e. `v_ℓ(e) ≤ v_ℓ(#(𝓞 K ⧸ Q) - 1)`. -/
theorem padicValNat_ramificationIdx_le {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
    (hres : CharP (NumberField.RingOfIntegers K ⧸ Q.asIdeal) p) (hne : p ≠ ℓ)
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    padicValNat ℓ (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K))
      ≤ padicValNat ℓ (Nat.card (NumberField.RingOfIntegers K ⧸ Q.asIdeal) - 1) := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  set e : ℕ := q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) with he
  set f : ℕ := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) with hf
  set N : Subgroup (Q.adicCompletion K)ˣ := MonoidHom.range
    (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)) with hN
  set U : Subgroup (Q.adicCompletion K)ˣ := (Q.adicCompletionIntegers K).unitGroup with hU
  set V : Subgroup U := N.subgroupOf U with hV
  have hadic : Commons.NumberTheory.NumberField.Completion.adicUnitsVal K Q = U := by
    rw [Commons.NumberTheory.NumberField.Completion.adicUnitsVal_eq_unitGroup K Q, hU]
  have hfpos : 0 < f := by rw [hf]; exact Ideal.inertiaDeg_pos q.asIdeal _
  have hepos : 0 < e := by rw [he]; exact Ideal.ramificationIdx_pos _ q.asIdeal
  -- the valuation formula
  have hA : Nat.card ((Q.adicCompletion K)ˣ ⧸ N) = f * N.relIndex U := by
    rw [hN]
    have h := natCard_quotient_units_range_norm_eq_mul_relIndex_adicUnitsVal Q q hq
    rw [hadic, ← hf] at h
    exact h
  -- the norm index theorem plus `[E : F] = e · f`
  have hB : Nat.card ((Q.adicCompletion K)ˣ ⧸ N) = e * f := by
    rw [hN]
    rw [Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_of_commute
        hcomm Q q hq,
      ← Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq,
      ← he, ← hf]
  have her : e = N.relIndex U := by
    have h1 : e * f = f * N.relIndex U := by rw [← hB, hA]
    have h2 : e * f = N.relIndex U * f := by rwa [mul_comm f (N.relIndex U)] at h1
    exact Nat.mul_right_cancel hfpos h2
  -- the quotient `U ⧸ (U ⊓ N)` has order `e`
  have hC : Nat.card (U ⧸ V) = e := by
    rw [hV, Commons.GroupTheory.natCard_quotient_subgroupOf_eq_relIndex U N, ← her]
  haveI hfinV : Finite (U ⧸ V) :=
    (Nat.card_ne_zero.mp (by rw [hC]; exact hepos.ne')).2
  haveI hftyV : Fintype (U ⧸ V) := Fintype.ofFinite _
  -- the finite `ℓ`-group quotient of order `ℓ ^ v_ℓ(e)`
  haveI hcomV : IsMulCommutative (U ⧸ V) := IsMulCommutative.of_comm (fun a b => mul_comm a b)
  obtain ⟨H', hH'⟩ := Commons.GroupTheory.exists_subgroup_card_quotient_eq_pow_factorization
    (G := U ⧸ V) (p := ℓ)
  haveI hnormH' : H'.Normal := Subgroup.normal_of_isMulCommutative H'
  have hPcard : Nat.card ((U ⧸ V) ⧸ H') = ℓ ^ padicValNat ℓ e := by
    rw [hH', hC, Nat.factorization_def e (Fact.out : ℓ.Prime)]
  -- the surjection `(O_K)ˣ ↠ (U ⧸ V) ⧸ H'`
  let φU : (Q.adicCompletionIntegers K)ˣ →* U :=
    ((Q.adicCompletionIntegers K).unitGroupMulEquiv.symm).toMonoidHom
  have hφUsurj : Function.Surjective φU := by
    intro x
    obtain ⟨w, hw⟩ := (Q.adicCompletionIntegers K).unitGroupMulEquiv.symm.surjective x
    exact ⟨w, hw⟩
  haveI hnormV : V.Normal := Subgroup.normal_of_isMulCommutative V
  let ψ : U →* U ⧸ V := QuotientGroup.mk' V
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective V x
    exact ⟨y, hy⟩
  let φ : (Q.adicCompletionIntegers K)ˣ →* ((U ⧸ V) ⧸ H') :=
    (QuotientGroup.mk' H').comp (ψ.comp φU)
  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective H' x
    obtain ⟨z, hz⟩ := hψsurj y
    obtain ⟨w, hw⟩ := hφUsurj z
    refine ⟨w, ?_⟩
    show (QuotientGroup.mk' H') (ψ (φU w)) = x
    rw [hw, hz, hy]
  haveI hfinP : Finite ((U ⧸ V) ⧸ H') := QuotientGroup.finite
  have hdvd : ℓ ^ padicValNat ℓ e ∣ Nat.card (NumberField.RingOfIntegers K ⧸ Q.asIdeal) - 1 := by
    have h := NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits (P := (U ⧸ V) ⧸ H')
      Q hres hne (IsPGroup.of_card hPcard) φ hφsurj
    rw [hPcard] at h
    exact h
  -- `ℓ ^ v_ℓ(e) ∣ q - 1` and the residue field is nontrivial
  haveI hchar : CharP (NumberField.RingOfIntegers K ⧸ Q.asIdeal) p := hres
  haveI hntriv : Nontrivial (NumberField.RingOfIntegers K ⧸ Q.asIdeal) :=
    CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  haveI hfty : Fintype (NumberField.RingOfIntegers K ⧸ Q.asIdeal) := Fintype.ofFinite _
  have hN1 : Nat.card (NumberField.RingOfIntegers K ⧸ Q.asIdeal) - 1 ≠ 0 := by
    have h2 : 1 < Nat.card (NumberField.RingOfIntegers K ⧸ Q.asIdeal) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  exact (padicValNat_dvd_iff_le hN1).mp hdvd

end NK.Reconstruct
