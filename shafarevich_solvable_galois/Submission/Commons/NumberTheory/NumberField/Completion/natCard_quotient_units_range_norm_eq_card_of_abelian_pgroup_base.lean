import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_card_of_abelian_local_base
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_finrank_of_abelian_local
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
import Submission.Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.kernel_condition_of_prime_top_cyclic_middle_coprime
import Submission.Commons.FieldTheory.Galois.div_mem_range_norm_of_prime_quotient_coprime
import Submission.Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_of_ringEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_pgroup_intermediate_field
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The abelian local norm index theorem for `p`-groups: the base-change step

Target of this file (the requested lemma):
`Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base`:
for `B ⊆ E` a finite abelian Galois extension of local fields with `B` a finite extension of the
completion `Q.adicCompletion K` of a number field at a finite place, and `Gal(E/B)` a `p`-group,

`#(Bˣ ⧸ N_{E/B}(Eˣ)) = #Gal(E/B)`.

Since `IsPGroup 0 G` holds for every group `G`, the statement with `p = 0` is the *full* abelian
case, so the hypothesis `hp` is not restrictive.

## Structure of the proof

With `hupper` and `hlower` the two inequalities, the result is `le_antisymm hupper hlower`:

* `hupper` is `natCard_quotient_units_range_norm_le_card_of_abelian_local_base` (commons, PROVEN):
  `#(Bˣ ⧸ N) ≤ #Gal(E/B)` for every *abelian* `E/B`.  It is obtained by peeling off a subgroup
  `H ≤ G` with `G/H` cyclic and using the cyclic case plus the elementary tower inequality.
* `hlower` (`[E:B] ≤ #(Bˣ ⧸ N)`) is the local norm index theorem for the *lower* direction.

The lower bound is obtained from the commons lemma
`Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_pgroup_intermediate_field`
(PROVEN, by a companion agent): for `B ⊆ E` a finite abelian Galois extension of local fields over
`Q.adicCompletion K` and *every* intermediate field `M` whose extension `M/B` has `p`-group
Galois group,

`#(Bˣ ⧸ N_{M/B}(Mˣ)) = #Gal(M/B)`.

Applying it at `M = ⊤` and transporting both sides along `⊤ ≃ₐ[B] E`
(`IntermediateField.topEquiv`, via `natCard_quotient_units_range_norm_eq_of_ringEquiv` and
`AlgEquiv.autCongr`) gives exactly the lower bound for the extension `E/B`; the `p`-group
hypothesis transports because `AlgEquiv.autCongr (topEquiv)` is an isomorphism of groups.  Since
`IsPGroup 0 G` holds for every group `G`, the statement with `p = 0` is the *full* abelian case, so
the hypothesis `hp` is not restrictive.

## The lower bound: what is used and what is proven in this file

The lower bound is the deep local class field theory input; it is proved in the companion commons
file cited above (via the fundamental class / Tate's theorem route), and it is not reproved here.
Everything in this file serves the valuation-theoretic analysis of the norm index and the transport
of the extension data:

* (`NormIndexUnits.natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux`)
  the **valuation formula**: the value-group logarithm `unitsValLog B` (commons) is surjective with
  kernel `U = (Q.adicCompletionIntegers K).unitGroup` and satisfies
  `unitsValLog (N u) = (unitsValLog u)^f` for `u ∈ Eˣ`, where `f` is the inertia degree of `q | Q`;
  hence `v(N Eˣ) = fℤ` and

  `#(Bˣ ⧸ N) = f · [U : U ∩ N]`.

* (`NormIndexUnits.finrank_le_index_range_norm_adicCompletion_of_units`)
  consequently it **suffices** to know `[U : U ∩ N] = e` (`e` = ramification index), i.e.

  `(range N).relIndex U = q.asIdeal.ramificationIdx (𝓞 K)`.

* (`inertiaDeg_le_natCard_quotient_units_range_norm_adicCompletion`) the special case
  `[U : U ∩ N] ≥ 1` of that statement gives `#(Bˣ ⧸ N) ≥ f`, i.e. the norm index theorem for
  unramified `E/B`.

* (`exists_norm_units_of_unramified_top_and_dvd_ramificationIdx`) the arithmetic content of the
  residual case of Milne's divisibility step (Milne, *CFT*, III.2) for the unramified twist.

* (`isGalois_of_ringEquiv`, `norm_eq_of_ringEquiv`, `moduleFinite_of_ringEquiv`,
  `natCard_quotient_units_range_norm_eq_of_ringEquiv`) the transport of the field-theoretic data
  (Galois-ness, the norm, finite-dimensionality, the norm quotient) along a compatible pair of ring
  isomorphisms — the algebraic half of the universe bridge.

Further context: the upper bound (`natCard_quotient_units_range_norm_le_card_of_abelian_local_base`),
the cyclic case (`natCard_quotient_units_range_norm_eq_card_of_cyclic*`), the unramified case
(`..._of_ramificationIdx_eq_one`), the kernel condition for an unramified or cyclic middle
(`kernel_condition_of_unramified_top`, `kernel_condition_of_prime_top_cyclic_middle_coprime`),
and Hilbert 90 are all in the commons.
-/

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum

/-! ## The valuation formula: the norm index splits as `f` times the unit part

Writing `v` for the value-group logarithm `unitsValLog` of `B = Q.adicCompletion K` and
`U = v.ker = (Q.adicCompletionIntegers K).unitGroup`, the identity `v (N u) = (v u)^f`
(`unitsValLog_norm`, `f` = inertia degree) shows that the norm group has value group `fℤ`, so
the index of the norm group splits as `f` times the index of `U ∩ N_{E/B}(Eˣ)` in `U`.
-/

namespace NormIndexUnits

lemma toAdd_pow_multiplicative (a : Multiplicative ℤ) (n : ℕ) :
    (a ^ n).toAdd = (n : ℤ) * a.toAdd := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, show (a ^ k * a).toAdd = (a ^ k).toAdd + a.toAdd from rfl, ih]
      push_cast
      ring

lemma ofAdd_pow (a : ℤ) (n : ℕ) :
    (Multiplicative.ofAdd a) ^ n = Multiplicative.ofAdd ((n : ℤ) * a) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow_multiplicative]
  rfl

noncomputable def multIntToZMod (n : ℕ) : Multiplicative ℤ →* Multiplicative (ZMod n) :=
  AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))

lemma multIntToZMod_apply (n : ℕ) (z : Multiplicative ℤ) :
    multIntToZMod n z = Multiplicative.ofAdd ((z.toAdd : ℤ) : ZMod n) := rfl

lemma multIntToZMod_ofAdd_pow_self (n : ℕ) (a : ℤ) :
    multIntToZMod n ((Multiplicative.ofAdd a) ^ n) = 1 := by
  have hzero : (((n : ℤ)) : ZMod n) = 0 := by rw [Int.cast_natCast, ZMod.natCast_self]
  rw [ofAdd_pow, multIntToZMod_apply]
  change Multiplicative.ofAdd ((((n : ℤ) * a : ℤ)) : ZMod n) = 1
  rw [Int.cast_mul, hzero, zero_mul]
  rfl

lemma multIntToZMod_surjective (n : ℕ) : Function.Surjective (multIntToZMod n) := by
  intro y
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (b := y.toAdd)
  refine ⟨Multiplicative.ofAdd z, ?_⟩
  rw [multIntToZMod_apply]
  exact congrArg Multiplicative.ofAdd hz

lemma multIntToZMod_eq_one_iff (n : ℕ) (z : Multiplicative ℤ) :
    multIntToZMod n z = 1 ↔ (n : ℤ) ∣ z.toAdd := by
  rw [multIntToZMod_apply, ← ZMod.intCast_zmod_eq_zero_iff_dvd (a := z.toAdd) (b := n)]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    simpa using h'
  · intro h
    rw [h]
    rfl

end NormIndexUnits

namespace NormIndexUnits

/-- **The valuation formula for the norm index.**  The index of the norm group splits as the
inertia degree times the index of the unit part. -/
theorem natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K))) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) *
        (MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K))).relIndex (adicUnitsVal K Q) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  set f := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) with hf
  set B := (Q.adicCompletion K)ˣ with hB
  set U : Subgroup B := adicUnitsVal K Q with hU
  set N : Subgroup B := MonoidHom.range
    (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)) with hN
  set w : B →* Multiplicative (ZMod f) :=
    (multIntToZMod f).comp (unitsValLog (Q.adicCompletion K)) with hw
  have hw_apply : ∀ x : B, w x = multIntToZMod f (unitsValLog (Q.adicCompletion K) x) := fun x => rfl
  have hUker : U = (unitsValLog (Q.adicCompletion K)).ker := rfl
  have hNle : N ≤ w.ker := by
    rintro x ⟨u, rfl⟩
    rw [MonoidHom.mem_ker, hw_apply, unitsValLog_norm Q q hq u,
      unitsValLog_apply (q.adicCompletion L)]
    exact multIntToZMod_ofAdd_pow_self f _
  -- `w.ker = U ⊔ N`
  have hwk : U ⊔ N = w.ker := by
    refine le_antisymm (sup_le ?_ hNle) ?_
    · intro x hx
      rw [MonoidHom.mem_ker, hw_apply, show unitsValLog (Q.adicCompletion K) x = 1 from
        MonoidHom.mem_ker.mp hx, map_one]
    · intro x hx
      rw [MonoidHom.mem_ker, hw_apply, multIntToZMod_eq_one_iff] at hx
      obtain ⟨m, hm⟩ := hx
      obtain ⟨u, hu⟩ := unitsValLog_adicCompletion_surjective L q (Multiplicative.ofAdd m)
      set z : B := Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K) u with hz
      have hzval : unitsValLog (Q.adicCompletion K) z = unitsValLog (Q.adicCompletion K) x := by
        apply Multiplicative.toAdd.injective
        rw [hz, unitsValLog_norm Q q hq u, hu, toAdd_pow_multiplicative, hm, ← hf]
        rfl
      have hmem : x * z⁻¹ ∈ U := by
        rw [hUker, MonoidHom.mem_ker, map_mul, map_inv, hzval, mul_inv_cancel]
      refine Subgroup.mem_sup.mpr ⟨x * z⁻¹, hmem, z, ⟨u, hz⟩, ?_⟩
      simp
  have hcard : (U ⊔ N).index = f := by
    rw [hwk, Subgroup.index_ker]
    have hrange : w.range = ⊤ := MonoidHom.range_eq_top.mpr
      ((multIntToZMod_surjective f).comp (unitsValLog_adicCompletion_surjective K Q))
    rw [hrange, Subgroup.card_top]
    exact Nat.card_zmod f
  haveI : N.Normal := Subgroup.normal_of_isMulCommutative N
  calc Nat.card (B ⧸ N) = N.index := Subgroup.index_eq_card N
    _ = N.relIndex (U ⊔ N) * (U ⊔ N).index :=
        (Subgroup.relIndex_mul_index (le_sup_right : N ≤ U ⊔ N)).symm
    _ = N.relIndex U * (U ⊔ N).index := by rw [Subgroup.relIndex_sup_right (H := U)]
    _ = N.relIndex U * f := by rw [hcard]
    _ = f * N.relIndex U := by rw [mul_comm]


/-- **Reduction of the lower bound to the unit statement** (Herbrand's theorem).

If the unit part `[U : U ∩ N_{E/B}(Eˣ)]` of the norm index equals the ramification index `e`, then
the full norm index is the degree `[E : B] = e·f`: combine the valuation formula with
`finrank = e·f`.  This isolates the class-field-theoretic input as a statement about the unit
groups only. -/
theorem finrank_le_index_range_norm_adicCompletion_of_units
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    (MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K))).relIndex (adicUnitsVal K Q) =
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) →
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) ≤
        (MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K))).index := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro hun
  have hval := natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux Q q hq
  rw [Subgroup.index_eq_card, hval, hun]
  rw [← Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq]
  exact le_of_eq (Nat.mul_comm _ _)

end NormIndexUnits


/-! ## The "inertia degree" half of the lower bound

The value-group logarithm `unitsValLog (Q.adicCompletion K) : (Q.adicCompletion K)ˣ →* Multiplicative ℤ`
is surjective with kernel the unit group of the valuation ring, and
`unitsValLog (N u) = (unitsValLog u) ^ f` where `f` is the inertia degree of `q | Q`.  Hence the
norm group is contained in the preimage of `fℤ`, giving the lower bound `f ≤ #(Bˣ ⧸ N)`.  -/

open NormIndexUnits

/-- **The norm index is at least the inertia degree.**  For `L/K` a finite Galois extension of
number fields and `q | Q` a place, with `B = Q.adicCompletion K` and `E = q.adicCompletion L`, the
index of the norm group `N_{E/B}(Eˣ)` in `Bˣ` is at least the inertia degree of `q` over `Q`. -/
theorem inertiaDeg_le_natCard_quotient_units_range_norm_adicCompletion
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤
      Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K))) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  set f := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) with hf
  set B := (Q.adicCompletion K)ˣ with hB
  set N : Subgroup B := MonoidHom.range
    (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)) with hN
  set w : B →* Multiplicative (ZMod f) :=
    (multIntToZMod f).comp (unitsValLog (Q.adicCompletion K)) with hw
  have hw_apply : ∀ x : B, w x = multIntToZMod f (unitsValLog (Q.adicCompletion K) x) := fun x => rfl
  have hNle : N ≤ w.ker := by
    rintro x ⟨u, rfl⟩
    rw [MonoidHom.mem_ker, hw_apply, unitsValLog_norm Q q hq u,
      unitsValLog_apply (q.adicCompletion L)]
    exact multIntToZMod_ofAdd_pow_self f _
  have hwsurj : Function.Surjective w :=
    (multIntToZMod_surjective f).comp (unitsValLog_adicCompletion_surjective K Q)
  haveI hNnormal : N.Normal := Subgroup.normal_of_isMulCommutative N
  haveI hKnormal : w.ker.Normal := MonoidHom.normal_ker w
  have hsurj : Function.Surjective
      (QuotientGroup.lift N (QuotientGroup.mk' w.ker) (by
        rw [QuotientGroup.ker_mk']
        exact hNle)) := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective w.ker y
    refine ⟨QuotientGroup.mk x, ?_⟩
    rw [← hx, QuotientGroup.lift_mk']
  have hcard : Nat.card (B ⧸ w.ker) = f := by
    rw [(Subgroup.index_eq_card w.ker).symm, Subgroup.index_ker]
    have hrange : w.range = ⊤ := MonoidHom.range_eq_top.mpr hwsurj
    rw [hrange, Subgroup.card_top]
    exact Nat.card_zmod f
  haveI : Finite (B ⧸ N) :=
    finite_quotient_units_range_norm_adicCompletion (K := K) (L := L) Q q hq
  calc f = Nat.card (B ⧸ w.ker) := hcard.symm
    _ ≤ Nat.card (B ⧸ N) := Nat.card_le_card_of_surjective _ hsurj

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

namespace PrimeTopFracture

/-- **Fracture step**: the prime-top kernel condition follows from its unit form.
Pure valuation theory: if `N_{B/F}(x) = 1` then `v_B(x)^f = v_F(1) = 1`, so `x` is a unit of `B`,
and the unit statement applies. -/
theorem kernel_condition_of_prime_top_adicCompletion_of_units
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    (∀ u : adicUnitsVal L₁ q₁,
        Algebra.norm (q₀.adicCompletion L₀) ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 →
        ∃ w : (q₂.adicCompletion L₂)ˣ,
          Algebra.norm (q₁.adicCompletion L₁) (w : q₂.adicCompletion L₂) =
            ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁)) →
      MonoidHom.ker (Units.map (Algebra.norm (q₀.adicCompletion L₀) :
          q₁.adicCompletion L₁ →* q₀.adicCompletion L₀)) ≤
        MonoidHom.range (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁)) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  intro hunit x hx
  rw [MonoidHom.mem_ker] at hx
  set f := q₁.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₀) with hf
  have hfne : f ≠ 0 := (Ideal.inertiaDeg_pos (q := q₁.asIdeal)
    (R := NumberField.RingOfIntegers L₀)).ne'
  -- `x` is a unit of `q₁.adicCompletion L₁`
  have hxU : x ∈ adicUnitsVal L₁ q₁ := by
    have hkey := unitsValLog_norm q₀ q₁ hq₁ x
    rw [hx, map_one] at hkey
    have hpow : (unitsValLog (q₁.adicCompletion L₁) x) ^ f = (1 : Multiplicative ℤ) ^ f := by
      rw [← hkey, one_pow]
    have h1 : unitsValLog (q₁.adicCompletion L₁) x = 1 :=
      pow_right_injective_zint hfne hpow
    simpa [adicUnitsVal, MonoidHom.mem_ker] using h1
  have hxval : Algebra.norm (q₀.adicCompletion L₀) ((x : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 := by
    have h := congrArg (fun u : (q₀.adicCompletion L₀)ˣ => (u : q₀.adicCompletion L₀)) hx
    simpa using h
  obtain ⟨w, hw⟩ := hunit ⟨x, hxU⟩ hxval
  exact ⟨w, Units.ext hw⟩

end PrimeTopFracture

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false

theorem exists_algEquiv_lift {F B E : Type*} [Field F] [Field B] [Field E]
    [Algebra F B] [Algebra F E] [Algebra B E] [IsScalarTower F B E]
    [FiniteDimensional F B] [FiniteDimensional F E] [FiniteDimensional B E]
    [IsGalois F B] [IsGalois F E] [IsGalois B E]
    (σ : B ≃ₐ[F] B) :
    ∃ τ : E ≃ₐ[F] E, ∀ x : B, τ (algebraMap B E x) = algebraMap B E (σ x) := by
  let hBE : B →ₐ[F] E := IsScalarTower.toAlgHom F B E
  let K : IntermediateField F E := hBE.fieldRange
  let i : B ≃ₐ[F] ↥K := AlgEquiv.ofInjectiveField hBE
  haveI hKgal : IsGalois F ↥K := IsGalois.of_algEquiv i
  haveI hKnormal : Normal F ↥K := hKgal.to_normal
  let σK : ↥K ≃ₐ[F] ↥K := i.symm.trans (σ.trans i)
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥K) (E := E) σK
  refine ⟨τ, ?_⟩
  intro x
  have hx : (i x : E) = algebraMap B E x := rfl
  have h2 : ((AlgEquiv.restrictNormalHom ↥K τ) (i x) : E) = (σK (i x) : E) := by
    rw [hτ]
  have h3 : τ ((i x : E)) = ((AlgEquiv.restrictNormalHom ↥K τ) (i x) : E) :=
    (AlgEquiv.restrictNormalHom_apply K τ (i x)).symm
  have h4 : (σK (i x) : E) = algebraMap B E (σ x) := by
    show ((i.symm.trans (σ.trans i)) (i x) : E) = _
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply]
    have : i.symm (i x) = x := i.symm_apply_apply x
    rw [this]
    rfl
  rw [← hx, h3, h2, h4]

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

/-! ## The `Y`-action on the norm group (the `I_Y`-coprimality step of the fracture)

The norm group `N_{E/B}(Eˣ)` is stable under any automorphism of `B` that lifts to `E`:
for compatible `σ : B ≃ₐ[F] B`, `τ : E ≃ₐ[F] E` one has `σ (N_{E/B} x) = N_{E/B} (τ x)`
(`Algebra.norm_eq_of_equiv_equiv`).  This is what makes the `Gal(B/F)`-action on the
quotient `Bˣ ⧸ N_{E/B}(Eˣ)` (and on `U_B ⧸ (U_B ∩ N_{E/B}(Eˣ))`) well defined.
-/

theorem map_norm_eq_of_apply_eq {F B E : Type*} [Field F] [Field B] [Field E]
    [Algebra F B] [Algebra F E] [Algebra B E] [IsScalarTower F B E]
    (σ : B ≃ₐ[F] B) (τ : E ≃ₐ[F] E)
    (h : ∀ x : B, τ (algebraMap B E x) = algebraMap B E (σ x)) (x : E) :
    σ (Algebra.norm B x) = Algebra.norm B (τ x) := by
  have he : RingHom.comp (algebraMap B E) ↑σ.toRingEquiv =
      RingHom.comp ↑τ.toRingEquiv (algebraMap B E) := by
    ext y
    exact (h y).symm
  have key := Algebra.norm_eq_of_equiv_equiv σ.toRingEquiv τ.toRingEquiv he x
  rw [key]
  exact RingEquiv.apply_symm_apply σ.toRingEquiv (Algebra.norm B (τ.toRingEquiv x))

/-- The norm group of units is stable under any automorphism of the base that lifts. -/
theorem map_range_norm_units_le_of_apply_eq {F B E : Type*} [Field F] [Field B] [Field E]
    [Algebra F B] [Algebra F E] [Algebra B E] [IsScalarTower F B E]
    (σ : B ≃ₐ[F] B) (τ : E ≃ₐ[F] E)
    (h : ∀ x : B, τ (algebraMap B E x) = algebraMap B E (σ x)) :
    (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).map
        (Units.map σ.toRingEquiv.toMonoidHom) ≤
      MonoidHom.range (Units.map (Algebra.norm B : E →* B)) := by
  rintro y ⟨u, hu, rfl⟩
  obtain ⟨w, rfl⟩ := hu
  refine ⟨Units.map τ.toRingEquiv.toMonoidHom w, ?_⟩
  ext
  simp only [Units.coe_map]
  exact (map_norm_eq_of_apply_eq σ τ h (w : E)).symm

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- **The `I_Y`-coprimality step.**  In the prime-top situation (`[E : B₁] = p` prime, `E/B`
abelian not needed here, but `#Gal(B₁/B)` coprime to `p - 1`), every `σ ∈ Gal(B₁/B)` acts trivially
on `B₁ˣ ⧸ N_{E/B₁}(Eˣ)`: for all `u`, `σ u / u ∈ N_{E/B₁}(Eˣ)`. -/
theorem augmentation_adicUnitsVal_le_range_norm_of_prime_top
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    Nat.Prime (Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂)) →
    (Nat.card (q₁.adicCompletion L₁ ≃ₐ[q₀.adicCompletion L₀] q₁.adicCompletion L₁)).Coprime
        (Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) - 1) →
    ∀ (σ : q₁.adicCompletion L₁ ≃ₐ[q₀.adicCompletion L₀] q₁.adicCompletion L₁)
      (u : adicUnitsVal L₁ q₁),
      Units.map σ.toRingEquiv.toMonoidHom u / u ∈
        MonoidHom.range (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁)) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  intro hprime hcop σ u
  haveI hst : IsScalarTower (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    simpa [RingHom.comp_apply] using (RingHom.congr_fun
      (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp q₀ q₁ q₂ hq₁ hq₂ hq₀₂) x).symm
  haveI : FiniteDimensional (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    module_finite_adicCompletion q₀ q₁ hq₁
  haveI : FiniteDimensional (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₀ q₂ hq₀₂
  haveI : IsGalois (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    isGalois_adicCompletion q₀ q₁ hq₁
  haveI : IsGalois (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₀ q₂ hq₀₂
  haveI : IsGalois (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₁ q₂ hq₂
  haveI : FiniteDimensional (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₁ q₂ hq₂
  have hcard : Nat.card (q₂.adicCompletion L₂ ≃ₐ[q₁.adicCompletion L₁] q₂.adicCompletion L₂) =
      Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    IsGalois.card_aut_eq_finrank _ _
  haveI : Fact (Nat.Prime (Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂))) :=
    ⟨hprime⟩
  haveI : IsCyclic (q₂.adicCompletion L₂ ≃ₐ[q₁.adicCompletion L₁] q₂.adicCompletion L₂) :=
    isCyclic_of_prime_card hcard
  have hnorm : Nat.card ((q₁.adicCompletion L₁)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁))) =
      Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) := by
    rw [natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base' (K := L₀) (Q := q₀)
      (B := q₁.adicCompletion L₁) (B₁ := q₂.adicCompletion L₂), hcard]
  exact Commons.FieldTheory.Galois.div_mem_range_norm_of_prime_quotient_coprime
    (B := q₀.adicCompletion L₀) (B₁ := q₁.adicCompletion L₁) (E := q₂.adicCompletion L₂)
    (by rw [hnorm]; exact hprime) (by rw [hnorm]; exact hcop) σ u

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- **The unramified case of the unit-level prime-top statement.**  If the top step `E/B` is
unramified, every unit of `B` is a norm from `E` (the norm is surjective on units), so the
`H₂`-torsor statement holds for all `u`. -/
theorem forall_ker_adicUnitsVal_le_range_norm_of_ramificationIdx_eq_one
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal)
    (hunr : q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) = 1) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    ∀ u : adicUnitsVal L₁ q₁,
      ∃ w : (q₂.adicCompletion L₂)ˣ,
        Algebra.norm (q₁.adicCompletion L₁) (w : q₂.adicCompletion L₂) =
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  intro u
  haveI : IsGalois (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₁ q₂ hq₂
  haveI : FiniteDimensional (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₁ q₂ hq₂
  have hv : Valued.v (R := q₁.adicCompletion L₁) (Γ₀ := WithZero (Multiplicative ℤ))
      ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 :=
    (mem_adicUnitsVal L₁ q₁ (u : (q₁.adicCompletion L₁)ˣ)).mp u.2
  obtain ⟨x, hx⟩ := norm_units_surjective_of_ramificationIdx_eq_one q₁ q₂ hq₂ hunr
    ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) hv
  have hxu : x ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hx
    exact (Units.ne_zero (u : (q₁.adicCompletion L₁)ˣ)) hx.symm
  exact ⟨Units.mk0 x hxu, by rw [Units.val_mk0]; exact hx⟩

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

/-- **Reduction of the `H₂`-torsor statement to the totally ramified prime case.**  If the top step
`E/B` is either unramified or has ramification index equal to the (prime) degree, then the
statement holds: the ramification index divides the prime degree, so it is `1` or `p`, and the case
`e = 1` is the proven unramified case. -/
theorem ker_adicUnitsVal_le_range_norm_of_prime_top_of_ramified
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    (∀ u : adicUnitsVal L₁ q₁,
      q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) =
          Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) →
      Algebra.norm (q₀.adicCompletion L₀)
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 →
      ∃ w : (q₂.adicCompletion L₂)ˣ,
        Algebra.norm (q₁.adicCompletion L₁) (w : q₂.adicCompletion L₂) =
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁)) →
    (∀ a b : q₂.adicCompletion L₂ ≃ₐ[q₀.adicCompletion L₀] q₂.adicCompletion L₂, a * b = b * a) →
    Nat.Prime (Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂)) →
    ∀ u : adicUnitsVal L₁ q₁,
      Algebra.norm (q₀.adicCompletion L₀)
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 →
      ∃ w : (q₂.adicCompletion L₂)ˣ,
        Algebra.norm (q₁.adicCompletion L₁) (w : q₂.adicCompletion L₂) =
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  intro hram _hcomm hprime u hu
  -- the ramification index divides the prime degree
  have hdvd : q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) ∣
      Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    ⟨q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₁), by
      rw [Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        q₁ q₂ hq₂]⟩
  rcases Nat.Prime.eq_one_or_self_of_dvd hprime
    (q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁)) hdvd with h1 | hp
  · -- unramified case
    obtain ⟨w, hw⟩ := forall_ker_adicUnitsVal_le_range_norm_of_ramificationIdx_eq_one
      q₀ q₁ q₂ hq₁ hq₂ hq₀₂ h1 u
    exact ⟨w, hw⟩
  · -- totally ramified prime case: the hypothesis
    exact hram u hp hu

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- **Node 1 of the totally ramified plan: the unit part of the norm group.**

A *unit* of `B` is a norm from `E` if and only if it is the norm of a *unit* of `E`:
`U_B ⊓ N_{E/B}(Eˣ) = N_{E/B}(U_E)` as subgroups of `Bˣ`.

Both inclusions are the valuation identity `v_B(N x) = f · v_E(x)` (`unitsValLog_norm` at the pair
`(q₁, q₂)`) together with `f ≠ 0`. -/
theorem inf_adicUnitsVal_range_norm_units_eq_map_adicUnitsVal
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    adicUnitsVal L₁ q₁ ⊓ MonoidHom.range (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
        q₂.adicCompletion L₂ →* q₁.adicCompletion L₁)) =
      Subgroup.map (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁)) (adicUnitsVal L₂ q₂) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  haveI : IsGalois (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₁ q₂ hq₂
  haveI : FiniteDimensional (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₁ q₂ hq₂
  set f := q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₁) with hf
  have hfne : f ≠ 0 := (Ideal.inertiaDeg_pos (q := q₂.asIdeal)
    (R := NumberField.RingOfIntegers L₁)).ne'
  ext y
  constructor
  · rintro ⟨hyU, x, rfl⟩
    -- `x : (q₂.adicCompletion L₂)ˣ`; show `x` is a unit of `E`
    have hkey := unitsValLog_norm q₁ q₂ hq₂ x
    have h1 : unitsValLog (q₁.adicCompletion L₁)
        (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁) x) = 1 :=
      (unitsValLog_eq_one_iff _).mpr ((mem_adicUnitsVal L₁ q₁ _).mp hyU)
    rw [h1] at hkey
    have hx : unitsValLog (q₂.adicCompletion L₂) x = 1 :=
      pow_right_injective_zint hfne (by rw [← hkey, one_pow])
    exact ⟨x, (mem_adicUnitsVal L₂ q₂ x).mpr ((unitsValLog_eq_one_iff _).mp hx), rfl⟩
  · rintro ⟨x, hxU, rfl⟩
    refine ⟨?_, ⟨x, rfl⟩⟩
    refine (mem_adicUnitsVal L₁ q₁ _).mpr ?_
    refine (unitsValLog_eq_one_iff _).mp ?_
    rw [unitsValLog_norm q₁ q₂ hq₂ x,
      (unitsValLog_eq_one_iff _).mpr ((mem_adicUnitsVal L₂ q₂ x).mp hxU), one_pow]

end Commons.NumberTheory.NumberField.Completion

namespace Commons.FieldTheory.Galois

/-- The fixing subgroup of a binary supremum is the intersection of the fixing subgroups. -/
lemma fixingSubgroup_sup {F M : Type*} [Field F] [Field M] [Algebra F M]
    (L₁ L₂ : IntermediateField F M) :
    (L₁ ⊔ L₂).fixingSubgroup = L₁.fixingSubgroup ⊓ L₂.fixingSubgroup := by
  apply le_antisymm
  · exact le_inf (IntermediateField.fixingSubgroup_antitone le_sup_left)
      (IntermediateField.fixingSubgroup_antitone le_sup_right)
  · rw [← IntermediateField.le_iff_le (H := L₁.fixingSubgroup ⊓ L₂.fixingSubgroup)
      (K := L₁ ⊔ L₂)]
    refine sup_le ?_ ?_
    · rw [IntermediateField.le_iff_le (H := L₁.fixingSubgroup ⊓ L₂.fixingSubgroup) (K := L₁)]
      exact inf_le_left
    · rw [IntermediateField.le_iff_le (H := L₁.fixingSubgroup ⊓ L₂.fixingSubgroup) (K := L₂)]
      exact inf_le_right

/-- **The Galois group of a compositum of two independent Galois extensions.**

Let `M/F` be a finite Galois extension of fields and let `L₁ L₂ : IntermediateField F M` be
finite Galois subextensions with `L₁ ⊔ L₂ = ⊤` and `L₁ ⊓ L₂ = ⊥`.  Then the restriction maps
`Gal(M/F) → Gal(Lᵢ/F)` combine into an isomorphism `Gal(M/F) ≃* Gal(L₁/F) × Gal(L₂/F)`.

This is the standard "compositum of linearly disjoint Galois extensions" statement: the map is
injective because an automorphism fixing `L₁` and `L₂` pointwise fixes their compositum `⊤`, and
it is surjective by counting, since `[L₁ ⊔ L₂ : F] = [L₁ : F] · [L₂ : F]` when `L₁ ⊓ L₂ = ⊥`.

It is the structure theorem for the field `M = L₁·L₂` used by the unramified twist: it turns
`Gal(M/F)` into a direct product, so that inflation along the first factor followed by restriction
to the second is the coefficient map (see the roadmap note). -/
theorem galoisGroup_sup_mulEquiv_prod {F M : Type*} [Field F] [Field M] [Algebra F M]
    [FiniteDimensional F M] [IsGalois F M]
    (L₁ L₂ : IntermediateField F M) [FiniteDimensional F ↥L₁] [FiniteDimensional F ↥L₂]
    [IsGalois F ↥L₁] [IsGalois F ↥L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) (hinf : L₁ ⊓ L₂ = ⊥) :
    Nonempty ((M ≃ₐ[F] M) ≃* ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂))) := by
  haveI hN₁ : Normal F ↥L₁ := inferInstance
  haveI hN₂ : Normal F ↥L₂ := inferInstance
  let φ : (M ≃ₐ[F] M) →* ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) :=
    MonoidHom.prod (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₁)
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₂)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    have h1 : (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₁) σ = 1 := by
      have h := congrArg Prod.fst hσ
      simpa [φ] using h
    have h2 : (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₂) σ = 1 := by
      have h := congrArg Prod.snd hσ
      simpa [φ] using h
    have hmem1 : σ ∈ L₁.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have key := AlgEquiv.restrictNormalHom_apply (F := F) (K₁ := M) L₁ σ ⟨x, hx⟩
      rw [h1] at key
      simpa using key.symm
    have hmem2 : σ ∈ L₂.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have key := AlgEquiv.restrictNormalHom_apply (F := F) (K₁ := M) L₂ σ ⟨x, hx⟩
      rw [h2] at key
      simpa using key.symm
    have hbot : L₁.fixingSubgroup ⊓ L₂.fixingSubgroup = ⊥ := by
      rw [← fixingSubgroup_sup L₁ L₂, hsup]
      rw [Subgroup.eq_bot_iff_forall]
      intro τ hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      ext x
      exact hτ x trivial
    have hmem : σ ∈ L₁.fixingSubgroup ⊓ L₂.fixingSubgroup := ⟨hmem1, hmem2⟩
    rw [hbot] at hmem
    simpa using hmem
  refine ⟨MulEquiv.ofBijective φ ⟨hinj, ?_⟩⟩
  have hcard : Nat.card (M ≃ₐ[F] M) =
      Nat.card ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) := by
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank F M, IsGalois.card_aut_eq_finrank F ↥L₁,
      IsGalois.card_aut_eq_finrank F ↥L₂]
    have hd := IntermediateField.LinearDisjoint.finrank_sup
      (IntermediateField.LinearDisjoint.of_inf_eq_bot (F := F) hinf)
    rw [hsup] at hd
    rw [show Module.finrank F ↥(⊤ : IntermediateField F M) = Module.finrank F M from
      finrank_top F M] at hd
    exact hd
  haveI : Fintype ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) := Fintype.ofFinite _
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]; exact hcard⟩
  exact hbij.2

end Commons.FieldTheory.Galois

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Representation groupCohomology Rep

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient morphism of the unramified twist: the inclusion of the `(1 × Q)`-invariants
of a representation `A` of `P × Q` into `A`, transported to a morphism of representations of `P`
along `QuotientGroup.mk' (ker fst)`. -/
noncomputable def coeffMor {k : Type u} [CommRing k] {P Q : Type u} [Group P] [Group Q]
    (A : Rep k (P × Q)) :
    (Rep.resFunctor (MonoidHom.inl P Q)).obj
        ((Rep.resFunctor (QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q)))).obj
          (A.quotientToInvariants (MonoidHom.ker (MonoidHom.fst P Q)))) ⟶
      (Rep.resFunctor (MonoidHom.inl P Q)).obj A :=
  (Rep.resFunctor (MonoidHom.inl P Q)).map
      (ofHom (A.ρ.quotientToInvariants_lift (MonoidHom.ker (MonoidHom.fst P Q)))) ≫
    𝟙 (Rep.res (MonoidHom.inl P Q) A)

set_option backward.isDefEq.respectTransparency false in
/-- **The formal identity of the unramified twist** (general coefficient ring).

With `S := ker (fst : P × Q →* P) = 1 × Q` and `A` a representation of `P × Q`, the composite

`H²((P×Q) ⧸ S, A^S) --Inf_{S}--> H²(P×Q, A) --Res_{inl}--> H²(P, A)`

of the inflation along the projection onto the second factor with the restriction to the
complementary factor `P = P × 1` is the map on `H²` induced by the coefficient morphism
`coeffMor A` (the inclusion of the `S`-invariants `A^S ↪ A`), transported along the canonical
isomorphism `(QuotientGroup.mk' S).comp (MonoidHom.inl P Q) : P ≃* (P × Q) ⧸ S`.

Formally this is the functoriality `map_comp` of group cohomology; the content is the
identification of the right hand side as the *coefficient map*, i.e. that restriction to the
complementary factor inverts the inflation. -/
theorem inf_comp_res_eq_map_coeff {k : Type u} [CommRing k] {P Q : Type u} [Group P] [Group Q]
    (A : Rep k (P × Q)) :
    (groupCohomology.infNatTrans k (MonoidHom.ker (MonoidHom.fst P Q)) 2).app A ≫
      (groupCohomology.resNatTrans k (G := P) (H := P × Q) (MonoidHom.inl P Q) 2).app A
    = groupCohomology.map
        ((QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q))).comp (MonoidHom.inl P Q))
        (coeffMor A) 2 := by
  have h1 : (groupCohomology.infNatTrans k (MonoidHom.ker (MonoidHom.fst P Q)) 2).app A
      = groupCohomology.map (QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q)))
          (ofHom (A.ρ.quotientToInvariants_lift (MonoidHom.ker (MonoidHom.fst P Q)))) 2 := rfl
  have h2 : (groupCohomology.resNatTrans k (G := P) (H := P × Q) (MonoidHom.inl P Q) 2).app A
      = groupCohomology.map (MonoidHom.inl P Q) (𝟙 (Rep.res (MonoidHom.inl P Q) A)) 2 := rfl
  rw [h1, h2, ← groupCohomology.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The underlying linear map of the coefficient morphism is the inclusion of the invariants
`A^{1 × Q} ↪ A`. -/
theorem coe_coeffMor {k : Type u} [CommRing k] {P Q : Type u} [Group P] [Group Q]
    (A : Rep k (P × Q)) :
    (coeffMor A).hom.toLinearMap = Submodule.subtype _ := by
  rfl

/-- **The formal identity of the unramified twist**, in the coefficient ring `ℤ` (the one used
for the units of a local field): the `ℤ`-linear version of `inf_comp_res_eq_map_coeff`. -/
theorem H2_inf_comp_res_eq_map_coeff {P Q : Type} [Group P] [Group Q] (A : Rep ℤ (P × Q)) :
    (groupCohomology.infNatTrans ℤ (MonoidHom.ker (MonoidHom.fst P Q)) 2).app A ≫
      (groupCohomology.resNatTrans ℤ (G := P) (H := P × Q) (MonoidHom.inl P Q) 2).app A
    = groupCohomology.map
        ((QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q))).comp (MonoidHom.inl P Q))
        (coeffMor A) 2 :=
  inf_comp_res_eq_map_coeff A

/-- The canonical map `P → (P × Q) ⧸ (1 × Q)` through which the coefficient morphism of the
unramified twist is transported is a bijection (indeed an isomorphism of groups): it identifies
the complementary factor `P = P × 1` with the quotient by the other one. -/
theorem bijective_mk'_comp_inl {P Q : Type} [Group P] [Group Q] :
    Function.Bijective ((QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q))).comp
      (MonoidHom.inl P Q)) := by
  refine ⟨?_, ?_⟩
  · intro p p' h
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h
    obtain ⟨z, hz, hz'⟩ := (QuotientGroup.mk'_eq_mk' _).mp h
    have hz1 : (MonoidHom.fst P Q) z = 1 := MonoidHom.mem_ker.mp hz
    have := congrArg (MonoidHom.fst P Q) hz'
    simpa [map_mul, hz1] using this
  · intro x
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (MonoidHom.ker (MonoidHom.fst P Q)) x
    refine ⟨MonoidHom.fst P Q γ, ?_⟩
    rw [MonoidHom.comp_apply]
    refine ((QuotientGroup.mk'_eq_mk' _).mpr ⟨(1, γ.2), ?_, ?_⟩)
    · exact MonoidHom.mem_ker.mpr rfl
    · simp

end Commons.RepresentationTheory.GroupCohomology

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false

/-- **Every unit of the base field is a norm from the (unramified) top.**

Let `q₀ ⊆ q₁ ⊆ q₂` be a tower of places of number fields `L₀ ⊆ L₁ ⊆ L₂` such that the top step
`L₂_{q₂} / L₁_{q₁}` is unramified (`e = 1`), and assume that the inertia degree `f(q₂|q₁)` divides
the ramification index `e(q₁|q₀)`.  Then every unit of `L₀_{q₀}` is the norm of a unit of
`L₂_{q₂}` over `L₁_{q₁}`:

`(L₀_{q₀})ˣ ⊆ N_{L₂_{q₂} / L₁_{q₁}}((L₂_{q₂})ˣ)`.

This is the *arithmetic* content of the residual case of Milne's divisibility step
(Milne, *CFT*, III.2) for the unramified twist.  In the application, `L₁/L₀` is totally
ramified at `q₀` (`e(q₁|q₀) = [L₁:L₀]`), `L₂/L₁` is unramified at `q₁` (`e(q₂|q₁) = 1`) with
`f(q₂|q₁) = [L₁:L₀]`, so the divisibility hypothesis holds with equality; the argument is the
explicit description of the norm group of an unramified extension
(`dvd_inertiaDeg_log_val_iff_exists_norm_of_ramificationIdx_eq_one`): a unit of `L₀` has
`v_{L₁}`-valuation a multiple of `e(q₁|q₀)`, hence (by the hypothesis) a multiple of `f(q₂|q₁)`,
and precisely those elements are norms. -/
theorem exists_norm_units_of_unramified_top_and_dvd_ramificationIdx
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hunr : q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) = 1)
    (hdvd : q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₁) ∣
      q₁.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₀)) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    ∀ x : (q₀.adicCompletion L₀)ˣ,
      ∃ y : (q₂.adicCompletion L₂)ˣ,
        Algebra.norm (q₁.adicCompletion L₁) (y : q₂.adicCompletion L₂) =
          (Units.map (algebraMap (q₀.adicCompletion L₀) (q₁.adicCompletion L₁)).toMonoidHom x :
            (q₁.adicCompletion L₁)ˣ) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  haveI : IsGalois (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    isGalois_adicCompletion q₀ q₁ hq₁
  haveI : FiniteDimensional (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    module_finite_adicCompletion q₀ q₁ hq₁
  haveI : IsGalois (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₁ q₂ hq₂
  haveI : FiniteDimensional (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₁ q₂ hq₂
  intro x
  set xE : (q₁.adicCompletion L₁)ˣ :=
    Units.map (algebraMap (q₀.adicCompletion L₀) (q₁.adicCompletion L₁)).toMonoidHom x with hxE
  have hpow : ∀ (a : Multiplicative ℤ) (k : ℕ), (a ^ k).toAdd = (k : ℤ) * a.toAdd := by
    intro a k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, show (a ^ j * a).toAdd = (a ^ j).toAdd + a.toAdd from rfl, ih]
        push_cast
        ring
  -- the logarithm of the valuation of the image of `x` in `L₁_{q₁}`
  have hlog : WithZero.log (Valued.v (R := q₁.adicCompletion L₁)
        (Γ₀ := WithZero (Multiplicative ℤ)) (xE : q₁.adicCompletion L₁)) =
      (q₁.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₀) : ℤ) *
        Multiplicative.toAdd (unitsValLog (q₀.adicCompletion L₀) x) := by
    have h := congrArg Multiplicative.toAdd (unitsValLog_algebraMap q₀ q₁ hq₁ x)
    rw [← hxE] at h
    rw [unitsValLog_apply] at h
    rw [hpow] at h
    exact h
  -- the divisibility hypothesis in `ℤ`
  have hdvd' : (q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₁) : ℤ) ∣
      WithZero.log (Valued.v (R := q₁.adicCompletion L₁)
        (Γ₀ := WithZero (Multiplicative ℤ)) (xE : q₁.adicCompletion L₁)) := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨(c : ℤ) * Multiplicative.toAdd (unitsValLog (q₀.adicCompletion L₀) x), ?_⟩
    rw [hlog, hc]
    push_cast
    ring
  -- the explicit norm group of the unramified extension `L₂_{q₂} / L₁_{q₁}`
  obtain ⟨y, hy⟩ := (dvd_inertiaDeg_log_val_iff_exists_norm_of_ramificationIdx_eq_one
    (Q := q₁) (q := q₂) hq₂ hunr (xE : q₁.adicCompletion L₁) (Units.ne_zero xE)).mp hdvd'
  have hyne : y ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hy
    exact Units.ne_zero xE hy.symm
  refine ⟨Units.mk0 y hyne, ?_⟩
  rw [Units.val_mk0]
  exact hy


/-! ## Transport of the extension data along a pair of ring isomorphisms

The statement of the target involves three independent universes (`K`, `B`, `E`), while the
cohomological machinery used for the lower bound (`groupCohomology`, `tateCohomology`) is locked
to `Type 0`.  The lemmas below transport the field-theoretic data of an extension of fields
(`IsGalois`, `Module.Finite`, `Algebra.norm`, and the norm quotient `Bˣ ⧸ N(Eˣ)`) along a
compatible pair of ring isomorphisms `eB : B ≃+* B₀`, `eE : E ≃+* E₀` (compatible meaning
`eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)`), so that a `Type 0` statement implies the
general one.  They are the algebraic half of the universe bridge.
-/

theorem isGalois_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) [IsGalois B E] :
    IsGalois B₀ E₀ := by
  have he : RingHom.comp (algebraMap B₀ E₀) (eB : B →+* B₀) =
      RingHom.comp (eE : E →+* E₀) (algebraMap B E) := by ext x; exact (h x).symm
  haveI := Algebra.IsSeparable.of_equiv_equiv eB eE he
  haveI : Normal B₀ E₀ := Normal.of_equiv_equiv (f := eB) (g := eE) he
  exact IsGalois.mk

theorem norm_eq_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (x : E) :
    eB (Algebra.norm B x) = Algebra.norm B₀ (eE x) := by
  have he : RingHom.comp (algebraMap B₀ E₀) (eB : B →+* B₀) =
      RingHom.comp (eE : E →+* E₀) (algebraMap B E) := by ext x; exact (h x).symm
  have hx := Algebra.norm_eq_of_equiv_equiv eB eE he x
  rw [hx, RingEquiv.apply_symm_apply]

theorem moduleFinite_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) [Module.Finite B E] :
    Module.Finite B₀ E₀ := by
  let σ : B →+* B₀ := eB.toRingHom
  let f : E →ₛₗ[σ] E₀ :=
    { toFun := eE
      map_add' := fun x y => eE.map_add x y
      map_smul' := fun b x => by
        show eE (b • x) = eB b • eE x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, h b] }
  exact Module.Finite.of_surjective f eE.surjective

/-- The norm quotient `Bˣ ⧸ N_{E/B}(Eˣ)` is transported along a compatible pair of ring
isomorphisms. -/
theorem natCard_quotient_units_range_norm_eq_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E]
    [Field B₀] [Field E₀] [Algebra B E] [Algebra B₀ E₀]
    (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (B₀ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))) := by
  have hnorm : ∀ u : Eˣ, Units.map eB.toMulEquiv (Units.map (Algebra.norm B : E →* B) u) =
      Units.map (Algebra.norm B₀ : E₀ →* B₀) (Units.map eE.toMulEquiv u) := by
    intro u
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact norm_eq_of_ringEquiv eB eE h (u : E)
  have hmap : Subgroup.map (Units.map eB.toMulEquiv)
        (MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      exact ⟨Units.map eE.toMulEquiv u, (hnorm u).symm⟩
    · rintro ⟨v, rfl⟩
      refine ⟨Units.map (Algebra.norm B : E →* B) (Units.map eE.symm.toMulEquiv v),
        ⟨Units.map eE.symm.toMulEquiv v, rfl⟩, ?_⟩
      rw [hnorm (Units.map eE.symm.toMulEquiv v)]
      congr 1
      ext
      simp
  haveI : (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).Normal :=
    Subgroup.normal_of_isMulCommutative _
  haveI : (MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))).Normal :=
    Subgroup.normal_of_isMulCommutative _
  exact Nat.card_congr (QuotientGroup.congr _ _ (Units.mapEquiv eB.toMulEquiv) hmap).toEquiv

set_option maxHeartbeats 4000000

/-- **The requested lemma** (still conditional on the lower bound, see the module docstring). -/
theorem natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type*} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a)
    {p : ℕ} (hp : IsPGroup p (E ≃ₐ[B] E)) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (E ≃ₐ[B] E) := by
  -- The crux: the norm index theorem for every intermediate field `M` with `M/B` a `p`-group
  -- extension (`p = 0` allowed, in which case it is the full abelian case).
  have hcrux := natCard_quotient_units_range_norm_pgroup_intermediate_field (K := K) Q hcomm
  -- the top field `⊤ ↔ E` transports the `p`-group hypothesis
  have hp_top : IsPGroup p (↥(⊤ : IntermediateField B E) ≃ₐ[B] ↥(⊤ : IntermediateField B E)) :=
    IsPGroup.of_equiv hp
      (AlgEquiv.autCongr (IntermediateField.topEquiv (F := B) (E := E))).symm
  have hkey := hcrux ⊤ p hp_top
  -- transport the norm quotient along `⊤ ≃ₐ[B] E`
  have hcomp : ∀ x : B,
      (IntermediateField.topEquiv (F := B) (E := E)).toRingEquiv
        (algebraMap B ↥(⊤ : IntermediateField B E) x) = algebraMap B E x :=
    fun x => (IntermediateField.topEquiv (F := B) (E := E)).commutes x
  have hq := Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_of_ringEquiv
      (B := B) (E := ↥(⊤ : IntermediateField B E)) (B₀ := B) (E₀ := E)
      (RingEquiv.refl B) (IntermediateField.topEquiv (F := B) (E := E)).toRingEquiv hcomp
  have hcardtop : Nat.card (↥(⊤ : IntermediateField B E) ≃ₐ[B] ↥(⊤ : IntermediateField B E)) =
      Nat.card (E ≃ₐ[B] E) :=
    Nat.card_congr (AlgEquiv.autCongr (IntermediateField.topEquiv (F := B) (E := E))).toEquiv
  rw [← hq, hkey, hcardtop]
end Commons.NumberTheory.NumberField.Completion
