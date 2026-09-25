import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.vClass_eq_one_iff
import Submission.Work.QuadraticFields.RankTwo
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Invariants
import Submission.Work.ClassFieldTower.classGroupTwoRank_eq_finrank_modN
import Submission.Work.ClassFieldTower.unitTwoRank_eq_finrank_units_modSquares

/-!
# `Work.ShafarevichKoch.vTwo_rank_two` is FALSE

The requested lemma

```
Work.QuadraticFields.rankTwo (VTwo F) = unitTwoRank F + classGroupTwoRank F
```

is **false**, and this file machine-checks a counterexample for `F = ℚ`, where the left-hand
side is `0` and the right-hand side is `1`.

## Diagnosis

`Work.QuadraticFields.rankTwo A` is (`RankTwo.lean`) the `𝔽₂`-dimension of `A ⧸ A²`; applied to
the subgroup `VTwo F ≤ Fˣ` it computes

`dim_{𝔽₂} (V_∅ / V_∅²)`,  `V_∅ = {x ∈ Fˣ : (x) is a square fractional ideal}`.

The arithmetic invariant of Koch/Hajir–Maire–Ramakrishna is instead

`d(V_∅/(Fˣ)²) = dim_{𝔽₂} (V_∅ / (Fˣ)²)`

(the quotient by the *full* group of squares of `Fˣ`, not by `V_∅²`; see Hajir--Maire--Ramakrishna,
*Deficiency of p-class tower groups and Minkowski units*, arXiv:2103.09508, exact sequence
`0 → O_Fˣ/O_F^{×2} → V_∅/(Fˣ)² → Cl_F[2] → 0` and the resulting
`d(V_∅/(Fˣ)²) = d(O_Fˣ) + d(Cl_F)`).  The two quotients differ: `Fˣ² ≤ V_∅`, so

* `(Fˣ)²/V_∅² ↪ V_∅/V_∅²` via `x² V_∅² ↦ x V_∅`, and this map is an isomorphism onto its image
  exactly when `V_∅ ⊇ ±(Fˣ)²`; the quotient `(Fˣ)/V_∅` is **infinite** for every number field
  (it surjects onto `Fˣ/±(Fˣ)²`, which contains the square classes of the primes, infinitely
  many independent ones).

Consequently `V_∅/V_∅²` is an infinite `𝔽₂`-vector space, so Mathlib's
`Module.finrank` (which is `0` on infinite-dimensional spaces) returns `0`, while the right-hand
side `unitTwoRank F + classGroupTwoRank F = (r₁+r₂) + rank₂ Cl_F ≥ 1` is always positive.
This is why the equation fails for *every* number field; `F = ℚ` is the cheapest witness.

## The correct statement

The F₂-dimension of the Kummer radical `V_∅/(Fˣ)²` is what `card_unramifiedQuadraticLevels_le`
actually needs, and it is a true theorem (it is the exact sequence displayed above).  In Lean it
reads, with `Work.QuadraticFields.squareSubgroup (Fˣ).subgroupOf (VTwo F)` the image of the squares
of `Fˣ` in `V_∅`:

```
Work.QuadraticFields.rankTwo (↥(VTwo F) ⧸ (Work.QuadraticFields.squareSubgroup Fˣ).subgroupOf (VTwo F))
  = Work.ClassFieldTower.unitTwoRank F + Work.ClassFieldTower.classGroupTwoRank F
```

## Contents of this file

* `subsingleton_classGroup_rat`: `Cl(𝓞 ℚ)` is trivial (`𝓞 ℚ ≅ ℤ` is a PID).
* `unitEmbed_rat_eq_one_or_neg_one`: a unit of `𝓞 ℚ` is `±1`.
* `VTwo_rat_eq_or_neg_sq`: for `F = ℚ`, `V_∅ = {±x²}` -- the Kummer radical is as small as the
  triviality of the class group allows.
* `primeClass_injective`: the classes of `p²`, `p` prime, are pairwise distinct in
  `V_∅/V_∅²` (two distinct primes are separated by the `p`-adic valuation).
* `infinite_modN_VTwo_rat`: hence `ModN (Additive V_∅) 2 ≅ V_∅/V_∅²` is infinite.
* `finrank_eq_zero_of_infinite_module`: an infinite `𝔽₂`-vector space has `finrank` zero.
* ★ `vTwo_rank_two_rat_false`: `rankTwo (VTwo ℚ) ≠ unitTwoRank ℚ + classGroupTwoRank ℚ`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField
open Work.QuadraticFields

noncomputable section

namespace Work.ShafarevichKoch

/-! ## 1. The arithmetic input for `F = ℚ`: `Cl(𝓞 ℚ) = 1` and `(𝓞 ℚ)ˣ = {±1}` -/

/-- **The class group of `𝓞 ℚ` is trivial.**  `𝓞 ℚ` is `ℤ` up to the ring isomorphism
`IsIntegralClosure.equiv`, and `Cl ℤ = 1` because `ℤ` is a GCD domain. -/
lemma subsingleton_classGroup_rat : Subsingleton (ClassGroup (NumberField.RingOfIntegers ℚ)) :=
  Equiv.subsingleton
    (ClassGroup.mulEquiv (IsIntegralClosure.equiv ℤ ℤ ℚ (𝓞 ℚ)).toRingEquiv).symm.toEquiv

/-- **A unit of `𝓞 ℚ` is `±1`**: transported along `ℤ ≃+* 𝓞 ℚ` it is a unit of `ℤ`, hence `±1`,
and the structure map `𝓞 ℚ → ℚ` carries `±1` to `±1`. -/
lemma unitEmbed_rat_eq_one_or_neg_one (u : (NumberField.RingOfIntegers ℚ)ˣ) :
    unitEmbed ℚ u = 1 ∨ unitEmbed ℚ u = -1 := by
  set e : ℤ ≃+* NumberField.RingOfIntegers ℚ :=
    (IsIntegralClosure.equiv ℤ ℤ ℚ (NumberField.RingOfIntegers ℚ)).toRingEquiv with he
  set v : ℤˣ := (Units.mapEquiv e.toMulEquiv).symm u with hv
  have hvu : u = Units.mapEquiv e.toMulEquiv v :=
    ((Units.mapEquiv e.toMulEquiv).apply_symm_apply u).symm
  have hval : (u : NumberField.RingOfIntegers ℚ) = e (v : ℤ) := by
    rw [hvu, Units.coe_mapEquiv]; rfl
  have hAlg : ∀ a : ℤ, e a = algebraMap ℤ (NumberField.RingOfIntegers ℚ) a := by
    intro a
    simpa using
      AlgEquiv.commutes (IsIntegralClosure.equiv ℤ ℤ ℚ (NumberField.RingOfIntegers ℚ)) a
  have hmain : ((unitEmbed ℚ u : ℚˣ) : ℚ) = (v : ℚ) := by
    rw [show ((unitEmbed ℚ u : ℚˣ) : ℚ)
        = algebraMap (NumberField.RingOfIntegers ℚ) ℚ (u : NumberField.RingOfIntegers ℚ)
          from rfl, hval, hAlg]
    simp
  rcases Int.units_eq_one_or v with h | h
  · left
    refine Units.ext ?_
    show ((unitEmbed ℚ u : ℚˣ) : ℚ) = ((1 : ℚˣ) : ℚ)
    rw [hmain, h]; norm_num
  · right
    refine Units.ext ?_
    show ((unitEmbed ℚ u : ℚˣ) : ℚ) = ((-1 : ℚˣ) : ℚ)
    rw [hmain, h]; norm_num

/-- **The Kummer radical of `ℚ` is the set of `±` squares.**  Since `Cl(𝓞 ℚ) = 1`, the Kummer
two-descent `vClass` is trivial, so `vClass_eq_one_iff` describes `V_∅`: every `x` whose principal
ideal is a square is a unit times a square, and units are `±1`. -/
lemma VTwo_rat_eq_or_neg_sq (x : ℚˣ) (hx : x ∈ VTwo ℚ) :
    ∃ y : ℚˣ, x = y ^ 2 ∨ x = -(y ^ 2) := by
  haveI : Subsingleton (ClassGroup (𝓞 ℚ)) := subsingleton_classGroup_rat
  obtain ⟨u, y, hy⟩ := (vClass_eq_one_iff ℚ ⟨x, hx⟩).mp (Subsingleton.elim _ _)
  rcases unitEmbed_rat_eq_one_or_neg_one u with h | h
  · exact ⟨y, Or.inl (by rw [show x = unitEmbed ℚ u * y ^ 2 from hy, h, one_mul])⟩
  · exact ⟨y, Or.inr (by rw [show x = unitEmbed ℚ u * y ^ 2 from hy, h, neg_one_mul])⟩

/-! ## 2. Squares lie in `V_∅`, and the classes of `p²` in `V_∅/V_∅²` are distinct -/

/-- **Every square lies in `V_∅`**: `(y²) = (y)²` is a square fractional ideal. -/
lemma sq_mem_VTwo (F : Type*) [Field F] [NumberField F] (y : Fˣ) : y ^ 2 ∈ VTwo F := by
  refine ⟨FracIdealOf F y, ?_⟩
  rw [pow_two, FracIdealOf_mul]

/-- A (nonzero) natural number `p`, regarded as an element of `ℚˣ`. -/
noncomputable def primeUnit (p : ℕ) (hp : p.Prime) : ℚˣ :=
  Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)

/-- The element `p² ∈ V_∅` attached to a prime `p`. -/
noncomputable def primeClass (p : ℕ) (hp : p.Prime) : ↥(VTwo ℚ) :=
  ⟨primeUnit p hp ^ 2, sq_mem_VTwo ℚ _⟩

/-- **The classes of `p²`, `p` prime, are pairwise distinct in `V_∅/V_∅²`.**

If `p² ≡ q²` modulo `V_∅²`, then `(p/q)² = v²` for some `v ∈ V_∅`; by
`VTwo_rat_eq_or_neg_sq` we have `v = ±y²`, so `(p/q)² = y⁴` and hence
`q/p = ±y²`.  Therefore `padicValRat p (q/p)` is both `-1` (a direct computation) and even
(it agrees with `padicValRat p (±y²)`), a contradiction.  Hence `p = q`. -/
lemma primeClass_injective :
    Function.Injective (fun s : {p : ℕ // p.Prime} =>
      (QuotientGroup.mk (primeClass s.1 s.2) : ↥(VTwo ℚ) ⧸ squareSubgroup ↥(VTwo ℚ))) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ heq
  have hmem : (primeClass p hp)⁻¹ * primeClass q hq ∈ squareSubgroup ↥(VTwo ℚ) :=
    QuotientGroup.eq.mp heq
  obtain ⟨v, hv⟩ : ∃ v : ↥(VTwo ℚ), v ^ 2 = (primeClass p hp)⁻¹ * primeClass q hq := by
    have h := hmem
    simp only [squareSubgroup] at h
    rw [Work.ClassFieldTower.sqSubgroup_eq_range] at h
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp h
    rw [powMonoidHom_apply] at hv
    exact ⟨v, hv⟩
  -- the relation, pushed down to `ℚ`: `((v : ℚˣ) : ℚ)² = ((q : ℚ) * (p : ℚ)⁻¹)²`
  have hvQ : ((v : ℚˣ) : ℚ) ^ 2 = ((q : ℚ) * (p : ℚ)⁻¹) ^ 2 := by
    have h := congrArg (fun w : ↥(VTwo ℚ) => ((w : ℚˣ) : ℚ)) hv
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, primeClass, primeUnit,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_mk0] at h
    rw [h]; ring_nf
  by_contra hne
  have hpq_ne : p ≠ q := fun h => hne (Subtype.ext h)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  -- the `p`-adic valuation of `q/p` is `-1`, hence odd
  have hxval : padicValRat p ((q : ℚ) * (p : ℚ)⁻¹) = -1 := by
    rw [padicValRat.mul hq0 (inv_ne_zero hp0), padicValRat.inv, padicValRat.of_nat,
      padicValRat.self hp.one_lt, padicValNat_primes hpq_ne]
    norm_num
  -- but it also agrees with the valuation of `v = ±y²`, which is even
  have haeven : Even (padicValRat p ((v : ℚˣ) : ℚ)) := by
    obtain ⟨y, hy | hy⟩ := VTwo_rat_eq_or_neg_sq (v : ℚˣ) v.2
    · have hy' : ((v : ℚˣ) : ℚ) = ((y : ℚˣ) : ℚ) ^ 2 := by
        have := congrArg (fun u : ℚˣ => (u : ℚ)) hy
        simpa using this
      rw [hy', padicValRat.pow]
      exact even_two_mul _
    · have hy' : ((v : ℚˣ) : ℚ) = -(((y : ℚˣ) : ℚ) ^ 2) := by
        have := congrArg (fun u : ℚˣ => (u : ℚ)) hy
        simpa using this
      rw [hy', padicValRat.neg, padicValRat.pow]
      exact even_two_mul _
  have hcancel : padicValRat p ((q : ℚ) * (p : ℚ)⁻¹) = padicValRat p ((v : ℚˣ) : ℚ) := by
    have h2 : padicValRat p (((q : ℚ) * (p : ℚ)⁻¹) ^ 2)
        = padicValRat p (((v : ℚˣ) : ℚ) ^ 2) := by rw [hvQ]
    rw [padicValRat.pow, padicValRat.pow] at h2
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2
  have : Even (-1 : ℤ) := by
    rw [← hxval, hcancel]
    exact haeven
  norm_num at this

/-! ## 3. `V_∅/V_∅²` is infinite, and an infinite `𝔽₂`-vector space has `finrank` zero -/

/-- **`V_∅/V_∅²` is infinite** for `F = ℚ`: the (infinitely many) classes of `p²` are distinct. -/
lemma infinite_quotient_VTwo_rat : Infinite (↥(VTwo ℚ) ⧸ squareSubgroup ↥(VTwo ℚ)) := by
  haveI : Infinite {p : ℕ // p.Prime} := (Nat.infinite_setOfPred_prime).to_subtype
  exact Infinite.of_injective _ primeClass_injective

/-- **`ModN (Additive V_∅) 2 ≅ V_∅/V_∅²` is infinite** (transported along
`natCard_modN_two_eq_natCard_sqQuotient`). -/
lemma infinite_modN_VTwo_rat : Infinite (ModN (Additive ↥(VTwo ℚ)) 2) := by
  haveI : Infinite (↥(VTwo ℚ) ⧸ squareSubgroup ↥(VTwo ℚ)) := infinite_quotient_VTwo_rat
  have h : Nat.card (ModN (Additive ↥(VTwo ℚ)) 2) = 0 := by
    rw [Work.ClassFieldTower.natCard_modN_two_eq_natCard_sqQuotient]
    exact Nat.card_eq_zero.mpr
      (Or.inr (show Infinite (↥(VTwo ℚ) ⧸ Subgroup.closure (Set.range fun x => x ^ 2))
        from infinite_quotient_VTwo_rat))
  rcases Nat.card_eq_zero.mp h with hemp | hinf
  · exact (hemp.false (ModN.mkQ 2 0)).elim
  · exact hinf

/-- **An infinite module over a finite field has `finrank` zero**: `finrank` is
`Cardinal.toNat` of the rank, and a finite `finrank` would make the module finite. -/
lemma finrank_eq_zero_of_infinite_module {K M : Type*} [Field K] [Finite K]
    [AddCommGroup M] [Module K M] (h : Infinite M) : Module.finrank K M = 0 := by
  by_contra hne
  have hpos : 0 < Module.finrank K M := Nat.pos_of_ne_zero hne
  haveI : Module.Finite K M := Module.finite_of_finrank_pos hpos
  exact h.not_finite (Module.finite_of_finite K)

/-! ## 4. The counterexample -/

/-- `classGroupTwoRank ℚ = 0`: the class group of `ℚ` is trivial. -/
lemma classGroupTwoRank_rat : Work.ClassFieldTower.classGroupTwoRank ℚ = 0 := by
  rw [Work.ClassFieldTower.classGroupTwoRank_eq_finrank_modN ℚ]
  haveI : Subsingleton (ClassGroup (𝓞 ℚ)) := subsingleton_classGroup_rat
  haveI : Subsingleton (ModN (Additive (ClassGroup (𝓞 ℚ))) 2) := inferInstance
  exact Module.finrank_zero_of_subsingleton

/-- **The requested identity fails at `F = ℚ`**: the left-hand side is `0` (the `𝔽₂`-vector space
`V_∅/V_∅²` is infinite, so its `finrank` is `0`), while the right-hand side is
`unitTwoRank ℚ + classGroupTwoRank ℚ = 1 + 0 = 1`. -/
theorem vTwo_rank_two_rat_false :
    Work.QuadraticFields.rankTwo (VTwo ℚ) ≠
      Work.ClassFieldTower.unitTwoRank ℚ + Work.ClassFieldTower.classGroupTwoRank ℚ := by
  have hL : Work.QuadraticFields.rankTwo (VTwo ℚ) = 0 := by
    unfold Work.QuadraticFields.rankTwo
    exact finrank_eq_zero_of_infinite_module infinite_modN_VTwo_rat
  have hU : Work.ClassFieldTower.unitTwoRank ℚ = 1 := Work.ClassFieldTower.unitTwoRank_rat
  have hC : Work.ClassFieldTower.classGroupTwoRank ℚ = 0 := classGroupTwoRank_rat
  rw [hL, hU, hC]
  norm_num

end Work.ShafarevichKoch
