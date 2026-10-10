import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Submission.NK.Reconstruct.fourf5Input
import Submission.NK.Reconstruct.hausRank
import Submission.NK.Reconstruct.lemma4f4_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shimizu's Proposition 4f.5 for arbitrary number fields

Shimizu (arXiv:2009.10431, §4, Proposition 4f.5): for number fields `K₁, K₂`, if one of them has a
complex prime and `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}` for a finite extension `L/K₁K₂` with `L/ℚ` Galois,
then `K₁ = K₂`.

The formalised proof (`Submission/Work/Reconstruct/fourf5Rank.lean`) runs the rank computation of
Shimizu's proof from the two class-field-theory inputs

* `NK.Reconstruct.HausRankInput Ω ℓ` — `r_ℓ(K) = rank_{ℤ_ℓ} Γ_K^{tf}`, and
* `NK.Reconstruct.RankStrictMonoLevelInput ℚ Ω ℓ` — Lemma 4f.2, CoNF (10.3.7),

together with `NK.Reconstruct.ResRankInput Ω ℓ` (the rank computation
`r_ℓ(K₁) ≤ r_ℓ(K₁ ∩ K₂)`).

For the *reconstruction step* the two base fields `K₁`, `K₂` are **arbitrary number fields** inside
the common separable closure `Ω` (the pair `(L₀, levelMap ϕ L₀)` of the level-pair assembly), so the
inputs have to be available in that generality; the version for levels that are Galois over `ℚ` is
the special case `NumFieldIn.ofFrobLevel` of the version given here.  This file states the general
inputs and proves Proposition 4f.5 from them.

## Contents

* `NK.Reconstruct.RankStrictMonoLevelInputGen` — Lemma 4f.2 for arbitrary number fields;
* `NK.Reconstruct.ResRankInputGen` — the rank computation of Prop. 4f.5 for arbitrary number
  fields;
* **`NK.Reconstruct.Fourf5InputGen`** — Proposition 4f.5 for arbitrary number fields;
* `NK.Reconstruct.numberField_complex_of_le` — a complex prime is inherited by finite extensions
  (proved outright, not an input);
* **`NK.Reconstruct.fourf5_gen_of_rankInputs`** — Proposition 4f.5 from the three inputs;
* `NK.Reconstruct.fourf5Input_of_gen`, `NK.Reconstruct.rankStrictMonoLevelInput_of_gen`,
  `NK.Reconstruct.resRankInput_of_gen` — the Galois-over-`ℚ` forms are special cases.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise NumberField

universe u

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-! ## A complex prime is inherited by finite extensions -/

/-- **A complex prime descends to every finite extension**: if a number field `K ⊆ Ω` has a complex
prime, so does every finite extension `E ⊇ K` inside `Ω`.

This is *not* an arithmetic input: an infinite place of `K` is dominated by a place of the finite
(hence algebraic) extension `E` (`NumberField.InfinitePlace.comap_surjective`), and a place above a
complex place is complex (`NumberField.InfinitePlace.IsComplex.of_comap`). -/
theorem numberField_complex_of_le (K E : NumFieldIn ℚ Ω) [IsSepClosure ↥K.L Ω] (h : K.L ≤ E.L)
    (hv : ∃ v : NumberField.InfinitePlace ↥K.L, NumberField.InfinitePlace.IsComplex v) :
    ∃ w : NumberField.InfinitePlace ↥E.L, NumberField.InfinitePlace.IsComplex w := by
  obtain ⟨v, hv⟩ := hv
  haveI : Algebra ↥K.L ↥E.L :=
    ({ toFun := fun x => ⟨x.1, h x.2⟩
       map_one' := Subtype.ext rfl
       map_mul' := fun a b => Subtype.ext rfl
       map_zero' := Subtype.ext rfl
       map_add' := fun a b => Subtype.ext rfl } : ↥K.L →+* ↥E.L).toAlgebra
  haveI : Algebra.IsAlgebraic ↥K.L ↥E.L := Algebra.IsAlgebraic.of_finite ↥K.L ↥E.L
  obtain ⟨w, hw⟩ := NumberField.InfinitePlace.comap_surjective (k := ↥K.L) (K := ↥E.L) v
  have hw' : w.comap (algebraMap ↥K.L ↥E.L) = v := hw
  exact ⟨w, NumberField.InfinitePlace.IsComplex.of_comap (algebraMap ↥K.L ↥E.L) (by
    rw [hw']; exact hv)⟩

/-! ## The two rank inputs, for arbitrary number fields -/

/-- **Shimizu's Lemma 4f.2** (CoNF (10.3.7)) for arbitrary number fields inside `Ω`: for finite
number-field levels `M ⊆ N` of `Ω/ℚ` with `N` having a complex prime, `r_ℓ(M) < r_ℓ(N)`.

The specialisation to levels that are Galois over `ℚ` is `NK.Reconstruct.RankStrictMonoLevelInput`. -/
def RankStrictMonoLevelInputGen (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (M N : NumFieldIn ℚ Ω) [IsSepClosure ↥M.L Ω] [IsSepClosure ↥N.L Ω], M.L ≤ N.L → M.L ≠ N.L →
    (∃ v : NumberField.InfinitePlace ↥N.L, NumberField.InfinitePlace.IsComplex v) →
      rankGamma ↥M.L Ω ℓ < rankGamma ↥N.L Ω ℓ

/-- **The rank computation of Shimizu's proof of Proposition 4f.5**, for arbitrary number fields
inside `Ω`: if `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}` and `M = K₁ ∩ K₂`, then `r_ℓ(K₁) ≤ r_ℓ(M)`.

In Shimizu's proof this is the computation
`im(res^{K₁}) = im(res^{K₂}) = Hom(Γ_L/N, ℤ_ℓ)` (the equality of the images is the common kernel
`N = ker π_{L/K₁} = ker π_{L/K₂}`, `NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq`), which has
rank `r_ℓ(K₁)`, is contained in `Hom(Γ_L,ℤ_ℓ)^{G(L/K₁∩K₂)}` — the images are invariant under both
`G(L/K₁)` and `G(L/K₂)` and `G(L/K₁∩K₂)` is generated by them, `L/ℚ` being Galois — and the
invariants have rank `r_ℓ(K₁ ∩ K₂)` by the "In particular" of Lemma 4f.1, i.e. by
`NK.Reconstruct.lemma4f1_of_transfer_rank` (whose *finite-cokernel* half is the named transfer
input `NK.Reconstruct.TransferInput`, CoNF (1.6.7)).

This is the single place in Proposition 4f.5 where the duality `res = π^*` and the transfer identity
enter.  The version for `FrobLevel`s is `NK.Reconstruct.ResRankInput`. -/
def ResRankInputGen (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K₁ K₂ M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K₁.L Ω]
    [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥M.L Ω],
    M.L = (K₁.L ⊓ K₂.L) → (K₁.L ≤ L.L) → (K₂.L ≤ L.L) →
    (levelInfinityOf K₁ ℓ ⊔ L.L = L.L ⊔ levelInfinityOf K₂ ℓ) →
      rankGamma ↥K₁.L Ω ℓ ≤ rankGamma ↥M.L Ω ℓ

/-- **Shimizu's Proposition 4f.5** (arXiv:2009.10431, §4) for arbitrary number fields inside `Ω`:
for finite number-field levels `K₁, K₂ ⊆ L` of `Ω/ℚ` with `L/ℚ` Galois, if one of the `K_i` has a
complex prime and `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}`, then `K₁ = K₂`.

The version with the `K_i` required to be Galois over `ℚ` is `NK.Reconstruct.Fourf5Input`. -/
def Fourf5InputGen (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω],
    (K₁.L ≤ L.L) → (K₂.L ≤ L.L) →
    (levelInfinityOf K₁ ℓ ⊔ L.L : IntermediateField ℚ Ω)
        = (L.L ⊔ levelInfinityOf K₂ ℓ : IntermediateField ℚ Ω) →
    (∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v) →
      K₁.L = K₂.L

/-! ## Proposition 4f.5 from the inputs -/

/-- **Shimizu's Proposition 4f.5** from the three inputs: the rank identification
`NK.Reconstruct.HausRankInput`, Lemma 4f.2 in the general form
`NK.Reconstruct.RankStrictMonoLevelInputGen`, and the rank computation
`NK.Reconstruct.ResRankInputGen`.

The proof is Shimizu's: with `M := K₁ ∩ K₂`,

1. `r_ℓ(K₁) = r_ℓ(K₂)` — the kernels of `π^{tf}_{L/K₁}` and `π^{tf}_{L/K₂}` agree because
   `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}` (`NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq`), and the rank
   of `Γ_K^{tf}` is the rank of the image of the base change
   (`NK.Reconstruct.rank_hausQuot_eq_rank_range_hausPi`);
2. Lemma 4f.2 applied to `M ⊆ K₁` (which has a complex prime by hypothesis) forces `M = K₁`, i.e.
   `K₁ ⊆ K₂`, using `r_ℓ(K₁) ≤ r_ℓ(M)` from the rank computation;
3. `K₂` has a complex prime by `NK.Reconstruct.numberField_complex_of_le`, and Lemma 4f.2 applied
   to `K₁ ⊆ K₂` contradicts the equality of ranks. -/
theorem fourf5_gen_of_rankInputs (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : HausRankInput Ω ℓ) (hM : RankStrictMonoLevelInputGen Ω ℓ)
    (hR : ResRankInputGen Ω ℓ) : Fourf5InputGen Ω ℓ := by
  intro K₁ K₂ L hsep₁ hsep₂ h₁ h₂ hsup hcomplex
  haveI : IsSepClosure ↥L.L Ω := isSepClosure_of_le L.L
  -- Step 1: the ℓ-ranks of `K₁` and `K₂` agree.
  have hker := ker_hausPi_eq_of_levelInfinity_eq K₁ K₂ L h₁ h₂ ℓ hsup
  have hrank : rankGamma ↥K₁.L Ω ℓ = rankGamma ↥K₂.L Ω ℓ := by
    have hcard : (rankGamma ↥K₁.L Ω ℓ : Cardinal) = (rankGamma ↥K₂.L Ω ℓ : Cardinal) := by
      rw [← hH ↥K₁.L Ω, ← hH ↥K₂.L Ω]
      exact rank_hausQuot_eq_of_ker_eq K₁ K₂ L h₁ h₂ ℓ hker
    exact_mod_cast hcard
  -- the meet `M = K₁ ∩ K₂`
  let M : NumFieldIn ℚ Ω := K₁.inf K₂
  have hMK₁ : M.L ≤ K₁.L := NumFieldIn.inf_le_left K₁ K₂
  have hMK₂ : M.L ≤ K₂.L := NumFieldIn.inf_le_right K₁ K₂
  have hMsup : M.L = (K₁.L ⊓ K₂.L) := NumFieldIn.inf_L K₁ K₂
  haveI : IsSepClosure ↥M.L Ω := isSepClosure_of_le M.L
  -- Step 2: the rank computation `r_ℓ(K₁) ≤ r_ℓ(M)` forces `M = K₁`.
  have hup : rankGamma ↥K₁.L Ω ℓ ≤ rankGamma ↥M.L Ω ℓ := hR K₁ K₂ M L hMsup h₁ h₂ hsup
  have hM₁ : M.L = K₁.L := by
    by_contra hne
    exact absurd hup (not_le.mpr (hM M K₁ hMK₁ hne hcomplex))
  have hle : K₁.L ≤ K₂.L := hM₁ ▸ hMK₂
  -- Step 3: Lemma 4f.2 on `K₁ ⊆ K₂` contradicts the equality of ranks.
  obtain ⟨w, hw⟩ := numberField_complex_of_le K₁ K₂ hle hcomplex
  by_contra hne
  exact (ne_of_lt (hM K₁ K₂ hle hne ⟨w, hw⟩)) hrank

/-! ## The Galois-over-`ℚ` forms are special cases -/

/-- `Fourf5InputGen` implies the Galois-over-`ℚ` form `NK.Reconstruct.Fourf5Input`. -/
theorem fourf5Input_of_gen {ℓ : ℕ} [Fact ℓ.Prime] (h : Fourf5InputGen Ω ℓ) :
    Fourf5Input Ω ℓ := by
  intro K₁ K₂ L h₁ h₂ hsep₁ hsep₂ hsup hcomplex
  exact h (NumFieldIn.ofFrobLevel K₁) (NumFieldIn.ofFrobLevel K₂) L h₁ h₂ hsup hcomplex

/-- `RankStrictMonoLevelInputGen` implies the Galois-over-`ℚ` form
`NK.Reconstruct.RankStrictMonoLevelInput`. -/
theorem rankStrictMonoLevelInput_of_gen {ℓ : ℕ} [Fact ℓ.Prime]
    (h : RankStrictMonoLevelInputGen Ω ℓ) : RankStrictMonoLevelInput ℚ Ω ℓ := by
  intro M N hMN hne hv
  haveI : IsSepClosure ↥M.L Ω := isSepClosure_of_le M.L
  haveI : IsSepClosure ↥N.L Ω := isSepClosure_of_le N.L
  exact h (NumFieldIn.ofFrobLevel M) (NumFieldIn.ofFrobLevel N) hMN hne hv

end NK.Reconstruct
