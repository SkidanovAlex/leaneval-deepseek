import Mathlib
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalCFT.All
import Submission.NK.LocalInputs.Inputs
import Submission.NK.Mine.UnitsAux
import Submission.NK.Mine.index_powSub_units_eq
import Submission.NK.Mine.index_powSub_cpl_eq

namespace NK.Mine

open IsDedekindDomain.HeightOneSpectrum
open scoped Classical
open scoped IsMulCommutative
open NK.LocalInputs.CommGroupRank

set_option maxHeartbeats 4000000

/-- **The residue characteristic is the unique prime `ℓ` for which the profinite completion of
`κˣ` has `(ℤ/ℓ^n)²`-quotients for all `n`.**

For `κ = K_𝔭` a `p`-adic field the profinite completion of `κˣ` is `Ẑ × μ(κ) × ℤ_p^{[κ:ℚ_p]}`;
its pro-`ℓ` completion has rank `≥ 2` exactly for `ℓ = p`. -/
theorem hasZl2Quotient_completionUnits_iff {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p ℓ : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p) :
    NK.LocalTame.HasZl2Quotient ℓ
        (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K)) ↔ ℓ = p := by
  constructor
  · -- only the residue characteristic survives
    intro h
    by_contra hne
    set q : ℕ := Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) with hqdef
    haveI hfin : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
      Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
    haveI hne' : Nonempty (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := ⟨0⟩
    haveI hft : Fintype (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := Fintype.ofFinite _
    have hq2 : 2 ≤ q := by
      rw [hqdef, Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hq1 : 0 < q - 1 := by omega
    -- an exponent `n` with `q - 1 < ℓ ^ n`
    obtain ⟨n, hnpos, hnbig⟩ : ∃ n : ℕ, 0 < n ∧ q - 1 < ℓ ^ n := by
      refine ⟨q, by omega, ?_⟩
      calc q - 1 < q := by omega
        _ < 2 ^ q := Nat.lt_two_pow_self
        _ ≤ ℓ ^ q := Nat.pow_le_pow_left (Nat.Prime.two_le hℓ) q
    -- the `ℓ ^ n`-th power subgroups of `κˣ` and of its profinite completion
    set SA : Subgroup (𝔭.adicCompletion K)ˣ :=
      Subgroup.closure (Set.range fun y : (𝔭.adicCompletion K)ˣ => y ^ (ℓ ^ n)) with hSA
    set S : Subgroup (cpl ((𝔭.adicCompletion K)ˣ)) :=
      Subgroup.closure (Set.range fun y : cpl ((𝔭.adicCompletion K)ˣ) => y ^ (ℓ ^ n)) with hS
    have hidx : SA.index = ℓ ^ n * (ℓ ^ n).gcd (q - 1) := by
      rw [hSA, hqdef]
      exact index_powSub_units_eq 𝔭 hp hℓ hne hchar n
    haveI hfinA : Finite ((𝔭.adicCompletion K)ˣ ⧸ SA) :=
      Nat.finite_of_card_ne_zero (by
        rw [← Subgroup.index_eq_card, hidx]
        exact Nat.mul_ne_zero (pow_ne_zero n hℓ.ne_zero) (Nat.gcd_ne_zero_right hq1.ne'))
    have hcpl : S.index = SA.index := by
      rw [hS, hSA]
      exact index_powSub_cpl_eq ((𝔭.adicCompletion K)ˣ) (pow_pos hℓ.pos n)
    haveI hfinS : Finite (cpl ((𝔭.adicCompletion K)ˣ) ⧸ S) :=
      Nat.finite_of_card_ne_zero (by
        rw [← Subgroup.index_eq_card, hcpl, hidx]
        exact Nat.mul_ne_zero (pow_ne_zero n hℓ.ne_zero) (Nat.gcd_ne_zero_right hq1.ne'))
    -- `HasZl2Quotient` forces the index of `S` to be large
    have h' : NK.LocalTame.HasZl2Quotient ℓ (cpl ((𝔭.adicCompletion K)ˣ)) := h
    have hbound : ℓ ^ (2 * n) ≤ S.index := by
      obtain ⟨f, hf⟩ := h' n hnpos
      have hz : ∀ z : Multiplicative (ZMod (ℓ ^ n)), z ^ (ℓ ^ n) = 1 := fun z => by
        rw [← ofAdd_toAdd z, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
          ofAdd_zero]
      have hker : S ≤ f.ker := by
        rw [hS, Subgroup.closure_le]
        rintro x ⟨y, rfl⟩
        show f (y ^ (ℓ ^ n)) = 1
        rw [map_pow]
        exact Prod.ext (by simpa using hz (f y).1) (by simpa using hz (f y).2)
      let g : cpl ((𝔭.adicCompletion K)ˣ) ⧸ S →*
          (Multiplicative (ZMod (ℓ ^ n)) × Multiplicative (ZMod (ℓ ^ n))) :=
        QuotientGroup.lift S f hker
      have hg : Function.Surjective g := by
        intro y
        obtain ⟨x, hx⟩ := hf y
        exact ⟨QuotientGroup.mk' S x, by
          rw [show g (QuotientGroup.mk' S x) = f x from QuotientGroup.lift_mk' (φ := f) S hker x, hx]⟩
      have hmain := Nat.card_le_card_of_surjective g hg
      have hcard : Nat.card (Multiplicative (ZMod (ℓ ^ n)) × Multiplicative (ZMod (ℓ ^ n)))
          = ℓ ^ (2 * n) := by
        haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ.ne_zero⟩
        rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd (α := ZMod (ℓ ^ n))),
          Nat.card_eq_fintype_card, ZMod.card, ← pow_add, two_mul]
      rw [hcard] at hmain
      rwa [← Subgroup.index_eq_card] at hmain
    have hlow2 : ℓ ^ (2 * n) ≤ ℓ ^ n * (ℓ ^ n).gcd (q - 1) :=
      hbound.trans (le_of_eq (hcpl.trans hidx))
    -- but the index is small
    have hsmall : ℓ ^ n * (ℓ ^ n).gcd (q - 1) < ℓ ^ (2 * n) := by
      have h1 : (ℓ ^ n).gcd (q - 1) < ℓ ^ n :=
        lt_of_le_of_lt (Nat.gcd_le_right _ hq1) hnbig
      have h2 : ℓ ^ n * (ℓ ^ n).gcd (q - 1) < ℓ ^ n * ℓ ^ n :=
        Nat.mul_lt_mul_of_pos_left h1 (pow_pos hℓ.pos n)
      have h3 : ℓ ^ n * ℓ ^ n = ℓ ^ (2 * n) := by
        rw [← pow_add]; ring_nf
      rwa [h3] at h2
    omega
  · -- `ℓ = p`: the units of `κ` have `(ℤ/p^n)²`-quotients for all `n`
    rintro rfl
    intro n _hn
    exact exists_surjective_completionUnits 𝔭 hp hchar n

end NK.Mine
