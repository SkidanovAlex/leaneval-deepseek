import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.Lfield_cubic
import Submission.Work.Tower.CyclotomicBase.disc_Lfield
import Submission.Work.Tower.CyclotomicBase.discr_compositum

/-!
# The discriminant of the partial compositum `Mof s`

For pairwise distinct primes `rᵢ ≡ 1 (mod 3)` and a finite set `s` of indices, the compositum
`Mof r hr hr3 s = ∏_{i ∈ s} Lᵢ` of the cubic fields `Lᵢ` cut out by the characters `χᵢ` has
degree `3 ^ |s|` over `ℚ` and discriminant of absolute value
`(∏_{i ∈ s} rᵢ ^ 2) ^ (3 ^ (|s| - 1))`.

The `Lᵢ` have pairwise coprime discriminants (`disc_Lfield`), so `Mof r hr hr3 s` and `Lᵢ` are
linearly disjoint for `i ∉ s` (`NumberField.linearDisjoint_of_isGalois_isCoprime_discr`); this
gives both the degree (`IntermediateField.LinearDisjoint.finrank_sup`) and, via the general
compositum formula `discr_compositum`, the discriminant, by induction on `s`.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

open NumberField

namespace Work.Tower.CyclotomicBase

theorem Mof_disc {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] (s : Finset (Fin ℓ)) :
    Module.finrank ℚ ↥(Mof r hr hr3 s) = 3 ^ s.card ∧
    |NumberField.discr ↥(Mof r hr hr3 s)| =
      (((∏ i ∈ s, (r i) ^ 2 : ℕ)) : ℤ) ^ (3 ^ (s.card - 1)) := by
  induction s using Finset.induction with
  | empty =>
    rw [Mof_empty]
    constructor
    · simp
    · have hb : NumberField.discr ↥(⊥ : IntermediateField ℚ (Cyc r)) = 1 := by
        rw [NumberField.discr_eq_discr_of_algEquiv ↥(⊥ : IntermediateField ℚ (Cyc r))
          (IntermediateField.botEquiv ℚ (Cyc r)), NumberField.discr_rat]
      rw [hb]
      simp
  | insert i t ht ih =>
    obtain ⟨IHrank, IHdisc⟩ := ih
    -- the two fields of the induction step
    have hrank₂ : Module.finrank ℚ ↥(Lfield r hr hr3 i) = 3 := (Lfield_cubic r hr hr3 i).1
    haveI hG₁ : IsGalois ℚ ↥(Mof r hr hr3 t) := isGalois_Mof r hr hr3 t
    -- the two discriminants, as natural numbers
    have hMnat : (NumberField.discr ↥(Mof r hr hr3 t)).natAbs =
        (∏ j ∈ t, (r j) ^ 2) ^ (3 ^ (t.card - 1)) := by
      rw [← Int.natAbs_abs, IHdisc, Int.natAbs_pow, Int.natAbs_natCast]
    have hLnat : (NumberField.discr ↥(Lfield r hr hr3 i)).natAbs = (r i) ^ 2 := by
      rw [← Int.natAbs_abs, disc_Lfield r hr hr3 i, Int.natAbs_pow, Int.natAbs_natCast]
    -- the discriminants are coprime, because `i ∉ t` and `r` is injective
    have hcop_nat : Nat.Coprime (NumberField.discr ↥(Mof r hr hr3 t)).natAbs
        (NumberField.discr ↥(Lfield r hr hr3 i)).natAbs := by
      rw [hMnat, hLnat]
      exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_right 2
        (Nat.Coprime.prod_left fun j hj => Nat.Coprime.pow_left 2
          ((Nat.coprime_primes (hr j) (hr i)).mpr fun h => ht (hrinj h ▸ hj))))
    have hcop : IsCoprime (NumberField.discr ↥(Mof r hr hr3 t))
        (NumberField.discr ↥(Lfield r hr hr3 i)) :=
      Int.isCoprime_iff_nat_coprime.mpr hcop_nat
    have hdisj : (Mof r hr hr3 t).LinearDisjoint (Lfield r hr hr3 i) :=
      NumberField.linearDisjoint_of_isGalois_isCoprime_discr (Cyc r) _ _ hcop
    -- the exponent identity behind the discriminant formula
    have hkey : (∏ j ∈ t, (r j) ^ 2) ^ (3 ^ (t.card - 1) * 3)
        = (∏ j ∈ t, (r j) ^ 2) ^ (3 ^ t.card) := by
      rcases Nat.eq_zero_or_pos t.card with h0 | hpos
      · simp [Finset.card_eq_zero.mp h0]
      · rw [← pow_succ, Nat.sub_add_cancel hpos]
    refine ⟨?_, ?_⟩
    · rw [Mof_insert r hr hr3 i t, hdisj.finrank_sup, IHrank, hrank₂,
        Finset.card_insert_of_notMem ht, pow_succ]
    · have hgoal_nat : (NumberField.discr ↥(Mof r hr hr3 (insert i t))).natAbs =
          (∏ j ∈ insert i t, (r j) ^ 2) ^ (3 ^ ((insert i t).card - 1)) := by
        rw [Mof_insert r hr hr3 i t,
          discr_compositum (Cyc r) (Mof r hr hr3 t) (Lfield r hr hr3 i) hcop,
          hrank₂, IHrank, hMnat, hLnat, ← pow_mul,
          Finset.prod_insert ht, Finset.card_insert_of_notMem ht, Nat.add_sub_cancel,
          mul_pow, hkey, mul_comm]
      rw [← Int.natCast_natAbs, hgoal_nat, Nat.cast_pow]

end Work.Tower.CyclotomicBase
