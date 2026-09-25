import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs

set_option linter.style.haveILetI false

namespace Work.Tower.CyclotomicBase

/-- **Chinese remainder theorem for the unit groups of `ZMod`.**

Let `r : Fin ℓ → ℕ` be a family of pairwise distinct primes and `D r = ∏ᵢ rᵢ`. Then the
coordinate maps `(ℤ/D)ˣ → (ℤ/rᵢ)ˣ` are jointly surjective: any family of units `uᵢ ∈ (ℤ/rᵢ)ˣ`
is the image of a single unit of `ℤ/D`.

The proof picks, for each `i`, a natural number `xᵢ` which is `1` modulo `D/rᵢ` and congruent to
a representative of `uᵢ` modulo `rᵢ` (Chinese remainder theorem for `ℕ`); the product `∏ᵢ xᵢ` is
then congruent to `uᵢ` modulo `rᵢ` and coprime to every `rᵢ`, hence to `D`, so it defines a unit
of `ℤ/D` with the required images. -/
theorem exists_unitsMap_eq {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hrinj : Function.Injective r) (u : ∀ i, (ZMod (r i))ˣ) :
    ∃ v : (ZMod (D r))ˣ, ∀ i, ZMod.unitsMap (r_dvd_D r i) v = u i := by
  classical
  -- `r i` divides `D r / r j` whenever `i ≠ j` (the primes are pairwise distinct).
  have hrdiv : ∀ {i j : Fin ℓ}, i ≠ j → r i ∣ D r / r j := by
    intro i j hij
    have hcop : (r i).Coprime (r j) :=
      (Nat.coprime_primes (hr i) (hr j)).mpr fun h => hij (hrinj h)
    have hdvd : r i ∣ D r := r_dvd_D r i
    rw [← Nat.div_mul_cancel (r_dvd_D r j)] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  -- `D r / r i` is the product of the remaining primes, hence coprime to `r i`.
  have hcopQr : ∀ i, (D r / r i).Coprime (r i) := by
    intro i
    have hprod : r i * ∏ j ∈ Finset.univ.erase i, r j = D r :=
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)
    have hdiv : D r / r i = ∏ j ∈ Finset.univ.erase i, r j := by
      rw [← hprod]
      exact Nat.mul_div_cancel_left _ (hr i).pos
    rw [hdiv]
    exact Nat.Coprime.prod_left fun j hj =>
      (Nat.coprime_primes (hr j) (hr i)).mpr fun h => (Finset.mem_erase.mp hj).1 (hrinj h)
  -- For each `i`, CRT produces `x i` which is `1` mod `D r / r i` and `(u i).val` mod `r i`.
  have hex : ∀ i, ∃ x : ℕ, x ≡ 1 [MOD D r / r i] ∧ x ≡ (u i : ZMod (r i)).val [MOD r i] := by
    intro i
    obtain ⟨x, hx1, hx2⟩ := Nat.chineseRemainder (hcopQr i) 1 (u i : ZMod (r i)).val
    exact ⟨x, hx1, hx2⟩
  choose x hx1 hx2 using hex
  -- The product `∏ j, x j` is congruent to `(u i).val` modulo each `r i`.
  have hmod : ∀ i, (∏ j, x j) ≡ (u i : ZMod (r i)).val [MOD r i] := by
    intro i
    have hrest : (∏ j ∈ Finset.univ.erase i, x j) ≡ 1 [MOD r i] := by
      refine Finset.prod_induction x (fun a => a ≡ 1 [MOD r i]) ?_ (Nat.ModEq.refl 1) ?_
      · intro a b ha hb
        simpa using ha.mul hb
      · intro j hj
        exact (hx1 j).of_dvd (hrdiv ((Finset.mem_erase.mp hj).1).symm)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    calc x i * ∏ j ∈ Finset.univ.erase i, x j
        ≡ (u i : ZMod (r i)).val * 1 [MOD r i] := (hx2 i).mul hrest
      _ = (u i : ZMod (r i)).val := mul_one _
  -- Hence the product is a unit of `ℤ/D`.
  have hcopX : (∏ j, x j).Coprime (D r) := by
    rw [D_def, Nat.coprime_prod_right_iff]
    intro i _
    rw [Nat.coprime_iff_gcd_eq_one, (hmod i).gcd_eq, ← Nat.coprime_iff_gcd_eq_one]
    exact ZMod.val_coe_unit_coprime (u i)
  -- The corresponding unit of `ZMod (D r)` has the required images.
  refine ⟨ZMod.unitOfCoprime (∏ j, x j) hcopX, fun i => ?_⟩
  haveI : NeZero (r i) := ⟨(hr i).ne_zero⟩
  apply Units.ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (r_dvd_D r i),
    ← ZMod.natCast_zmod_val (u i : ZMod (r i)), ZMod.natCast_eq_natCast_iff]
  exact hmod i

end Work.Tower.CyclotomicBase
