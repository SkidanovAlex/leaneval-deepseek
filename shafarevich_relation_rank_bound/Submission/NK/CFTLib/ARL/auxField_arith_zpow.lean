import Mathlib
import Submission.NK.CFTLib.ARL.auxField_arith

/-!
# The arithmetic of the auxiliary modulus, integer exponents

`NK.CFTLib.ARL.auxField_arith` produces a modulus `M`, a prime `ℓ` and the avoidance
conditions, together with the *additive* (i.e. `ℕ`-exponent) orthogonality statement

  `ℓ ^ u · aᵢ ^ v = 1` in `ZMod M`  ⟹  `n ∣ u` and `n ∣ v`.

For the auxiliary-field construction one needs the same statement for the classes in the unit
group `(ZMod M)ˣ` and for **integer** exponents:

  `ℓu ^ j · (au i) ^ k = 1` in `(ZMod M)ˣ`  ⟹  `n ∣ j` and `n ∣ k`  (`j k : ℤ`).

The integer-exponent form is deduced from the `ℕ`-exponent form by reducing the exponents modulo
the order of the group `(ZMod M)ˣ`: `g ^ j = g ^ (j % card G)`, and `n` divides `card G` because
`g ^ card G = 1`.
-/

set_option autoImplicit false

namespace NK.CFTLib.ARL

/-- **Integer exponents from natural exponents.**  Let `g h` be elements of a finite group and
suppose that every relation `g ^ u * h ^ v = 1` with *natural* exponents forces `n ∣ u` and
`n ∣ v`.  Then the same holds for integer exponents.  (Reduce the exponents modulo
`Fintype.card G`; note `n ∣ Fintype.card G`.) -/
theorem dvd_of_zpow_mul_eq_one {G : Type*} [Group G] [Fintype G] {g h : G} {n : ℕ}
    (hmain : ∀ u v : ℕ, g ^ u * h ^ v = 1 → n ∣ u ∧ n ∣ v) {j k : ℤ}
    (hjk : g ^ j * h ^ k = 1) : (n : ℤ) ∣ j := by
  classical
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
  have hgN : g ^ Fintype.card G = 1 := pow_card_eq_one
  have hhN : h ^ Fintype.card G = 1 := pow_card_eq_one
  have hndvdN : n ∣ Fintype.card G :=
    (hmain (Fintype.card G) 0 (by rw [pow_zero, mul_one, hgN])).1
  have hz : (n : ℤ) ∣ ((Fintype.card G : ℕ) : ℤ) := by exact_mod_cast hndvdN
  have hCne : (Fintype.card G : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
  set j' : ℤ := j % (Fintype.card G : ℤ) with hj'def
  set k' : ℤ := k % (Fintype.card G : ℤ) with hk'def
  have hj'nn : 0 ≤ j' := by rw [hj'def]; exact Int.emod_nonneg j hCne
  have hk'nn : 0 ≤ k' := by rw [hk'def]; exact Int.emod_nonneg k hCne
  have hgj : g ^ j = g ^ j' := by rw [hj'def]; exact zpow_eq_zpow_emod' j hgN
  have hhk : h ^ k = h ^ k' := by rw [hk'def]; exact zpow_eq_zpow_emod' k hhN
  have hrel : g ^ j' * h ^ k' = 1 := by rw [← hgj, ← hhk]; exact hjk
  have hgj' : g ^ j' = g ^ j'.toNat := by
    nth_rewrite 1 [← Int.toNat_of_nonneg hj'nn]
    rw [zpow_natCast]
  have hhk' : h ^ k' = h ^ k'.toNat := by
    nth_rewrite 1 [← Int.toNat_of_nonneg hk'nn]
    rw [zpow_natCast]
  have hnat : g ^ j'.toNat * h ^ k'.toNat = 1 := by rw [← hgj', ← hhk']; exact hrel
  have hdvdj' : n ∣ j'.toNat := (hmain j'.toNat k'.toNat hnat).1
  have h1 : (n : ℤ) ∣ j' := by
    rw [← Int.toNat_of_nonneg hj'nn]
    exact_mod_cast hdvdj'
  have h2 : (n : ℤ) ∣ j - j' := by
    have hsplit : j - j' = (Fintype.card G : ℤ) * (j / (Fintype.card G : ℤ)) := by
      have h := Int.emod_add_mul_ediv j (Fintype.card G : ℤ)
      rw [hj'def]
      linarith
    rw [hsplit]
    exact dvd_mul_of_dvd_left hz _
  have h3 := dvd_add h1 h2
  rwa [show j' + (j - j') = j by ring] at h3

/-- **Integer exponents from natural exponents, both coordinates.**  Version of
`dvd_of_zpow_mul_eq_one` for `k` as well, obtained by swapping the roles of `g` and `h`. -/
theorem zpow_dvd_of_nat_pow_dvd {G : Type*} [Group G] [Fintype G] {g h : G} {n : ℕ}
    (hmain : ∀ u v : ℕ, g ^ u * h ^ v = 1 → n ∣ u ∧ n ∣ v) {j k : ℤ}
    (hjk : g ^ j * h ^ k = 1) : (n : ℤ) ∣ j ∧ (n : ℤ) ∣ k := by
  refine ⟨dvd_of_zpow_mul_eq_one hmain hjk, ?_⟩
  have hmain' : ∀ u v : ℕ, h ^ u * g ^ v = 1 → n ∣ u ∧ n ∣ v := by
    intro u v huv
    have h1 : h ^ u = (g ^ v)⁻¹ := eq_inv_of_mul_eq_one_left huv
    have h2 : g ^ v * h ^ u = 1 := by rw [h1, mul_inv_cancel]
    exact (hmain v u h2).symm
  have hjk' : h ^ k * g ^ j = 1 := by
    have h1 : h ^ k = (g ^ j)⁻¹ := eq_inv_of_mul_eq_one_right hjk
    rw [h1, inv_mul_cancel]
  exact dvd_of_zpow_mul_eq_one hmain' hjk'

/-- The integer-exponent form of the main arithmetic input of the auxiliary-field construction:
there are a modulus `M` coprime to the primes of `T`, a unit `ℓu` and units `au i` lifting the
`a i` (and `ℓ`) such that the relation `ℓu ^ j * (au i) ^ k = 1` forces `n ∣ j` and `n ∣ k` for
integer exponents. -/
theorem auxField_arith_zpow (n : ℕ) (hn : 0 < n) {ι : Type} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i, 1 < a i) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ∃ (M : ℕ) (_ : NeZero M) (ℓu : (ZMod M)ˣ) (au : ι → (ZMod M)ˣ),
      (∀ p ∈ T, ¬ p ∣ M) ∧ (∀ i, (au i : ZMod M) = (a i : ZMod M)) ∧
      ∀ i (j k : ℤ), ℓu ^ j * (au i) ^ k = 1 → (n : ℤ) ∣ j ∧ (n : ℤ) ∣ k := by
  obtain ⟨M, hMne, ℓ, hℓprime, hMT, hcop, hℓM, hmain⟩ := auxField_arith n hn a ha T hT
  refine ⟨M, hMne, ZMod.unitOfCoprime ℓ ((hℓprime.coprime_iff_not_dvd).mpr hℓM),
    fun i => ZMod.unitOfCoprime (a i) (hcop i), hMT, ?_, ?_⟩
  · intro i
    rw [ZMod.coe_unitOfCoprime]
  · intro i j k hrel
    refine zpow_dvd_of_nat_pow_dvd (fun u v huv => hmain i u v ?_) hrel
    have := congrArg (fun y : (ZMod M)ˣ => (y : ZMod M)) huv
    simpa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one,
      ZMod.coe_unitOfCoprime] using this

end NK.CFTLib.ARL
