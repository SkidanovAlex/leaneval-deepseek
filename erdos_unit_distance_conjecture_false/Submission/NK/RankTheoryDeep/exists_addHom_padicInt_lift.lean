import Mathlib

/-!
# The additive universal property of `ℤ_2` as the limit `lim_n ℤ/2^n`

Given a compatible family of *additive* homomorphisms `f n : A →+ ZMod (2^n)` — compatible
meaning that `f m x` is the reduction of `f n x` along `ZMod.castHom (pow_dvd_pow 2 h)` for
`m ≤ n` — we produce an additive homomorphism `g : A →+ ℤ_[2]` whose `n`-th reduction
`PadicInt.toZModPow n` is `f n`.

Mathlib's `PadicInt.lift` provides exactly this statement for `R` a `NonAssocSemiring` and *ring*
homomorphisms.  The present lemma is the additive version, needed when the source is only an
`AddCommGroup`.  There is no way to reduce it to the ring version, so the projective limit is
reconstructed here additively.

## The argument

* For `x : A` the integer representatives `k_n := (f n x).val` form a `2`-adically Cauchy sequence
  (`PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub`): compatibility forces `2^i ∣ k_{i+1} - k_i`.
* `PadicInt.ofIntSeq` turns this sequence into an element `g₀ x : ℤ_[2]`, and Mathlib's
  `PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub` identifies its reductions:
  `toZModPow n (g₀ x) = (k_n : ZMod (2^n)) = f n x`.
* Additivity is then forced by `PadicInt.ext_of_toZModPow` (the reductions separate points of
  `ℤ_[2]`): the two sides have the same reduction mod `2^n` for every `n`, since `f n` is additive.
-/

namespace NK.RankTheoryDeep

open PadicInt

noncomputable section

variable {A : Type*} [AddCommGroup A]

/-- The integer representative sequence attached to a family `f` of additive homomorphisms:
`n ↦ (f n x).val`, the unique element of `{0, …, 2^n - 1}` representing `f n x`. -/
private def nthInt (f : ∀ n : ℕ, A →+ ZMod (2^n)) (x : A) (n : ℕ) : ℤ := ((f n x).val : ℤ)

/-- **Compatibility implies `2`-adic coherence of the representatives.**  If the family `f` is
compatible then the integer representatives `k_n = (f n x).val` satisfy `2^i ∣ k_{i+1} - k_i`,
which is precisely the hypothesis of `PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub`. -/
private lemma pow_dvd_nthInt_sub (f : ∀ n : ℕ, A →+ ZMod (2^n))
    (hf : ∀ (m n : ℕ) (h : m ≤ n) (x : A),
      f m x = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m)) (f n x))
    (x : A) (i : ℕ) : (2 : ℤ) ^ i ∣ nthInt f x (i + 1) - nthInt f x i := by
  have h := hf i (i + 1) (Nat.le_succ i) x
  -- `ZMod.castHom (pow_dvd_pow 2 _) _ (f (i+1) x)` is the `val` of `f (i+1) x`, reduced mod `2^i`
  have h1 : (((f (i + 1) x).val : ℕ) : ZMod (2 ^ i)) =
      ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ i)) (ZMod (2 ^ i)) (f (i + 1) x) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have h2 : (((f i x).val : ℕ) : ZMod (2 ^ i)) =
      ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ i)) (ZMod (2 ^ i)) (f (i + 1) x) := by
    rw [ZMod.natCast_zmod_val, h]
  have hkey : (((f (i + 1) x).val : ℕ) : ZMod (2 ^ i)) =
      (((f i x).val : ℕ) : ZMod (2 ^ i)) := h1.trans h2.symm
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub ((f i x).val : ℤ) ((f (i + 1) x).val : ℤ)
    (2 ^ i)).mp (by simpa only [Int.cast_natCast] using hkey.symm)
  simpa [nthInt] using this

/-- The candidate lift of the compatible family `f`, at a point `x : A`, obtained as the `2`-adic
limit of the integer representatives `(f n x).val`. -/
private def liftAt (f : ∀ n : ℕ, A →+ ZMod (2^n))
    (hf : ∀ (m n : ℕ) (h : m ≤ n) (x : A),
      f m x = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m)) (f n x)) (x : A) : ℤ_[2] :=
  PadicInt.ofIntSeq (nthInt f x)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (nthInt f x) 2 (pow_dvd_nthInt_sub f hf x))

/-- **The defining property of the lift**: its `n`-th reduction is `f n`. -/
private lemma toZModPow_liftAt (f : ∀ n : ℕ, A →+ ZMod (2^n))
    (hf : ∀ (m n : ℕ) (h : m ≤ n) (x : A),
      f m x = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m)) (f n x))
    (x : A) (n : ℕ) : PadicInt.toZModPow n (liftAt f hf x) = f n x := by
  have h := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (nthInt f x) 2 (pow_dvd_nthInt_sub f hf x) n
  simp only [liftAt]
  exact h.trans (by simp [nthInt])

/-- **The lift is additive**, because the reductions `toZModPow n` separate the points of `ℤ_[2]`
(`PadicInt.ext_of_toZModPow`) and `f n` is additive for every `n`. -/
private def liftHom (f : ∀ n : ℕ, A →+ ZMod (2^n))
    (hf : ∀ (m n : ℕ) (h : m ≤ n) (x : A),
      f m x = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m)) (f n x)) : A →+ ℤ_[2] where
  toFun := liftAt f hf
  map_zero' := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    simp [toZModPow_liftAt f hf]
  map_add' := fun x y => by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    simp [toZModPow_liftAt f hf]

/-- **The additive universal property of `ℤ_2` as the limit `lim_n ℤ/2^n`.**  Given a compatible
family of additive homomorphisms `f n : A →+ ZMod (2^n)` — where compatibility means that for
`m ≤ n` the value `f m x` is the reduction of `f n x` along `ZMod.castHom (pow_dvd_pow 2 h)` —
there is an additive homomorphism `g : A →+ ℤ_[2]` whose `n`-th reduction is `f n`. -/
theorem exists_addHom_padicInt_lift {A : Type*} [AddCommGroup A] (f : ∀ n : ℕ, A →+ ZMod (2^n))
    (hf : ∀ (m n : ℕ) (h : m ≤ n) (x : A),
      f m x = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m)) (f n x)) :
    ∃ g : A →+ PadicInt 2, ∀ (n : ℕ) (x : A), PadicInt.toZModPow n (g x) = f n x :=
  ⟨liftHom f hf, fun n x => toZModPow_liftAt f hf x n⟩

end

end NK.RankTheoryDeep
