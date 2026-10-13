import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSAM3.Api
import Submission.Work.DSM5b.Basic

/-!
# `modSplit_twist` — shared definitions

Vocabulary for the node `DSMap.Gaps.modSplit_twist` (the "TWIST" node of the EQP design):
the *levels* `W_n = ψW(B)^{1/p^n}` of a perfection `W` of `B`, together with the elementary
root-tower bookkeeping used to move between them.
-/

open CategoryTheory
open scoped TensorProduct

namespace Work.DSEQP

universe a

/-! ## Group powers of a ring equivalence are function iterates -/

lemma ringEquiv_pow_apply {R : Type a} [CommSemiring R] (f : R ≃+* R) (n : ℕ) (x : R) :
    (⇑(f ^ n)) x = (⇑f)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    exact (congrArg f (ih x)).trans (Function.iterate_succ_apply' _ _ _).symm

/-! ## Root-tower bookkeeping for `k ↦ x^{1/p^k}` -/

section Roots

variable {R : Type a} [CommRing R] (p : ℕ) [ExpChar R p] [PerfectRing R p]

/-- The `n`-fold iterate of the inverse Frobenius is the `n`-th iterate of
`(frobeniusEquiv R p).symm` as a function. -/
lemma iterateFrobeniusEquiv_symm_apply (n : ℕ) (x : R) :
    (iterateFrobeniusEquiv R p n).symm x = ((frobeniusEquiv R p).symm^[n]) x := by
  rw [iterateFrobeniusEquiv_symm]
  exact ringEquiv_pow_apply (frobeniusEquiv R p).symm n x

/-- Additivity of the `n`-th root map. -/
lemma iterateFrobeniusEquiv_symm_add (n : ℕ) (x y : R) :
    ((frobeniusEquiv R p).symm^[n]) (x + y) =
      ((frobeniusEquiv R p).symm^[n]) x + ((frobeniusEquiv R p).symm^[n]) y := by
  rw [← iterateFrobeniusEquiv_symm_apply p n (x + y),
    ← iterateFrobeniusEquiv_symm_apply p n x, ← iterateFrobeniusEquiv_symm_apply p n y, map_add]

/-- Multiplicativity of the `n`-th root map. -/
lemma iterateFrobeniusEquiv_symm_mul (n : ℕ) (x y : R) :
    ((frobeniusEquiv R p).symm^[n]) (x * y) =
      ((frobeniusEquiv R p).symm^[n]) x * ((frobeniusEquiv R p).symm^[n]) y := by
  rw [← iterateFrobeniusEquiv_symm_apply p n (x * y),
    ← iterateFrobeniusEquiv_symm_apply p n x, ← iterateFrobeniusEquiv_symm_apply p n y, map_mul]

/-- `(x^{1/p^n})^{p^n} = x`. -/
lemma iterateFrobeniusEquiv_symm_pow (n : ℕ) (x : R) :
    (((frobeniusEquiv R p).symm^[n]) x) ^ (p ^ n) = x := by
  have h := (Work.DSM5b.IsRootTower.frozen p R x).pow_pow 0 n
  simpa only [zero_add, Function.iterate_zero_apply] using h

/-- The `n`-th root map inverts `p ^ n`-th powers. -/
lemma iterateFrobeniusEquiv_symm_apply_pow (n : ℕ) (x : R) :
    (iterateFrobeniusEquiv R p n).symm (x ^ (p ^ n)) = x := by
  rw [← iterateFrobeniusEquiv_def]
  exact RingEquiv.symm_apply_apply _ x

/-- `p ^ N`-th powers are injective. -/
lemma pow_pow_injective (N : ℕ) : Function.Injective (fun x : R => x ^ (p ^ N)) := by
  have hinj : Function.Injective ((⇑(frobenius R p))^[N]) :=
    (injective_frobenius R p).iterate N
  intro x y hxy
  apply hinj
  rwa [iterate_frobenius, iterate_frobenius]

/-- **Root bookkeeping.**  For `k ≤ N`, raising the `k`-th root of `y` to the `p ^ N`-th power
gives `y ^ (p ^ (N - k))`. -/
lemma iterateFrobeniusEquiv_symm_pow_pow (y : R) {k N : ℕ} (hk : k ≤ N) :
    (((frobeniusEquiv R p).symm^[k]) y) ^ (p ^ N) = y ^ (p ^ (N - k)) := by
  have h1 : (((frobeniusEquiv R p).symm^[k]) y) ^ (p ^ k) = y :=
    iterateFrobeniusEquiv_symm_pow p k y
  have hN : p ^ N = p ^ k * p ^ (N - k) := by rw [← pow_add, Nat.add_sub_of_le hk]
  rw [hN, pow_mul, h1]

/-- **Root bookkeeping, inverted.**  For `k ≤ N`, the `p ^ N`-th root of
`y ^ (p ^ (N - k))` is the `p ^ k`-th root of `y`. -/
lemma iterateFrobeniusEquiv_symm_eq (y : R) {k N : ℕ} (hk : k ≤ N) :
    ((frobeniusEquiv R p).symm^[N]) (y ^ (p ^ (N - k))) = ((frobeniusEquiv R p).symm^[k]) y := by
  refine pow_pow_injective p N ?_
  show (((frobeniusEquiv R p).symm^[N]) (y ^ (p ^ (N - k)))) ^ (p ^ N) =
      (((frobeniusEquiv R p).symm^[k]) y) ^ (p ^ N)
  rw [iterateFrobeniusEquiv_symm_pow_pow p (y ^ (p ^ (N - k))) (le_refl N),
    iterateFrobeniusEquiv_symm_pow_pow p y hk]
  simp

/-- **Root bookkeeping, mixed.**  For `k ≤ N`, the `p ^ (N - k)`-th power of the `N`-th root of
`x` is the `k`-th root of `x`. -/
lemma iterateFrobeniusEquiv_symm_pow_eq (x : R) {k N : ℕ} (hk : k ≤ N) :
    (((frobeniusEquiv R p).symm^[N]) x) ^ (p ^ (N - k)) = ((frobeniusEquiv R p).symm^[k]) x := by
  have h := (Work.DSM5b.IsRootTower.frozen p R x).pow_pow k (N - k)
  rw [Nat.add_sub_of_le hk] at h
  exact h

end Roots

/-! ## The levels `W_n = ψW(B)^{1/p^n}` -/

section Level

variable {A B W : Type a} [CommRing A] [CommRing B] [Algebra A B] [CommRing W]
variable [Algebra A W]

/-- `W_n = ψW(B)^{1/p^n} = {w : W | ∃ b : B, w ^ (p^n) = ψW b}`, an `A`-submodule of `W`. -/
def twistLevel (p : ℕ) [Fact p.Prime] [CharP W p] (ψW : B →+* W)
    (hAW : algebraMap A W = ψW.comp (algebraMap A B)) (n : ℕ) : Submodule A W where
  carrier := {w | ∃ b : B, w ^ (p ^ n) = ψW b}
  zero_mem' := ⟨0, by rw [zero_pow (pow_ne_zero n (Fact.out : p.Prime).pos.ne'), map_zero]⟩
  add_mem' := by
    rintro x y ⟨b, hb⟩ ⟨b', hb'⟩
    exact ⟨b + b', by rw [add_pow_char_pow, hb, hb', ← map_add]⟩
  smul_mem' := by
    rintro a x ⟨b, hb⟩
    refine ⟨(algebraMap A B a) ^ (p ^ n) * b, ?_⟩
    have ha : algebraMap A W a = ψW (algebraMap A B a) := by rw [hAW]; rfl
    rw [Algebra.smul_def, mul_pow, hb, ha, map_mul, map_pow]

@[simp] lemma mem_twistLevel (p : ℕ) [Fact p.Prime] [CharP W p] (ψW : B →+* W)
    (hAW : algebraMap A W = ψW.comp (algebraMap A B)) {n : ℕ} {w : W} :
    w ∈ twistLevel p ψW hAW n ↔ ∃ b : B, w ^ (p ^ n) = ψW b := Iff.rfl

/-- The levels are nested. -/
lemma twistLevel_mono (p : ℕ) [Fact p.Prime] [CharP W p] (ψW : B →+* W)
    (hAW : algebraMap A W = ψW.comp (algebraMap A B)) {m n : ℕ} (hmn : m ≤ n) :
    twistLevel p ψW hAW m ≤ twistLevel p ψW hAW n := by
  intro w hw
  obtain ⟨b, hb⟩ := hw
  refine ⟨b ^ (p ^ (n - m)), ?_⟩
  rw [map_pow, ← hb, ← pow_mul, ← pow_add, Nat.add_sub_of_le hmn]

end Level

/-! ## An `A`-linear functional at a unit -/

section ApplyOne

variable {A B : Type a} [CommRing A] [CommRing B] [Algebra A B]

/-- `φ (algebraMap A B z) = z * φ 1`. -/
lemma apply_algebraMap_one (φ : B →ₗ[A] A) (z : A) : φ (algebraMap A B z) = z * φ 1 := by
  rw [show algebraMap A B z = z • (1 : B) from by rw [Algebra.smul_def, mul_one],
    map_smul, smul_eq_mul]

/-- `φ (algebraMap A B z * b) = z * φ b`. -/
lemma apply_algebraMap_mul (φ : B →ₗ[A] A) (z : A) (b : B) :
    φ (algebraMap A B z * b) = z * φ b := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

end ApplyOne

end Work.DSEQP
