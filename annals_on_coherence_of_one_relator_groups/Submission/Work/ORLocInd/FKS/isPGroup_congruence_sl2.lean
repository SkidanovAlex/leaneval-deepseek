import Mathlib

namespace Work.ORLocInd.FKS

open Matrix

/-!
# The principal congruence subgroup of `SL(2, ℤ/p^k)` is a `p`-group

We show that any `2 × 2` matrix over `ZMod (p^k)` congruent to the identity modulo `p` has
`p`-power order, whence the kernel of the reduction `SL(2, ℤ/p^k) → SL(2, ℤ/p)` is a `p`-group.

The heart of the argument is the congruence `(1 + p^m X)^p ≡ 1  (mod p^(m+1))` for `m ≥ 1`:
in the binomial expansion `∑ᵢ C(p,i) • (p^m X)^i` the term `i = 1` contributes `p^(m+1) X`, and
every term `i ≥ 2` contributes `C(p,i) p^(m i) X^i` with `p^(m+1) | C(p,i) p^(m i)`.
-/

/-- `p^(m+1)` divides `C(p,j) * p^(m j)` for `p` prime, `m ≥ 1` and `0 < j ≤ p`. -/
private lemma p_pow_dvd (p m j : ℕ) (hp : p.Prime) (hm : 0 < m) (hj : 0 < j) (hjp : j ≤ p) :
    p ^ (m + 1) ∣ p ^ (m * j) * p.choose j := by
  rcases lt_or_eq_of_le hjp with h | h
  · obtain ⟨k, hk⟩ := hp.dvd_choose_self (by omega) h
    rw [hk, ← mul_assoc, ← pow_succ]
    have hle : m ≤ m * j := by simpa using Nat.mul_le_mul_left m hj
    exact dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) k
  · rw [h, Nat.choose_self, mul_one]
    have hle : m * 2 ≤ m * p := Nat.mul_le_mul_left m hp.two_le
    exact pow_dvd_pow p (by omega)

/-- Elements of `ZMod (p^k)` that are killed by the reduction modulo `p` are multiples of `p`. -/
private lemma castHom_eq_zero_aux (p k : ℕ) (h : p ∣ p ^ k) (x : ZMod (p ^ k))
    (hx : ZMod.castHom h (ZMod p) x = 0) :
    ∃ y : ZMod (p ^ k), x = (p : ZMod (p ^ k)) * y := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  have ha : (a : ZMod p) = 0 := by simpa using hx
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha
  obtain ⟨b, hb⟩ := ha
  exact ⟨(b : ZMod (p ^ k)), by rw [hb]; push_cast; ring⟩

/-- A matrix congruent to the identity modulo `p` is of the form `1 + p • Y`. -/
private lemma exists_eq_one_add_smul_aux (p k : ℕ) (h : p ∣ p ^ k)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)))
    (hA : A.map (ZMod.castHom h (ZMod p)) = 1) :
    ∃ Y : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)), A = 1 + (p : ZMod (p ^ k)) • Y := by
  have hex : ∀ i j : Fin 2, ∃ y : ZMod (p ^ k),
      A i j - (if i = j then 1 else 0) = (p : ZMod (p ^ k)) * y := by
    intro i j
    apply castHom_eq_zero_aux p k h
    rw [map_sub]
    have h1 : ZMod.castHom h (ZMod p) (A i j) = (if i = j then 1 else 0) := by
      have := congrFun (congrFun hA i) j
      simpa [Matrix.map_apply, Matrix.one_apply] using this
    have h2 : ZMod.castHom h (ZMod p) (if i = j then (1 : ZMod (p ^ k)) else 0)
        = (if i = j then (1 : ZMod p) else 0) := by
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij]; exact map_one _
      · rw [if_neg hij, if_neg hij]; exact map_zero _
    rw [h1, h2, sub_self]
  let Y : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)) := fun i j => Classical.choose (hex i j)
  have hY : ∀ i j, A i j - (if i = j then 1 else 0) = (p : ZMod (p ^ k)) * Y i j :=
    fun i j => Classical.choose_spec (hex i j)
  refine ⟨Y, ?_⟩
  apply Matrix.ext
  intro i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  have hh := hY i j
  rw [sub_eq_iff_eq_add] at hh
  rw [hh, smul_eq_mul, add_comm]

/-- The key congruence: `(1 + p^m X)^p ≡ 1 (mod p^(m+1))` for matrices over a commutative
ring, `p` prime and `m ≥ 1`.  The proof uses only the centrality of the scalar `p^m` and the
binomial theorem for the commuting elements `1` and `p^m • X`. -/
private lemma matrix_step_aux {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p m : ℕ) (hp : p.Prime) (hm : 0 < m) (Y : Matrix ι ι R) :
    ∃ Z : Matrix ι ι R, (1 + (p ^ m : R) • Y) ^ p = 1 + (p ^ (m + 1) : R) • Z := by
  have hnatCast : ∀ n : ℕ, (n : Matrix ι ι R) = (n : R) • (1 : Matrix ι ι R) := by
    intro n; ext i j; rw [Matrix.natCast_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  have hterm : ∀ i : ℕ, ((p ^ m : R) • Y) ^ i * ((p.choose i : ℕ) : Matrix ι ι R)
      = (((p ^ (m * i) * p.choose i : ℕ) : R)) • Y ^ i := by
    intro i
    rw [smul_pow, ← pow_mul, hnatCast (p.choose i), smul_mul_assoc, mul_smul_comm, mul_one,
        smul_smul, ← Nat.cast_pow, ← Nat.cast_mul]
  refine ⟨∑ i ∈ Finset.range p,
    (((p ^ (m * (i + 1)) * p.choose (i + 1)) / p ^ (m + 1) : ℕ) : R) • Y ^ (i + 1), ?_⟩
  have hexp : (1 + (p ^ m : R) • Y) ^ p
      = ∑ i ∈ Finset.range (p + 1),
          ((p ^ m : R) • Y) ^ i * ((p.choose i : ℕ) : Matrix ι ι R) := by
    rw [show (1 : Matrix ι ι R) + (p ^ m : R) • Y = ((p ^ m : R) • Y) + 1 by rw [add_comm],
        Commute.add_pow (Commute.one_right _) p]
    simp
  rw [hexp, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, hnatCast 1, one_smul]
  have hsum : ∑ i ∈ Finset.range p,
        ((p ^ m : R) • Y) ^ (i + 1) * ((p.choose (i + 1) : ℕ) : Matrix ι ι R)
      = (p ^ (m + 1) : R) • (∑ i ∈ Finset.range p,
          (((p ^ (m * (i + 1)) * p.choose (i + 1)) / p ^ (m + 1) : ℕ) : R) • Y ^ (i + 1)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hterm (i + 1)]
    have hd : p ^ (m + 1) * ((p ^ (m * (i + 1)) * p.choose (i + 1)) / p ^ (m + 1))
        = p ^ (m * (i + 1)) * p.choose (i + 1) :=
      Nat.mul_div_cancel' (p_pow_dvd p m (i + 1) hp hm (by omega)
        (by have := Finset.mem_range.mp hi; omega))
    calc (((p ^ (m * (i + 1)) * p.choose (i + 1) : ℕ) : R)) • Y ^ (i + 1)
        = (((p ^ (m + 1) * ((p ^ (m * (i + 1)) * p.choose (i + 1)) / p ^ (m + 1)) : ℕ) : R))
            • Y ^ (i + 1) := by
          rw [hd]
      _ = (p ^ (m + 1) : R)
            • ((((p ^ (m * (i + 1)) * p.choose (i + 1)) / p ^ (m + 1) : ℕ) : R) • Y ^ (i + 1)) := by
          rw [Nat.cast_mul, Nat.cast_pow, smul_smul]
  rw [hsum]
  abel

/-- The kernel of the reduction `SL(2, ℤ/p^k) → SL(2, ℤ/p)` is a `p`-group.  Matrices congruent
to the identity modulo `p` satisfy `(1 + pX)^(p^s) ≡ 1  (mod p^(s+1))`: in the binomial expansion of
`(1 + pX)^p` the term `i = 1` contributes `p^2 X` and each term `i ≥ 2` contributes
`C(p,i) p^(2i) X^i` with `p | C(p,i)`. -/
theorem isPGroup_congruence_sl2 (p k : ℕ) (hp : p.Prime) (h : p ∣ p^k) :
    IsPGroup p (MonoidHom.ker (Matrix.SpecialLinearGroup.map (ZMod.castHom h (ZMod p)) :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod (p^k)) →*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨k - 1, ?_⟩
  let K : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)) := Matrix.SpecialLinearGroup.coeMonoidHom g.1
  have hmap : K.map (ZMod.castHom h (ZMod p)) = 1 := by
    have h1 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
        (x : Matrix (Fin 2) (Fin 2) (ZMod p))) (MonoidHom.mem_ker.mp g.2)
    simpa [K, Matrix.SpecialLinearGroup.coeMonoidHom_apply,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using h1
  obtain ⟨Y, hY⟩ := exists_eq_one_add_smul_aux p k h K hmap
  have hiter : ∀ s : ℕ, ∃ Z : Matrix (Fin 2) (Fin 2) (ZMod (p ^ k)),
      K ^ (p ^ s) = 1 + (p ^ (s + 1) : ZMod (p ^ k)) • Z := by
    intro s
    induction s with
    | zero => exact ⟨Y, by rw [hY]; simp⟩
    | succ t ih =>
        obtain ⟨Z, hZ⟩ := ih
        obtain ⟨Z', hZ'⟩ := matrix_step_aux p (t + 1) hp (Nat.succ_pos t) Z
        exact ⟨Z', by rw [pow_succ, pow_mul, hZ, hZ']⟩
  obtain ⟨Z, hZ⟩ := hiter (k - 1)
  have hK1 : K ^ (p ^ (k - 1)) = 1 := by
    rw [hZ,
      show (p ^ ((k - 1) + 1) : ZMod (p ^ k)) = 0 from
        ZMod.natCast_pow_eq_zero_of_le p (by omega),
      zero_smul, add_zero]
  have hg1 : g.1 ^ (p ^ (k - 1)) = 1 := by
    apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    rw [map_pow, map_one]
    exact hK1
  exact Subtype.ext hg1

end Work.ORLocInd.FKS
