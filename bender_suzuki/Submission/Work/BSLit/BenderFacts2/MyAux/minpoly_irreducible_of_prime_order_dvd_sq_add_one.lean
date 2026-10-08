import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.BSLit.BenderFacts2.MyAux

/-- If `ℓ ∣ q² + 1` then `ℓ ∣ q⁴ - 1`. -/
theorem dvd_four_of_dvd_sq_add_one (q ℓ : ℕ) (h : ℓ ∣ q ^ 2 + 1) : ℓ ∣ q ^ 4 - 1 := by
  have h2 : q ^ 2 + 1 ∣ q ^ 4 - 1 := by
    refine ⟨q ^ 2 - 1, ?_⟩
    have hh := Nat.sq_sub_sq (q ^ 2) 1
    simp only [one_pow] at hh
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring]
    exact hh
  exact dvd_trans h h2

/-- Over a finite field `F` of characteristic `p`, if `ℓ` is a prime with `ℓ ∣ |F|² + 1`,
then `(ℓ : F) ≠ 0`.  Indeed `Nat.card F = p ^ n` with `n ≥ 1`, so `p ∣ |F|²` and also
`p ∣ |F|² + 1`, whence `p ∣ 1`, impossible; and `p = ℓ` because `(ℓ : F) = 0` forces
`p ∣ ℓ`. -/
theorem natCast_ne_zero_of_prime_dvd_sq_add_one {F : Type*} [Field F] [Finite F]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hdvd : ℓ ∣ Nat.card F ^ 2 + 1) : (ℓ : F) ≠ 0 := by
  intro h
  obtain ⟨p, hp⟩ := CharP.exists F
  haveI : CharP F p := hp
  have hpprime : p.Prime := CharP.char_is_prime F p
  have hpℓ : p ∣ ℓ := (CharP.cast_eq_zero_iff F p ℓ).mp h
  have hpeq : p = ℓ := (Nat.prime_dvd_prime_iff_eq hpprime hℓ).mp hpℓ
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F p
  have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hpdvd : p ∣ Nat.card F ^ 2 := by
    rw [hcard, pow_two]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (PNat.pos n).ne') _
  have hp1 : p ∣ Nat.card F ^ 2 + 1 := hpeq ▸ hdvd
  have hsub : p ∣ Nat.card F ^ 2 + 1 - Nat.card F ^ 2 := Nat.dvd_sub hp1 hpdvd
  rw [Nat.add_sub_cancel_left] at hsub
  have h2 := hpprime.two_le
  have := Nat.le_of_dvd one_pos hsub
  omega

/-- `X - 1` does not divide the geometric sum `∑_{i<ℓ} X^i` when `(ℓ : F) ≠ 0`. -/
theorem X_sub_one_not_dvd_geom_sum {F : Type*} [Field F] {ℓ : ℕ} (hℓ : (ℓ : F) ≠ 0) :
    ¬ (Polynomial.X - 1 : Polynomial F) ∣
        ∑ i ∈ Finset.range ℓ, (Polynomial.X : Polynomial F) ^ i := by
  intro hd
  have hd' : (Polynomial.X - Polynomial.C (1 : F)) ∣
      (∑ i ∈ Finset.range ℓ, (Polynomial.X : Polynomial F) ^ i) := by
    simpa using hd
  have h2 : (∑ i ∈ Finset.range ℓ, (Polynomial.X : Polynomial F) ^ i).IsRoot 1 :=
    (Polynomial.dvd_iff_isRoot).mp hd'
  have h1 : (∑ i ∈ Finset.range ℓ, (Polynomial.X : Polynomial F) ^ i).eval 1 = 0 := h2
  rw [Polynomial.eval_finsetSum] at h1
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow] at h1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
  exact hℓ h1

/-- `X ^ ℓ - 1` divides `X ^ (|F|⁴) - X` when `ℓ ∣ |F|⁴ - 1`. -/
theorem X_pow_sub_one_dvd_X_pow_card_pow_sub_X {F : Type*} [Field F] [Finite F] (ℓ : ℕ)
    (h : ℓ ∣ Nat.card F ^ 4 - 1) :
    (Polynomial.X : Polynomial F) ^ ℓ - 1 ∣
      (Polynomial.X : Polynomial F) ^ (Nat.card F ^ 4) - Polynomial.X := by
  obtain ⟨k, hk⟩ := h
  have hQ : 1 ≤ Nat.card F ^ 4 := Nat.one_le_pow 4 _ Nat.card_pos
  have hQeq : Nat.card F ^ 4 = ℓ * k + 1 := by rw [← hk, Nat.sub_add_cancel hQ]
  have h1 : (Polynomial.X : Polynomial F) ^ ℓ - 1 ∣
      ((Polynomial.X : Polynomial F) ^ ℓ) ^ k - 1 := by
    have := sub_dvd_pow_sub_pow ((Polynomial.X : Polynomial F) ^ ℓ) (1 : Polynomial F) k
    simpa using this
  have h2 : ((Polynomial.X : Polynomial F) ^ ℓ) ^ k - 1 ∣
      (Polynomial.X : Polynomial F) ^ (Nat.card F ^ 4) - Polynomial.X := by
    refine ⟨Polynomial.X, ?_⟩
    rw [hQeq, pow_add, pow_one, pow_mul]; ring
  exact dvd_trans h1 h2

/-- The minimal polynomial of a matrix `A` with `A ^ ℓ = 1` divides `X ^ ℓ - 1`. -/
theorem minpoly_dvd_X_pow_sub_one {F : Type*} [Field F]
    (A : Matrix.GeneralLinearGroup (Fin 4) F) {ℓ : ℕ} (hA : A ^ ℓ = 1) :
    minpoly F (A : Matrix (Fin 4) (Fin 4) F) ∣ (Polynomial.X : Polynomial F) ^ ℓ - 1 := by
  have hM : (A : Matrix (Fin 4) (Fin 4) F) ^ ℓ = 1 := by
    rw [← Units.val_pow_eq_pow_val, hA, Units.val_one]
  refine minpoly.dvd F _ ?_
  rw [map_sub, map_pow, map_one, Polynomial.aeval_X, hM, sub_self]

/-- The minimal polynomial of a `4 × 4` matrix has degree at most `4`. -/
theorem minpoly_natDegree_le_four {F : Type*} [Field F]
    (A : Matrix.GeneralLinearGroup (Fin 4) F) :
    (minpoly F (A : Matrix (Fin 4) (Fin 4) F)).natDegree ≤ 4 := by
  have h := Matrix.minpoly_dvd_charpoly (A : Matrix (Fin 4) (Fin 4) F)
  have h4 : (A : Matrix (Fin 4) (Fin 4) F).charpoly.natDegree = 4 := by
    rw [Matrix.charpoly_natDegree_eq_dim]; simp
  have hc : (A : Matrix (Fin 4) (Fin 4) F).charpoly ≠ 0 := by
    intro h0; rw [h0] at h4; simp at h4
  have := Polynomial.natDegree_le_of_dvd h hc
  rwa [h4] at this

/-- **Key degree computation.**  Let `F` be a finite field and `ℓ` an odd prime with
`ℓ ∣ |F|² + 1`.  If `f` is an irreducible polynomial dividing `X ^ ℓ - 1`, and `f` does not
divide `X - 1`, then `f` has degree `4`.

The proof: since `ℓ ∣ |F|² + 1` we get `ℓ ∣ |F|⁴ - 1`, so `X ^ ℓ - 1 ∣ X ^ (|F|⁴) - X` and
hence `f.natDegree ∣ 4`.  If moreover `f.natDegree ∣ 2`, then `f ∣ X ^ (|F|²) - X`; working in
`F[X]/(f)` with `x = X mod f`, the element `x` satisfies `x ^ ℓ = 1`, `x ≠ 1` (as `f ∤ X - 1`)
and `x ^ (|F|²) = x`, so `x` has order `ℓ` and `ℓ ∣ |F|² - 1`, contradicting `ℓ ∣ |F|² + 1`.
Therefore `f.natDegree = 4`. -/
theorem irreducible_factor_natDegree_eq_four {F : Type*} [Field F] [Finite F] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hodd : Odd ℓ) (hdvd : ℓ ∣ Nat.card F ^ 2 + 1) {f : Polynomial F}
    (hf : Irreducible f) (hne : ¬ f ∣ Polynomial.X - 1)
    (hfdiv : f ∣ (Polynomial.X : Polynomial F) ^ ℓ - 1) : f.natDegree = 4 := by
  have h4 : ℓ ∣ Nat.card F ^ 4 - 1 := dvd_four_of_dvd_sq_add_one _ _ hdvd
  have hdeg4 : f.natDegree ∣ 4 :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hf
      (dvd_trans hfdiv (X_pow_sub_one_dvd_X_pow_card_pow_sub_X ℓ h4))
  have hnot2 : ¬ f.natDegree ∣ 2 := by
    intro hd2
    have hfdvd : f ∣ (Polynomial.X : Polynomial F) ^ (Nat.card F ^ 2) - Polynomial.X :=
      (Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hf).mp hd2
    haveI : Fact (Irreducible f) := ⟨hf⟩
    have hroot : Polynomial.aeval (AdjoinRoot.root f) f = 0 := by
      rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
    have hxe : (AdjoinRoot.root f) ^ ℓ = 1 := by
      have hh : Polynomial.aeval (AdjoinRoot.root f)
          ((Polynomial.X : Polynomial F) ^ ℓ - 1) = 0 := by
        obtain ⟨g, hg⟩ := hfdiv
        rw [hg, map_mul, hroot, zero_mul]
      rw [map_sub, map_pow, map_one, Polynomial.aeval_X] at hh
      exact sub_eq_zero.mp hh
    have hxq : (AdjoinRoot.root f) ^ (Nat.card F ^ 2) = AdjoinRoot.root f := by
      have hh : Polynomial.aeval (AdjoinRoot.root f)
          ((Polynomial.X : Polynomial F) ^ (Nat.card F ^ 2) - Polynomial.X) = 0 := by
        obtain ⟨g, hg⟩ := hfdvd
        rw [hg, map_mul, hroot, zero_mul]
      rw [map_sub, map_pow, Polynomial.aeval_X, sub_eq_zero] at hh
      exact hh
    have hxne1 : (AdjoinRoot.root f) ≠ 1 := by
      intro hx
      have h1 : (AdjoinRoot.mk f) (Polynomial.X - 1) = 0 := by
        rw [← AdjoinRoot.aeval_eq, hx]; simp
      exact hne ((AdjoinRoot.mk_eq_zero).mp h1)
    have hx0 : (AdjoinRoot.root f) ≠ 0 := by
      intro h0; rw [h0, zero_pow hℓ.pos.ne'] at hxe; exact one_ne_zero hxe.symm
    have hord : orderOf (AdjoinRoot.root f) = ℓ := by
      have hd : orderOf (AdjoinRoot.root f) ∣ ℓ := orderOf_dvd_of_pow_eq_one hxe
      rcases hℓ.eq_one_or_self_of_dvd (orderOf (AdjoinRoot.root f)) hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hxne1
      · exact h1
    have hpow : (AdjoinRoot.root f) ^ (Nat.card F ^ 2 - 1) = 1 := by
      have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow 2 _ Nat.card_pos
      have hchain : (AdjoinRoot.root f) ^ (Nat.card F ^ 2 - 1) * AdjoinRoot.root f
          = (1 : AdjoinRoot f) * AdjoinRoot.root f := by
        rw [← pow_succ, Nat.sub_add_cancel hq2, hxq, one_mul]
      exact mul_right_cancel₀ hx0 hchain
    have hdv : ℓ ∣ Nat.card F ^ 2 - 1 := by
      rw [← hord]; exact orderOf_dvd_of_pow_eq_one hpow
    have h2 : ℓ ∣ 2 := by
      have := Nat.dvd_sub hdvd hdv
      rwa [show Nat.card F ^ 2 + 1 - (Nat.card F ^ 2 - 1) = 2 by
        have h := Nat.one_le_pow 2 (Nat.card F) Nat.card_pos; omega] at this
    have : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2
    rw [this] at hodd
    exact absurd hodd (by decide)
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.dvd_prime_pow Nat.prime_two] at hdeg4
  obtain ⟨k, _hk2, hk⟩ := hdeg4
  interval_cases k
  · exact absurd (by rw [hk]; norm_num) hnot2
  · exact absurd (by rw [hk]; norm_num) hnot2
  · rw [hk]; norm_num

/-- `X - 1` does not divide the minimal polynomial of `A`, where `A` has odd prime order `ℓ`
with `ℓ ∣ |F|² + 1`.

Indeed, if `X - 1 ∣ m` then `m = (X - 1)·h` with `h ∣ Φ := ∑_{i<ℓ} X^i`, and `Φ` is coprime to
`X - 1` (as `Φ(1) = ℓ ≠ 0`).  Any irreducible factor `g` of `h` is then a factor of
`X ^ ℓ - 1` not dividing `X - 1`, so `deg g = 4`; but `g ∣ h` and `deg h ≤ deg m - 1 ≤ 3`, a
contradiction.  Hence `h` is a unit, `m = X - 1`, and then `A = 1`, contradicting `orderOf A = ℓ`. -/
theorem not_X_sub_one_dvd_minpoly {F : Type*} [Field F] [Finite F]
    (A : Matrix.GeneralLinearGroup (Fin 4) F) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hdvd : ℓ ∣ Nat.card F ^ 2 + 1) (hord : orderOf A = ℓ) :
    ¬ (Polynomial.X - 1 : Polynomial F) ∣ minpoly F (A : Matrix (Fin 4) (Fin 4) F) := by
  set m : Polynomial F := minpoly F (A : Matrix (Fin 4) (Fin 4) F) with hm
  have hA : A ^ ℓ = 1 := by rw [← hord]; exact pow_orderOf_eq_one A
  have hmm : m.Monic := by rw [hm]; exact minpoly.monic (Matrix.isIntegral _)
  have hm4 : m.natDegree ≤ 4 := by rw [hm]; exact minpoly_natDegree_le_four A
  have hmdvd : m ∣ (Polynomial.X : Polynomial F) ^ ℓ - 1 := by
    rw [hm]; exact minpoly_dvd_X_pow_sub_one A hA
  have hmne : m ≠ Polynomial.X - 1 := by
    intro hmeq
    have h1 : Polynomial.aeval (A : Matrix (Fin 4) (Fin 4) F) (Polynomial.X - 1 : Polynomial F) = 0 := by
      rw [← hmeq, hm]; exact minpoly.aeval F _
    rw [map_sub, Polynomial.aeval_X, map_one, sub_eq_zero] at h1
    have hA1 : A = 1 := by
      apply Units.ext
      simpa using h1
    rw [hA1] at hord
    simp only [orderOf_one] at hord
    have h2 := hℓ.two_le
    omega
  intro hd1
  have hℓne : (ℓ : F) ≠ 0 := natCast_ne_zero_of_prime_dvd_sq_add_one hℓ hdvd
  obtain ⟨h, hh⟩ := hd1
  have hmne0 : m ≠ 0 := hmm.ne_zero
  have hX1 : (Polynomial.X - 1 : Polynomial F) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hhne0 : h ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hh; exact hmne0 hh
  have hΦ : (Polynomial.X - 1 : Polynomial F) *
      (∑ i ∈ Finset.range ℓ, (Polynomial.X : Polynomial F) ^ i) =
      (Polynomial.X : Polynomial F) ^ ℓ - 1 := by
    simpa using mul_geom_sum (Polynomial.X : Polynomial F) ℓ
  have hhΦ : h ∣ ∑ i ∈ Finset.range ℓ, (Polynomial.X : Polynomial F) ^ i := by
    have h1 : (Polynomial.X - 1 : Polynomial F) * h ∣
        (Polynomial.X - 1 : Polynomial F) *
          (∑ i ∈ Finset.range ℓ, (Polynomial.X : Polynomial F) ^ i) := by
      rw [hΦ, ← hh]; exact hmdvd
    exact (mul_dvd_mul_iff_left hX1).mp h1
  by_cases hunit : IsUnit h
  · -- `h` is a unit: then `m = X - 1`, contradicting `hmne`
    have hhmonic : h.Monic :=
      Polynomial.Monic.of_mul_monic_left (p := Polynomial.X - (1 : Polynomial F)) (q := h)
        (Polynomial.monic_X_sub_C 1) (by rw [← hh]; exact hmm)
    have hdeg0 : h.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    have hcoeff : h.coeff 0 = 1 := by
      have hlead : h.leadingCoeff = 1 := hhmonic
      rw [Polynomial.leadingCoeff, hdeg0] at hlead
      exact hlead
    have hh1 : h = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, hcoeff, Polynomial.C_1]
    exact hmne (by rw [hh, hh1, mul_one])
  · -- `h` is a nonunit: it has an irreducible factor `g` of degree `4`, but `deg g ≤ deg h ≤ 3`
    obtain ⟨g, hgirr, hgdvd⟩ := WfDvdMonoid.exists_irreducible_factor hunit hhne0
    have hgdiv : g ∣ (Polynomial.X : Polynomial F) ^ ℓ - 1 := by
      rw [← hΦ]
      exact dvd_mul_of_dvd_right (dvd_trans hgdvd hhΦ) _
    have hgne : ¬ g ∣ Polynomial.X - 1 := by
      intro hg1
      have hassoc := hgirr.associated_of_dvd (Polynomial.irreducible_X_sub_C (1 : F)) hg1
      have hX1g : (Polynomial.X - 1 : Polynomial F) ∣ g := hassoc.symm.dvd
      have : (Polynomial.X - 1 : Polynomial F) ∣
          ∑ i ∈ Finset.range ℓ, (Polynomial.X : Polynomial F) ^ i :=
        dvd_trans hX1g (dvd_trans hgdvd hhΦ)
      exact X_sub_one_not_dvd_geom_sum hℓne this
    have hg4 : g.natDegree = 4 :=
      irreducible_factor_natDegree_eq_four hℓ hodd hdvd hgirr hgne hgdiv
    have hgle : g.natDegree ≤ h.natDegree := Polynomial.natDegree_le_of_dvd hgdvd hhne0
    have hhdeg : h.natDegree ≤ 3 := by
      have hX1deg : (Polynomial.X - 1 : Polynomial F).natDegree = 1 := by
        simpa using Polynomial.natDegree_X_sub_C (1 : F)
      have hmul : m.natDegree = (Polynomial.X - 1 : Polynomial F).natDegree + h.natDegree := by
        rw [hh, Polynomial.natDegree_mul hX1 hhne0]
      omega
    omega

/-- **Bender–Suzuki auxiliary fact.**  Let `F` be a finite field, `A ∈ GL₄(F)` an element of odd
prime order `ℓ`, with `ℓ ∣ |F|² + 1`.  Then the minimal polynomial of `A` is irreducible of
degree `4`.

Since `|F|² ≡ -1 (mod ℓ)`, every irreducible factor of `X ^ ℓ - 1` other than `X - 1` has degree
`4`; and a degree count shows that `X - 1` cannot divide the minimal polynomial.  Choosing an
irreducible factor `f` of the minimal polynomial gives `deg f = 4 = deg m`, hence `m = f`. -/
theorem minpoly_irreducible_of_prime_order_dvd_sq_add_one {F : Type*} [Field F] [Finite F]
    (A : Matrix.GeneralLinearGroup (Fin 4) F) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hord : orderOf A = ℓ) (hdvd : ℓ ∣ Nat.card F ^ 2 + 1) :
    Irreducible (minpoly F (A : Matrix (Fin 4) (Fin 4) F)) ∧
      (minpoly F (A : Matrix (Fin 4) (Fin 4) F)).natDegree = 4 := by
  set m : Polynomial F := minpoly F (A : Matrix (Fin 4) (Fin 4) F) with hm
  have hmm : m.Monic := by rw [hm]; exact minpoly.monic (Matrix.isIntegral _)
  have hmdegpos : 0 < m.natDegree := by
    rw [hm]; exact minpoly.natDegree_pos (Matrix.isIntegral _)
  have hmne0 : m ≠ 0 := hmm.ne_zero
  have hm_nonunit : ¬ IsUnit m := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have hm4 : m.natDegree ≤ 4 := by rw [hm]; exact minpoly_natDegree_le_four A
  have hA : A ^ ℓ = 1 := by rw [← hord]; exact pow_orderOf_eq_one A
  have hmdvd : m ∣ (Polynomial.X : Polynomial F) ^ ℓ - 1 := by
    rw [hm]; exact minpoly_dvd_X_pow_sub_one A hA
  have hnot1 : ¬ (Polynomial.X - 1 : Polynomial F) ∣ m := by
    rw [hm]; exact not_X_sub_one_dvd_minpoly A hℓ hodd hdvd hord
  obtain ⟨f, hfirr, hfdvd⟩ := WfDvdMonoid.exists_irreducible_factor hm_nonunit hmne0
  have hfdiv : f ∣ (Polynomial.X : Polynomial F) ^ ℓ - 1 := dvd_trans hfdvd hmdvd
  have hfne : ¬ f ∣ Polynomial.X - 1 := by
    intro hf1
    have hassoc := hfirr.associated_of_dvd (Polynomial.irreducible_X_sub_C (1 : F)) hf1
    exact hnot1 (dvd_trans hassoc.symm.dvd hfdvd)
  have hf4 : f.natDegree = 4 :=
    irreducible_factor_natDegree_eq_four hℓ hodd hdvd hfirr hfne hfdiv
  have hfdeg_le : f.natDegree ≤ m.natDegree := Polynomial.natDegree_le_of_dvd hfdvd hmne0
  have hmdeg : m.natDegree = 4 := le_antisymm hm4 (hf4 ▸ hfdeg_le)
  have hassocmf : Associated f m :=
    Polynomial.associated_of_dvd_of_natDegree_le hfdvd hmne0 (by omega)
  exact ⟨hassocmf.irreducible hfirr, hmdeg⟩

end Work.BSLit.BenderFacts2.MyAux
