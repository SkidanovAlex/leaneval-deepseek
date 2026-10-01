import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation_global_sharp_aux
import Submission.Commons.NumberTheory.DirichletCharacter.split_sum6
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_primeMod_good
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_primeSq

open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

/-! ### Elementary helpers for the six-shift cubic correlation -/

/-- Conjugating a character value with `starRingEnd` does not change its norm. -/
lemma cc6_norm_star_char {n : ℕ} (χ : DirichletCharacter ℂ n) (z : ZMod n) :
    ‖(starRingEnd ℂ) (χ z)‖ = ‖χ z‖ := Complex.norm_conj _

/-- The sixth entry of the six-tuple, when the index is `< 3`. -/
lemma cc6_vec_of_lt (a b : Fin 3 → ℕ) {i : Fin 6} (h : i.val < 3) :
    (![a 0, a 1, a 2, b 0, b 1, b 2] i : ℕ) = a ⟨i.val, h⟩ := by
  obtain ⟨iv, hiv⟩ := i
  simp only at h
  interval_cases iv <;> rfl

/-- The sixth entry of the six-tuple, when the index is `≥ 3`. -/
lemma cc6_vec_of_ge (a b : Fin 3 → ℕ) {i : Fin 6} (h : 3 ≤ i.val) (hlt : i.val - 3 < 3) :
    (![a 0, a 1, a 2, b 0, b 1, b 2] i : ℕ) = b ⟨i.val - 3, hlt⟩ := by
  obtain ⟨iv, hiv⟩ := i
  simp only at h
  interval_cases iv <;> rfl

/-- The index of `a l` inside the six-tuple. -/
def cc6_idxL (l : Fin 3) : Fin 6 := ⟨l.val, by omega⟩

/-- The index of `b l` inside the six-tuple. -/
def cc6_idxR (l : Fin 3) : Fin 6 := ⟨3 + l.val, by omega⟩

lemma cc6_vec_idxL (a b : Fin 3 → ℕ) (l : Fin 3) :
    (![a 0, a 1, a 2, b 0, b 1, b 2] (cc6_idxL l) : ℕ) = a l := by
  obtain ⟨lv, hlv⟩ := l
  simp only [cc6_idxL]
  interval_cases lv <;> rfl

lemma cc6_vec_idxR (a b : Fin 3 → ℕ) (l : Fin 3) :
    (![a 0, a 1, a 2, b 0, b 1, b 2] (cc6_idxR l) : ℕ) = b l := by
  obtain ⟨lv, hlv⟩ := l
  simp only [cc6_idxR]
  interval_cases lv <;> rfl

/-- If two naturals are congruent modulo `p`, then `p` divides the absolute value of their
difference (written as `natAbs` of the integer difference). -/
lemma cc6_dvd_natAbs_sub_of_zmod_eq {p x y : ℕ} (h : (x : ZMod p) = (y : ZMod p)) :
    p ∣ ((x : ℤ) - (y : ℤ)).natAbs := by
  have h0 : (((x : ℤ) - (y : ℤ) : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
  have h1 : (p : ℤ) ∣ ((x : ℤ) - (y : ℤ)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ((x : ℤ) - (y : ℤ)) p).mp h0
  have h2 : ((p : ℤ)).natAbs ∣ (((x : ℤ) - (y : ℤ))).natAbs := Int.natAbs_dvd_natAbs.mpr h1
  simpa using h2

/-- Expansion of a product of three linear factors as an explicit product. -/
lemma cc6_prod_fin3_eq {n : ℕ} (a : Fin 3 → ℕ) (x : ZMod n) :
    (∏ l : Fin 3, (x + (a l : ZMod n)))
      = (x + (a 0 : ZMod n)) * (x + (a 1 : ZMod n)) * (x + (a 2 : ZMod n)) :=
  Fin.prod_univ_three _

/-- The cubic correlation with the triple product written in expanded form. -/
lemma cc6_sum_eq_explicit {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a b : Fin 3 → ℕ) :
    (∑ x : ZMod n, χ (∏ l : Fin 3, (x + (a l : ZMod n))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod n)))))
      = ∑ x : ZMod n,
          χ ((x + (a 0 : ZMod n)) * (x + (a 1 : ZMod n)) * (x + (a 2 : ZMod n))) *
          (starRingEnd ℂ)
            (χ ((x + (b 0 : ZMod n)) * (x + (b 1 : ZMod n)) * (x + (b 2 : ZMod n)))) := by
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [cc6_prod_fin3_eq a x, cc6_prod_fin3_eq b x]

/-- Trivial bound: the cubic correlation is at most the number of terms. -/
lemma cc6_norm_le_card {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod n, χ (∏ l : Fin 3, (x + (a l : ZMod n))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod n))))‖ ≤ (n : ℝ) := by
  calc ‖∑ x : ZMod n, χ (∏ l : Fin 3, (x + (a l : ZMod n))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod n))))‖
      ≤ ∑ x : ZMod n, ‖χ (∏ l : Fin 3, (x + (a l : ZMod n))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod n))))‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ZMod n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_mul, cc6_norm_star_char χ]
        nlinarith [DirichletCharacter.norm_le_one χ (∏ l : Fin 3, (x + (a l : ZMod n))),
          DirichletCharacter.norm_le_one χ (∏ l : Fin 3, (x + (b l : ZMod n))),
          norm_nonneg (χ (∏ l : Fin 3, (x + (a l : ZMod n)))),
          norm_nonneg (χ (∏ l : Fin 3, (x + (b l : ZMod n))))]
    _ = (n : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card]
        simp

/-- The `gcd` factors in the correlation bound are at least `1`. -/
lemma cc6_one_le_gcd_cast {n x : ℕ} [NeZero n] : (1 : ℝ) ≤ ((Nat.gcd n x : ℕ) : ℝ) := by
  have hpos : 0 < Nat.gcd n x := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne n))
  have : (1 : ℕ) ≤ Nat.gcd n x := hpos
  exact_mod_cast this

/-- A sub-product of the `gcd` weight is at least `1`. -/
lemma cc6_one_le_gcd_prod {n : ℕ} [NeZero n] (a b : Fin 3 → ℕ) (i : Fin 6) (s : Finset (Fin 6)) :
    1 ≤ ∏ j ∈ s, (((Nat.gcd n (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) :=
  Finset.one_le_prod₀ (fun _ _ => cc6_one_le_gcd_cast)

/-- The `gcd` weight is nonnegative. -/
lemma cc6_gcd_prod_nonneg (n : ℕ) (a b : Fin 3 → ℕ) (i : Fin 6) (s : Finset (Fin 6)) :
    0 ≤ ∏ j ∈ s, (((Nat.gcd n (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) :=
  Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)

/-! ### The "bad" (degenerate) case at a prime modulus -/

/-- If the multiplicity functions of two triples `f`, `g` agree modulo `o ≥ 2`, and the value
`f l0` occurs only once among the `f l` and never among the `g l`, we reach a contradiction. -/
lemma cc6_bad_mult_contra {p o : ℕ} (ho : 2 ≤ o) (f g : Fin 3 → ℕ) (l0 : Fin 3)
    (hbad : ∀ x : ZMod p, (Finset.univ.filter (fun l : Fin 3 => (f l : ZMod p) = x)).card % o
        = (Finset.univ.filter (fun l : Fin 3 => (g l : ZMod p) = x)).card % o)
    (hf : ∀ l : Fin 3, l ≠ l0 → (f l : ZMod p) ≠ (f l0 : ZMod p))
    (hg : ∀ l : Fin 3, (g l : ZMod p) ≠ (f l0 : ZMod p)) : False := by
  classical
  have hcard_f :
      (Finset.univ.filter (fun l : Fin 3 => (f l : ZMod p) = (f l0 : ZMod p))).card = 1 := by
    apply le_antisymm
    · rw [Finset.card_le_one]
      intro l1 h1 l2 h2
      rw [Finset.mem_filter] at h1 h2
      by_cases hl1 : l1 = l0
      · by_cases hl2 : l2 = l0
        · rw [hl1, hl2]
        · exact absurd h2.2 (hf l2 hl2)
      · exact absurd h1.2 (hf l1 hl1)
    · exact Finset.card_pos.mpr ⟨l0, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩⟩
  have hcard_g :
      (Finset.univ.filter (fun l : Fin 3 => (g l : ZMod p) = (f l0 : ZMod p))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro l _ h
    exact hg l h
  have h := hbad (f l0 : ZMod p)
  rw [hcard_f, hcard_g] at h
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < o)] at h
  exact one_ne_zero h

/-- In the degenerate ("bad") case at a prime modulus, the unique value of the six-tuple is
congruent modulo `p` to another one. -/
lemma cc6_bad_dvd {p : ℕ} {o : ℕ} (ho : 2 ≤ o) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hbad : ∀ x : ZMod p, (Finset.univ.filter (fun l : Fin 3 => (a l : ZMod p) = x)).card % o
        = (Finset.univ.filter (fun l : Fin 3 => (b l : ZMod p) = x)).card % o) :
    ∃ j : Fin 6, j ≠ i ∧ p ∣ (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
        - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) := by
  classical
  by_contra hcon
  have hne : ∀ j : Fin 6, j ≠ i → (![a 0, a 1, a 2, b 0, b 1, b 2] j : ZMod p)
      ≠ (![a 0, a 1, a 2, b 0, b 1, b 2] i : ZMod p) := by
    intro j hj hjeq
    exact hcon ⟨j, hj, cc6_dvd_natAbs_sub_of_zmod_eq hjeq.symm⟩
  rcases lt_or_ge i.val 3 with hi3 | hi3
  · refine cc6_bad_mult_contra ho a b ⟨i.val, hi3⟩ hbad ?_ ?_
    · intro l hl heq
      have hj : cc6_idxL l ≠ i := by
        intro h
        apply hl
        have h1 : l.val = i.val := by simpa [cc6_idxL] using congrArg Fin.val h
        exact Fin.ext h1
      have hveq : (![a 0, a 1, a 2, b 0, b 1, b 2] (cc6_idxL l) : ZMod p)
          = (![a 0, a 1, a 2, b 0, b 1, b 2] i : ZMod p) := by
        rw [cc6_vec_idxL, cc6_vec_of_lt a b hi3]
        exact heq
      exact hne _ hj hveq
    · intro l heq
      have hj : cc6_idxR l ≠ i := by
        intro h
        have h1 : 3 + l.val = i.val := by simpa [cc6_idxR] using congrArg Fin.val h
        omega
      have hveq : (![a 0, a 1, a 2, b 0, b 1, b 2] (cc6_idxR l) : ZMod p)
          = (![a 0, a 1, a 2, b 0, b 1, b 2] i : ZMod p) := by
        rw [cc6_vec_idxR, cc6_vec_of_lt a b hi3]
        exact heq
      exact hne _ hj hveq
  · have hlt : i.val - 3 < 3 := by omega
    refine cc6_bad_mult_contra ho b a ⟨i.val - 3, hlt⟩ (fun x => (hbad x).symm) ?_ ?_
    · intro l hl heq
      have hj : cc6_idxR l ≠ i := by
        intro h
        apply hl
        have h1 : 3 + l.val = i.val := by simpa [cc6_idxR] using congrArg Fin.val h
        exact Fin.ext (by show l.val = i.val - 3; omega)
      have hveq : (![a 0, a 1, a 2, b 0, b 1, b 2] (cc6_idxR l) : ZMod p)
          = (![a 0, a 1, a 2, b 0, b 1, b 2] i : ZMod p) := by
        rw [cc6_vec_idxR, cc6_vec_of_ge a b hi3 hlt]
        exact heq
      exact hne _ hj hveq
    · intro l heq
      have hj : cc6_idxL l ≠ i := by
        intro h
        have h1 : l.val = i.val := by simpa [cc6_idxL] using congrArg Fin.val h
        omega
      have hveq : (![a 0, a 1, a 2, b 0, b 1, b 2] (cc6_idxL l) : ZMod p)
          = (![a 0, a 1, a 2, b 0, b 1, b 2] i : ZMod p) := by
        rw [cc6_vec_idxL, cc6_vec_of_ge a b hi3 hlt]
        exact heq
      exact hne _ hj hveq

/-! ### The global bound at a prime modulus -/

theorem charCorrelation6_prime_global {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (h1 : χ ≠ 1) (a b : Fin 3 → ℕ) (i : Fin 6) :
    ‖∑ x : ZMod p, χ (∏ l : Fin 3, (x + (a l : ZMod p))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod p))))‖
      ≤ (6 : ℝ) ^ (p.primeFactors.card) * Real.sqrt (p : ℝ) *
          ∏ j ∈ Finset.univ.erase i,
            (((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
               - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
  classical
  have hp : p.Prime := Fact.out
  have ho : 2 ≤ orderOf χ := by
    have h2 : orderOf χ ≠ 1 := fun h => h1 (orderOf_eq_one_iff.mp h)
    have h3 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  have hcard : p.primeFactors.card = 1 := by rw [hp.primeFactors]; simp
  by_cases hgood : ∃ x : ZMod p,
      (Finset.univ.filter (fun l : Fin 3 => (a l : ZMod p) = x)).card % orderOf χ
        ≠ (Finset.univ.filter (fun l : Fin 3 => (b l : ZMod p) = x)).card % orderOf χ
  · obtain ⟨x, hx⟩ := hgood
    have h := charCorrelation6_primeMod_good χ h1 (fun l => (a l : ZMod p))
      (fun l => (b l : ZMod p)) ⟨x, hx⟩
    rw [hcard, pow_one]
    refine h.trans ?_
    exact le_mul_of_one_le_right (by positivity)
      (cc6_one_le_gcd_prod a b i (Finset.univ.erase i))
  · simp only [not_exists, not_not] at hgood
    obtain ⟨j0, hj0ne, hj0dvd⟩ := cc6_bad_dvd ho a b i hgood
    rw [hcard, pow_one]
    have hmem : j0 ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj0ne, Finset.mem_univ j0⟩
    have hgcd : p ≤ Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
        - (![a 0, a 1, a 2, b 0, b 1, b 2] j0 : ℤ)).natAbs) :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hp.pos) (Nat.dvd_gcd dvd_rfl hj0dvd)
    have hgj : (p : ℝ) ≤ ((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
        - (![a 0, a 1, a 2, b 0, b 1, b 2] j0 : ℤ)).natAbs)) : ℕ) := by
      exact_mod_cast hgcd
    have hprod : (p : ℝ) ≤ ∏ j ∈ Finset.univ.erase i,
        (((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
          - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) :=
      calc (p : ℝ) ≤ ((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
              - (![a 0, a 1, a 2, b 0, b 1, b 2] j0 : ℤ)).natAbs)) : ℕ) := hgj
        _ ≤ ((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
              - (![a 0, a 1, a 2, b 0, b 1, b 2] j0 : ℤ)).natAbs)) : ℕ) *
            ∏ j ∈ (Finset.univ.erase i).erase j0,
              (((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
                - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) :=
            le_mul_of_one_le_right (by positivity)
              (cc6_one_le_gcd_prod a b i ((Finset.univ.erase i).erase j0))
        _ = ∏ j ∈ Finset.univ.erase i,
              (((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
                - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
            rw [Finset.mul_prod_erase (Finset.univ.erase i)
              (fun j => (((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
                - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ)) hmem]
    have h6 : (1 : ℝ) ≤ 6 * Real.sqrt (p : ℝ) := by
      have hp1 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hsp : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr (by linarith)
      nlinarith [Real.sqrt_nonneg (p : ℝ)]
    calc ‖∑ x : ZMod p, χ (∏ l : Fin 3, (x + (a l : ZMod p))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod p))))‖
        ≤ (p : ℝ) := cc6_norm_le_card χ a b
      _ ≤ ∏ j ∈ Finset.univ.erase i,
          (((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
            - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) := hprod
      _ ≤ (6 * Real.sqrt (p : ℝ)) * ∏ j ∈ Finset.univ.erase i,
          (((Nat.gcd p (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
            - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
          have hh := mul_le_mul_of_nonneg_right h6
            (cc6_gcd_prod_nonneg p a b i (Finset.univ.erase i))
          simpa using hh

/-- **Global cubic correlation bound for cube-free modulus, unique-value (singleton) case.**

For a cube-free modulus `q`, a primitive non-trivial character `χ` mod `q`, and a tuple of six
shifts `v = ![](a0,a1,a2,b0,b1,b2)` in which the value `v i` occurs exactly once,
`‖∑_{x : ZMod q} χ ((x+a0)(x+a1)(x+a2)) * conj (χ ((x+b0)(x+b1)(x+b2)))‖`
`≤ 6^{ω(q)} √q · ∏_{j ≠ i} gcd q |v_i - v_j|`.

This is the cubic analogue of the proven `charCorrelation_global_sharp_aux` (quadratic case).
Proof: strong induction on `q`, peeling off one prime at a time with `split_sum6` (valid for any
coprime factorisation) and `factorLeft`/`factorRight` (`primitive_factor_coprime`); at each prime
`p | q` one has `v_p(q) ∈ {1,2}`:

* `v_p(q) = 1`: apply `charCorrelation6_primeMod_good` when the pair is "good" (the multiplicity
  functions of the two triples of shifts are not congruent mod `orderOf χ_p`), and the trivial
  bound `p` otherwise.  In the bad case, the unique value `v i` has multiplicity `1` in one tuple
  and `0` in the other, which is never congruent mod `≥ 2`; hence *if* `v i` is unique modulo `p`
  the pair is good, and if some other shift is `≡ v i (mod p)` then
  `p ∣ ∏_{j ≠ i} gcd p |v_i - v_j|`.
* `v_p(q) = 2`: use `charCorrelation6_primeSq`
  (`NumberTheory/DirichletCharacter/charCorrelation6_primeSq`).

The `gcd` factors and the factor `√(p^e)` multiply over the prime factors, using
`Nat.Coprime.gcd_mul`-type identities, `ω(q) = ∑_{p | q} 1` and `√(uv) = √u·√v`. -/
theorem charCorrelation6_cubefree_global {q : ℕ} [NeZero q]
    (hcube : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1)
    (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → (![a 0, a 1, a 2, b 0, b 1, b 2] i)
        ≠ (![a 0, a 1, a 2, b 0, b 1, b 2] j)) :
    ‖∑ x : ZMod q, χ (∏ l : Fin 3, (x + (a l : ZMod q))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod q))))‖
      ≤ (6 : ℝ) ^ (q.primeFactors.card) * Real.sqrt (q : ℝ) *
          ∏ j ∈ Finset.univ.erase i,
            (((Nat.gcd q (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
               - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
  have key : ∀ (n : ℕ) [NeZero n], (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ n) →
      ∀ (χ : DirichletCharacter ℂ n), χ.IsPrimitive → χ ≠ 1 →
      ∀ (a b : Fin 3 → ℕ) (i : Fin 6),
        (∀ j : Fin 6, j ≠ i → (![a 0, a 1, a 2, b 0, b 1, b 2] i)
          ≠ (![a 0, a 1, a 2, b 0, b 1, b 2] j)) →
        ‖∑ x : ZMod n, χ (∏ l : Fin 3, (x + (a l : ZMod n))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod n))))‖
          ≤ (6 : ℝ) ^ (n.primeFactors.card) * Real.sqrt (n : ℝ) *
              ∏ j ∈ Finset.univ.erase i,
                (((Nat.gcd n (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
                  - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn0 hn χ hχ h1 a b i hi
      by_cases hpp : IsPrimePow n
      · obtain ⟨p, e, hp, he, hn_eq⟩ := (isPrimePow_nat_iff n).mp hpp
        haveI : Fact p.Prime := ⟨hp⟩
        have he3 : e ≤ 2 := by
          by_contra h
          rw [not_le] at h
          have hd : p ^ 3 ∣ p ^ e := pow_dvd_pow p (by omega)
          rw [hn_eq] at hd
          exact hn p hp hd
        rcases (by omega : e = 1 ∨ e = 2) with he1 | he2
        · rw [he1, pow_one] at hn_eq
          subst n
          exact charCorrelation6_prime_global χ h1 a b i
        · rw [he2] at hn_eq
          subst n
          rcases eq_or_ne p 2 with hp2 | hp2
          · have hpp2 : (p ^ 2).primeFactors.card = 1 := by
              rw [Nat.primeFactors_pow p (by norm_num : 2 ≠ 0), hp.primeFactors]
              simp
            have hsqrt : Real.sqrt (((p ^ 2 : ℕ)) : ℝ) = (p : ℝ) := by
              rw [Nat.cast_pow, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (p : ℝ))]
            have htriv : ‖∑ x : ZMod (p ^ 2), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ 2)))) *
                (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ 2)))))‖
                ≤ (p : ℝ) ^ 2 := by
              simpa only [Nat.cast_pow] using cc6_norm_le_card (n := p ^ 2) χ a b
            rw [hpp2, hsqrt, pow_one]
            refine htriv.trans ?_
            have h1p : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i,
                (((Nat.gcd (p ^ 2) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
                  - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) :=
              cc6_one_le_gcd_prod a b i _
            have hp2' : (p : ℝ) = 2 := by rw [hp2]; norm_num
            nlinarith [h1p]
          · have hpp2 : (p ^ 2).primeFactors.card = 1 := by
              rw [Nat.primeFactors_pow p (by norm_num : 2 ≠ 0), hp.primeFactors]
              simp
            have hsqrt : Real.sqrt (((p ^ 2 : ℕ)) : ℝ) = (p : ℝ) := by
              rw [Nat.cast_pow, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (p : ℝ))]
            rw [hpp2, hsqrt, pow_one]
            exact charCorrelation6_primeSq hp2 χ hχ h1 a b i
      · by_cases hn1 : n = 1
        · subst hn1
          refine (cc6_norm_le_card (n := 1) χ a b).trans (le_of_eq ?_)
          simp [Nat.primeFactors_one, Nat.gcd_one_left]
        · have hn2 : 2 ≤ n := by have h := NeZero.ne n; omega
          obtain ⟨u, v, hu1, hv1, huv, huv_eq⟩ := exists_coprime_factorization hn2 hpp
          subst n
          have huNZ : NeZero u := ⟨by omega⟩
          have hvNZ : NeZero v := ⟨by omega⟩
          have hu0 : u ≠ 0 := by omega
          have hv0 : v ≠ 0 := by omega
          have hu_lt : u < u * v := by nlinarith
          have hv_lt : v < u * v := by nlinarith
          have hcu : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u := fun p hp hd =>
            hn p hp (dvd_mul_of_dvd_left hd v)
          have hcv : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ v := fun p hp hd =>
            hn p hp (dvd_mul_of_dvd_right hd u)
          have hFLprim := factorLeft_isPrimitive huv χ hχ
          have hFRprim := factorRight_isPrimitive huv χ hχ
          have hFLne : factorLeft huv χ ≠ 1 := by
            intro h
            have hc : (factorLeft huv χ).conductor = 1 := by
              rw [h]; exact DirichletCharacter.conductor_one
            rw [DirichletCharacter.isPrimitive_def] at hFLprim
            omega
          have hFRne : factorRight huv χ ≠ 1 := by
            intro h
            have hc : (factorRight huv χ).conductor = 1 := by
              rw [h]; exact DirichletCharacter.conductor_one
            rw [DirichletCharacter.isPrimitive_def] at hFRprim
            omega
          have hIu := ih u hu_lt hcu (factorLeft huv χ) hFLprim hFLne a b i hi
          have hIv := ih v hv_lt hcv (factorRight huv χ) hFRprim hFRne a b i hi
          rw [cc6_sum_eq_explicit χ a b,
            split_sum6 huv χ (a 0) (a 1) (a 2) (b 0) (b 1) (b 2), norm_mul,
            ← cc6_sum_eq_explicit (factorLeft huv χ) a b,
            ← cc6_sum_eq_explicit (factorRight huv χ) a b]
          refine (mul_le_mul hIu hIv (norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
          have hprod : (∏ j ∈ Finset.univ.erase i,
                  (((Nat.gcd (u * v) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
                    - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ))
              = (∏ j ∈ Finset.univ.erase i,
                    (((Nat.gcd u (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
                      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ))
                * (∏ j ∈ Finset.univ.erase i,
                    (((Nat.gcd v (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
                      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ)) := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro j hj
            rw [gcd_mul_gcd_of_coprime huv]
            push_cast
            ring
          rw [hprod, card_primeFactors_mul_of_coprime hu0 hv0 huv, pow_add, Nat.cast_mul,
            Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (u : ℝ))]
          ring
  exact key q hcube χ hχ h1 a b i hi

end Commons.NumberTheory.DirichletCharacter
