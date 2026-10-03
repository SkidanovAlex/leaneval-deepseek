import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea4.exists_unit_jacobi_neg_one
import Submission.Work.FIArea4.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

set_option linter.style.haveILetI false

noncomputable section

/-! ## The integer-valued Jacobi-symbol sum -/

/-- The integer-valued Jacobi-symbol sum `Σ_{r < m} (r | m)`. -/
def Sint (m : ℕ) : ℤ := ∑ r ∈ Finset.range m, jacobiSym (r : ℤ) m

lemma Sint_eq_real (m : ℕ) :
    (Sint m : ℝ) = ∑ r ∈ Finset.range m, (jacobiSym (r : ℤ) m : ℝ) := by
  rw [Sint, Int.cast_sum]

/-- `J((a % m) | m) = J(a | m)` (the numerator is reduced modulo the denominator). -/
lemma jacobiSym_mod_natCast (a m : ℕ) :
    jacobiSym (((a % m : ℕ)) : ℤ) m = jacobiSym (a : ℤ) m := by
  rw [Int.natCast_emod, ← jacobiSym.mod_left]

/-! ## Two Finset counting lemmas -/

/-- **Periodic sums.**  If `f` has period `m`, the sum of `f` over `k` full periods
`0, …, k*m-1` is `k` times the sum over one period. -/
lemma sum_range_mul_of_periodic {R : Type*} [Semiring R] {m : ℕ} (f : ℕ → R)
    (hper : ∀ y, f (y + m) = f y) (k : ℕ) :
    ∑ y ∈ Finset.range (k * m), f y = (k : R) * ∑ r ∈ Finset.range m, f r := by
  have hstep : ∀ k y, f (k * m + y) = f y := by
    intro k
    induction k with
    | zero => intro y; rw [Nat.zero_mul, Nat.zero_add]
    | succ k ih =>
      intro y
      rw [show (k + 1) * m + y = (k * m + y) + m by ring, hper, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * m = k * m + m by ring, Finset.sum_range_add, ih]
    have hS : ∑ x ∈ Finset.range m, f (k * m + x) = ∑ r ∈ Finset.range m, f r :=
      Finset.sum_congr rfl (fun x _ => hstep k x)
    rw [hS, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- **The affine map `r ↦ (c*r+b) % m` permutes `0, …, m-1`** when `c` is coprime to `m`;
hence it may be substituted in a sum over `Finset.range m`. -/
lemma sum_range_mod_perm {R : Type*} [AddCommMonoid R] {m c b : ℕ} (hm : 0 < m)
    (hc : Nat.Coprime c m) (g : ℕ → R) :
    ∑ r ∈ Finset.range m, g ((c * r + b) % m) = ∑ r ∈ Finset.range m, g r := by
  have hmem : ∀ r ∈ Finset.range m, (c * r + b) % m ∈ Finset.range m := by
    intro r hr
    rw [Finset.mem_range] at hr ⊢
    exact Nat.mod_lt _ hm
  have hinj : Set.InjOn (fun r => (c * r + b) % m) (Finset.range m) := by
    intro r₁ h₁ r₂ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at h₁ h₂
    have heq' : (c * r₁ + b) % m = (c * r₂ + b) % m := heq
    have hcast : ((c * r₁ + b : ℕ) : ZMod m) = ((c * r₂ + b : ℕ) : ZMod m) := by
      rw [← ZMod.natCast_mod (c * r₁ + b) m, ← ZMod.natCast_mod (c * r₂ + b) m, heq']
    simp only [Nat.cast_add, Nat.cast_mul] at hcast
    have hcancel : (c : ZMod m) * (r₁ : ZMod m) = (c : ZMod m) * (r₂ : ZMod m) :=
      add_right_cancel hcast
    have hu : IsUnit ((c : ℕ) : ZMod m) := (ZMod.isUnit_iff_coprime c m).mpr hc
    have hr : ((r₁ : ℕ) : ZMod m) = ((r₂ : ℕ) : ZMod m) := hu.mul_left_cancel hcancel
    have hval := congrArg ZMod.val hr
    rw [ZMod.val_natCast, ZMod.val_natCast] at hval
    have h₁' : r₁ % m = r₁ := Nat.mod_eq_of_lt h₁
    have h₂' : r₂ % m = r₂ := Nat.mod_eq_of_lt h₂
    omega
  have himg : Finset.image (fun r => (c * r + b) % m) (Finset.range m) = Finset.range m := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · rw [Finset.image_subset_iff]
      exact hmem
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← Finset.sum_image hinj, himg]

/-- **Odd indices.**  In a sum over `0, …, 2N-1` a term supported on the odd indices may be
reindexed by `x = 2y+1`, `y < N`. -/
lemma sum_range_two_mul_odd {R : Type*} [AddCommMonoid R] (g : ℕ → R) (N : ℕ) :
    ∑ x ∈ Finset.range (2 * N), (if x % 2 = 1 then g x else 0)
      = ∑ y ∈ Finset.range N, g (2 * y + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 2 by ring, Finset.sum_range_add, ih]
    have h2 : (∑ i ∈ Finset.range 2, (if (2 * N + i) % 2 = 1 then g (2 * N + i) else 0))
        = g (2 * N + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have h0 : (2 * N + 0) % 2 ≠ 1 := by omega
      have h1 : (2 * N + 1) % 2 = 1 := by omega
      rw [if_neg h0, if_pos h1, zero_add]
    rw [h2, Finset.sum_range_succ]

/-! ## The sum over the odd part vanishes when it is not a square -/

/-- **Odd case.**  If `m ≥ 1` is odd and not a perfect square then `Σ_{r<m} (r|m) = 0`:
a unit `x` with `(x|m) = -1` permutes `0, …, m-1` multiplicatively, forcing the sum to be
its own negative. -/
lemma Sint_eq_zero_of_odd_not_sq (m : ℕ) (hm : 1 ≤ m) (hodd : Odd m)
    (hnsq : ∀ k : ℕ, m ≠ k ^ 2) : Sint m = 0 := by
  obtain ⟨x, hx8, hcop, hJmx⟩ := Work.FIArea4.exists_odd_jacobi_neg_one m hm hodd hnsq
  have hxodd : Odd x := by
    rw [Nat.odd_iff]
    have h := Nat.mod_lt x (by norm_num : 0 < 8)
    omega
  have hxe : Even (x / 2) := by
    have hx : x = 8 * (x / 8) + 1 := by
      have := Nat.div_add_mod x 8
      omega
    rw [hx, show (8 * (x / 8) + 1) / 2 = 4 * (x / 8) by omega]
    exact ⟨2 * (x / 8), by ring⟩
  have hJxm : jacobiSym (x : ℤ) m = -1 := by
    have hrec := jacobiSym.quadratic_reciprocity hodd hxodd
    have h1 : (-1 : ℤ) ^ (m / 2 * (x / 2)) = 1 := by
      apply Even.neg_one_pow
      obtain ⟨t, ht⟩ := hxe
      exact ⟨m / 2 * t, by rw [ht]; ring⟩
    rw [hJmx, h1, one_mul] at hrec
    exact hrec.symm
  have hperm := sum_range_mod_perm (R := ℤ) (b := 0) (by omega : 0 < m) hcop
    (fun r => jacobiSym (r : ℤ) m)
  have hA : Sint m = ∑ r ∈ Finset.range m, jacobiSym (((x * r : ℕ)) : ℤ) m := by
    rw [Sint, ← hperm]
    exact Finset.sum_congr rfl (fun r _ => by
      rw [Nat.add_zero]
      exact jacobiSym_mod_natCast (x * r) m)
  have hB : (∑ r ∈ Finset.range m, jacobiSym (((x * r : ℕ)) : ℤ) m) = - Sint m := by
    have hsub : ∀ r : ℕ, jacobiSym (((x * r : ℕ)) : ℤ) m
        = jacobiSym (x : ℤ) m * jacobiSym ((r : ℕ) : ℤ) m := by
      intro r
      rw [Nat.cast_mul, jacobiSym.mul_left]
    rw [Finset.sum_congr rfl (fun r _ => hsub r), ← Finset.mul_sum]
    change jacobiSym (x : ℤ) m * Sint m = - Sint m
    rw [hJxm]
    ring
  linarith [hA.trans hB]

/-! ## The two-adic reduction -/

/-- **Reduction to the odd part.**  For odd `m` and `ν ≥ 1`,
`Σ_{x < 2^ν m} (x | 2^ν m) = 2^{ν-1} Σ_{r<m} (r|m)`. -/
lemma Sint_two_pow_mul_odd (ν m : ℕ) (hm : 0 < m) (hodd : Odd m) (hν : 1 ≤ ν) :
    Sint (2 ^ ν * m) = ((2 ^ (ν - 1) : ℕ) : ℤ) * Sint m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero (2 ^ ν) := ⟨pow_ne_zero ν (by norm_num)⟩
  have hpt : ∀ x : ℕ, jacobiSym (x : ℤ) (2 ^ ν * m)
      = if x % 2 = 1 then jacobiSym (x : ℤ) m else 0 := by
    intro x
    rw [jacobiSym.mul_right]
    by_cases hx : x % 2 = 1
    · rw [if_pos hx,
        Work.FIArea4.jacobiSym_two_pow_eq_one_of_odd (e := ν) (Nat.odd_iff.mpr hx), one_mul]
    · rw [if_neg hx]
      have hx0 : x % 2 = 0 := by omega
      have hJ2 : jacobiSym (x : ℤ) 2 = 0 := by
        rw [← jacobiSym.legendreSym.to_jacobiSym 2 (x : ℤ)]
        show quadraticChar (ZMod 2) ((x : ℤ) : ZMod 2) = 0
        have hx2 : ((x : ℤ) : ZMod 2) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hx0)
        rw [hx2, quadraticChar_zero]
      rw [jacobiSym.pow_right, hJ2, zero_pow (by omega : ν ≠ 0), zero_mul]
  have h1 : Sint (2 ^ ν * m) = ∑ x ∈ Finset.range (2 ^ ν * m),
      (if x % 2 = 1 then jacobiSym (x : ℤ) m else 0) := by
    rw [Sint]
    exact Finset.sum_congr rfl (fun x _ => hpt x)
  have hdm : 2 ^ ν * m = 2 * (2 ^ (ν - 1) * m) := by
    have hp : (2 : ℕ) ^ ν = 2 * 2 ^ (ν - 1) := by
      have hν1 : ν = (ν - 1) + 1 := by omega
      nth_rewrite 1 [hν1]
      rw [pow_succ']
    rw [hp]; ring
  have h2 : ∑ x ∈ Finset.range (2 ^ ν * m),
      (if x % 2 = 1 then jacobiSym (x : ℤ) m else 0)
      = ∑ y ∈ Finset.range (2 ^ (ν - 1) * m), jacobiSym (((2 * y + 1 : ℕ)) : ℤ) m := by
    rw [hdm]
    exact sum_range_two_mul_odd (fun x => jacobiSym (x : ℤ) m) (2 ^ (ν - 1) * m)
  have hper : ∀ y, jacobiSym (((2 * (y + m) + 1 : ℕ)) : ℤ) m
      = jacobiSym (((2 * y + 1 : ℕ)) : ℤ) m := by
    intro y
    refine jacobiSym.mod_left' ?_
    have hcast : (((2 * (y + m) + 1 : ℕ)) : ℤ) = (((2 * y + 1 : ℕ)) : ℤ) + (m : ℤ) * 2 := by
      push_cast; ring
    rw [hcast, Int.add_mul_emod_self_left]
  have h3 : ∑ y ∈ Finset.range (2 ^ (ν - 1) * m), jacobiSym (((2 * y + 1 : ℕ)) : ℤ) m
      = ((2 ^ (ν - 1) : ℕ) : ℤ)
          * ∑ r ∈ Finset.range m, jacobiSym (((2 * r + 1 : ℕ)) : ℤ) m :=
    sum_range_mul_of_periodic (fun y => jacobiSym (((2 * y + 1 : ℕ)) : ℤ) m) hper (2 ^ (ν - 1))
  have h4 : ∑ r ∈ Finset.range m, jacobiSym (((2 * r + 1 : ℕ)) : ℤ) m = Sint m := by
    rw [Sint]
    have hperm := sum_range_mod_perm (R := ℤ) (b := 1) hm (Nat.coprime_two_left.mpr hodd)
      (fun r => jacobiSym (r : ℤ) m)
    rw [← hperm]
    exact Finset.sum_congr rfl (fun r _ => (jacobiSym_mod_natCast (2 * r + 1) m).symm)
  rw [h1, h2, h3, h4]

/-! ## The vanishing half of *FI* Lemma 21.1 -/

/-- **The vanishing half of the Jacobi-symbol sum of *FI* Lemma 21.1.**

For `d ≥ 1` whose odd part is *not* a perfect square,

  `Σ_{x = 0}^{d−1} (x | d) = 0`

(with Mathlib's `jacobiSym`, i.e. the paper's (8.15) convention).  Together with
`Work.FIArea7.sum_jacobiSym_eq_totient_of_oddPart_sq` this is the dichotomy used in Lemma 21.1
(*"unless `d` and `q/d` are squares in which case the sum equals `qφ(d)φ(q/d)`"*, and `0`
otherwise), which is what makes the orthogonality relation of the Dirichlet symbols of §21 vanish,
and it is also the hypothesis shape of `Work.FIArea4.polya_vinogradov` (where it says that
`n ↦ jacobiSym n b` is not the principal character). -/
theorem sum_jacobiSym_eq_zero_of_oddPart_not_sq (d : ℕ) (hd : 0 < d)
    (hsq : ∀ k : ℕ, Work.FIPlan.oddPart d ≠ k ^ 2) :
    ∑ x ∈ Finset.range d, (jacobiSym (x : ℤ) d : ℝ) = 0 := by
  have hd0 : d ≠ 0 := hd.ne'
  set m := Work.FIPlan.oddPart d with hm
  set ν := d.factorization 2 with hν
  have hdm : 2 ^ ν * m = d := by
    rw [hν, hm]; exact Work.FIArea4.oddPart_mul_two_pow d
  have hmpos : 0 < m := by rw [hm]; exact Work.FIArea4.oddPart_pos hd0
  have hmodd : Odd m := by rw [hm]; exact Work.FIArea4.oddPart_odd hd0
  have hnsq : ∀ k : ℕ, m ≠ k ^ 2 := fun k => by rw [hm]; exact hsq k
  have hSint : Sint m = 0 := Sint_eq_zero_of_odd_not_sq m (by omega) hmodd hnsq
  have hSintd : Sint d = 0 := by
    rcases Nat.eq_zero_or_pos ν with hν0 | hνpos
    · have hdmeq : d = m := by rw [← hdm, hν0, pow_zero, one_mul]
      rw [hdmeq, hSint]
    · rw [← hdm, Sint_two_pow_mul_odd ν m hmpos hmodd hνpos, hSint, mul_zero]
  have h := Sint_eq_real d
  rw [hSintd] at h
  simpa using h.symm

end

end Work.FIArea7
