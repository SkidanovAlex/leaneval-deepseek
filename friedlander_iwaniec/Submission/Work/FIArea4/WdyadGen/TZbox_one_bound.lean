import Mathlib
import Submission.Work.FIArea4.WdyadGenDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `s = 1` column bound for `TZbox`

We prove that the class sums `TZbox D (2D) β r 1` — the `s = 1` slice of the dual variance
matrix `Mentry` over the dyadic modulus range `(D, 2D]` — satisfy

  `Σ_{R < r ≤ 2R} ‖TZbox D (2D) β r 1‖² ≤ (R + D) · Σ_{D < d ≤ 2D} Σ_{a < d} ‖β a d‖²`.

The proof has two ingredients.

* For `s = 1` the congruence condition `s ≡ r a (mod d)` reads `r a ≡ 1 (mod d)`, so for each
  modulus `d ∈ (D,2D]` and each `r` there is at most one `a < d` contributing, namely the
  canonical representative of `r⁻¹ ∈ ZMod d` (and none when `(r,d) ≠ 1`).  Hence
  `Σ_{a<d} β a d · Mentry d a r 1` is a single term.
* Cauchy–Schwarz over the `D` moduli, followed by a counting bound: for each `d`, the number of
  `r ∈ (R,2R]` falling into a fixed residue class mod `d` is at most `R/d + 1`; equivalently the
  sum over `r` of a `d`-periodic nonnegative function is at most `(R/d+1)` times its period sum.
-/

namespace Work.FIArea4.WdyadGen

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-! ## The `Mentry` row sums at `s = 1` -/

/-- The Jacobi symbol has norm-square at most `1`, for any value of the upper argument. -/
lemma normSq_jacobiSym_le_one (r : ℕ) (M : ℕ) :
    Complex.normSq (((jacobiSym (r : ℤ) M : ℤ)) : ℂ) ≤ 1 := by
  rw [Complex.normSq_intCast]
  rcases jacobiSym.trichotomy (r : ℤ) M with h | h | h <;> rw [h] <;> norm_num

/-- Multiplying by a Jacobi symbol does not increase the norm-square. -/
lemma normSq_mul_jacobiSym_le (r M : ℕ) (x : ℂ) :
    Complex.normSq (x * ((jacobiSym (r : ℤ) M : ℤ) : ℂ)) ≤ Complex.normSq x := by
  rw [Complex.normSq_mul]
  calc Complex.normSq x * Complex.normSq (((jacobiSym (r : ℤ) M : ℤ)) : ℂ)
      ≤ Complex.normSq x * 1 :=
        mul_le_mul_of_nonneg_left (normSq_jacobiSym_le_one r M) (Complex.normSq_nonneg x)
    _ = Complex.normSq x := mul_one _

/-- For `s = 1` the sum over the residue classes `a < d` against `Mentry` collapses to the single
class `a ≡ r⁻¹ (mod d)` whenever `(r,d) = 1`, and vanishes otherwise. -/
lemma sum_row_Mentry_one (d : ℕ) (hd : 0 < d) (β : ℕ → ℕ → ℂ) (r : ℕ) :
    (∑ a ∈ Finset.range d, β a d * Mentry d a r 1)
      = if Nat.Coprime r d then
          β (((r : ZMod d)⁻¹).val) d * ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
        else 0 := by
  haveI : NeZero d := ⟨hd.ne'⟩
  by_cases hc : Nat.Coprime r d
  · rw [if_pos hc]
    have ha₀lt : (((r : ZMod d)⁻¹).val) < d := ZMod.val_lt _
    have hval : ((((r : ZMod d)⁻¹).val : ℕ) : ZMod d) = (r : ZMod d)⁻¹ := ZMod.natCast_zmod_val _
    have hmul : (r : ZMod d) * (((r : ZMod d)⁻¹).val : ZMod d) = 1 := by
      rw [hval]; exact ZMod.coe_mul_inv_eq_one r hc
    have huniq : ∀ a ∈ Finset.range d, (r : ZMod d) * (a : ZMod d) = 1 →
        a = ((r : ZMod d)⁻¹).val := by
      intro a ha h
      have h2 : (a : ZMod d) = (((r : ZMod d)⁻¹).val : ZMod d) := by
        calc (a : ZMod d) = (a : ZMod d) * ((r : ZMod d) * (((r : ZMod d)⁻¹).val : ZMod d)) := by
              rw [hmul, mul_one]
          _ = ((a : ZMod d) * (r : ZMod d)) * (((r : ZMod d)⁻¹).val : ZMod d) := by ring
          _ = (1 : ZMod d) * (((r : ZMod d)⁻¹).val : ZMod d) := by
              rw [mul_comm (a : ZMod d) (r : ZMod d), h]
          _ = (((r : ZMod d)⁻¹).val : ZMod d) := one_mul _
      have h3 : (a : ZMod d).val = ((((r : ZMod d)⁻¹).val : ℕ) : ZMod d).val := by rw [h2]
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha), ZMod.val_natCast_of_lt ha₀lt] at h3
      exact h3
    rw [Finset.sum_eq_single (((r : ZMod d)⁻¹).val)]
    · rw [Mentry, if_pos ⟨hc, by rw [Nat.cast_one]; exact hmul.symm⟩]
    · intro a ha hne
      have hcond : ¬(Nat.Coprime r d ∧ (((1 : ℕ) : ZMod d) = (r : ZMod d) * (a : ZMod d))) := by
        intro hcon
        rw [Nat.cast_one] at hcon
        exact hne (huniq a ha hcon.2.symm)
      rw [Mentry, if_neg hcond, mul_zero]
    · intro hnotmem
      exact absurd (Finset.mem_range.mpr ha₀lt) hnotmem
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro a ha
    have hcond : ¬(Nat.Coprime r d ∧ (((1 : ℕ) : ZMod d) = (r : ZMod d) * (a : ZMod d))) := by
      intro hcon; exact hc hcon.1
    rw [Mentry, if_neg hcond, mul_zero]

/-! ## Counting `d`-periodic functions on a dyadic interval -/

lemma periodic_add_mul (d : ℕ) (g : ℕ → ℝ) (hper : ∀ r, g (r + d) = g r) :
    ∀ k x : ℕ, g (x + k * d) = g x := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have h1 : x + (k + 1) * d = (x + k * d) + d := by ring
    rw [h1, hper, ih]

lemma periodic_mod_of_period (d : ℕ) (g : ℕ → ℝ) (hper : ∀ r, g (r + d) = g r) :
    ∀ r, g r = g (r % d) := by
  intro r
  have hr : r % d + (r / d) * d = r := by
    rw [Nat.mul_comm (r / d) d, Nat.add_comm]; exact Nat.div_add_mod r d
  simpa [hr] using periodic_add_mul d g hper (r / d) (r % d)

/-- The sum of a `d`-periodic function over one full period of `d` consecutive integers equals its
sum over `range d`. -/
lemma sum_Ioc_periodic_base (d : ℕ) (hd : 0 < d) (g : ℕ → ℝ) (hper : ∀ r, g (r + d) = g r)
    (R : ℕ) : ∑ r ∈ Finset.Ioc R (R + d), g r = ∑ c ∈ Finset.range d, g c := by
  have hkey : ∀ x y : ℕ, x ∈ Finset.Ioc R (R + d) → y ∈ Finset.Ioc R (R + d) → x ≤ y →
      x % d = y % d → x = y := by
    intro x y hx hy hle hxy
    simp only [Finset.mem_Ioc] at hx hy
    have hmodeq : x ≡ y [MOD d] := hxy
    have hdvd : d ∣ y - x := Nat.ModEq.dvd' hmodeq
    have hlt : y - x < d := by omega
    have h0 : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  have hinj : Set.InjOn (fun r => r % d) ↑(Finset.Ioc R (R + d)) := by
    intro x hx y hy hxy
    rcases le_total x y with hle | hle
    · exact hkey x y hx hy hle hxy
    · exact (hkey y x hy hx hle hxy.symm).symm
  have hsub : (Finset.Ioc R (R + d)).image (fun r => r % d) ⊆ Finset.range d := by
    intro c hc
    simp only [Finset.mem_image, Finset.mem_Ioc] at hc
    obtain ⟨r, _, rfl⟩ := hc
    exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
  have himg : (Finset.Ioc R (R + d)).image (fun r => r % d) = Finset.range d := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_range, Finset.card_image_of_injOn hinj, Nat.card_Ioc]
    omega
  rw [Finset.sum_congr rfl (fun r _ => periodic_mod_of_period d g hper r)]
  rw [← Finset.sum_image hinj, himg]

/-- The sum of a `d`-periodic function over `m` full periods is `m` times its period sum. -/
lemma sum_Ioc_periodic_mul (d : ℕ) (hd : 0 < d) (g : ℕ → ℝ) (hper : ∀ r, g (r + d) = g r)
    (R m : ℕ) : ∑ r ∈ Finset.Ioc R (R + m * d), g r = m * ∑ c ∈ Finset.range d, g c := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : Finset.Ioc R (R + (m + 1) * d) =
        Finset.Ioc R (R + m * d) ∪ Finset.Ioc (R + m * d) (R + (m + 1) * d) :=
      (Finset.Ioc_union_Ioc_eq_Ioc (Nat.le_add_right R (m * d))
        (Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.le_succ m)) R)).symm
    have hdisj : Disjoint (Finset.Ioc R (R + m * d))
        (Finset.Ioc (R + m * d) (R + (m + 1) * d)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_Ioc] at hx hy
      exact absurd hy.1 (not_lt.mpr hx.2)
    have hblock : ∑ r ∈ Finset.Ioc (R + m * d) (R + (m + 1) * d), g r
        = ∑ c ∈ Finset.range d, g c := by
      have hmd : (m + 1) * d = m * d + d := by ring
      have himg : Finset.Ioc (R + m * d) (R + (m + 1) * d)
          = (Finset.Ioc R (R + d)).image (fun j => j + m * d) := by
        ext x
        simp only [Finset.mem_Ioc, Finset.mem_image]
        constructor
        · intro hx
          obtain ⟨hx1, hx2⟩ := hx
          rw [hmd] at hx2
          have h5 : m * d ≤ x := by omega
          exact ⟨x - m * d, ⟨by omega, by omega⟩, by omega⟩
        · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
          rw [hmd]
          exact ⟨by omega, by omega⟩
      have hinj : Set.InjOn (fun j => j + m * d) ↑(Finset.Ioc R (R + d)) := by
        intro x _ y _ hxy; exact Nat.add_right_cancel hxy
      rw [himg, Finset.sum_image hinj]
      rw [Finset.sum_congr rfl (fun j _ => periodic_add_mul d g hper m j)]
      exact sum_Ioc_periodic_base d hd g hper R
    rw [hsplit, Finset.sum_union hdisj, ih, hblock, Nat.cast_add, Nat.cast_one]
    ring

/-- A `d`-periodic nonnegative function on `(R, 2R]` is bounded by `(R/d + 1)` times its period
sum. -/
lemma sum_Ioc_periodic_le (d : ℕ) (hd : 0 < d) (g : ℕ → ℝ)
    (hper : ∀ r, g (r + d) = g r) (h0 : ∀ r, 0 ≤ g r) (R : ℕ) :
    ∑ r ∈ Finset.Ioc R (2 * R), g r ≤ ((R : ℝ) / d + 1) * ∑ c ∈ Finset.range d, g c := by
  set M : ℕ := R / d + 1 with hM
  have hRd : R < M * d := by
    have h1 : d * (R / d) + R % d = R := Nat.div_add_mod R d
    have h2 : R % d < d := Nat.mod_lt R hd
    have h3 : R < d * (R / d) + d := by omega
    calc R < d * (R / d) + d := h3
      _ = (R / d) * d + d := by rw [Nat.mul_comm]
      _ = (R / d + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
      _ = M * d := by rw [hM]
  calc ∑ r ∈ Finset.Ioc R (2 * R), g r
      ≤ ∑ r ∈ Finset.Ioc R (R + M * d), g r := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Ioc_subset_Ioc_right (by omega)
        · intro x _ _; exact h0 x
      _ = M * ∑ c ∈ Finset.range d, g c := sum_Ioc_periodic_mul d hd g hper R M
      _ ≤ ((R : ℝ) / d + 1) * ∑ c ∈ Finset.range d, g c := by
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun c _ => h0 c))
        have h4 : ((M : ℕ) : ℝ) ≤ (R : ℝ) / d + 1 := by
          have := Nat.cast_div_le (α := ℝ) (m := R) (n := d)
          rw [hM]; push_cast; linarith
        exact h4

/-! ## The `r`-sum in terms of the canonical representatives of `r⁻¹` -/

/-- For a fixed `r`, the sum over `a < d` of `F a` against the congruence `r a ≡ 1 (mod d)`
collapses to the canonical representative of `r⁻¹` in `ZMod d`. -/
lemma sum_range_ite_inv (d : ℕ) (hd : 0 < d) (F : ℕ → ℝ) (r : ℕ) :
    (∑ a ∈ Finset.range d, (if Nat.Coprime r d ∧ (r : ZMod d) * (a : ZMod d) = 1 then F a else 0))
      = if Nat.Coprime r d then F (((r : ZMod d)⁻¹).val) else 0 := by
  haveI : NeZero d := ⟨hd.ne'⟩
  by_cases hc : Nat.Coprime r d
  · rw [if_pos hc]
    have ha₀lt : (((r : ZMod d)⁻¹).val) < d := ZMod.val_lt _
    have hmul : (r : ZMod d) * (((r : ZMod d)⁻¹).val : ZMod d) = 1 := by
      rw [ZMod.natCast_zmod_val]; exact ZMod.coe_mul_inv_eq_one r hc
    have huniq : ∀ a ∈ Finset.range d, (r : ZMod d) * (a : ZMod d) = 1 →
        a = ((r : ZMod d)⁻¹).val := by
      intro a ha h
      have h2 : (a : ZMod d) = (((r : ZMod d)⁻¹).val : ZMod d) := by
        calc (a : ZMod d) = (a : ZMod d) * ((r : ZMod d) * (((r : ZMod d)⁻¹).val : ZMod d)) := by
              rw [hmul, mul_one]
          _ = ((a : ZMod d) * (r : ZMod d)) * (((r : ZMod d)⁻¹).val : ZMod d) := by ring
          _ = (1 : ZMod d) * (((r : ZMod d)⁻¹).val : ZMod d) := by
              rw [mul_comm (a : ZMod d) (r : ZMod d), h]
          _ = (((r : ZMod d)⁻¹).val : ZMod d) := one_mul _
      have h3 : (a : ZMod d).val = ((((r : ZMod d)⁻¹).val : ℕ) : ZMod d).val := by rw [h2]
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha), ZMod.val_natCast_of_lt ha₀lt] at h3
      exact h3
    rw [Finset.sum_eq_single (((r : ZMod d)⁻¹).val)]
    · rw [if_pos ⟨hc, hmul⟩]
    · intro a ha hne
      have hcond : ¬(Nat.Coprime r d ∧ (r : ZMod d) * (a : ZMod d) = 1) := by
        intro hcon; exact hne (huniq a ha hcon.2)
      rw [if_neg hcond]
    · intro hnotmem; exact absurd (Finset.mem_range.mpr ha₀lt) hnotmem
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro a ha
    have hcond : ¬(Nat.Coprime r d ∧ (r : ZMod d) * (a : ZMod d) = 1) := by
      intro hcon; exact hc hcon.1
    rw [if_neg hcond]

/-- The dyadic `r`-sum of the inverse-residue weight: at most `(R/d + 1)` copies of the period
sum `Σ_{a<d} F a`, because for each fixed `a` the congruence `r a ≡ 1 (mod d)` has at most one
solution for `r` modulo `d`. -/
lemma sum_row_Ioc_le (d : ℕ) (hd : 0 < d) (R : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    ∑ r ∈ Finset.Ioc R (2 * R), (if Nat.Coprime r d then F (((r : ZMod d)⁻¹).val) else 0)
      ≤ ((R : ℝ) / d + 1) * ∑ a ∈ Finset.range d, F a := by
  set G : ℕ → ℝ := fun r =>
    ∑ a ∈ Finset.range d,
      (if Nat.Coprime r d ∧ (r : ZMod d) * (a : ZMod d) = 1 then F a else 0) with hG
  have hGg : ∀ r, G r = (if Nat.Coprime r d then F (((r : ZMod d)⁻¹).val) else 0) :=
    fun r => sum_range_ite_inv d hd F r
  have hper : ∀ r, G (r + d) = G r := by
    intro r
    simp only [hG]
    apply Finset.sum_congr rfl
    intro a _
    have hcast : (((r + d : ℕ)) : ZMod d) = (r : ZMod d) := by
      rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    have hcop : Nat.Coprime (r + d) d ↔ Nat.Coprime r d := by
      simpa using Nat.coprime_add_mul_left_left r d 1
    simp only [hcast, hcop]
  have h0 : ∀ r, 0 ≤ G r := by
    intro r
    simp only [hG]
    apply Finset.sum_nonneg
    intro a _
    by_cases h : Nat.Coprime r d ∧ (r : ZMod d) * (a : ZMod d) = 1
    · rw [if_pos h]; exact hF a
    · rw [if_neg h]
  have hb : (∑ c ∈ Finset.range d, G c) ≤ ∑ a ∈ Finset.range d, F a := by
    simp only [hG]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro a _
    have hcard : ((Finset.range d).filter
        (fun c => Nat.Coprime c d ∧ (c : ZMod d) * (a : ZMod d) = 1)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro c1 hc1 c2 hc2
      simp only [Finset.mem_filter] at hc1 hc2
      have h1 : (c1 : ZMod d) = (c2 : ZMod d) := by
        calc (c1 : ZMod d) = (c1 : ZMod d) * 1 := (mul_one _).symm
          _ = (c1 : ZMod d) * ((a : ZMod d) * (c2 : ZMod d)) := by
              rw [mul_comm (a : ZMod d) (c2 : ZMod d), hc2.2.2]
          _ = ((c1 : ZMod d) * (a : ZMod d)) * (c2 : ZMod d) := by ring
          _ = 1 * (c2 : ZMod d) := by rw [hc1.2.2]
          _ = (c2 : ZMod d) := one_mul _
      haveI : NeZero d := ⟨hd.ne'⟩
      have h3 := congrArg ZMod.val h1
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hc1.1),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hc2.1)] at h3
      exact h3
    calc ∑ c ∈ Finset.range d,
            (if Nat.Coprime c d ∧ (c : ZMod d) * (a : ZMod d) = 1 then F a else 0)
        = ((Finset.range d).filter
            (fun c => Nat.Coprime c d ∧ (c : ZMod d) * (a : ZMod d) = 1)).card * F a := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * F a := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hF a)
      _ = F a := one_mul _
  calc ∑ r ∈ Finset.Ioc R (2 * R), (if Nat.Coprime r d then F (((r : ZMod d)⁻¹).val) else 0)
      = ∑ r ∈ Finset.Ioc R (2 * R), G r := Finset.sum_congr rfl (fun r _ => (hGg r).symm)
    _ ≤ ((R : ℝ) / d + 1) * ∑ c ∈ Finset.range d, G c := sum_Ioc_periodic_le d hd G hper h0 R
    _ ≤ ((R : ℝ) / d + 1) * ∑ a ∈ Finset.range d, F a :=
        mul_le_mul_of_nonneg_left hb (by positivity)

/-! ## The bound -/

theorem TZbox_one_bound {D1 : ℕ} (hD1 : 1 ≤ D1) (R : ℕ) (β : ℕ → ℕ → ℂ) :
    ∑ r ∈ Finset.Ioc R (2 * R), Complex.normSq (Work.FIArea4.TZbox D1 (2 * D1) β r 1)
      ≤ ((R : ℝ) + (D1 : ℝ)) * (∑ d ∈ Finset.Ioc D1 (2 * D1), ∑ a ∈ Finset.range d, Complex.normSq (β a d)) := by
  have hD1pos : 0 < D1 := hD1
  set S : Finset ℕ := Finset.Ioc D1 (2 * D1) with hS
  have hScard : (S.card : ℝ) = (D1 : ℝ) := by
    rw [hS, Nat.card_Ioc]
    have h : 2 * D1 - D1 = D1 := by omega
    rw [h]
  have hrow : ∀ r, TZbox D1 (2 * D1) β r 1 =
      ∑ d ∈ S, (if Nat.Coprime r d then
          β (((r : ZMod d)⁻¹).val) d * ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
        else 0) := by
    intro r
    rw [hS]
    simp only [TZbox]
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < d := by have := (Finset.mem_Ioc.mp hd).1; omega
    exact sum_row_Mentry_one d hdpos β r
  -- Cauchy–Schwarz over the `D1` moduli, dropping the unimodular Jacobi symbol
  have hpoint : ∀ r, Complex.normSq (TZbox D1 (2 * D1) β r 1) ≤
      (D1 : ℝ) * ∑ d ∈ S,
        (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0) := by
    intro r
    rw [hrow r]
    set FF : ℕ → ℂ := fun d => (if Nat.Coprime r d then
        β (((r : ZMod d)⁻¹).val) d * ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
      else 0) with hFF
    have h1 : Complex.normSq (∑ d ∈ S, FF d) ≤ (S.card : ℝ) * ∑ d ∈ S, Complex.normSq (FF d) := by
      rw [Complex.normSq_eq_norm_sq]
      calc ‖∑ d ∈ S, FF d‖ ^ 2 ≤ (∑ d ∈ S, ‖FF d‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S FF) 2
        _ ≤ (S.card : ℝ) * ∑ d ∈ S, ‖FF d‖ ^ 2 := sq_sum_le_card_mul_sum_sq
        _ = (S.card : ℝ) * ∑ d ∈ S, Complex.normSq (FF d) := by
            congr 1
            apply Finset.sum_congr rfl
            intro d _
            rw [Complex.normSq_eq_norm_sq]
    have h2 : ∑ d ∈ S, Complex.normSq (FF d) ≤
        ∑ d ∈ S, (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hcd : Nat.Coprime r d
      · rw [hFF]
        simp only []
        rw [if_pos hcd, if_pos hcd]
        exact normSq_mul_jacobiSym_le r (Work.FIPlan.oddPart d) _
      · rw [hFF]
        simp only []
        rw [if_neg hcd, if_neg hcd]
        simp
    calc Complex.normSq (∑ d ∈ S, FF d) ≤ (S.card : ℝ) * ∑ d ∈ S, Complex.normSq (FF d) := h1
      _ ≤ (S.card : ℝ) * ∑ d ∈ S,
            (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (D1 : ℝ) * ∑ d ∈ S,
            (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0) := by
          rw [hScard]
  have hmain : ∑ r ∈ Finset.Ioc R (2 * R), Complex.normSq (TZbox D1 (2 * D1) β r 1)
      ≤ (D1 : ℝ) * ∑ d ∈ S, ∑ r ∈ Finset.Ioc R (2 * R),
          (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0) := by
    calc ∑ r ∈ Finset.Ioc R (2 * R), Complex.normSq (TZbox D1 (2 * D1) β r 1)
        ≤ ∑ r ∈ Finset.Ioc R (2 * R), (D1 : ℝ) * ∑ d ∈ S,
            (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0) :=
          Finset.sum_le_sum (fun r _ => hpoint r)
      _ = (D1 : ℝ) * ∑ r ∈ Finset.Ioc R (2 * R), ∑ d ∈ S,
            (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0) := by
          rw [Finset.mul_sum]
      _ = (D1 : ℝ) * ∑ d ∈ S, ∑ r ∈ Finset.Ioc R (2 * R),
            (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0) := by
          rw [Finset.sum_comm]
  refine hmain.trans ?_
  have hd_bound : ∀ d ∈ S, ∑ r ∈ Finset.Ioc R (2 * R),
        (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0)
      ≤ ((R : ℝ) / D1 + 1) * ∑ a ∈ Finset.range d, Complex.normSq (β a d) := by
    intro d hd
    have hdpos : 0 < d := by have := (Finset.mem_Ioc.mp hd).1; omega
    have hdle : D1 ≤ d := le_of_lt (Finset.mem_Ioc.mp hd).1
    have h1 := sum_row_Ioc_le d hdpos R (fun a => Complex.normSq (β a d))
      (fun a => Complex.normSq_nonneg _)
    refine h1.trans ?_
    have h2 : (R : ℝ) / d + 1 ≤ (R : ℝ) / D1 + 1 := by
      have h3 : (R : ℝ) / d ≤ (R : ℝ) / D1 :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg R) (by exact_mod_cast hD1pos)
          (by exact_mod_cast hdle)
      linarith
    exact mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hD1ne : (D1 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < D1 := by exact_mod_cast hD1pos
    positivity
  have harith : (D1 : ℝ) * ((R : ℝ) / D1 + 1) = (R : ℝ) + (D1 : ℝ) := by
    rw [mul_add, mul_one, mul_div_cancel₀ (R : ℝ) hD1ne]
  calc (D1 : ℝ) * ∑ d ∈ S, ∑ r ∈ Finset.Ioc R (2 * R),
        (if Nat.Coprime r d then Complex.normSq (β (((r : ZMod d)⁻¹).val) d) else 0)
      ≤ (D1 : ℝ) * ∑ d ∈ S,
          ((R : ℝ) / D1 + 1) * ∑ a ∈ Finset.range d, Complex.normSq (β a d) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hd_bound) (by positivity)
    _ = ((D1 : ℝ) * ((R : ℝ) / D1 + 1)) *
          ∑ d ∈ S, ∑ a ∈ Finset.range d, Complex.normSq (β a d) := by
        simp only [mul_assoc, Finset.mul_sum]
    _ = ((R : ℝ) + (D1 : ℝ)) * ∑ d ∈ S, ∑ a ∈ Finset.range d, Complex.normSq (β a d) := by
        rw [harith]
    _ = ((R : ℝ) + (D1 : ℝ)) *
          (∑ d ∈ Finset.Ioc D1 (2 * D1), ∑ a ∈ Finset.range d, Complex.normSq (β a d)) := by
        rw [hS]

end

end Work.FIArea4.WdyadGen
