import Mathlib
import Submission.Work.HP.Defs

/-!
# Auxiliary lemmas for `dvd_gcdMinors2_veronese`

The main statement compares `p^e ∣ gcdMinors2 (ν x) (ν y)` with `p^e ∣ gcdMinors2 x y`.
Everything reduces to the following elementary description of "`p^e` divides all `2×2`
minors": for a vector `u` with a coordinate not divisible by `p`,
`p^e ∣ gcdMinors2 u v` iff `v ≡ c·u (mod p^e)` for some integer `c`.

This file provides the tool lemmas:

* `monDi`, `monDij`: explicit monomial exponent vectors (`X_i^d`, `X_i^{d-1}X_j`);
* `gcdMinors2_dvd_iff`: `a ∣ gcdMinors2 u v ↔ ∀ i j, a ∣ (u_i v_j - u_j v_i)`;
* `veronese_modEq`: `v ≡ c·u (mod E)` implies `ν v ≡ c^d · ν u (mod E)`;
* coprimality/cancellation lemmas for `p` prime.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.NA

open Work.HP

/-- The exponent vector of the monomial `X_i ^ d`. -/
def monDi (d n : ℕ) (i : Fin (n + 1)) : Mon d n :=
  ⟨fun k => ⟨if k = i then d else 0, by split <;> omega⟩,
   by rw [Finset.sum_ite_eq' Finset.univ i (fun _ => d)]; simp⟩

/-- The exponent vector of the monomial `X_i ^{d-1} X_j` (with `1 ≤ d`). -/
def monDij (d n : ℕ) (hd : 1 ≤ d) (i j : Fin (n + 1)) : Mon d n :=
  ⟨fun k => ⟨(if k = i then d - 1 else 0) + (if k = j then 1 else 0),
      by split <;> split <;> omega⟩,
   by
     have h : (∑ k : Fin (n + 1),
         ((if k = i then d - 1 else 0) + (if k = j then 1 else 0) : ℕ)) = d := by
       rw [Finset.sum_add_distrib,
           Finset.sum_ite_eq' Finset.univ i (fun _ => d - 1),
           Finset.sum_ite_eq' Finset.univ j (fun _ => 1)]
       simp only [Finset.mem_univ, ite_true]
       omega
     exact h⟩

theorem veronese_monDi (d n : ℕ) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    veronese d n x (monDi d n i) = x i ^ d := by
  simp only [veronese, monDi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem veronese_monDij (d n : ℕ) (hd : 1 ≤ d) (x : Fin (n + 1) → ℤ) (i j : Fin (n + 1)) :
    veronese d n x (monDij d n hd i j) = x i ^ (d - 1) * x j := by
  simp only [veronese, monDij]
  rw [show (∏ k, x k ^ ((if k = i then d - 1 else 0) + (if k = j then 1 else 0)))
        = (∏ k, x k ^ (if k = i then d - 1 else 0))
            * (∏ k, x k ^ (if k = j then 1 else 0)) by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun k _ => pow_add _ _ _)]
  rw [Finset.prod_eq_single i (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ i) h),
      Finset.prod_eq_single j (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- `a` divides `gcdMinors2 u v` iff it divides every `2×2` minor. -/
theorem gcdMinors2_dvd_iff {ι : Type*} [Fintype ι] (a : ℤ) (u v : ι → ℤ) :
    a ∣ Work.HP.gcdMinors2 u v ↔ ∀ i j : ι, a ∣ (u i * v j - u j * v i) := by
  rw [Work.HP.gcdMinors2]
  constructor
  · intro h i j
    exact dvd_trans h (Finset.gcd_dvd (s := Finset.univ)
      (f := fun ij : ι × ι => u ij.1 * v ij.2 - u ij.2 * v ij.1) (Finset.mem_univ (i, j)))
  · intro h
    exact Finset.dvd_gcd (fun ij _ => h ij.1 ij.2)

/-- `E ∣ a - b` gives `a ≡ b mod E`. -/
theorem modEq_of_dvd_sub {E a b : ℤ} (h : E ∣ (a - b)) : a ≡ b [ZMOD E] :=
  Int.modEq_iff_dvd.mpr (by simpa using dvd_neg.mpr h)

/-- `v ≡ c·u (mod E)` implies `ν v ≡ c^d · ν u (mod E)`. -/
theorem veronese_modEq {d n : ℕ} {E c : ℤ} {u v : Fin (n + 1) → ℤ}
    (h : ∀ i, v i ≡ c * u i [ZMOD E]) (m : Mon d n) :
    veronese d n v m ≡ c ^ d * veronese d n u m [ZMOD E] := by
  rw [veronese, veronese]
  have h2 : (∏ i, (c * u i) ^ (m.1 i : ℕ)) = c ^ d * ∏ i, u i ^ (m.1 i : ℕ) := by
    rw [show (∏ i, (c * u i) ^ (m.1 i : ℕ))
          = (∏ i, c ^ (m.1 i : ℕ)) * (∏ i, u i ^ (m.1 i : ℕ)) by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => mul_pow _ _ _)]
    rw [Finset.prod_pow_eq_pow_sum, m.2]
  rw [← h2]
  exact Int.ModEq.prod (fun i _ => Int.ModEq.pow _ (h i))

theorem isCoprime_pow_of_not_dvd {P a : ℤ} (hp : Prime P) (h : ¬ P ∣ a) (e : ℕ) :
    IsCoprime a (P ^ e) :=
  ((hp.coprime_iff_not_dvd.mpr h).symm).pow_right

/-- Cancellation: if `p` is prime, `p ∤ a` and `p^e ∣ a*b` then `p^e ∣ b`. -/
theorem dvd_of_dvd_mul_of_not_dvd_pow {P a b : ℤ} (hp : Prime P) {e : ℕ}
    (ha : ¬ P ∣ a) (h : P ^ e ∣ a * b) : P ^ e ∣ b := by
  have hc : IsCoprime (P ^ e) a := (((hp.coprime_iff_not_dvd.mpr ha).symm).pow_right).symm
  exact hc.dvd_of_dvd_mul_left h

/-- **Extraction of the proportionality constant mod `E` for the Veronese pair.**

If all `2×2` minors of `(νu, νv)` vanish mod `E` and some component `νu m₀` is coprime to `E`,
then `νv ≡ c · νu (mod E)` for a single integer `c`. -/
theorem exists_mu_of_veronese {d n : ℕ} {E : ℤ} (u v : Fin (n + 1) → ℤ) (m0 : Mon d n)
    (hrel : ∀ m m', E ∣ (veronese d n u m * veronese d n v m'
        - veronese d n u m' * veronese d n v m))
    (hU : IsCoprime (veronese d n u m0) E) :
    ∃ c : ℤ, ∀ m, E ∣ (veronese d n v m - c * veronese d n u m) := by
  obtain ⟨x, y, hxy⟩ := hU
  refine ⟨veronese d n v m0 * x, fun m => ?_⟩
  have hx : E ∣ x * veronese d n u m0 - 1 := by
    have h : x * veronese d n u m0 - 1 = (-y) * E := by linarith [hxy]
    rw [h]; exact dvd_mul_left _ _
  have h1 : E ∣ x * (veronese d n u m0 * veronese d n v m
      - veronese d n u m * veronese d n v m0) :=
    dvd_mul_of_dvd_right (by simpa using dvd_neg.mpr (hrel m m0)) x
  have h2 : E ∣ (x * veronese d n u m0 - 1) * veronese d n v m :=
    dvd_mul_of_dvd_left hx _
  have key : veronese d n v m - (veronese d n v m0 * x) * veronese d n u m
      = x * (veronese d n u m0 * veronese d n v m - veronese d n u m * veronese d n v m0)
        - (x * veronese d n u m0 - 1) * veronese d n v m := by ring
  rw [key]
  exact dvd_sub h1 h2

/-- **Direction `⟸` of the main theorem at the level of the two vectors.**

If `v ≡ c·u (mod E)` then `E` divides every `2×2` minor of `(νu, νv)`. -/
theorem dvd_gcdMinors2_veronese_of_modEq {d n : ℕ} {E c : ℤ} {u v : Fin (n + 1) → ℤ}
    (h : ∀ i, E ∣ (v i - c * u i)) :
    E ∣ Work.HP.gcdMinors2 (veronese d n u) (veronese d n v) := by
  rw [gcdMinors2_dvd_iff]
  intro m m'
  have hmod : ∀ i, v i ≡ c * u i [ZMOD E] := fun i => modEq_of_dvd_sub (h i)
  have hu := veronese_modEq (d := d) (n := n) (E := E) (c := c) (u := u) (v := v) hmod m
  have hv := veronese_modEq (d := d) (n := n) (E := E) (c := c) (u := u) (v := v) hmod m'
  have A : E ∣ (c ^ d * veronese d n u m - veronese d n v m) := Int.ModEq.dvd hu
  have B : E ∣ (c ^ d * veronese d n u m' - veronese d n v m') := Int.ModEq.dvd hv
  have key : veronese d n u m * veronese d n v m' - veronese d n u m' * veronese d n v m
      = -(veronese d n u m * (c ^ d * veronese d n u m' - veronese d n v m'))
        + veronese d n u m' * (c ^ d * veronese d n u m - veronese d n v m) := by ring
  rw [key]
  exact dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_right B _)) (dvd_mul_of_dvd_right A _)

end Work.HP.NA
