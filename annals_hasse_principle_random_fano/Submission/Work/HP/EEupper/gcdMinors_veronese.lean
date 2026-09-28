import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.NA.exists_lam_gcdMinors2
import Submission.Work.HP.GM.nat_eq_of_forall_prime_pow_dvd_iff
import Submission.Work.HP.GM.exists_not_dvd_mul_of_dvd_gcdMinors2_veronese

/-!
# Lemma G of Browning--Le Boudec--Sawin: the gcd of the `2 × 2` minors commutes with the Veronese map

For primitive integer vectors `x, y : ℤ^{n+1}` and `1 ≤ d`, the gcd of the `2 × 2` minors of the pair
`(ν_{d,n}(x), ν_{d,n}(y))` of Veronese vectors equals the gcd of the `2 × 2` minors of `(x, y)`.

Reduction (as in the paper, and in `Submission/Work/HP/EE/gcdMinors_veronese`): for every prime `p`
and exponent `e`, `p^e` divides one gcd iff it divides the other; equality then follows from
`Work.HP.GM.nat_eq_of_forall_prime_pow_dvd_iff`.

* `p^e ∣ gcdMinors2 x y → p^e ∣ gcdMinors2 (νx) (νy)`: `Work.HP.NA.exists_lam_gcdMinors2` gives
  `c` with `y ≡ c · x (mod p^e)`; homogeneity of the Veronese map (`Work.HP.NA.veronese_modEq`)
  gives `ν y ≡ c^d · ν x (mod p^e)`, so every minor of the Veronese pair vanishes.
* the converse: if `p^e ∣ gcdMinors2 (νx) (νy)`, the same tool applied to the *Veronese* vectors
  (which are primitive at `p` because `x` is) yields `c` with `ν y ≡ c · ν x (mod p^e)`; the two
  probes `ν x (monDi i) = x i^d` and `ν x (monDij i j) = x i^{d-1} x j` then force
  `p^e ∣ x i0 · y j - x j · y i0` for every `j` (where `p ∤ x i0`), hence `p^e ∣ gcdMinors2 x y`.
-/

namespace Work.HP.EEupper

open Finset

/-- `Work.HP.gcdMinors2` is a normalized (hence nonnegative) gcd. -/
lemma gcdMinors2_nonneg {ι : Type*} [Fintype ι] (x y : ι → ℤ) : 0 ≤ Work.HP.gcdMinors2 x y := by
  have h := Finset.normalize_gcd (s := Finset.univ)
    (f := fun ij : ι × ι => x ij.1 * y ij.2 - x ij.2 * y ij.1)
  rw [← Int.abs_eq_normalize] at h
  exact abs_eq_self.mp h

/-- If `p^e` divides the gcd of the `2 × 2` minors of `(x, y)` and `x` is primitive at `p`, then
`p^e` divides the gcd of the `2 × 2` minors of the Veronese vectors `ν x, ν y`. -/
theorem dvd_gcdMinors2_veronese_of_dvd (d n : ℕ) (p : ℕ) (hp : p.Prime)
    (x y : Fin (n + 1) → ℤ) (hx : ∃ i, ¬ (p : ℤ) ∣ x i) (e : ℕ) :
    (p : ℤ) ^ e ∣ Work.HP.gcdMinors2 x y →
      (p : ℤ) ^ e ∣ Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) := by
  intro hg
  obtain ⟨c, hc⟩ := Work.HP.NA.exists_lam_gcdMinors2 hp x y hx hg
  refine (Work.HP.NA.gcdMinors2_dvd_iff ((p : ℤ) ^ e) (Work.HP.veronese d n x)
    (Work.HP.veronese d n y)).mpr (fun m m' => ?_)
  have hm : Work.HP.veronese d n y m ≡ c ^ d * Work.HP.veronese d n x m [ZMOD (p : ℤ) ^ e] :=
    Work.HP.NA.veronese_modEq (E := (p : ℤ) ^ e) (c := c)
      (fun j => Work.HP.NA.modEq_of_dvd_sub (hc j)) m
  have hm' : Work.HP.veronese d n y m' ≡ c ^ d * Work.HP.veronese d n x m' [ZMOD (p : ℤ) ^ e] :=
    Work.HP.NA.veronese_modEq (E := (p : ℤ) ^ e) (c := c)
      (fun j => Work.HP.NA.modEq_of_dvd_sub (hc j)) m'
  rw [Int.modEq_iff_dvd] at hm hm'
  have key : Work.HP.veronese d n x m * Work.HP.veronese d n y m'
      - Work.HP.veronese d n x m' * Work.HP.veronese d n y m
      = Work.HP.veronese d n x m'
          * (c ^ d * Work.HP.veronese d n x m - Work.HP.veronese d n y m)
        - Work.HP.veronese d n x m
          * (c ^ d * Work.HP.veronese d n x m' - Work.HP.veronese d n y m') := by
    ring
  rw [key]
  exact dvd_sub (dvd_mul_of_dvd_right hm _) (dvd_mul_of_dvd_right hm' _)

/-- Converse direction: if `p^e` divides the gcd of the `2 × 2` minors of the Veronese vectors and
both `x` and `y` are primitive at `p`, then `p^e` divides the gcd of the `2 × 2` minors of `(x, y)`. -/
theorem dvd_gcdMinors2_of_dvd_veronese (d n : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : p.Prime)
    (x y : Fin (n + 1) → ℤ) (hx : ∃ i, ¬ (p : ℤ) ∣ x i) (hy : ∃ i, ¬ (p : ℤ) ∣ y i)
    (e : ℕ) :
    (p : ℤ) ^ e ∣ Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) →
      (p : ℤ) ^ e ∣ Work.HP.gcdMinors2 x y := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases e with _ | e
  · intro _; exact one_dvd _
  intro hG
  obtain ⟨i0, hi0⟩ := hx
  -- the Veronese vector `ν x` is primitive at `p`
  have hnu : ∃ m : Mon d n, ¬ (p : ℤ) ∣ Work.HP.veronese d n x m :=
    ⟨Work.HP.NA.monDi d n i0, by
      rw [Work.HP.NA.veronese_monDi]
      exact fun h => hi0 (hpz.dvd_of_dvd_pow h)⟩
  obtain ⟨c, hc⟩ := Work.HP.NA.exists_lam_gcdMinors2 hp (Work.HP.veronese d n x)
    (Work.HP.veronese d n y) hnu hG
  -- `p ∤ c`
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro hpc'
    obtain ⟨k, hk⟩ := hy
    have h1 : (p : ℤ) ∣ y k ^ d := by
      have h2 := hc (Work.HP.NA.monDi d n k)
      rw [Work.HP.NA.veronese_monDi d n y k, Work.HP.NA.veronese_monDi d n x k] at h2
      have h3 : (p : ℤ) ∣ (y k ^ d - c * x k ^ d) :=
        dvd_trans (dvd_pow_self (p : ℤ) (by omega)) h2
      have h4 : (p : ℤ) ∣ c * x k ^ d := dvd_mul_of_dvd_left hpc' _
      simpa using dvd_add h3 h4
    exact hk (hpz.dvd_of_dvd_pow h1)
  -- `p ∤ y i0`
  have hyi0 : ¬ (p : ℤ) ∣ y i0 := by
    intro hyi0'
    have h2 := hc (Work.HP.NA.monDi d n i0)
    rw [Work.HP.NA.veronese_monDi d n y i0, Work.HP.NA.veronese_monDi d n x i0] at h2
    have h3 : (p : ℤ) ∣ (y i0 ^ d - c * x i0 ^ d) :=
      dvd_trans (dvd_pow_self (p : ℤ) (by omega)) h2
    have h4 : (p : ℤ) ∣ y i0 ^ d := dvd_pow hyi0' (by omega)
    have h5 : (p : ℤ) ∣ c * x i0 ^ d := by
      have hh : (p : ℤ) ∣ (y i0 ^ d - c * x i0 ^ d) - y i0 ^ d := dvd_sub h3 h4
      have heq : (y i0 ^ d - c * x i0 ^ d) - y i0 ^ d = -(c * x i0 ^ d) := by ring
      rw [heq] at hh
      exact dvd_neg.mp hh
    rcases hpz.dvd_or_dvd h5 with h6 | h6
    · exact hpc h6
    · exact hi0 (hpz.dvd_of_dvd_pow h6)
  -- the relation `p^{e+1} ∣ y i0^{d-1} · (x i0 · y j - x j · y i0)` for all `j`
  have hstep5 : ∀ j : Fin (n + 1), (p : ℤ) ^ (e + 1) ∣ (x i0 * y j - x j * y i0) := by
    intro j
    by_cases hj : j = i0
    · subst hj; simp
    · have h2 := hc (Work.HP.NA.monDij d n hd i0 j)
      rw [Work.HP.NA.veronese_monDij d n hd y i0 j,
          Work.HP.NA.veronese_monDij d n hd x i0 j] at h2
      have h3 := hc (Work.HP.NA.monDi d n i0)
      rw [Work.HP.NA.veronese_monDi d n y i0, Work.HP.NA.veronese_monDi d n x i0] at h3
      have hyd : y i0 ^ d = y i0 ^ (d - 1) * y i0 := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
      have hxd : x i0 ^ d = x i0 ^ (d - 1) * x i0 := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
      rw [hyd, hxd] at h3
      have h4 : (p : ℤ) ^ (e + 1)
          ∣ x i0 * (y i0 ^ (d - 1) * y j - c * (x i0 ^ (d - 1) * x j)) :=
        dvd_mul_of_dvd_right h2 (x i0)
      have h5 : (p : ℤ) ^ (e + 1)
          ∣ x j * (y i0 ^ (d - 1) * y i0 - c * (x i0 ^ (d - 1) * x i0)) :=
        dvd_mul_of_dvd_right h3 (x j)
      have h6 : (p : ℤ) ^ (e + 1) ∣ y i0 ^ (d - 1) * (x i0 * y j - x j * y i0) := by
        have hsub := dvd_sub h4 h5
        have key : x i0 * (y i0 ^ (d - 1) * y j - c * (x i0 ^ (d - 1) * x j))
            - x j * (y i0 ^ (d - 1) * y i0 - c * (x i0 ^ (d - 1) * x i0))
            = y i0 ^ (d - 1) * (x i0 * y j - x j * y i0) := by ring
        rwa [key] at hsub
      have hny : ¬ (p : ℤ) ∣ y i0 ^ (d - 1) := fun h => hyi0 (hpz.dvd_of_dvd_pow h)
      exact Work.HP.NA.dvd_of_dvd_mul_of_not_dvd_pow hpz hny h6
  -- promote to all `2 × 2` minors of `(x, y)`
  have hstep6 : ∀ i j : Fin (n + 1), (p : ℤ) ^ (e + 1) ∣ (x i * y j - x j * y i) := by
    intro i j
    have h1 := hstep5 j
    have h2 := hstep5 i
    have hcomb : (p : ℤ) ^ (e + 1) ∣ x i0 * (x i * y j - x j * y i) := by
      have hsub := dvd_sub (dvd_mul_of_dvd_right h1 (x i)) (dvd_mul_of_dvd_right h2 (x j))
      have key : x i * (x i0 * y j - x j * y i0) - x j * (x i0 * y i - x i * y i0)
          = x i0 * (x i * y j - x j * y i) := by ring
      rwa [key] at hsub
    exact Work.HP.NA.dvd_of_dvd_mul_of_not_dvd_pow hpz hi0 hcomb
  exact (Work.HP.NA.gcdMinors2_dvd_iff ((p : ℤ) ^ (e + 1)) x y).mpr hstep6

/-- **Lemma G of Browning--Le Boudec--Sawin.** For `1 ≤ d` and primitive `x, y`, the gcd of the
`2 × 2` minors of the pair of Veronese vectors `(ν_{d,n}(x), ν_{d,n}(y))` equals the gcd of the
`2 × 2` minors of `(x, y)`. -/
theorem gcdMinors_veronese (d n : ℕ) (hd : 1 ≤ d) (x y : Fin (n + 1) → ℤ)
    (hx : Work.HP.IsPrim x) (hy : Work.HP.IsPrim y) :
    Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) = Work.HP.gcdMinors2 x y := by
  set G := Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) with hG
  set g := Work.HP.gcdMinors2 x y with hg
  have hiff : ∀ p : ℕ, p.Prime → ∀ e : ℕ, p ^ e ∣ G.natAbs ↔ p ^ e ∣ g.natAbs := by
    intro p hp e
    have hx' : ∃ i, ¬ (p : ℤ) ∣ x i := Work.HP.GM.exists_not_dvd_of_isPrim x hx hp
    have hy' : ∃ i, ¬ (p : ℤ) ∣ y i := Work.HP.GM.exists_not_dvd_of_isPrim y hy hp
    have h1 : (p : ℤ) ^ e ∣ G ↔ (p : ℤ) ^ e ∣ g :=
      ⟨dvd_gcdMinors2_of_dvd_veronese d n hd p hp x y hx' hy' e,
       dvd_gcdMinors2_veronese_of_dvd d n p hp x y hx' e⟩
    have key : ∀ {A : ℤ}, p ^ e ∣ A.natAbs ↔ (p : ℤ) ^ e ∣ A := by
      intro A
      have h := Int.natAbs_dvd_natAbs (a := (p : ℤ) ^ e) (b := A)
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at h
    rw [key, key]
    exact h1
  have hEq : G.natAbs = g.natAbs :=
    Work.HP.GM.nat_eq_of_forall_prime_pow_dvd_iff (fun p e hp => hiff p hp e)
  have hGnn : 0 ≤ G := gcdMinors2_nonneg (Work.HP.veronese d n x) (Work.HP.veronese d n y)
  have hgnn : 0 ≤ g := gcdMinors2_nonneg x y
  calc G = (G.natAbs : ℤ) := (Int.natAbs_of_nonneg hGnn).symm
    _ = (g.natAbs : ℤ) := by rw [hEq]
    _ = g := Int.natAbs_of_nonneg hgnn

end Work.HP.EEupper
