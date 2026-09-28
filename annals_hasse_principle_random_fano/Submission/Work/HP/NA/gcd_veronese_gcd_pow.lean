import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.NA.exists_lam_gcdMinors2
import Submission.Work.HP.EE.veronese_swap

namespace Work.HP.NA

open Work.HP

/-- The `2×2` minor of `(ν x, ν y)` indexed by the pair of monomials `monDij j k`, `monDij j l`
factors as `(x j * y j)^(d-1) * (x k * y l - x l * y k)`.  This is the elementary identity that
drives the hard direction of the `p`-adic comparison. -/
theorem veronese_monDij_minor (d n : ℕ) (hd : 1 ≤ d) (x y : Fin (n + 1) → ℤ)
    (j k l : Fin (n + 1)) :
    veronese d n x (monDij d n hd j k) * veronese d n y (monDij d n hd j l)
      - veronese d n x (monDij d n hd j l) * veronese d n y (monDij d n hd j k)
      = (x j * y j) ^ (d - 1) * (x k * y l - x l * y k) := by
  rw [veronese_monDij d n hd x j k, veronese_monDij d n hd y j l,
      veronese_monDij d n hd x j l, veronese_monDij d n hd y j k, mul_pow]
  ring

/-- Easy direction of the `p`-adic comparison (Browning--Le Boudec--Sawin, Lemma G):
if `p^e` divides every `2×2` minor of `(x, y)` and `x` has a coordinate coprime to `p`, then `p^e`
divides every `2×2` minor of `(ν x, ν y)`. -/
theorem veronese_dvd_of_dvd_gcdMinors2 (d n p e : ℕ) (hp : p.Prime) (x y : Fin (n + 1) → ℤ)
    (hx : ∃ i, ¬ (p : ℤ) ∣ x i)
    (h : (p : ℤ) ^ e ∣ gcdMinors2 x y) :
    (p : ℤ) ^ e ∣ gcdMinors2 (veronese d n x) (veronese d n y) := by
  obtain ⟨c, hc⟩ := exists_lam_gcdMinors2 hp x y hx h
  have hmod : ∀ i, y i ≡ c * x i [ZMOD (p : ℤ) ^ e] := fun i => modEq_of_dvd_sub (hc i)
  rw [gcdMinors2_dvd_iff]
  intro m1 m2
  have h1 : veronese d n y m1 ≡ c ^ d * veronese d n x m1 [ZMOD (p : ℤ) ^ e] :=
    veronese_modEq hmod m1
  have h2 : veronese d n y m2 ≡ c ^ d * veronese d n x m2 [ZMOD (p : ℤ) ^ e] :=
    veronese_modEq hmod m2
  have hsub := Int.ModEq.sub
    (Int.ModEq.mul (Int.ModEq.refl (veronese d n x m1)) h2)
    (Int.ModEq.mul (Int.ModEq.refl (veronese d n x m2)) h1)
  have hz : veronese d n x m1 * (c ^ d * veronese d n x m2)
      - veronese d n x m2 * (c ^ d * veronese d n x m1) = 0 := by ring
  rw [hz] at hsub
  have := Int.modEq_iff_dvd.mp hsub
  rw [zero_sub] at this
  exact dvd_neg.mp this

/-- `p ∤ gcdMinors2 (ν x, ν y)` in the "bad" case where every product `x j * y j` is divisible
by `p`, but `x` and `y` each have a coordinate coprime to `p`.  Indeed then one finds indices
`i₀, i₁` with `p ∣ x i₁`, `p ∣ y i₀`, `p ∤ x i₀ y i₁`, and the degree-`d` minor
`x i₀^d y i₁^d - x i₁^d y i₀^d` is not divisible by `p`. -/
theorem not_dvd_veronese_of_all_p_dvd (d n p : ℕ) (hd : 1 ≤ d) (hp : p.Prime)
    (x y : Fin (n + 1) → ℤ) (hx : ∃ i, ¬ (p : ℤ) ∣ x i) (hy : ∃ i, ¬ (p : ℤ) ∣ y i)
    (hall : ∀ j, (p : ℤ) ∣ x j * y j) :
    ¬ (p : ℤ) ∣ gcdMinors2 (veronese d n x) (veronese d n y) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨i0, hi0⟩ := hx
  obtain ⟨j0, hj0⟩ := hy
  have hpyi0 : (p : ℤ) ∣ y i0 := by
    rcases hpz.dvd_or_dvd (hall i0) with h | h
    · exact absurd h hi0
    · exact h
  have hpxj0 : (p : ℤ) ∣ x j0 := by
    rcases hpz.dvd_or_dvd (hall j0) with h | h
    · exact h
    · exact absurd h hj0
  have hAi : ¬ (p : ℤ) ∣ x i0 ^ d := fun h => hi0 (hpz.dvd_of_dvd_pow h)
  have hAj : ¬ (p : ℤ) ∣ y j0 ^ d := fun h => hj0 (hpz.dvd_of_dvd_pow h)
  have hA : ¬ (p : ℤ) ∣ x i0 ^ d * y j0 ^ d := hpz.not_dvd_mul hAi hAj
  have hB : (p : ℤ) ∣ x j0 ^ d * y i0 ^ d :=
    dvd_mul_of_dvd_left
      (dvd_trans hpxj0 (dvd_pow_self (x j0) (by omega : d ≠ 0))) (y i0 ^ d)
  intro hdiv
  have hmin := (gcdMinors2_dvd_iff (p : ℤ) (veronese d n x) (veronese d n y)).mp hdiv
    (monDi d n i0) (monDi d n j0)
  rw [veronese_monDi d n x i0, veronese_monDi d n y j0,
      veronese_monDi d n x j0, veronese_monDi d n y i0] at hmin
  refine hA ?_
  have key : x i0 ^ d * y j0 ^ d
      = (x i0 ^ d * y j0 ^ d - x j0 ^ d * y i0 ^ d) + x j0 ^ d * y i0 ^ d := by ring
  rw [key]
  exact dvd_add hmin hB

/-- Hard direction of the `p`-adic comparison: if `p^e` divides every `2×2` minor of
`(ν x, ν y)`, and `x, y` each have a coordinate coprime to `p`, then `p^e` divides every `2×2`
minor of `(x, y)`. -/
theorem dvd_of_veronese_dvd (d n p e : ℕ) (hd : 1 ≤ d) (hp : p.Prime)
    (x y : Fin (n + 1) → ℤ) (hx : ∃ i, ¬ (p : ℤ) ∣ x i) (hy : ∃ i, ¬ (p : ℤ) ∣ y i)
    (h : (p : ℤ) ^ e ∣ gcdMinors2 (veronese d n x) (veronese d n y)) :
    (p : ℤ) ^ e ∣ gcdMinors2 x y := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [gcdMinors2_dvd_iff]
  intro k l
  by_cases hcase : ∃ j, ¬ (p : ℤ) ∣ x j * y j
  · obtain ⟨j, hj⟩ := hcase
    have hmin := (gcdMinors2_dvd_iff ((p : ℤ) ^ e) (veronese d n x) (veronese d n y)).mp h
      (monDij d n hd j k) (monDij d n hd j l)
    rw [veronese_monDij_minor d n hd x y j k l] at hmin
    exact dvd_of_dvd_mul_of_not_dvd_pow hpz
      (fun hdvd => hj (hpz.dvd_of_dvd_pow hdvd)) hmin
  · push Not at hcase
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · exact absurd
        (dvd_trans (dvd_pow_self (p : ℤ) (ne_of_gt he)) h)
        (not_dvd_veronese_of_all_p_dvd d n p hd hp x y hx hy hcase)

/-- The `p`-adic comparison of the gcd of minors of `(x, y)` and of `(ν x, ν y)`. -/
theorem dvd_gcdMinors2_veronese_iff (d n p e : ℕ) (hd : 1 ≤ d) (hp : p.Prime)
    (x y : Fin (n + 1) → ℤ) (hx : ∃ i, ¬ (p : ℤ) ∣ x i) (hy : ∃ i, ¬ (p : ℤ) ∣ y i) :
    ((p : ℤ) ^ e ∣ gcdMinors2 (veronese d n x) (veronese d n y)) ↔
      ((p : ℤ) ^ e ∣ gcdMinors2 x y) :=
  ⟨fun h => dvd_of_veronese_dvd d n p e hd hp x y hx hy h,
   fun h => veronese_dvd_of_dvd_gcdMinors2 d n p e hp x y hx h⟩

theorem gcd_veronese_gcd_pow (d n p r : ℕ) (hd : 1 ≤ d) (hp : p.Prime) (x y : Fin (n + 1) → ℤ)
    (hx : ∃ i, ¬ (p : ℤ) ∣ x i) (hy : ∃ i, ¬ (p : ℤ) ∣ y i) :
    Nat.gcd (Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y)).natAbs (p ^ r)
      = Nat.gcd (Work.HP.gcdMinors2 x y).natAbs (p ^ r) := by
  set G1 : ℤ := gcdMinors2 (veronese d n x) (veronese d n y) with hG1
  set G2 : ℤ := gcdMinors2 x y with hG2
  have hiff : ∀ e : ℕ, (p : ℤ) ^ e ∣ G1 ↔ (p : ℤ) ^ e ∣ G2 := by
    intro e
    rw [hG1, hG2]
    exact ⟨fun h => dvd_of_veronese_dvd d n p e hd hp x y hx hy h,
      fun h => veronese_dvd_of_dvd_gcdMinors2 d n p e hp x y hx h⟩
  have hbridge : ∀ (G : ℤ) (e : ℕ), (p ^ e ∣ G.natAbs) ↔ ((p : ℤ) ^ e ∣ G) := by
    intro G e
    have h1 : (p ^ e ∣ G.natAbs) ↔ (((p ^ e : ℕ) : ℤ) ∣ (G.natAbs : ℤ)) :=
      (Int.natCast_dvd_natCast (m := p ^ e) (n := G.natAbs)).symm
    have h2 : (((p ^ e : ℕ) : ℤ) ∣ (G.natAbs : ℤ)) ↔ ((p : ℤ) ^ e ∣ (G.natAbs : ℤ)) := by
      rw [Nat.cast_pow]
    have h3 : ((p : ℤ) ^ e ∣ (G.natAbs : ℤ)) ↔ ((p : ℤ) ^ e ∣ G) := Int.dvd_natAbs
    exact h1.trans (h2.trans h3)
  have hnat : ∀ e : ℕ, p ^ e ∣ G1.natAbs ↔ p ^ e ∣ G2.natAbs :=
    fun e => (hbridge G1 e).trans ((hiff e).trans (hbridge G2 e).symm)
  refine Nat.dvd_antisymm ?_ ?_
  · obtain ⟨k, hkr, hkeq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right G1.natAbs (p ^ r))
    rw [hkeq]
    exact Nat.dvd_gcd ((hnat k).mp (hkeq ▸ Nat.gcd_dvd_left G1.natAbs (p ^ r)))
      (pow_dvd_pow p hkr)
  · obtain ⟨k, hkr, hkeq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right G2.natAbs (p ^ r))
    rw [hkeq]
    exact Nat.dvd_gcd ((hnat k).mpr (hkeq ▸ Nat.gcd_dvd_left G2.natAbs (p ^ r)))
      (pow_dvd_pow p hkr)

end Work.HP.NA
