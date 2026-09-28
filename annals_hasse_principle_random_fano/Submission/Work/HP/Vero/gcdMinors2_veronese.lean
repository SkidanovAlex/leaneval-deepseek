import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.NA.VeroAux

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Vero

open Work.HP

/-! ## Auxiliary lemmas proved here -/

section peel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Function.update α j (α j) = α`. -/
lemma update_self_eq (α : ι → ℕ) (j : ι) : Function.update α j (α j) = α := by
  funext i
  by_cases h : i = j <;> simp [Function.update_apply, h]

/-- Peeling one unit off the `j`-th exponent of a product of powers. -/
lemma prod_pow_update (f : ι → ℤ) (α : ι → ℕ) (j : ι) (c : ℕ) :
    ∏ i, f i ^ (Function.update α j c) i = (∏ i ∈ Finset.univ.erase j, f i ^ α i) * f j ^ c := by
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i => f i ^ (Function.update α j c) i) (Finset.mem_univ j)]
  congr 1
  · refine Finset.prod_congr rfl (fun i hi => ?_)
    have hne : ¬ (i = j) := (Finset.mem_erase.mp hi).1
    rw [Function.update_apply]
    simp only [hne, if_false]
  · rw [Function.update_self]

/-- Peeling one unit off the `j`-th exponent when it is positive. -/
lemma prod_pow_update_mul (f : ι → ℤ) (α : ι → ℕ) (j : ι) (hj : 0 < α j) :
    (∏ i, f i ^ α i) = f j * ∏ i, f i ^ (Function.update α j (α j - 1)) i := by
  have e1 : (∏ i, f i ^ α i) = (∏ i ∈ Finset.univ.erase j, f i ^ α i) * f j ^ (α j) := by
    have h := prod_pow_update f α j (α j)
    rw [update_self_eq α j] at h
    exact h
  have e2 : (∏ i, f i ^ (Function.update α j (α j - 1)) i)
      = (∏ i ∈ Finset.univ.erase j, f i ^ α i) * f j ^ (α j - 1) :=
    prod_pow_update f α j (α j - 1)
  have hpow : f j ^ (α j) = f j * f j ^ (α j - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hj]
    rw [pow_succ']
  rw [e1, e2, hpow]
  ring

/-- Sum of an updated exponent vector. -/
lemma sum_update (α : ι → ℕ) (j : ι) (c : ℕ) :
    ∑ i, (Function.update α j c) i = (∑ i ∈ Finset.univ.erase j, α i) + c := by
  rw [← Finset.sum_erase_add Finset.univ
    (fun i => (Function.update α j c) i) (Finset.mem_univ j)]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hne : ¬ (i = j) := (Finset.mem_erase.mp hi).1
    rw [Function.update_apply]
    simp only [hne, if_false]
  · rw [Function.update_self]

end peel

/-- **Expansion lemma.**  If `q` divides every `2 × 2` minor `x i * y j - x j * y i` of the two
vectors `x, y`, then `q` divides the `2 × 2` minor of any two monomials of equal total degree. -/
theorem dvd_pow_prod_sub_of_dvd_minors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℤ) (q : ℤ) (h : ∀ i j, q ∣ x i * y j - x j * y i) :
    ∀ (s : ℕ) (α β : ι → ℕ), (∑ i, α i = s) → (∑ i, β i = s) →
      q ∣ (∏ i, x i ^ α i) * (∏ i, y i ^ β i) - (∏ i, y i ^ α i) * (∏ i, x i ^ β i) := by
  intro s
  refine Nat.strong_induction_on (p := fun s => ∀ α β : ι → ℕ,
    (∑ i, α i = s) → (∑ i, β i = s) →
      q ∣ (∏ i, x i ^ α i) * (∏ i, y i ^ β i) - (∏ i, y i ^ α i) * (∏ i, x i ^ β i)) s ?_
  intro s ih α β hα hβ
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have hα0 : ∀ i, α i = 0 := by
      intro i
      have hle : α i ≤ ∑ j, α j :=
        Finset.single_le_sum (f := α) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hβ0 : ∀ i, β i = 0 := by
      intro i
      have hle : β i ≤ ∑ j, β j :=
        Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    simpa [hα0, hβ0] using (dvd_zero q : q ∣ 0)
  · obtain ⟨j₀, hj₀⟩ : ∃ i, 0 < α i := by
      by_contra hcon
      push_neg at hcon
      have hzero : ∑ i, α i = 0 :=
        Finset.sum_eq_zero (fun i _ => Nat.le_zero.mp (hcon i))
      omega
    obtain ⟨j₁, hj₁⟩ : ∃ i, 0 < β i := by
      by_contra hcon
      push_neg at hcon
      have hzero : ∑ i, β i = 0 :=
        Finset.sum_eq_zero (fun i _ => Nat.le_zero.mp (hcon i))
      omega
    let α' : ι → ℕ := Function.update α j₀ (α j₀ - 1)
    let β' : ι → ℕ := Function.update β j₁ (β j₁ - 1)
    have hα'sum : ∑ i, α' i = s - 1 := by
      have h1 : ∑ i, α' i = (∑ i ∈ Finset.univ.erase j₀, α i) + (α j₀ - 1) :=
        sum_update α j₀ (α j₀ - 1)
      have h2 : (∑ i ∈ Finset.univ.erase j₀, α i) + α j₀ = s := by
        rw [Finset.sum_erase_add Finset.univ α (Finset.mem_univ j₀), hα]
      omega
    have hβ'sum : ∑ i, β' i = s - 1 := by
      have h1 : ∑ i, β' i = (∑ i ∈ Finset.univ.erase j₁, β i) + (β j₁ - 1) :=
        sum_update β j₁ (β j₁ - 1)
      have h2 : (∑ i ∈ Finset.univ.erase j₁, β i) + β j₁ = s := by
        rw [Finset.sum_erase_add Finset.univ β (Finset.mem_univ j₁), hβ]
      omega
    have hIH : q ∣ (∏ i, x i ^ α' i) * (∏ i, y i ^ β' i)
        - (∏ i, y i ^ α' i) * (∏ i, x i ^ β' i) :=
      ih (s - 1) (by omega) α' β' hα'sum hβ'sum
    have hkey : (∏ i, x i ^ α i) * (∏ i, y i ^ β i) - (∏ i, y i ^ α i) * (∏ i, x i ^ β i)
        = (x j₀ * y j₁) * ((∏ i, x i ^ α' i) * (∏ i, y i ^ β' i)
            - (∏ i, y i ^ α' i) * (∏ i, x i ^ β' i))
          + (x j₀ * y j₁ - x j₁ * y j₀) * ((∏ i, y i ^ α' i) * (∏ i, x i ^ β' i)) := by
      rw [prod_pow_update_mul x α j₀ hj₀, prod_pow_update_mul y β j₁ hj₁,
        prod_pow_update_mul y α j₀ hj₀, prod_pow_update_mul x β j₁ hj₁]
      ring
    rw [hkey]
    exact dvd_add (dvd_mul_of_dvd_right hIH _) (dvd_mul_of_dvd_left (h j₀ j₁) _)


/-- If no integer prime divides both `q` and `g`, then `q` and `g` are coprime. -/
lemma isCoprime_of_forall_prime_not_dvd {q g : ℤ}
    (h : ∀ p : ℤ, Prime p → p ∣ q → ¬ p ∣ g) : IsCoprime q g := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
  have hpdvd' : ((p : ℕ) : ℤ) ∣ ((q.gcd g : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpdvd
  have h1 : (p : ℤ) ∣ q := dvd_trans hpdvd' (Int.gcd_dvd_left q g)
  have h2 : (p : ℤ) ∣ g := dvd_trans hpdvd' (Int.gcd_dvd_right q g)
  exact h (p : ℤ) hpz h1 h2

/-- If a prime divides every `2 × 2` minor of the Veronese embeddings of two primitive vectors,
then some coordinate has `p ∤ x j * y j`. -/
lemma exists_not_dvd_mul_of_prime_dvd_veronese_minors {d n : ℕ} (hd : 1 ≤ d) (p : ℤ)
    (hp : Prime p) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (h : ∀ a b : Mon d n,
      p ∣ veronese d n x a * veronese d n y b - veronese d n x b * veronese d n y a) :
    ∃ j : Fin (n + 1), ¬ p ∣ x j * y j := by
  have prim_not_dvd : ∀ v : Fin (n + 1) → ℤ, IsPrim v → ∃ i, ¬ p ∣ v i := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    have h1 : p ∣ (Finset.univ.gcd v : ℤ) := Finset.dvd_gcd (fun i _ => hcon i)
    rw [hv] at h1
    exact hp.not_dvd_one h1
  obtain ⟨j₁, hj₁⟩ := prim_not_dvd x hx
  obtain ⟨j₀, hj₀⟩ := prim_not_dvd y hy
  by_contra hcon
  push_neg at hcon
  by_cases hjj : j₀ = j₁
  · rw [hjj] at hj₀
    rcases (hp.dvd_mul).mp (hcon j₁) with h1 | h1
    · exact hj₁ h1
    · exact hj₀ h1
  · have hxj₀ : p ∣ x j₀ := by
      rcases (hp.dvd_mul).mp (hcon j₀) with h1 | h1
      · exact h1
      · exact absurd h1 hj₀
    have hyj₁ : p ∣ y j₁ := by
      rcases (hp.dvd_mul).mp (hcon j₁) with h1 | h1
      · exact absurd h1 hj₁
      · exact h1
    have hminor := h (NA.monDi d n j₀) (NA.monDi d n j₁)
    rw [NA.veronese_monDi, NA.veronese_monDi, NA.veronese_monDi, NA.veronese_monDi] at hminor
    have hd0 : d ≠ 0 := by omega
    have h1 : p ∣ x j₀ ^ d * y j₁ ^ d := dvd_mul_of_dvd_left (hxj₀.pow hd0) _
    have h2 : p ∣ x j₁ ^ d * y j₀ ^ d := by
      have heq : x j₁ ^ d * y j₀ ^ d
          = (x j₀ ^ d * y j₁ ^ d) - ((x j₀ ^ d * y j₁ ^ d) - (x j₁ ^ d * y j₀ ^ d)) := by
        ring
      rw [heq]
      exact dvd_sub h1 hminor
    rcases (hp.dvd_mul).mp h2 with h3 | h3
    · exact hj₁ (hp.dvd_of_dvd_pow h3)
    · exact hj₀ (hp.dvd_of_dvd_pow h3)

/-- The gcd of the `2 × 2` minors of the columns `ν_{d,n}(x), ν_{d,n}(y)` equals the gcd of the
`2 × 2` minors of the columns `x, y` (the paper's "Lemma G").

Suggested route: `≥`: if `q ∣ x_i y_j - x_j y_i` for all `i,j` then `q ∣ P(x)Q(y) - P(y)Q(x)` for
all degree-`d` monomials `P,Q`, hence `q` divides every minor of `ν(x),ν(y)`.  `≤`: let the prime
`p` divide every minor of `ν(x),ν(y)`; the paper shows `p ∣ x_j^{d-1}y_j^{d-1}(x_k y_l - x_l y_k)`
for all `j,k,l`, so it suffices to find `j` with `p ∤ x_j y_j`; if no such `j` existed then
primitivity of `x,y` gives distinct `j₀,j₁` with `p ∤ x_{j₁}y_{j₀}` and `p ∣ x_{j₀}`, and the
minor of the monomials `d·e_{j₀}`, `d·e_{j₁}` is `x_{j₀}^d y_{j₁}^d - x_{j₁}^d y_{j₀}^d ≢ 0 mod p`,
a contradiction.  Conclude with `Int.gcd`/`Finset.gcd` divisibility theory (`Finset.gcd_eq_one_iff`
etc.). -/
theorem gcdMinors2_veronese (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) :
    gcdMinors2 (veronese d n x) (veronese d n y) = gcdMinors2 x y := by
  let Q : ℤ := gcdMinors2 (veronese d n x) (veronese d n y)
  let G : ℤ := gcdMinors2 x y
  have hQmin : ∀ a b : Mon d n,
      Q ∣ veronese d n x a * veronese d n y b - veronese d n x b * veronese d n y a :=
    (NA.gcdMinors2_dvd_iff Q (veronese d n x) (veronese d n y)).mp (dvd_refl Q)
  have hGmin : ∀ i j : Fin (n + 1), G ∣ x i * y j - x j * y i :=
    (NA.gcdMinors2_dvd_iff G x y).mp (dvd_refl G)
  have hGdvdQ : G ∣ Q := by
    refine (NA.gcdMinors2_dvd_iff G (veronese d n x) (veronese d n y)).mpr (fun a b => ?_)
    have h := dvd_pow_prod_sub_of_dvd_minors x y G hGmin (∑ i, (a.1 i : ℕ))
      (fun i => (a.1 i : ℕ)) (fun i => (b.1 i : ℕ)) rfl (by rw [a.2, b.2])
    simpa only [veronese, mul_comm] using h
  have hQdvdG : Q ∣ G := by
    refine (NA.gcdMinors2_dvd_iff Q x y).mpr (fun k l => ?_)
    let M : ℤ := x k * y l - x l * y k
    let c : Fin (n + 1) → ℤ := fun j => (x j * y j) ^ (d - 1)
    have hA : ∀ j, Q ∣ c j * M := by
      intro j
      have h := hQmin (NA.monDij d n hd j k) (NA.monDij d n hd j l)
      rw [NA.veronese_monDij, NA.veronese_monDij, NA.veronese_monDij, NA.veronese_monDij] at h
      have hkey : c j * M = (x j ^ (d - 1) * x k) * (y j ^ (d - 1) * y l)
          - (x j ^ (d - 1) * x l) * (y j ^ (d - 1) * y k) := by
        show (x j * y j) ^ (d - 1) * (x k * y l - x l * y k) = _
        rw [mul_pow]
        ring
      rw [hkey]
      exact h
    have hB : IsCoprime Q (Finset.univ.gcd c) := by
      refine isCoprime_of_forall_prime_not_dvd (fun p hp hpQ => ?_)
      have hmin : ∀ a b : Mon d n,
          p ∣ veronese d n x a * veronese d n y b - veronese d n x b * veronese d n y a :=
        fun a b => dvd_trans hpQ (hQmin a b)
      obtain ⟨j, hj⟩ := exists_not_dvd_mul_of_prime_dvd_veronese_minors hd p hp x y hx hy hmin
      intro hgc
      have hc : p ∣ c j := dvd_trans hgc (Finset.gcd_dvd (f := c) (Finset.mem_univ j))
      exact hj (hp.dvd_of_dvd_pow hc)
    have hmain : Q ∣ Finset.univ.gcd (fun j => c j * M) := Finset.dvd_gcd (fun j _ => hA j)
    rw [Finset.gcd_mul_right] at hmain
    exact (normalize_associated M).dvd_iff_dvd_right.mp (hB.dvd_of_dvd_mul_left hmain)
  have hQnn : 0 ≤ Q := by
    show 0 ≤ gcdMinors2 (veronese d n x) (veronese d n y)
    exact Finset.Int.finsetGcd_nonneg
  have hGnn : 0 ≤ G := by
    show 0 ≤ gcdMinors2 x y
    exact Finset.Int.finsetGcd_nonneg
  have hnat : Q.natAbs = G.natAbs :=
    Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.mpr hQdvdG) (Int.natAbs_dvd_natAbs.mpr hGdvdQ)
  calc Q = (Q.natAbs : ℤ) := (Int.natAbs_of_nonneg hQnn).symm
    _ = (G.natAbs : ℤ) := by rw [hnat]
    _ = G := Int.natAbs_of_nonneg hGnn

end Work.HP.Vero
