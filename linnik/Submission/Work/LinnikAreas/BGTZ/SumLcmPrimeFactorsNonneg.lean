import Mathlib

namespace Work.LinnikAreas.BGTZ

open scoped BigOperators

/-!
# Non-negativity of the double sum `∑_{d,e ≤ R} θ_d θ_e ∏_{p | [d,e]} f(p)`

For `0 ≤ f(p) ≤ 1` the kernel `([d,e]) ↦ ∏_{p | [d,e]} f(p)` is positive semi-definite:
writing `A d` for the (finite) set of prime factors of `d` and fixing a finite set `Q` of primes
containing every `A d`, the prime-by-prime identity

`[p ∈ A d ∪ A e]·f(p) + [p ∉ A d ∪ A e] = f(p) + (1 - f(p))·[p ∉ A d]·[p ∉ A e]`

expands (via `Finset.prod_add`) the product over `p ∈ Q` into a sum over subsets `t ⊆ Q`, and the
whole double sum collapses to

`∑_{t ⊆ Q} (∏_{p ∈ t} f(p)) (∏_{p ∈ Q \ t} (1 - f(p))) · (∑_d θ_d ∏_{p ∈ Q \ t} [p ∉ A d])² ≥ 0`,

a sum of non-negative terms. The lemma `double_sum_factor` performs the collapse
`∑_i ∑_j u_i u_j (c (Y_i Y_j)) = c (∑_i u_i Y_i)²`, and `nonneg_double_sum_lcm_kernel` is the
general statement; the requested theorem instantiates it with `A = Nat.primeFactors` and
`Q = Nat.primesLE R`.
-/

/-- Collapse of a double sum: `∑_i ∑_j u_i u_j (c·(Y_i·Y_j)) = c·(∑_i u_i·Y_i)²`. -/
theorem double_sum_factor {ι : Type*} [DecidableEq ι] (s : Finset ι) (u Y : ι → ℝ) (c : ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, u i * u j * (c * (Y i * Y j)) = c * (∑ i ∈ s, u i * Y i)^2 := by
  have h1 : (∑ i ∈ s, u i * Y i)^2 = ∑ i ∈ s, ∑ j ∈ s, (u i * Y i) * (u j * Y j) := by
    rw [pow_two, Finset.sum_mul_sum]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  ring

/-- **Non-negativity of the prime-factor `lcm` kernel.** For a finite index set `s`, a finite set
`Q` of naturals, `f : ℕ → ℝ` with `0 ≤ f p ≤ 1`, coefficients `u`, and prime-factor sets
`A i ⊆ Q`, the double sum `∑_{i,j} u_i u_j ∏_{p ∈ A i ∪ A j} f(p)` is non-negative. -/
theorem nonneg_double_sum_lcm_kernel {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Q : Finset ℕ) (f : ℕ → ℝ) (u : ι → ℝ) (A : ι → Finset ℕ)
    (hf0 : ∀ p, 0 ≤ f p) (hf1 : ∀ p, f p ≤ 1)
    (hA : ∀ i ∈ s, A i ⊆ Q) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, u i * u j * ∏ p ∈ (A i ∪ A j), f p := by
  let X : ℕ → ι → ℝ := fun p i => if p ∈ A i then 0 else 1
  let C : Finset ℕ → ℝ := fun t => (∏ p ∈ t, f p) * ∏ p ∈ Q \ t, (1 - f p)
  let Yf : Finset ℕ → ι → ℝ := fun t i => ∏ p ∈ Q \ t, X p i
  have hCnn : ∀ t, 0 ≤ C t := by
    intro t
    simp only [C]
    exact mul_nonneg (Finset.prod_nonneg fun p hp => hf0 p)
      (Finset.prod_nonneg fun p hp => sub_nonneg.mpr (hf1 p))
  -- prime-by-prime identity `[p ∈ A i ∪ A j]·f(p) + [p ∉ A i ∪ A j] = f(p) + (1-f(p))·[p ∉ A i]·[p ∉ A j]`
  have coef : ∀ (p : ℕ) (i j : ι),
      (if p ∈ A i ∪ A j then f p else 1) = f p + (1 - f p) * (X p i * X p j) := by
    intro p i j
    simp only [X]
    by_cases hi : p ∈ A i <;> by_cases hj : p ∈ A j <;> simp [hi, hj]
  have hprod : ∀ i ∈ s, ∀ j ∈ s,
      ∏ p ∈ (A i ∪ A j), f p = ∑ t ∈ Q.powerset, C t * (Yf t i * Yf t j) := by
    intro i hi j hj
    have hsub : A i ∪ A j ⊆ Q := Finset.union_subset (hA i hi) (hA j hj)
    have hsubset := Finset.prod_subset (f := fun p => if p ∈ A i ∪ A j then f p else 1) hsub
      (fun x hxQ hxnot => by rw [if_neg hxnot])
    have hext : ∏ p ∈ (A i ∪ A j), f p = ∏ p ∈ Q, (if p ∈ A i ∪ A j then f p else 1) := by
      rw [← hsubset]
      exact Finset.prod_congr rfl (fun p hp => by rw [if_pos hp])
    rw [hext]
    have hstep : ∏ p ∈ Q, (if p ∈ A i ∪ A j then f p else 1)
        = ∏ p ∈ Q, (f p + (1 - f p) * (X p i * X p j)) :=
      Finset.prod_congr rfl (fun p hp => coef p i j)
    rw [hstep, Finset.prod_add]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hinner : ∏ p ∈ Q \ t, ((1 - f p) * (X p i * X p j))
        = (∏ p ∈ Q \ t, (1 - f p)) * (Yf t i * Yf t j) := by
      simp only [Yf]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    rw [hinner]
    simp only [C]
    ring
  have hS : ∑ i ∈ s, ∑ j ∈ s, u i * u j * ∏ p ∈ (A i ∪ A j), f p
      = ∑ i ∈ s, ∑ j ∈ s, u i * u j * (∑ t ∈ Q.powerset, C t * (Yf t i * Yf t j)) :=
    Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => by rw [hprod i hi j hj]))
  rw [hS]
  have hswap : ∑ i ∈ s, ∑ j ∈ s, u i * u j * (∑ t ∈ Q.powerset, C t * (Yf t i * Yf t j))
      = ∑ t ∈ Q.powerset, ∑ i ∈ s, ∑ j ∈ s, u i * u j * (C t * (Yf t i * Yf t j)) := by
    have e1 : ∀ i ∈ s, (∑ j ∈ s, u i * u j * (∑ t ∈ Q.powerset, C t * (Yf t i * Yf t j)))
        = ∑ j ∈ s, ∑ t ∈ Q.powerset, u i * u j * (C t * (Yf t i * Yf t j)) :=
      fun i hi => Finset.sum_congr rfl
        (fun j hj => Finset.mul_sum Q.powerset (fun t => C t * (Yf t i * Yf t j)) (u i * u j))
    calc
      ∑ i ∈ s, ∑ j ∈ s, u i * u j * (∑ t ∈ Q.powerset, C t * (Yf t i * Yf t j))
          = ∑ i ∈ s, ∑ j ∈ s, ∑ t ∈ Q.powerset, u i * u j * (C t * (Yf t i * Yf t j)) :=
            Finset.sum_congr rfl e1
      _ = ∑ i ∈ s, ∑ t ∈ Q.powerset, ∑ j ∈ s, u i * u j * (C t * (Yf t i * Yf t j)) :=
            Finset.sum_congr rfl (fun i hi => Finset.sum_comm)
      _ = ∑ t ∈ Q.powerset, ∑ i ∈ s, ∑ j ∈ s, u i * u j * (C t * (Yf t i * Yf t j)) :=
            Finset.sum_comm
  rw [hswap]
  have hfac : ∀ t ∈ Q.powerset,
      ∑ i ∈ s, ∑ j ∈ s, u i * u j * (C t * (Yf t i * Yf t j))
        = C t * (∑ i ∈ s, u i * Yf t i)^2 :=
    fun t ht => double_sum_factor s u (Yf t) (C t)
  rw [Finset.sum_congr rfl hfac]
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (hCnn t) (sq_nonneg _)

theorem SumLcmPrimeFactorsNonneg (f θ : ℕ → ℝ) (R : ℕ)
    (hf0 : ∀ p, 0 ≤ f p) (hf1 : ∀ p, f p ≤ 1) :
    0 ≤ ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
      θ d * θ e * ∏ p ∈ (Nat.lcm d e).primeFactors, f p := by
  -- `primeFactors` turns `lcm` into a union
  have hlcm : ∀ d ∈ Finset.Icc 1 R, ∀ e ∈ Finset.Icc 1 R,
      (Nat.lcm d e).primeFactors = d.primeFactors ∪ e.primeFactors := by
    intro d hd e he
    have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
    have he0 : e ≠ 0 := by have := (Finset.mem_Icc.mp he).1; omega
    ext p
    rw [Nat.mem_primeFactors, Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hdvd, -⟩
      rcases (hp.dvd_lcm).mp hdvd with h | h
      · exact Or.inl ⟨hp, h, hd0⟩
      · exact Or.inr ⟨hp, h, he0⟩
    · rintro (⟨hp, h, -⟩ | ⟨hp, h, -⟩)
      · exact ⟨hp, h.trans (Nat.dvd_lcm_left d e), lcm_ne_zero_iff.mpr ⟨hd0, he0⟩⟩
      · exact ⟨hp, h.trans (Nat.dvd_lcm_right d e), lcm_ne_zero_iff.mpr ⟨hd0, he0⟩⟩
  -- every prime factor of `d ≤ R` lies in `primesLE R`
  have hsubset : ∀ d ∈ Finset.Icc 1 R, Nat.primeFactors d ⊆ Nat.primesLE R := by
    intro d hd
    have hd2 : d ≤ R := (Finset.mem_Icc.mp hd).2
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpd, hdne⟩ := hp
    rw [Nat.mem_primesLE]
    exact ⟨le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hdne) hpd) hd2, hpp⟩
  have hkey := nonneg_double_sum_lcm_kernel (Finset.Icc 1 R) (Nat.primesLE R) f θ
    Nat.primeFactors hf0 hf1 hsubset
  rw [show ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        θ d * θ e * ∏ p ∈ (Nat.lcm d e).primeFactors, f p
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        θ d * θ e * ∏ p ∈ (Nat.primeFactors d ∪ Nat.primeFactors e), f p from
    Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => by rw [hlcm d hd e he]))]
  exact hkey

end Work.LinnikAreas.BGTZ
