import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.SelbergWeights

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

/-!
# The Möbius inversion identity for the optimal Selberg weights (`1/φ`-density)

The optimal Selberg weights of `SelbergWeights.lean` are built from a squarefree modulus `P`,
a level `D`, the local weight `w l = ∏_{p ∣ l} (p - 2)`, the normalising constant
`G = Σ_{l ∈ T} 1/w l` on `T = selbergT D P`, the coordinates
`y l = μ l / (w l · G)` and the weights

  `λ d = φ d · Σ_{l ∈ T, d ∣ l} μ(l/d) · y l`.

The content of this file is the `linear-inverse` identity of the Selberg sieve: the triangular
system `λ d / φ d = Σ_{l : d ∣ l} μ(l/d) y l` inverts to

  `Σ_{d ∈ T, l ∣ d} λ d / φ d = y l`   for every `l ∈ T`,

which is what makes `G` the exact value of the Σ_{d,e} λ_d λ_e / φ(lcm d e) quadratic form.

The proof is Möbius inversion on the divisibility lattice: substituting the definition of `λ`
and interchanging the two (finite) summations reduces the claim to the elementary identity
`∑_{d : l ∣ d ∣ e} μ(e/d) = [e = l]`, which is `moebius_sum_div_filter_dvd` below.
-/

/-- **Möbius inversion on the divisor lattice.** For `e ≠ 0`, the sum of `μ (e / d)` over the
divisors `d` of `e` that are multiples of `l` is the indicator of `e = l`. -/
lemma sum_moebius_div_filter_dvd {e l : ℕ} (he : e ≠ 0) :
    (∑ d ∈ e.divisors.filter (fun d => l ∣ d), (ArithmeticFunction.moebius (e / d) : ℝ))
      = if e = l then (1 : ℝ) else 0 := by
  by_cases hle : l ∣ e
  · -- Reindex `d = l * a` with `a ∣ e / l`; the summand becomes `μ (e/(l a)) = μ ((e/l)/a)`,
    -- and `∑_{a ∣ m} μ (m/a) = ∑_{a ∣ m} μ a = [m = 1]`.
    have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hle (Nat.pos_of_ne_zero he)
    have hm0 : e / l ≠ 0 := fun h => he (by rw [← Nat.mul_div_cancel' hle, h, mul_zero])
    have hset : e.divisors.filter (fun d => l ∣ d) = (e / l).divisors.image (fun a => l * a) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hde, -⟩, hld⟩
        refine ⟨d / l, ⟨?_, hm0⟩, ?_⟩
        · have h1 : d = l * (d / l) := (Nat.mul_div_cancel' hld).symm
          have h2 : e = l * (e / l) := (Nat.mul_div_cancel' hle).symm
          have h3 : l * (d / l) ∣ l * (e / l) := by rw [← h1, ← h2]; exact hde
          exact (Nat.mul_dvd_mul_iff_left hl0).mp h3
        · exact Nat.mul_div_cancel' hld
      · rintro ⟨a, ⟨hae, -⟩, rfl⟩
        refine ⟨⟨?_, he⟩, dvd_mul_right l a⟩
        obtain ⟨c, hc⟩ := hae
        exact ⟨c, by rw [← Nat.mul_div_cancel' hle, hc]; ring⟩
    rw [hset, Finset.sum_image (fun x _ y _ h => Nat.mul_left_cancel hl0 h)]
    have key : (∑ a ∈ (e / l).divisors, (ArithmeticFunction.moebius (e / (l * a)) : ℝ))
        = (∑ a ∈ (e / l).divisors, (ArithmeticFunction.moebius a : ℝ)) := by
      have h1 : (∑ a ∈ (e / l).divisors, (ArithmeticFunction.moebius (e / (l * a)) : ℝ))
          = ∑ a ∈ (e / l).divisors, (ArithmeticFunction.moebius ((e / l) / a) : ℝ) :=
        Finset.sum_congr rfl fun a _ => by
          rw [(Nat.div_div_eq_div_mul e l a).symm]
      rw [h1]
      exact Nat.sum_div_divisors (e / l) (fun a => (ArithmeticFunction.moebius a : ℝ))
    rw [key]
    have hcast : (∑ a ∈ (e / l).divisors, (ArithmeticFunction.moebius a : ℝ))
        = ((∑ a ∈ (e / l).divisors, ArithmeticFunction.moebius a : ℤ) : ℝ) := by
      rw [Int.cast_sum]
    rw [hcast, Commons.NumberTheory.Moebius.sum_moebius_divisors]
    have hiff : e / l = 1 ↔ e = l := by
      constructor
      · intro h; rw [← Nat.mul_div_cancel' hle, h, mul_one]
      · intro h; rw [h, Nat.div_self hl0]
    by_cases h1 : e / l = 1
    · rw [if_pos h1, if_pos (hiff.mp h1)]; norm_num
    · rw [if_neg h1, if_neg (fun h => h1 (hiff.mpr h))]; norm_num
  · -- `l` does not divide `e`, so no divisor of `e` is a multiple of `l`: both sides vanish.
    have hempty : e.divisors.filter (fun d => l ∣ d) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun d hd => ?_
      rw [Finset.mem_filter] at hd
      exact hle (hd.2.trans (Nat.dvd_of_mem_divisors hd.1))
    rw [hempty, Finset.sum_empty, if_neg (fun h => hle (by rw [← h]))]

/-- **Inversion of the Selberg weight system.**  For `l` in the truncated divisor set
`T = selbergT D P`, the sum of the optimal Selberg coefficients `λ d / φ d` over the divisors
`d ∈ T` of the level that are multiples of `l` recovers the `y`-coordinate `y l`,
i.e. the triangular system `λ d / φ d = Σ_{l : d ∣ l} μ(l/d) y l` is inverted.

(Neither `1 ≤ D` nor the squarefreeness of `P` is needed for this purely divisor-theoretic
identity; they are kept because they are part of the calling context.) -/
theorem selbergLam_linv (D P : ℕ) (hD : 1 ≤ D) (hPsq : Squarefree P) {l : ℕ}
    (hl : l ∈ Work.NumberTheory.Chen.BTermCount.selbergT D P) :
    (∑ d ∈ (Work.NumberTheory.Chen.BTermCount.selbergT D P).filter (fun d : ℕ => l ∣ d),
        Work.NumberTheory.Chen.BTermCount.selbergLam D P d / (Nat.totient d : ℝ))
      = Work.NumberTheory.Chen.BTermCount.selbergY D P l := by
  classical
  have _ := hD
  have _ := hPsq
  -- membership description of `selbergT D P`
  have hmemT : ∀ d : ℕ, d ∈ selbergT D P ↔ 1 ≤ d ∧ d ≤ D ∧ d ∣ P := by
    intro d
    simp only [selbergT, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  -- Step 1: divide the definition of `λ` by `φ d` (legitimate because `d ≥ 1` on `T`).
  have hpt : ∀ d ∈ selbergT D P, selbergLam D P d / (Nat.totient d : ℝ)
      = ∑ l' ∈ selbergT D P,
          (if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * selbergY D P l' else 0) := by
    intro d hd
    have hd0 : (Nat.totient d : ℝ) ≠ 0 := by
      have h1 : 0 < d := ((hmemT d).mp hd).1
      exact_mod_cast (Nat.totient_pos.mpr h1).ne'
    rw [selbergLam, if_pos hd, mul_div_cancel_left₀ _ hd0]
  -- Step 2: the Möbius sum over the pairs `l ∣ d ∣ l'` collapses to the indicator of `l' = l`.
  have hinner : ∀ l' ∈ selbergT D P,
      (∑ d ∈ (selbergT D P).filter (fun d => l ∣ d ∧ d ∣ l'),
        (ArithmeticFunction.moebius (l' / d) : ℝ)) = if l' = l then 1 else 0 := by
    intro l' hl'
    have hl'0 : l' ≠ 0 := by have h1 : 1 ≤ l' := ((hmemT l').mp hl').1; omega
    have hl'P : l' ∣ P := ((hmemT l').mp hl').2.2
    have hl'D : l' ≤ D := ((hmemT l').mp hl').2.1
    -- every `d` with `l ∣ d ∣ l'` and `d ∣ P` already lies in `T`, so the two filters agree
    have hset : (selbergT D P).filter (fun d => l ∣ d ∧ d ∣ l')
        = l'.divisors.filter (fun d => l ∣ d) := by
      ext d
      rw [Finset.mem_filter, Finset.mem_filter, hmemT, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd1, hdD, hdP⟩, hld, hdl'⟩
        exact ⟨⟨hdl', hl'0⟩, hld⟩
      · rintro ⟨⟨hdl', -⟩, hld⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdl' (Nat.pos_of_ne_zero hl'0),
          le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hl'0) hdl') hl'D,
          hdl'.trans hl'P⟩, hld, hdl'⟩
    rw [hset, sum_moebius_div_filter_dvd hl'0]
  calc (∑ d ∈ (selbergT D P).filter (fun d : ℕ => l ∣ d), selbergLam D P d / (Nat.totient d : ℝ))
      = ∑ d ∈ (selbergT D P).filter (fun d => l ∣ d), ∑ l' ∈ selbergT D P,
          (if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * selbergY D P l' else 0) :=
        Finset.sum_congr rfl fun d hd => hpt d (Finset.mem_filter.mp hd).1
    _ = ∑ l' ∈ selbergT D P, ∑ d ∈ (selbergT D P).filter (fun d => l ∣ d),
          (if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * selbergY D P l' else 0) :=
        Finset.sum_comm
    _ = ∑ l' ∈ selbergT D P, (if l' = l then (1 : ℝ) else 0) * selbergY D P l' := by
        refine Finset.sum_congr rfl fun l' hl' => ?_
        rw [← Finset.sum_filter, Finset.filter_filter, ← Finset.sum_mul, hinner l' hl']
    _ = selbergY D P l := by
        rw [Finset.sum_eq_single_of_mem l hl (fun b _ hb => by rw [if_neg hb, zero_mul]),
          if_pos rfl, one_mul]

end Work.NumberTheory.Chen.BTermCount
