/-
  Companion paper ("Asymptotic sieve for primes"), §3: the identification of the two forms of
  `T(x; y, z)` — the `∑_{b ≤ y} μ(b) ∑_{c ≤ z} Λ(c) V_{bc}(x)` form of (5.1) and the
  `∑_{n ≤ x} aₙρₙ L(n; y, z)` form used in (3.4) — and, more generally, the triple/divisor
  exchange underlying the estimates of §§5–8.
-/
import Mathlib
import Submission.ASP.Defs
import Submission.ASP.S3v

namespace Submission.ASP

open Finset

noncomputable section

/-- For `0 < n ≤ N`, the divisors of `n` satisfying a predicate `p` are exactly the elements
of `Icc 1 N` that divide `n` and satisfy `p`. -/
lemma divisors_filter_eq' {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) (p : ℕ → Prop)
    [DecidablePred p] :
    n.divisors.filter p = (Finset.Icc 1 N).filter (fun b => b ∣ n ∧ p b) := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hn0 : n ≠ 0 := by omega
  ext b
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hbd, _⟩, hpb⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hbd (by omega),
      le_trans (Nat.le_of_dvd (by omega) hbd) hnN⟩, hbd, hpb⟩
  · rintro ⟨_, hbd, hpb⟩
    exact ⟨⟨hbd, hn0⟩, hpb⟩

/-- Exchange the order of summation in `∑_{n ≤ N} ∑_{b ∣ n, p b}`. -/
theorem sum_divisors_filter_swap' {N : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ b ∈ n.divisors.filter p, F n b)
      = ∑ b ∈ (Finset.Icc 1 N).filter p,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n), F n b := by
  have hL : (∑ n ∈ Finset.Icc 1 N, ∑ b ∈ n.divisors.filter p, F n b)
      = ∑ n ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          (if b ∣ n ∧ p b then F n b else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [divisors_filter_eq' hn, Finset.sum_filter]
  rw [hL, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : p b
  · rw [if_pos hb]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hbn : b ∣ n <;> simp [hbn, hb]
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro n _
    by_cases hbn : b ∣ n <;> simp [hbn, hb]

/-- Reindexing a divisor-filtered interval sum: for `p ≥ 1`,
`∑_{n ≤ N, p ∣ n} f n = ∑_{m ≤ N/p} f (p m)`. -/
lemma sum_filter_dvd_eq' {p N : ℕ} (hp : 0 < p) (f : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), f n)
      = ∑ m ∈ Finset.Icc 1 (N / p), f (p * m) := by
  refine Finset.sum_bij' (fun n _ => n / p) (fun m _ => p * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnIcc, hpn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnIcc
    have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hp).mpr hple, Nat.div_le_div_right hnN⟩
  · intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), by
      calc p * m ≤ p * (N / p) := Nat.mul_le_mul_left p hmN
        _ ≤ N := Nat.mul_div_le N p⟩, dvd_mul_right p m⟩
  · intro n hn
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
  · intro m _
    exact Nat.mul_div_right m hp
  · intro n hn
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

/-- **The triple/divisor exchange**: for any `G`, any `N` and any predicates `p`, `q`,
```
∑_{b ≤ N, p b} μ(b) ∑_{c ≤ N, q c} Λ(c) ∑_{d ≤ N, bc ∣ d} G d
   = ∑_{n ≤ N} G n ∑_{b ∣ n, p b} μ(b) ∑_{c ∣ n/b, q c} Λ(c) .
```
-/
lemma sum_triple_filter (G : ℕ → ℝ) (N : ℕ) (p q : ℕ → Prop)
    [DecidablePred p] [DecidablePred q] :
    (∑ b ∈ (Finset.Icc 1 N).filter p,
        (ArithmeticFunction.moebius b : ℝ) *
          ∑ c ∈ (Finset.Icc 1 N).filter q,
            ArithmeticFunction.vonMangoldt c *
              ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n), G n)
      = ∑ n ∈ Finset.Icc 1 N, G n *
          ∑ b ∈ n.divisors.filter p,
            (ArithmeticFunction.moebius b : ℝ) *
              ∑ c ∈ (n / b).divisors.filter q,
                ArithmeticFunction.vonMangoldt c := by
  classical
  -- Step 1: for each `b`, rewrite the inner `(c, n)` sum into a sum over `m = n / b`.
  have h1 : ∀ b ∈ (Finset.Icc 1 N).filter p,
      (∑ c ∈ (Finset.Icc 1 N).filter q,
            ArithmeticFunction.vonMangoldt c *
              ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n), G n)
        = ∑ m ∈ Finset.Icc 1 (N / b),
            G (b * m) * ∑ c ∈ m.divisors.filter q,
              ArithmeticFunction.vonMangoldt c := by
    intro b hb
    obtain ⟨hbIcc, hpb⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hbIcc
    have hbpos : 0 < b := hb1
    have stepA : ∀ c, ArithmeticFunction.vonMangoldt c *
          (∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n), G n)
        = ∑ m ∈ Finset.Icc 1 (N / b),
            ArithmeticFunction.vonMangoldt c * (if c ∣ m then G (b * m) else 0) := by
      intro c
      rw [Finset.mul_sum]
      rw [show (∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n),
              ArithmeticFunction.vonMangoldt c * G n)
            = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n),
              (if b * c ∣ n then ArithmeticFunction.vonMangoldt c * G n else 0) from by
          rw [Finset.sum_filter, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n _
          by_cases h : b * c ∣ n
          · have hb' : b ∣ n := dvd_trans (dvd_mul_right b c) h
            simp [h, hb']
          · by_cases hb' : b ∣ n <;> simp [h, hb']]
      rw [sum_filter_dvd_eq' hbpos]
      apply Finset.sum_congr rfl
      intro m _
      by_cases h : c ∣ m
      · rw [if_pos h, if_pos (Nat.mul_dvd_mul_left b h)]
      · rw [if_neg h, if_neg (fun hbc => h (Nat.dvd_of_mul_dvd_mul_left hbpos hbc)), mul_zero]
    rw [Finset.sum_congr rfl (fun c _ => stepA c), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hmIcc : m ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨hm1, le_trans hmN (Nat.div_le_self N b)⟩
    have hfilter : ((Finset.Icc 1 N).filter q).filter (fun c => c ∣ m)
        = m.divisors.filter q := by
      rw [Finset.filter_filter, divisors_filter_eq' hmIcc q]
      apply Finset.filter_congr
      intro c _
      exact and_comm
    have e1 : (∑ c ∈ (Finset.Icc 1 N).filter q,
            ArithmeticFunction.vonMangoldt c * (if c ∣ m then G (b * m) else 0))
        = ∑ c ∈ (Finset.Icc 1 N).filter q,
            (if c ∣ m then ArithmeticFunction.vonMangoldt c * G (b * m) else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : c ∣ m <;> simp [h]
    have e2 : (∑ c ∈ (Finset.Icc 1 N).filter q,
            (if c ∣ m then ArithmeticFunction.vonMangoldt c * G (b * m) else 0))
        = (∑ c ∈ (((Finset.Icc 1 N).filter q).filter (fun c => c ∣ m)),
              ArithmeticFunction.vonMangoldt c) * G (b * m) := by
      rw [← Finset.sum_filter, Finset.sum_mul]
    rw [e1, e2, hfilter]
    ring
  -- Step 2: reindex `m ↦ n = b m`.
  have h2 : (∑ b ∈ (Finset.Icc 1 N).filter p,
        (ArithmeticFunction.moebius b : ℝ) *
          ∑ m ∈ Finset.Icc 1 (N / b),
            G (b * m) * ∑ c ∈ m.divisors.filter q,
              ArithmeticFunction.vonMangoldt c)
      = ∑ b ∈ (Finset.Icc 1 N).filter p,
        (ArithmeticFunction.moebius b : ℝ) *
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n),
            G n * ∑ c ∈ (n / b).divisors.filter q,
              ArithmeticFunction.vonMangoldt c := by
    apply Finset.sum_congr rfl
    intro b hb
    obtain ⟨hbIcc, hpb⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hbIcc
    have hbpos : 0 < b := hb1
    congr 1
    trans ∑ m ∈ Finset.Icc 1 (N / b),
        (fun n => G n * ∑ c ∈ (n / b).divisors.filter q,
          ArithmeticFunction.vonMangoldt c) (b * m)
    · apply Finset.sum_congr rfl
      intro m _
      dsimp only
      rw [Nat.mul_div_right m hbpos]
    · exact (sum_filter_dvd_eq' hbpos (fun n => G n *
        ∑ c ∈ (n / b).divisors.filter q,
          ArithmeticFunction.vonMangoldt c)).symm
  -- Step 3: the outer `(b, n)` swap.
  rw [Finset.sum_congr rfl (fun b hb => by rw [h1 b hb]), h2]
  have h3 : (∑ b ∈ (Finset.Icc 1 N).filter p,
        (ArithmeticFunction.moebius b : ℝ) *
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n),
            G n * ∑ c ∈ (n / b).divisors.filter q,
              ArithmeticFunction.vonMangoldt c)
      = ∑ b ∈ (Finset.Icc 1 N).filter p,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n),
            (ArithmeticFunction.moebius b : ℝ) *
              (G n * ∑ c ∈ (n / b).divisors.filter q,
                ArithmeticFunction.vonMangoldt c) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
  rw [h3, (sum_divisors_filter_swap' p (fun n b =>
        (ArithmeticFunction.moebius b : ℝ) *
          (G n * ∑ c ∈ (n / b).divisors.filter q,
            ArithmeticFunction.vonMangoldt c))).symm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The `T(x;y,z)` instance of the triple/divisor exchange. -/
lemma Tsum2_aux (G : ℕ → ℝ) (N : ℕ) (_hN : 1 ≤ N) (y z : ℝ) :
    (∑ b ∈ (Finset.Icc 1 N).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
        (ArithmeticFunction.moebius b : ℝ) *
          ∑ c ∈ (Finset.Icc 1 N).filter (fun c => ((c : ℕ) : ℝ) ≤ z),
            ArithmeticFunction.vonMangoldt c *
              ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n), G n)
      = ∑ n ∈ Finset.Icc 1 N, G n *
          ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
            (ArithmeticFunction.moebius b : ℝ) *
              ∑ c ∈ (n / b).divisors.filter (fun c => ((c : ℕ) : ℝ) ≤ z),
                ArithmeticFunction.vonMangoldt c :=
  sum_triple_filter G N (fun b => ((b : ℕ) : ℝ) ≤ y) (fun c => ((c : ℕ) : ℝ) ≤ z)

/-- **§3 bridge**: the two ways of writing `T(x; y, z)` agree. -/
theorem Tsum2_eq_Tsum2L (a lam : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) (y z : ℝ) :
    Tsum2 a lam (N : ℝ) y z = Tsum2L a lam N y z := by
  unfold Tsum2 Tsum2L Vb Ltrunc
  simp only [Nat.floor_natCast]
  exact Tsum2_aux (fun n => a n * rhoOf lam n) N hN y z

/-- **§3, equation (3.4)** in terms of the objects of `Defs`: with
`S(x;Z) = ∑_{n ≤ x} aₙρₙ Λ(n > Z)`,
`S(x;Z) = T(x;Y) − T(x;Y,Z) + S₁ + S₂ + S₃`, where `T(x;Y,Z)` is `Defs.Tsum2`. -/
theorem S_eq' (a lam : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) {y z sy sz : ℝ}
    (hy_sy : y ≤ sy) (hz_sz : z ≤ sz) :
    (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
        (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
      = Tsum a lam (N : ℝ) y - Tsum2 a lam (N : ℝ) y z + S2 a lam N y z sy
        + S3 a lam N z sy sz + S1 a lam N sy sz := by
  rw [S_eq a lam N hy_sy hz_sz, ← Tsum2_eq_Tsum2L a lam N hN y z]

/-- **§6 (and §7, §8), the `S₁` bridge**: the "combinatorial" form of `S₁` (summing over
`b c d ≤ x` with `b > sy`, `c > sz`) equals the divisor form `∑_{n ≤ x} aₙρₙ Λ₁(n; sy, sz)`
of §3/`S3v`. -/
theorem S1_eq_triple (a lam : ℕ → ℝ) (N : ℕ) (sy sz : ℝ) :
    S1 a lam N sy sz
      = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (Finset.Icc 1 N).filter (fun c => sz < ((c : ℕ) : ℝ)),
              ArithmeticFunction.vonMangoldt c *
                ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n),
                  a n * rhoOf lam n := by
  unfold S1 Lam1
  exact (sum_triple_filter (fun n => a n * rhoOf lam n) N
    (fun b => sy < ((b : ℕ) : ℝ)) (fun c => sz < ((c : ℕ) : ℝ))).symm

end

end Submission.ASP
