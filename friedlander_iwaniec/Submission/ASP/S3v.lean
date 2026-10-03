/-
  Companion paper ("Asymptotic sieve for primes"), §3: the Vaughan-type decomposition of
  `Λ(n > z)` into `L(n;y) - L(n;y,z) + Λ₁ + Λ₂ + Λ₃` (equations (3.1)–(3.2)), the identity
  behind `S(x;Z) = T(x;Y) - T(x;Y,Z) + S₁ + S₂ + S₃` (3.4).
-/
import Mathlib
import Submission.ASP.Defs
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors

namespace Submission.ASP

open Finset

noncomputable section

/-! ### A Möbius summation identity -/

/-- `∑_{b | n} μ(b) ∑_{c | n/b} g c = g n` for every `g` and `n ≥ 1`
(equivalently `μ * (g * ζ) = g`). -/
theorem sum_moebius_mul_sum_divisors_eq {g : ℕ → ℝ} (n : ℕ) (hn : 1 ≤ n) :
    (∑ b ∈ n.divisors,
        (ArithmeticFunction.moebius b : ℝ) * (∑ c ∈ (n / b).divisors, g c)) = g n := by
  have hn0 : n ≠ 0 := by omega
  -- `n / c = 1` together with `c ∣ n` forces `c = n`
  have hcdvd : ∀ c ∈ n.divisors.filter (fun c => (n / c : ℕ) = 1), c = n := by
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hcd, h1⟩ := hc
    have h2 : c * (n / c) = n := Nat.mul_div_cancel' (Nat.mem_divisors.mp hcd).1
    rw [h1, mul_one] at h2
    exact h2
  -- step 1: the inner divisor sum, viewed inside `n.divisors`
  have step1 : ∀ b ∈ n.divisors,
      (∑ c ∈ (n / b).divisors, g c)
        = ∑ c ∈ n.divisors, (if b * c ∣ n then g c else 0) := by
    intro b hb
    obtain ⟨hbd, _⟩ := Nat.mem_divisors.mp hb
    have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hbd (by omega)
    have hbn : b ≤ n := Nat.le_of_dvd (by omega) hbd
    have hset : (n / b).divisors = n.divisors.filter (fun c => b * c ∣ n) := by
      ext c
      rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hcd, _⟩
        have hmul : b * (n / b) = n := Nat.mul_div_cancel' hbd
        have h1 : b * c ∣ n := by rw [← hmul]; exact Nat.mul_dvd_mul_left b hcd
        exact ⟨⟨dvd_trans (dvd_mul_left c b) h1, hn0⟩, h1⟩
      · rintro ⟨⟨hcd, _⟩, hbc⟩
        have hmul : b * (n / b) = n := Nat.mul_div_cancel' hbd
        have hbc' : b * c ∣ b * (n / b) := by rw [hmul]; exact hbc
        exact ⟨Nat.dvd_of_mul_dvd_mul_left hb0 hbc', ne_of_gt (Nat.div_pos hbn hb0)⟩
    rw [hset, Finset.sum_filter]
  -- step 2: the inner Möbius sum in the variable `b`
  have step2 : ∀ c ∈ n.divisors,
      (∑ b ∈ n.divisors, (if b * c ∣ n then (ArithmeticFunction.moebius b : ℝ) else 0))
        = if (n / c : ℕ) = 1 then 1 else 0 := by
    intro c hc
    obtain ⟨hcd, _⟩ := Nat.mem_divisors.mp hc
    have hc0 : 0 < c := Nat.pos_of_dvd_of_pos hcd (by omega)
    have hcn : c ≤ n := Nat.le_of_dvd (by omega) hcd
    have hset : n.divisors.filter (fun b => b * c ∣ n) = (n / c).divisors := by
      ext b
      rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hbd, _⟩, hbc⟩
        have hmul : c * (n / c) = n := Nat.mul_div_cancel' hcd
        have hbc' : c * b ∣ c * (n / c) := by rw [hmul]; simpa [Nat.mul_comm] using hbc
        exact ⟨Nat.dvd_of_mul_dvd_mul_left hc0 hbc', ne_of_gt (Nat.div_pos hcn hc0)⟩
      · rintro ⟨hbd, _⟩
        have hmul : c * (n / c) = n := Nat.mul_div_cancel' hcd
        refine ⟨⟨dvd_trans hbd (Nat.div_dvd_of_dvd hcd), hn0⟩, ?_⟩
        rw [← hmul]
        simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left c hbd
    rw [← Finset.sum_filter, hset]
    have hcast : ((∑ d ∈ (n / c).divisors, ArithmeticFunction.moebius d : ℤ) : ℝ)
        = ∑ d ∈ (n / c).divisors, (ArithmeticFunction.moebius d : ℝ) := by push_cast; ring
    rw [← hcast, Commons.NumberTheory.Moebius.sum_moebius_divisors]
    by_cases h : (n / c : ℕ) = 1 <;> simp [h]
  calc (∑ b ∈ n.divisors,
        (ArithmeticFunction.moebius b : ℝ) * (∑ c ∈ (n / b).divisors, g c))
      = ∑ b ∈ n.divisors, ∑ c ∈ n.divisors,
          (ArithmeticFunction.moebius b : ℝ) * (if b * c ∣ n then g c else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [step1 b hb, Finset.mul_sum]
    _ = ∑ c ∈ n.divisors, ∑ b ∈ n.divisors,
          (ArithmeticFunction.moebius b : ℝ) * (if b * c ∣ n then g c else 0) :=
        Finset.sum_comm
    _ = ∑ c ∈ n.divisors, g c *
          (∑ b ∈ n.divisors, (if b * c ∣ n then (ArithmeticFunction.moebius b : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        by_cases h : b * c ∣ n <;> simp [h] <;> ring
    _ = ∑ c ∈ n.divisors, g c * (if (n / c : ℕ) = 1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [step2 c hc]
    _ = g n := by
        have hset : n.divisors.filter (fun c => (n / c : ℕ) = 1) = {n} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          exact ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, hn0⟩,
            by rw [Nat.div_self (by omega)]⟩, fun c hc => hcdvd c hc⟩
        have hstep : ∀ c, g c * (if (n / c : ℕ) = 1 then (1 : ℝ) else 0)
            = (if (n / c : ℕ) = 1 then g c else 0) := by
          intro c; by_cases h : (n / c : ℕ) = 1 <;> simp [h]
        rw [Finset.sum_congr rfl (fun c _ => hstep c), ← Finset.sum_filter, hset,
          Finset.sum_singleton]

/-! ### The Vaughan-type truncations of §3 -/

/-- `L(n;y,z) = F(n;y,z) = ∑_{bc | n, b ≤ y, c ≤ z} μ(b) Λ(c)`. -/
def Ltrunc (n : ℕ) (y z : ℝ) : ℝ :=
  ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
    (ArithmeticFunction.moebius b : ℝ) *
      ∑ c ∈ (n / b).divisors.filter (fun c => ((c : ℕ) : ℝ) ≤ z), ArithmeticFunction.vonMangoldt c

/-- `Λ₁(n;y,z) = ∑_{bc | n} μ(b > sy) Λ(c > sz)`. -/
def Lam1 (n : ℕ) (sy sz : ℝ) : ℝ :=
  ∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
    (ArithmeticFunction.moebius b : ℝ) *
      ∑ c ∈ (n / b).divisors.filter (fun c => sz < ((c : ℕ) : ℝ)), ArithmeticFunction.vonMangoldt c

/-- `Λ₂(n;y,z) = ∑_{bc | n} μ(y < b ≤ sy) Λ(c > z)`. -/
def Lam2 (n : ℕ) (y z sy : ℝ) : ℝ :=
  ∑ b ∈ n.divisors.filter (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy),
    (ArithmeticFunction.moebius b : ℝ) *
      ∑ c ∈ (n / b).divisors.filter (fun c => z < ((c : ℕ) : ℝ)), ArithmeticFunction.vonMangoldt c

/-- `Λ₃(n;y,z) = ∑_{bc | n} μ(b > sy) Λ(z < c ≤ sz)`. -/
def Lam3 (n : ℕ) (z sy sz : ℝ) : ℝ :=
  ∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
    (ArithmeticFunction.moebius b : ℝ) *
      ∑ c ∈ (n / b).divisors.filter (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
        ArithmeticFunction.vonMangoldt c

/-- `logWeight n y = ∑_{b | n, b ≤ y} μ(b) log(n/b)`. -/
lemma logWeight_eq_sum_log_div {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    logWeight n y = ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
      (ArithmeticFunction.moebius b : ℝ) * Real.log (((n / b : ℕ) : ℝ)) := by
  rw [logWeight]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mem_filter] at hb
  obtain ⟨hbd, _⟩ := Nat.mem_divisors.mp hb.1
  have hb0 : b ≠ 0 := (Nat.pos_of_dvd_of_pos hbd (by omega)).ne'
  have hcast : (((n / b : ℕ)) : ℝ) = (n : ℝ) / (b : ℝ) := Nat.cast_div hbd (by positivity)
  rw [hcast, Real.log_div (by positivity) (by positivity)]

/-- For `m ≥ 1`, `∑_{c | m} Λ(c)·1_{z<c} = log m − ∑_{c|m,c≤z}Λ(c)`. -/
lemma sum_ite_vonMangoldt_eq (m : ℕ) (z : ℝ) :
    (∑ c ∈ m.divisors,
        (if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0))
      = Real.log (m : ℝ) - ∑ c ∈ m.divisors.filter (fun c => ((c : ℕ) : ℝ) ≤ z),
          ArithmeticFunction.vonMangoldt c := by
  have hsplit := Finset.sum_filter_add_sum_filter_not m.divisors
    (fun c => ((c : ℕ) : ℝ) ≤ z) (fun c => ArithmeticFunction.vonMangoldt c)
  have h1 : (∑ c ∈ m.divisors,
        (if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0))
      = ∑ c ∈ m.divisors.filter (fun c => ¬ (((c : ℕ) : ℝ) ≤ z)),
          ArithmeticFunction.vonMangoldt c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : ((c : ℕ) : ℝ) ≤ z
    · simp [h]
    · rw [if_pos (not_le.mp h)]; simp [h]
  rw [h1]
  linarith [hsplit ▸ ArithmeticFunction.vonMangoldt_sum (n := m)]

/-- `∑_{c | m, z < c} Λ(c) = ∑_{c | m}(if z < c then Λ c else 0)`. -/
private lemma sum_filter_lt_eq (m : ℕ) (z : ℝ) :
    (∑ c ∈ m.divisors.filter (fun c => z < ((c : ℕ) : ℝ)), ArithmeticFunction.vonMangoldt c)
      = ∑ c ∈ m.divisors,
          (if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0) := by
  rw [Finset.sum_filter]

/-- `∑_{c | m, c ≤ z} Λ(c) = ∑_{c | m}(if c ≤ z then Λ c else 0)`. -/
private lemma sum_filter_le_eq (m : ℕ) (z : ℝ) :
    (∑ c ∈ m.divisors.filter (fun c => ((c : ℕ) : ℝ) ≤ z), ArithmeticFunction.vonMangoldt c)
      = ∑ c ∈ m.divisors,
          (if ((c : ℕ) : ℝ) ≤ z then ArithmeticFunction.vonMangoldt c else 0) := by
  rw [Finset.sum_filter]

/-- **§3, equation (3.2)**: `Λ(n > z) = L(n;y) − L(n;y,z) + Λ₁ + Λ₂ + Λ₃`. -/
theorem vonMangoldt_gt_decomp {n : ℕ} (hn : 1 ≤ n) {y z sy sz : ℝ}
    (hy_sy : y ≤ sy) (hz_sz : z ≤ sz) :
    (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0)
      = (logWeight n y - Ltrunc n y z) + Lam2 n y z sy + Lam3 n z sy sz + Lam1 n sy sz := by
  classical
  set G : ℕ → ℝ := fun c => if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0
    with hG
  have hGn : G n = if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0 := rfl
  -- the Möbius identity applied to `G`
  have hkey : G n = ∑ b ∈ n.divisors,
      (ArithmeticFunction.moebius b : ℝ) * (∑ c ∈ (n / b).divisors, G c) :=
    (sum_moebius_mul_sum_divisors_eq n hn).symm
  set F : ℕ → ℝ := fun b =>
    (ArithmeticFunction.moebius b : ℝ) * (∑ c ∈ (n / b).divisors, G c) with hF
  -- splitting the `b`-sum
  have hsplit : (∑ b ∈ n.divisors, F b)
      = (∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y), F b)
        + (∑ b ∈ n.divisors.filter (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy), F b)
        + (∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)), F b) := by
    have h1 := Finset.sum_filter_add_sum_filter_not n.divisors
      (fun b => ((b : ℕ) : ℝ) ≤ y) F
    have h2 := Finset.sum_filter_add_sum_filter_not
      (n.divisors.filter (fun b => ¬ (((b : ℕ) : ℝ) ≤ y)))
      (fun b => ((b : ℕ) : ℝ) ≤ sy) F
    have e1 : (n.divisors.filter (fun b => ¬ (((b : ℕ) : ℝ) ≤ y))).filter
          (fun b => ((b : ℕ) : ℝ) ≤ sy)
        = n.divisors.filter (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy) := by
      ext b
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hb, h1⟩, h2⟩; exact ⟨hb, not_le.mp h1, h2⟩
      · rintro ⟨hb, h1, h2⟩; exact ⟨⟨hb, not_le.mpr h1⟩, h2⟩
    have e2 : (n.divisors.filter (fun b => ¬ (((b : ℕ) : ℝ) ≤ y))).filter
          (fun b => ¬ (((b : ℕ) : ℝ) ≤ sy))
        = n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)) := by
      ext b
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hb, h1⟩, h2⟩; exact ⟨hb, not_le.mp h2⟩
      · rintro ⟨hb, h1⟩
        exact ⟨⟨hb, not_le.mpr (lt_of_le_of_lt hy_sy h1)⟩, not_le.mpr h1⟩
    rw [← h1, ← h2, e1, e2]
    ring
  -- the three pieces
  have hA : (∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y), F b)
      = logWeight n y - Ltrunc n y z := by
    have hinner : ∀ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
        (∑ c ∈ (n / b).divisors, G c)
          = Real.log (((n / b : ℕ) : ℝ))
            - ∑ c ∈ (n / b).divisors.filter (fun c => ((c : ℕ) : ℝ) ≤ z),
                ArithmeticFunction.vonMangoldt c := by
      intro b _
      simp only [hG]
      exact sum_ite_vonMangoldt_eq (n / b) z
    have h1 : (∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y), F b)
        = (∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
              (ArithmeticFunction.moebius b : ℝ) * Real.log (((n / b : ℕ) : ℝ)))
          - ∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
              (ArithmeticFunction.moebius b : ℝ)
                * ∑ c ∈ (n / b).divisors.filter (fun c => ((c : ℕ) : ℝ) ≤ z),
                    ArithmeticFunction.vonMangoldt c := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hF]
      rw [hinner b hb]
      ring
    rw [h1, ← logWeight_eq_sum_log_div hn, Ltrunc]
  have hB : (∑ b ∈ n.divisors.filter
        (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy), F b)
      = Lam2 n y z sy := by
    rw [Lam2]
    apply Finset.sum_congr rfl
    intro b _
    simp only [hF, hG]
    exact congrArg (fun x => (ArithmeticFunction.moebius b : ℝ) * x)
      (sum_filter_lt_eq (n / b) z).symm
  have hC : (∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)), F b)
      = Lam3 n z sy sz + Lam1 n sy sz := by
    have hinner : ∀ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (∑ c ∈ (n / b).divisors, G c)
          = (∑ c ∈ (n / b).divisors.filter
                (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
                ArithmeticFunction.vonMangoldt c)
            + ∑ c ∈ (n / b).divisors.filter (fun c => sz < ((c : ℕ) : ℝ)),
                ArithmeticFunction.vonMangoldt c := by
      intro b _
      simp only [hG]
      have h2 := Finset.sum_filter_add_sum_filter_not (n / b).divisors
        (fun c => ((c : ℕ) : ℝ) ≤ sz)
        (fun c => if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0)
      rw [← h2]
      congr 1
      · rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro c _
        by_cases h : ((c : ℕ) : ℝ) ≤ sz <;> simp [h]
      · rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro c _
        by_cases h : sz < ((c : ℕ) : ℝ)
        · have h1 : ¬ (((c : ℕ) : ℝ) ≤ sz) := not_le.mpr h
          have h2' : z < ((c : ℕ) : ℝ) := lt_of_le_of_lt hz_sz h
          simp [h, h1, h2']
        · have h1 : ((c : ℕ) : ℝ) ≤ sz := not_lt.mp h
          simp [h, h1]
    have h1 : (∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)), F b)
        = (∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
              (ArithmeticFunction.moebius b : ℝ)
                * ∑ c ∈ (n / b).divisors.filter
                    (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
                    ArithmeticFunction.vonMangoldt c)
          + ∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
              (ArithmeticFunction.moebius b : ℝ)
                * ∑ c ∈ (n / b).divisors.filter (fun c => sz < ((c : ℕ) : ℝ)),
                    ArithmeticFunction.vonMangoldt c := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hF]
      rw [hinner b hb]
      ring
    rw [h1, Lam3, Lam1]
  rw [← hGn, hkey, hsplit, hA, hB, hC]
  ring

/-! ### The summed identity (3.4) -/

/-- `T(x;Y,Z)` in the form `∑_{n ≤ x} aₙρₙ L(n;Y,Z)`. -/
def Tsum2L (a lam : ℕ → ℝ) (N : ℕ) (y z : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * Ltrunc n y z

/-- `S₁(x;Y,Z) = ∑_{n ≤ x} aₙρₙ Λ₁(n;Y,Z)`. -/
def S1 (a lam : ℕ → ℝ) (N : ℕ) (sy sz : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * Lam1 n sy sz

/-- `S₂(x;Y,Z) = ∑_{n ≤ x} aₙρₙ Λ₂(n;Y,Z)`. -/
def S2 (a lam : ℕ → ℝ) (N : ℕ) (y z sy : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * Lam2 n y z sy

/-- `S₃(x;Y,Z) = ∑_{n ≤ x} aₙρₙ Λ₃(n;Y,Z)`. -/
def S3 (a lam : ℕ → ℝ) (N : ℕ) (z sy sz : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * Lam3 n z sy sz

/-- **§3, equation (3.4)**: with `S(x;Z) = ∑_{n ≤ x} aₙρₙ Λ(n > Z)`,
`S(x;Z) = T(x;Y) − T(x;Y,Z) + S₁ + S₂ + S₃`. -/
theorem S_eq (a lam : ℕ → ℝ) (N : ℕ) {y z sy sz : ℝ} (hy_sy : y ≤ sy) (hz_sz : z ≤ sz) :
    (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
        (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
      = Tsum a lam (N : ℝ) y - Tsum2L a lam N y z + S2 a lam N y z sy
        + S3 a lam N z sy sz + S1 a lam N sy sz := by
  rw [Tsum, Nat.floor_natCast, Tsum2L, S1, S2, S3]
  have hstep : ∀ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
      (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0)
      = a n * rhoOf lam n * (logWeight n y - Ltrunc n y z + Lam2 n y z sy
          + Lam3 n z sy sz + Lam1 n sy sz) := by
    intro n hn
    rw [vonMangoldt_gt_decomp (Finset.mem_Icc.mp hn).1 hy_sy hz_sz]
  rw [Finset.sum_congr rfl hstep]
  have hsplit : (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
        (logWeight n y - Ltrunc n y z + Lam2 n y z sy + Lam3 n z sy sz + Lam1 n sy sz))
      = (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * logWeight n y)
        - (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * Ltrunc n y z)
        + (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * Lam2 n y z sy)
        + (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * Lam3 n z sy sz)
        + (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n * Lam1 n sy sz) := by
    rw [show (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
          (logWeight n y - Ltrunc n y z + Lam2 n y z sy + Lam3 n z sy sz + Lam1 n sy sz))
        = ∑ n ∈ Finset.Icc 1 N, (a n * rhoOf lam n * logWeight n y
            - a n * rhoOf lam n * Ltrunc n y z
            + a n * rhoOf lam n * Lam2 n y z sy
            + a n * rhoOf lam n * Lam3 n z sy sz
            + a n * rhoOf lam n * Lam1 n sy sz) from by
      apply Finset.sum_congr rfl
      intro n _
      ring]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit]


end

end Submission.ASP
