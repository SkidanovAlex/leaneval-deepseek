/-
  Companion paper ("Asymptotic sieve for primes"), §6: estimation of `S₁(x;Y,Z)`.
  This file contains the combinatorial reduction (the "dropping of `μ(b)`", (6.1)–(6.3)).
-/
import Mathlib
import Submission.ASP.Defs
import Submission.ASP.S3v
import Submission.ASP.S3w
import Submission.Work.FIChain.LocalS5
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_div_sub_log_bounded

namespace Submission.ASP

open Finset

noncomputable section

/-- The summand `aₙρₙ` of the companion paper. -/
def Gseq (a lam : ℕ → ℝ) (n : ℕ) : ℝ := a n * rhoOf lam n

lemma Gseq_nonneg {a lam : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hrho : ∀ n, 0 ≤ rhoOf lam n)
    (n : ℕ) : 0 ≤ Gseq a lam n := mul_nonneg (ha n) (hrho n)

/-- The range `{b ∈ [1,N] : y < b}` of §6 (the "`b > y`" of a truncated sum). -/
def seg (N : ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun b => y < ((b : ℕ) : ℝ))

/-- The `c`-range (6.1) of §6: `sz < c ≤ N/sy`.  The truncation `c ≤ N/sy` is automatic
for every `c` that actually occurs in `S₁`, since `b > sy` and `b c d ≤ N` force `c < N/sy`. -/
def cseg (N : ℕ) (sz sy : ℝ) : Finset ℕ :=
  (seg N sz).filter (fun c => ((c : ℕ) : ℝ) ≤ (N : ℝ) / sy)

/-! ### §6: dropping `μ(b)` -/

/-- **§6, (6.1)–(6.3), first step**: for `a ≥ 0`, `ρ ≥ 0` and `sy ≥ 0`, dropping `μ(b)` we get
```
|S₁(x; sy, sz)| ≤ ∑_{sz < c} Λ(c) ∑_{d : (⌊sy⌋+1) c d ≤ N} V_{cd}(x) ,
```
the truncation on `d` keeping exactly the pairs for which some `b > sy` with `b c d ≤ N` exists;
`δ₂` bounds `N/(bc)` for `b > sy`, `c > sz`, so that `d ≤ δ₂` for the surviving pairs. -/
lemma S1_le_Vb (a lam : ℕ → ℝ) (N : ℕ) {sy sz : ℝ} {δ2 : ℕ}
    (ha : ∀ n, 0 ≤ a n) (hrho : ∀ n, 0 ≤ rhoOf lam n) (hsy : 0 < sy)
    (hδ2 : ∀ b c : ℕ, sy < (b : ℝ) → sz < (c : ℝ) → N / (b * c) ≤ δ2) :
    |S1 a lam N sy sz| ≤
      ∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
          ∑ d ∈ (Finset.Icc 1 δ2).filter (fun d => (⌊sy⌋₊ + 1) * c * d ≤ N),
            Vb a lam (c * d) N := by
  classical
  have hGnn : ∀ n, 0 ≤ Gseq a lam n := Gseq_nonneg ha hrho
  have hS1 : S1 a lam N sy sz =
      ∑ b ∈ seg N sy, (ArithmeticFunction.moebius b : ℝ) *
          ∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
              ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n), Gseq a lam n := by
    simpa only [seg, Gseq] using S1_eq_triple a lam N sy sz
  have h1 : |S1 a lam N sy sz| ≤
      ∑ b ∈ seg N sy, ∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
            ∑ d ∈ Finset.Icc 1 (N / (b * c)), Gseq a lam (b * c * d) := by
    rw [hS1]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    apply Finset.sum_le_sum
    intro b hb
    rw [abs_mul]
    have hμ : |(((ArithmeticFunction.moebius b : ℤ)) : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := b)
      rw [← Int.cast_abs]
      exact_mod_cast h
    have hcnn : 0 ≤ ∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n), Gseq a lam n := by
      apply Finset.sum_nonneg
      intro c _
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Finset.sum_nonneg (fun n _ => hGnn n))
    calc |(((ArithmeticFunction.moebius b : ℤ)) : ℝ)| *
          |∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
              ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n), Gseq a lam n|
        = |(((ArithmeticFunction.moebius b : ℤ)) : ℝ)| *
          (∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
              ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n), Gseq a lam n) := by
          rw [abs_of_nonneg hcnn]
      _ ≤ 1 * (∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
              ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n), Gseq a lam n) :=
          mul_le_mul_of_nonneg_right hμ hcnn
      _ = ∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
            ∑ d ∈ Finset.Icc 1 (N / (b * c)), Gseq a lam (b * c * d) := by
          rw [one_mul]
          apply Finset.sum_congr rfl
          intro c hc
          have hc1 : 1 ≤ c := (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
          have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
          rw [sum_filter_dvd_eq' (p := b * c) (by positivity : 0 < b * c)
            (fun n => Gseq a lam n)]
  have h2 : ∀ c ∈ seg N sz,
      (∑ b ∈ seg N sy, ∑ d ∈ Finset.Icc 1 (N / (b * c)), Gseq a lam (b * c * d))
        ≤ ∑ d ∈ (Finset.Icc 1 δ2).filter (fun d => (⌊sy⌋₊ + 1) * c * d ≤ N),
            Vb a lam (c * d) N := by
    intro c hc
    obtain ⟨hcIcc, hcsz⟩ := Finset.mem_filter.mp hc
    obtain ⟨hc1, hcN⟩ := Finset.mem_Icc.mp hcIcc
    have hcpos : 0 < c := hc1
    have hreshape : (∑ b ∈ seg N sy, ∑ d ∈ Finset.Icc 1 (N / (b * c)), Gseq a lam (b * c * d))
        = ∑ b ∈ seg N sy, ∑ d ∈ Finset.Icc 1 δ2,
            (if b * c * d ≤ N then Gseq a lam (b * c * d) else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨hbIcc, hbsy⟩ := Finset.mem_filter.mp hb
      obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hbIcc
      have hbc : 0 < b * c := by positivity
      have hset : Finset.Icc 1 (N / (b * c))
          = (Finset.Icc 1 δ2).filter (fun d => b * c * d ≤ N) := by
        ext d
        rw [Finset.mem_Icc, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨hd1, hdle⟩
          refine ⟨⟨hd1, le_trans hdle (hδ2 b c hbsy hcsz)⟩, ?_⟩
          have := (Nat.le_div_iff_mul_le hbc).mp hdle
          calc b * c * d = d * (b * c) := by ring
            _ ≤ N := this
        · rintro ⟨⟨hd1, _⟩, hbcd⟩
          refine ⟨hd1, (Nat.le_div_iff_mul_le hbc).mpr ?_⟩
          calc d * (b * c) = b * c * d := by ring
            _ ≤ N := hbcd
      rw [hset, Finset.sum_filter]
    rw [hreshape, Finset.sum_comm]
    -- the inner `b`-sum is empty as soon as `(⌊sy⌋+1) c d > N`
    have hzero : ∀ d ∈ Finset.Icc 1 δ2, ¬ ((⌊sy⌋₊ + 1) * c * d ≤ N) →
        (∑ b ∈ (seg N sy).filter (fun b => b * c * d ≤ N), Gseq a lam (b * c * d)) = 0 := by
      intro d _ hdf
      rw [Finset.sum_eq_zero]
      intro b hb
      obtain ⟨hbsy, hbcd⟩ := Finset.mem_filter.mp hb
      have hbsy' : sy < (b : ℝ) := (Finset.mem_filter.mp hbsy).2
      have hbf : ⌊sy⌋₊ + 1 ≤ b := by
        have h1 : ⌊sy⌋₊ < b := (Nat.floor_lt (le_of_lt hsy)).mpr hbsy'
        omega
      have hle : (⌊sy⌋₊ + 1) * c * d ≤ b * c * d :=
        Nat.mul_le_mul_right d (Nat.mul_le_mul_right c hbf)
      exact absurd (le_trans hle hbcd) hdf
    have hif : (∑ d ∈ Finset.Icc 1 δ2, ∑ b ∈ seg N sy,
            (if b * c * d ≤ N then Gseq a lam (b * c * d) else 0))
        = ∑ d ∈ Finset.Icc 1 δ2,
            (if (⌊sy⌋₊ + 1) * c * d ≤ N then
              ∑ b ∈ (seg N sy).filter (fun b => b * c * d ≤ N), Gseq a lam (b * c * d)
              else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdf : (⌊sy⌋₊ + 1) * c * d ≤ N
      · rw [if_pos hdf]
        exact (Finset.sum_filter (s := seg N sy) (p := fun b => b * c * d ≤ N)
          (f := fun b => Gseq a lam (b * c * d))).symm
      · rw [if_neg hdf]
        rw [(Finset.sum_filter (s := seg N sy) (p := fun b => b * c * d ≤ N)
          (f := fun b => Gseq a lam (b * c * d))).symm, hzero d hd hdf]
    have hfilter : (∑ d ∈ Finset.Icc 1 δ2,
            (if (⌊sy⌋₊ + 1) * c * d ≤ N then
              ∑ b ∈ (seg N sy).filter (fun b => b * c * d ≤ N), Gseq a lam (b * c * d)
              else 0))
        = ∑ d ∈ (Finset.Icc 1 δ2).filter (fun d => (⌊sy⌋₊ + 1) * c * d ≤ N),
            ∑ b ∈ (seg N sy).filter (fun b => b * c * d ≤ N),
              Gseq a lam (b * c * d) :=
      (Finset.sum_filter (s := Finset.Icc 1 δ2)
        (p := fun d => (⌊sy⌋₊ + 1) * c * d ≤ N)
        (f := fun d => ∑ b ∈ (seg N sy).filter (fun b => b * c * d ≤ N),
          Gseq a lam (b * c * d))).symm
    rw [hif, hfilter]
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hdIcc, hdf⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hdIcc
    have hdpos : 0 < d := hd1
    have hinj : Set.InjOn (fun b => b * c * d)
        ↑((seg N sy).filter (fun b => b * c * d ≤ N)) := by
      intro x _ y _ hxy
      have h1 : x * c = y * c := Nat.mul_right_cancel hdpos hxy
      exact Nat.mul_right_cancel hcpos h1
    have hsub : ((seg N sy).filter (fun b => b * c * d ≤ N)).image (fun b => b * c * d)
        ⊆ (Finset.Icc 1 N).filter (fun n => c * d ∣ n) := by
      intro n hn
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hb', hbcd⟩ := Finset.mem_filter.mp hb
      obtain ⟨hbIcc, hbsy⟩ := Finset.mem_filter.mp hb'
      obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hbIcc
      have hb0 : b ≠ 0 := by omega
      have hc0 : c ≠ 0 := by omega
      have hd0 : d ≠ 0 := by omega
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.mul_ne_zero hb0 hc0) hd0),
        hbcd⟩, by
        have : c * d ∣ b * (c * d) := dvd_mul_left (c * d) b
        calc c * d ∣ (b * c) * d := by simpa [Nat.mul_assoc] using this
          _ = b * c * d := rfl⟩
    calc (∑ b ∈ (seg N sy).filter (fun b => b * c * d ≤ N), Gseq a lam (b * c * d))
        = ∑ n ∈ ((seg N sy).filter (fun b => b * c * d ≤ N)).image (fun b => b * c * d),
            Gseq a lam n := (Finset.sum_image hinj).symm
      _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => c * d ∣ n), Gseq a lam n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hGnn n)
      _ = Vb a lam (c * d) N := by
          rw [Vb, Nat.floor_natCast]
          simp only [Gseq]
  -- the terms with `c > N/sy` have an empty `d`-range
  have hcrestrict : (∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
          ∑ d ∈ (Finset.Icc 1 δ2).filter (fun d => (⌊sy⌋₊ + 1) * c * d ≤ N), Vb a lam (c * d) N)
      = ∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
          ∑ d ∈ (Finset.Icc 1 δ2).filter (fun d => (⌊sy⌋₊ + 1) * c * d ≤ N),
            Vb a lam (c * d) N := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro c hc hnot
    have hzero : (∑ d ∈ (Finset.Icc 1 δ2).filter (fun d => (⌊sy⌋₊ + 1) * c * d ≤ N),
        Vb a lam (c * d) N) = 0 := by
      rw [Finset.sum_eq_zero]
      intro d hd
      exact absurd (Finset.mem_filter.mpr ⟨hc, by
        have hcd : (⌊sy⌋₊ + 1) * c ≤ (⌊sy⌋₊ + 1) * c * d := by
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
          calc (⌊sy⌋₊ + 1) * c = (⌊sy⌋₊ + 1) * c * 1 := by ring
            _ ≤ (⌊sy⌋₊ + 1) * c * d := Nat.mul_le_mul_left _ hd1
        have hcN : c ≤ N / (⌊sy⌋₊ + 1) :=
          (Nat.le_div_iff_mul_le (by omega)).mpr (by
            rw [Nat.mul_comm]
            exact le_trans hcd (Finset.mem_filter.mp hd).2)
        exact le_trans (le_trans (Nat.cast_le.mpr hcN) (Nat.cast_div_le)) (by
          apply div_le_div_of_nonneg_left (by positivity) hsy
          rw [Nat.cast_add, Nat.cast_one]
          exact le_of_lt (Nat.lt_floor_add_one sy))⟩) hnot
    rw [hzero, mul_zero]
  calc |S1 a lam N sy sz|
      ≤ ∑ b ∈ seg N sy, ∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
            ∑ d ∈ Finset.Icc 1 (N / (b * c)), Gseq a lam (b * c * d) := h1
    _ = ∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
          ∑ b ∈ seg N sy, ∑ d ∈ Finset.Icc 1 (N / (b * c)), Gseq a lam (b * c * d) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
    _ ≤ ∑ c ∈ seg N sz, ArithmeticFunction.vonMangoldt c *
          ∑ d ∈ (Finset.Icc 1 δ2).filter (fun d => (⌊sy⌋₊ + 1) * c * d ≤ N),
            Vb a lam (c * d) N := by
        apply Finset.sum_le_sum
        intro c hc
        exact mul_le_mul_of_nonneg_left (h2 c hc) ArithmeticFunction.vonMangoldt_nonneg
    _ = ∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
          ∑ d ∈ (Finset.Icc 1 δ2).filter (fun d => (⌊sy⌋₊ + 1) * c * d ≤ N),
            Vb a lam (c * d) N := hcrestrict

/-! ### The insertion of (1.7) -/

/-- `lcm(ν, c·d) = c·lcm(ν,d)` when `c` is coprime to `ν` and to `d`. -/
lemma lcm_mul_left_coprime {c d ν : ℕ} (hcd : Nat.Coprime c d) (hcν : Nat.Coprime c ν) :
    Nat.lcm ν (c * d) = c * Nat.lcm ν d := by
  have h : Nat.Coprime c (ν * d) := hcν.mul_right hcd
  have hc : Nat.Coprime c (Nat.lcm ν d) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul ν d) h
  refine Nat.dvd_antisymm ?_ ?_
  · rw [Nat.lcm_dvd_iff]
    exact ⟨(Nat.dvd_lcm_left ν d).mul_left c, Nat.mul_dvd_mul_left c (Nat.dvd_lcm_right ν d)⟩
  · have h1 : c ∣ Nat.lcm ν (c * d) :=
      dvd_trans (dvd_mul_right c d) (Nat.dvd_lcm_right ν (c * d))
    have h2 : Nat.lcm ν d ∣ Nat.lcm ν (c * d) :=
      Nat.lcm_dvd (Nat.dvd_lcm_left ν (c * d))
        (dvd_trans (dvd_mul_left d c) (Nat.dvd_lcm_right ν (c * d)))
    have h3 : Nat.lcm c (Nat.lcm ν d) ∣ Nat.lcm ν (c * d) := Nat.lcm_dvd h1 h2
    rwa [hc.lcm_eq_mul] at h3

/-- A squarefree integer with nonzero von Mangoldt weight is a prime. -/
lemma prime_of_squarefree_vonMangoldt_ne_zero {c : ℕ} (hsf : Squarefree c)
    (hv : ArithmeticFunction.vonMangoldt c ≠ 0) : c.Prime := by
  obtain ⟨p, k, hp, hkpos, hk⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hv
  have hpn : Nat.Prime p := Nat.prime_iff.mpr hp
  have hk1 : k = 1 := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos) with ⟨j, rfl⟩
    cases j with
    | zero => rfl
    | succ j =>
      exfalso
      refine Nat.squarefree_iff_prime_squarefree.mp hsf p hpn ⟨p ^ j, ?_⟩
      rw [← hk, ← pow_two, ← pow_add]
      congr 1
      omega
  rw [hk1, pow_one] at hk
  exact hk ▸ hpn

/-- The `d`-range of §6 for a fixed `c`. -/
def dseg (N : ℕ) (sy : ℝ) (δ2 c : ℕ) : Finset ℕ :=
  (Finset.Icc 1 δ2).filter (fun d => (⌊sy⌋₊ + 1) * c * d ≤ N)

/-- `M(x)` of §6, (6.3)/(6.5): `∑_{d ≤ δ₂, ♭} ∑_{ν ≤ Δ} λ_ν g([d,ν])`. -/
def M6 (g lam : ℕ → ℝ) (δ2 Δ : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 δ2).filter Squarefree,
    ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν d)

/-- `L(x)` of §6, (6.3)/(6.4): `∑_{c ∈ (6.1), ♭} Λ(c) g(c)`. -/
def L6 (g : ℕ → ℝ) (N : ℕ) (sz sy : ℝ) : ℝ :=
  ∑ c ∈ (cseg N sz sy).filter Squarefree, ArithmeticFunction.vonMangoldt c * g c

/-- **§6, the insertion of (1.7)**: for `b` a modulus,
`V_b(x) = A(x)·∑_{ν ≤ Δ} λ_ν g([ν,b]) + ∑_{ν ≤ Δ} λ_ν r_{[ν,b]}(x)`. -/
lemma Vb_eq_Icc (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (lam : ℕ → ℝ) (N b : ℕ) {Δ : ℕ}
    (happ : Approx a g r (N : ℝ)) (hΔN : Δ ≤ N)
    (hsupp : ∀ ν, ν ∉ Finset.Icc 1 Δ → lam ν = 0) :
    Vb a lam b (N : ℝ)
      = ∑ ν ∈ Finset.Icc 1 Δ,
          lam ν * (g (Nat.lcm ν b) * Acount a (N : ℝ) + r (Nat.lcm ν b) N) := by
  rw [Vb_eq_sum_lcm, Nat.floor_natCast]
  rw [(Finset.sum_subset (Finset.Icc_subset_Icc_right hΔN)
      (fun x _ hx => by rw [hsupp x hx, zero_mul])).symm]
  apply Finset.sum_congr rfl
  intro ν _
  rw [happ (Nat.lcm ν b) N]

/-! ### §6, (6.3): splitting off the main term -/

/-- **§6, (6.3)**: after inserting (1.7) into the reduced form of `S₁`, the main terms factor as
`A(x)·L(x)·M(x)` and the remainders are collected in the last sum. -/
theorem S1_le_main_rem (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (lam : ℕ → ℝ) (N : ℕ)
    {sy sz : ℝ} {δ2 Δ : ℕ}
    (ha : ∀ n, 0 ≤ a n) (hrho : ∀ n, 0 ≤ rhoOf lam n) (hsy : 0 < sy)
    (hδ2 : ∀ b c : ℕ, sy < (b : ℝ) → sz < (c : ℝ) → N / (b * c) ≤ δ2)
    (ha_sq : ∀ n, ¬ Squarefree n → a n = 0)
    (happ : Approx a g r (N : ℝ)) (hΔN : Δ ≤ N)
    (hsupp : ∀ ν, ν ∉ Finset.Icc 1 Δ → lam ν = 0)
    (hΔsz : (Δ : ℝ) < sz)
    (hg : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hgnn : ∀ n, 0 ≤ g n)
    (hpos : ∀ d, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν d)) :
    |S1 a lam N sy sz| ≤
      Acount a (N : ℝ) * L6 g N sz sy * M6 g lam δ2 Δ
        + ∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
            ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
              |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0) := by
  classical
  refine le_trans (S1_le_Vb a lam N ha hrho hsy hδ2) ?_
  have hAnn : 0 ≤ Acount a (N : ℝ) := Finset.sum_nonneg (fun n _ => ha n)
  have hM6nn : 0 ≤ M6 g lam δ2 Δ := by
    unfold M6
    exact Finset.sum_nonneg (fun d _ => hpos d)
  -- Step 1: only squarefree `c` contribute
  have hsingle : (∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
        ∑ d ∈ dseg N sy δ2 c, Vb a lam (c * d) N)
      = ∑ c ∈ (cseg N sz sy).filter Squarefree, ArithmeticFunction.vonMangoldt c *
        ∑ d ∈ dseg N sy δ2 c,
          (if Squarefree (c * d) then Vb a lam (c * d) N else 0) := by
    have hrest : (∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
          ∑ d ∈ dseg N sy δ2 c, Vb a lam (c * d) N)
        = ∑ c ∈ (cseg N sz sy).filter Squarefree, ArithmeticFunction.vonMangoldt c *
          ∑ d ∈ dseg N sy δ2 c, Vb a lam (c * d) N := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro c hc hnot
      have hnsf : ¬ Squarefree c := fun h => hnot (Finset.mem_filter.mpr ⟨hc, h⟩)
      have hzd : ∀ d, Vb a lam (c * d) N = 0 := by
        intro d
        refine Vb_eq_zero_of_not_squarefree ha_sq ?_ N
        intro hcd_sf
        exact hnsf (Squarefree.squarefree_of_dvd (dvd_mul_right c d) hcd_sf)
      rw [Finset.sum_eq_zero (fun d _ => hzd d), mul_zero]
    rw [hrest]
    apply Finset.sum_congr rfl
    intro c _
    have hif : (∑ d ∈ dseg N sy δ2 c, Vb a lam (c * d) N)
        = ∑ d ∈ dseg N sy δ2 c,
            (if Squarefree (c * d) then Vb a lam (c * d) N else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hsf : Squarefree (c * d)
      · rw [if_pos hsf]
      · rw [if_neg hsf]
        exact Vb_eq_zero_of_not_squarefree ha_sq hsf N
    rw [hif]
  -- Step 2: the per-`c` bound
  have hper : ∀ c ∈ (cseg N sz sy).filter Squarefree,
      ArithmeticFunction.vonMangoldt c *
          (∑ d ∈ dseg N sy δ2 c,
            (if Squarefree (c * d) then Vb a lam (c * d) N else 0))
        ≤ ArithmeticFunction.vonMangoldt c *
            (Acount a (N : ℝ) * g c * M6 g lam δ2 Δ
              + ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
                  |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)) := by
    intro c hc
    obtain ⟨hcc, hcsf⟩ := Finset.mem_filter.mp hc
    by_cases hv : ArithmeticFunction.vonMangoldt c = 0
    · rw [hv, zero_mul, zero_mul]
    · have hcp : c.Prime := prime_of_squarefree_vonMangoldt_ne_zero hcsf hv
      refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
      have hrestrict : (∑ d ∈ dseg N sy δ2 c,
            (if Squarefree (c * d) then Vb a lam (c * d) N else 0))
          = ∑ d ∈ (dseg N sy δ2 c).filter (fun d => Squarefree (c * d)),
              Vb a lam (c * d) N := by
        rw [Finset.sum_filter]
      rw [hrestrict]
      trans ∑ d ∈ (dseg N sy δ2 c).filter (fun d => Squarefree (c * d)),
          (Acount a (N : ℝ) * g c * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν d))
            + ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |r (Nat.lcm ν (c * d)) N|)
      · apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hdseg, hdsf⟩ := Finset.mem_filter.mp hd
        have hcd : Nat.Coprime c d := Nat.coprime_of_squarefree_mul hdsf
        rw [Vb_eq_Icc a g r lam N (c * d) happ hΔN hsupp]
        have hrewrite : (∑ ν ∈ Finset.Icc 1 Δ,
              lam ν * (g (Nat.lcm ν (c * d)) * Acount a (N : ℝ) + r (Nat.lcm ν (c * d)) N))
            = Acount a (N : ℝ) * g c * (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν d))
              + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν (c * d)) N := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro ν hν
          obtain ⟨hν1, hν2⟩ := Finset.mem_Icc.mp hν
          have hcν : Nat.Coprime c ν := by
            refine hcp.coprime_iff_not_dvd.mpr (fun hdvd => ?_)
            have h1 : (c : ℝ) ≤ (ν : ℝ) :=
              by exact_mod_cast (Nat.le_of_dvd (by omega) hdvd)
            have h2 : ((ν : ℕ) : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hν2
            have hszc : sz < (c : ℝ) :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp hcc).1).2
            linarith
          have hcl : Nat.Coprime c (Nat.lcm ν d) :=
            Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul ν d) (hcν.mul_right hcd)
          rw [lcm_mul_left_coprime hcd hcν, hg c (Nat.lcm ν d) hcl]
          ring
        rw [hrewrite]
        refine add_le_add le_rfl ?_
        apply Finset.sum_le_sum
        intro ν _
        rw [← abs_mul]
        exact le_abs_self _
      · rw [Finset.sum_add_distrib]
        refine add_le_add ?_ ?_
        · rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hAnn (hgnn c))
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hpos d)
          intro d hd
          obtain ⟨hdseg, hdsf⟩ := Finset.mem_filter.mp hd
          exact Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hdseg).1, Squarefree.squarefree_of_dvd (dvd_mul_left d c) hdsf⟩
        · have heq : (∑ d ∈ (dseg N sy δ2 c).filter (fun d => Squarefree (c * d)),
                ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |r (Nat.lcm ν (c * d)) N|)
              = ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
                  |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro d _
            by_cases h : Squarefree (c * d) <;> simp [h]
          exact le_of_eq heq
  calc (∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
        ∑ d ∈ dseg N sy δ2 c, Vb a lam (c * d) N)
      = ∑ c ∈ (cseg N sz sy).filter Squarefree, ArithmeticFunction.vonMangoldt c *
        ∑ d ∈ dseg N sy δ2 c,
          (if Squarefree (c * d) then Vb a lam (c * d) N else 0) := hsingle
    _ ≤ ∑ c ∈ (cseg N sz sy).filter Squarefree, ArithmeticFunction.vonMangoldt c *
            (Acount a (N : ℝ) * g c * M6 g lam δ2 Δ
              + ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
                  |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)) :=
        Finset.sum_le_sum hper
    _ = Acount a (N : ℝ) *
            (∑ c ∈ (cseg N sz sy).filter Squarefree, ArithmeticFunction.vonMangoldt c * g c) *
            M6 g lam δ2 Δ
          + ∑ c ∈ (cseg N sz sy).filter Squarefree, ArithmeticFunction.vonMangoldt c *
              ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
                |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0) := by
        rw [Finset.sum_congr rfl (fun c _ =>
          mul_add (ArithmeticFunction.vonMangoldt c) _ _), Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
    _ ≤ Acount a (N : ℝ) * L6 g N sz sy * M6 g lam δ2 Δ
          + ∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
              ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
                |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0) := by
        refine add_le_add ?_ ?_
        · rfl
        · refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro c _ _
          refine mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun ν _ =>
              mul_nonneg (abs_nonneg _) (by
                by_cases h : Squarefree (c * d) <;> simp [h]))))

/-! ### §6: the remainder term -/

/-- **§6, the remainder term of (6.3)**: bounded by `log(M δ₂)·(R′)`-sum, by the **squarefree**
fibre exchange `(c,d) ↦ cd` and the `lcm`-shadow bound.  Only the pairs with `c·d` squarefree
contribute (the exact sum vanishes on the others, since `V_{cd}` is supported on squarefree
moduli), and for those the moduli `[ν, cd]` are squarefree, which is the form in which (R′) is
available. -/
lemma rem6_le (r : ℕ → ℕ → ℝ) (lam : ℕ → ℝ) (N : ℕ) {sy sz : ℝ} {δ2 Δ M D : ℕ}
    (hM : ∀ c ∈ cseg N sz sy, c ≤ M) (hDE : Δ * (M * δ2) ≤ D)
    (hlam1 : ∀ ν, |lam ν| ≤ 1) (hlam_sq : ∀ ν, ¬ Squarefree ν → lam ν = 0) :
    ∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
        ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
          |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)
      ≤ Real.log ((M : ℝ) * (δ2 : ℝ)) * RemainderSum r D N := by
  classical
  have hδ2Mpos : (0 : ℝ) ≤ Real.log ((M : ℝ) * (δ2 : ℝ)) := by
    rcases Nat.eq_zero_or_pos (M * δ2) with h | h
    · have h0 : (M : ℝ) * (δ2 : ℝ) = 0 := by rw [← Nat.cast_mul, h, Nat.cast_zero]
      rw [h0, Real.log_zero]
    · refine Real.log_nonneg ?_
      rw [← Nat.cast_mul]
      exact_mod_cast h
  -- step 1: expand and extend the ranges
  have hstep1 : (∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
        ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
          |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0))
      ≤ ∑ c ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 δ2, ∑ ν ∈ Finset.Icc 1 Δ,
          ArithmeticFunction.vonMangoldt c *
            (|lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)) := by
    calc (∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
          ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
            |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0))
        = ∑ c ∈ cseg N sz sy, ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
            ArithmeticFunction.vonMangoldt c *
              (|lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)) := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.mul_sum]
      _ ≤ ∑ c ∈ Finset.Icc 1 M, ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
            ArithmeticFunction.vonMangoldt c *
              (|lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun c hc =>
            Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp
              (Finset.mem_filter.mp hc).1).1).1, hM c hc⟩) ?_
          intro c _ _
          exact Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun ν _ =>
            mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (mul_nonneg (abs_nonneg _) (by by_cases h : Squarefree (c * d) <;> simp [h]))))
      _ ≤ ∑ c ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 δ2, ∑ ν ∈ Finset.Icc 1 Δ,
            ArithmeticFunction.vonMangoldt c *
              (|lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)) := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun d _ _ => Finset.sum_nonneg (fun ν _ =>
              mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (mul_nonneg (abs_nonneg _) (by by_cases h : Squarefree (c * d) <;> simp [h]))))
  -- step 2: swap the order so that `ν` is outermost and factor out `|λ_ν|`
  have hstep2 : (∑ c ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 δ2, ∑ ν ∈ Finset.Icc 1 Δ,
          ArithmeticFunction.vonMangoldt c *
            (|lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)))
      = ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| *
          (∑ c ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 δ2,
            ArithmeticFunction.vonMangoldt c *
              (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun d _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_comm)]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  -- step 3: the squarefree fibre exchange `(c,d) ↦ cd`
  have hstep3 : ∀ ν ∈ Finset.Icc 1 Δ,
      (∑ c ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 δ2,
          ArithmeticFunction.vonMangoldt c *
            (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0))
        ≤ ∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree,
            Real.log (e : ℝ) * |r (Nat.lcm ν e) N| := by
    intro ν _
    have h := sum_vonMangoldt_mul_le_sqfree (M := δ2) (P := M)
      (X := fun e => |r (Nat.lcm ν e) N|) (fun e => abs_nonneg _)
    rw [Nat.mul_comm δ2 M] at h
    refine le_trans ?_ h
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro d _
    apply Finset.sum_le_sum
    intro c _
    rw [Nat.mul_comm c d]
  -- step 4: `log e ≤ log (M δ₂)`
  have hstep4 : ∀ ν ∈ Finset.Icc 1 Δ,
      (∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree,
          Real.log (e : ℝ) * |r (Nat.lcm ν e) N|)
        ≤ Real.log ((M : ℝ) * (δ2 : ℝ)) *
            ∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree, |r (Nat.lcm ν e) N| := by
    intro ν _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
    have he2 : e ≤ M * δ2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).2
    have hloge : Real.log (e : ℝ) ≤ Real.log ((M : ℝ) * (δ2 : ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [← Nat.cast_mul]
      exact_mod_cast he2
    exact mul_le_mul_of_nonneg_right hloge (abs_nonneg _)
  -- step 5: `|λ_ν| ≤ 1` (with the squarefree reduction)
  have hstep5 : (∑ ν ∈ Finset.Icc 1 Δ, |lam ν| *
        (∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree, |r (Nat.lcm ν e) N|))
      ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          ∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree, |r (Nat.lcm ν e) N| := by
    conv_rhs => rw [Finset.sum_filter (s := Finset.Icc 1 Δ) (p := Squarefree)
      (f := fun ν => ∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree,
        |r (Nat.lcm ν e) N|)]
    apply Finset.sum_le_sum
    intro ν _
    by_cases hν : Squarefree ν
    · rw [if_pos hν]
      exact mul_le_of_le_one_left (Finset.sum_nonneg (fun e _ => abs_nonneg _)) (hlam1 ν)
    · rw [if_neg hν, hlam_sq ν hν]; simp
  -- step 6: the `lcm`-shadow bound
  have hstep6 : (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        ∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree, |r (Nat.lcm ν e) N|)
      ≤ RemainderSum r D N :=
    sum_lcm_le_remainderSum (Δ := Δ) (M := M * δ2) (D := D) hDE N
  calc (∑ c ∈ cseg N sz sy, ArithmeticFunction.vonMangoldt c *
        ∑ d ∈ dseg N sy δ2 c, ∑ ν ∈ Finset.Icc 1 Δ,
          |lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0))
      ≤ ∑ c ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 δ2, ∑ ν ∈ Finset.Icc 1 Δ,
          ArithmeticFunction.vonMangoldt c *
            (|lam ν| * (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)) := hstep1
    _ = ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| *
          (∑ c ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 δ2,
            ArithmeticFunction.vonMangoldt c *
              (if Squarefree (c * d) then |r (Nat.lcm ν (c * d)) N| else 0)) := hstep2
    _ ≤ ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| *
          (∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree,
            Real.log (e : ℝ) * |r (Nat.lcm ν e) N|) := by
        refine Finset.sum_le_sum (fun ν hν => ?_)
        exact mul_le_mul_of_nonneg_left (hstep3 ν hν) (abs_nonneg _)
    _ ≤ ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| *
          (Real.log ((M : ℝ) * (δ2 : ℝ)) *
            ∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree, |r (Nat.lcm ν e) N|) := by
        refine Finset.sum_le_sum (fun ν hν => ?_)
        exact mul_le_mul_of_nonneg_left (hstep4 ν hν) (abs_nonneg _)
    _ = Real.log ((M : ℝ) * (δ2 : ℝ)) *
          (∑ ν ∈ Finset.Icc 1 Δ, |lam ν| *
            (∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree, |r (Nat.lcm ν e) N|)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ν _
        ring
    _ ≤ Real.log ((M : ℝ) * (δ2 : ℝ)) *
          (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
            ∑ e ∈ (Finset.Icc 1 (M * δ2)).filter Squarefree, |r (Nat.lcm ν e) N|) :=
        mul_le_mul_of_nonneg_left hstep5 hδ2Mpos
    _ ≤ Real.log ((M : ℝ) * (δ2 : ℝ)) * RemainderSum r D N :=
        mul_le_mul_of_nonneg_left hstep6 hδ2Mpos

/-! ### §6, (6.4): the bound for `L(x)` -/

/-! ### §6, the assembly of (6.6) -/

/-- **§6, (6.6)**: combining (6.3), the remainder bound and the two estimates of `L` and `M`,
`S₁(x;y,z) ≪ A(x)(log δ/log Δ + (log x)^{-2})`. -/
theorem S1_bound (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (lam : ℕ → ℝ) (N : ℕ)
    {sy sz : ℝ} {δ2 Δ M D : ℕ} {C₅ C₆ : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hrho : ∀ n, 0 ≤ rhoOf lam n) (hsy : 0 < sy)
    (hδ2 : ∀ b c : ℕ, sy < (b : ℝ) → sz < (c : ℝ) → N / (b * c) ≤ δ2)
    (ha_sq : ∀ n, ¬ Squarefree n → a n = 0)
    (happ : Approx a g r (N : ℝ)) (hΔN : Δ ≤ N)
    (hsupp : ∀ ν, ν ∉ Finset.Icc 1 Δ → lam ν = 0)
    (hΔsz : (Δ : ℝ) < sz)
    (hg : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hgnn : ∀ n, 0 ≤ g n)
    (hpos : ∀ d, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν d))
    (hlam1 : ∀ ν, |lam ν| ≤ 1) (hlam_sq : ∀ ν, ¬ Squarefree ν → lam ν = 0)
    (hMran : ∀ c ∈ cseg N sz sy, c ≤ M) (hDE : Δ * (M * δ2) ≤ D)
    (hC₅ : 0 ≤ C₅) (hC₆ : 0 ≤ C₆)
    (hL : L6 g N sz sy ≤ C₅) (hM6 : M6 g lam δ2 Δ ≤ C₆) :
    |S1 a lam N sy sz| ≤
      Acount a (N : ℝ) * C₅ * C₆ + Real.log ((M : ℝ) * (δ2 : ℝ)) * RemainderSum r D N := by
  refine le_trans (S1_le_main_rem a g r lam N ha hrho hsy hδ2 ha_sq happ hΔN hsupp hΔsz hg hgnn
    hpos) ?_
  have hAnn : 0 ≤ Acount a (N : ℝ) := Finset.sum_nonneg (fun n _ => ha n)
  have hM6nn : 0 ≤ M6 g lam δ2 Δ := by
    unfold M6
    exact Finset.sum_nonneg (fun d _ => hpos d)
  have hrem := rem6_le r lam N hMran hDE hlam1 hlam_sq
  have h1 : Acount a (N : ℝ) * L6 g N sz sy * M6 g lam δ2 Δ
      ≤ Acount a (N : ℝ) * C₅ * C₆ := by
    have h2 : Acount a (N : ℝ) * L6 g N sz sy * M6 g lam δ2 Δ
        = (Acount a (N : ℝ) * M6 g lam δ2 Δ) * L6 g N sz sy := by ring
    rw [h2]
    calc (Acount a (N : ℝ) * M6 g lam δ2 Δ) * L6 g N sz sy
        ≤ (Acount a (N : ℝ) * M6 g lam δ2 Δ) * C₅ :=
          mul_le_mul_of_nonneg_left hL (mul_nonneg hAnn hM6nn)
      _ = Acount a (N : ℝ) * C₅ * M6 g lam δ2 Δ := by ring
      _ ≤ Acount a (N : ℝ) * C₅ * C₆ :=
          mul_le_mul_of_nonneg_left hM6 (mul_nonneg hAnn hC₅)
  exact add_le_add h1 hrem

end

end Submission.ASP
