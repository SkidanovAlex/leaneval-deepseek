import Mathlib
import Submission.Work.FIChain.Defs

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.FIChain

open Finset
open Submission.ASP
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The `μ(c)`-signed splitting of `S₃`

We prove the companion's §8 identity in the reindexed form used by `Work.FIChain`:
`S₃ = S₃⁺ − S₃⁻` where `S₃^{±}` are the `Work.FIChain.S3plusC`/`S3minusC` of `Defs`.

The mechanism is a *sign flip*: both `S₃` and the difference carry the
`μ(c)`-weighted `Λ(c)`-splitting, and on the squarefree support the factor `μ(c)`
is `−1` on every `c` whose von Mangoldt weight is non-zero (such a `c` is prime). -/

/-- On the squarefree support, `μ(c)·Λ(c) = −Λ(c)`: if `c ∣ n` with `n` squarefree and
`Λ(c) ≠ 0`, then `c` is a prime. -/
lemma s3f_moebius_mul_vonMangoldt_eq_neg {c n : ℕ} (hcn : c ∣ n) (hsq : Squarefree n) :
    (ArithmeticFunction.moebius c : ℝ) * ArithmeticFunction.vonMangoldt c
      = -ArithmeticFunction.vonMangoldt c := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt c = 0
  · rw [hΛ, mul_zero, neg_zero]
  · have hpv : IsPrimePow c := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    have hsqc : Squarefree c := hsq.squarefree_of_dvd hcn
    have hcp : Nat.Prime c := Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsqc, hpv⟩
    rw [ArithmeticFunction.moebius_apply_prime hcp]
    push_cast
    ring

/-- Termwise form of the sign flip on the squarefree support. -/
lemma s3f_vonMangoldt_mul_eq_neg_moebius (a : ℕ → ℝ) (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (b c e : ℕ) (w : ℝ) :
    ArithmeticFunction.vonMangoldt c * (a (b * (c * e)) * w)
      = -((ArithmeticFunction.moebius c : ℝ) * ArithmeticFunction.vonMangoldt c
          * (a (b * (c * e)) * w)) := by
  by_cases hx : a (b * (c * e)) = 0
  · rw [hx]; ring
  · have hsq : Squarefree (b * (c * e)) := by
      by_contra h; exact hx (ha _ h)
    have hdiv : c ∣ b * (c * e) := ⟨b * e, by ring⟩
    have h := s3f_moebius_mul_vonMangoldt_eq_neg hdiv hsq
    rw [h]; ring

/-! ## The reindexing of the divisor-filtered `ℓ`-sum -/

/-- Reindexing a divisor-filtered interval sum: for `K : ℕ → ℝ` and a predicate `P`,
`∑_{ℓ ≤ N} (∑_{b | ℓ, P b} μ(b))·K ℓ = ∑_{b ≤ N, P b} μ(b)·∑_{e : be ≤ N} K (be)`. -/
lemma s3f_sum_divisors_reindex (K : ℕ → ℝ) (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter P, (ArithmeticFunction.moebius b : ℝ)) * K ℓ)
      = ∑ b ∈ (Finset.Icc 1 N).filter P, (ArithmeticFunction.moebius b : ℝ) *
          ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * e ≤ N), K (b * e) := by
  have hdiv : ∀ ℓ ∈ Finset.Icc 1 N,
      ℓ.divisors.filter P = (Finset.Icc 1 N).filter (fun b => b ∣ ℓ ∧ P b) := by
    intro ℓ hℓ
    obtain ⟨hℓ1, hℓN⟩ := Finset.mem_Icc.mp hℓ
    have hℓ0 : ℓ ≠ 0 := by omega
    ext b
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hbd, _⟩, hpb⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hbd (by omega),
        le_trans (Nat.le_of_dvd (by omega) hbd) hℓN⟩, hbd, hpb⟩
    · rintro ⟨⟨hb1, _⟩, hbd, hpb⟩
      exact ⟨⟨hbd, hℓ0⟩, hpb⟩
  calc (∑ ℓ ∈ Finset.Icc 1 N,
          (∑ b ∈ ℓ.divisors.filter P, (ArithmeticFunction.moebius b : ℝ)) * K ℓ)
      = ∑ ℓ ∈ Finset.Icc 1 N,
          ∑ b ∈ (Finset.Icc 1 N).filter (fun b => b ∣ ℓ ∧ P b),
            (ArithmeticFunction.moebius b : ℝ) * K ℓ := by
        apply Finset.sum_congr rfl; intro ℓ hℓ
        rw [hdiv ℓ hℓ, Finset.sum_mul]
    _ = ∑ ℓ ∈ Finset.Icc 1 N,
          ∑ b ∈ Finset.Icc 1 N,
            (if b ∣ ℓ ∧ P b then (ArithmeticFunction.moebius b : ℝ) * K ℓ else 0) := by
        apply Finset.sum_congr rfl; intro ℓ _
        rw [Finset.sum_filter]
    _ = ∑ b ∈ Finset.Icc 1 N,
          ∑ ℓ ∈ Finset.Icc 1 N,
            (if b ∣ ℓ ∧ P b then (ArithmeticFunction.moebius b : ℝ) * K ℓ else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ b ∈ Finset.Icc 1 N,
          (if P b then (ArithmeticFunction.moebius b : ℝ) *
              ∑ ℓ ∈ (Finset.Icc 1 N).filter (fun ℓ => b ∣ ℓ), K ℓ else 0) := by
        apply Finset.sum_congr rfl; intro b _
        by_cases hpb : P b
        · rw [if_pos hpb, Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro ℓ _
          by_cases hbd : b ∣ ℓ <;> simp [hpb, hbd]
        · rw [if_neg hpb]
          apply Finset.sum_eq_zero; intro ℓ _
          simp [hpb]
    _ = ∑ b ∈ (Finset.Icc 1 N).filter P,
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ ℓ ∈ (Finset.Icc 1 N).filter (fun ℓ => b ∣ ℓ), K ℓ := by
        rw [Finset.sum_filter]
    _ = ∑ b ∈ (Finset.Icc 1 N).filter P,
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * e ≤ N), K (b * e) := by
        apply Finset.sum_congr rfl; intro b hb
        congr 1
        obtain ⟨hbIcc, _⟩ := Finset.mem_filter.mp hb
        obtain ⟨hb1, _⟩ := Finset.mem_Icc.mp hbIcc
        have hbpos : 0 < b := hb1
        rw [sum_filter_dvd_eq' hbpos K]
        apply Finset.sum_congr ?_ (fun e _ => rfl)
        ext e
        simp only [Finset.mem_Icc, Finset.mem_filter]
        constructor
        · rintro ⟨he1, he2⟩
          exact ⟨⟨he1, le_trans he2 (Nat.div_le_self N b)⟩,
            by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hbpos).mp he2⟩
        · rintro ⟨⟨he1, _⟩, he3⟩
          exact ⟨he1, (Nat.le_div_iff_mul_le hbpos).mpr (by rw [mul_comm]; exact he3)⟩

/-- Exchange of the `e`- and `c`-sums against the pair of product constraints
`be ≤ N`, `(be)c ≤ N` on the one side, and `bc e ≤ N` on the other. -/
lemma s3f_swap_ec (X : ℕ → ℕ → ℝ) (N b : ℕ) (z sz : ℝ) :
    (∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * e ≤ N),
        ∑ c ∈ (Finset.Icc 1 N).filter
          (fun c => z < ((c:ℕ):ℝ) ∧ ((c:ℕ):ℝ) ≤ sz ∧ (b*e)*c ≤ N), X e c)
      = ∑ c ∈ (Finset.Icc 1 N).filter (fun c => z < ((c:ℕ):ℝ) ∧ ((c:ℕ):ℝ) ≤ sz),
        ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c*e) ≤ N), X e c := by
  rw [← Finset.sum_sigma (t := fun e => (Finset.Icc 1 N).filter
        (fun c => z < ((c:ℕ):ℝ) ∧ ((c:ℕ):ℝ) ≤ sz ∧ (b*e)*c ≤ N))
        (f := fun p : Sigma (fun _ : ℕ => ℕ) => X p.1 p.2)]
  rw [← Finset.sum_sigma (t := fun c => (Finset.Icc 1 N).filter (fun e => b * (c*e) ≤ N))
        (f := fun q : Sigma (fun _ : ℕ => ℕ) => X q.2 q.1)]
  refine Finset.sum_bij' (fun p _ => (⟨p.2, p.1⟩ : Sigma (fun _ : ℕ => ℕ)))
    (fun q _ => (⟨q.2, q.1⟩ : Sigma (fun _ : ℕ => ℕ))) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_sigma] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp1 hp2 ⊢
    refine ⟨⟨hp2.1, hp2.2.1, hp2.2.2.1⟩, hp1.1, ?_⟩
    calc b * (p.2 * p.1) = (b * p.1) * p.2 := by ring
      _ ≤ N := hp2.2.2.2
  · intro q hq
    rw [Finset.mem_sigma] at hq ⊢
    obtain ⟨hq1, hq2⟩ := hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq1 hq2 ⊢
    refine ⟨⟨hq2.1, ?_⟩, ?_⟩
    · calc b * q.2 ≤ b * (q.1 * q.2) := by
            apply Nat.mul_le_mul_left
            exact Nat.le_mul_of_pos_left q.2 (by omega)
        _ ≤ N := hq2.2
    · refine ⟨hq1.1, hq1.2.1, hq1.2.2, ?_⟩
      calc (b * q.2) * q.1 = b * (q.1 * q.2) := by ring
        _ ≤ N := hq2.2
  · intro p hp; rfl
  · intro q hq; rfl
  · intro p hp; rfl

/-- **The reindexing of the companion's §8 `ℓ`-form into the `(b,c,e)`-form**. -/
lemma s3f_reindex_C (a lam : ℕ → ℝ) (N : ℕ) (z sy sz : ℝ) (g : ℕ → ℝ) :
    (∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ *
          (∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
            (ArithmeticFunction.moebius c : ℝ) * g c * a (ℓ * c)))
      = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (Finset.Icc 1 N).filter
                (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
              (ArithmeticFunction.moebius c : ℝ) * g c *
                ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
                  a (b * (c * e)) * rhoOf lam (b * e) := by
  rw [show (∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ *
          (∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
            (ArithmeticFunction.moebius c : ℝ) * g c * a (ℓ * c)))
      = ∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)) *
          (rhoOf lam ℓ *
            (∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
            (ArithmeticFunction.moebius c : ℝ) * g c * a (ℓ * c))) from by
        apply Finset.sum_congr rfl; intro ℓ _; ring]
  rw [s3f_sum_divisors_reindex (fun ℓ => rhoOf lam ℓ *
        (∑ c ∈ (Finset.Icc 1 N).filter
            (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
          (ArithmeticFunction.moebius c : ℝ) * g c * a (ℓ * c)))
        N (fun b => sy < ((b : ℕ) : ℝ))]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  have h1 : (∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * e ≤ N),
        rhoOf lam (b * e) *
          (∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c:ℕ):ℝ) ∧ ((c:ℕ):ℝ) ≤ sz ∧ (b*e)*c ≤ N),
            (ArithmeticFunction.moebius c : ℝ) * g c * a ((b*e)*c)))
      = ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * e ≤ N),
          ∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c:ℕ):ℝ) ∧ ((c:ℕ):ℝ) ≤ sz ∧ (b*e)*c ≤ N),
            (ArithmeticFunction.moebius c : ℝ) * g c * a ((b*e)*c) * rhoOf lam (b*e) := by
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    ring
  rw [h1, s3f_swap_ec (fun e c => (ArithmeticFunction.moebius c : ℝ) * g c * a ((b*e)*c)
        * rhoOf lam (b*e)) N b z sz]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro e _
  have hassoc : (b*e)*c = b*(c*e) := by ring
  rw [hassoc]; ring

/-! ## The main identity -/

theorem s3f_S3_eq_S3plusC_sub_S3minusC (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) (Δ : ℕ)
    (ha : ∀ n, ¬ Squarefree n → a n = 0) (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (hΔz : (Δ : ℝ) < z) (hz : 1 ≤ z) (hC : 0 < C) :
    Submission.ASP.S3 a lam N z sy sz
      = Work.FIChain.S3plusC a lam N z sy sz C - Work.FIChain.S3minusC a lam N z sy sz C := by
  -- `S₃ = −S₃^{signed}` : on the squarefree support `μ(c) = −1` on every contributing `c`.
  have hS3 : Submission.ASP.S3 a lam N z sy sz = - S3signed a lam N z sy sz := by
    rw [S3_eq_rho_eb a lam N z sy sz Δ ha hlam_supp hΔz]
    simp only [S3signed]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    have hY : (∑ c ∈ (Finset.Icc 1 N).filter (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
          ArithmeticFunction.vonMangoldt c *
            ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
              a (b * (c * e)) * rhoOf lam (b * e))
        = -(∑ c ∈ (Finset.Icc 1 N).filter (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
          (ArithmeticFunction.moebius c : ℝ) * ArithmeticFunction.vonMangoldt c *
            ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
              a (b * (c * e)) * rhoOf lam (b * e)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e he
      exact s3f_vonMangoldt_mul_eq_neg_moebius a ha b c e (rhoOf lam (b * e))
    rw [hY]; ring
  -- `S₃⁻ − S₃⁺ = S₃^{signed}` : the `ℓ`-form reindexes to the `(b,c,e)`-form.
  have hCeq : S3minusC a lam N z sy sz C - S3plusC a lam N z sy sz C
      = S3signed a lam N z sy sz := by
    simp only [S3minusC, S3plusC, S3minusInnerC, S3plusInnerC, S3signed]
    rw [← Finset.sum_sub_distrib]
    trans ∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ *
          (∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
            (ArithmeticFunction.moebius c : ℝ) * ArithmeticFunction.vonMangoldt c
              * a (ℓ * c))
    · apply Finset.sum_congr rfl
      intro ℓ hℓ
      have hinner : (∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
            (ArithmeticFunction.moebius c : ℝ) * lamMinus c C * a (ℓ * c))
          - (∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
            (ArithmeticFunction.moebius c : ℝ) * lamPlus c C * a (ℓ * c))
          = ∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
            (ArithmeticFunction.moebius c : ℝ) * ArithmeticFunction.vonMangoldt c
              * a (ℓ * c) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro c hc
        have hcz : z < ((c : ℕ) : ℝ) := (Finset.mem_filter.mp hc).2.1
        have hc2 : 2 ≤ c := by
          have h1 : (1 : ℝ) < (c : ℝ) := lt_of_le_of_lt hz hcz
          have h2 : (1 : ℕ) < c := by exact_mod_cast h1
          omega
        rw [vonMangoldt_eq_lamMinus_sub_lamPlus c hc2 hC]
        ring
      rw [← mul_sub, hinner]
    · exact s3f_reindex_C a lam N z sy sz (fun c => ArithmeticFunction.vonMangoldt c)
  linarith [hS3, hCeq]

end

end Work.FIChain
