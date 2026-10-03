import Mathlib
import Submission.ASP.S3v
import Submission.ASP.S3w

open Finset

noncomputable section

namespace Submission.ASP


/-- Reindexing: `∑_{z<c} Λ c ∑_{e : ce ≤ M} f(ce) = ∑_k f(k) ∑_{c|k, z<c} Λ c`. -/
lemma sum_vonMangoldt_dvd_reindex (f : ℕ → ℝ) (z : ℝ) (M : ℕ) :
    (∑ c ∈ (Finset.Icc 1 M).filter (fun c => z < ((c : ℕ) : ℝ)),
        ArithmeticFunction.vonMangoldt c *
          ∑ e ∈ (Finset.Icc 1 M).filter (fun e => c * e ≤ M), f (c * e))
      = ∑ k ∈ Finset.Icc 1 M, f k *
          ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
            ArithmeticFunction.vonMangoldt c := by
  classical
  set C : Finset ℕ := (Finset.Icc 1 M).filter (fun c => z < ((c : ℕ) : ℝ)) with hC
  set L : ℕ → Finset ℕ := fun c => (Finset.Icc 1 M).filter (fun e => c * e ≤ M) with hLdef
  set R : ℕ → Finset ℕ := fun k => k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)) with hRdef
  have hmemC : ∀ c, c ∈ C ↔ (1 ≤ c ∧ c ≤ M) ∧ z < ((c : ℕ) : ℝ) := by
    intro c; rw [hC, Finset.mem_filter, Finset.mem_Icc]
  have hmemL : ∀ c e, e ∈ L c ↔ (1 ≤ e ∧ e ≤ M) ∧ c * e ≤ M := by
    intro c e; rw [hLdef, Finset.mem_filter, Finset.mem_Icc]
  have hmemR : ∀ k c, c ∈ R k ↔ (c ∣ k ∧ k ≠ 0) ∧ z < ((c : ℕ) : ℝ) := by
    intro k c; rw [hRdef, Finset.mem_filter, Nat.mem_divisors]
  have hleft : (∑ c ∈ C, ArithmeticFunction.vonMangoldt c * ∑ e ∈ L c, f (c * e))
      = ∑ p ∈ C.sigma L, ArithmeticFunction.vonMangoldt p.1 * f (p.1 * p.2) := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl (fun c _ => by rw [Finset.mul_sum])
  have hright : (∑ k ∈ Finset.Icc 1 M, f k * ∑ c ∈ R k, ArithmeticFunction.vonMangoldt c)
      = ∑ q ∈ (Finset.Icc 1 M).sigma R, f q.1 * ArithmeticFunction.vonMangoldt q.2 := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
  rw [hleft, hright]
  refine Finset.sum_bij (fun p _ => (⟨p.1 * p.2, p.1⟩ : Σ k : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · rintro ⟨c, e⟩ hp
    rw [Finset.mem_sigma] at hp ⊢
    obtain ⟨hc, he⟩ := hp
    obtain ⟨⟨hc1, hcM⟩, hcz⟩ := (hmemC c).mp hc
    obtain ⟨⟨he1, heM⟩, hce⟩ := (hmemL c e).mp he
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hc1)
        (Nat.one_le_iff_ne_zero.mp he1)), hce⟩
    · rw [hmemR]
      exact ⟨⟨Nat.dvd_mul_right c e, Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hc1)
        (Nat.one_le_iff_ne_zero.mp he1)⟩, hcz⟩
  · rintro ⟨c₁, e₁⟩ h₁ ⟨c₂, e₂⟩ h₂ heq
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp heq
    have h12 : c₁ = c₂ := eq_of_heq h2
    obtain ⟨⟨hc1a, -⟩, -⟩ := (hmemC c₁).mp (Finset.mem_sigma.mp h₁).1
    have hcpos : 0 < c₂ := by omega
    have heq2 : e₁ = e₂ := Nat.mul_left_cancel hcpos (h12 ▸ h1)
    rw [h12, heq2]
  · rintro ⟨k, c⟩ hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hk, hc⟩ := hq
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    obtain ⟨⟨hcdvd, hkne⟩, hcz⟩ := (hmemR k c).mp hc
    have hc1 : 1 ≤ c := Nat.pos_of_dvd_of_pos hcdvd (by omega)
    have hck : c ≤ k := Nat.le_of_dvd (by omega) hcdvd
    refine ⟨(⟨c, k / c⟩ : Σ _ : ℕ, ℕ), ?_, ?_⟩
    · rw [Finset.mem_sigma]
      refine ⟨(hmemC c).mpr ⟨⟨hc1, le_trans hck hkM⟩, hcz⟩, ?_⟩
      rw [hmemL]
      exact ⟨⟨Nat.div_pos hck hc1, le_trans (Nat.div_le_self k c) hkM⟩,
        by rw [Nat.mul_div_cancel' hcdvd]; exact hkM⟩
    · rw [Sigma.mk.inj_iff]
      exact ⟨Nat.mul_div_cancel' hcdvd, HEq.rfl⟩
  · rintro ⟨c, e⟩ _
    exact mul_comm _ _

/-- **§7, first step**: `S₂` as a triple sum over `(b,c,n)`. -/
theorem S2_eq_triple (a lam : ℕ → ℝ) (N : ℕ) (y z sy : ℝ) :
    S2 a lam N y z sy
      = ∑ b ∈ (Finset.Icc 1 N).filter
            (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy),
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (Finset.Icc 1 N).filter (fun c => z < ((c : ℕ) : ℝ)),
              ArithmeticFunction.vonMangoldt c *
                ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b * c ∣ n),
                  a n * rhoOf lam n := by
  unfold S2 Lam2
  exact (sum_triple_filter (fun n => a n * rhoOf lam n) N
    (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy)
    (fun c => z < ((c : ℕ) : ℝ))).symm

/-- **§7, the inner reindexing**: for a fixed `b`, the `c`- and `e`-sums collapse onto
`∑_k f(bk)·∑_{c | k, z < c} Λ c` (this is what produces the factor with the sign changes of
`μ(b)` around which the bilinear-form hypothesis (B′) is applied). -/
lemma S2_inner (a lam : ℕ → ℝ) {N b : ℕ} (hb : 1 ≤ b) (z : ℝ) :
    (∑ c ∈ (Finset.Icc 1 N).filter (fun c => z < ((c : ℕ) : ℝ)),
        ArithmeticFunction.vonMangoldt c *
          ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * (c * e)))
      = ∑ k ∈ Finset.Icc 1 N,
          (if b * k ≤ N then a (b * k) * rhoOf lam (b * k) else 0) *
            ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
              ArithmeticFunction.vonMangoldt c := by
  classical
  have h1 := sum_vonMangoldt_dvd_reindex
    (fun k => if b * k ≤ N then a (b * k) * rhoOf lam (b * k) else 0) z N
  rw [← h1]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : b * (c * e) ≤ N
  · have hce : c * e ≤ N :=
      le_trans (Nat.le_mul_of_pos_left (c * e) (by omega : 0 < b)) h
    simp only [if_pos h, if_pos hce]
  · by_cases hce : c * e ≤ N
    · simp only [if_neg h, if_pos hce, if_neg h]
    · simp only [if_neg h, if_neg hce]

/-- `∑_{n ≤ N, q | n} f n = ∑_{e ≤ N, q e ≤ N} f (q e)` (the filtered-range form). -/
lemma sum_filter_dvd_eq'' {q N : ℕ} (hq : 1 ≤ q) (f : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n), f n)
      = ∑ e ∈ (Finset.Icc 1 N).filter (fun e => q * e ≤ N), f (q * e) := by
  rw [sum_filter_dvd_eq' (p := q) (by omega) f]
  refine Finset.sum_congr ?_ (fun e _ => rfl)
  ext e
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨he1, heM⟩
    exact ⟨⟨he1, le_trans heM (Nat.div_le_self N q)⟩,
      le_trans (Nat.mul_le_mul_left q heM) (Nat.mul_div_le N q)⟩
  · rintro ⟨⟨he1, -⟩, hqe⟩
    exact ⟨he1, (Nat.le_div_iff_mul_le (by omega : 0 < q)).mpr (by rw [mul_comm]; exact hqe)⟩

/-- **§7, (7.1) first form**: `|S₂| ≤ (log x)∑_k |∑_{y<b≤sy} μ(b)ρ_{bk}a_{bk}|`.  The gain over
the trivial triangle inequality is that the sum over `b` is kept *inside* the absolute value,
where the sign changes of `μ(b)` produce the cancellation measured by the bilinear hypothesis
(B′). -/
theorem abs_S2_le (a lam : ℕ → ℝ) (N : ℕ) (y z sy : ℝ) :
    |S2 a lam N y z sy| ≤ Real.log (N : ℝ) *
      ∑ k ∈ Finset.Icc 1 N,
        |∑ b ∈ (Finset.Icc 1 N).filter
            (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy ∧ b * k ≤ N),
          (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))| := by
  classical
  set B : Finset ℕ := (Finset.Icc 1 N).filter
    (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy) with hB
  set C : Finset ℕ := (Finset.Icc 1 N).filter (fun c => z < ((c : ℕ) : ℝ)) with hC
  -- ### Step 1: `S₂` as a `(b,c,e)` triple sum
  have hstep1 : S2 a lam N y z sy
      = ∑ b ∈ B, (ArithmeticFunction.moebius b : ℝ) *
          ∑ c ∈ C, ArithmeticFunction.vonMangoldt c *
            ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
              a (b * (c * e)) * rhoOf lam (b * (c * e)) := by
    rw [S2_eq_triple, hB, hC]
    apply Finset.sum_congr rfl
    intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    congr 1
    apply Finset.sum_congr rfl
    intro c hc
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
    congr 1
    rw [sum_filter_dvd_eq'' (q := b * c)
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
      (fun n => a n * rhoOf lam n)]
    refine Finset.sum_congr ?_ (fun e _ => ?_)
    · apply Finset.filter_congr
      intro e _
      rw [Nat.mul_assoc]
    · rw [Nat.mul_assoc]
  -- ### Step 2: the inner reindexing (the `b`-cancellation form)
  have hstep2 : S2 a lam N y z sy
      = ∑ b ∈ B, (ArithmeticFunction.moebius b : ℝ) *
          ∑ k ∈ Finset.Icc 1 N,
            (if b * k ≤ N then a (b * k) * rhoOf lam (b * k) else 0) *
              ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
                ArithmeticFunction.vonMangoldt c := by
    rw [hstep1]
    apply Finset.sum_congr rfl
    intro b hb
    congr 1
    refine S2_inner a lam ?_ z
    rw [hB] at hb
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  -- ### Step 3: swap the `b`- and `k`-sums
  have hstep3 : S2 a lam N y z sy
      = ∑ k ∈ Finset.Icc 1 N,
          (∑ b ∈ B.filter (fun b => b * k ≤ N),
            (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))) *
              ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
                ArithmeticFunction.vonMangoldt c := by
    rw [hstep2]
    have h1 : ∀ b ∈ B, (ArithmeticFunction.moebius b : ℝ) *
          ∑ k ∈ Finset.Icc 1 N,
            (if b * k ≤ N then a (b * k) * rhoOf lam (b * k) else 0) *
              ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
                ArithmeticFunction.vonMangoldt c
        = ∑ k ∈ Finset.Icc 1 N,
            (ArithmeticFunction.moebius b : ℝ) *
              ((if b * k ≤ N then a (b * k) * rhoOf lam (b * k) else 0) *
                ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
                  ArithmeticFunction.vonMangoldt c) := by
      intro b _; rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    conv_rhs => rw [Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : b * k ≤ N
    · simp only [h, if_true]
      ring
    · simp only [h, if_false]
      ring
  rw [hstep3]
  -- ### Step 4: the `Λ`-sum over divisors is `≤ log N`, then the triangle inequality
  have hset : ∀ k : ℕ, B.filter (fun b => b * k ≤ N)
      = (Finset.Icc 1 N).filter
          (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy ∧ b * k ≤ N) := by
    intro k
    rw [hB, Finset.filter_filter]
    congr 1
    ext b
    simp only [and_assoc]
  have hVle : ∀ k ∈ Finset.Icc 1 N, (∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
        ArithmeticFunction.vonMangoldt c) ≤ Real.log (N : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    have h1 : (∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
        ArithmeticFunction.vonMangoldt c) ≤ ∑ c ∈ k.divisors, ArithmeticFunction.vonMangoldt c :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun c _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    have h2 : (∑ c ∈ k.divisors, ArithmeticFunction.vonMangoldt c) = Real.log (k : ℝ) :=
      ArithmeticFunction.vonMangoldt_sum
    have h3 : Real.log (k : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < k))
        (by exact_mod_cast hkN)
    linarith
  have hVnn : ∀ k : ℕ, (0 : ℝ) ≤ ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
        ArithmeticFunction.vonMangoldt c :=
    fun k => Finset.sum_nonneg (fun c _ => ArithmeticFunction.vonMangoldt_nonneg)
  calc |∑ k ∈ Finset.Icc 1 N,
          (∑ b ∈ B.filter (fun b => b * k ≤ N),
            (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))) *
              ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
                ArithmeticFunction.vonMangoldt c|
      ≤ ∑ k ∈ Finset.Icc 1 N,
          |(∑ b ∈ B.filter (fun b => b * k ≤ N),
            (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))) *
              ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
                ArithmeticFunction.vonMangoldt c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.Icc 1 N,
          |∑ b ∈ B.filter (fun b => b * k ≤ N),
            (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))| *
              ∑ c ∈ k.divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
                ArithmeticFunction.vonMangoldt c := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul, abs_of_nonneg (hVnn k)]
    _ ≤ ∑ k ∈ Finset.Icc 1 N,
          |∑ b ∈ B.filter (fun b => b * k ≤ N),
            (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))| *
              Real.log (N : ℝ) :=
        Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hVle k hk) (abs_nonneg _))
    _ = Real.log (N : ℝ) * ∑ k ∈ Finset.Icc 1 N,
          |∑ b ∈ B.filter (fun b => b * k ≤ N),
            (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = Real.log (N : ℝ) * ∑ k ∈ Finset.Icc 1 N,
          |∑ b ∈ (Finset.Icc 1 N).filter
              (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy ∧ b * k ≤ N),
            (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))| := by
        congr 1
        exact Finset.sum_congr rfl (fun k _ => by rw [hset k])

end Submission.ASP

end
