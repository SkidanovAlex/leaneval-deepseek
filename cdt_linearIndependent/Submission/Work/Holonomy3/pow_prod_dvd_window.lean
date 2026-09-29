import Mathlib
import Submission.Work.Holonomy3.log_den_defs

namespace Work.Holonomy3

open scoped BigOperators

/-- The factorization at a prime `p` of a product of distinct primes is the indicator of `p`
belonging to the index set. -/
theorem factorization_prod_primes (s : Finset ℕ) (hs : ∀ q ∈ s, q.Prime) (p : ℕ)
    (hp : p.Prime) :
    (∏ q ∈ s, q).factorization p = if p ∈ s then 1 else 0 := by
  rw [Nat.factorization_prod (fun q hq => (hs q hq).ne_zero)]
  rw [Finsupp.finsetSum_apply]
  have hcongr : ∀ q ∈ s, q.factorization p = if q = p then (1 : ℕ) else 0 := by
    intro q hq
    rw [Nat.Prime.factorization (hs q hq)]
    by_cases hqp : q = p
    · subst hqp; simp
    · rw [Finsupp.single_eq_of_ne (Ne.symm hqp)]; simp [hqp]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']

/-- Exact `p`-adic valuation of the proper-prime-power factor `ppFac l N`: the number of exponents
`j ≥ 2` with `l < p ^ j ≤ N`. -/
theorem ppFac_factorization (l N p : ℕ) (hp : p.Prime) :
    (ppFac l N).factorization p
      = ((Finset.Icc 2 N).filter (fun j => l < p ^ j ∧ p ^ j ≤ N)).card := by
  rw [ppFac]
  rw [Nat.factorization_prod]
  · rw [Finsupp.finsetSum_apply]
    have hcongr : ∀ j ∈ Finset.Icc 2 N,
        ((∏ q ∈ (Finset.Icc 1 N).filter (fun q => q.Prime ∧ l < q ^ j ∧ q ^ j ≤ N), q).factorization p)
          = (if p ∈ (Finset.Icc 1 N).filter (fun q => q.Prime ∧ l < q ^ j ∧ q ^ j ≤ N)
              then 1 else 0) := by
      intro j hj
      exact factorization_prod_primes _ (fun q hq => (Finset.mem_filter.mp hq).2.1) p hp
    rw [Finset.sum_congr rfl hcongr]
    rw [← Finset.card_filter]
    congr 1
    apply Finset.filter_congr
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, -⟩, -, hltj, hlej⟩
      exact ⟨hltj, hlej⟩
    · rintro ⟨hlj, hlej⟩
      have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have hple : p ≤ N :=
        le_trans (calc p ≤ p ^ 2 := by nlinarith [hp.two_le]
              _ ≤ p ^ j := Nat.pow_le_pow_right hp.one_le hj2) hlej
      exact ⟨⟨hp.one_le, hple⟩, hp, hlj, hlej⟩
  · intro j hj
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    exact (Finset.mem_filter.mp hq).2.1.ne_zero

/-- Exact `p`-adic valuation of the prime-cutoff window product `Lge l N D`: it is `1` exactly when
`l < p ≤ N` and the window `[N - D, N]` (with `0` removed) contains a multiple of `p`, and `0`
otherwise. -/
theorem Lge_factorization (l D N p : ℕ) (hp : p.Prime) :
    (Submission.CDT.LcmGe.Lge l N D).factorization p
      = if (l < p ∧ p ≤ N ∧ ∃ m ∈ (Finset.Icc (N - D) N).erase 0, p ∣ m) then 1 else 0 := by
  rw [Submission.CDT.LcmGe.Lge]
  rw [factorization_prod_primes _
    (fun q hq => (Finset.mem_filter.mp hq).2.1) p hp]
  congr 1
  apply propext
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1p, hpN⟩, hpr, hlt, hdiv⟩
    exact ⟨hlt, hpN, hdiv⟩
  · rintro ⟨hlt, hpN, hdiv⟩
    exact ⟨⟨hp.one_le, hpN⟩, hp, hlt, hdiv⟩

/-- **Single-position valuation bound.**  For a nonnegative exponent `M` lying in the window
`[N - D, N]` (or equal to `0`), the `p`-adic valuation of `M` is bounded by the sum of the
`p`-adic valuations of `lcmUpto l`, of the window product `Lge l N D` and of the proper prime power
factor `ppFac l N`. -/
theorem single_bound (l D N M p : ℕ) (hp : p.Prime)
    (hwin : M = 0 ∨ (N - D ≤ M ∧ M ≤ N)) :
    M.factorization p ≤ (Submission.CDTPlan.lcmUpto l).factorization p
      + (Submission.CDT.LcmGe.Lge l N D).factorization p
      + (ppFac l N).factorization p := by
  by_cases hM0 : M = 0
  · subst hM0
    rw [Nat.factorization_zero]
    exact Nat.zero_le _
  · obtain ⟨hlo, hhi⟩ : N - D ≤ M ∧ M ≤ N := by
      rcases hwin with h | h
      · exact absurd h hM0
      · exact h
    have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
    set b := (Submission.CDTPlan.lcmUpto l).factorization p with hb
    have hb_log : b = Nat.log p l := by
      rw [hb]; exact Nat.factorization_lcmUpto l hp
    -- the inclusion `(b, a] ⊆ J`
    have hsub : M.factorization p - b
        ≤ ((Finset.Icc 1 N).filter (fun j => l < p ^ j ∧ p ^ j ∣ M)).card := by
      have hsubs : Finset.Icc (b + 1) (M.factorization p)
          ⊆ (Finset.Icc 1 N).filter (fun j => l < p ^ j ∧ p ^ j ∣ M) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        obtain ⟨hbj, hja⟩ := hj
        rw [Finset.mem_filter, Finset.mem_Icc]
        have hpj : p ^ j ∣ M := (hp.pow_dvd_iff_le_factorization hM0).mpr hja
        have hpjle : p ^ j ≤ M := Nat.le_of_dvd hMpos hpj
        refine ⟨⟨by omega, ?_⟩, ?_, hpj⟩
        · calc j ≤ p ^ j := le_trans (Nat.lt_two_pow_self (n := j)).le
                (Nat.pow_le_pow_left hp.two_le j)
            _ ≤ M := hpjle
            _ ≤ N := hhi
        · have h1 : l < p ^ (Nat.log p l + 1) := by
            simpa using Nat.lt_pow_succ_log_self hp.one_lt l
          have h2 : p ^ (Nat.log p l + 1) ≤ p ^ j :=
            Nat.pow_le_pow_right hp.pos (by omega)
          linarith
      calc M.factorization p - b = (Finset.Icc (b + 1) (M.factorization p)).card := by
            rw [Nat.card_Icc]; omega
        _ ≤ _ := Finset.card_le_card hsubs
    -- the card bound `J.card ≤ v_p Lge + v_p ppFac`
    have hJle : ((Finset.Icc 1 N).filter (fun j => l < p ^ j ∧ p ^ j ∣ M)).card
        ≤ (Submission.CDT.LcmGe.Lge l N D).factorization p + (ppFac l N).factorization p := by
      set J := (Finset.Icc 1 N).filter (fun j => l < p ^ j ∧ p ^ j ∣ M) with hJ
      have hsplit : J.card
          = (J.filter (fun j => j = 1)).card + (J.filter (fun j => ¬ j = 1)).card :=
        (Finset.card_filter_add_card_filter_not (s := J) (fun j => j = 1)).symm
      have hJ1 : (J.filter (fun j => j = 1)).card
          ≤ (Submission.CDT.LcmGe.Lge l N D).factorization p := by
        have hle1 : (J.filter (fun j => j = 1)).card ≤ 1 := by
          have hsub1 : J.filter (fun j => j = 1) ⊆ ({1} : Finset ℕ) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rw [Finset.mem_singleton]
            exact hj.2
          have := Finset.card_le_card hsub1
          simpa using this
        rcases Nat.eq_zero_or_pos (J.filter (fun j => j = 1)).card with h0 | hpos
        · rw [h0]; exact Nat.zero_le _
        · obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
          have hj1 : j = 1 := (Finset.mem_filter.mp hj).2
          have h1J : 1 ∈ J := by
            have : j ∈ J := (Finset.mem_filter.mp hj).1
            rwa [hj1] at this
          rw [hJ, Finset.mem_filter, Finset.mem_Icc] at h1J
          obtain ⟨⟨-, -⟩, hl1, hp1dvd⟩ := h1J
          have hpred : l < p ∧ p ≤ N ∧ ∃ m ∈ (Finset.Icc (N - D) N).erase 0, p ∣ m := by
            refine ⟨by simpa using hl1, ?_, M, ?_, by simpa using hp1dvd⟩
            · exact le_trans (Nat.le_of_dvd hMpos (by simpa using hp1dvd)) hhi
            · rw [Finset.mem_erase, Finset.mem_Icc]; exact ⟨hM0, hlo, hhi⟩
          rw [Lge_factorization l D N p hp, if_pos hpred]
          exact hle1
      have hJ2 : (J.filter (fun j => ¬ j = 1)).card ≤ (ppFac l N).factorization p := by
        have hsub2 : J.filter (fun j => ¬ j = 1)
            ⊆ (Finset.Icc 2 N).filter (fun j => l < p ^ j ∧ p ^ j ≤ N) := by
          intro j hj
          rw [Finset.mem_filter] at hj
          obtain ⟨hjJ, hjne⟩ := hj
          rw [hJ, Finset.mem_filter, Finset.mem_Icc] at hjJ
          obtain ⟨⟨hj1, hjN⟩, hlj, hjdvd⟩ := hjJ
          rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, hjN⟩, hlj, le_trans (Nat.le_of_dvd hMpos hjdvd) hhi⟩
        rw [ppFac_factorization l N p hp]
        exact Finset.card_le_card hsub2
      rw [hsplit]
      exact Nat.add_le_add hJ1 hJ2
    have hmain : max 0 (M.factorization p - b)
        ≤ (Submission.CDT.LcmGe.Lge l N D).factorization p + (ppFac l N).factorization p := by
      rw [max_eq_right (Nat.zero_le _)]
      exact le_trans hsub hJle
    have h1 : M.factorization p ≤ b + (M.factorization p - b) := by omega
    have h2 : M.factorization p - b ≤ max 0 (M.factorization p - b) := le_max_right _ _
    have h4 : b + max 0 (M.factorization p - b)
        ≤ (Submission.CDTPlan.lcmUpto l).factorization p
          + (Submission.CDT.LcmGe.Lge l N D).factorization p + (ppFac l N).factorization p := by
      rw [hb]
      omega
    exact le_trans (le_trans h1 (Nat.add_le_add_left h2 b)) h4

/-- **Single-position divisibility.**  For an exponent `M` in the window `[N - D, N]` (or `M = 0`,
where the power is `1`), `(max 1 M)^W` is cleared by `(lcmUpto l)^W` together with the `E`-th
powers of the window product `Lge l N D` and of `ppFac l N`, for any `W ≤ E`. -/
theorem step (l D N M W E : ℕ) (hW : W ≤ E)
    (hwin : M = 0 ∨ (N - D ≤ M ∧ M ≤ N)) :
    (max 1 M) ^ W ∣ (Submission.CDTPlan.lcmUpto l) ^ W
      * (Submission.CDT.LcmGe.Lge l N D) ^ E * (ppFac l N) ^ E := by
  by_cases hM0 : M = 0
  · subst hM0
    simp
  · have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM0
    have hmax : max 1 M = M := max_eq_right hM1
    have hLU : (Submission.CDTPlan.lcmUpto l) ≠ 0 := Nat.lcmUpto_ne_zero l
    have hLge : (Submission.CDT.LcmGe.Lge l N D) ≠ 0 := by
      rw [Submission.CDT.LcmGe.Lge, Finset.prod_ne_zero_iff]
      intro q hq
      exact (Finset.mem_filter.mp hq).2.1.ne_zero
    have hPp : (ppFac l N) ≠ 0 := (ppFac_pos l N).ne'
    rw [hmax]
    refine (Nat.factorization_prime_le_iff_dvd (pow_ne_zero W hM0)
      (mul_ne_zero (mul_ne_zero (pow_ne_zero W hLU) (pow_ne_zero E hLge))
        (pow_ne_zero E hPp))).mp ?_
    intro p hp
    have hLfac : (M ^ W).factorization p = W * M.factorization p := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hRfac : ((Submission.CDTPlan.lcmUpto l) ^ W * (Submission.CDT.LcmGe.Lge l N D) ^ E
          * (ppFac l N) ^ E).factorization p
        = W * (Submission.CDTPlan.lcmUpto l).factorization p
          + E * (Submission.CDT.LcmGe.Lge l N D).factorization p
          + E * (ppFac l N).factorization p := by
      rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero W hLU) (pow_ne_zero E hLge))
            (pow_ne_zero E hPp),
        Finsupp.add_apply,
        Nat.factorization_mul (pow_ne_zero W hLU) (pow_ne_zero E hLge), Finsupp.add_apply,
        Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow,
        Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
        smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [hLfac, hRfac]
    have hs : M.factorization p ≤ (Submission.CDTPlan.lcmUpto l).factorization p
        + ((Submission.CDT.LcmGe.Lge l N D).factorization p + (ppFac l N).factorization p) := by
      have := single_bound l D N M p hp hwin
      omega
    calc W * M.factorization p
        ≤ W * ((Submission.CDTPlan.lcmUpto l).factorization p
            + ((Submission.CDT.LcmGe.Lge l N D).factorization p + (ppFac l N).factorization p)) :=
          Nat.mul_le_mul_left W hs
      _ = W * (Submission.CDTPlan.lcmUpto l).factorization p
            + W * ((Submission.CDT.LcmGe.Lge l N D).factorization p + (ppFac l N).factorization p) := by
          ring
      _ ≤ W * (Submission.CDTPlan.lcmUpto l).factorization p
            + E * ((Submission.CDT.LcmGe.Lge l N D).factorization p + (ppFac l N).factorization p) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hW) _
      _ = W * (Submission.CDTPlan.lcmUpto l).factorization p
            + E * (Submission.CDT.LcmGe.Lge l N D).factorization p
            + E * (ppFac l N).factorization p := by
          ring

/-- **Prime-power clearing of the window denominators.**  For exponent vectors `m s` lying in the
window `[n s - D, n s]` (or equal to `0`, in which case the corresponding power is `1`), the
product `∏_s (max 1 (m s))^(w s)` is cleared by `[1,…,l]^(Σ_s w s)` times the `E`-th powers of the
paper's window products `L^{≥l}_{n_s,D}` and of the proper prime powers `ppFac l (n_s)`, for any
`E ≥ w s` for all `s`.

Prime by prime: `v_p(m s) = min(v_p(m s), v_p([1,…,l])) + #{j : l < p^j, p^j | m s}`; the first
part is bounded by `(Σ_s w s)·v_p([1,…,l])` using the weights, and the second by `E` times the
number of positions whose window contains a multiple of `p^j`, which is exactly what the
`L^{≥l}`/`ppFac` factors count. -/
theorem pow_prod_dvd_window (l D : ℕ) {d : ℕ} (n m w : Fin d → ℕ) (E : ℕ)
    (hE : ∀ s, w s ≤ E) (hpos : ∀ s, m s = 0 ∨ (n s - D ≤ m s ∧ m s ≤ n s)) :
    (∏ s : Fin d, (max 1 (m s)) ^ (w s)) ∣
      (Submission.CDTPlan.lcmUpto l) ^ (∑ s : Fin d, w s) *
        (∏ s : Fin d, Submission.CDT.LcmGe.Lge l (n s) D) ^ E *
        (∏ s : Fin d, Work.Holonomy3.ppFac l (n s)) ^ E := by
  have hstep : ∀ s : Fin d, (max 1 (m s)) ^ (w s)
      ∣ (Submission.CDTPlan.lcmUpto l) ^ (w s) * (Submission.CDT.LcmGe.Lge l (n s) D) ^ E
        * (ppFac l (n s)) ^ E :=
    fun s => step l D (n s) (m s) (w s) E (hE s) (hpos s)
  have h1 : (∏ s : Fin d, (max 1 (m s)) ^ (w s))
      ∣ (∏ s : Fin d, (Submission.CDTPlan.lcmUpto l) ^ (w s)
          * (Submission.CDT.LcmGe.Lge l (n s) D) ^ E * (ppFac l (n s)) ^ E) :=
    Finset.prod_dvd_prod_of_dvd (s := Finset.univ)
      (f := fun s : Fin d => (max 1 (m s)) ^ (w s))
      (g := fun s : Fin d => (Submission.CDTPlan.lcmUpto l) ^ (w s)
          * (Submission.CDT.LcmGe.Lge l (n s) D) ^ E * (ppFac l (n s)) ^ E)
      (fun s _ => hstep s)
  have hprod : (∏ s : Fin d, (Submission.CDTPlan.lcmUpto l) ^ (w s)
        * (Submission.CDT.LcmGe.Lge l (n s) D) ^ E * (ppFac l (n s)) ^ E)
      = (Submission.CDTPlan.lcmUpto l) ^ (∑ s : Fin d, w s)
        * (∏ s : Fin d, Submission.CDT.LcmGe.Lge l (n s) D) ^ E
        * (∏ s : Fin d, Work.Holonomy3.ppFac l (n s)) ^ E := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.prod_pow, Finset.prod_pow]
  rw [hprod] at h1
  exact h1

end Work.Holonomy3
