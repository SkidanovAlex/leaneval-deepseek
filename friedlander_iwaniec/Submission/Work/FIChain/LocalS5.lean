/-
  Companion paper (§5): estimation of `T(x;Y,Z)`.

  `T(x;y;z) = ∑_{b ≤ y} μ(b) ∑_{c ≤ z} Λ(c) V_{bc}(x)` (the object `Tsum2` of `Defs.lean`).
  We collect here the two analytic ingredients of the estimate `T ≪ A(x)(log x)^{-2}`:
  * the `Λ`-congruence sum over `c` (§5's "by (2.4), (1.8)"),
  * the fibre exchange `∑_b ∑_c Λ(c) X(bc) ≤ ∑_d (log d) X(d)` used for the remainder terms.
-/
import Mathlib
import Submission.ASP.Defs
import Submission.Work.FIChain.LocalS4

namespace Submission.ASP

open Finset

noncomputable section

/-! ### Vanishing of `V_d` for non-squarefree moduli -/

/-- Under (1.16) (`a` supported on squarefree numbers), `V_d(x) = 0` whenever `d` is not squarefree
(this is why the `Λ`-sums of §§5–8 are automatically restricted to squarefree moduli). -/
lemma Vb_eq_zero_of_not_squarefree {a lam : ℕ → ℝ} (ha : ∀ n : ℕ, ¬ Squarefree n → a n = 0)
    {d : ℕ} (hd : ¬ Squarefree d) (x : ℝ) : Vb a lam d x = 0 := by
  rw [Vb]
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_filter] at hn
  have hnns : ¬ Squarefree n := fun h => hd (h.squarefree_of_dvd hn.2)
  rw [ha n hnns, zero_mul]

/-! ### The `Λ`-fibre exchange of §5 -/

/-- `∑_{b ≤ M} ∑_{c ≤ P} Λ(c) X(bc) ≤ ∑_{d ≤ MP} (log d) X(d)` for `X ≥ 0`: the fibre of
`(b,c) ↦ bc` over `d` carries the weight `∑_{c ∣ d} Λ(c) = log d`. -/
theorem sum_vonMangoldt_mul_le {M P : ℕ} {X : ℕ → ℝ} (hX : ∀ d : ℕ, 0 ≤ X d) :
    (∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
        ArithmeticFunction.vonMangoldt c * X (b * c))
      ≤ ∑ d ∈ Finset.Icc 1 (M * P), Real.log (d : ℝ) * X d := by
  classical
  have hmaps : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 P),
      p.1 * p.2 ∈ Finset.Icc 1 (M * P) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hp1a, hp1b⟩ := Finset.mem_Icc.mp hp1
    obtain ⟨hp2a, hp2b⟩ := Finset.mem_Icc.mp hp2
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega)), Nat.mul_le_mul hp1b hp2b⟩
  have hprod : (∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
        ArithmeticFunction.vonMangoldt c * X (b * c))
      = ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 P),
          ArithmeticFunction.vonMangoldt p.2 * X (p.1 * p.2) :=
    (Finset.sum_product _ _ (fun p : ℕ × ℕ => ArithmeticFunction.vonMangoldt p.2 * X (p.1 * p.2))).symm
  rw [hprod]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (f := fun p : ℕ × ℕ => ArithmeticFunction.vonMangoldt p.2 * X (p.1 * p.2))]
  apply Finset.sum_le_sum
  intro d hd
  set F := ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 P)).filter (fun p : ℕ × ℕ => p.1 * p.2 = d)
    with hF
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) ↑F := by
    intro p hp q hq hpq
    rw [hF, Finset.mem_coe, Finset.mem_filter] at hp hq
    have hp2 : 0 < p.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp.1).2).1
    have hq2 : 0 < q.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hq.1).2).1
    have h1 : p.1 = d / p.2 := by
      rw [← hp.2, Nat.mul_div_cancel p.1 hp2]
    have h2 : q.1 = d / q.2 := by
      rw [← hq.2, Nat.mul_div_cancel q.1 hq2]
    have hpq' : p.2 = q.2 := hpq
    have : p.1 = q.1 := by rw [h1, h2, hpq']
    exact Prod.ext this hpq
  have hfiber : (∑ p ∈ F, ArithmeticFunction.vonMangoldt p.2 * X (p.1 * p.2))
      = (∑ p ∈ F, ArithmeticFunction.vonMangoldt p.2) * X d := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hF, Finset.mem_filter] at hp
    rw [hp.2]
  rw [hfiber]
  refine mul_le_mul_of_nonneg_right ?_ (hX d)
  have hsub : F.image (fun p : ℕ × ℕ => p.2) ⊆ d.divisors := by
    intro c hc
    obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hc
    rw [hF, Finset.mem_filter] at hp
    rw [← hpc]
    exact Nat.mem_divisors.mpr ⟨⟨p.1, by rw [mul_comm, hp.2]⟩, by omega⟩
  calc (∑ p ∈ F, ArithmeticFunction.vonMangoldt p.2)
      = ∑ c ∈ F.image (fun p : ℕ × ℕ => p.2), ArithmeticFunction.vonMangoldt c :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ c ∈ d.divisors, ArithmeticFunction.vonMangoldt c :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun c _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log (d : ℝ) := ArithmeticFunction.vonMangoldt_sum

/-- The `Λ`-fibre exchange of §5 in the **squarefree** form: the left-hand sum vanishes unless
`b * c` is squarefree, so the fibre sums may be restricted to squarefree `d`, on which the fibre
weight is `∑_{c ∣ d, c prime} log c = log d`. -/
theorem sum_vonMangoldt_mul_le_sqfree {M P : ℕ} {X : ℕ → ℝ} (hX : ∀ d : ℕ, 0 ≤ X d) :
    (∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
        ArithmeticFunction.vonMangoldt c *
          (if Squarefree (b * c) then X (b * c) else 0))
      ≤ ∑ d ∈ (Finset.Icc 1 (M * P)).filter Squarefree, Real.log (d : ℝ) * X d := by
  classical
  set s : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 P)).filter (fun p => Squarefree (p.1 * p.2)) with hs
  have hmaps : ∀ p ∈ s, p.1 * p.2 ∈ (Finset.Icc 1 (M * P)).filter Squarefree := by
    intro p hp
    rw [hs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hpsf⟩ := hp
    obtain ⟨hp1a, hp1b⟩ := Finset.mem_Icc.mp hp1
    obtain ⟨hp2a, hp2b⟩ := Finset.mem_Icc.mp hp2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega)), Nat.mul_le_mul hp1b hp2b⟩, hpsf⟩
  have hprod : (∑ p ∈ s, ArithmeticFunction.vonMangoldt p.2 * X (p.1 * p.2))
      = ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
          ArithmeticFunction.vonMangoldt c *
            (if Squarefree (b * c) then X (b * c) else 0) := by
    rw [hs, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : Squarefree (b * c) <;> simp [h]
  rw [← hprod]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (t := (Finset.Icc 1 (M * P)).filter Squarefree)
    (f := fun p : ℕ × ℕ => ArithmeticFunction.vonMangoldt p.2 * X (p.1 * p.2))]
  apply Finset.sum_le_sum
  intro d hd
  set F : Finset (ℕ × ℕ) := s.filter (fun p : ℕ × ℕ => p.1 * p.2 = d) with hF
  have hmem : ∀ p ∈ F, 0 < p.2 := by
    intro p hp
    rw [hF, Finset.mem_filter, hs, Finset.mem_filter, Finset.mem_product] at hp
    exact (Finset.mem_Icc.mp hp.1.1.2).1
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) ↑F := by
    intro p hp q hq hpq
    rw [hF, Finset.mem_coe, Finset.mem_filter] at hp hq
    have hp2 : 0 < p.2 := hmem p (by rw [hF, Finset.mem_filter]; exact hp)
    have hq2 : 0 < q.2 := hmem q (by rw [hF, Finset.mem_filter]; exact hq)
    have h1 : p.1 = d / p.2 := by rw [← hp.2, Nat.mul_div_cancel p.1 hp2]
    have h2 : q.1 = d / q.2 := by rw [← hq.2, Nat.mul_div_cancel q.1 hq2]
    have hpq' : p.2 = q.2 := hpq
    exact Prod.ext (by rw [h1, h2, hpq']) hpq'
  have hfiber : (∑ p ∈ F, ArithmeticFunction.vonMangoldt p.2 * X (p.1 * p.2))
      = (∑ p ∈ F, ArithmeticFunction.vonMangoldt p.2) * X d := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hF, Finset.mem_filter] at hp
    rw [hp.2]
  rw [hfiber]
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  refine mul_le_mul_of_nonneg_right ?_ (hX d)
  have hsub : F.image (fun p : ℕ × ℕ => p.2) ⊆ d.divisors := by
    intro c hc
    obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hc
    rw [hF, Finset.mem_filter] at hp
    rw [← hpc]
    exact Nat.mem_divisors.mpr ⟨⟨p.1, by rw [mul_comm, hp.2]⟩, by omega⟩
  calc (∑ p ∈ F, ArithmeticFunction.vonMangoldt p.2)
      = ∑ c ∈ F.image (fun p : ℕ × ℕ => p.2), ArithmeticFunction.vonMangoldt c :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ c ∈ d.divisors, ArithmeticFunction.vonMangoldt c :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun c _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log (d : ℝ) := ArithmeticFunction.vonMangoldt_sum

/-! ### The `Λ`-congruence sum over `c` (§5, "by (2.4), (1.8)") -/

/-- `∑_{n ≤ z} 1/n ≤ log z + 1`. -/
lemma sum_inv_Icc_le_log_add_one (z : ℕ) :
    (∑ n ∈ Finset.Icc 1 z, ((n : ℝ))⁻¹) ≤ Real.log (z : ℝ) + 1 := by
  induction z with
  | zero => simp
  | succ z ih =>
    rcases Nat.eq_zero_or_pos z with hz | hz
    · subst hz; simp
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ z + 1)]
    have hstep : (((z + 1 : ℕ)) : ℝ)⁻¹ ≤ Real.log (((z + 1 : ℕ)) : ℝ) - Real.log (z : ℝ) := by
      have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
      have hx : (0 : ℝ) < ((z : ℝ) + 1) / (z : ℝ) := by positivity
      have h := Real.one_sub_inv_le_log_of_pos hx
      rw [inv_div] at h
      rw [Real.log_div (by positivity) (by positivity)] at h
      have h2 : 1 - (z : ℝ) / ((z : ℝ) + 1) = (((z : ℝ) + 1))⁻¹ := by
        field_simp
        ring
      rw [h2] at h
      simp only [Nat.cast_add, Nat.cast_one]
      exact h
    linarith

/-- `∑_{p ≤ z} (log p) g(p) ≤ C (log z + 1)²`, from (1.8). -/
lemma sum_primes_log_mul_g_le {g : ℕ → ℝ} (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z →
      (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) * g p)
        ≤ C * (Real.log (z : ℝ) + 1) ^ 2 := by
  obtain ⟨Cb, hCbpos, hCb⟩ := hbound
  have hmaxpos : (0 : ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max Cb 1, hmaxpos, fun z hz => ?_⟩
  have hz1 : (0 : ℝ) ≤ Real.log (z : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
  calc (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) * g p)
      ≤ ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (z : ℝ) * (max Cb 1 * ((p : ℝ))⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp'
        rw [Finset.mem_filter, Finset.mem_Icc] at hp'
        have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp'.2.pos
        have hlogp : Real.log (p : ℝ) ≤ Real.log (z : ℝ) :=
          Real.log_le_log hppos (by exact_mod_cast hp'.1.2)
        have hgp : g p ≤ Cb / (p : ℝ) := hCb p hp'.2
        have hle : Cb / (p : ℝ) ≤ max Cb 1 / (p : ℝ) :=
          div_le_div_of_nonneg_right (le_max_left _ _) hppos.le
        calc Real.log (p : ℝ) * g p
            ≤ Real.log (z : ℝ) * (max Cb 1 / (p : ℝ)) :=
              mul_le_mul hlogp (le_trans hgp hle) (hp p hp'.2) hz1
          _ = Real.log (z : ℝ) * (max Cb 1 * ((p : ℝ))⁻¹) := by rw [div_eq_mul_inv]
    _ = Real.log (z : ℝ) * max Cb 1
          * ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, ((p : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ ≤ Real.log (z : ℝ) * max Cb 1 * (Real.log (z : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
          (sum_inv_Icc_le_log_add_one z)
        · intro p hp'; exact (Finset.mem_filter.mp hp').1
        · intro p _ _; positivity
    _ ≤ max Cb 1 * (Real.log (z : ℝ) + 1) ^ 2 := by
        have hM : 0 ≤ max Cb 1 := le_trans (by norm_num) (le_max_right _ _)
        have h2 : 0 ≤ Real.log (z : ℝ) + 1 := by linarith
        calc Real.log (z : ℝ) * max Cb 1 * (Real.log (z : ℝ) + 1)
            = max Cb 1 * (Real.log (z : ℝ) * (Real.log (z : ℝ) + 1)) := by ring
          _ ≤ max Cb 1 * ((Real.log (z : ℝ) + 1) * (Real.log (z : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) h2) hM
          _ = max Cb 1 * (Real.log (z : ℝ) + 1) ^ 2 := by ring

/-- **§5**: `∑_{p ≤ z} (log p) g(p/(ν,p)) ≤ C (log(ν z + 2))²` for squarefree `ν ≥ 1`, `z ≥ 2`. -/
theorem sum_primes_log_mul_g_div_gcd_le {g : ℕ → ℝ}
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν z : ℕ, Squarefree ν → 2 ≤ z →
      (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) * g (p / Nat.gcd ν p))
        ≤ C * (Real.log ((ν : ℝ) * (z : ℝ) + 2)) ^ 2 := by
  obtain ⟨Cb, hCbpos, hCb⟩ := hbound
  obtain ⟨C1, hC1pos, hC1⟩ := sum_primes_log_mul_g_le hp ⟨Cb, hCbpos, hCb⟩
  refine ⟨2 + 4 * C1, by positivity, fun ν z hν hz => ?_⟩
  -- split the `p`-sum according to `p ∣ ν`
  have hsplit : (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) * g (p / Nat.gcd ν p))
      = (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, if p ∣ ν then Real.log (p : ℝ) else 0)
        + ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime,
            if p ∣ ν then 0 else Real.log (p : ℝ) * g p := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp'
    rw [Finset.mem_filter] at hp'
    by_cases hpd : p ∣ ν
    · rw [if_pos hpd, if_pos hpd]
      have hgcd : Nat.gcd ν p = p := by rw [Nat.gcd_comm ν p, Nat.gcd_eq_left hpd]
      rw [hgcd, Nat.div_self hp'.2.pos, hg1]
      ring
    · rw [if_neg hpd, if_neg hpd]
      have hcop : Nat.Coprime ν p := (hp'.2.coprime_iff_not_dvd.mpr hpd).symm
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.div_one]
      ring
  -- the primes dividing `ν`
  have hbound1 : (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, if p ∣ ν then Real.log (p : ℝ) else 0)
      ≤ Real.log (ν : ℝ) := by
    rw [← Finset.sum_filter]
    have h1 : ∀ p ∈ ((Finset.Icc 1 z).filter Nat.Prime).filter (fun p => p ∣ ν),
        Real.log (p : ℝ) = ArithmeticFunction.vonMangoldt p := by
      intro p hp'
      rw [Finset.mem_filter, Finset.mem_filter] at hp'
      exact (ArithmeticFunction.vonMangoldt_apply_prime hp'.1.2).symm
    have hsub : ((Finset.Icc 1 z).filter Nat.Prime).filter (fun p => p ∣ ν) ⊆ ν.divisors := by
      intro p hp'
      rw [Finset.mem_filter, Finset.mem_filter] at hp'
      exact Nat.mem_divisors.mpr ⟨hp'.2, hν.ne_zero⟩
    calc (∑ p ∈ ((Finset.Icc 1 z).filter Nat.Prime).filter (fun p => p ∣ ν), Real.log (p : ℝ))
        = ∑ p ∈ ((Finset.Icc 1 z).filter Nat.Prime).filter (fun p => p ∣ ν),
            ArithmeticFunction.vonMangoldt p := Finset.sum_congr rfl h1
      _ ≤ ∑ c ∈ ν.divisors, ArithmeticFunction.vonMangoldt c :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun c _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Real.log (ν : ℝ) := ArithmeticFunction.vonMangoldt_sum
  -- the primes not dividing `ν`
  have hbound2 : (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime,
        if p ∣ ν then 0 else Real.log (p : ℝ) * g p)
      ≤ C1 * (Real.log (z : ℝ) + 1) ^ 2 := by
    refine le_trans (Finset.sum_le_sum (fun p hp' => ?_)) (hC1 z hz)
    rw [Finset.mem_filter] at hp'
    by_cases hpd : p ∣ ν
    · rw [if_pos hpd]
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp'.2.one_le)) (hp p hp'.2)
    · rw [if_neg hpd]
  rw [hsplit]
  refine le_trans (add_le_add hbound1 hbound2) ?_
  -- logarithmic comparison
  have hν1 : (1 : ℝ) ≤ (ν : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hν.ne_zero)
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have harg4 : (4 : ℝ) ≤ (ν : ℝ) * (z : ℝ) + 2 := by nlinarith
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    norm_num
  have hlarg : (1 : ℝ) < Real.log ((ν : ℝ) * (z : ℝ) + 2) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) harg4
    rw [hlog4] at h
    linarith [Real.log_two_gt_d9]
  have hlogz_le : Real.log (z : ℝ) ≤ Real.log ((ν : ℝ) * (z : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hlogν_le : Real.log (ν : ℝ) ≤ Real.log ((ν : ℝ) * (z : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have h2log2 : 2 * Real.log 2 ≤ Real.log ((ν : ℝ) * (z : ℝ) + 2) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) harg4
    rwa [hlog4] at h
  have hsum : Real.log (z : ℝ) + 1 ≤ 2 * Real.log ((ν : ℝ) * (z : ℝ) + 2) := by
    have h1 : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hsq : (Real.log (z : ℝ) + 1) ^ 2
      ≤ 4 * (Real.log ((ν : ℝ) * (z : ℝ) + 2)) ^ 2 := by
    have hL : 0 ≤ Real.log (z : ℝ) + 1 := by
      have h0 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ (z : ℝ))
      linarith
    nlinarith [hsum, hL, hlarg]
  have hνsq : Real.log (ν : ℝ) ≤ (Real.log ((ν : ℝ) * (z : ℝ) + 2)) ^ 2 := by
    nlinarith [hlogν_le, hlarg]
  have hC1nn : 0 ≤ C1 := le_of_lt hC1pos
  nlinarith [hνsq, hsq, hC1nn, hlarg]

end

end Submission.ASP
