import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Totient
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors

set_option autoImplicit false

namespace Commons.NumberTheory.Sieve

open Finset
open scoped ArithmeticFunction.Moebius


/-- Splitting a product with an inner indicator sum into a double sum with an indicator. -/
lemma ite_mul_sum_ite (T : Finset ℕ) (l d : ℕ) (m : ℝ) (w : ℕ → ℝ) :
    (if l ∣ d then m * (∑ e ∈ T, if d ∣ e then w e else 0) else 0)
      = ∑ e ∈ T, (if (l ∣ d ∧ d ∣ e) then m * w e else 0) := by
  by_cases h : l ∣ d
  · rw [if_pos h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hde : d ∣ e <;> simp [h, hde]
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]
    intro hc
    exact h hc.1

/-- For squarefree `e` and `l`, the sum of `μ` over the divisors of `e` that are multiples
of `l` is `μ l` if `e = l` and `0` otherwise. -/
lemma sum_moebius_divisors_filter_dvd (e l : ℕ) (he : e ≠ 0) (hsq : Squarefree e) :
    (∑ d ∈ e.divisors.filter (fun d => l ∣ d), (ArithmeticFunction.moebius d : ℝ))
      = if e = l then (ArithmeticFunction.moebius l : ℝ) else 0 := by
  by_cases hle : l ∣ e
  · have hlne : l ≠ 0 := by
      rintro rfl
      exact he (by simpa using hle)
    have hlpos : 0 < l := Nat.pos_of_ne_zero hlne
    have hqne : e / l ≠ 0 := by
      intro h
      have : e = l * (e / l) := (Nat.mul_div_cancel' hle).symm
      rw [h, mul_zero] at this
      exact he this
    have hbij : (∑ d ∈ e.divisors.filter (fun d => l ∣ d), (ArithmeticFunction.moebius d : ℝ))
        = ∑ k ∈ (e / l).divisors, (ArithmeticFunction.moebius (l * k) : ℝ) := by
      refine Finset.sum_bij'
        (fun d _ => d / l) (fun k _ => l * k) ?_ ?_ ?_ ?_ ?_
      · intro d hd
        rw [Finset.mem_filter] at hd
        obtain ⟨hdmem, hld⟩ := hd
        rw [Nat.mem_divisors]
        refine ⟨?_, hqne⟩
        have hdvde : d ∣ e := Nat.dvd_of_mem_divisors hdmem
        have h1 : d = l * (d / l) := (Nat.mul_div_cancel' hld).symm
        have h2 : e = l * (e / l) := (Nat.mul_div_cancel' hle).symm
        have h3 : l * (d / l) ∣ l * (e / l) := by rw [← h1, ← h2]; exact hdvde
        exact (Nat.mul_dvd_mul_iff_left hlpos).mp h3
      · intro k hk
        rw [Finset.mem_filter]
        have hkdiv : k ∣ e / l := Nat.dvd_of_mem_divisors hk
        refine ⟨Nat.mem_divisors.mpr ⟨?_, he⟩, dvd_mul_right l k⟩
        obtain ⟨c, hc⟩ := hkdiv
        refine ⟨c, ?_⟩
        calc e = l * (e / l) := (Nat.mul_div_cancel' hle).symm
          _ = l * (k * c) := by rw [hc]
          _ = (l * k) * c := by ring
      · intro d hd
        exact (Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2)
      · intro k hk
        exact Nat.mul_div_right k hlpos
      · intro d hd
        rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2]
    rw [hbij]
    have hstep : (∑ k ∈ (e / l).divisors, (ArithmeticFunction.moebius (l * k) : ℝ))
        = (ArithmeticFunction.moebius l : ℝ) *
            (∑ k ∈ (e / l).divisors, (ArithmeticFunction.moebius k : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkdiv : k ∣ e / l := Nat.dvd_of_mem_divisors hk
      have hlk : l * k ∣ e := by
        obtain ⟨c, hc⟩ := hkdiv
        refine ⟨c, ?_⟩
        calc e = l * (e / l) := (Nat.mul_div_cancel' hle).symm
          _ = l * (k * c) := by rw [hc]
          _ = (l * k) * c := by ring
      have hsqlk : Squarefree (l * k) := hsq.squarefree_of_dvd hlk
      have hcop : Nat.Coprime l k := Nat.coprime_of_squarefree_mul hsqlk
      have hmu : ArithmeticFunction.moebius (l * k) =
          ArithmeticFunction.moebius l * ArithmeticFunction.moebius k :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      rw [hmu]
      push_cast
      ring
    rw [hstep]
    have hcast : (∑ k ∈ (e / l).divisors, (ArithmeticFunction.moebius k : ℝ))
        = if e / l = 1 then (1 : ℝ) else 0 := by
      have h2 : (∑ k ∈ (e / l).divisors, (ArithmeticFunction.moebius k : ℝ))
          = ((∑ k ∈ (e / l).divisors, ArithmeticFunction.moebius k : ℤ) : ℝ) := by
        push_cast
        ring
      rw [h2, Commons.NumberTheory.Moebius.sum_moebius_divisors]
      by_cases h1 : e / l = 1 <;> simp [h1]
    rw [hcast]
    have hiff : e / l = 1 ↔ e = l := by
      constructor
      · intro h1
        calc e = l * (e / l) := (Nat.mul_div_cancel' hle).symm
          _ = l * 1 := by rw [h1]
          _ = l := mul_one l
      · intro h1
        rw [h1, Nat.div_self hlpos]
    by_cases h1 : e / l = 1
    · rw [if_pos h1, if_pos (hiff.mp h1), mul_one]
    · rw [if_neg h1, mul_zero, if_neg (fun h => h1 (hiff.mpr h))]
  · have hempty : e.divisors.filter (fun d => l ∣ d) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro d hd
      rw [Finset.mem_filter] at hd
      exact hle (dvd_trans hd.2 (Nat.dvd_of_mem_divisors hd.1))
    rw [hempty, Finset.sum_empty]
    rw [if_neg]
    intro h
    exact hle (h ▸ dvd_rfl)

/-- Inner-sum identity of the Selberg sieve weights: for squarefree `M` and a divisor
`l ≤ D` of `M`, the double sum over pairs `l ∣ d ∣ e` of divisors of `M` with `e ≤ D`
of `μ(d)/φ(e)` collapses to `μ(l)/φ(l)`. -/
theorem selberg_weight_inner_sum (M D l : ℕ) (hM : 1 ≤ M) (hMsq : Squarefree M) (hD : 1 ≤ D)
    (hl : l ∈ M.divisors.filter (fun d : ℕ => d ≤ D)) :
    (∑ d ∈ (M.divisors.filter (fun d : ℕ => d ≤ D)).filter (fun d : ℕ => l ∣ d),
        (ArithmeticFunction.moebius d : ℝ) *
          (∑ e ∈ (M.divisors.filter (fun e : ℕ => e ≤ D)).filter (fun e : ℕ => d ∣ e),
             (1 : ℝ) / (Nat.totient e : ℝ)))
      = (ArithmeticFunction.moebius l : ℝ) / (Nat.totient l : ℝ) := by
  classical
  set T : Finset ℕ := M.divisors.filter (fun d : ℕ => d ≤ D) with hT
  have hMpos : 0 < M := hM
  have hMne : M ≠ 0 := hMpos.ne'
  have hlT : l ∈ T := hl
  have hlM : l ∣ M := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1
  have hlsq : Squarefree l := hMsq.squarefree_of_dvd hlM
  have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hlM hMpos
  have hTpos : ∀ d ∈ T, 0 < d := by
    intro d hd
    exact Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) hMpos
  have hTmem : ∀ {d e : ℕ}, d ∣ e → e ∈ T → d ∈ T := by
    intro d e hde he
    have heM : e ∣ M := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp he).1
    have heD : e ≤ D := (Finset.mem_filter.mp he).2
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨dvd_trans hde heM, hMne⟩,
      le_trans (Nat.le_of_dvd (hTpos e he) hde) heD⟩
  have step1 : (∑ d ∈ T.filter (fun d => l ∣ d),
        (ArithmeticFunction.moebius d : ℝ) *
          (∑ e ∈ T.filter (fun e => d ∣ e), (1 : ℝ) / (Nat.totient e : ℝ)))
      = ∑ d ∈ T, ∑ e ∈ T,
          (if (l ∣ d ∧ d ∣ e) then
            (ArithmeticFunction.moebius d : ℝ) * ((1 : ℝ) / (Nat.totient e : ℝ)) else 0) := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    exact ite_mul_sum_ite T l d (ArithmeticFunction.moebius d : ℝ)
      (fun e => (1 : ℝ) / (Nat.totient e : ℝ))
  have step3 : ∀ e ∈ T,
      (∑ d ∈ T, (if (l ∣ d ∧ d ∣ e) then
          (ArithmeticFunction.moebius d : ℝ) * ((1 : ℝ) / (Nat.totient e : ℝ)) else 0))
        = ((1 : ℝ) / (Nat.totient e : ℝ)) *
            (if e = l then (ArithmeticFunction.moebius l : ℝ) else 0) := by
    intro e he
    have hkey : (∑ d ∈ T, (if (l ∣ d ∧ d ∣ e) then (ArithmeticFunction.moebius d : ℝ) else 0))
        = if e = l then (ArithmeticFunction.moebius l : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      have hTeq : T.filter (fun d => l ∣ d ∧ d ∣ e) = e.divisors.filter (fun d => l ∣ d) := by
        ext d
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨_, hld, hde⟩
          exact ⟨Nat.mem_divisors.mpr ⟨hde, (hTpos e he).ne'⟩, hld⟩
        · rintro ⟨hdmem, hld⟩
          exact ⟨hTmem (Nat.dvd_of_mem_divisors hdmem) he, hld,
            Nat.dvd_of_mem_divisors hdmem⟩
      rw [hTeq]
      exact sum_moebius_divisors_filter_dvd e l (hTpos e he).ne'
        (hMsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp he).1))
    calc (∑ d ∈ T, (if (l ∣ d ∧ d ∣ e) then
            (ArithmeticFunction.moebius d : ℝ) * ((1 : ℝ) / (Nat.totient e : ℝ)) else 0))
        = ∑ d ∈ T, ((1 : ℝ) / (Nat.totient e : ℝ)) *
            (if (l ∣ d ∧ d ∣ e) then (ArithmeticFunction.moebius d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro d _
          by_cases hc : (l ∣ d ∧ d ∣ e) <;> simp [hc] <;> ring
      _ = ((1 : ℝ) / (Nat.totient e : ℝ)) *
            (∑ d ∈ T, (if (l ∣ d ∧ d ∣ e) then (ArithmeticFunction.moebius d : ℝ) else 0)) := by
          rw [Finset.mul_sum]
      _ = ((1 : ℝ) / (Nat.totient e : ℝ)) *
            (if e = l then (ArithmeticFunction.moebius l : ℝ) else 0) := by rw [hkey]
  have step4 : (∑ e ∈ T, ((1 : ℝ) / (Nat.totient e : ℝ)) *
        (if e = l then (ArithmeticFunction.moebius l : ℝ) else 0))
      = (ArithmeticFunction.moebius l : ℝ) / (Nat.totient l : ℝ) := by
    have hsum : (∑ e ∈ T, ((1 : ℝ) / (Nat.totient e : ℝ)) *
          (if e = l then (ArithmeticFunction.moebius l : ℝ) else 0))
        = ((1 : ℝ) / (Nat.totient l : ℝ)) * (ArithmeticFunction.moebius l : ℝ) := by
      have h1 := Finset.sum_eq_single_of_mem l hlT
        (f := fun e => ((1 : ℝ) / (Nat.totient e : ℝ)) *
          (if e = l then (ArithmeticFunction.moebius l : ℝ) else 0))
        (fun b _ hne => by rw [if_neg hne, mul_zero])
      rw [h1, if_pos rfl]
    rw [hsum]
    ring
  calc (∑ d ∈ T.filter (fun d => l ∣ d),
        (ArithmeticFunction.moebius d : ℝ) *
          (∑ e ∈ T.filter (fun e => d ∣ e), (1 : ℝ) / (Nat.totient e : ℝ)))
      = ∑ d ∈ T, ∑ e ∈ T,
          (if (l ∣ d ∧ d ∣ e) then
            (ArithmeticFunction.moebius d : ℝ) * ((1 : ℝ) / (Nat.totient e : ℝ)) else 0) := step1
    _ = ∑ e ∈ T, ∑ d ∈ T,
          (if (l ∣ d ∧ d ∣ e) then
            (ArithmeticFunction.moebius d : ℝ) * ((1 : ℝ) / (Nat.totient e : ℝ)) else 0) :=
          Finset.sum_comm
    _ = ∑ e ∈ T, ((1 : ℝ) / (Nat.totient e : ℝ)) *
            (if e = l then (ArithmeticFunction.moebius l : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          exact step3 e he
    _ = (ArithmeticFunction.moebius l : ℝ) / (Nat.totient l : ℝ) := step4

end Commons.NumberTheory.Sieve