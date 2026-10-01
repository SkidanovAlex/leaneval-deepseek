import Mathlib
import Submission.Work.LinnikAreas.BGTZ.MuRBasic
import Submission.Work.LinnikAreas.BGTZ.fiber_single_general
import Submission.Work.LinnikAreas.BGTZ.linnik_rhs_reindex
import Submission.Work.LinnikAreas.BGTZ.muDivSumIdentity

namespace Work.LinnikAreas.BGTZ

/-- Outer index set of the reindexing identity: multiples of `k` up to `R` coprime to `Q0`. -/
abbrev reindexA (R k Q0 : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter (fun d => k ∣ d ∧ Nat.Coprime d Q0)

/-- Inner index set of the reindexing identity: squarefree `r ≤ R/d` coprime to `d`. -/
abbrev reindexB (R d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d ∧ Squarefree r)

/-! The three arithmetic inputs of the reindexing below are proved in their own modules and
imported above: `fiber_single_general` (singleton-fibre evaluation), `linnik_rhs_reindex`
(the right-hand reindexing `m ↦ k * m`) and `muDivSumIdentity` (the Möbius divisor-sum
identity, proved in `BGTZ/muDivSumIdentity.lean`). -/

theorem moebius_reindex (g : ℕ → ℝ) (hg1 : g 1 = 1)
    (hgmul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    (R k Q0 : ℕ) (hk : Squarefree k) (hk1 : 1 ≤ k) (hkQ0 : Nat.Coprime k Q0)
    (hQ0 : Squarefree Q0) :
    (∑ d ∈ (Finset.Icc 1 R).filter (fun d => k ∣ d ∧ Nat.Coprime d Q0),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (∑ r ∈ (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d ∧ Squarefree r),
            1 / g r) / g d)
      = (((ArithmeticFunction.moebius k : ℤ) : ℝ) / g k) *
          ∑ m ∈ (Finset.Icc 1 R).filter (fun m => k * m ≤ R ∧ m ∣ Q0), 1 / g m := by
  classical
  simp only [one_div]
  change (∑ d ∈ reindexA R k Q0, muR d * (∑ r ∈ reindexB R d, (g r)⁻¹) / g d)
      = (muR k / g k) *
          ∑ m ∈ (Finset.Icc 1 R).filter (fun m => k * m ≤ R ∧ m ∣ Q0), (g m)⁻¹
  -- Step 1: expand the outer sum into a double sum
  have h1 : (∑ d ∈ reindexA R k Q0, muR d * (∑ r ∈ reindexB R d, (g r)⁻¹) / g d)
      = ∑ d ∈ reindexA R k Q0, ∑ r ∈ reindexB R d, muR d * (g d)⁻¹ * (g r)⁻¹ := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [h1]
  -- Step 2: convert to a sum over the sigma type
  rw [Finset.sum_sigma']
  -- Step 3: fibre over the product `d * r`
  have hmap : ∀ x ∈ (reindexA R k Q0).sigma (reindexB R), x.1 * x.2 ∈ Finset.Icc 1 R := by
    rintro ⟨a, b⟩ hx
    simp only [Finset.mem_sigma] at hx
    obtain ⟨ha, hb⟩ := hx
    simp only [reindexA, Finset.mem_filter, Finset.mem_Icc] at ha
    simp only [reindexB, Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨ha1, haR⟩, -⟩ := ha
    obtain ⟨⟨hb1, hbR⟩, -⟩ := hb
    simp only [Finset.mem_Icc]
    have hbR' : b * a ≤ R := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hbR
    have hpos : 0 < a * b := Nat.mul_pos (by omega) (by omega)
    exact ⟨by omega, by rw [mul_comm]; exact hbR'⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to (s := (reindexA R k Q0).sigma (reindexB R))
    (t := Finset.Icc 1 R) (g := fun x : Sigma (fun _ : ℕ => ℕ) => x.1 * x.2) hmap
    (fun x : Sigma (fun _ : ℕ => ℕ) => muR x.1 * (g x.1)⁻¹ * (g x.2)⁻¹)
  rw [← hfiber]
  -- Step 4: evaluate each fibre
  have hstep4 : ∀ n ∈ Finset.Icc 1 R,
      (∑ x ∈ ((reindexA R k Q0).sigma (reindexB R)).filter (fun x => x.1 * x.2 = n),
          muR x.1 * (g x.1)⁻¹ * (g x.2)⁻¹)
        = (g n)⁻¹ * (if (k ∣ n ∧ n / k ∣ Q0) then muR k else 0) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnR⟩ := hn
    rw [Finset.sum_filter]
    rw [Finset.sum_sigma]
    have hinner : ∀ a ∈ reindexA R k Q0,
        (∑ r ∈ reindexB R a, (if a * r = n then muR a * (g a)⁻¹ * (g r)⁻¹ else 0))
          = (if a ∣ n ∧ n / a ∈ reindexB R a then
              muR a * (g a)⁻¹ * (g (n / a))⁻¹ else 0) := by
      intro a ha
      simp only [reindexA, Finset.mem_filter, Finset.mem_Icc] at ha
      exact fiber_single_general (reindexB R a) a n (by omega)
        (fun r => muR a * (g a)⁻¹ * (g r)⁻¹)
    rw [Finset.sum_congr rfl hinner]
    have hstep : ∀ a ∈ reindexA R k Q0,
        (if a ∣ n ∧ n / a ∈ reindexB R a then
              muR a * (g a)⁻¹ * (g (n / a))⁻¹ else 0)
          = (if a ∣ n ∧ Nat.Coprime a (n / a) ∧ Squarefree (n / a) then
              muR a * (g n)⁻¹ else 0) := by
      intro a ha
      simp only [reindexA, Finset.mem_filter, Finset.mem_Icc] at ha
      obtain ⟨⟨ha1, haR⟩, -⟩ := ha
      have hapos : 0 < a := by omega
      by_cases hdvd : a ∣ n
      · have hmemiff : n / a ∈ reindexB R a ↔ Nat.Coprime a (n / a) ∧ Squarefree (n / a) := by
          rw [reindexB, Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨_, hc, hs⟩
            exact ⟨Nat.coprime_comm.mp hc, hs⟩
          · rintro ⟨hc, hs⟩
            exact ⟨⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hapos,
              Nat.div_le_div_right hnR⟩, Nat.coprime_comm.mpr hc, hs⟩
        by_cases hmem : n / a ∈ reindexB R a
        · have hc : Nat.Coprime a (n / a) ∧ Squarefree (n / a) := hmemiff.mp hmem
          rw [if_pos ⟨hdvd, hmem⟩, if_pos ⟨hdvd, hc.1, hc.2⟩]
          have hgn : g n = g a * g (n / a) := by
            conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
            exact hgmul a (n / a) hc.1
          rw [hgn, mul_inv_rev]
          ring
        · have hc : ¬ (Nat.Coprime a (n / a) ∧ Squarefree (n / a)) :=
            fun h => hmem (hmemiff.mpr h)
          rw [if_neg (fun h => hmem h.2), if_neg (fun h => hc ⟨h.2.1, h.2.2⟩)]
      · rw [if_neg (fun h => hdvd h.1), if_neg (fun h => hdvd h.1)]
    rw [Finset.sum_congr rfl hstep]
    have hfac : (∑ a ∈ reindexA R k Q0,
          (if a ∣ n ∧ Nat.Coprime a (n / a) ∧ Squarefree (n / a) then
              muR a * (g n)⁻¹ else 0))
        = (g n)⁻¹ * (∑ a ∈ reindexA R k Q0,
          (if a ∣ n ∧ Nat.Coprime a (n / a) ∧ Squarefree (n / a) then muR a else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      by_cases h : a ∣ n ∧ Nat.Coprime a (n / a) ∧ Squarefree (n / a)
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h, mul_zero]
    rw [hfac]
    congr 1
    have hset : (reindexA R k Q0).filter
          (fun d => d ∣ n ∧ Nat.Coprime d (n / d) ∧ Squarefree (n / d))
        = n.divisors.filter
          (fun d => k ∣ d ∧ Nat.Coprime d Q0 ∧ Nat.Coprime d (n / d) ∧ Squarefree (n / d)) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨⟨hd1, hdR⟩, hk', hQ'⟩, hdvd, hc, hs⟩
        exact ⟨⟨hdvd, Nat.one_le_iff_ne_zero.mp hn1⟩, hk', hQ', hc, hs⟩
      · rintro ⟨⟨hdvd, hn0⟩, hk', hQ', hc, hs⟩
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
        exact ⟨⟨⟨by omega, Nat.le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd) hnR⟩,
          hk', hQ'⟩, hdvd, hc, hs⟩
    rw [← Finset.sum_filter, hset]
    exact muDivSumIdentity k Q0 n hk hk1 hkQ0 hQ0
  rw [Finset.sum_congr rfl hstep4]
  -- Step 5: identify the surviving sum with the right-hand side
  have hfin : (∑ n ∈ Finset.Icc 1 R,
        (g n)⁻¹ * (if (k ∣ n ∧ n / k ∣ Q0) then muR k else 0))
      = muR k * ∑ n ∈ (Finset.Icc 1 R).filter (fun n => k ∣ n ∧ n / k ∣ Q0), (g n)⁻¹ := by
    rw [Finset.mul_sum]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : k ∣ n ∧ n / k ∣ Q0
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hfin]
  rw [← linnik_rhs_reindex g hgmul R k Q0 hk1 hkQ0]
  rw [div_eq_mul_inv]
  ring

end Work.LinnikAreas.BGTZ
