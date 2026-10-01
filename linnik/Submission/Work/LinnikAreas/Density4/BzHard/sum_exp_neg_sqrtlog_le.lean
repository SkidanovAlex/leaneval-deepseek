import Mathlib

namespace Work.LinnikAreas.Density4.BzHard

/-- Pointwise comparison for the tail terms: if `m` exceeds `√N` (in the sense that it is
larger than `Nat.sqrt N`, hence larger than the real square root of `N`), then the exponential
weight `exp (-(c √(log m)))` is dominated by `exp (-(c/4) √(log N))`. -/
private lemma ptwise_exp_le {c : ℝ} (hc : 0 < c) {N m : ℕ} (hN : 2 ≤ N)
    (hm : Nat.sqrt N < m) :
    Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))) ≤
      Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hle1 : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h := Nat.sqrt_le' N
    exact_mod_cast h
  have hlt2 : Real.sqrt (N : ℝ) < (Nat.sqrt N : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    have h := Nat.lt_succ_sqrt' N
    exact_mod_cast h
  have hmge : (Nat.sqrt N : ℝ) + 1 ≤ (m : ℝ) := by
    have : Nat.sqrt N + 1 ≤ m := Nat.succ_le_of_lt hm
    exact_mod_cast this
  have hsqrt : Real.sqrt (N : ℝ) < (m : ℝ) := by linarith
  have hsNpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hloglt : Real.log (Real.sqrt (N : ℝ)) < Real.log (m : ℝ) := Real.log_lt_log hsNpos hsqrt
  rw [Real.log_sqrt (le_of_lt hNpos)] at hloglt
  have hlogle : Real.log (N : ℝ) / 2 ≤ Real.log (m : ℝ) := le_of_lt hloglt
  have hLN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hsqrtm : Real.sqrt (Real.log (N : ℝ) / 2) ≤ Real.sqrt (Real.log (m : ℝ)) :=
    Real.sqrt_le_sqrt hlogle
  have h14 : (1 / 4 : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤ Real.sqrt (Real.log (N : ℝ) / 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    rw [mul_pow, Real.sq_sqrt hLN]
    nlinarith
  have hquart : (1 / 4 : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤ Real.sqrt (Real.log (m : ℝ)) :=
    le_trans h14 hsqrtm
  apply Real.exp_le_exp.mpr
  nlinarith [hquart, hc]

/-- Arithmetic companion: `Nat.sqrt N` stays below `2 · exp((c/4)^2) · N · exp (-(c/4)√(log N))`.
This is the step that absorbs the contribution of the small indices `m ≤ √N`. -/
private lemma sqrt_le_exp_mul {c : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    (Nat.sqrt N : ℝ) ≤ 2 * Real.exp ((c / 4) ^ 2) * (N : ℝ) *
      Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hMs : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h := Nat.sqrt_le' N
    exact_mod_cast h
  refine le_trans hMs ?_
  set L := Real.log (N : ℝ) with hL
  set A := (c / 4) ^ 2 with hA
  set X := A + L / 2 - (c / 4) * Real.sqrt L with hXdef
  have hLnn : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hX : 0 ≤ X := by
    rw [hXdef, hA]
    have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLnn
    nlinarith [sq_nonneg ((c / 4) - Real.sqrt L / 2), hs, hLnn]
  have hsqrt_eq : Real.sqrt (N : ℝ) = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos, hL]; ring_nf
  rw [hsqrt_eq]
  have hN_eq : (N : ℝ) = Real.exp L := by rw [hL]; exact (Real.exp_log hNpos).symm
  rw [hN_eq]
  have hexpX : 1 ≤ Real.exp X := Real.one_le_exp hX
  have hALB : A + L + (-(c / 4) * Real.sqrt L) = L / 2 + X := by rw [hXdef]; ring
  have hinner : Real.exp A * Real.exp L * Real.exp (-(c / 4) * Real.sqrt L)
      = Real.exp (L / 2 + X) := by
    rw [← Real.exp_add, ← Real.exp_add, hALB]
  rw [show 2 * Real.exp A * Real.exp L * Real.exp (-(c / 4) * Real.sqrt L)
        = 2 * (Real.exp A * Real.exp L * Real.exp (-(c / 4) * Real.sqrt L)) by ring,
      hinner, Real.exp_add]
  have h2 : (1 : ℝ) ≤ 2 * Real.exp X := by linarith
  have hnn : (0 : ℝ) ≤ Real.exp (L / 2) := Real.exp_nonneg _
  nlinarith [h2, hnn]

theorem sum_exp_neg_sqrtlog_le {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ m ∈ Finset.Icc 1 (N - 1), Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))))
        ≤ C * (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by
  refine ⟨1 + 2 * Real.exp ((c / 4) ^ 2), by positivity, ?_⟩
  intro N hN
  have hM1 : 1 ≤ Nat.sqrt N := Nat.le_sqrt.2 (by omega)
  have hMN : Nat.sqrt N ≤ N - 1 := by
    have := Nat.sqrt_lt_self (show 1 < N by omega); omega
  have hunion : Finset.Icc 1 (N - 1)
      = Finset.Icc 1 (Nat.sqrt N) ∪ Finset.Icc (Nat.sqrt N + 1) (N - 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 (Nat.sqrt N))
      (Finset.Icc (Nat.sqrt N + 1) (N - 1)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1 hx2; omega
  rw [hunion, Finset.sum_union hdisj]
  have hS1 : (∑ m ∈ Finset.Icc 1 (Nat.sqrt N),
        Real.exp (-(c * Real.sqrt (Real.log (m : ℝ))))) ≤ (Nat.sqrt N : ℝ) := by
    calc (∑ m ∈ Finset.Icc 1 (Nat.sqrt N),
            Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))))
        ≤ ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), (1 : ℝ) := by
          apply Finset.sum_le_sum; intro m hm
          rw [Finset.mem_Icc] at hm
          rw [Real.exp_le_one_iff]
          have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm.1)
          have hs : 0 ≤ Real.sqrt (Real.log (m : ℝ)) := Real.sqrt_nonneg _
          nlinarith [mul_nonneg hc.le hs]
      _ = (Nat.sqrt N : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc]
          simp
  have hS2 : (∑ m ∈ Finset.Icc (Nat.sqrt N + 1) (N - 1),
        Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))))
      ≤ (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by
    calc (∑ m ∈ Finset.Icc (Nat.sqrt N + 1) (N - 1),
            Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))))
        ≤ ∑ m ∈ Finset.Icc (Nat.sqrt N + 1) (N - 1),
            Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by
          apply Finset.sum_le_sum; intro m hm
          rw [Finset.mem_Icc] at hm
          exact ptwise_exp_le hc hN (by omega)
      _ = (Finset.Icc (Nat.sqrt N + 1) (N - 1)).card •
            Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := Finset.sum_const _
      _ ≤ (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by
          rw [nsmul_eq_mul]
          have hcard_nat : (Finset.Icc (Nat.sqrt N + 1) (N - 1)).card ≤ N := by
            rw [Nat.card_Icc]; omega
          have hcard : ((Finset.Icc (Nat.sqrt N + 1) (N - 1)).card : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast hcard_nat
          exact mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
  have hMb := sqrt_le_exp_mul (c := c) hN
  calc (∑ m ∈ Finset.Icc 1 (Nat.sqrt N),
          Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))))
        + (∑ m ∈ Finset.Icc (Nat.sqrt N + 1) (N - 1),
          Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))))
      ≤ (Nat.sqrt N : ℝ) + (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) :=
        add_le_add hS1 hS2
    _ ≤ 2 * Real.exp ((c / 4) ^ 2) * (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ)))
          + (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by linarith [hMb]
    _ = (1 + 2 * Real.exp ((c / 4) ^ 2)) * (N : ℝ) *
          Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by ring

end Work.LinnikAreas.Density4.BzHard
