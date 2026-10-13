import Mathlib
import Submission.Work.DSM4p.Chart
import Submission.Work.DSM4p.ChartUnit

/-!
# DSM4p — the monomial estimate (Bhatt, arXiv:1608.08882, Theorem 3.1(2))

This is the cokernel clause of the quantitative Riemann extension theorem for the chart
model `D n = Work.DSM4p.chartLevel hgr Q.ϖ n` of `Submission/Work/DSM4p/Chart.lean`, with
`t = ϖ` the pseudo-uniformiser and `g = gr 0` the element whose `p`-power roots are adjoined.

Stated elementwise, with `x_k(m) = ϖ_k^m / g_k` the chart generators:

  `∀ m k c J I n, p^(k+1)·m ≤ c → ∃ x : B, ϖ_k g_k · x_J(n+c)^I - x ∈ p^m · D n.`

The point is that the constant `c = p^(k+1)·m` is *uniform in `n`*, which is what makes the
almost-pro-isomorphism of Theorem 3.1 "uniform" in the sense of Remark 3.2.

## The two cases (Bhatt's proof, with the extra factor `ϖ_k`)

Write `L := max k J` and use the root relations `ϖ_L^{p^(L-m)} = ϖ_m`, `g_L^{p^(L-m)} = g_m`
(`rootSystem_pow_pow`, `chartUnit_pow_pow`), together with `ϖ_0^p = p·v` for a unit `v`
(`Q.unit`).  Since `x_J(n+c) = ϖ_J^c · x_J(n)` (`chartGen_level_succ` iterated), the element
equals `ϖ_k g_k ϖ_J^(cI) x_J(n)^I`, i.e. (in the ambient ring)

  `ϖ_k g_k · x_J(n+c)^I = ϖ_0^{1/p^k + (n+c)I/p^J} · g_0^{1/p^k - I/p^J}`.

* **Case A** (`p^J ≤ I·p^k`, i.e. `I/p^J ≥ 1/p^k`): the `ϖ`-exponent `1/p^k + cI/p^J` is at
  least `p·m` because `c ≥ p^(k+1) m`; so the element is `p^m` times an element of `D n`.
  Here `p^m·v^m·ϖ_L^e·g_L^{p^(L-k)} = ϖ_k ϖ_J^(cI) g_k` with `e` chosen so that
  `e + p·m·p^L = p^(L-k) + cI·p^(L-J)`; the inequality making `e` a genuine natural number
  is exactly `p·m·p^L ≤ p^(L-k) + c·I·p^(L-J)` (the `caseA_bound` estimate).
* **Case B** (`I·p^k < p^J`, i.e. `I/p^J < 1/p^k`, forcing `k ≤ J` and `I ≤ p^(J-k)` when
  `I ≥ 1`): the fractional power `g_0^{1/p^k - I/p^J} = g_J^{p^(J-k) - I}` is a genuine power
  of `g_J ∈ B`, so the element is *literally* the image of an element of `B`.

`I = 0` is degenerate (`x_J(n+c)^0 = 1`) and is handled separately.

The two analytic sub-lemmas are also available as standalone modules
(`Submission/Work/DSM4p/caseA_bound.lean`, `caseA_prod.lean`, `caseB_form.lean`); the proofs
below are self-contained.
-/

namespace Work.DSM4p

universe a
theorem chartMono_estimate {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (Q : DSMap.PerfectoidData p B) (gr : ℕ → B) (hgr : Work.DSM4p.IsRootSystem p gr)
    (m k c J I n : ℕ) (hc : p ^ (k + 1) * m ≤ c) :
    ∃ x : B, algebraMap B (Work.DSM4p.ChartAmbient gr) (Q.ϖ k * gr k) *
        (Work.DSM4p.chartGen hgr Q.ϖ (n + c) J) ^ I -
        algebraMap B (Work.DSM4p.ChartAmbient gr) x ∈
      (Ideal.span {(p : B)} ^ m) • (Work.DSM4p.chartLevel hgr Q.ϖ n).toSubmodule := by
  rcases Nat.eq_zero_or_pos I with hI0 | hIpos
  · subst hI0
    refine ⟨Q.ϖ k * gr k, ?_⟩
    simp
  · obtain ⟨v, hv⟩ := Q.unit
    by_cases hcase : p ^ J ≤ I * p ^ k
    · -- ## Case A : `e ≥ 1/p^k` (Bhatt's first case)
      set L : ℕ := max k J with hLdef
      have hkL : k ≤ L := by rw [hLdef]; exact le_max_left k J
      have hJL : J ≤ L := by rw [hLdef]; exact le_max_right k J
      set e : ℕ := p ^ (L - k) + c * I * p ^ (L - J) - p * m * p ^ L with hedef
      set w : B := Q.ϖ L ^ e * gr L ^ (p ^ (L - k)) with hwdef
      set U : ChartAmbient gr := ↑((chartUnit hgr J ^ I)⁻¹) with hUdef
      have hbound : p * m * p ^ L ≤ p ^ (L - k) + c * I * p ^ (L - J) := by
        have key : p * m * p ^ J ≤ c * I := by
          have h1 : p * m * p ^ J ≤ p * m * (I * p ^ k) := Nat.mul_le_mul_left (p * m) hcase
          have h2 : p * m * (I * p ^ k) = p ^ (k + 1) * m * I := by rw [pow_succ]; ring
          have h3 : p ^ (k + 1) * m * I ≤ c * I := Nat.mul_le_mul_right I hc
          exact le_trans h1 (le_trans (le_of_eq h2) h3)
        calc p * m * p ^ L
            = (p * m * p ^ J) * p ^ (L - J) := by
                rw [show p ^ L = p ^ (L - J) * p ^ J from by
                  rw [← pow_add, Nat.sub_add_cancel hJL]]
                ring
          _ ≤ (c * I) * p ^ (L - J) := Nat.mul_le_mul_right _ key
          _ = c * I * p ^ (L - J) := rfl
          _ ≤ p ^ (L - k) + c * I * p ^ (L - J) := Nat.le_add_left _ _
      have hwkey : (p : B) ^ m * (↑(v ^ m) * w) = Q.ϖ k * Q.ϖ J ^ (c * I) * gr k := by
        have hvo : (p : B) ^ m * ↑(v ^ m) = Q.ϖ 0 ^ (p * m) := by
          have h1 : ((p : B) * ↑v) ^ m = Q.ϖ 0 ^ (p * m) := by rw [← hv, pow_mul]
          have h2 : ((p : B) * ↑v) ^ m = (p : B) ^ m * ↑(v ^ m) := by
            rw [mul_pow, Units.val_pow_eq_pow_val]
          rw [← h2]; exact h1
        have h0L : Q.ϖ L ^ p ^ L = Q.ϖ 0 := IsRootSystem.pow_pow_zero Q.root L
        have hvarpi : Q.ϖ L ^ p ^ (L - k) = Q.ϖ k := rootSystem_pow_pow Q.root hkL
        have hgrk : gr L ^ p ^ (L - k) = gr k := rootSystem_pow_pow hgr hkL
        have hvarpiJ : Q.ϖ L ^ p ^ (L - J) = Q.ϖ J := rootSystem_pow_pow Q.root hJL
        have hexp : p ^ L * (p * m) + e = p ^ (L - k) + p ^ (L - J) * (c * I) := by
          have h2 : p * m * p ^ L + e = p ^ (L - k) + c * I * p ^ (L - J) := by
            rw [hedef]
            exact Nat.add_sub_of_le hbound
          have h3 : p ^ L * (p * m) = p * m * p ^ L := by ring
          have h4 : p ^ (L - J) * (c * I) = c * I * p ^ (L - J) := by ring
          rw [h3, h4]
          exact h2
        rw [hwdef]
        calc (p : B) ^ m * (↑(v ^ m) * (Q.ϖ L ^ e * gr L ^ p ^ (L - k)))
            = ((p : B) ^ m * ↑(v ^ m)) * (Q.ϖ L ^ e * gr L ^ p ^ (L - k)) := by ring
          _ = Q.ϖ 0 ^ (p * m) * (Q.ϖ L ^ e * gr L ^ p ^ (L - k)) := by rw [hvo]
          _ = (Q.ϖ L ^ p ^ L) ^ (p * m) * (Q.ϖ L ^ e * gr L ^ p ^ (L - k)) := by rw [← h0L]
          _ = Q.ϖ L ^ (p ^ L * (p * m) + e) * gr L ^ p ^ (L - k) := by
                rw [← pow_mul, ← mul_assoc, ← pow_add]
          _ = Q.ϖ L ^ (p ^ (L - k) + p ^ (L - J) * (c * I)) * gr L ^ p ^ (L - k) := by
                rw [hexp]
          _ = Q.ϖ L ^ p ^ (L - k) * (Q.ϖ L ^ p ^ (L - J)) ^ (c * I) * gr L ^ p ^ (L - k) := by
                rw [pow_add, pow_mul]
          _ = Q.ϖ k * Q.ϖ J ^ (c * I) * gr k := by rw [hvarpi, hvarpiJ, hgrk]
      have hpowid : Q.ϖ J ^ (c * I) * Q.ϖ J ^ (n * I) = Q.ϖ J ^ ((n + c) * I) := by
        rw [← pow_add, ← Nat.add_mul, Nat.add_comm c n]
      have hw2 : (p : B) ^ m * (↑(v ^ m) * w * Q.ϖ J ^ (n * I)) =
          Q.ϖ k * Q.ϖ J ^ ((n + c) * I) * gr k := by
        calc (p : B) ^ m * (↑(v ^ m) * w * Q.ϖ J ^ (n * I))
            = ((p : B) ^ m * (↑(v ^ m) * w)) * Q.ϖ J ^ (n * I) := by ring
          _ = (Q.ϖ k * Q.ϖ J ^ (c * I) * gr k) * Q.ϖ J ^ (n * I) := by rw [hwkey]
          _ = Q.ϖ k * (Q.ϖ J ^ (c * I) * Q.ϖ J ^ (n * I)) * gr k := by ring
          _ = Q.ϖ k * Q.ϖ J ^ ((n + c) * I) * gr k := by rw [hpowid]
      have hz : algebraMap B (ChartAmbient gr) (↑(v ^ m)) * algebraMap B (ChartAmbient gr) w *
            (chartGen hgr Q.ϖ n J) ^ I =
          algebraMap B (ChartAmbient gr) (↑(v ^ m) * w * Q.ϖ J ^ (n * I)) * U := by
        rw [chartGen_pow_eq hgr Q.ϖ n J I, hUdef]
        simp only [map_mul]
        ring
      have hEform : algebraMap B (ChartAmbient gr) (Q.ϖ k * gr k) *
            (chartGen hgr Q.ϖ (n + c) J) ^ I =
          algebraMap B (ChartAmbient gr) (Q.ϖ k * Q.ϖ J ^ ((n + c) * I) * gr k) * U := by
        rw [chartGen_pow_eq hgr Q.ϖ (n + c) J I, hUdef]
        simp only [map_mul]
        ring
      have hEq : algebraMap B (ChartAmbient gr) (Q.ϖ k * gr k) *
            (chartGen hgr Q.ϖ (n + c) J) ^ I =
          algebraMap B (ChartAmbient gr) ((p : B) ^ m) *
            (algebraMap B (ChartAmbient gr) (↑(v ^ m)) * algebraMap B (ChartAmbient gr) w *
              (chartGen hgr Q.ϖ n J) ^ I) := by
        rw [hEform, hz, ← hw2]
        simp only [map_mul]
        ring
      have hzmem : algebraMap B (ChartAmbient gr) (↑(v ^ m)) * algebraMap B (ChartAmbient gr) w *
            (chartGen hgr Q.ϖ n J) ^ I ∈ chartLevel hgr Q.ϖ n :=
        mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.algebraMap_mem _ _))
          (pow_mem (chartGen_mem hgr Q.ϖ n J) I)
      refine ⟨0, ?_⟩
      rw [map_zero, sub_zero, hEq]
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, ← Algebra.smul_def]
      exact Submodule.smul_mem_pointwise_smul _ ((p : B) ^ m) _ hzmem
    · -- ## Case B : `e < 1/p^k` (Bhatt's second case); the element is literally in `B`
      have hlt : I * p ^ k < p ^ J := lt_of_not_ge hcase
      have hI1 : 1 ≤ I := hIpos
      have hkJ : k ≤ J := by
        by_contra h
        have h1 : p ^ J < p ^ k := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (not_le.mp h)
        have h2 : p ^ k ≤ I * p ^ k := by
          calc p ^ k = 1 * p ^ k := (one_mul _).symm
            _ ≤ I * p ^ k := Nat.mul_le_mul_right _ hI1
        exact absurd hlt (not_lt.mpr (le_trans h1.le h2))
      have hIle : I ≤ p ^ (J - k) := by
        have h3 : p ^ J = p ^ (J - k) * p ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hkJ]
        rw [h3] at hlt
        exact le_of_lt (lt_of_mul_lt_mul_right hlt (Nat.zero_le _))
      have hunit : chartUnit hgr k * (chartUnit hgr J ^ I)⁻¹ =
          chartUnit hgr J ^ (p ^ (J - k) - I) := by
        rw [← mul_right_cancel_iff (a := chartUnit hgr J ^ I)]
        rw [mul_assoc, inv_mul_cancel, mul_one,
          mul_comm (chartUnit hgr J ^ (p ^ (J - k) - I)) (chartUnit hgr J ^ I),
          ← pow_add, Nat.add_sub_cancel' hIle]
        exact (chartUnit_pow_pow hgr hkJ).symm
      have hUel : (chartUnit hgr k : ChartAmbient gr) * ↑((chartUnit hgr J ^ I)⁻¹) =
          algebraMap B (ChartAmbient gr) (gr J ^ (p ^ (J - k) - I)) := by
        rw [← Units.val_mul, hunit, Units.val_pow_eq_pow_val, chartUnit_val, ← map_pow]
      have hB1 : algebraMap B (ChartAmbient gr) (Q.ϖ k * gr k) *
            (chartGen hgr Q.ϖ (n + c) J) ^ I =
          algebraMap B (ChartAmbient gr) (Q.ϖ k) *
            algebraMap B (ChartAmbient gr) (Q.ϖ J ^ ((n + c) * I)) *
            algebraMap B (ChartAmbient gr) (gr J ^ (p ^ (J - k) - I)) := by
        calc algebraMap B (ChartAmbient gr) (Q.ϖ k * gr k) *
              (chartGen hgr Q.ϖ (n + c) J) ^ I
            = algebraMap B (ChartAmbient gr) (Q.ϖ k) * algebraMap B (ChartAmbient gr) (gr k) *
                (algebraMap B (ChartAmbient gr) (Q.ϖ J ^ ((n + c) * I)) *
                  ↑((chartUnit hgr J ^ I)⁻¹)) := by
                rw [map_mul, chartGen_pow_eq hgr Q.ϖ (n + c) J I]
          _ = algebraMap B (ChartAmbient gr) (Q.ϖ k) *
                algebraMap B (ChartAmbient gr) (Q.ϖ J ^ ((n + c) * I)) *
                (algebraMap B (ChartAmbient gr) (gr k) * ↑((chartUnit hgr J ^ I)⁻¹)) := by
                ring
          _ = algebraMap B (ChartAmbient gr) (Q.ϖ k) *
                algebraMap B (ChartAmbient gr) (Q.ϖ J ^ ((n + c) * I)) *
                algebraMap B (ChartAmbient gr) (gr J ^ (p ^ (J - k) - I)) := by
                rw [← chartUnit_val hgr k, hUel]
      refine ⟨Q.ϖ k * Q.ϖ J ^ ((n + c) * I) * gr J ^ (p ^ (J - k) - I), ?_⟩
      rw [hB1, ← map_mul, ← map_mul, sub_self]
      exact Submodule.zero_mem _

end Work.DSM4p
