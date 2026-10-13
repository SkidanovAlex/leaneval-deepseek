import Mathlib
import Submission.Work.DSM4p.Chart

/-!
# The divisibility `g ∣ p ^ n` in the chart levels

Inside `B[1/g]` (`g = gr 0`) the `n`-th chart level is generated over `B` by
`x_k = ϖ_k^n / g_k`.  The key point is the perfectoid relation `ϖ_0 ^ p = p · v`
with `v` a unit of `B` (`DSMap.PerfectoidData.unit`): multiplying by `v^{-n}` turns
`p ^ n` into `ϖ_0 ^{pn} = ϖ_0 ^{n(p-1)} · ϖ_0 ^ n`, and `ϖ_0 ^ n = g · x_0`.  Hence

`p ^ n / g = v^{-n} · ϖ_0 ^{n(p-1)} · x_0`,

and the prefactor lies in the image of `B ⊆ chartLevel`.  This is the `dvd` clause of
`Work.DSM4p.RETTower` realised in the chart model.
-/

namespace Work.DSM4p

universe a

theorem chartLevel_dvd {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (Q : DSMap.PerfectoidData p B) (gr : ℕ → B) (hgr : Work.DSM4p.IsRootSystem p gr) (n : ℕ) :
    ∃ y ∈ Work.DSM4p.chartLevel hgr Q.ϖ n,
      algebraMap B (Work.DSM4p.ChartAmbient gr) (gr 0) * y =
        algebraMap B (Work.DSM4p.ChartAmbient gr) ((p : B) ^ n) := by
  obtain ⟨v, hv⟩ := Q.unit
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  -- `v⁻¹ · ϖ₀^p = p`
  have hkey : (↑(v⁻¹) : B) * (Q.ϖ 0) ^ p = (p : B) := by
    calc (↑(v⁻¹) : B) * (Q.ϖ 0) ^ p
        = (↑(v⁻¹) : B) * ((p : B) * (v : B)) := by rw [hv]
      _ = (p : B) * ((↑(v⁻¹) : B) * (v : B)) := by ring
      _ = (p : B) := by rw [Units.inv_mul, mul_one]
  have hpow : ((↑(v⁻¹) : B) * (Q.ϖ 0) ^ p) ^ n = (p : B) ^ n := by rw [hkey]
  have hexp : n * (p - 1) + n = p * n := by
    calc n * (p - 1) + n = n * (p - 1) + n * 1 := by rw [Nat.mul_one]
      _ = n * ((p - 1) + 1) := by rw [Nat.mul_add]
      _ = n * p := by rw [Nat.sub_add_cancel hp1]
      _ = p * n := by rw [Nat.mul_comm]
  have hc : (↑(v⁻¹) : B) ^ n * (Q.ϖ 0) ^ (n * (p - 1)) * (Q.ϖ 0) ^ n = (p : B) ^ n := by
    have h1 : (Q.ϖ 0) ^ (n * (p - 1)) * (Q.ϖ 0) ^ n = (Q.ϖ 0) ^ (p * n) := by
      rw [← pow_add, hexp]
    calc (↑(v⁻¹) : B) ^ n * (Q.ϖ 0) ^ (n * (p - 1)) * (Q.ϖ 0) ^ n
        = (↑(v⁻¹) : B) ^ n * ((Q.ϖ 0) ^ (n * (p - 1)) * (Q.ϖ 0) ^ n) := by ring
      _ = (↑(v⁻¹) : B) ^ n * (Q.ϖ 0) ^ (p * n) := by rw [h1]
      _ = ((↑(v⁻¹) : B) * (Q.ϖ 0) ^ p) ^ n := by rw [mul_pow, ← pow_mul]
      _ = (p : B) ^ n := hpow
  refine ⟨algebraMap B (ChartAmbient gr) ((↑(v⁻¹) : B) ^ n * (Q.ϖ 0) ^ (n * (p - 1))) *
      chartGen hgr Q.ϖ n 0, ?_, ?_⟩
  · exact mul_mem (Subalgebra.algebraMap_mem _ _) (chartGen_mem hgr Q.ϖ n 0)
  · calc algebraMap B (ChartAmbient gr) (gr 0) *
          (algebraMap B (ChartAmbient gr) ((↑(v⁻¹) : B) ^ n * (Q.ϖ 0) ^ (n * (p - 1))) *
            chartGen hgr Q.ϖ n 0)
        = algebraMap B (ChartAmbient gr) ((↑(v⁻¹) : B) ^ n * (Q.ϖ 0) ^ (n * (p - 1))) *
            (algebraMap B (ChartAmbient gr) (gr 0) * chartGen hgr Q.ϖ n 0) := by ring
      _ = algebraMap B (ChartAmbient gr) ((↑(v⁻¹) : B) ^ n * (Q.ϖ 0) ^ (n * (p - 1))) *
            algebraMap B (ChartAmbient gr) ((Q.ϖ 0) ^ n) := by rw [chartGen_mul_gr]
      _ = algebraMap B (ChartAmbient gr)
            ((↑(v⁻¹) : B) ^ n * (Q.ϖ 0) ^ (n * (p - 1)) * (Q.ϖ 0) ^ n) := by
            simp only [map_mul]
      _ = algebraMap B (ChartAmbient gr) ((p : B) ^ n) := by rw [hc]

end Work.DSM4p
