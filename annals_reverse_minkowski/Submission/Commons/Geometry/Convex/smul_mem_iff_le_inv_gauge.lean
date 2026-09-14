import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Gauge
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.GDelta.MetrizableSpace

namespace Commons.Geometry.Convex

open Set Filter
open scoped Pointwise Topology

/-- For a compact convex set `K` with `0` in its interior, and `t > 0`, membership in the
scaled set `t • K` is equivalent to the gauge bound `gauge K y ≤ t`. -/
theorem gauge_le_iff_of_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKc : IsCompact K) (hK : Convex ℝ K) (h0 : (0 : E) ∈ interior K)
    {y : E} {t : ℝ} (ht : 0 < t) :
    gauge K y ≤ t ↔ y ∈ t • K := by
  have hKnhds : K ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp h0
  have hcl : closure K = K := hKc.isClosed.closure_eq
  have h1 : gauge K y ≤ t ↔ gauge K (t⁻¹ • y) ≤ 1 := by
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr ht.le), smul_eq_mul, inv_mul_le_iff₀ ht, mul_one]
  rw [h1, gauge_le_one_iff_mem_closure hK hKnhds, hcl]
  exact (Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne' K y).symm

theorem smul_mem_iff_le_inv_gauge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKc : IsCompact K) (hK : Convex ℝ K) (h0 : (0 : E) ∈ interior K)
    {u : E} (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    r • u ∈ K ↔ r ≤ (gauge K u)⁻¹ := by
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact one_ne_zero hu.symm
  have hAK : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)
  have hbdd : Bornology.IsVonNBounded ℝ K := hKc.isVonNBounded ℝ
  have hgpos : 0 < gauge K u := (gauge_pos hAK hbdd).mpr hu_ne
  constructor
  · intro hmem
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · rw [← hr0]
      exact inv_nonneg.mpr hgpos.le
    · have hgauge : gauge K u ≤ r⁻¹ := by
        rw [gauge_le_iff_of_pos hKc hK h0 (inv_pos.mpr hrpos),
          Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hrpos.ne') K u]
        simpa using hmem
      exact (le_inv_comm₀ hgpos hrpos).mp hgauge
  · intro hle
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · rw [← hr0, zero_smul]
      exact interior_subset h0
    · have hgauge : gauge K u ≤ r⁻¹ := (le_inv_comm₀ hgpos hrpos).mpr hle
      have hmem : u ∈ r⁻¹ • K :=
        (gauge_le_iff_of_pos hKc hK h0 (inv_pos.mpr hrpos)).mp hgauge
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hrpos.ne') K u] at hmem
      simpa using hmem

end Commons.Geometry.Convex