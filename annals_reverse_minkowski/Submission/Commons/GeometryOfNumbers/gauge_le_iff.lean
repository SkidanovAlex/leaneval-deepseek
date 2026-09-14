import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.GeometryOfNumbers

open Set Filter
open scoped Pointwise Topology

/-- Monotonicity of the scaled body `s • K` for a convex set `K` containing `0`:
if `0 ≤ s ≤ s'` and `y ∈ s • K`, then `y ∈ s' • K`. -/
theorem mem_smul_of_mem_smul_of_le {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ K) (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    {y : EuclideanSpace ℝ (Fin n)} {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s')
    (hy : y ∈ Set.image (fun x : EuclideanSpace ℝ (Fin n) => s • x) K) :
    y ∈ Set.image (fun x : EuclideanSpace ℝ (Fin n) => s' • x) K := by
  rcases eq_or_lt_of_le hs with rfl | hs_pos
  · rw [Set.mem_image] at hy
    obtain ⟨z, _hz, hzy⟩ := hy
    simp only [zero_smul] at hzy
    subst hzy
    rw [Set.mem_image]
    exact ⟨0, h0K, by simp⟩
  · have hs'_pos : 0 < s' := lt_of_lt_of_le hs_pos hss
    rw [Set.mem_image] at hy ⊢
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨(s / s') • z, ?_, ?_⟩
    · exact hC.smul_mem_of_zero_mem h0K hz
        ⟨div_nonneg hs hs'_pos.le, (div_le_one hs'_pos).mpr hss⟩
    · show s' • ((s / s') • z) = y
      rw [smul_smul, mul_div_cancel₀ s hs'_pos.ne', hzy]

/-- Closedness/limit step: if `K` is compact, contains `0`, `t ≥ 0` and `y ∈ r • K`
for every `r > t`, then `y ∈ t • K`. -/
theorem mem_smul_of_forall_lt {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : IsCompact K) (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    {y : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ r : ℝ, t < r → y ∈ Set.image (fun x : EuclideanSpace ℝ (Fin n) => r • x) K) :
    y ∈ Set.image (fun x : EuclideanSpace ℝ (Fin n) => t • x) K := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · -- The case `t = 0`: `K` is bounded, so `y` must vanish.
    subst ht0
    have hy0 : y = 0 := by
      obtain ⟨R, hR⟩ :=
        (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin n))).mp
          hKc.isBounded
      have hR0 : 0 ≤ R := by
        have hz := hR h0K
        rw [Metric.mem_closedBall] at hz
        simpa using hz
      have hbound : ∀ z ∈ K, ‖z‖ ≤ R := by
        intro z hz
        have hz' := hR hz
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz'
        exact hz'
      have key : ∀ ε : ℝ, 0 < ε → ‖y‖ ≤ ε := by
        intro ε hε
        have hR1 : 0 < R + 1 := by linarith
        set r : ℝ := ε / (R + 1) with hrdef
        have hrpos : 0 < r := div_pos hε hR1
        have hmem := h r hrpos
        rw [Set.mem_image] at hmem
        obtain ⟨z, hz, hzy⟩ := hmem
        have hnorm : ‖y‖ = r * ‖z‖ := by
          rw [← hzy, norm_smul, Real.norm_of_nonneg hrpos.le]
        have hrR : r * R ≤ ε := by
          rw [hrdef, div_mul_eq_mul_div, div_le_iff₀ hR1]
          nlinarith [le_of_lt hε]
        rw [hnorm]
        exact le_trans (mul_le_mul_of_nonneg_left (hbound z hz) hrpos.le) hrR
      exact norm_eq_zero.mp
        (le_antisymm (le_of_forall_pos_le_add (fun ε hε => by simpa using key ε hε))
          (norm_nonneg y))
    rw [hy0]
    rw [Set.mem_image]
    exact ⟨0, h0K, by simp⟩
  · -- The case `t > 0`: take the limit along `r k = t + 1/(k+1) ↓ t`.
    set r : ℕ → ℝ := fun k => t + ((k : ℝ) + 1)⁻¹ with hrdef
    have hr_gt : ∀ k : ℕ, t < r k := by
      intro k
      have hpos : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
      rw [hrdef]
      linarith
    have hx_ex : ∀ k : ℕ, ∃ z ∈ K, y = r k • z := fun k => by
      have hmem := h (r k) (hr_gt k)
      rw [Set.mem_image] at hmem
      obtain ⟨z, hz, hzy⟩ := hmem
      exact ⟨z, hz, hzy.symm⟩
    choose x hxK hxy using hx_ex
    have hx_eq : ∀ k : ℕ, x k = (r k)⁻¹ • y := by
      intro k
      have hrne : r k ≠ 0 := ne_of_gt (lt_of_le_of_lt ht (hr_gt k))
      rw [hxy k, inv_smul_smul₀ hrne]
    have hbase : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
      (tendsto_atTop_add_const_right _ (1 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
    have hrt : Filter.Tendsto r Filter.atTop (nhds t) := by
      have h' := hbase.const_add t
      simpa only [add_zero, hrdef] using h'
    have hrt_inv : Filter.Tendsto (fun k : ℕ => (r k)⁻¹) Filter.atTop (nhds t⁻¹) :=
      hrt.inv₀ (ne_of_gt htpos)
    have hlim : Filter.Tendsto (fun k : ℕ => (r k)⁻¹ • y) Filter.atTop (nhds (t⁻¹ • y)) :=
      hrt_inv.smul_const y
    have hmemK : ∀ k : ℕ, (r k)⁻¹ • y ∈ K := fun k => by rw [← hx_eq k]; exact hxK k
    have htinv : t⁻¹ • y ∈ K :=
      hKc.isClosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmemK)
    have hy : y = t • (t⁻¹ • y) := (smul_inv_smul₀ (ne_of_gt htpos) y).symm
    rw [hy, Set.mem_image]
    exact ⟨t⁻¹ • y, htinv, rfl⟩

theorem gauge_le_iff {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hC : Convex ℝ K) (hKc : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    sInf {s : ℝ | 0 ≤ s ∧ y ∈ Set.image (fun x : EuclideanSpace ℝ (Fin n) => s • x) K} ≤ t
      ↔ y ∈ Set.image (fun x : EuclideanSpace ℝ (Fin n) => t • x) K := by
  set A : Set ℝ := {s : ℝ | 0 ≤ s ∧ y ∈ Set.image (fun x : EuclideanSpace ℝ (Fin n) => s • x) K}
    with hAdef
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := interior_subset h0
  have hAbs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)
  have hne : A.Nonempty :=
    Set.Nonempty.mono (fun s hs => ⟨hs.1.le, hs.2⟩) (hAbs.gauge_set_nonempty (x := y))
  have hBdd : BddBelow A := ⟨0, fun s hs => hs.1⟩
  constructor
  · intro hle
    refine mem_smul_of_forall_lt hKc h0K ht fun r hr => ?_
    have hsr : sInf A < r := lt_of_le_of_lt hle hr
    obtain ⟨b, hb, hbr⟩ := (csInf_lt_iff hBdd hne).mp hsr
    exact mem_smul_of_mem_smul_of_le hC h0K hb.1 hbr.le hb.2
  · intro hmem
    exact csInf_le hBdd ⟨ht, hmem⟩

end Commons.GeometryOfNumbers