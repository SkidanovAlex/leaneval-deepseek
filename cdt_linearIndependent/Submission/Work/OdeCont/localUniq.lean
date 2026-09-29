import Mathlib

namespace Work.OdeCont

lemma localUniq {k : ℕ} {A : ℂ → Fin k → Fin k → ℂ} {Z : ℂ → Fin k → ℂ} {w : ℂ} {R C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ z ∈ Metric.ball w R, ∀ v : Fin k → ℂ,
      ‖(fun i : Fin k => ∑ j, A z i j * v j)‖ ≤ C * ‖v‖)
    (hZ : ∀ z ∈ Metric.ball w R, HasDerivAt Z (fun i : Fin k => ∑ j, A z i j * Z z j) z)
    (hw : Z w = 0) : ∀ z ∈ Metric.ball w R, Z z = 0 := by
  intro z hz
  have hRpos : 0 < R := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hz)
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, w + t • (z - w) ∈ Metric.ball w R := by
    intro t ht
    have h1 : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
    have h2 : (0:ℝ) ≤ t := ht.1
    have h3 : (1 - t) + t = 1 := by ring
    have hwmem : w ∈ Metric.ball w R := by
      rw [Metric.mem_ball]; simpa using hRpos
    have hcombo := (convex_iff_add_mem.mp (convex_ball w R)) hwmem hz h1 h2 h3
    have heq : (1 - t) • w + t • z = w + t • (z - w) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rwa [heq] at hcombo
  have hZcont : ContinuousOn Z (Metric.ball w R) :=
    fun x hx => (hZ x hx).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun t : ℝ => Z (w + t • (z - w))) (Set.Icc (0:ℝ) 1) := by
    have hg : Continuous (fun t : ℝ => w + t • (z - w)) := by fun_prop
    exact ContinuousOn.comp hZcont hg.continuousOn (fun t ht => hseg t ht)
  have hderiv : ∀ t ∈ Set.Ico (0:ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => Z (w + t • (z - w)))
        ((z - w) • (fun i : Fin k =>
          ∑ j, A (w + t • (z - w)) i j * Z (w + t • (z - w)) j))
        (Set.Ici t) t := by
    intro t ht
    have hgt : HasDerivAt (fun s : ℝ => w + s • (z - w)) (z - w) t := by
      simpa using (((hasDerivAt_id t).smul_const (z - w)).const_add w)
    have hZt := hZ (w + t • (z - w)) (hseg t (Set.Ico_subset_Icc_self ht))
    exact (HasDerivAt.scomp t hZt hgt).hasDerivWithinAt
  have hbound' : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖(z - w) • (fun i : Fin k =>
          ∑ j, A (w + t • (z - w)) i j * Z (w + t • (z - w)) j)‖
        ≤ (‖z - w‖ * C) * ‖Z (w + t • (z - w))‖ := by
    intro t ht
    have hmem := hseg t (Set.Ico_subset_Icc_self ht)
    have hb := hbound (w + t • (z - w)) hmem (Z (w + t • (z - w)))
    rw [norm_smul]
    calc ‖z - w‖ * ‖(fun i : Fin k =>
            ∑ j, A (w + t • (z - w)) i j * Z (w + t • (z - w)) j)‖
        ≤ ‖z - w‖ * (C * ‖Z (w + t • (z - w))‖) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (‖z - w‖ * C) * ‖Z (w + t • (z - w))‖ := by ring
  have ha : (fun t : ℝ => Z (w + t • (z - w))) 0 = 0 := by
    simpa using hw
  have hfin : (fun t : ℝ => Z (w + t • (z - w))) 1 = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont hderiv ha hbound' 1 (by norm_num)
  simpa using hfin

end Work.OdeCont
