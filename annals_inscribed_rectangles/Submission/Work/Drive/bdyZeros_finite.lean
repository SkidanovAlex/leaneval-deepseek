import Mathlib
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.exists_local_normalForm
import Submission.Work.Drive.finite_of_isCompact_of_isolated

/-!
# Finiteness of the boundary zeros

For a smooth `F : ℝ^{m+1} → ℝ^m` whose zeros on the boundary of the unit box `[0,1]^(m+1)` are cut
out transversally on a single face (the hypothesis `hbdy` of `Submission.Drive.ParityProp`), the set
`bdyZeros F` of boundary zeros is finite.  The content is that each such zero is isolated in
`bdyZeros F`: near a zero `p` on the face `x i = c`, the implicit function theorem
(`exists_local_normalForm`) exhibits the zero set of `F` as a graph over the normal direction, and
the boundary of the box cuts that graph in the single point `p`.  Compactness
(`isCompact_bdyZeros`) then gives finiteness via `finite_of_isCompact_of_isolated`.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-- **Isolation of boundary zeros.**  Under the transversality hypothesis `hbdy`, every boundary
zero of `F` has an open neighbourhood meeting `bdyZeros F` only in itself. -/
theorem bdyZeros_isolated {m : ℕ} {F : Amb m → Tgt m}
    (hF : ContDiff ℝ Ctop F)
    (hbdy : ∀ x ∈ Submission.Drive.unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb m // v i = 0} => fderiv ℝ F x v.1))
    {p : Amb m} (hp : p ∈ bdyZeros F) :
    ∃ U : Set (Amb m), IsOpen U ∧ p ∈ U ∧ U ∩ bdyZeros F ⊆ {p} := by
  obtain ⟨hpbd, hFp⟩ := hp
  obtain ⟨i, hi01, hiint, hisurj⟩ := hbdy p hpbd hFp
  -- The local normal form of the zero set of `F` near `p`
  obtain ⟨δ, ρ, η, hδpos, hρpos, hηcd, _hηi, hηp, _hA, hB⟩ :=
    exists_local_normalForm hF hFp i hisurj
  -- The graph parametrising the zero set of `F` near `p`
  let g : ℝ → Amb m := fun u => u • EuclideanSpace.single i (1:ℝ) + η u
  have hgcont : Continuous g := by
    have h1 : Continuous (fun u : ℝ => u • (EuclideanSpace.single i (1:ℝ) : Amb m)) :=
      continuous_id.smul continuous_const
    exact h1.add hηcd.continuous
  have hgp : g (p i) = p := by
    show (p i) • EuclideanSpace.single i (1:ℝ) + η (p i) = p
    rw [hηp]; abel
  -- `g` is continuous at `p i`, so it stays within `ρ/2` of `p` there
  have hznu : ∀ᶠ u in 𝓝 (p i), g u ∈ Metric.ball (g (p i)) (ρ/2) :=
    hgcont.continuousAt.tendsto (Metric.ball_mem_nhds (g (p i)) (by linarith))
  obtain ⟨ν, hνpos, hν⟩ := Metric.mem_nhds_iff.mp hznu
  have hν' : ∀ u : ℝ, |u - p i| < ν → ‖g u - g (p i)‖ < ρ/2 := by
    intro u hu
    have hu' : u ∈ Metric.ball (p i) ν := by rw [Metric.mem_ball, Real.dist_eq]; exact hu
    have h2 : dist (g u) (g (p i)) < ρ/2 := Metric.mem_ball.mp (hν hu')
    rwa [dist_eq_norm] at h2
  -- on a neighbourhood of `p`, all coordinates other than `i` stay strictly inside `(0,1)`
  have hIoo : ∀ᶠ z in 𝓝 p, ∀ j : Fin (m+1), j ≠ i → z j ∈ Set.Ioo (0:ℝ) 1 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · have hmem : (fun z : Amb m => z j) ⁻¹' Set.Ioo (0:ℝ) 1 ∈ 𝓝 p :=
        (isOpen_Ioo.preimage (by fun_prop : Continuous (fun z : Amb m => z j))).mem_nhds
          (hiint j hji)
      exact Filter.Eventually.mono hmem (fun z hz _ => hz)
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.mem_nhds_iff.mp hIoo
  -- the isolating radius
  have hmin1 : 0 < min ν ε₂ := lt_min hνpos hε₂pos
  have hmin2 : 0 < min δ (min 1 (ρ/2)) := lt_min hδpos (lt_min one_pos (by linarith))
  set ε : ℝ := min (min ν ε₂) (min δ (min 1 (ρ/2))) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; have h := lt_min hmin1 hmin2; linarith
  have hεmin : ε < min (min ν ε₂) (min δ (min 1 (ρ/2))) := by rw [hεdef]; linarith
  have hεν : ε < ν := lt_of_lt_of_le hεmin (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεε₂ : ε < ε₂ := lt_of_lt_of_le hεmin (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεδ : ε < δ := lt_of_lt_of_le hεmin (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε1 : ε < 1 := lt_of_lt_of_le hεmin
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hερ : ε < ρ/2 := lt_of_lt_of_le hεmin
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, Metric.mem_ball_self hεpos, ?_⟩
  rintro z ⟨hzball, hzbdy⟩
  rw [Metric.mem_ball, dist_eq_norm] at hzball
  simp only [Set.mem_singleton_iff]
  have hcoord : |z i - p i| ≤ ‖z - p‖ := by
    have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin (m+1) => ℝ) (z - p) i
    simpa using h
  have hzi_δ : |z i - p i| < δ := lt_of_le_of_lt hcoord (lt_trans hzball hεδ)
  have hzν : |z i - p i| < ν := lt_of_le_of_lt hcoord (lt_trans hzball hεν)
  have hzv : ‖g (z i) - g (p i)‖ < ρ/2 := hν' (z i) hzν
  have hA2 : ‖p - g (z i)‖ = ‖g (z i) - g (p i)‖ := by
    rw [hgp]
    exact norm_sub_rev _ _
  -- `z` satisfies the smallness condition of the normal form
  have hzg : ‖z - g (z i)‖ < ρ := by
    have hsub : z - g (z i) = (z - p) + (p - g (z i)) := by abel
    calc ‖z - g (z i)‖ = ‖(z - p) + (p - g (z i))‖ := by rw [hsub]
      _ ≤ ‖z - p‖ + ‖p - g (z i)‖ := norm_add_le _ _
      _ = ‖z - p‖ + ‖g (z i) - g (p i)‖ := by rw [hA2]
      _ < ε + ρ/2 := by linarith
      _ < ρ := by linarith
  have hzg' : ‖z - z i • EuclideanSpace.single i (1:ℝ) - η (z i)‖ < ρ := by
    have heq : z - z i • EuclideanSpace.single i (1:ℝ) - η (z i) = z - g (z i) := by
      simp only [g]; abel
    rw [heq]; exact hzg
  -- hence `z` lies on the graph
  have hzeq : z = g (z i) := (hB z hzi_δ hzg').mp hzbdy.2
  obtain ⟨_hzbox, j, hj⟩ := hzbdy.1
  -- the face of `z` must be the face `i`
  have hzi01 : z i = 0 ∨ z i = 1 := by
    by_cases hji : j = i
    · subst hji; exact hj
    · exfalso
      have hzj : z j ∈ Set.Ioo (0:ℝ) 1 := by
        have h1 : z ∈ Metric.ball p ε₂ := by
          rw [Metric.mem_ball, dist_eq_norm]; linarith
        exact hε₂ h1 j hji
      rcases hj with h | h <;> rw [h] at hzj <;> norm_num at hzj
  have hzigap : |z i - p i| < 1 := lt_of_le_of_lt hcoord (lt_trans hzball hε1)
  have hzi_eq : z i = p i := by
    rcases hzi01 with h | h <;> rcases hi01 with h' | h' <;>
      (rw [h, h'] at hzigap ⊢ <;> norm_num at hzigap)
  rw [hzeq, hzi_eq, hgp]

theorem bdyZeros_finite {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (hF : ContDiff ℝ Work.Drive.Ctop F)
    (hbdy : ∀ x ∈ Submission.Drive.unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} => fderiv ℝ F x v.1)) :
    (Work.Drive.bdyZeros F).Finite := by
  refine finite_of_isCompact_of_isolated (isCompact_bdyZeros hF.continuous) ?_
  intro p hp
  exact bdyZeros_isolated hF hbdy hp

end

end Work.Drive
