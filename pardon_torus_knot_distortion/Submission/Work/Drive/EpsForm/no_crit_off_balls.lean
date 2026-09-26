import Mathlib

namespace Work.Drive.EpsForm

open scoped Topology

/-- **For small perturbations the critical points of `f + t·g` inside a fixed compact set stay near the critical points of `f`.** Let `f g : ℝ² → ℝ` be `C²`, `K` compact, `X` a finite set containing every critical point of `f` in `K`, and `r > 0`. Then for all small `t`, every critical point in `K` of `q ↦ f q + t * g q` lies within distance `r` of some element of `X`.

Route (compactness): `K \ ⋃_{x∈X} ball(x, r)` is compact and carries no critical point of `f`, so `‖fderiv ℝ f ·‖` has a positive lower bound there; on that compact set `fderiv ℝ (fun q => f q + t * g q) = fderiv ℝ f + t • fderiv ℝ g` converges uniformly to `fderiv ℝ f` as `t → 0` because `fderiv ℝ g` is bounded there, so for small `t` it does not vanish. Handle `K \ ⋃ ball = ∅` separately. -/
theorem no_crit_off_balls {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (X : Finset (ℝ × ℝ))
    (hX : ∀ p ∈ K, fderiv ℝ f p = 0 → p ∈ X) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ p ∈ K,
      fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) p = 0 → ∃ x ∈ X, ‖p - x‖ < r := by
  -- `U` is the union of the `r`-balls around the elements of `X`.
  set U : Set (ℝ × ℝ) := ⋃ x ∈ (X : Set (ℝ × ℝ)), Metric.ball x r with hU
  -- `A = K \ U` is the compact set of points of `K` far from every element of `X`.
  set A : Set (ℝ × ℝ) := K \ U with hA
  have hUopen : IsOpen U := by
    rw [hU]; exact isOpen_biUnion fun x _ => Metric.isOpen_ball
  have hAclosed : IsClosed A := by
    rw [hA]; exact hK.isClosed.sdiff hUopen
  have hAcomp : IsCompact A := hK.of_isClosed_subset hAclosed Set.sdiff_subset
  have hfderiv : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hgderiv : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hmem_ball : ∀ {p x : ℝ × ℝ}, p ∈ Metric.ball x r ↔ ‖p - x‖ < r := by
    intro p x; rw [Metric.mem_ball, dist_eq_norm]
  have hmemU : ∀ p : ℝ × ℝ, p ∈ U ↔ ∃ x ∈ X, ‖p - x‖ < r := by
    intro p
    rw [hU, Set.mem_iUnion₂]
    constructor
    · rintro ⟨x, hx, hpx⟩; exact ⟨x, hx, hmem_ball.mp hpx⟩
    · rintro ⟨x, hx, hpx⟩; exact ⟨x, hx, hmem_ball.mpr hpx⟩
  by_cases hAne : A.Nonempty
  · -- `A` is nonempty and carries no critical point of `f`.
    obtain ⟨c, hcA, hcmin⟩ := hAcomp.exists_isMinOn hAne (hfderiv.continuousOn.norm)
    have hcA' : c ∈ K ∧ c ∉ U := by simpa [hA] using hcA
    have hm_pos : 0 < ‖fderiv ℝ f c‖ := by
      rw [norm_pos_iff]
      intro hcrit
      exact hcA'.2 (by
        rw [hU]
        exact Set.mem_iUnion₂.mpr ⟨c, hX c hcA'.1 hcrit, Metric.mem_ball_self hr⟩)
    -- `M` bounds `‖fderiv ℝ g‖` on `A`.
    obtain ⟨M, hM⟩ := hAcomp.exists_bound_of_continuousOn hgderiv.continuousOn
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM c hcA)
    refine ⟨‖fderiv ℝ f c‖ / (2 * (M + 1)), ?_, ?_⟩
    · apply div_pos hm_pos; linarith
    · intro t ht p hpK hcrit
      by_contra hcon
      have hcon' : ∀ x ∈ X, r ≤ ‖p - x‖ := by
        intro x hx
        by_contra hlt
        exact hcon ⟨x, hx, not_le.mp hlt⟩
      have hpnotU : p ∉ U := fun hmem => by
        obtain ⟨x, hx, hpx⟩ := (hmemU p).mp hmem
        exact absurd hpx (not_lt.mpr (hcon' x hx))
      have hpA : p ∈ A := by rw [hA]; exact ⟨hpK, hpnotU⟩
      -- the derivative of the perturbation is `fderiv f + t • fderiv g`.
      have hderiv : fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) p
          = fderiv ℝ f p + t • fderiv ℝ g p := by
        have hf1 : DifferentiableAt ℝ f p := (hf.differentiable (by norm_num)).differentiableAt
        have hg1 : DifferentiableAt ℝ g p := (hg.differentiable (by norm_num)).differentiableAt
        have hfun : (fun q : ℝ × ℝ => f q + t * g q) = f + (fun q : ℝ × ℝ => t * g q) := rfl
        rw [hfun, fderiv_add hf1 (hg1.const_mul t), fderiv_const_mul hg1 t]
      have hδpos : 0 < ‖fderiv ℝ f c‖ / (2 * (M + 1)) := by
        apply div_pos hm_pos; linarith
      -- the perturbation term is smaller than the lower bound `‖fderiv ℝ f c‖`.
      have hδM : (‖fderiv ℝ f c‖ / (2 * (M + 1))) * M ≤ ‖fderiv ℝ f c‖ / 2 := by
        have h1 : (‖fderiv ℝ f c‖ / (2 * (M + 1))) * M
            ≤ (‖fderiv ℝ f c‖ / (2 * (M + 1))) * (M + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hδpos.le
        have h2 : (‖fderiv ℝ f c‖ / (2 * (M + 1))) * (M + 1) = ‖fderiv ℝ f c‖ / 2 := by
          rw [div_mul_eq_mul_div, mul_comm (‖fderiv ℝ f c‖) (M + 1), mul_comm 2 (M + 1)]
          exact mul_div_mul_left _ 2 (by linarith)
        linarith
      have hlt : |t| * M < ‖fderiv ℝ f c‖ := by
        have h1 : |t| * M ≤ (‖fderiv ℝ f c‖ / (2 * (M + 1))) * M :=
          mul_le_mul_of_nonneg_right (le_of_lt ht) hMnn
        have h2 : ‖fderiv ℝ f c‖ / 2 < ‖fderiv ℝ f c‖ := by linarith
        linarith
      -- hence the perturbed derivative does not vanish at `p ∈ A`.
      have hnorm : 0 < ‖fderiv ℝ (fun q : ℝ × ℝ => f q + t * g q) p‖ := by
        rw [hderiv]
        have hb : ‖t • fderiv ℝ g p‖ ≤ |t| * M := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hM p hpA) (abs_nonneg t)
        have htri : ‖fderiv ℝ f p‖ ≤ ‖fderiv ℝ f p + t • fderiv ℝ g p‖ + ‖t • fderiv ℝ g p‖ := by
          calc ‖fderiv ℝ f p‖
              = ‖(fderiv ℝ f p + t • fderiv ℝ g p) - t • fderiv ℝ g p‖ := by
                rw [add_sub_cancel_right]
            _ ≤ ‖fderiv ℝ f p + t • fderiv ℝ g p‖ + ‖t • fderiv ℝ g p‖ := norm_sub_le _ _
        have hmin : ‖fderiv ℝ f c‖ ≤ ‖fderiv ℝ f p‖ := hcmin hpA
        linarith
      exact (norm_pos_iff.mp hnorm) hcrit
  · -- the complement is empty: every point of `K` is already close to `X`.
    refine ⟨1, one_pos, ?_⟩
    intro t ht p hpK hcrit
    have hpU : p ∈ U := by
      by_contra hmem
      exact hAne ⟨p, by rw [hA]; exact ⟨hpK, hmem⟩⟩
    exact (hmemU p).mp hpU

end Work.Drive.EpsForm
