import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Core.Lev

open scoped NNReal ENNReal ContDiff
open Set

/-- The truncation `w ↦ max ‖w‖ Λ` of the modulus is `1`-Lipschitz on `ℂ`. -/
lemma lipschitzWith_max_normC (Λ : ℝ) : LipschitzWith 1 (fun w : ℂ => max ‖w‖ Λ) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm]
  calc |max ‖x‖ Λ - max ‖y‖ Λ| ≤ |‖x‖ - ‖y‖| := abs_max_sub_max_le_abs _ _ _
    _ ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
    _ = 1 * ‖x - y‖ := by ring

/-- **The truncated modulus of a `C¹` function is Lipschitz.**  If `u` is `C¹` on the polydisc of
multi-radius `ρ` and `ρ' j < ρ j` for every `j`, then `z ↦ max ‖u z‖ Λ` is Lipschitz on the smaller
polydisc of multi-radius `ρ'`.

Indeed, choose a radius `ρ''` strictly between `ρ'` and `ρ` (e.g. the midpoint), and let `s` be the
product of the closed discs of radii `ρ''_j`; `s` is compact, convex, contained in the polydisc of
radius `ρ`, and contains the polydisc of radius `ρ'`.  Since `u` is `C¹` on the (open) polydisc of
radius `ρ`, its Fréchet derivative is continuous there, hence bounded by some `M` on `s`; the mean
value theorem on the convex set `s` turns this into a Lipschitz bound for `u` on `s`, and composition
with the `1`-Lipschitz map `w ↦ max ‖w‖ Λ` gives the claim on the smaller polydisc. -/
theorem srcWLipschitz {n : ℕ} {ρ ρ' : Fin n → ℝ} (hρ'ρ : ∀ j, ρ' j < ρ j)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ)) (Λ : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (fun z => max ‖u z‖ Λ) (Work.CR.Flat.polydisc 0 ρ') := by
  classical
  -- a radius strictly between `ρ'` and `ρ`
  set ρ'' : Fin n → ℝ := fun j => (ρ' j + ρ j) / 2 with hρ''def
  have hlt1 : ∀ j, ρ' j < ρ'' j := fun j => by simp only [hρ''def]; linarith [hρ'ρ j]
  have hlt2 : ∀ j, ρ'' j < ρ j := fun j => by simp only [hρ''def]; linarith [hρ'ρ j]
  -- the compact convex set `s = ∏_j {‖z_j‖ ≤ ρ''_j}`
  set s : Set (Work.NN.Core.Cn n) :=
    Set.univ.pi (fun j => Metric.closedBall (0 : ℂ) (ρ'' j)) with hsdef
  have hs_compact : IsCompact s := isCompact_univ_pi fun j => isCompact_closedBall 0 (ρ'' j)
  have hs_sub_ρ : s ⊆ Work.CR.Flat.polydisc 0 ρ := by
    intro z hz
    rw [Set.mem_pi] at hz
    intro j
    have h1 : ‖z j‖ ≤ ρ'' j := by
      have := hz j (Set.mem_univ j)
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    simpa using lt_of_le_of_lt h1 (hlt2 j)
  have hs_sub_ρ' : Work.CR.Flat.polydisc 0 ρ' ⊆ s := by
    intro z hz
    rw [Set.mem_pi]
    intro j _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (lt_trans (by simpa using hz j) (hlt1 j))
  -- the derivative is continuous on the larger polydisc, hence bounded on `s`
  have hcont : ContinuousOn (fderiv ℝ u) s :=
    (hu.continuousOn_fderiv_of_isOpen (Work.CR.Flat.isOpen_polydisc 0 ρ) le_rfl).mono hs_sub_ρ
  obtain ⟨M, hM⟩ := hs_compact.exists_bound_of_continuousOn hcont
  set C : NNReal := ⟨max M 0, le_max_right _ _⟩ with hCdef
  have hbound : ∀ x ∈ s, ‖fderiv ℝ u x‖₊ ≤ C := by
    intro x hx
    exact_mod_cast le_trans (hM x hx) (le_max_left M 0)
  have hd : ∀ x ∈ s, DifferentiableAt ℝ u x := by
    intro x hx
    exact (hu.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds (hs_sub_ρ hx))).differentiableAt
      (by norm_num)
  have hconv : Convex ℝ s := by
    have h : s = ⋂ j, (LinearMap.proj j : Work.NN.Core.Cn n →ₗ[ℝ] ℂ) ⁻¹'
        Metric.closedBall (0 : ℂ) (ρ'' j) := by
      ext z
      simp only [hsdef, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_iInter, Set.mem_preimage,
        LinearMap.proj_apply]
    rw [h]
    exact convex_iInter fun j => (convex_closedBall (0 : ℂ) (ρ'' j)).linear_preimage _
  -- the mean value theorem on the convex set `s`
  have hLip : LipschitzOnWith C u s := hconv.lipschitzOnWith_of_nnnorm_fderiv_le hd hbound
  refine ⟨1 * C, ?_⟩
  have hcomp : LipschitzOnWith (1 * C) ((fun w : ℂ => max ‖w‖ Λ) ∘ u) s :=
    (lipschitzWith_max_normC Λ).comp_lipschitzOnWith hLip
  have hres := hcomp.mono hs_sub_ρ'
  rwa [Function.comp_def] at hres

end Work.NN.Core.Lev
