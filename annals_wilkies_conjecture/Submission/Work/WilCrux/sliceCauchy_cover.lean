import Mathlib
import Submission.Work.WilCrux.SliceCauchyDefs
import Submission.Work.WilCrux.fibreFderivFamFun
import Submission.Work.WilCrux.dDir_famFun_append
import Submission.Work.WilCrux.exists_osc_fderiv_single

namespace Work.WilCrux

/-- **The uniform-Cauchy sets cover `Q`.**  For `w ∈ Q` the slice `G w` is `C¹` on the ball of
radius `r0`, so the map `z ↦ fderiv ℝ (G w) z` is continuous at `0`; hence for every `ε > 0` the
oscillation of the `j`-th partial `z ↦ fderiv ℝ (G w) z (Pi.single j 1)` on a small punctured
ball is `< ε`, and `w` belongs to `sliceCauchySet G j k ε` for all large enough `k` (the radius
threshold `1/((k:ℝ)+1)` can be made as small as we like while keeping `η ≤ 1`).

Ingredients: `hsl` gives `ContDiffAt ℝ 1 (G w) 0` (since `0 ∈ Metric.ball 0 r0` and `r0 > 0`),
hence `ContinuousAt (fderiv ℝ (G w)) 0` by `ContDiffAt.continuousAt_fderiv`, so for `ε > 0` there
is `δ > 0` with `‖z‖ < δ → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε/2`; take
`η := min δ r0 1 > 0` and `k` with `1/((k:ℝ)+1) < η`.  For `z, z' ≠ 0` with `‖z‖ < η`,
`‖z'‖ < η` the triangle inequality gives the required bound `< ε`.  `hoff` (with `z ≠ 0` and
`‖z‖ < η ≤ r0`) gives the `c1Loc` memberships via `Work.WilCrux.mem_c1Loc_of_contDiffAt`, and
(otherwise irrelevant) `Pi.single (Fin.natAdd a j) 1 = Fin.append 0 (Pi.single j 1)` together
with `Work.WilCrux.fibreFderivFamFun` identifies the two `dDir`-values appearing in
`sliceCauchySet` with the slice partials `fderiv ℝ (G w) z (Pi.single j 1)` (using
`DifferentiableAt` from `hoff`, i.e. `ContDiffAt.differentiableAt`). -/
theorem sliceCauchy_cover {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (Q : Set (Fin a → ℝ)) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (j : Fin b) {ε : ℝ} (hε : 0 < ε) :
    Q ⊆ ⋃ k : ℕ, sliceCauchySet G j k ε := by
  intro w hw
  rw [Set.mem_iUnion]
  have hcd : ContDiffAt ℝ 1 (G w) 0 :=
    (hsl w hw).contDiffAt (Metric.ball_mem_nhds 0 hr0)
  obtain ⟨η₀, hη₀pos, hη₀⟩ := exists_osc_fderiv_single (G w) j hε hcd
  set η : ℝ := min (min η₀ r0) 1 with hηdef
  have hηpos : 0 < η := lt_min (lt_min hη₀pos hr0) one_pos
  have hηle1 : η ≤ 1 := min_le_right _ _
  have hηleη₀ : η ≤ η₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hηler0 : η ≤ r0 := le_trans (min_le_left _ _) (min_le_right _ _)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / ((k:ℝ) + 1) < η := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
    have hnpos : (0:ℝ) < (n:ℝ) :=
      lt_of_lt_of_le (one_div_pos.mpr hηpos) (le_of_lt hn)
    refine ⟨n, ?_⟩
    have h1 : 1 / ((n:ℝ) + 1) < 1 / (n:ℝ) :=
      one_div_lt_one_div_of_lt hnpos (by linarith)
    have h2 : 1 / (n:ℝ) < η := by
      have hn' : (1:ℝ) < (n:ℝ) * η := (div_lt_iff₀ hηpos).mp hn
      rw [div_lt_iff₀ hnpos]; linarith
    exact lt_trans h1 h2
  refine ⟨k, η, hk, hηle1, ?_⟩
  intro z z' hz hzlt hz' hz'lt
  have hzr0 : ‖z‖ < r0 := lt_of_lt_of_le hzlt hηler0
  have hz'r0 : ‖z'‖ < r0 := lt_of_lt_of_le hz'lt hηler0
  have hzcd : ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z) := hoff w hw z hz hzr0
  have hz'cd : ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z') := hoff w hw z' hz' hz'r0
  refine ⟨mem_c1Loc_of_contDiffAt hzcd, mem_c1Loc_of_contDiffAt hz'cd, ?_⟩
  rw [dDir_famFun_append G w z j (hzcd.differentiableAt (by norm_num)),
      dDir_famFun_append G w z' j (hz'cd.differentiableAt (by norm_num))]
  exact hη₀ z z' (lt_of_lt_of_le hzlt hηleη₀) (lt_of_lt_of_le hz'lt hηleη₀)

end Work.WilCrux
