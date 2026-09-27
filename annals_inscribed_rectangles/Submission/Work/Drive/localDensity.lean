import Mathlib
import Submission.Work.Drive.exists_meet3Data_of_good_family
import Submission.Work.Drive.chartSourceReality
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.contDiffAt_chartDiff3_family_fin

namespace Work.Drive

/-- **The local genericity conclusion holds on an open dense set of parameters, near any base
parameter.**

This is the *density* half of the localized (chart-per-piece) parametric Sard: under the hypotheses of
`Work.Drive.exists_meet3Data_of_good_family` for one chart `p` and one compact piece `K` — the chart
containment `hres` and the parameter surjectivity `hsurj` on the parameter ball of radius `δ` — every
parameter `t₀` of norm `< δ` has other parameters `t` arbitrarily close to it for which the *same local
conclusion* holds on `K`: all triple points in `K` are transversal, and every boundary triple point in
`K` lies on exactly one face coordinate, the others being strictly interior, with a crossing direction.

The proof is an application of `Work.Drive.exists_meet3Data_of_good_family` to the translated family
`t' ↦ G (t₀ + t')`: joint smoothness, the seam invariance and the two hypotheses above are inherited on
the smaller ball (the parameter surjectivity by the chain rule), and the conclusion's parameter is
shifted back by `t₀`. -/
theorem localDensity
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {m : ℕ} (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (hsmooth : ∀ (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G t k))
    (hseam : ∀ (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → G t k x = G t k (Work.Drive.seamInv x))
    (p : M) (K : Set (EuclideanSpace ℝ (Fin 9))) (δ : ℝ) (hK : IsCompact K) (hδ : 0 < δ)
    (hres : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < δ → y ∈ K →
      ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source)
    (hsurj : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < δ → y ∈ K →
      Work.Drive.TParity.chartDiff3 p (G t) y = 0 →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G t') y) t))
    {t₀ : EuclideanSpace ℝ (Fin m)} (ht₀ : ‖t₀‖ < δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : EuclideanSpace ℝ (Fin m), ‖t - t₀‖ < ε ∧
      (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Work.Drive.TParity.meet3 (G t) y →
        Work.Drive.TripleTransverse (Work.Drive.TParity.md3 (G t) 0 y)
          (Work.Drive.TParity.md3 (G t) 1 y) (Work.Drive.TParity.md3 (G t) 2 y)) ∧
      (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Work.Drive.TParity.meet3 (G t) y →
        y ∈ Submission.Drive.unitBoxBdry 8 →
        ∃ (k : Fin 3) (i : Fin 3),
          (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
          (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
            Work.Drive.TripleCommonDir (Work.Drive.TParity.md3 (G t) 0 y)
              (Work.Drive.TParity.md3 (G t) 1 y) (Work.Drive.TParity.md3 (G t) 2 y) v ∧
            (v k) i ≠ 0) := by
  classical
  -- The radius on which the shifted family `t' ↦ G (t₀ + t')` inherits the two hypotheses `hres`
  -- and `hsurj`: it must leave the parameter inside the ball of radius `δ` (whence `δ - ‖t₀‖`) and
  -- it must stay below the requested distance `ε`.
  set r : ℝ := min ((δ - ‖t₀‖) / 2) ε with hrdef
  have hδt : 0 < δ - ‖t₀‖ := by linarith
  have hrpos : 0 < r := by
    rw [hrdef]; exact lt_min (by linarith) hε
  have hrδ : r ≤ δ - ‖t₀‖ := by
    rw [hrdef]; exact (min_le_left _ _).trans (by linarith)
  have hrε : r ≤ ε := by
    rw [hrdef]; exact min_le_right _ _
  -- ## Joint smoothness of the translated family
  have hG' : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) =>
        G (t₀ + q.1) k q.2) := by
    intro k
    have hφ : ContMDiff
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => (t₀ + q.1, q.2)) := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    have h := (hG k).comp hφ
    simpa [Function.comp_def] using h
  -- ## The chart containment is inherited on the smaller ball
  have hcontain' : ∀ (t' : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t'‖ < r → y ∈ K → ∀ k : Fin 3,
      G (t₀ + t') k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source := by
    intro t' y ht' hy k
    refine hres (t₀ + t') y ?_ hy k
    have h1 : ‖t₀ + t'‖ ≤ ‖t₀‖ + ‖t'‖ := norm_add_le _ _
    linarith
  -- ## The parameter surjectivity is inherited (chain rule with the translation)
  have hsurj' : ∀ (t' : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t'‖ < r →
      y ∈ K → Work.Drive.TParity.chartDiff3 p (G (t₀ + t')) y = 0 →
      Function.Surjective (fderiv ℝ (fun t'' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G (t₀ + t'')) y) t') := by
    intro t' y ht' hy hzero
    have hnorm : ‖t₀ + t'‖ < δ := by
      have h1 : ‖t₀ + t'‖ ≤ ‖t₀‖ + ‖t'‖ := norm_add_le _ _
      linarith
    have hS := hsurj (t₀ + t') y hnorm hy hzero
    -- differentiability of the charted difference map in the parameter, at the base parameter
    have hFdiff : DifferentiableAt ℝ (fun s : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G s) y) (t₀ + t') := by
      have hjoint : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
            Work.Drive.TParity.chartDiff3 p (G q.1) q.2) (t₀ + t', y) :=
        contDiffAt_chartDiff3_family_fin m G hG p (t₀ + t') (y₀ := y)
          (fun k => hres (t₀ + t') y hnorm hy k)
      have hpair : DifferentiableAt ℝ
          (fun s : EuclideanSpace ℝ (Fin m) => (s, y)) (t₀ + t') := by fun_prop
      have hcomp := hjoint.differentiableAt (by simp) |>.comp (t₀ + t') hpair
      simpa [Function.comp_def] using hcomp
    have hτdiff : DifferentiableAt ℝ (fun t'' : EuclideanSpace ℝ (Fin m) =>
        t₀ + t'') t' := by fun_prop
    have hτderiv : fderiv ℝ (fun t'' : EuclideanSpace ℝ (Fin m) => t₀ + t'') t' =
        (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
      ((hasFDerivAt_id t').const_add t₀).fderiv
    change Function.Surjective (fderiv ℝ ((fun s : EuclideanSpace ℝ (Fin m) =>
      Work.Drive.TParity.chartDiff3 p (G s) y) ∘ (fun t'' : EuclideanSpace ℝ (Fin m) =>
        t₀ + t'')) t')
    have hderiv : fderiv ℝ ((fun s : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G s) y) ∘ (fun t'' : EuclideanSpace ℝ (Fin m) =>
          t₀ + t'')) t'
        = fderiv ℝ (fun s : EuclideanSpace ℝ (Fin m) =>
          Work.Drive.TParity.chartDiff3 p (G s) y) (t₀ + t') := by
      rw [fderiv_comp t' hFdiff hτdiff, hτderiv]
      exact ContinuousLinearMap.comp_id _
    rw [hderiv]
    exact hS
  -- ## Apply the parametric Sard genericity theorem to the translated family
  obtain ⟨t', ht', htrans, hface⟩ :=
    exists_meet3Data_of_good_family m (fun t' => G (t₀ + t')) hG' p K hK hrpos hcontain' hsurj'
  refine ⟨t₀ + t', ?_, htrans, hface⟩
  have hsub : t₀ + t' - t₀ = t' := by abel
  rw [hsub]
  exact lt_of_lt_of_le ht' hrε

end Work.Drive
