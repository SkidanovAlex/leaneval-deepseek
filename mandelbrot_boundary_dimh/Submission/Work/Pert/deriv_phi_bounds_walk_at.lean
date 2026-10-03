import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk

/-!
# `Work.Pert.deriv_phi_bounds_walk_at`

The **`T₀`-version** of `Work.Pert.Ksub2.deriv_phi_bounds_walk`: there the radius `T₀` bounding the
compact set `K'` is *produced* (as `max 1 CK` from compactness), here it is *given* together with
the hypotheses `0 < T₀` and `∀ w ∈ K', ‖w‖ ≤ T₀`.

This matters for callers who already carry their own radius `T₀`: they cannot use the produced one
(the compactness bound `CK` of `K'` is not comparable with a given `T₀`, and the deep strip
`Dstrip M (T₀ + 1)` is monotone *increasing* in `T₀`, so a smaller produced radius gives a strictly
weaker statement).  The proof is therefore the one of `deriv_phi_bounds_walk` with the radius
construction removed: the argument uses the radius `T₀` only through `0 < T₀` and
`‖w‖ ≤ T₀` for `w ∈ K'`, both of which are hypotheses here.

The mathematical content is unchanged: uniform-in-`M` two-sided bounds for `‖deriv φ₀‖` along the
walk `u, u+1, …, u+n = w` with `u` in the deep strip `Dstrip M (T₀+1)`, `w ∈ K'`:

* **Clause 1 (upper)**: for `i ≤ n` the ball `ball (u+i) ρe` lies in `Dφ` and `‖deriv φ₀‖ ≤ Ce₀`
  there.  Deep points (`Re ≤ -Rd - ρe`) are handled by the asymptotic upper bound
  `deriv_phi_deep_upper`; shallow points are of the form `w - m` with `m ≤ m₀` bounded, so their
  `ρe`-balls sit inside the fixed compact `Z = ⋃_{m ≤ m₀} (cthickening ρe K' - m) ⊆ Dφ`, where
  `deriv φ₀` is bounded by compactness.
* **Clause 2 (lower)**: `cc₀ / M² ≤ ‖deriv φ₀ z‖` for `z ∈ Dφ` with `‖z - u‖ ≤ ρe`
  (`deriv_phi_strip_lower`).
-/

namespace Work.Pert

open MandelDim Complex Set Metric

noncomputable section

theorem deriv_phi_bounds_walk_at {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) {T₀ : ℝ} (hT₀ : 0 < T₀) (hT₀bd : ∀ w ∈ K', ‖w‖ ≤ T₀) : ∃ ρe : ℝ, 0 < ρe ∧ (∀ w ∈ K', Metric.ball w ρe ⊆ d.Dφ) ∧ ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ Ce₀ cc₀ : ℝ, 0 < Ce₀ ∧ 0 < cc₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ w ∈ K', ∀ u ∈ Work.Pert.Dstrip M (T₀ + 1), ∀ n : ℕ, u + (n : ℂ) = w → (∀ i : ℕ, i ≤ n → Metric.ball (u + (i : ℂ)) ρe ⊆ d.Dφ ∧ ∀ z : ℂ, z ∈ d.Dφ → ‖z - (u + (i : ℂ))‖ ≤ ρe → ‖deriv d.φ z‖ ≤ Ce₀) ∧ (∀ z : ℂ, z ∈ d.Dφ → ‖z - u‖ ≤ ρe → cc₀ / (M * M) ≤ ‖deriv d.φ z‖) := by
  -- ## the radius `ρe`, from compactness of `K'` inside the open `Dφ`
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := hK'c.exists_cthickening_subset_open d.Dφ_open hK'
  set ρe : ℝ := min ρ₀ (1 / 4) with hρedef
  have hρepos : 0 < ρe := lt_min hρ₀pos (by norm_num)
  have hρe_le₀ : ρe ≤ ρ₀ := min_le_left _ _
  have hρe_le : ρe ≤ 1 / 4 := min_le_right _ _
  have hSsub : Metric.cthickening ρe K' ⊆ d.Dφ :=
    subset_trans (cthickening_mono hρe_le₀ K') hρ₀sub
  have hballw : ∀ w ∈ K', Metric.ball w ρe ⊆ d.Dφ := by
    intro w hw z hz
    exact hSsub (Work.Pert.Ksub2.mem_cthickening_of_dist_le hw (le_of_lt (Metric.mem_ball.mp hz)))
  -- ## the two scale estimates
  obtain ⟨R, CA, hRpos, hCApos, hA⟩ := Work.Pert.Ksub2.deriv_phi_deep_upper d (T₀ + 1 + ρe)
  obtain ⟨M₁, cc, hM₁pos, hccpos, hB⟩ := Work.Pert.Ksub2.deriv_phi_strip_lower d (T₀ + 1)
  -- ## the deep/shallow threshold, the level bound and the fixed compact `Z`
  set Rd : ℝ := max R (d.ξ₀ + 1) with hRddef
  have hRleRd : R ≤ Rd := le_max_left _ _
  have hξleRd : d.ξ₀ + 1 ≤ Rd := le_max_right _ _
  have hRdpos : 0 < Rd := lt_of_lt_of_le hRpos hRleRd
  set m₀ : ℕ := ⌈T₀ + Rd + ρe⌉₊ + 1 with hm₀def
  set S : Set ℂ := Metric.cthickening ρe K' with hSdef
  set Z : Set ℂ := ⋃ m ∈ Finset.range (m₀ + 1), (fun z : ℂ => z - (m : ℂ)) '' S with hZdef
  have hScompact : IsCompact S := hK'c.cthickening (r := ρe)
  have hZcompact : IsCompact Z := by
    rw [hZdef]
    exact Finset.isCompact_biUnion _ (fun _ _ =>
      hScompact.image (continuous_id.sub continuous_const))
  have hZsub : Z ⊆ d.Dφ := by
    rw [hZdef]
    intro z hz
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hz
    obtain ⟨m, -, s, hsS, rfl⟩ := hz
    exact Work.Pert.Ksub2.Dphi_sub_nat d m (hSsub hsS)
  have hcontZ : ContinuousOn (fun z : ℂ => deriv d.φ z) Z :=
    (((d.φ_holo.contDiffOn d.Dφ_open).continuousOn_deriv_of_isOpen d.Dφ_open le_top)).mono hZsub
  obtain ⟨Csh, hCsh⟩ := hZcompact.exists_bound_of_continuousOn hcontZ
  refine ⟨ρe, hρepos, hballw, max M₁ 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), max 1 (max CA Csh), cc,
    lt_of_lt_of_le one_pos (le_max_left _ _), hccpos, ?_⟩
  intro M hM w hw u hu n hn
  have hM₁M : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hCAle : CA ≤ max 1 (max CA Csh) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCshle : Csh ≤ max 1 (max CA Csh) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  constructor
  · -- ## Clause 1: the walk points `u + i = w - (n - i)`
    intro i hi
    set m : ℕ := n - i with hmdef
    set p : ℂ := w - (m : ℂ) with hpdef
    have hp : u + (i : ℂ) = p := by
      rw [hpdef, hmdef, Nat.cast_sub hi, ← hn]; ring
    have himp : p.im = u.im := by rw [← hp]; simp
    rw [hp]
    have hre : ∀ z : ℂ, z.re = p.re + (z - p).re := fun z =>
      calc z.re = (p + (z - p)).re := by rw [add_sub_cancel]
           _ = p.re + (z - p).re := Complex.add_re p (z - p)
    have him : ∀ z : ℂ, z.im = p.im + (z - p).im := fun z =>
      calc z.im = (p + (z - p)).im := by rw [add_sub_cancel]
           _ = p.im + (z - p).im := Complex.add_im p (z - p)
    have hballnorm : ∀ z : ℂ, z ∈ Metric.ball p ρe → ‖z - p‖ ≤ ρe := by
      intro z hz
      have h := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at h
      exact le_of_lt h
    by_cases hdeep : p.re ≤ -Rd - ρe
    · -- deep: everything is inside the left half-plane, hence inside `QLeft ξ₀ ⊆ Dφ`
      have hzre_lt : ∀ z : ℂ, ‖z - p‖ ≤ ρe → z.re < -d.ξ₀ := by
        intro z hz
        have h1 : (z - p).re ≤ ‖z - p‖ := Complex.re_le_norm (z - p)
        rw [hre z]
        linarith
      constructor
      · intro z hz
        exact d.Q_sub (Work.Parab.halfplane_subset_QLeft d.ξ₀ (hzre_lt z (hballnorm z hz)))
      · intro z hzD hzd
        have hRz : R ≤ -z.re := by
          have h1 : (z - p).re ≤ ‖z - p‖ := Complex.re_le_norm (z - p)
          rw [hre z]
          linarith
        have hzim : |z.im| ≤ T₀ + 1 + ρe := by
          have h1 : |(z - p).im| ≤ ‖z - p‖ := Complex.abs_im_le_norm (z - p)
          have h3 : |u.im| ≤ T₀ + 1 := hu.2.2
          rw [him z, himp]
          calc |u.im + (z - p).im| ≤ |u.im| + |(z - p).im| := abs_add_le _ _
            _ ≤ (T₀ + 1) + ρe := add_le_add h3 (le_trans h1 hzd)
        exact le_trans (hA z hzD hRz hzim) hCAle
    · -- shallow: the walk point is `w - m` with `m ≤ m₀`, so the whole ball lies in `Z`
      push Not at hdeep
      have hmle : m ≤ m₀ := by
        have h2 : p.re = w.re - (m : ℝ) := by rw [hpdef]; simp
        have h3 : w.re ≤ T₀ := le_trans (Complex.re_le_norm w) (hT₀bd w hw)
        have h4 : (m : ℝ) < T₀ + Rd + ρe := by linarith
        have h5 : ((m₀ : ℕ) : ℝ) = ((⌈T₀ + Rd + ρe⌉₊ : ℕ) : ℝ) + 1 := by
          rw [hm₀def]; push_cast; ring
        have h6 : T₀ + Rd + ρe ≤ ((⌈T₀ + Rd + ρe⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        have h7 : (m : ℝ) < (m₀ : ℝ) := by rw [h5]; linarith
        exact le_of_lt (by exact_mod_cast h7)
      have hmZ : m ∈ Finset.range (m₀ + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hmle)
      have hpZ : ∀ z : ℂ, ‖z - p‖ ≤ ρe → z ∈ Z := by
        intro z hz
        rw [hZdef]
        refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hmZ, ?_⟩⟩
        refine ⟨z + (m : ℂ), ?_, ?_⟩
        · have hzz : z + (m : ℂ) = w + (z - p) := by rw [hpdef]; ring
          rw [hzz]
          refine Work.Pert.Ksub2.mem_cthickening_of_dist_le hw ?_
          rw [dist_eq_norm]
          simp only [add_sub_cancel_left]
          exact hz
        · ring
      have hballZ : Metric.ball p ρe ⊆ Z := fun z hz => hpZ z (hballnorm z hz)
      constructor
      · intro z hz; exact hZsub (hballZ hz)
      · intro z _ hzd
        exact le_trans (hCsh z (hpZ z hzd)) hCshle
  · -- ## Clause 2: the uniform lower bound at the deep strip
    intro z hzD hzd
    exact hB M hM₁M u hu z hzD (le_trans hzd hρe_le)

end

end Work.Pert
