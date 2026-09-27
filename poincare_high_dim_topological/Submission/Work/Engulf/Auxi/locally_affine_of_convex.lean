import Mathlib
import Submission.Work.Engulf.Basic

/-!
# Glueing locally `ψ`-affine functions on a convex set

This file proves `Work.Engulf.Auxi.locally_affine_of_convex`, the glueing step for
`Work.Engulf.Aux.exists_subdiv_affine`.

The mathematical content: a function which, near every point of a convex set `C`, agrees with the
restriction of some affine map (composed with an injective-on-the-cube `ψ`), is the restriction of a
single affine map.  The proof goes through the one-dimensional fact that a function that is locally
affine on a closed interval is (globally) affine; the segment argument is supplied by convexity of
`C` and the injectivity of `ψ` on the cube.
-/

open Set Metric PL

namespace Work.Engulf.Auxi

/-- Two affine maps `ℝ →ᵃ[ℝ] W` that agree at `0` and `1` are equal. -/
theorem affineMap_eq_of_apply_eq_zero_one {W : Type*} [AddCommGroup W] [Module ℝ W]
    {f g : ℝ →ᵃ[ℝ] W} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  apply AffineMap.ext
  intro x
  have hfx : f.linear x = x • f.linear 1 := by
    have : (x : ℝ) • (1 : ℝ) = x := by simp
    conv_lhs => rw [← this, map_smul]
  have hgx : g.linear x = x • g.linear 1 := by
    have : (x : ℝ) • (1 : ℝ) = x := by simp
    conv_lhs => rw [← this, map_smul]
  have hf1 : f.linear 1 = f 1 - f 0 := by
    have h := congr_fun (AffineMap.decomp f) 1
    simp only [Pi.add_apply] at h
    rw [eq_sub_iff_add_eq]; exact h.symm
  have hg1 : g.linear 1 = g 1 - g 0 := by
    have h := congr_fun (AffineMap.decomp g) 1
    simp only [Pi.add_apply] at h
    rw [eq_sub_iff_add_eq]; exact h.symm
  conv_lhs => rw [AffineMap.decomp f]
  conv_rhs => rw [AffineMap.decomp g]
  simp only [Pi.add_apply]
  rw [hfx, hgx, hf1, hg1, h0, h1]

/-- Two affine maps `ℝ →ᵃ[ℝ] W` agreeing at two distinct points are equal. -/
theorem affineMap_eq_of_apply_eq_two_points {W : Type*} [AddCommGroup W] [Module ℝ W]
    {f g : ℝ →ᵃ[ℝ] W} {u v : ℝ} (huv : u ≠ v) (hu : f u = g u) (hv : f v = g v) : f = g := by
  have hcomp : f.comp (AffineMap.lineMap u v) = g.comp (AffineMap.lineMap u v) := by
    apply affineMap_eq_of_apply_eq_zero_one
    · simpa only [AffineMap.comp_apply, AffineMap.lineMap_apply_zero] using hu
    · simpa only [AffineMap.comp_apply, AffineMap.lineMap_apply_one] using hv
  apply AffineMap.ext
  intro x
  have hx : AffineMap.lineMap u v ((x - u) / (v - u)) = x := by
    rw [AffineMap.lineMap_apply_ring]
    field_simp
    ring
  calc f x = f (AffineMap.lineMap u v ((x - u) / (v - u))) := by rw [hx]
    _ = (f.comp (AffineMap.lineMap u v)) ((x - u) / (v - u)) := by rw [AffineMap.comp_apply]
    _ = (g.comp (AffineMap.lineMap u v)) ((x - u) / (v - u)) := by rw [hcomp]
    _ = g x := by rw [AffineMap.comp_apply, hx]

/-- A nondegenerate closed interval intersected with an open set that contains a point of it
contains a second point. -/
theorem exists_ne_mem_Icc_inter_isOpen {a b : ℝ} (hab : a < b) {O : Set ℝ} (hO : IsOpen O)
    {x : ℝ} (hx : x ∈ Icc a b ∩ O) : ∃ y ∈ Icc a b ∩ O, y ≠ x := by
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.mp hO x hx.2
  rcases lt_or_ge x b with hxb | hxb
  · obtain ⟨y, hxy, hyb⟩ := exists_between (lt_min hxb (by linarith : x < x + ρ))
    have hyb1 : y < b := lt_of_lt_of_le hyb (min_le_left _ _)
    have hyb2 : y < x + ρ := lt_of_lt_of_le hyb (min_le_right _ _)
    refine ⟨y, ⟨⟨le_trans hx.1.1 (le_of_lt hxy), le_of_lt hyb1⟩, hρO ?_⟩, ne_of_gt hxy⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨y, hya, hyx⟩ :=
      exists_between (max_lt (show a < x by linarith [hx.1.1]) (show x - ρ < x by linarith))
    have hya1 : a < y := lt_of_le_of_lt (le_max_left _ _) hya
    have hya2 : x - ρ < y := lt_of_le_of_lt (le_max_right _ _) hya
    refine ⟨y, ⟨⟨le_of_lt hya1, le_of_lt (lt_of_lt_of_le hyx hx.1.2)⟩, hρO ?_⟩, ne_of_lt hyx⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩

/-- A function on a closed interval which is locally affine (each point has a neighbourhood on
which it agrees with some affine map `ℝ →ᵃ[ℝ] W`) agrees with a single affine map on the whole
interval. -/
theorem exists_affineMap_of_locally_affine_Icc {W : Type*} [AddCommGroup W] [Module ℝ W]
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → W}
    (hloc : ∀ s ∈ Icc a b, ∃ ε > 0, ∃ B : ℝ →ᵃ[ℝ] W,
      ∀ u ∈ Icc a b, dist u s < ε → g u = B u) :
    ∃ B : ℝ →ᵃ[ℝ] W, ∀ u ∈ Icc a b, g u = B u := by
  rcases lt_or_eq_of_le hab with hablt | habeq
  · let ε : ↥(Icc a b) → ℝ := fun s => Classical.choose (hloc s.1 s.2)
    have hε : ∀ s : ↥(Icc a b), 0 < ε s := fun s => (Classical.choose_spec (hloc s.1 s.2)).1
    let F : ↥(Icc a b) → (ℝ →ᵃ[ℝ] W) :=
      fun s => Classical.choose ((Classical.choose_spec (hloc s.1 s.2)).2)
    have hF : ∀ (s : ↥(Icc a b)) (u : ℝ), u ∈ Icc a b → dist u s.1 < ε s → g u = F s u :=
      fun s => Classical.choose_spec ((Classical.choose_spec (hloc s.1 s.2)).2)
    have hlc : IsLocallyConstant F := by
      rw [IsLocallyConstant.iff_exists_open]
      intro s
      refine ⟨Subtype.val ⁻¹' ball s.1 (ε s), ?_, ?_, ?_⟩
      · exact isOpen_ball.preimage continuous_subtype_val
      · exact mem_preimage.mpr (mem_ball_self (hε s))
      · intro s' hs'
        have hs'mem : s'.1 ∈ ball s.1 (ε s) := mem_preimage.mp hs'
        have hd : dist s'.1 s.1 < ε s := mem_ball.mp hs'mem
        have hOopen : IsOpen (ball s.1 (ε s) ∩ ball s'.1 (ε s')) :=
          isOpen_ball.inter isOpen_ball
        obtain ⟨y, hy, hyne⟩ := exists_ne_mem_Icc_inter_isOpen hablt hOopen (x := s'.1)
          (show s'.1 ∈ Icc a b ∩ (ball s.1 (ε s) ∩ ball s'.1 (ε s')) from
            ⟨s'.2, hs'mem, mem_ball_self (hε s')⟩)
        have hyab : y ∈ Icc a b := hy.1
        have hys : y ∈ ball s.1 (ε s) := hy.2.1
        have hys' : y ∈ ball s'.1 (ε s') := hy.2.2
        apply affineMap_eq_of_apply_eq_two_points (u := s'.1) (v := y) (Ne.symm hyne)
        · exact (hF s' s'.1 s'.2 (mem_ball_self (hε s'))).symm.trans (hF s s'.1 s'.2 hd)
        · exact (hF s' y hyab (mem_ball.mp hys')).symm.trans (hF s y hyab (mem_ball.mp hys))
    have : PreconnectedSpace ↥(Icc a b) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    refine ⟨F ⟨a, left_mem_Icc.mpr hab⟩, fun u hu => ?_⟩
    have h1 : g u = F ⟨u, hu⟩ u := hF ⟨u, hu⟩ u hu (by rw [dist_self]; exact hε ⟨u, hu⟩)
    rw [h1]
    have h2 : F ⟨u, hu⟩ = F ⟨a, left_mem_Icc.mpr hab⟩ := by
      have := congr_fun (hlc.eq_const ⟨a, left_mem_Icc.mpr hab⟩) ⟨u, hu⟩
      simpa using this
    rw [h2]
  · obtain ⟨ε, hε, B, hB⟩ := hloc a (left_mem_Icc.mpr hab)
    refine ⟨B, fun u hu => ?_⟩
    have hua : u = a := by
      rw [← habeq, Icc_self, mem_singleton_iff] at hu
      exact hu
    rw [hua]
    exact hB a (left_mem_Icc.mpr hab) (by rw [dist_self]; exact hε)

/-- **`locally_affine_of_convex`**: a function that is locally `ψ`-affine with values in the open unit cube at every point of a nonempty convex set `C ⊆ ℝ^N`, where `ψ` is injective on the open unit cube, is globally `ψ`-affine on `C` (one affine map `A` with `A z ∈ openCube 1` and `f z = ψ (A z)` for all `z ∈ C`).  Glueing step for `Work.Engulf.Aux.exists_subdiv_affine`. -/
theorem locally_affine_of_convex {n N : ℕ} {M : Type*} [TopologicalSpace M]
    (ψ : PL.E n → M)
    (hinj : ∀ x ∈ PL.openCube (n := n) 1, ∀ y ∈ PL.openCube (n := n) 1, ψ x = ψ y → x = y)
    {C : Set (PL.E N)} (hC : Convex ℝ C) (hne : C.Nonempty) (f : PL.E N → M)
    (hloc : ∀ y ∈ C, ∃ δ > 0, ∃ A : PL.E N →ᵃ[ℝ] PL.E n,
      ∀ z ∈ C ∩ Metric.ball y δ, A z ∈ PL.openCube (n := n) 1 ∧ f z = ψ (A z)) :
    ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ C, A z ∈ PL.openCube (n := n) 1 ∧ f z = ψ (A z) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  -- Choose, for every point `y`, an affine map `A' y` and a radius `δ' y`, valid at `y` when
  -- `y ∈ C`.  The choice is deliberately independent of the proof of membership in `C`.
  have hex : ∀ y : PL.E N, ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∃ δ : ℝ,
      y ∈ C → (0 < δ ∧ ∀ z ∈ C ∩ ball y δ,
        A z ∈ PL.openCube (n := n) 1 ∧ f z = ψ (A z)) := by
    intro y
    by_cases hy : y ∈ C
    · obtain ⟨δ, hδ, A, hA⟩ := hloc y hy
      exact ⟨A, δ, fun _ => ⟨hδ, hA⟩⟩
    · exact ⟨0, 1, fun h => absurd h hy⟩
  choose A' δ' hA'δ' using hex
  have hδ' : ∀ y (hy : y ∈ C), 0 < δ' y := fun y hy => (hA'δ' y hy).1
  have hA' : ∀ y (hy : y ∈ C) z (hz : z ∈ C ∩ ball y (δ' y)),
      A' y z ∈ PL.openCube (n := n) 1 ∧ f z = ψ (A' y z) := fun y hy => (hA'δ' y hy).2
  -- Consistency of the local affine maps on overlaps of `C`.
  have hcons : ∀ (y : PL.E N) (hy : y ∈ C) (y' : PL.E N) (hy' : y' ∈ C) (z : PL.E N),
      z ∈ C → dist z y < δ' y → dist z y' < δ' y' → A' y z = A' y' z := by
    intro y hy y' hy' z hzC hzy hzy'
    have h1 := hA' y hy z ⟨hzC, hzy⟩
    have h2 := hA' y' hy' z ⟨hzC, hzy'⟩
    exact hinj (A' y z) h1.1 (A' y' z) h2.1 (by rw [← h1.2, h2.2])
  refine ⟨A' x₀, fun z hz => ?_⟩
  -- The segment from `x₀` to `z`.
  let p : ℝ → PL.E N := fun t => AffineMap.lineMap x₀ z t
  have hp_mem : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ C :=
    fun t ht => hC.segment_subset hx₀ hz (lineMap_mem_segment ℝ x₀ z ht)
  have hp_apply : ∀ t : ℝ, p t = t • (z - x₀) + x₀ := by
    intro t; simp only [p, AffineMap.lineMap_apply_module']
  have hp_dist : ∀ u s : ℝ, p u - p s = (u - s) • (z - x₀) := by
    intro u s
    rw [hp_apply u, hp_apply s, add_sub_add_right_eq_sub, ← sub_smul]
  let g : ℝ → PL.E n := fun t => A' (p t) (p t)
  -- `g` is locally affine on `[0,1]`.
  have hloc_g : ∀ s ∈ Icc (0 : ℝ) 1, ∃ ε > 0, ∃ B : ℝ →ᵃ[ℝ] PL.E n,
      ∀ u ∈ Icc (0 : ℝ) 1, dist u s < ε → g u = B u := by
    intro s hs
    have hMs : (0 : ℝ) < ‖z - x₀‖ + 1 := by positivity
    refine ⟨min 1 (δ' (p s) / (‖z - x₀‖ + 1)), ?_,
      (A' (p s)).comp (AffineMap.lineMap x₀ z), ?_⟩
    · exact lt_min one_pos (div_pos (hδ' (p s) (hp_mem s hs)) hMs)
    · intro u hu hdist
      have h1 : |u - s| < δ' (p s) / (‖z - x₀‖ + 1) := by
        rw [← Real.dist_eq]
        exact lt_of_lt_of_le hdist (min_le_right _ _)
      have hdist' : dist (p u) (p s) < δ' (p s) := by
        rw [dist_eq_norm, hp_dist u s, norm_smul, Real.norm_eq_abs]
        calc |u - s| * ‖z - x₀‖ ≤ |u - s| * (‖z - x₀‖ + 1) :=
              mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (z - x₀)]) (abs_nonneg _)
          _ < (δ' (p s) / (‖z - x₀‖ + 1)) * (‖z - x₀‖ + 1) :=
              mul_lt_mul_of_pos_right h1 hMs
          _ = δ' (p s) := div_mul_cancel₀ _ (ne_of_gt hMs)
      have hcg : g u = A' (p s) (p u) :=
        hcons (p u) (hp_mem u hu) (p s) (hp_mem s hs) (p u) (hp_mem u hu)
          (by rw [dist_self]; exact hδ' (p u) (hp_mem u hu)) hdist'
      rw [hcg, AffineMap.comp_apply]
  obtain ⟨B, hB⟩ := exists_affineMap_of_locally_affine_Icc (a := 0) (b := 1) zero_le_one
    (g := g) hloc_g
  -- `B` is the affine map `A' x₀` along the segment.
  have hC₀ : B = (A' x₀).comp (AffineMap.lineMap x₀ z) := by
    set t₀ : ℝ := min (δ' x₀ / (‖z - x₀‖ + 1)) 1 / 2 with ht₀
    have ht₀_pos : 0 < t₀ := by
      rw [ht₀]; exact half_pos (lt_min (div_pos (hδ' x₀ hx₀) (by positivity)) one_pos)
    have ht₀_mem : t₀ ∈ Icc (0 : ℝ) 1 := by
      rw [ht₀]
      refine ⟨le_of_lt ht₀_pos, ?_⟩
      have : min (δ' x₀ / (‖z - x₀‖ + 1)) 1 ≤ 1 := min_le_right _ _
      linarith
    have ht₀_lt : t₀ < δ' x₀ / (‖z - x₀‖ + 1) := by
      rw [ht₀]
      have hle : min (δ' x₀ / (‖z - x₀‖ + 1)) 1 ≤ δ' x₀ / (‖z - x₀‖ + 1) := min_le_left _ _
      have hpos : 0 < min (δ' x₀ / (‖z - x₀‖ + 1)) 1 :=
        lt_min (div_pos (hδ' x₀ hx₀) (by positivity)) one_pos
      linarith
    apply affineMap_eq_of_apply_eq_two_points (u := 0) (v := t₀) (ne_of_lt ht₀_pos)
    · rw [← hB 0 (left_mem_Icc.mpr zero_le_one)]
      simp only [g, p, AffineMap.lineMap_apply_zero, AffineMap.comp_apply]
    · rw [← hB t₀ ht₀_mem]
      have hpt : p t₀ - x₀ = t₀ • (z - x₀) := by rw [hp_apply t₀]; abel
      have hdt : dist (p t₀) x₀ < δ' x₀ := by
        rw [dist_eq_norm, hpt, norm_smul, Real.norm_eq_abs]
        have hMs : (0 : ℝ) < ‖z - x₀‖ + 1 := by positivity
        have hna : (0 : ℝ) ≤ ‖z - x₀‖ := norm_nonneg _
        calc |t₀| * ‖z - x₀‖ ≤ |t₀| * (‖z - x₀‖ + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ = t₀ * (‖z - x₀‖ + 1) := by rw [abs_of_pos ht₀_pos]
          _ < (δ' x₀ / (‖z - x₀‖ + 1)) * (‖z - x₀‖ + 1) :=
              mul_lt_mul_of_pos_right ht₀_lt hMs
          _ = δ' x₀ := div_mul_cancel₀ _ (ne_of_gt hMs)
      have hcons₀ : A' (p t₀) (p t₀) = A' x₀ (p t₀) :=
        hcons (p t₀) (hp_mem t₀ ht₀_mem) x₀ hx₀ (p t₀) (hp_mem t₀ ht₀_mem)
          (by rw [dist_self]; exact hδ' (p t₀) (hp_mem t₀ ht₀_mem)) hdt
      simp only [g]
      rw [hcons₀, AffineMap.comp_apply]
  -- Hence the value at `z` from the base map is the value from the local map at `z`.
  have key : A' x₀ z = A' z z := by
    have h1 : (A' x₀).comp (AffineMap.lineMap x₀ z) 1 = A' x₀ z := by
      rw [AffineMap.comp_apply, AffineMap.lineMap_apply_one]
    rw [← h1, ← hC₀, ← hB 1 (right_mem_Icc.mpr zero_le_one)]
    simp only [g, p, AffineMap.lineMap_apply_one]
  constructor
  · rw [key]; exact (hA' z hz z ⟨hz, mem_ball_self (hδ' z hz)⟩).1
  · rw [key]; exact (hA' z hz z ⟨hz, mem_ball_self (hδ' z hz)⟩).2

end Work.Engulf.Auxi
