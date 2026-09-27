import Submission.Work.EQ.UnivCover.Defs

/-!
# Disc-like sets of a complex manifold

Chart balls of a `ChartedSpace ℂ X` are disc-like (`IsDiscLike`), and the disc-like sets form a
neighbourhood basis; moreover, if `X` is second countable there is a countable cover of `X` by
disc-like sets.
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology
open Work.EQ.UnivCover

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X]

/-- A convex combination of two points of a convex set, with nonnegative coefficients summing to
one, lies in the set. -/
theorem convex_combo_mem {E : Type*} [AddCommMonoid E] [Module ℝ E] {s : Set E} (hs : Convex ℝ s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ s :=
  (convex_iff_add_mem.mp hs) hx hy ha hb hab

/-- The homeomorphic image under an inverse chart of a Euclidean ball contained in the chart target
is disc-like. -/
theorem isDiscLike_symm_image_ball (c : OpenPartialHomeomorph X ℂ) (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.ball a ρ ⊆ c.target) : IsDiscLike (c.symm '' Metric.ball a ρ) := by
  have hballconv : Convex ℝ (Metric.ball a ρ) := convex_ball a ρ
  refine ⟨c.symm.isOpen_image_of_subset_source Metric.isOpen_ball hsub, ?_, ?_⟩
  · -- path connected: push the straight segment through the chart
    rintro x ⟨w₁, hw₁, rfl⟩ y ⟨w₂, hw₂, rfl⟩
    have hball : ∀ t, (Path.segment w₁ w₂) t ∈ Metric.ball a ρ := by
      intro t
      have hmem : (Path.segment w₁ w₂) t ∈ Set.range (Path.segment w₁ w₂) := ⟨t, rfl⟩
      rw [Path.range_segment] at hmem
      exact hballconv.segment_subset hw₁ hw₂ hmem
    refine ⟨⟨⟨fun t => c.symm ((Path.segment w₁ w₂) t),
        (c.continuousOn_symm.comp_continuous (Path.segment w₁ w₂).continuous
          fun t => hsub (hball t))⟩, ?_, ?_⟩,
      fun t => ⟨(Path.segment w₁ w₂) t, hball t, rfl⟩⟩
    · show c.symm ((Path.segment w₁ w₂) 0) = c.symm w₁
      rw [Path.source]
    · show c.symm ((Path.segment w₁ w₂) 1) = c.symm w₂
      rw [Path.target]
  · -- simply connected: straight-line homotopy inside the ball
    rintro y hy γ hγ
    obtain ⟨wy, hwy, rfl⟩ := hy
    have hγsrc : ∀ t, γ t ∈ c.source := by
      intro t
      obtain ⟨w, hw, hwv⟩ := hγ t
      rw [← hwv]
      exact c.map_target (hsub hw)
    set σ : unitInterval → ℂ := fun t => c (γ t) with hσ
    have hσball : ∀ t, σ t ∈ Metric.ball a ρ := by
      intro t
      obtain ⟨w, hw, hwv⟩ := hγ t
      have : c (γ t) = w := by rw [← hwv, c.right_inv (hsub hw)]
      simpa [hσ, this] using hw
    have hσcont : Continuous σ :=
      c.continuousOn.comp_continuous γ.continuous hγsrc
    have hσ0 : σ 0 = wy := by
      have : γ 0 = c.symm wy := γ.source
      simp only [hσ, this, c.right_inv (hsub hwy)]
    have hσ1 : σ 1 = wy := by
      have : γ 1 = c.symm wy := γ.target
      simp only [hσ, this, c.right_inv (hsub hwy)]
    refine ⟨⟨⟨fun p : unitInterval × unitInterval =>
        c.symm ((1 - (p.1 : ℝ)) • σ p.2 + (p.1 : ℝ) • wy), ?_⟩, ?_, ?_⟩, ?_⟩
    · -- continuity
      have hcont : Continuous fun p : unitInterval × unitInterval =>
          (1 - (p.1 : ℝ)) • σ p.2 + (p.1 : ℝ) • wy := by fun_prop
      have hmem : ∀ p : unitInterval × unitInterval,
          (1 - (p.1 : ℝ)) • σ p.2 + (p.1 : ℝ) • wy ∈ c.target := fun p =>
        hsub (convex_combo_mem hballconv (hσball p.2) hwy (by linarith [p.1.2.2])
          (by exact_mod_cast p.1.2.1) (by ring))
      exact c.continuousOn_symm.comp_continuous hcont hmem
    · -- at homotopy parameter `0`
      intro t
      show c.symm ((1 - ((0 : unitInterval) : ℝ)) • σ t + ((0 : unitInterval) : ℝ) • wy) = γ t
      rw [show ((0 : unitInterval) : ℝ) = 0 by simp, sub_zero, one_smul, zero_smul, add_zero,
        hσ]
      exact c.left_inv (hγsrc t)
    · -- at homotopy parameter `1`
      intro t
      show c.symm ((1 - ((1 : unitInterval) : ℝ)) • σ t + ((1 : unitInterval) : ℝ) • wy)
        = c.symm wy
      rw [show ((1 : unitInterval) : ℝ) = 1 by simp, sub_self, zero_smul, one_smul, zero_add]
    · -- the endpoints are fixed along the homotopy
      intro s t ht
      have ht' : t = 0 ∨ t = 1 := by simpa using ht
      have hcombo : ∀ w : ℂ, (1 - (s : ℝ)) • w + (s : ℝ) • w = w := by
        intro w
        rw [← add_smul, show (1 - (s : ℝ)) + (s : ℝ) = 1 by ring, one_smul]
      rcases ht' with rfl | rfl
      · show c.symm ((1 - (s : ℝ)) • σ 0 + (s : ℝ) • wy) = γ 0
        rw [hσ0, hcombo wy, γ.source]
      · show c.symm ((1 - (s : ℝ)) • σ 1 + (s : ℝ) • wy) = γ 1
        rw [hσ1, hcombo wy, γ.target]

/-- The disc-like sets form a neighbourhood basis of a complex manifold. -/
theorem hasDiscBasis_of_chartedSpace [ChartedSpace ℂ X] : HasDiscBasis X := by
  intro x U hU hx
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
  have hxtarget : c x ∈ c.target := c.map_source (mem_chart_source ℂ x)
  have himg_open : IsOpen (c '' (U ∩ c.source)) :=
    c.isOpen_image_of_subset_source (hU.inter c.open_source) Set.inter_subset_right
  have himg_mem : c x ∈ c '' (U ∩ c.source) := ⟨x, ⟨hx, mem_chart_source ℂ x⟩, rfl⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (chart_target_mem_nhds ℂ x) (himg_open.mem_nhds himg_mem))
  refine ⟨c.symm '' Metric.ball (c x) ρ, isDiscLike_symm_image_ball c (c x) hρ
    (fun w hw => (hball hw).1), ?_, ?_⟩
  · exact ⟨c x, Metric.mem_ball_self hρ, c.left_inv (mem_chart_source ℂ x)⟩
  · rintro y ⟨w, hw, rfl⟩
    obtain ⟨z, hz, hzw⟩ := (hball hw).2
    rw [← hzw, c.left_inv hz.2]
    exact hz.1

/-- In a second countable space where the disc-like sets form a neighbourhood basis there is a
countable cover by disc-like sets. -/
theorem exists_discCover [ChartedSpace ℂ X] [SecondCountableTopology X] (hB : HasDiscBasis X) :
    ∃ U : ℕ → Set X, DiscCover U := by
  classical
  choose V hV using fun x : X => hB x Set.univ isOpen_univ (Set.mem_univ x)
  have hVnhds : ∀ x : X, V x ∈ 𝓝 x := fun x => (hV x).1.isOpen.mem_nhds (hV x).2.1
  obtain ⟨s, hsc, hsU⟩ := TopologicalSpace.countable_cover_nhds hVnhds
  by_cases hne : s.Nonempty
  · haveI hne' : Nonempty (↥s) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    haveI hcnt : Countable (↥s) := hsc
    obtain ⟨f, hf⟩ := exists_surjective_nat (↥s)
    refine ⟨fun n => V (f n), fun n => (hV (f n)).1, ?_⟩
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ y ∈ s, V y := by rw [hsU]; exact Set.mem_univ x
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hys, hyx⟩ := hx
    obtain ⟨n, hn⟩ := hf ⟨y, hys⟩
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    rw [hn]
    exact hyx
  · -- `s = ∅` forces `X` to be empty, and then the constant family `∅` works
    have hs : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hempty : (Set.univ : Set X) = ∅ := by rw [← hsU, hs]; simp
    refine ⟨fun _ => (∅ : Set X), fun _ => ⟨isOpen_empty, ?_, ?_⟩, ?_⟩
    · intro x hx; exact absurd hx (Set.notMem_empty x)
    · intro x hx; exact absurd hx (Set.notMem_empty x)
    · simp [hempty]

end Work.EQ.UnivCover
