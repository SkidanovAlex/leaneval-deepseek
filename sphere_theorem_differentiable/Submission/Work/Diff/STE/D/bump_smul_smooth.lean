import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.STE.D

/-- **A smooth bump supported in an open set which smooths a product.**  For a compact set `K`
contained in an open set `U` of `ι → ℝ` (`ι` finite) and a function `g` which is `C^∞` *on* `U`
(so that its values off `U` may be junk), there is a `C^∞` function `φ`, equal to `1` on `K`, with
`tsupport φ ⊆ U`, and such that the product `x ↦ φ x • g x` is `C^∞` on all of `ι → ℝ`.

This is the standard "multiply a locally smooth function by a bump" device.  Suggested route:
`∃ f, tsupport f ⊆ s ∧ ... ∧ f x = 1` for `s ∈ 𝓝 x` is `exists_contDiff_tsupport_subset`
(`Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension`); covering the compact `K` by finitely
many closed balls `closedBall x r ⊆ U` and setting `φ := 1 - ∏ (1 - φ_i)` gives `φ = 1` on `K` and
`tsupport φ ⊆ U`.  Smoothness of `φ • g`: at `x ∈ U` both factors are `C^∞` at `x`
(`ContDiffOn.contDiffAt`), and at `x ∉ U` one has `x ∉ tsupport φ`, hence `φ =ᶠ[𝓝 x] 0`
(`notMem_tsupport_iff_eventuallyEq`) so the product is eventually `0`. -/
theorem bump_smul_smooth
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K U : Set (ι → ℝ)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (g : (ι → ℝ) → F) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) :
    ∃ φ : (ι → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ x ∈ K, φ x = 1) ∧ tsupport φ ⊆ U ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x • g x) := by
  classical
  -- For each point `x` we pick a radius `r x > 0` such that `closedBall x (r x) ⊆ U`
  -- (possible since `U` is a neighbourhood of every point of `K ⊆ U`); off `K` the choice
  -- is arbitrary but still positive.
  have hex : ∀ x : ι → ℝ, ∃ r : ℝ, 0 < r ∧ (x ∈ K → Metric.closedBall x r ⊆ U) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU hx))
      refine ⟨ε / 2, half_pos hε, fun _ y hy => hεU ?_⟩
      rw [Metric.mem_ball]
      have h1 := Metric.mem_closedBall.mp hy
      linarith
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  let r : (ι → ℝ) → ℝ := fun x => Classical.choose (hex x)
  have hr_pos : ∀ x, 0 < r x := fun x => (Classical.choose_spec (hex x)).1
  have hr_tsub : ∀ x ∈ K, Metric.closedBall x (r x) ⊆ U :=
    fun x hx => (Classical.choose_spec (hex x)).2 hx
  -- Cover the compact set `K` by the open balls `ball x (r x / 2)`, `x` ranging over a
  -- finite set `t ⊆ K`.
  have hnhds : ∀ x ∈ K, Metric.ball x (r x / 2) ∈ 𝓝 x :=
    fun x _ => Metric.ball_mem_nhds x (half_pos (hr_pos x))
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (r x / 2)) hnhds
  -- The individual bumps: equal to `1` on `closedBall x (r x / 2)`, supported in
  -- `closedBall x (r x) ⊆ U`.
  let φb : (x : ι → ℝ) → ContDiffBump x :=
    fun x => ⟨r x / 2, r x, half_pos (hr_pos x), by linarith [hr_pos x]⟩
  let φ : (ι → ℝ) → ℝ := fun y => 1 - ∏ x ∈ t, (1 - φb x y)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    show ContDiff ℝ (⊤ : ℕ∞) (fun y => 1 - ∏ x ∈ t, (1 - φb x y))
    refine ContDiff.sub contDiff_const ?_
    refine contDiff_prod (fun x _ => ?_)
    exact ContDiff.sub contDiff_const ((φb x).contDiff (n := ⊤))
  have hone : ∀ y ∈ K, φ y = 1 := by
    intro y hy
    obtain ⟨x, hxt, hyb⟩ : ∃ x ∈ t, y ∈ Metric.ball x (r x / 2) := by
      simpa only [Set.mem_iUnion, exists_prop] using hcov hy
    have h1 : φb x y = 1 :=
      (φb x).one_of_mem_closedBall (Metric.ball_subset_closedBall hyb)
    show 1 - ∏ x ∈ t, (1 - φb x y) = 1
    rw [Finset.prod_eq_zero hxt (by rw [h1]; ring)]
    ring
  -- The support of `φ` is contained in the union of the topological supports of the bumps:
  -- if none of the factors `1 - φb x` vanishes then the product equals `1`, so `φ = 0`.
  have hsupp : Function.support φ ⊆ ⋃ x ∈ t, tsupport (φb x) := by
    intro y hy
    by_contra hcon
    have hzero : ∀ x ∈ t, φb x y = 0 := by
      intro x hx
      refine image_eq_zero_of_notMem_tsupport ?_
      intro hmem
      exact hcon (by simp only [Set.mem_iUnion, exists_prop]; exact ⟨x, hx, hmem⟩)
    apply hy
    show 1 - ∏ x ∈ t, (1 - φb x y) = 0
    rw [Finset.prod_eq_one (fun x hx => by rw [hzero x hx]; ring)]
    ring
  have hcl : IsClosed (⋃ x ∈ t, tsupport (φb x)) :=
    Set.Finite.isClosed_biUnion t.finite_toSet (fun x _ => isClosed_tsupport _)
  have htsub1 : tsupport φ ⊆ ⋃ x ∈ t, tsupport (φb x) := by
    rw [tsupport]
    exact hcl.closure_subset_iff.mpr hsupp
  have htsub2 : (⋃ x ∈ t, tsupport (φb x)) ⊆ U := by
    intro y hy
    simp only [Set.mem_iUnion, exists_prop] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    have hyx' : y ∈ Metric.closedBall x (r x) := by
      rwa [(φb x).tsupport_eq] at hyx
    exact hr_tsub x (htK x hx) hyx'
  refine ⟨φ, hφ, hone, htsub1.trans htsub2, ?_⟩
  -- Smoothness of `φ • g`: on `U` both factors are smooth at the point, off `U` the product
  -- vanishes on a neighbourhood.
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact (hφ.contDiffAt).smul (hg.contDiffAt (hU.mem_nhds hy))
  · have hny : y ∉ tsupport φ := fun h => hy (htsub1.trans htsub2 h)
    have hev : φ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hny
    have hev2 : (fun z => φ z • g z) =ᶠ[𝓝 y] (fun _ => (0 : F)) :=
      hev.mono (fun z hz => by simp [hz])
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hev2

end Work.Diff.STE.D
