import Mathlib
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite
import Submission.Work.Whitney.PathTools.isPathConnected_compl_arc_union_finite

/-!
# Smooth immersed arcs and the smooth disjoint-arcs lemma

This file provides the *smooth* replacement of
`Work.Whitney.exists_disjoint_arcs_avoiding_finite` needed by the smooth (`C^∞`, immersive)
interfaces of `Work.Drive`:

* `Work.Drive.exists_smooth_immersed_arc`: in an open path-connected subset `W` of a smooth
  `n`-manifold (`n ≥ 2`), any two distinct points of `W` are joined by a smooth arc which is
  immersive on all of `ℝ` and injective on `[0,1]`, with image in `W`.  It is the germ arc
  `Work.Noncompact.CompressionTube.immersedArcWithGerm` with a trivially satisfied germ
  hypothesis (the germ of a chart line through a point of the open set `W`).

* `Work.Drive.exists_smooth_disjoint_arcs_avoiding_finite`: two smooth immersed arcs, injective on
  `[0,1]`, disjoint, avoiding a finite set except at their endpoints — the smooth version of the
  arc selection of the signed reduction.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Topology Set

/-- **A smooth immersed arc in an open path-connected set.**  In an open path-connected subset `W`
of a smooth `n`-manifold (`n ≥ 2`), two distinct points `x, y ∈ W` are joined by a curve
`γ : ℝ → M` which is `C^∞`, immersive on all of `ℝ`, injective on `[0,1]`, and maps `[0,1]` into
`W`. -/
theorem exists_smooth_immersed_arc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) (hWp : IsPathConnected W) {x y : M}
    (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) :
    ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ ∧
      (∀ t : ℝ, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t)) ∧
      γ 0 = x ∧ γ 1 = y ∧ Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ t ∈ W) := by
  classical
  have hn0 : 0 < n := by omega
  -- the chart at `x` and a non-zero direction
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x
  have hxc : x ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) x
  have hc : c ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓡 n) (n := (∞ : WithTop ℕ∞)) x
  have hcxt : c x ∈ c.target := c.map_source hxc
  let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn0⟩ : Fin n) (1 : ℝ)
  have hv : v ≠ 0 := by
    show (EuclideanSpace.single (⟨0, hn0⟩ : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) ≠ 0
    simp [EuclideanSpace.single, PiLp.single_eq_zero_iff]
  -- the germ of the chart line through `x` in the direction `v` stays in the open set `W`
  have hger : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e →
      c.symm (c x + t • v) ∈ W := by
    have hinner : Continuous (fun t : ℝ => c x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hcx0 : c x + (0 : ℝ) • v = c x := by rw [zero_smul, add_zero]
    have hsymm : ContinuousAt c.symm (c x + (0 : ℝ) • v) := by
      rw [hcx0]
      exact c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hcxt)
    have hcont : ContinuousAt (fun t : ℝ => c.symm (c x + t • v)) 0 :=
      ContinuousAt.comp' (f := fun t : ℝ => c x + t • v) (x := (0 : ℝ)) (g := c.symm)
        hsymm hinner.continuousAt
    have h0W : (fun t : ℝ => c.symm (c x + t • v)) 0 ∈ W := by
      show c.symm (c x + (0 : ℝ) • v) ∈ W
      rw [hcx0, c.left_inv hxc]
      exact hx
    have hmem : (fun t : ℝ => c.symm (c x + t • v)) ⁻¹' W ∈ 𝓝 (0 : ℝ) :=
      hcont (hW.mem_nhds h0W)
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨δ / 2, by linarith, ?_⟩
    intro t ht0 hte
    apply hδ
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]
    linarith
  obtain ⟨α, hα0, hα1, hαsm, hαimm, hαinj, hαW, -, -⟩ :=
    Work.Noncompact.CompressionTube.immersedArcWithGerm hn hW hWp.isConnected.isPreconnected
      hx hy hxy c hc hxc hv hger
  exact ⟨α, hαsm, hαimm, hα0, hα1, hαinj, hαW⟩

/-- **Two smooth immersed arcs, disjoint, avoiding a finite set but for their ends.**  This is
`Work.Whitney.exists_disjoint_arcs_avoiding_finite` with the two arcs `C^∞` on `ℝ` and immersive
on `[0,1]`. -/
theorem exists_smooth_disjoint_arcs_avoiding_finite {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [SecondCountableTopology M]
    (D : Set M) (hD : D.Finite)
    (p₁ p₂ q₁ q₂ : M) (h₁ : p₁ ≠ p₂) (h₂ : q₁ ≠ q₂) (h₃ : p₁ ≠ q₁) (h₄ : p₁ ≠ q₂)
    (h₅ : p₂ ≠ q₁) (h₆ : p₂ ≠ q₂) :
    ∃ γ₁ γ₂ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ₁ ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ₂ ∧
      (∀ t : ℝ, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ₁ t)) ∧
      (∀ t : ℝ, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ₂ t)) ∧
      γ₁ 0 = p₁ ∧ γ₁ 1 = q₁ ∧ γ₂ 0 = p₂ ∧ γ₂ 1 = q₂ ∧
      Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1) ∧ Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ D → t = 0 ∨ t = 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ D → t = 0 ∨ t = 1) ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) := by
  classical
  set F : Set M := D \ ({p₁, p₂, q₁, q₂} : Set M) with hFdef
  have hFfin : F.Finite := hD.sdiff
  have hpair : ({p₂, q₂} : Set M).Finite := (Set.finite_singleton q₂).insert p₂
  -- `γ₁` lives in the complement of `F` and of the two points `p₂`, `q₂`.
  set W₁ : Set M := (F ∪ {p₂, q₂})ᶜ with hW₁def
  have hW₁open : IsOpen W₁ := by
    rw [hW₁def]
    exact (hFfin.union hpair).isClosed.isOpen_compl
  have hW₁conn : IsPathConnected W₁ := by
    rw [hW₁def]
    exact Work.Whitney.PathTools.isPathConnected_compl_finite (n := n) (by omega)
      (F ∪ {p₂, q₂}) (hFfin.union hpair)
  have hmemW₁ : ∀ z : M, z ∈ W₁ ↔ z ∉ F ∧ z ≠ p₂ ∧ z ≠ q₂ := by
    intro z
    rw [hW₁def]
    constructor
    · intro h
      exact ⟨fun hc => h (Or.inl hc), fun hc => h (Or.inr (by simp [hc])),
        fun hc => h (Or.inr (by simp [hc]))⟩
    · rintro ⟨h1, h2, h3⟩ (h | h)
      · exact h1 h
      · rcases (by simpa using h : z = p₂ ∨ z = q₂) with h' | h'
        · exact h2 h'
        · exact h3 h'
  have hp₁W₁ : p₁ ∈ W₁ := by
    rw [hmemW₁]; exact ⟨by rw [hFdef]; simp, h₁, h₄⟩
  have hq₁W₁ : q₁ ∈ W₁ := by
    rw [hmemW₁]; exact ⟨by rw [hFdef]; simp, fun h => h₅ h.symm, h₂⟩
  obtain ⟨γ₁, hγ₁sm, hγ₁imm, hγ₁0, hγ₁1, hγ₁inj, hγ₁W⟩ :=
    exists_smooth_immersed_arc (n := n) (by omega) hW₁open hW₁conn hp₁W₁ hq₁W₁ h₃
  have hγ₁c : Continuous γ₁ := hγ₁sm.continuous
  have hγ₁not : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₁ t ∉ F ∧ γ₁ t ≠ p₂ ∧ γ₁ t ≠ q₂ :=
    fun t ht => (hmemW₁ (γ₁ t)).mp (hγ₁W t ht)
  -- `γ₂` lives in the complement of the image of `γ₁` and of `F`.
  set W₂ : Set M := (γ₁ '' Set.Icc (0 : ℝ) 1 ∪ F)ᶜ with hW₂def
  have hmemW₂ : ∀ z : M, z ∈ W₂ ↔ z ∉ γ₁ '' Set.Icc (0 : ℝ) 1 ∧ z ∉ F := by
    intro z
    rw [hW₂def]
    constructor
    · intro h
      exact ⟨fun hc => h (Or.inl hc), fun hc => h (Or.inr hc)⟩
    · rintro ⟨h1, h2⟩ (h | h)
      · exact h1 h
      · exact h2 h
  have hp₂W₂ : p₂ ∈ W₂ := by
    rw [hmemW₂]
    exact ⟨fun hc => (hγ₁not _ hc.choose_spec.1).2.1 hc.choose_spec.2, by rw [hFdef]; simp⟩
  have hq₂W₂ : q₂ ∈ W₂ := by
    rw [hmemW₂]
    exact ⟨fun hc => (hγ₁not _ hc.choose_spec.1).2.2 hc.choose_spec.2, by rw [hFdef]; simp⟩
  have hW₂conn : IsPathConnected W₂ := by
    rw [hW₂def]
    exact Work.Whitney.PathTools.isPathConnected_compl_arc_union_finite (n := n) hn
      hγ₁c hγ₁inj F hFfin
  have hW₂open : IsOpen W₂ := by
    rw [hW₂def]
    exact ((isCompact_Icc.image hγ₁c).isClosed.union hFfin.isClosed).isOpen_compl
  obtain ⟨γ₂, hγ₂sm, hγ₂imm, hγ₂0, hγ₂1, hγ₂inj, hγ₂W⟩ :=
    exists_smooth_immersed_arc (n := n) (by omega) hW₂open hW₂conn hp₂W₂ hq₂W₂ h₆
  have hγ₂not : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ∉ γ₁ '' Set.Icc (0 : ℝ) 1 ∧ γ₂ t ∉ F :=
    fun t ht => (hmemW₂ (γ₂ t)).mp (hγ₂W t ht)
  -- Membership in the four-point set, given membership in `D` but not in `F`.
  have hfour_of : ∀ z ∈ D, z ∉ F → z ∈ ({p₁, p₂, q₁, q₂} : Set M) := by
    intro z hzD hzF
    by_contra hcon
    exact hzF (by rw [hFdef]; exact ⟨hzD, hcon⟩)
  refine ⟨γ₁, γ₂, hγ₁sm, hγ₂sm, hγ₁imm, hγ₂imm, hγ₁0, hγ₁1, hγ₂0, hγ₂1,
    hγ₁inj, hγ₂inj, ?_, ?_, ?_⟩
  · intro t ht htD
    obtain ⟨hnotF, hnotp₂, hnotq₂⟩ := hγ₁not t ht
    have hmem := hfour_of (γ₁ t) htD hnotF
    simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl (hγ₁inj ht (by norm_num) (by rw [hγ₁0, h]))
    · exact absurd h hnotp₂
    · exact Or.inr (hγ₁inj ht (by norm_num) (by rw [hγ₁1, h]))
    · exact absurd h hnotq₂
  · intro t ht htD
    obtain ⟨hnotact, hnotF⟩ := hγ₂not t ht
    have hmem := hfour_of (γ₂ t) htD hnotF
    simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h
    · exact absurd (⟨0, by norm_num, by rw [hγ₁0]; exact h.symm⟩ :
        γ₂ t ∈ γ₁ '' Set.Icc (0 : ℝ) 1) hnotact
    · exact Or.inl (hγ₂inj ht (by norm_num) (by rw [hγ₂0, h]))
    · exact absurd (⟨1, by norm_num, by rw [hγ₁1]; exact h.symm⟩ :
        γ₂ t ∈ γ₁ '' Set.Icc (0 : ℝ) 1) hnotact
    · exact Or.inr (hγ₂inj ht (by norm_num) (by rw [hγ₂1, h]))
  · intro s hs t ht hst
    exact absurd (hst ▸ ⟨s, hs, rfl⟩ : γ₂ t ∈ γ₁ '' Set.Icc (0 : ℝ) 1) (hγ₂not t ht).1

end Work.Drive
