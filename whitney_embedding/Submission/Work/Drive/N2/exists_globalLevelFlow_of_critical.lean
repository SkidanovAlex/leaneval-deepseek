import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE
import Submission.Work.Drive.N2.exists_disjoint_chart_neighborhoods
import Submission.Work.Drive.N2.windowDatumExists
import Submission.Work.Drive.N2.exists_modelChart_data

open scoped Manifold ContDiff Topology
open Set

namespace Work.Drive.N2

open scoped Manifold ContDiff in
/-- **A small shrunk Morse chart with a value-confined compact exceptional set.**

Given a Morse chart `φ` of `f` at `x₀` (centred, quadratic on its source) and a neighbourhood `T`
of `x₀`, and `ε > 0`, there are a chart `χ` with source inside `T`, a radius `r > 0` and the
compact image `C = χ.symm '' closedBall 0 r` of the closed `r`-ball such that `C` is a closed
neighbourhood of `x₀` carrying only values within `ε` of `f x₀`, and the model ball
`{y ∈ χ.source | ‖χ y‖ < r}` is contained in `C`.  (The last two rows are what a "bad set" of a
level flow needs: `C` is where the flow may fail to move `f` at unit speed.) -/
theorem exists_small_chart_data {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    (f : M → ℝ) (x₀ : M) (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ : ℝ) (hx₀ : x₀ ∈ φ.source) (hcen : φ x₀ = 0)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    (hφ' : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ.symm z) φ.target)
    (hquad : ∀ y ∈ φ.source, f y = f x₀ + s₁ * (φ y 0) ^ 2 + s₂ * (φ y 1) ^ 2)
    {T : Set M} (hT : T ∈ 𝓝 x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ (χ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) (C : Set M),
      0 < r ∧ x₀ ∈ χ.source ∧ χ x₀ = 0 ∧ χ.source ⊆ T ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => χ y) χ.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => χ.symm z) χ.target ∧
      (∀ y ∈ χ.source, f y = f x₀ + s₁ * (χ y 0) ^ 2 + s₂ * (χ y 1) ^ 2) ∧
      IsCompact C ∧ C = χ.symm '' Metric.closedBall 0 r ∧
      Metric.closedBall 0 r ⊆ χ.target ∧ modelBall χ r ⊆ C ∧
      (∀ y ∈ C, |f y - f x₀| < ε) := by
  classical
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hT
  obtain ⟨ρ₁, hρ₁pos, hρ₁tgt, hρ₁sub⟩ :=
    exists_ball_preimage_subset φ hx₀ ((hUopen.inter φ.open_source).mem_nhds ⟨hxU, hx₀⟩)
  have hρ₁tgt' : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ₁ ⊆ φ.target := by
    simpa only [hcen] using hρ₁tgt
  have hρ₁sub' : φ.symm '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ₁ ⊆ U ∩ φ.source := by
    simpa only [hcen] using hρ₁sub
  set ρ : ℝ := min ρ₁ (min (ε / 2) 1) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₁pos (lt_min (half_pos hε) one_pos)
  have hρle₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hρleε : ρ ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρle1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < ε := by
    have h : ρ ^ 2 ≤ ρ := by nlinarith [hρpos, hρle1]
    linarith
  set r : ℝ := ρ / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrsq : r ^ 2 < ε := by rw [hrdef]; nlinarith [hρsq, hρpos]
  set W : Set M := φ.source ∩ φ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ρ with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
  have hx₀W : x₀ ∈ W := by
    rw [hWdef]
    refine ⟨hx₀, ?_⟩
    show φ x₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ρ
    rw [hcen]
    exact Metric.mem_ball_self hρpos
  have hsrcχ : (φ.restr W).source = W := by
    rw [OpenPartialHomeomorph.restr_source' φ W hWopen]
    exact inter_eq_right.mpr (by rw [hWdef]; exact inter_subset_left)
  have hsubχ : (φ.restr W).source ⊆ φ.source := by
    rw [hsrcχ, hWdef]; exact inter_subset_left
  have hballtgt : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r ⊆ (φ.restr W).target := by
    intro z hz
    have hzr : ‖z‖ ≤ r := by
      have h := Metric.mem_closedBall.mp hz
      simpa [dist_eq_norm] using h
    have hzρ : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ρ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      linarith
    have hzρ₁ : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ₁ := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      linarith
    have hztgt : z ∈ φ.target := hρ₁tgt' hzρ₁
    have hmemW : φ.symm z ∈ W := by
      rw [hWdef]
      refine ⟨φ.map_target hztgt, ?_⟩
      show φ (φ.symm z) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ρ
      rw [φ.right_inv hztgt]
      exact hzρ
    rw [OpenPartialHomeomorph.restr_target, hWopen.interior_eq]
    exact ⟨hztgt, hmemW⟩
  refine ⟨φ.restr W, r, (φ.restr W).symm '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r,
    hrpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, hballtgt, ?_, ?_⟩
  · rw [hsrcχ]; exact hx₀W
  · show φ x₀ = 0
    exact hcen
  · intro y hy
    rw [hsrcχ] at hy
    have hyφ : y ∈ φ.source := hy.1
    have hyb : φ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ρ := hy.2
    have hlt : ‖φ y‖ < ρ := by
      have h := Metric.mem_ball.mp hyb
      rwa [dist_eq_norm, sub_zero] at h
    have hmem : y ∈ φ.symm '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ₁ :=
      ⟨φ y, Metric.mem_closedBall.mpr (by
          rw [dist_eq_norm, sub_zero]
          exact le_trans (le_of_lt hlt) hρle₁),
        φ.left_inv hyφ⟩
    exact hUsub (hρ₁sub' hmem).1
  · simpa only [OpenPartialHomeomorph.restr_apply] using hφ.mono hsubχ
  · have hsub : (φ.restr W).target ⊆ φ.target := by
      rw [OpenPartialHomeomorph.restr_target]; exact inter_subset_left
    simpa only [OpenPartialHomeomorph.restr_symm_apply] using hφ'.mono hsub
  · intro y hy
    exact hquad y (hsubχ hy)
  · exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) r).image_of_continuousOn
      ((φ.restr W).continuousOn_invFun.mono hballtgt)
  · intro y hy
    rw [modelBall] at hy
    obtain ⟨hysrc, hyr⟩ := hy
    exact ⟨(φ.restr W) y,
      Metric.mem_closedBall.mpr (by rw [dist_eq_norm, sub_zero]; exact le_of_lt hyr),
      (φ.restr W).left_inv hysrc⟩
  · rintro y ⟨z, hz, rfl⟩
    have hztgt : z ∈ (φ.restr W).target := hballtgt hz
    have hysrc : (φ.restr W).symm z ∈ (φ.restr W).source := (φ.restr W).map_target hztgt
    have hvalφ : φ ((φ.restr W).symm z) = z := (φ.restr W).right_inv hztgt
    have hzr : ‖z‖ ≤ r := by
      have h := Metric.mem_closedBall.mp hz
      simpa [dist_eq_norm] using h
    have hnorm : ‖z‖ ^ 2 < ε :=
      lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg z) hzr 2) hrsq
    have h1 := hquad ((φ.restr W).symm z) (hsubχ hysrc)
    rw [hvalφ] at h1
    have h2 : f ((φ.restr W).symm z) - f x₀ = s₁ * z 0 ^ 2 + s₂ * z 1 ^ 2 := by linarith
    rw [h2]
    have h3 : |s₁ * z 0 ^ 2 + s₂ * z 1 ^ 2| ≤ ‖z‖ ^ 2 := by
      have hz' : z 0 ^ 2 + z 1 ^ 2 = ‖z‖ ^ 2 := Work.Drive.N2.norm_uVec z
      refine abs_le.mpr ⟨?_, ?_⟩ <;>
        rcases hs₁ with h | h <;> rcases hs₂ with h' | h' <;> rw [h, h'] <;> nlinarith
    linarith

open scoped Manifold ContDiff in
open Work.Drive.Morse in
theorem exists_globalLevelFlow_of_critical {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : IsMorseDistinct f) (hmorse : MorseLemma2)
    {n : ℕ} (p : Fin n → M) (hcrit : ∀ j, IsCritical f (p j))
    (hinj : Function.Injective p) (hcover : ∀ x, IsCritical f x → ∃ j, p j = x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : ℝ × M → M, ∃ K : Set M,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ ∧ (∀ x, Φ (0, x) = x) ∧
      (∀ (u v : ℝ) (x : M), Φ (u, Φ (v, x)) = Φ (u + v, x)) ∧ IsClosed K ∧
      (∀ y ∈ K, ∃ j : Fin n, |f y - f (p j)| < ε) ∧
      (∀ (y : M) (t : ℝ),
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∉ K) → f (Φ (t, y)) = f y + t) := by
  classical
  obtain ⟨hf_sm, hnd, _hdistinct⟩ := hf
  -- Morse charts at the enumerated critical points
  have hexφ : ∀ j : Fin n,
      ∃ (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (s₁ s₂ : ℝ),
        p j ∈ ψ.source ∧ ψ (p j) = 0 ∧ (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ψ y) ψ.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ψ.symm z) ψ.target ∧
        (∀ y ∈ ψ.source, f y = f (p j) + s₁ * (ψ y 0) ^ 2 + s₂ * (ψ y 1) ^ 2) :=
    fun j => exists_morseChart_fixed hf_sm (hnd (p j) (hcrit j)) hmorse
  choose ψ s₁ s₂ hψsrc hψ0 hs₁ hs₂ hψsm hψsymm hψquad using hexφ
  -- disjoint open neighbourhoods of the critical points
  obtain ⟨T, hTopen, hTmem, _hTcl, _hTiso, hTdisj⟩ :=
    exists_disjoint_chart_neighborhoods f hf_sm hnd p hinj hcrit hcover
  -- shrink each chart, keeping a small compact value-confined region
  have hexχ : ∀ j : Fin n,
      ∃ (χ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) (C : Set M),
        0 < r ∧ p j ∈ χ.source ∧ χ (p j) = 0 ∧ χ.source ⊆ T j ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => χ y) χ.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => χ.symm z) χ.target ∧
        (∀ y ∈ χ.source, f y = f (p j) + s₁ j * (χ y 0) ^ 2 + s₂ j * (χ y 1) ^ 2) ∧
        IsCompact C ∧ C = χ.symm '' Metric.closedBall 0 r ∧
        Metric.closedBall 0 r ⊆ χ.target ∧ modelBall χ r ⊆ C ∧
        (∀ y ∈ C, |f y - f (p j)| < ε) :=
    fun j => exists_small_chart_data f (p j) (ψ j) (s₁ j) (s₂ j) (hψsrc j) (hψ0 j)
      (hs₁ j) (hs₂ j) (hψsm j) (hψsymm j) (hψquad j) ((hTopen j).mem_nhds (hTmem j)) hε
  choose χ r C hr hpχ hχ0 hχT hχsm hχsymm hχquad hCcomp hCeq hCtarget hCball hCval using hexχ
  have hCsub : ∀ j, C j ⊆ (χ j).source := by
    intro j
    rw [hCeq j]
    rintro y ⟨z, hz, rfl⟩
    exact (χ j).map_target (hCtarget j hz)
  have hCcl : ∀ j, IsCompact (closure (C j)) ∧ closure (C j) ⊆ (χ j).source := by
    intro j
    have hclosed : IsClosed (C j) := (hCcomp j).isClosed
    rw [hclosed.closure_eq]
    exact ⟨hCcomp j, hCsub j⟩
  have hCcrit : ∀ y : M, (∀ j, y ∉ C j) → ¬ IsCritical f y := by
    intro y hy hyc
    obtain ⟨j, hj⟩ := hcover y hyc
    refine hy j (hj ▸ hCball j ⟨hpχ j, ?_⟩)
    rw [hχ0 j, norm_zero]
    exact hr j
  have hdisjχ : ∀ i j : Fin n, i ≠ j → Disjoint (χ i).source (χ j).source := by
    intro i j hij
    exact Disjoint.mono ((hχT i).trans subset_closure) ((hχT j).trans subset_closure)
      (hTdisj i j hij)
  -- the global model-adapted level flow
  obtain ⟨Φ, hΦsm, hΦ0, hΦcomp, hΦlevel, _hΦODE⟩ :=
    exists_modelAdapted_levelFlow_chartODE f hf_sm p χ s₁ s₂ r hr hpχ hχ0
      (fun j => ⟨hs₁ j, hs₂ j⟩)
      (fun j y hy => by rw [hχquad j y hy, Work.Drive.N2.chartQ, add_assoc])
      hχsm hχsymm hdisjχ C hCsub hCcl hCball hCcrit
  refine ⟨Φ, ⋃ j, C j, hΦsm, hΦ0, hΦcomp, ?_, ?_, ?_⟩
  · exact isClosed_iUnion_of_finite (fun j => (hCcomp j).isClosed)
  · intro y hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    exact ⟨j, hCval j y hj⟩
  · intro y t hK
    refine hΦlevel y t ?_ ?_
    · intro i
      have h0 : (0 : ℝ) ∈ Set.Icc (min 0 t) (max 0 t) :=
        ⟨min_le_left 0 t, le_max_left 0 t⟩
      have h := hK 0 h0
      rw [hΦ0 y] at h
      intro hmem
      exact h (Set.mem_iUnion.mpr ⟨i, hCball i hmem⟩)
    · intro u hu i hmem
      exact hK u hu (Set.mem_iUnion.mpr ⟨i, hCball i hmem⟩)

end Work.Drive.N2
