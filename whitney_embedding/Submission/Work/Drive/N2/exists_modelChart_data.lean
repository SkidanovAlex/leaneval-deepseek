import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.exists_morseChart_fixed
import Submission.Work.Drive.N2.exists_disjoint_chart_neighborhoods
import Submission.Work.Drive.N2.exists_distinct_criticalValues

/-!
# The chart/region data of the `n = 2` construction

Target of this file: `Work.Drive.N2.exists_modelChart_data`.  For a compact surface with a Morse
function having distinct critical values it produces the whole package consumed by the `n = 2`
Morse-theoretic construction: an injective enumeration `x i` of the critical points, pairwise
disjoint Morse charts `φ i` at them (centred, and equal to `f (x i) + s₁ u² + s₂ v²` on their
sources), signs `s₁ i, s₂ i ∈ {±1}`, radii `r i > 0` and regions `C i` whose closures are compact
and contained in the charts and which contain the corresponding model balls, such that every critical
point lies in one of the `C i`.

The ingredients are all previously proved bricks:

* `Work.Drive.N2.exists_injective_enum_critical` (`exists_distinct_criticalValues.lean`) —
  an injective listing of the (finitely many) critical points;
* `Work.Drive.N2.exists_disjoint_chart_neighborhoods` — open neighbourhoods `T i` of the critical
  points with pairwise disjoint closures;
* `Work.Drive.N2.exists_morseChart_fixed` — a Morse chart at a nondegenerate critical point, from the
  planar Morse lemma `Work.Drive.Morse.MorseLemma2`;
* `Work.Drive.N2.exists_ball_preimage_subset` (below, a general topological brick) and
  `Work.Drive.N2.exists_shrunk_chart_data` (below) — shrink each Morse chart into the prescribed
  `T i` while keeping a compact region containing a model ball.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

/-- **Balls around the centre of a chart inside a prescribed neighbourhood.**  For an open partial
homeomorphism `φ : X → Y` into a pseudometric space, a point `x` of its source, and a neighbourhood
`T` of `x`, there is `ρ > 0` such that the closed `φ x`-ball of radius `ρ` lies in the target of `φ`
and its `φ.symm`-image lies in `T`.

(Equivalently: the images under `φ.symm` of the balls of radius `ρ` form a neighbourhood basis of
`x`, because `φ.symm` is continuous at `φ x` and `φ.symm (φ x) = x`.) -/
lemma exists_ball_preimage_subset {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (φ : OpenPartialHomeomorph X Y) {x : X} (hx : x ∈ φ.source) {T : Set X} (hT : T ∈ 𝓝 x) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (φ x) ρ ⊆ φ.target ∧
      φ.symm '' Metric.closedBall (φ x) ρ ⊆ T := by
  have hcont : ContinuousAt (fun z => φ.symm z) (φ x) :=
    φ.continuousOn_invFun.continuousAt (φ.open_target.mem_nhds (φ.map_source hx))
  have hTx : T ∩ φ.source ∈ 𝓝 x := Filter.inter_mem hT (φ.open_source.mem_nhds hx)
  have hleft : φ.symm (φ x) = x := φ.left_inv hx
  have hmem : T ∩ φ.source ∈ 𝓝 (φ.symm (φ x)) := by rw [hleft]; exact hTx
  have hpre : φ.symm ⁻¹' (T ∩ φ.source) ∈ 𝓝 (φ x) := hcont.preimage_mem_nhds hmem
  have htgt : φ.target ∈ 𝓝 (φ x) := φ.open_target.mem_nhds (φ.map_source hx)
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hpre htgt)
  refine ⟨δ / 2, half_pos hδpos, ?_, ?_⟩
  · intro z hz
    exact (hδsub (Metric.closedBall_subset_ball (half_lt_self hδpos) hz)).2
  · rintro z ⟨w, hw, rfl⟩
    exact (hδsub (Metric.closedBall_subset_ball (half_lt_self hδpos) hw)).1.1

/-- **Shrinking a Morse chart into a prescribed neighbourhood, keeping a compact region.**  Given a
chart `φ` centred at `x₀` on which `f` is the quadratic normal form `f x₀ + s₁ u² + s₂ v²`, and a
neighbourhood `T` of `x₀`, there are a chart `χ` with `χ.source ⊆ T`, a radius `r > 0` and a set `C`
with `C ⊆ χ.source`, `IsCompact (closure C)`, `closure C ⊆ χ.source`, such that `C` contains the whole
`χ`-ball of radius `r` around `x₀` and all the data (normal form, smoothness of `χ` and `χ⁻¹`) still
holds for `χ`. -/
theorem exists_shrunk_chart_data {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    (f : M → ℝ) (x₀ : M) (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ : ℝ) (hx₀ : x₀ ∈ φ.source) (hcen : φ x₀ = 0)
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    (hφ' : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ.symm z) φ.target)
    (hquad : ∀ y ∈ φ.source, f y = f x₀ + s₁ * (φ y 0) ^ 2 + s₂ * (φ y 1) ^ 2)
    {T : Set M} (hT : T ∈ 𝓝 x₀) :
    ∃ (χ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) (C : Set M),
      0 < r ∧ x₀ ∈ χ.source ∧ χ x₀ = 0 ∧ χ.source ⊆ T ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => χ y) χ.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => χ.symm z) χ.target ∧
      (∀ y ∈ χ.source, f y = f x₀ + s₁ * (χ y 0) ^ 2 + s₂ * (χ y 1) ^ 2) ∧
      C ⊆ χ.source ∧ IsCompact (closure C) ∧ closure C ⊆ χ.source ∧
      {y | y ∈ χ.source ∧ ‖χ y‖ < r} ⊆ C := by
  -- an open neighbourhood of `x₀` inside `T`
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hT
  have hWopen : IsOpen (U ∩ φ.source) := hUopen.inter φ.open_source
  have hWmem : x₀ ∈ U ∩ φ.source := ⟨hxU, hx₀⟩
  obtain ⟨ρ, hρpos, hρtgt, hρsub⟩ :=
    exists_ball_preimage_subset φ hx₀ (hWopen.mem_nhds hWmem)
  -- the shrunk chart
  have hχsrc : ((φ.restr (U ∩ φ.source))).source = U ∩ φ.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hWopen]
    ext y
    simp only [Set.mem_inter_iff]
    tauto
  have hχtgt : ((φ.restr (U ∩ φ.source))).target ⊆ φ.target := by
    rw [OpenPartialHomeomorph.restr_target]
    exact Set.inter_subset_left
  refine ⟨φ.restr (U ∩ φ.source), ρ, φ.symm '' Metric.closedBall (φ x₀) ρ,
    hρpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hχsrc]; exact hWmem
  · show φ x₀ = 0
    exact hcen
  · rw [hχsrc]; exact subset_trans Set.inter_subset_left hUsub
  · have hsub : ((φ.restr (U ∩ φ.source))).source ⊆ φ.source := by
      rw [hχsrc]; exact Set.inter_subset_right
    exact hφ.mono hsub
  · exact hφ'.mono hχtgt
  · intro y hy
    have hyφ : y ∈ φ.source := by
      rw [hχsrc] at hy; exact hy.2
    show f y = f x₀ + s₁ * (φ y 0) ^ 2 + s₂ * (φ y 1) ^ 2
    exact hquad y hyφ
  · rw [hχsrc]
    exact hρsub
  · have hcomp : IsCompact (φ.symm '' Metric.closedBall (φ x₀) ρ) :=
      (isCompact_closedBall (φ x₀) ρ).image_of_continuousOn (φ.continuousOn_invFun.mono hρtgt)
    have hcl : closure (φ.symm '' Metric.closedBall (φ x₀) ρ)
        = φ.symm '' Metric.closedBall (φ x₀) ρ := hcomp.isClosed.closure_eq
    rw [hcl]; exact hcomp
  · have hcomp : IsCompact (φ.symm '' Metric.closedBall (φ x₀) ρ) :=
      (isCompact_closedBall (φ x₀) ρ).image_of_continuousOn (φ.continuousOn_invFun.mono hρtgt)
    have hcl : closure (φ.symm '' Metric.closedBall (φ x₀) ρ)
        = φ.symm '' Metric.closedBall (φ x₀) ρ := hcomp.isClosed.closure_eq
    rw [hcl, hχsrc]
    exact hρsub
  · intro y hy
    have hyφ : y ∈ φ.source := by
      rw [hχsrc] at hy; exact hy.1.2
    have hlt : ‖φ y‖ < ρ := by
      have h := hy.2
      rwa [show φ.restr (U ∩ φ.source) y = φ y from rfl] at h
    refine ⟨φ y, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, hcen, sub_zero]
      exact le_of_lt hlt
    · exact φ.left_inv hyφ

/-- **The chart/region data of the construction exists.**  For a compact surface with a Morse function
having distinct critical values one can produce the whole package that
`Work.Drive.N2.exists_modelAdapted_levelFlow` consumes: an enumeration of the critical points,
pairwise disjoint Morse charts at them (quadratic on their sources), signed quadratic forms, radii and
regions whose closures are compactly contained in the charts and which contain the corresponding model
balls, and which cover every critical point. -/
theorem exists_modelChart_data {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f)
    (hmorse : Work.Drive.Morse.MorseLemma2) :
    ∃ (N : ℕ) (x : Fin N → M) (φ : Fin N → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
      (s₁ s₂ r : Fin N → ℝ) (C : Fin N → Set M),
      (∀ i, 0 < r i) ∧
      (∀ i, x i ∈ (φ i).source) ∧
      (∀ i, φ i (x i) = 0) ∧
      (∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1)) ∧
      (∀ i y, y ∈ (φ i).source →
        f y = f (x i) + (s₁ i * (φ i y 0) ^ 2 + s₂ i * (φ i y 1) ^ 2)) ∧
      (∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ i y) (φ i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (φ i).symm y) (φ i).target) ∧
      (∀ i j, i ≠ j → Disjoint (φ i).source (φ j).source) ∧
      (∀ i, C i ⊆ (φ i).source) ∧
      (∀ i, IsCompact (closure (C i)) ∧ closure (C i) ⊆ (φ i).source) ∧
      (∀ i, {y | y ∈ (φ i).source ∧ ‖φ i y‖ < r i} ⊆ C i) ∧
      (∀ y, (∀ i, y ∉ C i) → ¬ Work.Drive.Morse.IsCritical f y) := by
  classical
  have hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f := hf.1
  have hnd : ∀ x, Work.Drive.Morse.IsCritical f x → Work.Drive.Morse.NondegCrit f x := hf.2.1
  -- an injective enumeration of the critical points
  obtain ⟨N, x, hxinj, hxcrit, hxcover⟩ :=
    Work.Drive.N2.exists_injective_enum_critical f hsmooth hnd
  -- pairwise disjoint open neighbourhoods of the critical points
  obtain ⟨T, hTopen, hTmem, _hTcl, _hTiso, hTdisj⟩ :=
    Work.Drive.N2.exists_disjoint_chart_neighborhoods f hsmooth hnd x hxinj hxcrit hxcover
  -- a Morse chart at each critical point
  have hexφ : ∀ i : Fin N,
      ∃ (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (s₁ s₂ : ℝ),
        x i ∈ φ.source ∧ φ (x i) = 0 ∧ (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ.symm z) φ.target ∧
        (∀ y ∈ φ.source, f y = f (x i) + s₁ * (φ y 0) ^ 2 + s₂ * (φ y 1) ^ 2) :=
    fun i => exists_morseChart_fixed hsmooth (hnd (x i) (hxcrit i)) hmorse
  choose φ s₁ s₂ hxφsrc hxφ0 hs₁ hs₂ hφsm hφsymm hφquad using hexφ
  -- shrink each Morse chart into `T i`, keeping a compact region
  have hexχ : ∀ i : Fin N,
      ∃ (χ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) (C : Set M),
        0 < r ∧ x i ∈ χ.source ∧ χ (x i) = 0 ∧ χ.source ⊆ T i ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => χ y) χ.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => χ.symm z) χ.target ∧
        (∀ y ∈ χ.source, f y = f (x i) + s₁ i * (χ y 0) ^ 2 + s₂ i * (χ y 1) ^ 2) ∧
        C ⊆ χ.source ∧ IsCompact (closure C) ∧ closure C ⊆ χ.source ∧
        {y | y ∈ χ.source ∧ ‖χ y‖ < r} ⊆ C :=
    fun i => exists_shrunk_chart_data f (x i) (φ i) (s₁ i) (s₂ i) (hxφsrc i) (hxφ0 i)
      (hφsm i) (hφsymm i) (hφquad i) ((hTopen i).mem_nhds (hTmem i))
  choose χ r C hr hχsrc hχ0 hχT hχsm hχsymm hχquad hCsub hCcomp hCcl hCball using hexχ
  refine ⟨N, x, χ, s₁, s₂, r, C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hr
  · exact hχsrc
  · exact hχ0
  · exact fun i => ⟨hs₁ i, hs₂ i⟩
  · intro i y hy
    rw [hχquad i y hy, add_assoc]
  · exact hχsm
  · exact hχsymm
  · intro i j hij
    refine (hTdisj i j hij).mono (subset_trans (hχT i) subset_closure)
      (subset_trans (hχT j) subset_closure)
  · exact hCsub
  · exact fun i => ⟨hCcomp i, hCcl i⟩
  · exact hCball
  · intro y hnot hycrit
    obtain ⟨i, hi⟩ := hxcover y hycrit
    exact hnot i (hi ▸ hCball i ⟨hχsrc i, by rw [hχ0 i, norm_zero]; exact hr i⟩)

end Work.Drive.N2

