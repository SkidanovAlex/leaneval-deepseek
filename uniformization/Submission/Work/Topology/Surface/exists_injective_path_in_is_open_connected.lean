import Mathlib
import Submission.Work.SimplyConnected.ABS.arc_join

/-!
# An open connected subset of a Riemann surface is arc-connected

Let `X` be a topological space with a `ℂ`-chart (so `X` is locally homeomorphic to `ℂ`, hence a
surface) and let `U ⊆ X` be open and connected.  Then any two distinct points of `U` are joined by
an **injective** path inside `U`:

`Work.Topology.Surface.exists_injective_path_in_is_open_connected`.

This is the classical statement that connected surfaces are *arc*-connected.  The proof is the
standard "the arc-reachable set is clopen" argument, for which two ingredients are needed:

* `Work.Topology.Arc.eq_or_exists_injective_path_trans` (in
  `Submission.Work.SimplyConnected.ABS.arc_join`): two injective paths `p → q → r` concatenate to an
  injective path `p → r`, unless `p = r`;
* a chart ball: in a chart, two points of a euclidean ball are joined by the image of the straight
  segment, which is injective and stays in the ball — `exists_injective_path_of_mem_chart_ball`.

The two local facts about charts are proved first, then the abstract "arc-reachable set" argument is
carried out for an arbitrary space satisfying the local input `HasInjectivePathNhdBasis`, and finally
that local input is verified for `U` using `chartAt`.

Note that the local argument is performed in the subtype `U` (rather than in `X`), which makes the
requirement "the path stays in `U`" automatic and lets the transitivity lemma above be applied
without tracking images.
-/

set_option linter.style.haveILetI false

open scoped Topology
open Set Filter

namespace Work.Topology.Surface

/-! ## Two local facts about charts -/

/-- **Straight segments in a chart ball.**  If the euclidean ball `Metric.ball a r` lies in the target
of a chart `c` and `z ≠ w` are two points of the source whose images lie in that ball, then `z` and
`w` are joined by an injective path whose `c`-image stays in the ball (so the path stays in the
chart, being the straight segment between `c z` and `c w` pulled back by `c.symm`). -/
theorem exists_injective_path_of_mem_chart_ball {X : Type*} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X ℂ) {a : ℂ} {r : ℝ}
    (htarget : Metric.ball a r ⊆ c.target)
    {z w : X} (hz : z ∈ c.source) (hw : w ∈ c.source)
    (hzc : c z ∈ Metric.ball a r) (hwc : c w ∈ Metric.ball a r) (hzw : z ≠ w) :
    ∃ γ : Path z w, Function.Injective γ ∧
      ∀ t : unitInterval, (γ t : X) ∈ c.source ∧ c (γ t) ∈ Metric.ball a r := by
  have hczw : c z ≠ c w := fun h => hzw (c.injOn hz hw h)
  have hball : ∀ t : unitInterval, (1 - (t : ℝ)) • c z + (t : ℝ) • c w ∈ Metric.ball a r :=
    fun t => (convex_ball a r) hzc hwc (a := 1 - (t : ℝ)) (b := (t : ℝ))
      (by linarith [t.2.2]) t.2.1 (by ring)
  let g : unitInterval → ℂ := fun t => (1 - (t : ℝ)) • c z + (t : ℝ) • c w
  have hgcont : Continuous g := by fun_prop
  have hfcont : Continuous (fun t => c.symm (g t)) :=
    c.continuousOn_symm.comp_continuous hgcont (fun t => htarget (hball t))
  let f : Path z w := Path.mk ⟨fun t => c.symm (g t), hfcont⟩
    (by simpa [g] using c.left_inv hz) (by simpa [g] using c.left_inv hw)
  have hft : ∀ t : unitInterval, (f t : X) = c.symm (g t) := fun t => rfl
  refine ⟨f, ?_, ?_⟩
  · intro s t hst
    have h2 : g s = g t := by
      have h3 : c (c.symm (g s)) = c (c.symm (g t)) :=
        congrArg c (by rw [← hft s, ← hft t]; exact hst)
      rwa [c.right_inv (htarget (hball s)), c.right_inv (htarget (hball t))] at h3
    have hlm : (AffineMap.lineMap (c z) (c w)) (s : ℝ)
        = (AffineMap.lineMap (c z) (c w)) (t : ℝ) := by
      simpa only [g, AffineMap.lineMap_apply_module] using h2
    rcases (AffineMap.lineMap_eq_lineMap_iff.mp hlm) with h | h
    · exact absurd h hczw
    · exact Subtype.ext h
  · intro t
    refine ⟨?_, ?_⟩
    · rw [hft t]; exact c.map_target (htarget (hball t))
    · rw [hft t, c.right_inv (htarget (hball t))]; exact hball t

/-- **Chart balls are a neighbourhood basis.**  A neighbourhood of `c.symm ζ` contains the
`c.symm`-image of a euclidean ball around `ζ` (which also lies in the target of `c`). -/
theorem exists_chart_ball_subset_of_mem_nhds {X : Type*} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X ℂ) {ζ : ℂ} (hζ : ζ ∈ c.target) {S : Set X}
    (hS : S ∈ nhds (c.symm ζ)) :
    ∃ ε > 0, Metric.ball ζ ε ⊆ c.target ∧ c.symm '' Metric.ball ζ ε ⊆ S := by
  have hcAt : ContinuousAt c.symm ζ :=
    c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hζ)
  have h1 : c.symm ⁻¹' S ∈ nhds ζ := Filter.mem_map.mp (Filter.le_def.mp hcAt S hS)
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp h1
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hζ)
  refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, ?_, ?_⟩
  · exact subset_trans (Metric.ball_subset_ball (min_le_right _ _)) hε₂
  · rintro x ⟨b, hb, rfl⟩
    exact hε₁ (Metric.ball_subset_ball (min_le_left _ _) hb)

/-! ## The local input and the arc-reachable set -/

/-- The local input of the arc theorem: every point has a neighbourhood basis each member `V` of
which has the property that any other point of `V` is joined to the centre by an **injective** path
with range in `V`. -/
def HasInjectivePathNhdBasis (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ y : Y, ∀ N ∈ nhds y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ V ⊆ N ∧
    ∀ w : Y, w ∈ V → w ≠ y → ∃ γ : Path y w, Function.Injective γ ∧ Set.range γ ⊆ V

/-- **The arc-reachable set is clopen.**  In a connected Hausdorff space with the local input
`HasInjectivePathNhdBasis`, any two distinct points are joined by an injective path.

Let `A` be the set of points reachable from `x` by an injective path (together with `x` itself).
`A` is open because the local input supplies injective paths from any `z ∈ A` to all nearby points,
which concatenate with an arc `x → z` by
`Work.Topology.Arc.eq_or_exists_injective_path_trans`; `A` is closed because a nearby point `w`
joined to `y` by an injective path would give arcs `x → w → y`, hence an arc `x → y`.  Connectivity
forces `A = univ`, and since `x ≠ y` the conclusion follows. -/
theorem exists_injective_path_of_hasInjectivePathNhdBasis {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] [ConnectedSpace Y] (h : HasInjectivePathNhdBasis Y)
    {x y : Y} (hxy : x ≠ y) : ∃ γ : Path x y, Function.Injective γ := by
  let A : Set Y := {z : Y | z = x ∨ ∃ γ : Path x z, Function.Injective γ}
  have hxA : x ∈ A := Or.inl rfl
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases hz with hzx | ⟨γ, hγ⟩
    · rw [hzx]
      obtain ⟨V, hVopen, hxV, -, hV⟩ := h x univ univ_mem
      refine mem_of_superset (hVopen.mem_nhds hxV) ?_
      intro w hw
      rcases eq_or_ne w x with rfl | hwx
      · exact Or.inl rfl
      · obtain ⟨β, hβ, -⟩ := hV w hw hwx
        exact Or.inr ⟨β, hβ⟩
    · obtain ⟨V, hVopen, hzV, -, hV⟩ := h z univ univ_mem
      refine mem_of_superset (hVopen.mem_nhds hzV) ?_
      intro w hw
      rcases eq_or_ne w z with rfl | hwz
      · exact Or.inr ⟨γ, hγ⟩
      rcases eq_or_ne w x with rfl | hwx
      · exact Or.inl rfl
      · obtain ⟨β, hβ, -⟩ := hV w hw hwz
        rcases Work.Topology.Arc.eq_or_exists_injective_path_trans γ β hγ hβ with h' | ⟨δ, hδ⟩
        · exact absurd h'.symm hwx
        · exact Or.inr ⟨δ, hδ⟩
  have hAclosed : IsClosed A := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y' hy'
    have hynx : y' ∈ ({x} : Set Y)ᶜ := by
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hyx
      exact hy' (hyx ▸ hxA)
    obtain ⟨V, hVopen, hyV, hVsub, hV⟩ :=
      h y' ({x} : Set Y)ᶜ (isClosed_singleton.isOpen_compl.mem_nhds hynx)
    refine mem_of_superset (hVopen.mem_nhds hyV) ?_
    intro w hw hwA
    have hwx : w ≠ x := fun hh => hVsub hw (by rw [hh]; exact mem_singleton x)
    rcases hwA with hwAx | ⟨γ, hγ⟩
    · exact hwx hwAx
    · have hwy : w ≠ y' := fun hh => hy' (hh ▸ (Or.inr ⟨γ, hγ⟩ : w ∈ A))
      obtain ⟨β, hβ, -⟩ := hV w hw hwy
      have hβsymm : Function.Injective ⇑(β.symm) := by
        intro s t hst
        rw [Path.symm_apply, Path.symm_apply] at hst
        exact unitInterval.symm_bijective.injective (hβ hst)
      rcases Work.Topology.Arc.eq_or_exists_injective_path_trans γ β.symm hγ hβsymm
        with h' | ⟨δ, hδ⟩
      · exact hy' (h'.symm ▸ hxA)
      · exact hy' (Or.inr ⟨δ, hδ⟩)
  have hAclopen : IsClopen A := ⟨hAclosed, hAopen⟩
  have hAuniv : A = univ := by
    rcases (isClopen_iff.mp hAclopen) with h0 | h1
    · exfalso
      rw [h0] at hxA
      exact hxA
    · exact h1
  have hyA : y ∈ A := by rw [hAuniv]; exact mem_univ y
  rcases hyA with hyx | ⟨γ, hγ⟩
  · exact absurd hyx.symm hxy
  · exact ⟨γ, hγ⟩

/-! ## The local input for an open subset of a charted space -/

/-- Every nonempty open subset of a `ℂ`-charted space satisfies `HasInjectivePathNhdBasis`: around
any point, a chart ball (intersected with the subset) is such a neighbourhood. -/
theorem hasInjectivePathNhdBasis_of_isOpen {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} (hUo : IsOpen U) : HasInjectivePathNhdBasis U := by
  intro z N hN
  obtain ⟨O, hON, hOopen, hzO⟩ := mem_nhds_iff.mp hN
  obtain ⟨W₀, hW₀open, hW₀eq⟩ := isOpen_induced_iff.mp hOopen
  have hzW₀ : (z : X) ∈ W₀ := by
    have h : z ∈ Subtype.val ⁻¹' W₀ := by rw [hW₀eq]; exact hzO
    exact h
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ (z : X)
  have hzsrc : (z : X) ∈ c.source := mem_chart_source ℂ (z : X)
  have hζtgt : c (z : X) ∈ c.target := c.map_source hzsrc
  have hSnhd : W₀ ∩ U ∈ nhds (c.symm (c (z : X))) := by
    rw [c.left_inv hzsrc]
    exact (hW₀open.inter hUo).mem_nhds ⟨hzW₀, z.2⟩
  obtain ⟨ε, hεpos, hεtgt, hεS⟩ := exists_chart_ball_subset_of_mem_nhds c hζtgt hSnhd
  refine ⟨Subtype.val ⁻¹' (c.symm '' Metric.ball (c (z : X)) ε), ?_, ?_, ?_, ?_⟩
  · exact (c.symm.isOpen_image_of_subset_source Metric.isOpen_ball hεtgt).preimage
      continuous_subtype_val
  · exact ⟨c (z : X), Metric.mem_ball_self hεpos, c.left_inv hzsrc⟩
  · intro p hp
    exact hON (by rw [← hW₀eq]; exact (hεS hp).1)
  · intro w hw hwz
    obtain ⟨b, hb, hbw⟩ := hw
    have hbtgt : b ∈ c.target := hεtgt hb
    have hwsrc : (w : X) ∈ c.source := by rw [← hbw]; exact c.map_target hbtgt
    have hcwb : c (w : X) ∈ Metric.ball (c (z : X)) ε := by
      rw [← hbw, c.right_inv hbtgt]; exact hb
    have hzw : (z : X) ≠ (w : X) := fun h => hwz (Subtype.ext h.symm)
    obtain ⟨γ, hγinj, hγ⟩ := exists_injective_path_of_mem_chart_ball c hεtgt hzsrc hwsrc
      (Metric.mem_ball_self hεpos) hcwb hzw
    have hmemW : ∀ t : unitInterval, γ t ∈ c.symm '' Metric.ball (c (z : X)) ε :=
      fun t => ⟨c (γ t), (hγ t).2, c.left_inv (hγ t).1⟩
    have hmemU : ∀ t : unitInterval, γ t ∈ U := fun t => (hεS (hmemW t)).2
    refine ⟨Path.mk ⟨fun t => ⟨γ t, hmemU t⟩, γ.continuous.subtype_mk hmemU⟩
      (Subtype.ext γ.source) (Subtype.ext γ.target), ?_, ?_⟩
    · intro s t hst
      exact hγinj (Subtype.ext_iff.mp hst)
    · intro p hp
      obtain ⟨t, rfl⟩ := hp
      exact hmemW t

/-! ## The main theorem -/

/-- **An open connected subset of a Riemann surface is arc-connected**: any two distinct points of
`U` are joined by an injective path inside `U`. -/
theorem exists_injective_path_in_is_open_connected {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {U : Set X} (hUo : IsOpen U) (hUc : IsConnected U) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) :
    ∃ γ : Path x y, (∀ t : unitInterval, (γ t : X) ∈ U) ∧ Function.Injective γ := by
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUc
  have hbasis : HasInjectivePathNhdBasis U := hasInjectivePathNhdBasis_of_isOpen hUo
  have hxy' : (⟨x, hx⟩ : U) ≠ ⟨y, hy⟩ := fun h => hxy (Subtype.ext_iff.mp h)
  obtain ⟨γ, hγinj⟩ := exists_injective_path_of_hasInjectivePathNhdBasis hbasis hxy'
  refine ⟨γ.map continuous_subtype_val, ?_, ?_⟩
  · intro t
    simp
  · rw [Path.map_coe]
    exact Subtype.val_injective.comp hγinj

end Work.Topology.Surface
