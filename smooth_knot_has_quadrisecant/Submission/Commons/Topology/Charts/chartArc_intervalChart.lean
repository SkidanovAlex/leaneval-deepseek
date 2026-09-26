import Mathlib.Algebra.Order.Star.Real

open Set
open scoped Topology

namespace Commons.Topology.Charts

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

/-- Affine homeomorphism from a bounded open interval `(a,b)` of the real
line (with `a < b`) to the open unit interval `(0,1)`.  Used to finish the
interval-charting: the nonempty coordinate strip, rewritten as
`Ioo (max lo 0) (min hi 1)`, is stretched affinely onto `(0,1)`. -/
noncomputable def intervalHomeo_openUnit {a b : ℝ} (hab : a < b) :
    {t : ℝ // t ∈ Set.Ioo a b} ≃ₜ {t : ℝ // t ∈ Set.Ioo 0 1} where
  toFun := fun x => ⟨(x.1 - a) / (b - a), by
    rw [Set.mem_Ioo]
    constructor
    · exact div_pos (sub_pos.mpr (Set.mem_Ioo.mp x.2).1) (sub_pos.mpr hab)
    · rw [div_lt_one (sub_pos.mpr hab)]
      linarith [Set.mem_Ioo.mp x.2]⟩
  invFun := fun y => ⟨a + (b - a) * y.1, by
    rw [Set.mem_Ioo]
    constructor
    · nlinarith [Set.mem_Ioo.mp y.2]
    · nlinarith [Set.mem_Ioo.mp y.2, hab]⟩
  left_inv := by
    intro x
    ext
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  right_inv := by
    intro y
    ext
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

/-- **Interval-charting of a chart-arc**: in a topological space `X`, let
`U` be a set with an arc chart `ψ : (0,1) ≃ₜ {x : X // x ∈ U}` (the
subtype `{t : ℝ // t ∈ Ioo 0 1}` is the open unit interval).  If the
coordinate strip `(lo,hi)` MEETS the unit interval (`hne`), then the
image under the chart coercion `t ↦ (ψ t : X)` of the strip
`{t | lo < (t : ℝ) < hi}` is interval-charted: its subtype is
homeomorphic to the open unit interval.

Proof outline: the map `t ↦ (ψ t : X)` is an embedding onto its image
(`ψ` is a homeo, the subtype-value map is an embedding), so the image
subtype is homeomorphic to the coordinate strip set
`D := {t : {t : ℝ // t ∈ Ioo 0 1} | (t : ℝ) ∈ Ioo lo hi}`; `D` is
homeomorphic (via the value map) to the real interval
`Ioo lo hi ∩ Ioo 0 1`, which is a nonempty open preconnected subset of ℝ
(`hne`), hence homeomorphic to `(0,1)` (e.g. via the classification of
open connected subsets of ℝ / an explicit interval homeo
`homeo_Ioo_openUnit`-style with the intersection rewritten to
`Ioo (max lo 0) (min hi 1)`). -/
theorem chartArc_intervalChart {X : Type*} [TopologicalSpace X] (U : Set X)
    (ψ : {t : ℝ // t ∈ Set.Ioo 0 1} ≃ₜ {x : X // x ∈ U})
    (lo hi : ℝ) (hne : (Set.Ioo lo hi ∩ Set.Ioo 0 1).Nonempty) :
    Nonempty ({x : X // x ∈ (fun t : {t : ℝ // t ∈ Set.Ioo 0 1} =>
      ((ψ t : {x : X // x ∈ U}) : X)) ''
      {t : {t : ℝ // t ∈ Set.Ioo 0 1} | (t : ℝ) ∈ Set.Ioo lo hi}} ≃ₜ
      {t : ℝ // t ∈ Set.Ioo 0 1}) := by
  classical
  -- The unit-interval coordinate subtype and the chart coercion.
  let T : Type := {t : ℝ // t ∈ Set.Ioo 0 1}
  let f : T → X := fun t => ((ψ t : {x : X // x ∈ U}) : X)
  let strip : Set T := {t : T | (t : ℝ) ∈ Set.Ioo lo hi}
  -- `C` is the coordinate strip set `D` of the proof outline.
  let C : Type := {t : T // t ∈ strip}
  -- The chart coercion is an embedding (homeo `ψ` composed with the
  -- subtype-value inclusion), so `homeomorphImage` realises the left half
  -- of the chain: `C ≃ₜ` image-subtype.
  have hf_emb : Topology.IsEmbedding f := by
    exact (Topology.IsEmbedding.comp
      (Topology.IsEmbedding.subtypeVal (p := fun x : X => x ∈ U))
      (Homeomorph.isEmbedding ψ))
  have hψ : C ≃ₜ {x : X // x ∈ f '' strip} := by
    simpa [C] using (hf_emb.homeomorphImage strip)
  -- The real-coordinate map `c ↦ (c : ℝ)` on `C` is also an embedding.
  have hval : Topology.IsEmbedding (fun c : C => ((c : T) : ℝ)) := by
    exact (Topology.IsEmbedding.comp
      (Topology.IsEmbedding.subtypeVal (p := fun t : ℝ => t ∈ Set.Ioo 0 1))
      (Topology.IsEmbedding.subtypeVal (p := fun t : T => t ∈ strip)))
  -- Its range is exactly the coordinate interval `(lo,hi) ∩ (0,1)`.
  have hrange' : Set.range (fun c : C => ((c : T) : ℝ)) = Set.Ioo lo hi ∩ Set.Ioo 0 1 := by
    ext r
    constructor
    · rintro ⟨c, rfl⟩
      constructor
      · exact c.2
      · exact c.1.2
    · rintro ⟨hr1, hr2⟩
      refine ⟨⟨⟨r, hr2⟩, ?_⟩, rfl⟩
      exact hr1
  -- ... which, `hne` being nonempty, rewrites to `Ioo (max lo 0) (min hi 1)`
  -- with `max lo 0 < min hi 1`.
  have hrange : Set.range (fun c : C => ((c : T) : ℝ)) = Set.Ioo (max lo 0) (min hi 1) := by
    rw [hrange', Set.Ioo_inter_Ioo]
  have hneJ : (Set.Ioo (max lo 0) (min hi 1)).Nonempty := by
    rwa [Set.Ioo_inter_Ioo] at hne
  rcases hneJ with ⟨x, hx⟩
  have hab : max lo 0 < min hi 1 := lt_trans (Set.mem_Ioo.mp hx).1 (Set.mem_Ioo.mp hx).2
  -- Assemble: image ≃ₜ C ≃ₜ real interval ≃ₜ (0,1).
  let hv : C ≃ₜ {t : ℝ // t ∈ Set.Ioo (max lo 0) (min hi 1)} :=
    (Topology.IsEmbedding.toHomeomorph hval).trans (Homeomorph.setCongr hrange)
  let H := (hψ.symm).trans (hv.trans (intervalHomeo_openUnit hab))
  change Nonempty ({x : X // x ∈ f '' strip} ≃ₜ {t : ℝ // t ∈ Set.Ioo 0 1})
  exact ⟨H⟩

end Commons.Topology.Charts