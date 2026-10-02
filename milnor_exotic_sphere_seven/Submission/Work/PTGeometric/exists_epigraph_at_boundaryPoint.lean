import Mathlib
import Submission.Work.PTGeometric.SourceRegionSetupBasic
import Submission.Work.PTGeometric.WeakRegion.exists_graph_halfSpace_cinf
import Submission.Work.PTGeometric.WeakRegion.modelData_boundaryZero_cinf

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the epigraph description of the source region at a boundary point

`Work.PTGeometric.exists_epigraph_at_boundaryPoint`: at a point `x` of the half-space model
`A = ℝ^{8+k+1}_+` which lies on the boundary (`x.1 0 = 0`) and at which the defining function `Φ` of
the source region is nonpositive, the region `{Φ ≤ 0}` is, near `x`, the *epigraph*
`{ψ (tail z) ≤ z 0}` of a nonnegative `C^∞` function `ψ` of the tangential coordinates, with
`ψ (tail x) = 0`.

The statement is a general fact about a smooth function on the half-space satisfying the boundary
clauses of `Work.PTGeometric.SourceRegionPhiInteriorSign` (a boundary-zero clause
`mfderiv Φ x = c • mfderiv (boundary coordinate) x`, `c < 0`, and the boundary sign condition), so it
is proved here in the general form `exists_epigraph_of_boundary_zero` (and the trivial case
`Φ x < 0` as `exists_epigraph_of_neg`); the target is their combination through `sourcePhi_spec`.

The route in the boundary-zero case is

* `Work.PTGeometric.WeakRegion.modelData_boundaryZero_cinf` reads `Φ` in the preferred
  (identity!) chart of `A` and produces `Ψ = Φ ∘ (clamp)` with
  `fderivWithin ℝ Ψ (range (𝓡∂ n)) p = c • proj 0`, `c < 0`, together with the boundary sign
  condition;
* `Work.PTGeometric.WeakRegion.exists_graph_halfSpace_cinf` (the half-space graph result) then
  produces the graph function `h` and the epigraph equivalence on a relative neighbourhood of `p`;
* `extChartAt (𝓡∂ n) x` is the ambient identity (`extChartAt_halfSpace_apply`), which turns the
  chart statement into the ambient one.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-! ## The half-space in identity coordinates -/

/-- **The extended chart at a point of the half-space is the identity** (the charted space structure
of `EuclideanHalfSpace n` is the self one, so `chartAt` is `OpenPartialHomeomorph.refl`). -/
theorem extChartAt_halfSpace_apply {n : ℕ} [NeZero n] (x y : EuclideanHalfSpace n) :
    (extChartAt (modelWithCornersEuclideanHalfSpace n) x) y = y.1 := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe, chartAt_self_eq]
  rfl

/-- The source of the extended chart at a point of the half-space is everything. -/
theorem extChartAt_halfSpace_source {n : ℕ} [NeZero n] (x : EuclideanHalfSpace n) :
    (extChartAt (modelWithCornersEuclideanHalfSpace n) x).source = univ := by
  rw [extChartAt, OpenPartialHomeomorph.extend_source, chartAt_self_eq]
  rfl

/-- The inverse of the extended chart at a point of the half-space is the clamping of the first
coordinate, so on the half-space it is again the identity. -/
theorem extChartAt_halfSpace_symm {n : ℕ} [NeZero n] (x : EuclideanHalfSpace n)
    {z : EuclideanSpace ℝ (Fin n)} (hz : 0 ≤ z.ofLp 0) :
    (extChartAt (modelWithCornersEuclideanHalfSpace n) x).symm z = ⟨z, hz⟩ := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe_symm, chartAt_self_eq, Function.comp_apply,
    OpenPartialHomeomorph.refl_symm]
  exact modelWithCornersEuclideanHalfSpace_symm_apply_of_le hz

/-! ## The two cases -/

/-- **The epigraph description at a boundary point where the function is strictly negative.**  Then
the region contains a whole neighbourhood of the point and `ψ = 0`, `W = univ` work: the epigraph
`{0 ≤ z 0}` is the whole half-space.

The set `V` is the preimage of `{Φ < 0}` under the clamping map `(𝓡∂ n).symm`, which is continuous
and equal to the identity on the half-space. -/
theorem exists_epigraph_of_neg {n : ℕ} [NeZero n]
    (Φ : EuclideanHalfSpace n → ℝ)
    (hΦ : ContMDiff (modelWithCornersEuclideanHalfSpace n) (modelWithCornersSelf ℝ ℝ)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) Φ)
    {x : EuclideanHalfSpace n} (hx : Φ x < 0) :
    ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (W V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen W ∧ tailVec x.1 ∈ W ∧
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) ψ W ∧
      (∀ u ∈ W, 0 ≤ ψ u) ∧ ψ (tailVec x.1) = 0 ∧
      IsOpen V ∧ x.1 ∈ V ∧ V ⊆ tailVec ⁻¹' W ∧
      (∀ (z : EuclideanSpace ℝ (Fin n)) (hzV : z ∈ V) (hz : 0 ≤ z.ofLp 0),
        (Φ ⟨z, hz⟩ ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0)) := by
  have hcont : Continuous fun z : EuclideanSpace ℝ (Fin n) => Φ ((𝓡∂ n).symm z) := by
    have h1 : Continuous Φ := hΦ.continuous
    fun_prop
  have hxsymm : (𝓡∂ n).symm x.1 = x := by
    simpa using modelWithCornersEuclideanHalfSpace_symm_apply_of_le (n := n) x.2
  refine ⟨fun _ => 0, univ, {z | Φ ((𝓡∂ n).symm z) < 0}, isOpen_univ, Set.mem_univ _,
    contDiffOn_const, (fun u _ => le_refl 0), rfl, isOpen_lt hcont continuous_const, ?_, ?_, ?_⟩
  · rw [Set.mem_ofPred_eq, hxsymm]; exact hx
  · intro z _
    exact Set.mem_univ _
  · intro z hzV hz
    have hsymm : (𝓡∂ n).symm z = ⟨z, hz⟩ :=
      modelWithCornersEuclideanHalfSpace_symm_apply_of_le hz
    have hzlt : Φ ⟨z, hz⟩ < 0 := by
      have h := hzV
      rw [Set.mem_ofPred_eq, hsymm] at h
      exact h
    exact ⟨fun _ => hz, fun _ => le_of_lt hzlt⟩

/-- **The epigraph description at a boundary zero.**  This is the half-space graph theorem
(`Work.PTGeometric.WeakRegion.exists_graph_halfSpace_cinf`) applied to the chart expression of `Φ` in
the *identity* chart of the half-space, which
`Work.PTGeometric.WeakRegion.modelData_boundaryZero_cinf` supplies (its conclusion is stated for
`extChartAt (𝓡∂ n) x`, which is the identity by `extChartAt_halfSpace_apply`). -/
theorem exists_epigraph_of_boundary_zero {n : ℕ} [NeZero n]
    (Φ : EuclideanHalfSpace n → ℝ)
    (hΦ : ContMDiff (modelWithCornersEuclideanHalfSpace n) (modelWithCornersSelf ℝ ℝ)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) Φ)
    {x : EuclideanHalfSpace n} (hxb : x.1 0 = 0) (hx0 : Φ x = 0)
    (hsign : ∀ᶠ y in 𝓝 x, y ∈ (modelWithCornersEuclideanHalfSpace n).boundary
      (EuclideanHalfSpace n) → 0 ≤ Φ y)
    (hone : ∃ (e : OpenPartialHomeomorph (EuclideanHalfSpace n) (EuclideanHalfSpace n)) (c : ℝ),
      e ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace n)
        (((⊤ : ℕ∞) : WithTop ℕ∞)) (EuclideanHalfSpace n) ∧
      x ∈ e.source ∧ c < 0 ∧
      (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (modelWithCornersEuclideanHalfSpace n).boundary
        (EuclideanHalfSpace n)) ∧
      mfderiv (modelWithCornersEuclideanHalfSpace n) (modelWithCornersSelf ℝ ℝ) Φ x
        = c • mfderiv (modelWithCornersEuclideanHalfSpace n) (modelWithCornersSelf ℝ ℝ)
            (fun y : EuclideanHalfSpace n => (e y).1 0) x) :
    ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (W V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen W ∧ tailVec x.1 ∈ W ∧
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) ψ W ∧
      (∀ u ∈ W, 0 ≤ ψ u) ∧ ψ (tailVec x.1) = 0 ∧
      IsOpen V ∧ x.1 ∈ V ∧ V ⊆ tailVec ⁻¹' W ∧
      (∀ (z : EuclideanSpace ℝ (Fin n)) (hzV : z ∈ V) (hz : 0 ≤ z.ofLp 0),
        (Φ ⟨z, hz⟩ ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0)) := by
  have hxb' : x ∈ (modelWithCornersEuclideanHalfSpace n).boundary (EuclideanHalfSpace n) :=
    (mem_boundary_halfSpace_iff n).mpr hxb
  obtain ⟨c, Ψ, hc, hagree, hp0, hC, hΨ0, hd, hsignΨ⟩ :=
    Work.PTGeometric.WeakRegion.modelData_boundaryZero_cinf (n := n) (A := EuclideanHalfSpace n)
      hΦ hxb' hx0 hsign hone
  obtain ⟨h, W, hWopen, hWmem, hWhsm, hWnn, hWh0, hep⟩ :=
    Work.PTGeometric.WeakRegion.exists_graph_halfSpace_cinf (n := n) Ψ
      ((extChartAt (modelWithCornersEuclideanHalfSpace n) x) x) hp0 hC hΨ0 c hc hd hsignΨ
  have hp_eq : (extChartAt (modelWithCornersEuclideanHalfSpace n) x) x = x.1 :=
    extChartAt_halfSpace_apply x x
  rw [hp_eq] at hWmem hWh0 hep
  have hagree' : ∀ (z : EuclideanSpace ℝ (Fin n)) (hz : 0 ≤ z.ofLp 0),
      Ψ z = Φ ⟨z, hz⟩ := by
    intro z hz
    have h1 := hagree ⟨z, hz⟩ (by rw [extChartAt_halfSpace_source]; exact Set.mem_univ _)
    rwa [extChartAt_halfSpace_apply] at h1
  rw [eventually_nhdsWithin_iff] at hep
  obtain ⟨V₀, hV₀sub, hV₀open, hV₀mem⟩ := mem_nhds_iff.mp hep
  refine ⟨h, W, V₀ ∩ tailVec ⁻¹' W, hWopen, hWmem, hWhsm, hWnn, hWh0,
    hV₀open.inter (hWopen.preimage continuous_tailVec), ⟨hV₀mem, hWmem⟩, (fun _ hz => hz.2), ?_⟩
  intro z hzV hz
  have hzI : z ∈ Set.range (modelWithCornersEuclideanHalfSpace n) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact hz
  have h1 := hV₀sub hzV.1 hzI
  rwa [hagree' z hz] at h1

/-! ## The target: the epigraph description at a boundary point of the source region -/

theorem exists_epigraph_at_boundaryPoint {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
      (Work.PTGeometric.sourceZeroSet G m hpow)
      (Work.PTGeometric.sourceBasepoint (D := D) (Fam := Fam) G m hpow))
    (x : EuclideanHalfSpace ((8 + k) + 1))
    (hx : Work.PTGeometric.sourcePhi G m hpow hphi x ≤ 0) (hxb : x.1 0 = 0) :
    ∃ (ψ : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → ℝ)
      (W V : Set (EuclideanSpace ℝ (Fin ((8 + k) + 1)))),
      IsOpen W ∧ Work.PTGeometric.tailVec x.1 ∈ W ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ W ∧
      (∀ u ∈ W, 0 ≤ ψ u) ∧ ψ (Work.PTGeometric.tailVec x.1) = 0 ∧
      IsOpen V ∧ x.1 ∈ V ∧ V ⊆ Work.PTGeometric.tailVec ⁻¹' W ∧
      (∀ (z : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (hzV : z ∈ V) (hz : 0 ≤ z.ofLp 0),
        (Work.PTGeometric.sourcePhi G m hpow hphi ⟨z, hz⟩ ≤ 0 ↔
          ψ (Work.PTGeometric.tailVec z) ≤ z.ofLp 0)) := by
  have hspec := Work.PTGeometric.sourcePhi_spec G m hpow hphi
  have hxb' : x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
      (EuclideanHalfSpace ((8 + k) + 1)) :=
    (Work.PTGeometric.mem_boundary_halfSpace_iff ((8 + k) + 1)).mpr hxb
  rcases eq_or_lt_of_le hx with hx0 | hxlt
  · exact exists_epigraph_of_boundary_zero (Work.PTGeometric.sourcePhi G m hpow hphi) hspec.1 hxb
      hx0 (hspec.2.2.2.2.2.2.2 x hxb' hx0) (hspec.2.2.2.2.2.2.1 x hxb' hx0)
  · exact exists_epigraph_of_neg (Work.PTGeometric.sourcePhi G m hpow hphi) hspec.1 hxlt

end

end Work.PTGeometric
