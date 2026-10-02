import Mathlib
import Submission.Work.ThomBordism.Transversality.Basic
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.setup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cut-off function `χ` for the transversality homotopy theorem

Given `F : M → E` transverse to the core on a neighbourhood `U` of `∂M`, step 1 of the proof of
`Work.ThomBordism.Transversality.TransversalApproximation` is a smooth function `χ : M → [0,1]`
which vanishes on a neighbourhood `V` of `∂M` (so that the homotopy is constant on `∂M` and the
transversality of `F` near `∂M` is inherited by `F'`) and is *positive* outside `U` (so that the
perturbation is active at every point where `F` is not transverse to the core).

The companion bump `β = β̂ ∘ Φ` on the target `E` (equal to `1` near `core = Φ ⁻¹' {0}` and
vanishing outside a small set of small `‖Φ‖`) is *not* constructed here; it is an easy consequence of
`exists_contMDiff_zero_iff_one_iff_of_isClosed` on `EuclideanSpace ℝ (Fin k)` and is needed only to
make the support of the perturbation compactly contained in the region where `Φ` is a submersion.
-/

open scoped Manifold ContDiff MeasureTheory
open Function Set Topology Manifold Filter MeasureTheory

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

/-- **The cut-off function.**  If `U` is an open set containing the boundary of a compact `T2`
manifold `M`, there is a smooth `χ : M → [0,1]` vanishing on a neighbourhood of `∂M` and positive
outside `U`. -/
theorem exists_contMDiff_vanishingNearBoundary_pos_off
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] [T2Space M]
    {U : Set M} (hU : IsOpen U) (hUbd : I.boundary M ⊆ U) :
    ∃ χ : M → ℝ, ContMDiff I (𝓘(ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ x, 0 ≤ χ x) ∧
      (∀ x, χ x ≤ 1) ∧
      (∃ V : Set M, IsOpen V ∧ I.boundary M ⊆ V ∧ ∀ x ∈ V, χ x = 0) ∧
      (∀ x, x ∉ U → 0 < χ x) := by
  classical
  haveI : NormalSpace M := inferInstance
  have hbdclosed : IsClosed (I.boundary M) :=
    I.isClosed_boundary (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  obtain ⟨u, huopen, hbdu, hucl⟩ := normal_exists_closure_subset hbdclosed hU hUbd
  obtain ⟨χ, hχ, hrange, hC, -⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (M := M) I
      (isClosed_closure (s := u)) (isClosed_empty : IsClosed (∅ : Set M))
      (show Disjoint (closure u) (∅ : Set M) by simp) (n := (⊤ : ℕ∞))
  refine ⟨χ, hχ, fun x => (hrange (Set.mem_range_self x)).1, fun x => (hrange (Set.mem_range_self x)).2,
    ⟨u, huopen, hbdu, by intro x hx; rw [← hC x]; exact subset_closure hx⟩, ?_⟩
  intro x hx
  have hxnotC : x ∉ closure u := fun hxc => hx (hucl hxc)
  have hne : χ x ≠ 0 := fun h0 => hxnotC (by rw [← hC x] at h0; exact h0)
  exact lt_of_le_of_ne ((hrange (Set.mem_range_self x)).1) (Ne.symm hne)

variable {n k : ℕ}

/-- **The bump `β = β̂ ∘ Φ` used to localise the perturbation near the core.**  For `δ > 0` there is
a smooth `β : E → [0,1]` which equals `1` on `{y : ‖Φ y‖ ≤ δ/4}` (in particular on the core
`X.core`) and vanishes on `{y : δ/3 ≤ ‖Φ y‖}`.  Multiplying the cut-off `χ` of
`exists_contMDiff_vanishingNearBoundary_pos_off` by `β ∘ F` therefore produces a perturbation
supported over the compact set `F (supp χ) ∩ {‖Φ‖ ≤ δ/3}`, which lies in the open region where `Φ`
is a submersion as soon as `δ` is small enough. -/
theorem exists_beta (X : CoreTarget n k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ β : X.E → ℝ, ContMDiff (𝓡 n) (𝓘(ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ (∀ y, 0 ≤ β y) ∧
      (∀ y, β y ≤ 1) ∧ (∀ y, ‖X.Φ y‖ ≤ δ / 4 → β y = 1) ∧ (∀ y, δ / 3 ≤ ‖X.Φ y‖ → β y = 0) := by
  classical
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin k)) :=
    ⟨δ / 4, δ / 3, by linarith, by linarith⟩
  refine ⟨fun y => b (X.Φ y), ?_, ?_, ?_, ?_, ?_⟩
  · have hb : ContMDiff (𝓡 k) (𝓘(ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) b :=
      contMDiff_iff_contDiff.mpr (b.contDiff (n := (⊤ : ℕ∞)))
    exact hb.comp X.contMDiff_Φ
  · exact fun y => b.nonneg
  · exact fun y => b.le_one
  · intro y hy
    refine b.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hy
  · intro y hy
    refine b.zero_of_le_dist ?_
    rw [dist_eq_norm, sub_zero]
    exact hy

end

end Work.ThomBordism.Transversality.TransversalApproximation
