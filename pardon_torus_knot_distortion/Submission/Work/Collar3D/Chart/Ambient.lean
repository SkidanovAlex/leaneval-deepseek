import Submission.Work.Collar3D.Chart.Equiv
import Submission.Work.Collar3D.Chart.chartToFun_continuous
import Submission.Work.Collar3D.Chart.chartToFun_family_continuous
import Submission.Work.Collar3D.Isotopy

/-!
# Extending a chart-supported move to the ambient space

Given a chart `Φ : U ≃ₜ M` of `ℝ³` and a homeomorphism `g` of the model which is the identity
outside a set `S` whose `Φ`-preimage is closed in `ℝ³`, the move `Φ.symm ∘ g ∘ Φ`, extended by the
identity outside `U`, is a homeomorphism of `ℝ³` supported in the chart:

* `Work.Collar3D.ambientOfChart` — the ambient homeomorphism, with its API
  `ambientOfChart_apply_of_mem`, `ambientOfChart_apply_of_notMem`,
  `ambientOfChart_eq_self_of_notMem_support`;
* `Work.Collar3D.ambientIsotopyOfChart` — the ambient *isotopy* extending a continuous family of
  such moves: **isotopy extension for a move of a chart**, with the support in the chart.

The special case in which `S` is compact is the one used by the collar computations
(`chartSupport_isCompact`), and is recorded as `chartSupport_isClosed` and the corollaries
`ambientOfChart_of_isCompact`, `ambientIsotopyOfChart_of_isCompact`.

This is the machinery that turns a move of the collar model `S¹ × ℝ × ℝ` (a slide, a push-off, a
side swap) into a move of `ℝ³`.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

variable {M : Type*} [TopologicalSpace M]

/-! ## The inverse continuity, from the forward one -/

/-- **Continuity of the inverse of the chart-supported extension**: `chartInvFun U Φ g` is
literally `chartToFun U Φ g.symm`, and `g.symm` also fixes the complement of `S` pointwise. -/
theorem chartInvFun_continuous (U : Set R3) (hU : IsOpen U) (Φ : U ≃ₜ M) (g : M ≃ₜ M)
    {S : Set M} (hS : IsClosed (chartSupport U Φ S)) (hg : ∀ y : M, y ∉ S → g y = y) :
    Continuous (chartInvFun U Φ g) := by
  have h : chartInvFun U Φ g = chartToFun U Φ g.symm := rfl
  rw [h]
  exact Work.Collar3D.Chart.chartToFun_continuous U hU Φ g.symm hS (fun y hy => by
    calc g.symm y = g.symm (g y) := by rw [hg y hy]
      _ = y := Homeomorph.symm_apply_apply g y)

/-- **Joint continuity of the inverse of a chart-supported family of extensions**, from
`Work.Collar3D.Chart.chartToFun_family_continuous`. -/
theorem chartInvFun_family_continuous (U : Set R3) (hU : IsOpen U) (Φ : U ≃ₜ M)
    (g : ℝ → M ≃ₜ M) {S : Set M} (hS : IsClosed (chartSupport U Φ S))
    (hg : ∀ (t : ℝ) (y : M), y ∉ S → g t y = y)
    (hcont : Continuous fun p : ℝ × M => (g p.1).symm p.2) :
    Continuous (fun p : ℝ × R3 => chartInvFun U Φ (g p.1) p.2) := by
  have h : (fun p : ℝ × R3 => chartInvFun U Φ (g p.1) p.2) =
      (fun p : ℝ × R3 => chartToFun U Φ ((g p.1).symm) p.2) := rfl
  rw [h]
  exact Work.Collar3D.Chart.chartToFun_family_continuous U hU Φ (fun t => (g t).symm) hS
    (fun t y hy => by
      calc (g t).symm y = (g t).symm (g t y) := by rw [hg t y hy]
        _ = y := Homeomorph.symm_apply_apply (g t) y)
    hcont

/-- The compact-support corollary of `Work.Collar3D.chartSupport_isCompact`. -/
theorem chartSupport_isClosed (U : Set R3) (Φ : U ≃ₜ M) {K : Set M} (hK : IsCompact K) :
    IsClosed (chartSupport U Φ K) :=
  (chartSupport_isCompact U Φ hK).isClosed

/-! ## The ambient homeomorphism -/

/-- **The extension of a chart-supported homeomorphism to an ambient homeomorphism of `ℝ³`.**  It
agrees with `Φ.symm ∘ g ∘ Φ` on the chart and is the identity outside it, hence is supported in
the chart. -/
def ambientOfChart (U : Set R3) (hU : IsOpen U) (Φ : U ≃ₜ M) (g : M ≃ₜ M) {S : Set M}
    (hS : IsClosed (chartSupport U Φ S)) (hg : ∀ y : M, y ∉ S → g y = y) : R3 ≃ₜ R3 where
  toFun := chartToFun U Φ g
  invFun := chartInvFun U Φ g
  left_inv := chartInvFun_chartToFun U Φ g
  right_inv := chartToFun_chartInvFun U Φ g
  continuous_toFun := Work.Collar3D.Chart.chartToFun_continuous U hU Φ g hS hg
  continuous_invFun := chartInvFun_continuous U hU Φ g hS hg

theorem ambientOfChart_apply_of_mem (U : Set R3) (hU : IsOpen U) (Φ : U ≃ₜ M) (g : M ≃ₜ M)
    {S : Set M} (hS : IsClosed (chartSupport U Φ S)) (hg : ∀ y : M, y ∉ S → g y = y) {x : R3}
    (hx : x ∈ U) :
    ambientOfChart U hU Φ g hS hg x = (Φ.symm (g (Φ ⟨x, hx⟩)) : R3) :=
  chartToFun_of_mem hx

theorem ambientOfChart_apply_of_notMem (U : Set R3) (hU : IsOpen U) (Φ : U ≃ₜ M) (g : M ≃ₜ M)
    {S : Set M} (hS : IsClosed (chartSupport U Φ S)) (hg : ∀ y : M, y ∉ S → g y = y) {x : R3}
    (hx : x ∉ U) : ambientOfChart U hU Φ g hS hg x = x :=
  chartToFun_of_notMem hx

/-- **The ambient homeomorphism is the identity outside the support** of the model move. -/
theorem ambientOfChart_eq_self_of_notMem_support (U : Set R3) (hU : IsOpen U) (Φ : U ≃ₜ M)
    (g : M ≃ₜ M) {S : Set M} (hS : IsClosed (chartSupport U Φ S))
    (hg : ∀ y : M, y ∉ S → g y = y) {x : R3} (hx : x ∉ chartSupport U Φ S) :
    ambientOfChart U hU Φ g hS hg x = x :=
  chartToFun_eq_self_of_notMem_support U Φ hg hx

/-- The compact-support form: a chart-supported homeomorphism whose model move is the identity
outside a *compact* set extends. -/
def ambientOfChart_of_isCompact (U : Set R3) (hU : IsOpen U) (Φ : U ≃ₜ M) (g : M ≃ₜ M)
    {K : Set M} (hK : IsCompact K) (hg : ∀ y : M, y ∉ K → g y = y) : R3 ≃ₜ R3 :=
  ambientOfChart U hU Φ g (chartSupport_isClosed U Φ hK) hg

/-! ## The ambient isotopy (isotopy extension for a chart move) -/

/-- **Isotopy extension for a move of a chart**: a continuous family of homeomorphisms of the model,
each fixing the complement of `S` pointwise (with `S` a fixed set whose `Φ`-preimage is closed),
extends to an ambient isotopy of `ℝ³` supported in the chart `U`, by the identity outside `U`. -/
def ambientIsotopyOfChart (U : Set R3) (hU : IsOpen U) (Φ : U ≃ₜ M) (g : ℝ → M ≃ₜ M)
    {S : Set M} (hS : IsClosed (chartSupport U Φ S))
    (hg : ∀ (t : ℝ) (y : M), y ∉ S → g t y = y)
    (hcont : Continuous fun p : ℝ × M => g p.1 p.2)
    (hcont_inv : Continuous fun p : ℝ × M => (g p.1).symm p.2) : AmbientIsotopy where
  toHomeomorph := fun t => ambientOfChart U hU Φ (g t) hS (hg t)
  continuous_toFun := by
    refine (Work.Collar3D.Chart.chartToFun_family_continuous U hU Φ g hS hg hcont).congr
      (fun p => ?_)
    rfl
  continuous_invFun := by
    refine (chartInvFun_family_continuous U hU Φ g hS hg hcont_inv).congr (fun p => ?_)
    rfl

@[simp] theorem ambientIsotopyOfChart_apply (U : Set R3) (hU : IsOpen U) (Φ : U ≃ₜ M)
    (g : ℝ → M ≃ₜ M) {S : Set M} (hS : IsClosed (chartSupport U Φ S))
    (hg : ∀ (t : ℝ) (y : M), y ∉ S → g t y = y)
    (hcont : Continuous fun p : ℝ × M => g p.1 p.2)
    (hcont_inv : Continuous fun p : ℝ × M => (g p.1).symm p.2) (t : ℝ) (x : R3) :
    ambientIsotopyOfChart U hU Φ g hS hg hcont hcont_inv t x =
      chartToFun U Φ (g t) x := rfl

end

end Work.Collar3D
