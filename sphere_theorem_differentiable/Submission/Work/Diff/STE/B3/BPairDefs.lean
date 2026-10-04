import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the vocabulary of the adjunction `BPair (Rstar i u) k = CPair i u (R i k)`

This file collects the definitions and the elementary "where does the junk live" facts that the
proof of the B3 adjunction `Work.Diff.STE.B3.BPair_Rstar` needs:

* `sigmaBall D i`, `sigmaClosedBall D i`: the open/closed flat balls of radius `D.σ i`;
* `overlapSet D i j`: the set of flat `i`-coordinates in which *both* charts `i` and `j` are genuine
  (`χ i ≠ 0` and `ζ j (pt i ·) ≠ 0`);
* `transMap D i j`: the chart transition `y ↦ coord j (pt i y)`, i.e. `z = T y`;
* `Phi D i u k p`: the intrinsic contraction `Σ_ab (Rstar i u p) (eᵢa) (eᵢb) · k p (eᵢa) (eᵢb)` of
  `Rstar i u` against `k`, read in the frame of chart `i`.

The mathematical content of the adjunction is that `Phi`, transported with the correct Jacobians,
is the `L²` density of `CPair i u (R i k)`.

## The junk facts

`extChartAt`/`(extChartAt _).symm` are completely arbitrary off `source`/`target`, so every
computation must first localise to where the maps are genuine.  The two decisive observations are

* `D.psi j z ≠ 0 → flatToE (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target` — because `ψ j = χ j · ζ j ∘ pt j`
  and `hχtsup` says the *topological* support of `χ j` lies in the chart target;
* hence on the support of `ψ j` the chart `j` is genuine, `coord j (pt j z) = z`, and `‖z‖ < σ j`
  (from `hζsupp`); in particular the frames are orthonormal there and the localised components
  `R j F a b` live in the closed `σ j`-ball.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The open flat ball of radius `D.σ i`: the region in the flat coordinates of chart `i` on which
the chart is genuine and the frame `e i` is `g₀`-orthonormal. -/
def sigmaBall (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | ‖z‖ < D.σ i}

/-- The closed flat ball of radius `D.σ i`. -/
def sigmaClosedBall (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | ‖z‖ ≤ D.σ i}

/-- The set of flat `i`-coordinates on which the charts `i` and `j` are *both* genuine: `χ i ≠ 0`
(so the flat coordinate is the chart `i` coordinate of `pt i y`) and `ζ j (pt i y) ≠ 0` (so `pt i y`
lies in the chart `j` source).  This is the domain of the chart transition `transMap D i j`. -/
def overlapSet (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {y | ‖y‖ < D.σ i ∧ D.ζ j (D.pt i y) ≠ 0}

/-- The chart transition in flat coordinates: `z = T y = coord j (pt i y)`. -/
def transMap (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (y : Fin (Module.finrank ℝ E) → ℝ) : Fin (Module.finrank ℝ E) → ℝ :=
  coord (I := I) (D.x₀ j) (D.pt i y)

/-- The intrinsic contraction of `Rstar i u` against `k` at `p`, read in the (orthonormal, where it
matters) frame `e i`.  By frame independence this is independent of the orthonormal frame chosen at
`p`; it vanishes identically off the support of `ζ i`. -/
def Phi (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Bil (I := I) (M := M)) (p : M) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    D.Rstar i u p (D.e i a p) (D.e i b p) * k p (D.e i a p) (D.e i b p)

variable (D : B3Data (I := I) (M := M) ι₀ g₀)

@[simp] lemma mem_sigmaBall {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ} :
    z ∈ sigmaBall D i ↔ ‖z‖ < D.σ i := Iff.rfl

@[simp] lemma mem_sigmaClosedBall {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ} :
    z ∈ sigmaClosedBall D i ↔ ‖z‖ ≤ D.σ i := Iff.rfl

/-- A point of the topological support of `χ i` has flat coordinate in the chart target. -/
lemma flatToE_mem_target_of_chi {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.χ i z ≠ 0) :
    flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
  D.hχtsup i z (subset_closure h)

/-- **Where the localised weight lives.**  If `ψ i z ≠ 0` then the flat coordinate `z` lies in the
chart target of `x₀ i`. -/
lemma target_of_psi_ne_zero {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.psi i z ≠ 0) :
    flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
  flatToE_mem_target_of_chi D (fun h0 => h (by simp only [B3Data.psi, h0, zero_mul]))

/-- On the support of `ψ i`, the chart at `x₀ i` evaluates `pt i z` to the flat coordinate `z`. -/
lemma extChartAt_pt_of_psi_ne_zero {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.psi i z ≠ 0) :
    (extChartAt I (D.x₀ i)) (D.pt i z) = flatToE (I := I) (D.x₀ i) z :=
  (extChartAt I (D.x₀ i)).right_inv (target_of_psi_ne_zero D h)

/-- On the support of `ψ i`, the flat coordinate of `pt i z` is `z`. -/
lemma coord_pt_of_psi_ne_zero {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.psi i z ≠ 0) :
    coord (I := I) (D.x₀ i) (D.pt i z) = z := by
  have hL : (Module.finBasis ℝ E).equivFun (flatToE (I := I) (D.x₀ i) z)
      = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z := by
    simp only [flatToE]
    rw [LinearEquiv.apply_symm_apply]
  simp only [coord, extChartAt_pt_of_psi_ne_zero D h, hL, add_sub_cancel_left]

/-- On the support of `ψ i`, the flat coordinate has norm less than `σ i`. -/
lemma norm_lt_sigma_of_psi_ne_zero {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.psi i z ≠ 0) : ‖z‖ < D.σ i := by
  have hζ : D.ζ i (D.pt i z) ≠ 0 := fun h0 => h (by simp only [B3Data.psi, h0, mul_zero])
  rw [← coord_pt_of_psi_ne_zero D h]
  exact (D.hζsupp i _ hζ).2

/-- On the support of `ψ i`, the cut-off `χ i` equals one. -/
lemma chi_eq_one_of_psi_ne_zero {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.psi i z ≠ 0) : D.χ i z = 1 :=
  D.hχ1 i z (le_of_lt (norm_lt_sigma_of_psi_ne_zero D h))

/-- On the support of `ψ i`, the frame `e i` is `g₀`-orthonormal at `pt i z`. -/
lemma isONFrame_of_psi_ne_zero {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.psi i z ≠ 0) :
    IsONFrame g₀ (D.pt i z) (fun a => D.e i a (D.pt i z)) :=
  D.heON i z (by have := norm_lt_sigma_of_psi_ne_zero D h; have := D.hσ i; linarith)

/-- On the support of `ψ i`, the weight `ζ i` does not vanish at `pt i z`. -/
lemma zeta_ne_zero_of_psi_ne_zero {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.psi i z ≠ 0) : D.ζ i (D.pt i z) ≠ 0 :=
  fun h0 => h (by simp only [B3Data.psi, h0, mul_zero])

/-- On the support of `ψ i`, the localised weight is the normalised weight at `pt i z`. -/
lemma psi_eq_zeta_of_psi_ne_zero {i : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.psi i z ≠ 0) : D.psi i z = D.ζ i (D.pt i z) := by
  rw [B3Data.psi, chi_eq_one_of_psi_ne_zero D h, one_mul]

/-- `Rstar i u` vanishes identically off the support of `ζ i`: every coefficient of the frame
expansion carries the factor `ζ i p`. -/
lemma Rstar_eq_zero_of_zeta_eq_zero {i : ι₀}
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    {p : M} (h : D.ζ i p = 0) : D.Rstar i u p = 0 := by
  ext X Y
  simp only [B3Data.Rstar, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, h, zero_mul, Finset.sum_const_zero, Pi.zero_apply]
  simp

/-- The intrinsic contraction vanishes off the support of `ζ i`. -/
lemma Phi_eq_zero_of_zeta_eq_zero {i : ι₀}
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Bil (I := I) (M := M)) {p : M} (h : D.ζ i p = 0) : Phi D i u k p = 0 := by
  have hR : D.Rstar i u p = 0 := Rstar_eq_zero_of_zeta_eq_zero D u h
  simp [Phi, hR]

/-- The intrinsic contraction is the contraction of `Rstar i u` against `k` in *any* orthonormal
frame at `p` (when the frame `e i` is orthonormal there). -/
lemma Phi_eq_sum_of_isONFrame {i : ι₀}
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Bil (I := I) (M := M)) {p : M}
    (hON : IsONFrame g₀ p (fun a => D.e i a p)) :
    Phi D i u k p = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      D.Rstar i u p (D.e i a p) (D.e i b p) * k p (D.e i a p) (D.e i b p) := rfl

/-- A point of the `σ j`-ball of the chart `j` lies in the cut-off support of `χ j`. -/
lemma chi_ne_zero_of_norm_le_sigma {j : ι₀} {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : ‖z‖ ≤ D.σ j) : D.χ j z ≠ 0 := by
  rw [D.hχ1 j z h]
  exact one_ne_zero

end Work.Diff.STE.B3
