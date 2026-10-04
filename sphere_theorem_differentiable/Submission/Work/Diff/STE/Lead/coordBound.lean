import Mathlib
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.psi.abs_coord_factor_le
import Submission.Work.Diff.STE.D.psi.JetAffine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform geometry on the compact region `Ky D i` (Lead layer, STE)

Helper lemmas, extracted from `Submission/Work/Diff/STE/Lead/deTurck_bound.lean` so that they are
available without the (still incomplete) main theorem of that file.

* `coordCLM_cFrame`: the coordinate functional `coordCLM x₀ x j` reads the coefficient of a vector
  in the coordinate frame of the chart at `x₀`.
* `coord_factor_uniform`: on the compact region `Ky D i` the coordinates of the
  `g₀`-orthonormal frame vectors in the coordinate frame are uniformly bounded.
* `flatToE_coord`: the flat coordinate of a point of the chart source, transported back to the
  model space, is its chart coordinate.
* `coordCLM_bound`: the coordinate functionals are uniformly equivalent to the `g₀`-norm on
  `Ky D i`.
* `gmat_qform_lower`: the uniform positive lower bound for the quadratic form of the Gram matrix of
  the coordinate frame on `Ky D i`.
-/

namespace Work.Diff.STE.Lead

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The three jet bounds for the chart matrix in the coordinate frame**: the value, the first and
the second spatial Fréchet derivative of the `(a,b)`-entry of the chart matrix of a section `h` in
the chart at `x₀ i`, read in the model space `E`, are all bounded by `C √(BNorm k h) / c ^ 3` at
every point `flatToE z` of the `σ i`-ball where the localised weight is at least `c > 0`. -/
def ChartJetBound (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (C : ℝ) : Prop :=
  ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) (c : ℝ),
    ‖z‖ ≤ D.σ i → 0 < c → c ≤ D.psi i z →
    (|Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) a b| ≤ C * Real.sqrt (D.BNorm k h) / c ^ 3)
  ∧ (∀ p : Fin (Module.finrank ℝ E),
      |(fderiv ℝ (fun y : E => (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y) a b)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) (Work.Diff.EXT.bB (E := E) p)|
        ≤ C * Real.sqrt (D.BNorm k h) / c ^ 3)
  ∧ (∀ p q : Fin (Module.finrank ℝ E),
      |(fderiv ℝ (fun y : E => (fderiv ℝ (fun y' : E =>
          (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y') a b) y))
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
          (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|
        ≤ C * Real.sqrt (D.BNorm k h) / c ^ 3)

/-- The coordinate functional `coordCLM (x₀ i) x j` reads the coordinate of a vector in the
coordinate frame: `coordCLM (x₀ i) x j (frameVector x₀ x (bB a)) = δ_{ja}`. -/
lemma coordCLM_cFrame (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (j a : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.D.coordCLM (I := I) (M := M) x₀ x j
        (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) a))
      = if j = a then 1 else 0 := by
  have h1 : Work.Diff.STE.D.coordCLM (I := I) (M := M) x₀ x j
      (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) a))
      = (Work.Diff.EXT.bB (E := E)).coord j (Work.Diff.EXT.bB (E := E) a) := by
    rw [Work.Diff.STE.D.coordCLM_apply]
    have h2 : Work.Diff.STE.D.chartCoordOf (I := I) (M := M) x₀ x
        (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) a))
        = Work.Diff.EXT.bB (E := E) a := by
      rw [Work.Diff.STE.D.chartCoordOf, Submission.Geodesic.frameVector]
      exact Bundle.Trivialization.continuousLinearMapAt_symmL (R := ℝ)
        (trivializationAt E (TangentSpace I) x₀) hx (Work.Diff.EXT.bB (E := E) a)
    rw [h2]
  rw [h1]
  have h3 : (Work.Diff.EXT.bB (E := E)).coord j (Work.Diff.EXT.bB (E := E) a)
      = if j = a then 1 else 0 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : j = a
    · subst h
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, h]
  exact h3

/-- **Uniform bound for the coordinates of the orthonormal frame in the coordinate frame.** -/
theorem coord_factor_uniform (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ (i : ι₀) (a : Fin (Module.finrank ℝ E))
      (y : Fin (Module.finrank ℝ E) → ℝ), y ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i →
      ∀ j : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))| ≤ B₀ := by
  classical
  have h : ∀ (i : ι₀) (a : Fin (Module.finrank ℝ E)), ∃ B : ℝ, 0 ≤ B ∧
      ∀ y ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i, ∀ j : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))| ≤ B :=
    fun i a => Work.Diff.STE.D.psi.abs_coord_factor_le (I := I) (M := M) D i a
  choose Bf hBf using h
  refine ⟨(∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), Bf i a) + 1,
    add_nonneg (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun a _ => (hBf i a).1) zero_le_one,
    fun i a y hy j => ?_⟩
  have h1 : Bf i a ≤ ∑ i' : ι₀, ∑ a' : Fin (Module.finrank ℝ E), Bf i' a' := by
    have h2 : Bf i a ≤ ∑ a' : Fin (Module.finrank ℝ E), Bf i a' :=
      Finset.single_le_sum (fun a' _ => (hBf i a').1) (Finset.mem_univ a)
    exact le_trans h2 (Finset.single_le_sum
      (fun i' _ => Finset.sum_nonneg fun a' _ => (hBf i' a').1) (Finset.mem_univ i))
  linarith [(hBf i a).2 y hy j, h1]

/-- The flat coordinate of a point of the chart source, transported back to the model space, is its
chart coordinate. -/
lemma flatToE_coord (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {i : ι₀} {x : M}
    (hx : x ∈ (extChartAt I (D.x₀ i)).source) :
    Work.Diff.STE.flatToE (I := I) (D.x₀ i) (coord (I := I) (D.x₀ i) x)
      = (extChartAt I (D.x₀ i)) x := by
  have harg : (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i))
      + ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) x)
        - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)))
      = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) x) := by abel
  simp only [Work.Diff.STE.flatToE, coord]
  rw [harg, LinearEquiv.symm_apply_apply]

/-- **The coordinate functionals are uniformly equivalent to the `g₀`-norm** on the region
`Ky D i`: the coordinates of a tangent vector are bounded by a constant times its `g₀`-length. -/
theorem coordCLM_bound (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (B₀ : ℝ)
    (hB₀_nn : 0 ≤ B₀)
    (hB₀ : ∀ (i : ι₀) (a : Fin (Module.finrank ℝ E))
      (y : Fin (Module.finrank ℝ E) → ℝ), y ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i →
      ∀ j : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))| ≤ B₀)
    (i : ι₀) {x : M} (hx : x ∈ (extChartAt I (D.x₀ i)).source)
    (hON : IsONFrame g₀ x (fun a => D.e i a x))
    (hKy : coord (I := I) (D.x₀ i) x ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i)
    (u : TangentSpace I x) (j : Fin (Module.finrank ℝ E)) :
    |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j u|
      ≤ B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u) := by
  have hu : u = ∑ a, g₀.inner x u (D.e i a x) • D.e i a x :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ x (fun a => D.e i a x) hON u).symm
  have h1 : Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j u
      = ∑ a, g₀.inner x u (D.e i a x)
          * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j (D.e i a x) := by
    conv_lhs => rw [hu]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul]
  have hcoe : ∀ a, |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j (D.e i a x)| ≤ B₀ := by
    intro a
    rw [← D.pt_coord i hx]
    exact hB₀ i a (coord (I := I) (D.x₀ i) x) hKy j
  rw [h1]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h2 : ∀ a : Fin (Module.finrank ℝ E),
      |g₀.inner x u (D.e i a x)
        * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j (D.e i a x)|
      ≤ B₀ * |g₀.inner x u (D.e i a x)| := by
    intro a
    rw [abs_mul]
    calc |g₀.inner x u (D.e i a x)|
          * |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j (D.e i a x)|
        ≤ |g₀.inner x u (D.e i a x)| * B₀ :=
          mul_le_mul_of_nonneg_left (hcoe a) (abs_nonneg _)
      _ = B₀ * |g₀.inner x u (D.e i a x)| := by ring
  calc ∑ a, |g₀.inner x u (D.e i a x)
          * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x j (D.e i a x)|
      ≤ ∑ a, B₀ * |g₀.inner x u (D.e i a x)| := Finset.sum_le_sum fun a _ => h2 a
    _ = B₀ * ∑ a, |g₀.inner x u (D.e i a x)| := by rw [Finset.mul_sum]
    _ ≤ B₀ * (Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u)) :=
        mul_le_mul_of_nonneg_left (D.sum_abs_inner_le i hON u) hB₀_nn
    _ = B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u) := by ring

/-- **The uniform positive lower bound for the quadratic form of the Gram matrix of the coordinate
frame** (of the fixed background metric `g₀`) on the region `Ky D i`. -/
theorem gmat_qform_lower (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (B₀ : ℝ)
    (hB₀_nn : 0 ≤ B₀)
    (hB₀ : ∀ (i : ι₀) (a : Fin (Module.finrank ℝ E))
      (y : Fin (Module.finrank ℝ E) → ℝ), y ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i →
      ∀ j : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))| ≤ B₀)
    (i : ι₀) {x : M} (hx : x ∈ (extChartAt I (D.x₀ i)).source)
    (hON : IsONFrame g₀ x (fun a => D.e i a x))
    (hKy : coord (I := I) (D.x₀ i) x ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i) :
    ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      (1 / (((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (B₀ + 1) ^ 2)) * ∑ a, (ξ a) ^ 2
        ≤ ∑ a, ∑ b, (Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)
            ((extChartAt I (D.x₀ i)) x) a b) * ξ a * ξ b := by
  intro ξ
  set w : TangentSpace I x := ∑ a, ξ a
    • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a) with hw
  -- the coordinates of `w` are the `ξ`
  have hbx : x ∈ (trivializationAt E (TangentSpace I) (D.x₀ i)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    rw [extChartAt_source] at hx
    exact hx
  have hcoeff : ∀ b, Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x b w = ξ b := by
    intro b
    have h1 : Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) x b w
        = ∑ a, ξ a * (if b = a then 1 else 0) := by
      rw [hw, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, smul_eq_mul, coordCLM_cFrame (I := I) (M := M) (D.x₀ i) hbx b a]
    rw [h1, Finset.sum_eq_single b]
    · simp
    · intro a _ ha
      rw [if_neg (fun h : b = a => ha h.symm), mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  have hnn : 0 ≤ g₀.inner x w w := by
    rcases eq_or_ne w 0 with h | h
    · rw [h]; simp
    · exact (g₀.pos x w h).le
  -- the coordinates of `w` are bounded by `B₀ √n ‖w‖`
  have hbd : ∀ a, |ξ a| ≤ B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x w w) := by
    intro a
    rw [← hcoeff a]
    exact coordCLM_bound (I := I) (M := M) D B₀ hB₀_nn hB₀ i hx hON hKy w a
  have hC : 0 ≤ B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg (mul_nonneg hB₀_nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hsq_bound : ∑ a, (ξ a) ^ 2
      ≤ (Module.finrank ℝ E : ℝ) * (B₀ * Real.sqrt (Module.finrank ℝ E)) ^ 2
          * g₀.inner x w w := by
    have h : ∑ a, (ξ a) ^ 2 ≤ ∑ _a : Fin (Module.finrank ℝ E),
        (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x w w)) ^ 2 := by
      refine Finset.sum_le_sum fun a _ => ?_
      rw [sq_le_sq, abs_of_nonneg hC]
      exact hbd a
    calc ∑ a, (ξ a) ^ 2 ≤ ∑ _a : Fin (Module.finrank ℝ E),
          (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x w w)) ^ 2 := h
      _ = (Module.finrank ℝ E : ℝ)
          * (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x w w)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (Module.finrank ℝ E : ℝ) * (B₀ * Real.sqrt (Module.finrank ℝ E)) ^ 2
          * g₀.inner x w w := by
          rw [mul_pow, Real.sq_sqrt hnn]
          ring
  -- bilinearity: `g₀(w,w)` is the quadratic form of the Gram matrix of the coordinate frame
  have hAcoef : ∀ a b : Fin (Module.finrank ℝ E),
      Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)
          ((extChartAt I (D.x₀ i)) x) a b
        = g₀.inner x
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
    intro a b
    rw [Work.Diff.STE.D.chartMatOf_apply, (extChartAt I (D.x₀ i)).left_inv hx]
  have hbil : g₀.inner x w w = ∑ a, ∑ b,
      (Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)
        ((extChartAt I (D.x₀ i)) x) a b) * ξ a * ξ b := by
    have h1 : g₀.inner x w w = ∑ a, ∑ b, ξ a * ξ b *
        g₀.inner x
          (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
          (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
      have e1 : ∀ a b : Fin (Module.finrank ℝ E),
          (g₀.inner x)
            (ξ a • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
            (ξ b • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b))
          = ξ a * ξ b * g₀.inner x
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
        intro a b
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      calc g₀.inner x w w
          = ∑ a, (g₀.inner x)
              (ξ a • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a)) w := by
            rw [hw]
            simp only [map_sum, sum_apply]
            rw [Finset.sum_comm]
        _ = ∑ a, ∑ b, (g₀.inner x)
              (ξ a • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
              (ξ b • Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hw]
            simp only [map_sum]
        _ = ∑ a, ∑ b, ξ a * ξ b * g₀.inner x
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) a))
              (Submission.Geodesic.frameVector (I := I) (D.x₀ i) x (Work.Diff.EXT.bB (E := E) b)) := by
            exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e1 a b
    rw [h1]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hAcoef a b]
    ring
  rw [← hbil]
  -- arithmetic
  have hq : (1 / (((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (B₀ + 1) ^ 2))
      * ((Module.finrank ℝ E : ℝ) * (B₀ * Real.sqrt (Module.finrank ℝ E)) ^ 2) ≤ 1 := by
    have hn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hs : (Real.sqrt (Module.finrank ℝ E)) ^ 2 = (Module.finrank ℝ E : ℝ) :=
      Real.sq_sqrt hn
    have hden : 0 < ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (B₀ + 1) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_one hden, one_mul]
    have h1 : (Module.finrank ℝ E : ℝ) ≤ (Module.finrank ℝ E : ℝ) + 1 := by linarith
    have h2 : B₀ ≤ B₀ + 1 := by linarith
    have h3 : (Module.finrank ℝ E : ℝ) * B₀
        ≤ ((Module.finrank ℝ E : ℝ) + 1) * (B₀ + 1) :=
      mul_le_mul h1 h2 hB₀_nn (by positivity)
    have h4 : 0 ≤ (Module.finrank ℝ E : ℝ) * B₀ := mul_nonneg hn hB₀_nn
    calc (Module.finrank ℝ E : ℝ) * (B₀ * Real.sqrt (Module.finrank ℝ E)) ^ 2
        = ((Module.finrank ℝ E : ℝ) * B₀) ^ 2 := by rw [mul_pow, hs]; ring
      _ ≤ (((Module.finrank ℝ E : ℝ) + 1) * (B₀ + 1)) ^ 2 := pow_le_pow_left₀ h4 h3 2
      _ = ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (B₀ + 1) ^ 2 := by rw [mul_pow]
  calc (1 / (((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (B₀ + 1) ^ 2)) * ∑ a, (ξ a) ^ 2
      ≤ (1 / (((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (B₀ + 1) ^ 2))
          * ((Module.finrank ℝ E : ℝ) * (B₀ * Real.sqrt (Module.finrank ℝ E)) ^ 2
              * g₀.inner x w w) :=
        mul_le_mul_of_nonneg_left hsq_bound (by positivity)
    _ = ((1 / (((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (B₀ + 1) ^ 2))
          * ((Module.finrank ℝ E : ℝ) * (B₀ * Real.sqrt (Module.finrank ℝ E)) ^ 2))
          * g₀.inner x w w := by ring
    _ ≤ 1 * g₀.inner x w w := mul_le_mul_of_nonneg_right hq hnn
    _ = g₀.inner x w w := one_mul _

end Work.Diff.STE.Lead
