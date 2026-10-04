import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.scoeff_add_of_support
import Submission.Work.Diff.STE.poincare_cube
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Lead.tendsto_coeffFun_of_BNorm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: subadditivity of the composite norm `D.BNorm`

The composite `Hᵏ` norm of Layer B3,
`D.BNorm k h = Σ_i Σ_{ab} CSq k (fourierCoeff (D.Rper i h a b))`,
is a sum of (weighted) `ℓ²` norms of the Fourier coefficients of the periodised localised
components, hence is subadditive up to the constant `2` (which comes from
`(a + b)² ≤ 2a² + 2b²`):

`D.BNorm k (X + Y) ≤ 2 * D.BNorm k X + 2 * D.BNorm k Y`.

The proof is the exact additive counterpart of `Work.Diff.STE.Lead.BNorm_sub_eq_sum`, and it is
assembly from four independent pieces:

* `Rper_add` (with `R_add`) — the periodisation is additive in the section (`Rper = B3.perFun ∘ R`, and
  `B3.perFun_add_fun` splits the lattice sum; the localised components are supported in the open
  unit cube, so all lattice sums are finitely supported);
* `fourierCoeff_add` — `fourierCoeff` is additive for continuous functions (linearity of the
  integral, `MeasureTheory.integral_add`);
* `CSq_add_le` — the weighted `ℓ²` norm squared obeys `CSq s (c + d) ≤ 2 CSq s c + 2 CSq s d`
  (the pointwise estimate `‖c m + d m‖² ≤ 2‖c m‖² + 2‖d m‖²` and `Summable.tsum_le_tsum`);
* `Rper_periodic` — the periodised components are `1`-periodic, which together with the
  smoothness hypotheses supplies the summability required by `CSq_add_le` through
  `Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff`.

The final step is the finite sum over the charts and the frame indices
(`Finset.sum_le_sum`, `Finset.sum_add_distrib`, `Finset.mul_sum`).
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric MeasureTheory

namespace Work.Diff.STE.Lead

/-! ## The two analytic ingredients (no manifold structure involved) -/

/-- **`fourierCoeff` is additive for continuous functions.**  This is the additive counterpart of
`Work.Diff.STE.fourierCoeff_sub`, and follows from linearity of the integral. -/
lemma fourierCoeff_add {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : (ι → ℝ) → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    Work.Diff.STE.fourierCoeff (f + g)
      = Work.Diff.STE.fourierCoeff f + Work.Diff.STE.fourierCoeff g := by
  funext k
  have h1 : Integrable (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * f x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous
      ((Work.Diff.STE.continuous_fourierExp (-k)).mul hf)
  have h2 : Integrable (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * g x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous
      ((Work.Diff.STE.continuous_fourierExp (-k)).mul hg)
  change (∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.fourierExp (-k) x * (f + g) x)
      = (∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.fourierExp (-k) x * f x)
        + (∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.fourierExp (-k) x * g x)
  rw [← MeasureTheory.integral_add h1 h2]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [Pi.add_apply]; ring)

/-- **Subadditivity of the weighted `ℓ²` norm squared.**  The constant `2` is the optimum of the
pointwise estimate `‖c m + d m‖² ≤ 2‖c m‖² + 2‖d m‖²`.  The summability hypotheses are what make
the two sides comparable (without them `CSq` is `0` on non-summable families, while a pointwise
sum of two non-summable families can be summable). -/
lemma CSq_add_le {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (c d : (ι → ℤ) → ℂ)
    (hc : Summable fun m => Work.Diff.STE.wt m ^ s * ‖c m‖ ^ 2)
    (hd : Summable fun m => Work.Diff.STE.wt m ^ s * ‖d m‖ ^ 2) :
    Work.Diff.STE.CSq s (c + d) ≤ 2 * Work.Diff.STE.CSq s c + 2 * Work.Diff.STE.CSq s d := by
  have hpt : ∀ m : ι → ℤ, Work.Diff.STE.wt m ^ s * ‖c m + d m‖ ^ 2
      ≤ 2 * (Work.Diff.STE.wt m ^ s * ‖c m‖ ^ 2)
        + 2 * (Work.Diff.STE.wt m ^ s * ‖d m‖ ^ 2) := by
    intro m
    have h1 : ‖c m + d m‖ ^ 2 ≤ (‖c m‖ + ‖d m‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    have h3 : (‖c m‖ + ‖d m‖) ^ 2 ≤ 2 * ‖c m‖ ^ 2 + 2 * ‖d m‖ ^ 2 := by
      nlinarith [sq_nonneg (‖c m‖ - ‖d m‖)]
    have h4 : 0 ≤ Work.Diff.STE.wt m ^ s :=
      pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) s
    calc Work.Diff.STE.wt m ^ s * ‖c m + d m‖ ^ 2
        ≤ Work.Diff.STE.wt m ^ s * (2 * ‖c m‖ ^ 2 + 2 * ‖d m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) h4
      _ = 2 * (Work.Diff.STE.wt m ^ s * ‖c m‖ ^ 2)
            + 2 * (Work.Diff.STE.wt m ^ s * ‖d m‖ ^ 2) := by ring
  have hsumRHS : Summable (fun m : ι → ℤ =>
      2 * (Work.Diff.STE.wt m ^ s * ‖c m‖ ^ 2)
        + 2 * (Work.Diff.STE.wt m ^ s * ‖d m‖ ^ 2)) :=
    (hc.mul_left 2).add (hd.mul_left 2)
  have hsumLHS : Summable (fun m : ι → ℤ => Work.Diff.STE.wt m ^ s * ‖c m + d m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) s) (sq_nonneg _))
      hpt hsumRHS
  calc Work.Diff.STE.CSq s (c + d)
      = ∑' m, Work.Diff.STE.wt m ^ s * ‖c m + d m‖ ^ 2 := rfl
    _ ≤ ∑' m, (2 * (Work.Diff.STE.wt m ^ s * ‖c m‖ ^ 2)
          + 2 * (Work.Diff.STE.wt m ^ s * ‖d m‖ ^ 2)) :=
        Summable.tsum_le_tsum hpt hsumLHS hsumRHS
    _ = 2 * Work.Diff.STE.CSq s c + 2 * Work.Diff.STE.CSq s d := by
        rw [Summable.tsum_add (hc.mul_left 2) (hd.mul_left 2), tsum_mul_left, tsum_mul_left]
        rfl

/-! ## Additivity of the periodised localised component -/

/-- **The localised component is additive in the section** (pointwise, from the definitions: the
chart matrix is the contraction of the section with the frame, and `Bil` is a family of continuous
bilinear forms with the pointwise `Add`). -/
lemma R_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X Y : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    D.R i (X + Y) a b = D.R i X a b + D.R i Y a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.add_apply, add_apply]
  ring

/-- **The periodisation is additive in the section**, as an equality of functions. -/
lemma Rper_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X Y : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    D.Rper i (X + Y) a b = D.Rper i X a b + D.Rper i Y a b := by
  have hR : D.R i (X + Y) a b = D.R i X a b + D.R i Y a b := R_add D X Y i a b
  have hsX : Function.support (D.R i X a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun _ hz => Set.pi_mono (fun _ _ => Set.Ioo_subset_Ioc_self) (D.R_support i X a b hz)
  have hsY : Function.support (D.R i Y a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun _ hz => Set.pi_mono (fun _ _ => Set.Ioo_subset_Ioc_self) (D.R_support i Y a b hz)
  show Work.Diff.STE.B3.perFun (D.R i (X + Y) a b)
      = Work.Diff.STE.B3.perFun (D.R i X a b) + Work.Diff.STE.B3.perFun (D.R i Y a b)
  rw [hR]
  exact Work.Diff.STE.B3.perFun_add_fun _ _ hsX hsY

/-- **The periodised localised component is `1`-periodic** (the lattice sum of a function supported
in the open unit cube, reindexed by a translation of the lattice).  Needed only to feed the
summability theorem `Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff`. -/
lemma Rper_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.Periodic1 (D.Rper i X a b) := by
  rw [show D.Rper i X a b = (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ∑' m : Fin (Module.finrank ℝ E) → ℤ,
        ((D.R i X a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)) from rfl]
  exact Work.Diff.STE.periodization_periodic (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i X a b z : ℝ) : ℂ))

/-! ## The target -/

theorem BNorm_add_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (X Y : Work.Diff.STE.Bil (I := I) (M := M))
    (hX : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i X a b))
    (hY : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i Y a b)) :
    D.BNorm k (X + Y) ≤ 2 * D.BNorm k X + 2 * D.BNorm k Y := by
  -- each summand of `BNorm k (X + Y)` is bounded by the corresponding summands of `BNorm k X`,
  -- `BNorm k Y`
  have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i (X + Y) a b))
        ≤ 2 * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i X a b))
          + 2 * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i Y a b)) := by
    intro i a b
    rw [Rper_add D X Y i a b]
    rw [fourierCoeff_add (D.Rper i X a b) (D.Rper i Y a b)
      (hX i a b).continuous (hY i a b).continuous]
    exact CSq_add_le k _ _
      (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _ (hX i a b)
        (Rper_periodic D X i a b) k)
      (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _ (hY i a b)
        (Rper_periodic D Y i a b) k)
  -- sum over the charts and the frame indices, and collect the constants
  calc D.BNorm k (X + Y)
      = ∑ i, ∑ a, ∑ b,
          Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i (X + Y) a b)) := rfl
    _ ≤ ∑ i, ∑ a, ∑ b,
          (2 * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i X a b))
            + 2 * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i Y a b))) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => hterm i a b
    _ = 2 * D.BNorm k X + 2 * D.BNorm k Y := by
        simp only [Work.Diff.STE.B3Data.BNorm, Finset.sum_add_distrib, Finset.mul_sum]

end Work.Diff.STE.Lead
