import Mathlib
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.Rstar_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: uniform bound for the chart matrix of the reconstruction `Rstar i u`

The reconstruction `D.Rstar i u` is the bilinear form on `M` whose frame expansion in the frame of
chart `i` has the coefficients
`ζ i · χ i (coord i p) · (√(dens i (coord i p)))⁻¹ · u a b (coord i p)`
(see `Work.Diff.STE.B3.Rstar_apply`).  The lemma proved here, `mat_Rstar_bound`, says that for
*continuous* coefficient families `u a b` and a *positive, bounded below* volume density, the chart
matrix of `Rstar i u` read in the frame of **any other chart** `j` is uniformly bounded on the
`σ j`-ball of flat coordinates.  This is the elementary "the reconstruction is a bounded
multiplication operator" statement of the B3 layer, used to dominate the source term of the
Galerkin ODE.

The proof is a direct estimate.  On the flat `σ j`-ball the point `p := D.pt j z` is the base point
of both the frame `e j`, which is **orthonormal** there (`D.heON`), and of the coefficients, which
involve `coord i p`.  Two cases:

* if `ζ i p = 0`, then `Rstar i u p = 0` (`Work.Diff.STE.B3.Rstar_eq_zero_of_zeta_eq_zero`) and the
  bound is trivial;
* otherwise `D.hζsupp` puts `p` in the chart `i` source with `‖coord i p‖ < D.σ i`; hence `χ i = 1`
  there (`D.hχ1`), the frame `e i` is `g₀`-orthonormal at `p` (`D.heON`, via `D.pt_coord`), and
  `coord i p` lies in the flat ball of radius `1/8` (because `2 σ i ≤ 1/4`), where the continuous
  coefficient functions `u a b` are uniformly bounded.  The density is bounded below on that ball
  by hypothesis, and every inner product against the orthonormal frame `e i` is bounded by `1` by
  Cauchy–Schwarz against the *unit* vector `e j a` — this last step is the content of
  `abs_inner_le_one_of_isONFrame`.
-/

namespace Work.Diff.STE.B3

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-! ## Elementary estimates -/

/-- **Cauchy–Schwarz against a vector of an orthonormal family.**  If `e` is a `g`-orthonormal
family at `x`, then the pairing of `e i` with any vector `v` is dominated by the `g`-length
`√(g v v)`.  (Version without `T2Space` of `Work.Diff.EXT.inner_le_sqrt_of_isONFrame`, needed
because the target statement carries no separation hypothesis.) -/
theorem abs_inner_le_sqrt_of_isONFrame (g : Submission.Diff.SMet I M) (x : M)
    {e : Fin (Module.finrank ℝ E) → TangentSpace I x} (he : IsONFrame g x e)
    (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x) :
    |g.inner x (e i) v| ≤ Real.sqrt (g.inner x v v) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have key : ∀ v z : TangentSpace I x, inner ℝ v z = g.inner x v z := fun v z => rfl
  have h1 : ‖e i‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, key (e i) (e i), he i i, if_pos rfl, Real.sqrt_one]
  have h2 : ‖v‖ = Real.sqrt (g.inner x v v) := by rw [norm_eq_sqrt_real_inner, key v v]
  calc |g.inner x (e i) v| = |inner ℝ (e i) v| := by rw [key]
    _ ≤ ‖e i‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = Real.sqrt (g.inner x v v) := by rw [h1, one_mul, h2]

/-- **Pairing with a unit vector.**  If `v` has `g`-length one, its pairing with any vector of a
`g`-orthonormal family is bounded by `1`. -/
theorem abs_inner_le_one_of_isONFrame (g : Submission.Diff.SMet I M) (x : M)
    {e : Fin (Module.finrank ℝ E) → TangentSpace I x} (he : IsONFrame g x e)
    (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x) (hv : g.inner x v v = 1) :
    |g.inner x (e i) v| ≤ 1 := by
  have h := abs_inner_le_sqrt_of_isONFrame g x he i v
  rw [hv, Real.sqrt_one] at h
  exact h

/-- **The absolute value of a double sum of products.**  If `|U c d| ≤ B c d` and `|X c| ≤ 1`,
`|Y d| ≤ 1`, then `|Σ_c Σ_d U c d * X c * Y d| ≤ Σ_c Σ_d B c d`. -/
theorem abs_sum_sum_prod_le {n : ℕ} (U : Fin n → Fin n → ℝ) (X Y : Fin n → ℝ)
    (B : Fin n → Fin n → ℝ)
    (hU : ∀ c d, |U c d| ≤ B c d) (hX : ∀ c, |X c| ≤ 1) (hY : ∀ d, |Y d| ≤ 1) :
    |∑ c, ∑ d, U c d * X c * Y d| ≤ ∑ c, ∑ d, B c d := by
  have hBnn : ∀ c d, 0 ≤ B c d := fun c d => le_trans (abs_nonneg _) (hU c d)
  have h1 : |∑ c, ∑ d, U c d * X c * Y d| ≤ ∑ c, |∑ d, U c d * X c * Y d| :=
    Finset.abs_sum_le_sum_abs _ _
  refine le_trans h1 (Finset.sum_le_sum fun c _ => ?_)
  have h2 : |∑ d, U c d * X c * Y d| ≤ ∑ d, |U c d * X c * Y d| :=
    Finset.abs_sum_le_sum_abs _ _
  refine le_trans h2 (Finset.sum_le_sum fun d _ => ?_)
  rw [abs_mul, abs_mul]
  have step1 : |U c d| * |X c| ≤ B c d * 1 :=
    mul_le_mul (hU c d) (hX c) (abs_nonneg _) (hBnn c d)
  calc |U c d| * |X c| * |Y d| ≤ (B c d * 1) * 1 :=
        mul_le_mul step1 (hY d) (abs_nonneg _) (mul_nonneg (hBnn c d) zero_le_one)
    _ = B c d := by ring

/-! ## The frame expansion of `mat j (Rstar i u)` -/

/-- **The evaluation of the chart matrix of the reconstruction.**  In the flat coordinate `z` of
chart `j`, the chart matrix of `Rstar i u` is the coefficient

`ζ i (pt j z) · χ i (coord i (pt j z)) · (√(dens i (coord i (pt j z))))⁻¹`

times the double sum `Σ_{cd} u c d (coord i (pt j z)) · ⟨e j a, e i c⟩ · ⟨e j b, e i d⟩`, all inner
products taken at the point `D.pt j z`.  This is `Rstar_apply` at `p = D.pt j z`. -/
theorem mat_Rstar_apply_eq
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.mat j (D.Rstar i u) a b z
      = (D.ζ i (D.pt j z) * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
          * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹)
        * (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            u c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
              * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z))
              * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z))) := by
  rw [Work.Diff.STE.B3Data.mat]
  exact Rstar_apply D i u (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z))

/-! ## The uniform bound -/

set_option maxHeartbeats 800000 in
theorem mat_Rstar_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hdens : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (i : ι₀)
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → c ≤ D.dens i z ∧ D.dens i z ≤ C)
    (a b : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ D.σ j → |D.mat j (D.Rstar i u) a b z| ≤ C := by
  classical
  obtain ⟨c, Cd, hc, hCd, hdensb⟩ := hdens
  -- Per-pair bounds for the coefficient families `u a b` on the flat ball of radius `1/8`.
  have hbnd : ∀ c' d' : Fin (Module.finrank ℝ E), ∃ B : ℝ,
      ∀ w : Fin (Module.finrank ℝ E) → ℝ, ‖w‖ ≤ 1 / 8 → |u c' d' w| ≤ B := by
    intro c' d'
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (1 / 8)
        ).exists_bound_of_continuousOn
      ((hu c' d').continuousOn (s := Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (1 / 8)))
    exact ⟨B, fun w hw => by
      simpa only [Real.norm_eq_abs] using
        hB w (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hw)⟩
  choose B hB using hbnd
  have hBnn : ∀ c' d' : Fin (Module.finrank ℝ E), 0 ≤ B c' d' :=
    fun c' d' => le_trans (abs_nonneg _) (hB c' d' 0 (by simp))
  have hCnn : 0 ≤ (∑ c' : Fin (Module.finrank ℝ E),
      ∑ d' : Fin (Module.finrank ℝ E), B c' d') :=
    Finset.sum_nonneg fun c' _ => Finset.sum_nonneg fun d' _ => hBnn c' d'
  refine ⟨(Real.sqrt c)⁻¹ * (∑ c' : Fin (Module.finrank ℝ E),
      ∑ d' : Fin (Module.finrank ℝ E), B c' d'),
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c)) hCnn, ?_⟩
  intro z hz
  by_cases hz0 : D.ζ i (D.pt j z) = 0
  · -- the reconstruction vanishes at `D.pt j z`
    have h0 : D.Rstar i u (D.pt j z) = 0 := Rstar_eq_zero_of_zeta_eq_zero D u hz0
    have hzero : D.mat j (D.Rstar i u) a b z = 0 := by
      rw [Work.Diff.STE.B3Data.mat, h0]
      simp
    rw [hzero, abs_zero]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c)) hCnn
  · -- the chart `i` is genuine at `D.pt j z` and both frames are orthonormal there
    have hz2 : ‖z‖ ≤ 2 * D.σ j := by have := D.hσ j; linarith
    have hsupp := D.hζsupp i (D.pt j z) hz0
    have hσ8 : D.σ i ≤ 1 / 8 := by have := D.hσ2 i; linarith
    have hwn : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)‖ ≤ 1 / 8 :=
      le_trans (le_of_lt hsupp.2) hσ8
    have honi : IsONFrame g₀ (D.pt j z) (fun c' => D.e i c' (D.pt j z)) := by
      have hpt : D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) = D.pt j z :=
        D.pt_coord i hsupp.1
      rw [← hpt]
      exact D.heON i _ (by have := D.hσ i; linarith [hsupp.2])
    have honj : IsONFrame g₀ (D.pt j z) (fun c' => D.e j c' (D.pt j z)) := D.heON j z hz2
    have hχ : D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) = 1 :=
      D.hχ1 i _ (le_of_lt hsupp.2)
    have hζle : D.ζ i (D.pt j z) ≤ 1 := by
      have h1 : (D.ζ i (D.pt j z)) ^ 2 ≤ 1 := by
        rw [← D.hζsq (D.pt j z)]
        exact Finset.single_le_sum (f := fun k : ι₀ => (D.ζ k (D.pt j z)) ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [D.hζnn i (D.pt j z)]
    have hdensz := hdensb i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
      (le_of_lt hsupp.2)
    have hinv : (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹
        ≤ (Real.sqrt c)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr hc) (Real.sqrt_le_sqrt hdensz.1)
    -- the two inner-product factors are bounded by one
    have hX : ∀ c' : Fin (Module.finrank ℝ E),
        |g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c' (D.pt j z))| ≤ 1 := by
      intro c'
      have h := abs_inner_le_sqrt_of_isONFrame g₀ (D.pt j z) honi c' (D.e j a (D.pt j z))
      rw [g₀.symm (D.pt j z) (D.e i c' (D.pt j z)) (D.e j a (D.pt j z))] at h
      rw [honj a a, if_pos rfl, Real.sqrt_one] at h
      exact h
    have hY : ∀ d' : Fin (Module.finrank ℝ E),
        |g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d' (D.pt j z))| ≤ 1 := by
      intro d'
      have h := abs_inner_le_sqrt_of_isONFrame g₀ (D.pt j z) honi d' (D.e j b (D.pt j z))
      rw [g₀.symm (D.pt j z) (D.e i d' (D.pt j z)) (D.e j b (D.pt j z))] at h
      rw [honj b b, if_pos rfl, Real.sqrt_one] at h
      exact h
    -- the coefficient double sum
    have hsum : |∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
          u c' d' (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
            * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c' (D.pt j z))
            * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d' (D.pt j z))|
        ≤ ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E), B c' d' :=
      abs_sum_sum_prod_le
        (fun c' d' => u c' d' (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)))
        (fun c' => g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c' (D.pt j z)))
        (fun d' => g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d' (D.pt j z)))
        (fun c' d' => B c' d') (fun c' d' => hB c' d' _ hwn) hX hY
    have hcoeff : |D.ζ i (D.pt j z)
          * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
          * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹|
        ≤ (Real.sqrt c)⁻¹ := by
      rw [abs_mul, abs_mul, hχ, abs_one, mul_one,
        abs_of_nonneg (D.hζnn i (D.pt j z)),
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      simpa using mul_le_mul hζle hinv (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by norm_num)
    rw [mat_Rstar_apply_eq D i j u a b z, abs_mul]
    exact mul_le_mul hcoeff hsum (abs_nonneg _)
      (inv_nonneg.mpr (Real.sqrt_nonneg c))

end

end Work.Diff.STE.B3
