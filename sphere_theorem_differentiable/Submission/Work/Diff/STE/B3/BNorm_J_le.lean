import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le
import Submission.Work.Diff.STE.B3.pdVec_integral_le_CSq
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.BPair_Rstar
import Submission.Work.Diff.STE.B3.mat_Rstar_bound
import Submission.Work.Diff.STE.B3.goodSet_smooth_noT2
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.D.bump_smul_smooth
import Submission.Work.Diff.STE.D.flatToE_mem_interior_target
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.B3.BNorm_prelim
import Submission.Work.Diff.STE.B3.closure_Omega_goodSet
import Submission.Work.Diff.STE.B3.tMapFun_injOn_det
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen
import Submission.Work.Diff.STE.B3.STruncR_CSq_le
import Submission.Work.Diff.STE.B3.STruncC_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the Friedrichs mollifier is bounded in the composite `Hᵏ` norm

This file proves `Work.Diff.STE.B3.BNorm_J_le`, the estimate

  `D.BNorm k (D.J ρ ε h) ≤ C · D.BNorm k h`   (`finrank ℝ E < 2k`, `‖ρ‖ ≤ 1`),

i.e. that the Friedrichs mollifier `J ρ ε = Σ_i R_i*(S_ε (R_i ·))` of Layer B3 is bounded in the
composite norm, uniformly in the section `h`.

## Route

`BNorm k (J h) = Σ_j Σ_{ab} CSq k (fourierCoeff (Rper j (J h) a b))` is a sum of chartwise `Hᵏ`
norms, so the heart of the matter is the *chart transfer*: the chart-`j` component of `J h` is a
sum of terms `(coefficient) · (u ∘ T)` with `T` the flat chart transition and `u` a component of
`h`; by `CSq_period_comp_arg_le` (the linchpin of Layer B3) such a term has `Hᵏ` norm bounded by
that of `u`, and the truncation `S_ε` only decreases it (`CSq_trunc_le`).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory BigOperators
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

set_option linter.unusedSectionVars false


/-! ## 1. Elementary facts about `CSq` and periodisations -/

section Elementary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `CSq` is quadratic under scalar multiplication. -/
lemma CSq_smul (s : ℕ) (c : ℝ) (d : (ι → ℤ) → ℂ) :
    CSq s (c • d) = c ^ 2 * CSq s d := by
  have hpt : ∀ k : ι → ℤ, wt k ^ s * ‖(c • d) k‖ ^ 2 = c ^ 2 * (wt k ^ s * ‖d k‖ ^ 2) := by
    intro k
    rw [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  show (∑' k : ι → ℤ, wt k ^ s * ‖(c • d) k‖ ^ 2)
      = c ^ 2 * ∑' k : ι → ℤ, wt k ^ s * ‖d k‖ ^ 2
  rw [show (fun k : ι → ℤ => wt k ^ s * ‖(c • d) k‖ ^ 2)
      = fun k : ι → ℤ => c ^ 2 * (wt k ^ s * ‖d k‖ ^ 2) from funext hpt]
  exact tsum_mul_left

/-- The `CSq` of a finite sum is bounded by the number of summands times the sum of the `CSq`s. -/
lemma CSq_sum_le {J : Type*} [Fintype J] (s : ℕ) (c : J → (ι → ℤ) → ℂ)
    (h : ∀ j, Summable fun m : ι → ℤ => wt m ^ s * ‖c j m‖ ^ 2) :
    CSq s (fun m => ∑ j, c j m) ≤ (Fintype.card J : ℝ) * ∑ j, CSq s (c j) := by
  have hpt : ∀ m : ι → ℤ, wt m ^ s * ‖∑ j, c j m‖ ^ 2
      ≤ (Fintype.card J : ℝ) * ∑ j, (wt m ^ s * ‖c j m‖ ^ 2) := by
    intro m
    have h0 : ‖∑ j, c j m‖ ≤ ∑ j, ‖c j m‖ := norm_sum_le _ _
    have h1 : (∑ j : J, ‖c j m‖) ^ 2 ≤ (Finset.univ : Finset J).card * ∑ j, ‖c j m‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [Finset.card_univ] at h1
    have h1' : ‖∑ j, c j m‖ ^ 2 ≤ (Fintype.card J : ℝ) * ∑ j, ‖c j m‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h0 2).trans h1
    have h2 : (0 : ℝ) ≤ wt m ^ s := pow_nonneg (le_of_lt (wt_pos m)) s
    have heq : wt m ^ s * ((Fintype.card J : ℝ) * ∑ j, ‖c j m‖ ^ 2)
        = (Fintype.card J : ℝ) * ∑ j, (wt m ^ s * ‖c j m‖ ^ 2) := by
      rw [← Finset.mul_sum]
      ring
    calc wt m ^ s * ‖∑ j, c j m‖ ^ 2
        ≤ wt m ^ s * ((Fintype.card J : ℝ) * ∑ j, ‖c j m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1' h2
      _ = (Fintype.card J : ℝ) * ∑ j, (wt m ^ s * ‖c j m‖ ^ 2) := heq
  have hsumRHS : Summable (fun m : ι → ℤ =>
      (Fintype.card J : ℝ) * ∑ j : J, wt m ^ s * ‖c j m‖ ^ 2) :=
    (summable_sum (f := fun (j : J) (m : ι → ℤ) => wt m ^ s * ‖c j m‖ ^ 2)
      (s := (Finset.univ : Finset J)) (fun j _ => h j)).mul_left _
  have hsumLHS : Summable (fun m : ι → ℤ => wt m ^ s * ‖∑ j, c j m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (le_of_lt (wt_pos m)) s) (sq_nonneg _)) hpt hsumRHS
  calc CSq s (fun m => ∑ j, c j m)
      = ∑' m, wt m ^ s * ‖∑ j, c j m‖ ^ 2 := rfl
    _ ≤ ∑' m, (Fintype.card J : ℝ) * ∑ j : J, wt m ^ s * ‖c j m‖ ^ 2 :=
        Summable.tsum_le_tsum hpt hsumLHS hsumRHS
    _ = (Fintype.card J : ℝ) * ∑' m, ∑ j : J, wt m ^ s * ‖c j m‖ ^ 2 := tsum_mul_left
    _ = (Fintype.card J : ℝ) * ∑ j : J, ∑' m, wt m ^ s * ‖c j m‖ ^ 2 := by
        congr 1
        exact Summable.tsum_finsetSum (f := fun (j : J) (m : ι → ℤ) => wt m ^ s * ‖c j m‖ ^ 2)
          (s := (Finset.univ : Finset J)) (fun j _ => h j)
    _ = (Fintype.card J : ℝ) * ∑ j : J, CSq s (c j) := rfl

/-- `fourierCoeff` is linear: the coefficients of a constant multiple. -/
lemma fourierCoeff_const_mul (c : ℂ) (g : (ι → ℝ) → ℂ) :
    fourierCoeff (fun y => c * g y) = fun k => c * fourierCoeff g k := by
  funext k
  simp only [fourierCoeff]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- `CSq` of a constant multiple. -/
lemma CSq_const_mul (s : ℕ) (c : ℂ) (d : (ι → ℤ) → ℂ) :
    CSq s (fun k => c * d k) = ‖c‖ ^ 2 * CSq s d := by
  have hpt : ∀ k : ι → ℤ, wt k ^ s * ‖c * d k‖ ^ 2 = ‖c‖ ^ 2 * (wt k ^ s * ‖d k‖ ^ 2) := by
    intro k
    rw [norm_mul, mul_pow]
    ring
  show (∑' k : ι → ℤ, wt k ^ s * ‖c * d k‖ ^ 2) = ‖c‖ ^ 2 * ∑' k : ι → ℤ, wt k ^ s * ‖d k‖ ^ 2
  rw [show (fun k : ι → ℤ => wt k ^ s * ‖c * d k‖ ^ 2)
      = fun k : ι → ℤ => ‖c‖ ^ 2 * (wt k ^ s * ‖d k‖ ^ 2) from funext hpt]
  exact tsum_mul_left

/-- The norm of a real number seen in `ℂ`. -/
lemma norm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- The Fourier coefficients of a finite sum of functions. -/
lemma fourierCoeff_sum {J : Type*} (s : Finset J) (g : J → (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hg : ∀ j ∈ s, IntegrableOn (fun x => fourierExp (-k) x * g j x)
      (unitCube (ι := ι)) volume) :
    fourierCoeff (fun x => ∑ j ∈ s, g j x) k = ∑ j ∈ s, fourierCoeff (g j) k := by
  simp only [fourierCoeff]
  rw [← MeasureTheory.integral_finsetSum]
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show fourierExp (-k) x * (∑ j ∈ s, g j x) = ∑ j ∈ s, fourierExp (-k) x * g j x
    rw [Finset.mul_sum]
  · intro j hj
    exact hg j hj

/-- The Fourier coefficients of a finite sum of continuous functions. -/
lemma fourierCoeff_finset_sum_of_continuous {J : Type*} [Fintype J]
    (g : J → (ι → ℝ) → ℂ) (hg : ∀ j, Continuous (g j)) (k : ι → ℤ) :
    fourierCoeff (fun x => ∑ j, g j x) k = ∑ j, fourierCoeff (g j) k :=
  fourierCoeff_sum Finset.univ g k fun j _ =>
    integrableOn_unitCube_of_continuous_cplx ((continuous_fourierExp (-k)).mul (hg j))

/-- Interchanging a `tsum` over the lattice with a finite sum, when all the summands vanish
outside a common finite set. -/
lemma tsum_finset_sum_eq {J : Type*} [Fintype J] {S : Finset (ι → ℤ)}
    (f : J → (ι → ℤ) → ℂ) (h : ∀ j m, m ∉ S → f j m = 0) :
    (∑' m, ∑ j, f j m) = ∑ j, ∑' m, f j m := by
  rw [tsum_eq_sum (s := S) (fun m hm => by simp [h _ _ hm])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_eq_sum (s := S) (fun m hm => h j m hm)]

end Elementary

/-! ## 2. A compact set between a compact set and an open neighbourhood -/

section Topology

/-- **A compact set strictly between a compact set and an open neighbourhood.**  For a compact `K`
contained in an open `U` there is a compact `K'` with `K ⊆ interior K'` and `K' ⊆ U`. -/
lemma exists_isCompact_between {n : ℕ} {K U : Set (Fin n → ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ K' : Set (Fin n → ℝ), IsCompact K' ∧ K ⊆ interior K' ∧ K' ⊆ U := by
  classical
  have hrad : ∀ x : Fin n → ℝ, ∃ r : ℝ, 0 < r ∧ (x ∈ K → Metric.closedBall x r ⊆ U) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU hx))
      refine ⟨ε / 2, half_pos hε, fun _ => ?_⟩
      exact (Metric.closedBall_subset_ball (by linarith)).trans hεU
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  choose r hr hrU using hrad
  obtain ⟨b', hb'K, hb'fin, hcover⟩ := hK.elim_finite_subcover_image
    (b := K) (c := fun x : Fin n → ℝ => Metric.ball x (r x / 2)) (fun x _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_biUnion hx (Metric.mem_ball_self (half_pos (hr x))))
  refine ⟨⋃ x ∈ b', Metric.closedBall x (r x / 2), ?_, ?_, ?_⟩
  · exact hb'fin.isCompact_biUnion (fun x _ => isCompact_closedBall x (r x / 2))
  · intro x hx
    obtain ⟨y, hyb, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact interior_mono (Set.subset_iUnion₂ y hyb)
      (Metric.ball_subset_interior_closedBall hxy)
  · intro x hx
    obtain ⟨y, hyb, hxy⟩ := Set.mem_iUnion₂.mp hx
    exact (hrU y (hb'K hyb)) (Metric.closedBall_subset_closedBall (by linarith [hr y]) hxy)

end Topology

/-! ## 3. The cross-chart expansion of the reconstruction, and its junk-free form -/

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- Distributing a constant product over a double sum (the algebra of the cross-chart
expansion). -/
lemma factor_sum {n : ℕ} (A K : ℝ) (X Y : Fin n → ℝ) (g : Fin n → Fin n → ℝ) :
    (∑ c, ∑ d, (A * K * X c * Y d) * g c d)
      = A * (K * (∑ c, ∑ d, g c d * X c * Y d)) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-- **The cross-chart expansion, pointwise and without `[T2Space M]`.**  The `j`-component of
`Rstar i u` is the double sum of the explicit coefficient `coeffFun` against the components of `u`
evaluated at the flat transition `tMapFun`. -/
theorem R_Rstar_expansion_pointwise_noT2 (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b : Fin (Module.finrank ℝ E))
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.R j (D.Rstar i u) a b z
      = ∑ c, ∑ d, Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z
          * u c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) := by
  rw [B3Data.R, mat_Rstar_apply_eq D i j u a b z]
  simp only [Work.Diff.STE.D.coeffFun, Work.Diff.STE.D.tMapFun]
  rw [factor_sum]

/-- The cross-chart coefficient vanishes when `ψ j` does. -/
lemma coeffFun_eq_zero_of_psi_eq_zero (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.psi j z = 0) :
    Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z = 0 := by
  conv_lhs => rw [Work.Diff.STE.D.coeffFun]
  rw [h]
  simp only [zero_mul]

/-- The cross-chart coefficient vanishes when `ζ i ∘ pt j` does. -/
lemma coeffFun_eq_zero_of_zeta_eq_zero (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (h : D.ζ i (D.pt j z) = 0) :
    Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z = 0 := by
  conv_lhs => rw [Work.Diff.STE.D.coeffFun]
  rw [h]
  ring

/-- The support of the cross-chart coefficient is contained in `Omega`. -/
lemma support_coeffFun_subset_Omega (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) :
    Function.support (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) ⊆
      Work.Diff.STE.D.Omega (I := I) (M := M) D i j := by
  intro z hz
  exact ⟨fun h0 => hz (coeffFun_eq_zero_of_psi_eq_zero D i j a b c d h0),
    fun h0 => hz (coeffFun_eq_zero_of_zeta_eq_zero D i j a b c d h0)⟩

/-- The support of the cross-chart coefficient lies in the open unit cube. -/
lemma support_coeffFun_subset_cube (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) :
    Function.support (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro z hz
  exact D.psi_supp j (fun h0 => hz (coeffFun_eq_zero_of_psi_eq_zero D i j a b c d h0))

/-- The (topological) support of the cross-chart coefficient is contained in the closed
`σ j`-ball, hence is compact. -/
lemma tsupport_coeffFun_subset_closedBall (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) :
    tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) ⊆
      Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ j) := by
  have h1 : tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) ⊆
      closure (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ j)) :=
    closure_mono (fun z hz => by
      rw [Metric.mem_ball, dist_zero_right]
      exact norm_lt_sigma_of_psi_ne_zero (D := D) (i := j) (z := z)
        (fun h0 => hz (coeffFun_eq_zero_of_psi_eq_zero D i j a b c d h0)))
  rw [closure_ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.hσ j).ne'] at h1
  exact h1

lemma isCompact_tsupport_coeffFun (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) :
    IsCompact (tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d)) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ j))
    (isClosed_tsupport _) (tsupport_coeffFun_subset_closedBall D i j a b c d)

/-- **The junk-free cross-chart expansion.**  The chart-`j` component of `R*_i u` can be written as
a double sum `Σ_{cd} G c d z * u c d (T z)` with `G c d` globally smooth and supported in the open
cube and `T` globally smooth and equal to the flat transition `tMapFun` near the support; moreover
`T` is injective with invertible derivative on an open set containing the supports.  This is the
form in which the chart transfer `CSq_period_comp_arg_le` can be applied.

The proof multiplies `coeffFun` and `tMapFun` by smooth bumps of the (junk-free) region
`goodSet`; since `coeffFun` vanishes identically near every point where the transition is not the
genuine one, the identity survives. -/
theorem bump_expansion (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b : Fin (Module.finrank ℝ E))
    (hgood : closure (Work.Diff.STE.D.Omega (I := I) (M := M) D i j) ⊆
      Work.Diff.STE.D.goodSet (I := I) (M := M) D i j)
    (hopen : IsOpen (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j))
    (hsmT : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j))
    (hsmC : ∀ c d : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j))
    (hinjT : Set.InjOn (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j))
    (hdetT : ∀ z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j,
      (fderiv ℝ (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z).det ≠ 0) :
    ∃ (T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ))
      (G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℂ)
      (U : Set (Fin (Module.finrank ℝ E) → ℝ)),
      IsOpen U ∧ ContDiff ℝ (⊤ : ℕ∞) T ∧ Set.InjOn T U ∧
      (∀ z ∈ U, (fderiv ℝ T z).det ≠ 0) ∧
      (∀ c d, ContDiff ℝ (⊤ : ℕ∞) (G c d)) ∧
      (∀ c d, Function.support (G c d) ⊆
        Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) ∧
      (∀ c d, IsCompact (tsupport (G c d))) ∧
      (∀ c d, tsupport (G c d) ⊆ U) ∧
      (∀ (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ),
        ((D.R j (D.Rstar i u) a b z : ℝ) : ℂ)
          = ∑ c, ∑ d, G c d z * ((u c d (T z) : ℝ) : ℂ)) := by
  classical
  set K : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    Set.iUnion (fun c : Fin (Module.finrank ℝ E) =>
      Set.iUnion (fun d : Fin (Module.finrank ℝ E) =>
        tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d))) with hKdef
  have hKmem : ∀ c d : Fin (Module.finrank ℝ E),
      tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) ⊆ K := by
    intro c d z hz
    rw [hKdef]
    exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨d, hz⟩⟩
  have hKcomp : IsCompact K := by
    rw [hKdef]
    exact isCompact_iUnion (fun c => isCompact_iUnion
      (fun d => isCompact_tsupport_coeffFun D i j a b c d))
  have hKsub : K ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j := by
    refine Set.iUnion_subset (fun c => Set.iUnion_subset (fun d => ?_))
    exact (closure_mono (support_coeffFun_subset_Omega D i j a b c d)).trans hgood
  obtain ⟨K', hK'comp, hKK', hK'U⟩ := exists_isCompact_between hKcomp hopen hKsub
  have hK'good : K' ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j := hK'U
  -- the bump on the transition
  obtain ⟨φT, hφTsm, hφT1, hφTsup, hTsm⟩ := Work.Diff.STE.D.bump_smul_smooth K'
    (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) hK'comp hopen hK'U
    (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) hsmT
  -- the bumps on the coefficients
  have hbump : ∀ c d : Fin (Module.finrank ℝ E),
      ∃ φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ ∧
        (∀ z ∈ tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d), φ z = 1) ∧
        tsupport φ ⊆ interior K' ∧
        ContDiff ℝ (⊤ : ℕ∞) (fun z =>
          φ z * ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) := by
    intro c d
    refine Work.Diff.STE.D.bump_smul_smooth
      (tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d)) (interior K')
      (isCompact_tsupport_coeffFun D i j a b c d) isOpen_interior ?_
      (fun z => ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) ?_
    · exact (hKmem c d).trans hKK'
    · refine (Complex.ofRealCLM.contDiff.comp_contDiffOn ?_)
      exact (hsmC c d).mono (interior_subset.trans hK'U)
  choose φ hφsm hφ1 hφsup hφsm2 using hbump
  have hGsup : ∀ c d : Fin (Module.finrank ℝ E),
      tsupport (fun z => φ c d z *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) ⊆
        interior K' := by
    intro c d
    have h1 : tsupport (fun z => φ c d z *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) ⊆
        tsupport (φ c d) ∪ tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) := by
      have hsub : Function.support (fun z => φ c d z *
          ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) ⊆
          Function.support (φ c d) ∪
            Function.support (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) := by
        intro z hz
        rcases mul_ne_zero_iff.mp (Function.mem_support.mp hz) with ⟨h1, h2⟩
        exact Or.inl (Function.mem_support.mpr (fun h => h1 (by rw [h, Complex.ofReal_zero])))
      rw [tsupport, tsupport, tsupport]
      refine (closure_mono hsub).trans ?_
      rw [closure_union]
    exact h1.trans (Set.union_subset (hφsup c d) ((hKmem c d).trans hKK'))
  refine ⟨fun z => φT z • Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z,
    (fun c d z => φ c d z * ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)),
    interior K', isOpen_interior, hTsm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- injectivity on `interior K'`
    intro z hz z' hz' h
    refine hinjT (hK'good (interior_subset hz)) (hK'good (interior_subset hz')) ?_
    have h1 : φT z = 1 := hφT1 z (interior_subset hz)
    have h2 : φT z' = 1 := hφT1 z' (interior_subset hz')
    simpa only [h1, h2, one_smul] using h
  · -- invertible derivative
    intro z hz
    have hev : (fun w => φT w • Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j w)
        =ᶠ[𝓝 z] Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j := by
      filter_upwards [isOpen_interior.mem_nhds hz] with w hw
      rw [hφT1 w (interior_subset hw), one_smul]
    rw [hev.fderiv_eq]
    exact hdetT z (hK'good (interior_subset hz))
  · intro c d; exact hφsm2 c d
  · -- supports inside the open cube
    intro c d z hz
    refine support_coeffFun_subset_cube D i j a b c d ?_
    intro h0
    exact hz (by
      show φ c d z * ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) = 0
      rw [h0]
      simp)
  · -- compact supports
    intro c d
    exact IsCompact.of_isClosed_subset hK'comp (isClosed_tsupport _)
      ((hGsup c d).trans interior_subset)
  · -- supports inside `U`
    intro c d
    exact hGsup c d
  · -- the identity
    intro u z
    rw [R_Rstar_expansion_pointwise_noT2 D i j a b u z]
    push_cast
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    by_cases hcd : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z = 0
    · rw [hcd]
      simp
    · have hzmem : z ∈ tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) :=
        subset_closure (Function.mem_support.mpr hcd)
      have h1 : φ c d z = 1 := hφ1 c d z hzmem
      have h2 : φT z = 1 := hφT1 z (interior_subset (hKK' (hKmem c d hzmem)))
      rw [h1, h2, one_smul]
      simp

/-- **The homogeneous form of the chart transfer.**  From the transfer estimate with an additive
constant one obtains the homogeneous estimate by rescaling `u` (and handling `u = 0`). -/
lemma homog_transfer {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (T : (ι → ℝ) → (ι → ℝ)) (f : (ι → ℝ) → ℂ)
    (h : ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → Periodic1 u →
      CSq s (fourierCoeff (fun z => ∑' m : ι → ℤ, f (z + iVec m) *
        u (T (z + iVec m))))
        ≤ C * (1 + CSq s (fourierCoeff u))) :
    ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → Periodic1 u →
      CSq s (fourierCoeff (fun z => ∑' m : ι → ℤ, f (z + iVec m) *
        u (T (z + iVec m))))
        ≤ 2 * C * CSq s (fourierCoeff u) := by
  intro u hu hup
  by_cases hz : CSq s (fourierCoeff u) = 0
  · -- each Fourier coefficient vanishes, hence so does `u`
    have hsum : Summable fun m : ι → ℤ => wt m ^ s * ‖fourierCoeff u m‖ ^ 2 :=
      summable_weighted_fourierCoeff_of_contDiff u hu hup s
    have hzero : ∀ k : ι → ℤ, fourierCoeff u k = 0 := by
      intro k
      have hle : wt k ^ s * ‖fourierCoeff u k‖ ^ 2 ≤
          ∑' m : ι → ℤ, wt m ^ s * ‖fourierCoeff u m‖ ^ 2 := by
        have := Summable.sum_le_tsum ({k} : Finset (ι → ℤ))
          (fun m _ => mul_nonneg (pow_nonneg (le_of_lt (wt_pos m)) s) (sq_nonneg _)) hsum
        simpa using this
      have h1 : wt k ^ s * ‖fourierCoeff u k‖ ^ 2 = 0 :=
        le_antisymm (hle.trans (le_of_eq hz))
          (mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _))
      have hw : (0 : ℝ) < wt k ^ s := pow_pos (wt_pos k) s
      have h2 : ‖fourierCoeff u k‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h' | h'
        · exact absurd h' (ne_of_gt hw)
        · exact h'
      have h3 : ‖fourierCoeff u k‖ = 0 := by
        nlinarith [norm_nonneg (fourierCoeff u k)]
      exact norm_eq_zero.mp h3
    have hu0 : u = 0 := by
      funext z
      rw [← flat.seriesFun_fourierCoeff u hu hup z]
      simp only [seriesFun, hzero, Pi.zero_apply, zero_mul, tsum_zero]
    have hfun : (fun z : ι → ℝ => ∑' m : ι → ℤ, f (z + iVec m) * u (T (z + iVec m)))
        = fun _ : ι → ℝ => (0 : ℂ) := by
      rw [hu0]
      funext z
      simp
    rw [hfun]
    have h0 : CSq s (fourierCoeff (fun _ : ι → ℝ => (0 : ℂ))) = 0 := by
      rw [show fourierCoeff (fun _ : ι → ℝ => (0 : ℂ)) = 0 from
        funext fun k => by simp [fourierCoeff]]
      simp [CSq]
    have hu0' : CSq s (fourierCoeff u) = 0 := by rw [hu0]; exact h0
    rw [h0, hu0', mul_zero]
  · have hpos : 0 < CSq s (fourierCoeff u) := lt_of_le_of_ne (CSq_nonneg s _) (Ne.symm hz)
    set cc : ℝ := Real.sqrt (CSq s (fourierCoeff u)) with hcc
    have hccpos : 0 < cc := Real.sqrt_pos.mpr hpos
    have hcc2 : cc ^ 2 = CSq s (fourierCoeff u) := Real.sq_sqrt (le_of_lt hpos)
    have hccne : cc ≠ 0 := hccpos.ne'
    let u' : (ι → ℝ) → ℂ := fun y => ((cc⁻¹ : ℝ) : ℂ) * u y
    have hu' : ContDiff ℝ (⊤ : ℕ∞) u' := by
      show ContDiff ℝ (⊤ : ℕ∞) (fun y => ((cc⁻¹ : ℝ) : ℂ) * u y)
      exact contDiff_const.mul hu
    have hper' : Periodic1 u' := by
      intro i x
      show ((cc⁻¹ : ℝ) : ℂ) * u (x + Pi.single i 1) = ((cc⁻¹ : ℝ) : ℂ) * u x
      rw [hup i x]
    have hbound := h u' hu' hper'
    have hcoeff : fourierCoeff u' = fun k => ((cc⁻¹ : ℝ) : ℂ) * fourierCoeff u k := by
      show fourierCoeff (fun y => ((cc⁻¹ : ℝ) : ℂ) * u y) = _
      exact fourierCoeff_const_mul _ u
    have hscale : CSq s (fourierCoeff u') = 1 := by
      rw [hcoeff, CSq_const_mul, norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hccpos.le),
        ← hcc2]
      field_simp
    rw [hscale] at hbound
    have hbound' : CSq s (fourierCoeff (fun z : ι → ℝ => ∑' m : ι → ℤ, f (z + iVec m) *
        u' (T (z + iVec m)))) ≤ 2 * C := by
      have h2 : (1 : ℝ) + 1 = 2 := by norm_num
      rw [h2] at hbound
      linarith [hbound]
    -- the scaling relation between the two left-hand sides
    have hperrel : (fun z : ι → ℝ => ∑' m : ι → ℤ, f (z + iVec m) * u (T (z + iVec m)))
        = (fun z : ι → ℝ => ((cc : ℝ) : ℂ) * (∑' m : ι → ℤ, f (z + iVec m) *
            u' (T (z + iVec m)))) := by
      funext z
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      show f (z + iVec m) * u (T (z + iVec m))
        = ((cc : ℝ) : ℂ) * (f (z + iVec m) * (((cc⁻¹ : ℝ) : ℂ) * u (T (z + iVec m))))
      have h1 : ((cc : ℝ) : ℂ) * (((cc⁻¹ : ℝ)) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hccne]
        rfl
      calc f (z + iVec m) * u (T (z + iVec m))
          = f (z + iVec m) * u (T (z + iVec m)) * (((cc : ℝ) : ℂ) * (((cc⁻¹ : ℝ)) : ℂ)) := by
            rw [h1, mul_one]
        _ = ((cc : ℝ) : ℂ) * (f (z + iVec m) * (((cc⁻¹ : ℝ) : ℂ) * u (T (z + iVec m)))) := by
            ring
    rw [hperrel, fourierCoeff_const_mul, CSq_const_mul]
    rw [norm_ofReal, abs_of_nonneg hccpos.le, ← hcc2]
    calc cc ^ 2 * CSq s (fourierCoeff (fun z : ι → ℝ => ∑' m : ι → ℤ, f (z + iVec m) *
          u' (T (z + iVec m))))
        ≤ cc ^ 2 * (2 * C) := mul_le_mul_of_nonneg_left hbound' (sq_nonneg cc)
      _ = 2 * C * cc ^ 2 := by ring

/-- The real part of `STruncC` is `B3Data.STruncR`. -/
lemma STruncC_re_eq (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    (Work.Diff.STE.STruncC ρ ε f z).re = B3Data.STruncR ρ ε f z := rfl

end Geometry

end Work.Diff.STE.B3

namespace Work.Diff.STE.B3

set_option maxHeartbeats 800000 in
theorem BNorm_J_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (hk : Module.finrank ℝ E < 2 * k) (ε : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b)) →
      D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h := by
  classical
  -- the per-`(j,a,b)` bound, uniform in the section
  have hmain : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d)) →
        CSq k (fourierCoeff (D.Rper j (D.J ρ ε h) a b)) ≤ Cf * D.BNorm k h := by
    intro j a b
    -- the junk-free expansion of the cross-chart terms
    choose T G U hUopen hTsm hTinj hTdet hGsm hGsupp hGcomp hGsub hid using fun (i : ι₀) =>
      Work.Diff.STE.B3.bump_expansion D i j a b
        (Work.Diff.STE.B3.closure_Omega_goodSet D i j)
        (Work.Diff.STE.B3.goodSet_smooth_noT2 D i j).1
        (Work.Diff.STE.B3.goodSet_smooth_noT2 D i j).2.1
        (fun c d => (Work.Diff.STE.B3.goodSet_smooth_noT2 D i j).2.2 a b c d)
        (Work.Diff.STE.B3.tMapFun_injOn_det D i j).1
        (Work.Diff.STE.B3.tMapFun_injOn_det D i j).2
    -- the transfer constants
    choose Ct hCt using fun (i : ι₀) (c d : Fin (Module.finrank ℝ E)) =>
      Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen (ι := Fin (Module.finrank ℝ E)) k
        (by simpa using hk) (T i) (G i c d)
        (hGsm i c d) (hGsupp i c d) (hGcomp i c d) (U i) (hUopen i) (hGsub i c d)
        (fun z _ => (hTsm i).contDiffAt) (hTinj i) (hTdet i)
    have hhom : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E))
        (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        CSq k (fourierCoeff (fun z => ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
          G i c d (z + Work.Diff.STE.iVec m) * u (T i (z + Work.Diff.STE.iVec m))))
          ≤ 2 * Ct i c d * CSq k (fourierCoeff u) :=
      fun i c d => homog_transfer k (Ct i c d) (hCt i c d).1 (T i) (G i c d) (hCt i c d).2
    refine ⟨(Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
      (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        2 * Ct i c d), ?_, ?_⟩
    · have h0 : (0 : ℝ) ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E), 2 * Ct i c d :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
          Finset.sum_nonneg fun d _ => by have := (hCt i c d).1; linarith
      have h1 : (0 : ℝ) ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E)) : ℝ) := by positivity
      exact mul_nonneg h1 h0
    · intro h hsm
      -- the chart components of `J ρ ε h`
      have hRsupp : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          Function.support (D.R i h c d) ⊆
            Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
              Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
        intro i c d z hz
        exact D.psi_supp i (fun h0 => hz (by
          simp only [B3Data.R, h0, zero_mul, mul_zero]))
      have hcomp : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.STruncC ρ ε (D.R i h c d)) ∧
            Work.Diff.STE.Periodic1 (Work.Diff.STE.STruncC ρ ε (D.R i h c d)) :=
        fun i c d => Work.Diff.STE.B3.STruncC_contDiff_periodic ρ hρ ε (D.R i h c d)
          (hsm i c d) (hRsupp i c d)
      -- `D.J ρ ε h` in terms of `STruncC`
      have hJeq : D.J ρ ε h = ∑ i : ι₀, D.Rstar i (fun c d w =>
          (Work.Diff.STE.STruncC ρ ε (D.R i h c d) w).re) := by
        rw [B3Data.J]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
      -- linearity of `R j` in its section argument
      have hRlin : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
          D.R j (D.J ρ ε h) a b w = ∑ i : ι₀,
            D.R j (D.Rstar i (fun c d y =>
              (Work.Diff.STE.STruncC ρ ε (D.R i h c d) y).re)) a b w := by
        intro w
        rw [hJeq]
        simp only [B3Data.R, B3Data.mat, Finset.sum_apply, sum_apply, Finset.mul_sum]
      -- the pointwise expansion of the cross-chart terms
      have hlin : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
          ((D.R j (D.J ρ ε h) a b w : ℝ) : ℂ) = ∑ i : ι₀,
            ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              G i c d w * Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w) := by
        intro w
        rw [hRlin w]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hid i (fun c d y => (Work.Diff.STE.STruncC ρ ε (D.R i h c d) y).re) w]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        have hre : (((Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w)).re : ℝ) : ℂ)
            = Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w) := by
          rw [Work.Diff.STE.STruncC]
          simp [Complex.ofReal_re]
        rw [hre]
      -- the decomposition of the `j`-th component of `J ρ ε h`
      have hpoint : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          D.Rper j (D.J ρ ε h) a b z =
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
                G i c d (z + Work.Diff.STE.iVec m) *
                  Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                    (T i (z + Work.Diff.STE.iVec m)) := by
        intro z
        set N : Fin (Module.finrank ℝ E) → ℤ := fun i => ⌊|z i|⌋ + 2 with hNdef
        set S : Finset (Fin (Module.finrank ℝ E) → ℤ) :=
          Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i)) with hSdef
        have hsupp' : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
            Function.support (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              G i c d w * Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w)) ⊆
              Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
                Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
          intro i c d w hw
          exact hGsupp i c d (fun h0 => hw (by
            show G i c d w * Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w) = 0
            rw [h0, zero_mul]))
        have hzero : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E))
            (m : Fin (Module.finrank ℝ E) → ℤ), m ∉ S →
            G i c d (z + Work.Diff.STE.iVec m) *
              Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                (T i (z + Work.Diff.STE.iVec m)) = 0 := by
          intro i c d m hm
          by_contra hne
          have hmem : ∀ j : Fin (Module.finrank ℝ E),
              m j ∈ Finset.Icc (-(N j)) (N j) := by
            intro j
            have hlt : |m j| < N j := by
              have := Work.Diff.STE.abs_lt_floor_add_two_of_support (hsupp' i c d)
                (x := z) (y := z) (fun j => by rw [sub_self, abs_zero]; norm_num) hne j
              simpa [hNdef] using this
            rw [Finset.mem_Icc]
            have h2 := abs_lt.mp hlt
            exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
          exact hm (by rw [hSdef, Fintype.mem_piFinset]; exact hmem)
        rw [show D.Rper j (D.J ρ ε h) a b z = ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
            ((D.R j (D.J ρ ε h) a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) from rfl]
        rw [tsum_congr (fun m => hlin (z + Work.Diff.STE.iVec m))]
        rw [tsum_finset_sum_eq (f := fun (i : ι₀) (m : Fin (Module.finrank ℝ E) → ℤ) =>
              ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                G i c d (z + Work.Diff.STE.iVec m) *
                  Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                    (T i (z + Work.Diff.STE.iVec m)))
            (fun i m hm => Finset.sum_eq_zero fun c _ =>
              Finset.sum_eq_zero fun d _ => hzero i c d m hm)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [tsum_finset_sum_eq (f := fun (c : Fin (Module.finrank ℝ E))
              (m : Fin (Module.finrank ℝ E) → ℤ) =>
              ∑ d : Fin (Module.finrank ℝ E),
                G i c d (z + Work.Diff.STE.iVec m) *
                  Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                    (T i (z + Work.Diff.STE.iVec m)))
            (fun c m hm => Finset.sum_eq_zero fun d _ => hzero i c d m hm)]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [tsum_finset_sum_eq (f := fun (d : Fin (Module.finrank ℝ E))
              (m : Fin (Module.finrank ℝ E) → ℤ) =>
              G i c d (z + Work.Diff.STE.iVec m) *
                Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                  (T i (z + Work.Diff.STE.iVec m)))
            (fun d m hm => hzero i c d m hm)]
      -- abbreviations for the terms of the finite sum
      set per : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun t =>
        fun z => ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
          G t.1 t.2.1 t.2.2 (z + Work.Diff.STE.iVec m) *
            Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2)
              (T t.1 (z + Work.Diff.STE.iVec m)) with hper_def
      set Ab : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ :=
        fun t => 2 * Ct t.1 t.2.1 t.2.2 with hAb_def
      set Bb : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ :=
        fun t => CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2)))
        with hBb_def
      have hper_t : ∀ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ContDiff ℝ (⊤ : ℕ∞) (per t) ∧ Work.Diff.STE.Periodic1 (per t) := by
        intro t
        rw [hper_def]
        obtain ⟨h1, h2, -⟩ := Work.Diff.STE.periodization_contDiff_periodic
          (fun w => G t.1 t.2.1 t.2.2 w *
            Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2) (T t.1 w))
          ((hGsm t.1 t.2.1 t.2.2).mul ((hcomp t.1 t.2.1 t.2.2).1.comp (hTsm t.1)))
          (fun w hw => hGsupp t.1 t.2.1 t.2.2 (fun h0 => hw (by
            show G t.1 t.2.1 t.2.2 w * Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2)
              (T t.1 w) = 0
            rw [h0, zero_mul])))
        exact ⟨h1, h2⟩
      -- the coefficient family of `Rper j (J ρ ε h) a b`
      have hperVal : ∀ (t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ),
          per t z = ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
            G t.1 t.2.1 t.2.2 (z + Work.Diff.STE.iVec m) *
              Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2)
                (T t.1 (z + Work.Diff.STE.iVec m)) := by
        intro t z
        rw [hper_def]
      have hfun : D.Rper j (D.J ρ ε h) a b = fun z => ∑ t, per t z := by
        funext z
        rw [hpoint]
        refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_congr rfl fun d _ => (hperVal (i, c, d) z).symm).trans ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type]
      have hcoeff : fourierCoeff (D.Rper j (D.J ρ ε h) a b)
          = fun m => ∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              fourierCoeff (per t) m := by
        rw [hfun]
        funext m
        rw [fourierCoeff_finset_sum_of_continuous _ (fun t => (hper_t t).1.continuous) m]
      -- reindexing the finite sums over the product index type
      have hBeq : (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2))))
          = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R i h c d))) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fintype.sum_prod_type]
      have hBeq' : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R i h c d))))
          ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              CSq k (fourierCoeff (D.Rper i h c d)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ =>
          Work.Diff.STE.B3.STruncR_CSq_le ρ hρ ε k (D.R i h c d) (hsm i c d) (hRsupp i c d)
      have hBN : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E), CSq k (fourierCoeff (D.Rper i h c d)))
          = D.BNorm k h := rfl
      -- the bound on the sum of the `Bb`
      have hB : (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Bb t)
          ≤ D.BNorm k h := by
        calc (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Bb t)
            = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R i h c d))) := by
              rw [hBb_def]
              exact hBeq
          _ ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                CSq k (fourierCoeff (D.Rper i h c d)) := hBeq'
          _ = D.BNorm k h := hBN
      -- the chain
      have hh : ∀ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          CSq k (fourierCoeff (per t)) ≤ Ab t * Bb t := by
        intro t
        have := hhom t.1 t.2.1 t.2.2 (Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2))
          (hcomp t.1 t.2.1 t.2.2).1 (hcomp t.1 t.2.1 t.2.2).2
        rw [hper_def, hAb_def, hBb_def]
        exact this
      have hsummand : ∀ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Ab t * Bb t ≤ Ab t * D.BNorm k h := by
        intro t
        have hAb : 0 ≤ Ab t := by
          rw [hAb_def]
          have := (hCt t.1 t.2.1 t.2.2).1
          linarith
        have hBb : Bb t ≤ D.BNorm k h := by
          have h1 : Bb t ≤ ∑ s, Bb s :=
            Finset.single_le_sum (f := fun s => Bb s)
              (fun s _ => by rw [hBb_def]; exact CSq_nonneg k _) (Finset.mem_univ t)
          exact h1.trans hB
        exact mul_le_mul_of_nonneg_left hBb hAb
      have hfin : CSq k (fourierCoeff (D.Rper j (D.J ρ ε h) a b))
          ≤ ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E)) : ℝ) *
              (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ab t))
            * D.BNorm k h := by
        calc CSq k (fourierCoeff (D.Rper j (D.J ρ ε h) a b))
            = CSq k (fun m => ∑ t, fourierCoeff (per t) m) := by rw [hcoeff]
          _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                Fin (Module.finrank ℝ E)) : ℝ) *
              ∑ t, CSq k (fourierCoeff (per t)) :=
              CSq_sum_le k _ (fun t => ?_)
          _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                Fin (Module.finrank ℝ E)) : ℝ) * ∑ t, Ab t * Bb t :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => hh t) (by positivity)
          _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                Fin (Module.finrank ℝ E)) : ℝ) * ((∑ t, Ab t) * D.BNorm k h) :=
              mul_le_mul_of_nonneg_left ?_ (by positivity)
          _ = ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                Fin (Module.finrank ℝ E)) : ℝ) * (∑ t, Ab t)) * D.BNorm k h := by ring
        · exact summable_weighted_fourierCoeff_of_contDiff _ (hper_t t).1 (hper_t t).2 k
        · rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun t _ => hsummand t
      -- translate the constant back
      refine hfin.trans ?_
      have hSbeq : (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ab t)
          = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E), 2 * Ct i c d := by
        rw [hAb_def]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fintype.sum_prod_type]
      have heq : ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E)) : ℝ) * (∑ t, Ab t)) * D.BNorm k h
          = ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E)) : ℝ) *
              (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
                ∑ d : Fin (Module.finrank ℝ E), 2 * Ct i c d)) * D.BNorm k h := by
        rw [hSbeq]
      exact le_of_eq heq
  -- assemble over `(j,a,b)`
  choose Cf hCf using fun (j : ι₀) (a b : Fin (Module.finrank ℝ E)) => hmain j a b
  refine ⟨∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Cf j a b, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => (hCf j a b).1
  · intro h hsm
    rw [show D.BNorm k (D.J ρ ε h) = ∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          CSq k (fourierCoeff (D.Rper j (D.J ρ ε h) a b)) from rfl]
    rw [show (∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Cf j a b) * D.BNorm k h
        = ∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            Cf j a b * D.BNorm k h from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]]
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a _ =>
      Finset.sum_le_sum fun b _ => ?_
    exact (hCf j a b).2 h hsm

end Work.Diff.STE.B3
