import Mathlib
import Submission.Work.Diff.EXT.chartMatBoundsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The induction step for `Work.Diff.EXT.chartMat_bounds_of_christoffel_bounds`

This file proves the analytic core of the chart-matrix bootstrap: if the chart Christoffel entries
`Γ` have uniformly bounded `k`-jets (all orders `≤ k`) and the chart matrix components have
uniformly bounded `k`-jets on `K`, then — using the metric-compatibility identity
`∂_m g_{ij} = Σ_p (Γ^p_{mi} g_{pj} + Γ^p_{mj} g_{ip})` — the chart matrix components have uniformly
bounded `(k+1)`-jets as well.

On the chart target `U` the first derivative of the component `g_{ij}` is the coefficient family
`z ↦ (m ↦ Σ_p (Γ^p_{mi} g_{pj} + Γ^p_{mj} g_{ip})(z))`, so
`‖D^{k+1} g_{ij}‖ = ‖D^k (fderiv g_{ij})‖` is bounded by the sum of the `k`-jets of those
coefficient functions, each of which is bounded by the binomial (Leibniz) bound applied to the
products `Γ · g`.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- Evaluation form of the coordinate expansion map `coordExpCLM`. -/
lemma coordExpCLM_apply_apply (c : Fin (Module.finrank ℝ E) → ℝ) (v : E) :
    coordExpCLM (E := E) c v
      = ∑ m : Fin (Module.finrank ℝ E), c m * ((Module.finBasis ℝ E).coord m) v := by
  simp [coordExpCLM, ContinuousLinearMap.smulRight_apply]

/-- **The binomial bound for a finite sum of two products.** -/
theorem norm_iteratedFDerivWithin_sum_two_mul_le'
    {ι : Type*} (u : Finset ι) {s : Set E} (hs : UniqueDiffOn ℝ s) {x : E} (hx : x ∈ s)
    {k : ℕ} (A B A' B' : ι → E → ℝ)
    (hA : ∀ i ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (A i) s)
    (hB : ∀ i ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (B i) s)
    (hA' : ∀ i ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (A' i) s)
    (hB' : ∀ i ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (B' i) s) :
    ‖iteratedFDerivWithin ℝ k (fun z => ∑ i ∈ u, (A i z * B i z + A' i z * B' i z)) s x‖
      ≤ ∑ i ∈ u,
          ((∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
              ‖iteratedFDerivWithin ℝ j (A i) s x‖ *
              ‖iteratedFDerivWithin ℝ (k - j) (B i) s x‖)
            + (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
              ‖iteratedFDerivWithin ℝ j (A' i) s x‖ *
              ‖iteratedFDerivWithin ℝ (k - j) (B' i) s x‖)) := by
  have hk_le : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
  have h1 : ∀ i ∈ u, ContDiffWithinAt ℝ (k : ℕ∞ω) (fun z => A i z * B i z) s x := by
    intro i hi
    exact (((hA i hi).contDiffWithinAt hx).mul ((hB i hi).contDiffWithinAt hx)).of_le hk_le
  have h2 : ∀ i ∈ u, ContDiffWithinAt ℝ (k : ℕ∞ω) (fun z => A' i z * B' i z) s x := by
    intro i hi
    exact (((hA' i hi).contDiffWithinAt hx).mul ((hB' i hi).contDiffWithinAt hx)).of_le hk_le
  have hsm : ∀ i ∈ u,
      ContDiffWithinAt ℝ (k : ℕ∞ω) (fun z => A i z * B i z + A' i z * B' i z) s x :=
    fun i hi => (h1 i hi).add (h2 i hi)
  rw [iteratedFDerivWithin_fun_sum_apply hs hx hsm]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => ?_))
  have hm1 := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := s) (x := x) (n := k)
    (N := ((⊤ : ℕ∞) : ℕ∞ω)) (hA i hi) (hB i hi) hs hx hk_le
  have hm2 := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := s) (x := x) (n := k)
    (N := ((⊤ : ℕ∞) : ℕ∞ω)) (hA' i hi) (hB' i hi) hs hx hk_le
  rw [fun_iteratedFDerivWithin_add_apply (h1 i hi) (h2 i hi) hs hx]
  exact (norm_add_le _ _).trans (add_le_add hm1 hm2)

/-- The `k`-th binomial moment of two families bounded by `P` and `C` on orders `≤ k`. -/
lemma sum_choose_mul_le {s : Set E} {y : E} {k : ℕ} (A B : E → ℝ) (P C : ℝ)
    (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hA : ∀ k' ≤ k, ‖iteratedFDerivWithin ℝ k' A s y‖ ≤ P)
    (hB : ∀ k' ≤ k, ‖iteratedFDerivWithin ℝ k' B s y‖ ≤ C) :
    (∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j A s y‖ *
          ‖iteratedFDerivWithin ℝ (k - j) B s y‖)
      ≤ (2 : ℝ) ^ k * (P * C) := by
  have h2 : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ) ^ k := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  calc (∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j A s y‖ *
          ‖iteratedFDerivWithin ℝ (k - j) B s y‖)
      ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (P * C) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hkj : k - j ≤ k := Nat.sub_le _ _
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hA j hjk) (hB (k - j) hkj) (norm_nonneg _) hP) (Nat.cast_nonneg _)
    _ = (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) * (P * C) := by rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ k * (P * C) := by rw [h2]

/-- **The first derivative of a chart matrix component**, expanded in the basis of the model
space. -/
lemma fderiv_cmMatEntry_eq (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j : Fin (Module.finrank ℝ E))
    (h : ∀ y ∈ (extChartAt I x₀).target, ∀ m : Fin (Module.finrank ℝ E),
      fderiv ℝ (cmMatEntry (I := I) (M := M) G x₀ t i j) y (Module.finBasis ℝ E m)
        = chartCoef (I := I) (M := M) G x₀ t i j m y) :
    ∀ y ∈ (extChartAt I x₀).target,
      fderiv ℝ (cmMatEntry (I := I) (M := M) G x₀ t i j) y
        = coordExpCLM (E := E) (fun m => chartCoef (I := I) (M := M) G x₀ t i j m y) := by
  intro y hy
  ext v
  have hv : (∑ m : Fin (Module.finrank ℝ E),
      (((Module.finBasis ℝ E).coord m) v) • (Module.finBasis ℝ E m : E)) = v := by
    simpa [Module.Basis.coord_apply] using (Module.Basis.sum_repr (Module.finBasis ℝ E) v).symm
  calc (fderiv ℝ (cmMatEntry (I := I) (M := M) G x₀ t i j) y) v
      = (fderiv ℝ (cmMatEntry (I := I) (M := M) G x₀ t i j) y)
          (∑ m : Fin (Module.finrank ℝ E),
            (((Module.finBasis ℝ E).coord m) v) • Module.finBasis ℝ E m) := by
        conv_lhs => rw [← hv]
    _ = ∑ m : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord m) v) *
            (fderiv ℝ (cmMatEntry (I := I) (M := M) G x₀ t i j) y) (Module.finBasis ℝ E m) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun m _ => by rw [map_smul, smul_eq_mul])
    _ = ∑ m : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord m) v) * chartCoef (I := I) (M := M) G x₀ t i j m y :=
        Finset.sum_congr rfl (fun m _ => by rw [h y hy m])
    _ = (coordExpCLM (E := E) (fun m => chartCoef (I := I) (M := M) G x₀ t i j m y)) v := by
        rw [coordExpCLM_apply_apply]
        exact Finset.sum_congr rfl (fun m _ => by ring)

/-- **The binomial bound for the coefficient of `dy^m` in `∂_m g_{ij}`.** -/
lemma chartCoef_jet_bound
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (k : ℕ) (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hCb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (cmMatEntry (I := I) (M := M) G x₀ t i j) y‖ ≤ C)
    (hPb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (l i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (cGamEntry (I := I) (M := M) G x₀ t l i j) y‖ ≤ P)
    {t : ℝ} (ht : t ∈ Set.Ico σ T) {y : E} (hy : y ∈ K)
    (i j m : Fin (Module.finrank ℝ E)) :
    ‖iteratedFDeriv ℝ k (chartCoef (I := I) (M := M) G x₀ t i j m) y‖
      ≤ 2 * ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * (P * C))) := by
  classical
  have hUopen : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
  have hyU : y ∈ (extChartAt I x₀).target := hKt hy
  obtain ⟨hUCM, hUGam, _⟩ :=
    chartData_contDiffOn (I := I) (M := M) G x₀ (extChartAt I x₀).target subset_rfl
  have hconv : ‖iteratedFDerivWithin ℝ k (chartCoef (I := I) (M := M) G x₀ t i j m)
        (extChartAt I x₀).target y‖
      = ‖iteratedFDeriv ℝ k (chartCoef (I := I) (M := M) G x₀ t i j m) y‖ := by
    rw [iteratedFDerivWithin_of_isOpen k hUopen hyU]
  rw [← hconv]
  have hmain := norm_iteratedFDerivWithin_sum_two_mul_le' (u := Finset.univ)
    (s := (extChartAt I x₀).target) (x := y) hUopen.uniqueDiffOn hyU (k := k)
    (A := fun p : Fin (Module.finrank ℝ E) => cGamEntry (I := I) (M := M) G x₀ t p m i)
    (B := fun p => cmMatEntry (I := I) (M := M) G x₀ t p j)
    (A' := fun p => cGamEntry (I := I) (M := M) G x₀ t p m j)
    (B' := fun p => cmMatEntry (I := I) (M := M) G x₀ t i p)
    (fun p _ => hUGam t m i p) (fun p _ => hUCM t p j)
    (fun p _ => hUGam t m j p) (fun p _ => hUCM t i p)
  have hPw : ∀ (p : Fin (Module.finrank ℝ E)) (k' : ℕ), k' ≤ k →
      ‖iteratedFDerivWithin ℝ k' (cGamEntry (I := I) (M := M) G x₀ t p m i)
        (extChartAt I x₀).target y‖ ≤ P := by
    intro p k' hk'
    rw [iteratedFDerivWithin_of_isOpen k' hUopen hyU]
    exact hPb t ht y hy k' hk' p m i
  have hPw' : ∀ (p : Fin (Module.finrank ℝ E)) (k' : ℕ), k' ≤ k →
      ‖iteratedFDerivWithin ℝ k' (cGamEntry (I := I) (M := M) G x₀ t p m j)
        (extChartAt I x₀).target y‖ ≤ P := by
    intro p k' hk'
    rw [iteratedFDerivWithin_of_isOpen k' hUopen hyU]
    exact hPb t ht y hy k' hk' p m j
  have hCw : ∀ (p : Fin (Module.finrank ℝ E)) (k' : ℕ), k' ≤ k →
      ‖iteratedFDerivWithin ℝ k' (cmMatEntry (I := I) (M := M) G x₀ t p j)
        (extChartAt I x₀).target y‖ ≤ C := by
    intro p k' hk'
    rw [iteratedFDerivWithin_of_isOpen k' hUopen hyU]
    exact hCb t ht y hy k' hk' p j
  have hCw' : ∀ (p : Fin (Module.finrank ℝ E)) (k' : ℕ), k' ≤ k →
      ‖iteratedFDerivWithin ℝ k' (cmMatEntry (I := I) (M := M) G x₀ t i p)
        (extChartAt I x₀).target y‖ ≤ C := by
    intro p k' hk'
    rw [iteratedFDerivWithin_of_isOpen k' hUopen hyU]
    exact hCb t ht y hy k' hk' i p
  calc ‖iteratedFDerivWithin ℝ k (chartCoef (I := I) (M := M) G x₀ t i j m)
        (extChartAt I x₀).target y‖
      ≤ ∑ p : Fin (Module.finrank ℝ E),
          ((∑ j' ∈ Finset.range (k + 1), (k.choose j' : ℝ) *
              ‖iteratedFDerivWithin ℝ j' (cGamEntry (I := I) (M := M) G x₀ t p m i)
                (extChartAt I x₀).target y‖ *
              ‖iteratedFDerivWithin ℝ (k - j') (cmMatEntry (I := I) (M := M) G x₀ t p j)
                (extChartAt I x₀).target y‖)
            + (∑ j' ∈ Finset.range (k + 1), (k.choose j' : ℝ) *
              ‖iteratedFDerivWithin ℝ j' (cGamEntry (I := I) (M := M) G x₀ t p m j)
                (extChartAt I x₀).target y‖ *
              ‖iteratedFDerivWithin ℝ (k - j') (cmMatEntry (I := I) (M := M) G x₀ t i p)
                (extChartAt I x₀).target y‖)) := hmain
    _ ≤ ∑ _p : Fin (Module.finrank ℝ E),
          (((2 : ℝ) ^ k * (P * C)) + ((2 : ℝ) ^ k * (P * C))) := by
        refine Finset.sum_le_sum (fun p _ => add_le_add ?_ ?_)
        · exact sum_choose_mul_le _ _ _ _ hP hC (hPw p) (hCw p)
        · exact sum_choose_mul_le _ _ _ _ hP hC (hPw' p) (hCw' p)
    _ = 2 * ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * (P * C))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The induction step.**  Uniform bounds of order `≤ k` for the Christoffel entries and the
chart matrix components produce a uniform bound of order `k+1` for the chart matrix components. -/
theorem cmMatEntry_succ_bound
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hderiv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (cmMatEntry (I := I) (M := M) G x₀ t i j) y (Module.finBasis ℝ E m)
        = chartCoef (I := I) (M := M) G x₀ t i j m y)
    (k : ℕ) (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hCb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (cmMatEntry (I := I) (M := M) G x₀ t i j) y‖ ≤ C)
    (hPb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (l i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (cGamEntry (I := I) (M := M) G x₀ t l i j) y‖ ≤ P) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ (k + 1) (cmMatEntry (I := I) (M := M) G x₀ t i j) y‖ ≤ C' := by
  classical
  refine ⟨‖coordExpCLM (E := E)‖ * ((Module.finrank ℝ E : ℝ) *
      (2 * ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * (P * C))))), ?_, ?_⟩
  · positivity
  · intro t ht y hy i j
    have hUopen : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
    have hyU : y ∈ (extChartAt I x₀).target := hKt hy
    obtain ⟨hUCM, hUGam, _⟩ :=
      chartData_contDiffOn (I := I) (M := M) G x₀ (extChartAt I x₀).target subset_rfl
    have hcoef : ∀ m : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞)
        (chartCoef (I := I) (M := M) G x₀ t i j m) (extChartAt I x₀).target := by
      intro m
      refine ContDiffOn.sum (fun p _ => ?_)
      exact ((hUGam t m i p).mul (hUCM t p j)).add ((hUGam t m j p).mul (hUCM t i p))
    have hCsm : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => fun m => chartCoef (I := I) (M := M) G x₀ t i j m z) y := by
      rw [contDiffAt_pi]
      intro m
      exact ((hcoef m).contDiffWithinAt hyU).contDiffAt (hUopen.mem_nhds hyU)
    have hk_le : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
    have hfd : fderiv ℝ (cmMatEntry (I := I) (M := M) G x₀ t i j) =ᶠ[𝓝 y]
        (fun z => coordExpCLM (E := E) (fun m => chartCoef (I := I) (M := M) G x₀ t i j m z)) := by
      filter_upwards [hUopen.mem_nhds hyU] with z hz
      exact fderiv_cmMatEntry_eq (I := I) (M := M) G x₀ t i j
        (fun z hz m => hderiv t ht z hz i j m) z hz
    have hbnd : ‖iteratedFDeriv ℝ k
          (fun z => fun m => chartCoef (I := I) (M := M) G x₀ t i j m z) y‖
        ≤ ∑ m : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ k (chartCoef (I := I) (M := M) G x₀ t i j m) y‖ :=
      norm_iteratedFDeriv_pi_le_sum_gen hCsm hk_le
    calc ‖iteratedFDeriv ℝ (k + 1) (cmMatEntry (I := I) (M := M) G x₀ t i j) y‖
        = ‖iteratedFDeriv ℝ k (fderiv ℝ (cmMatEntry (I := I) (M := M) G x₀ t i j)) y‖ :=
          (norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
            (f := cmMatEntry (I := I) (M := M) G x₀ t i j) (x := y) (n := k)).symm
      _ = ‖iteratedFDeriv ℝ k (fun z => coordExpCLM (E := E)
            (fun m => chartCoef (I := I) (M := M) G x₀ t i j m z)) y‖ := by
          rw [(hfd.iteratedFDeriv ℝ k).eq_of_nhds]
      _ = ‖(coordExpCLM (E := E)).compContinuousMultilinearMap
            (iteratedFDeriv ℝ k (fun z => fun m => chartCoef (I := I) (M := M) G x₀ t i j m z) y)‖ := by
          rw [show (fun z : E => coordExpCLM (E := E)
                (fun m => chartCoef (I := I) (M := M) G x₀ t i j m z))
              = ((coordExpCLM (E := E)) ∘
                (fun z => fun m => chartCoef (I := I) (M := M) G x₀ t i j m z)) from rfl]
          rw [ContinuousLinearMap.iteratedFDeriv_comp_left (coordExpCLM (E := E)) hCsm hk_le]
      _ ≤ ‖coordExpCLM (E := E)‖ * ‖iteratedFDeriv ℝ k
            (fun z => fun m => chartCoef (I := I) (M := M) G x₀ t i j m z) y‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le (coordExpCLM (E := E))
            (iteratedFDeriv ℝ k (fun z => fun m => chartCoef (I := I) (M := M) G x₀ t i j m z) y)
      _ ≤ ‖coordExpCLM (E := E)‖ * ∑ m : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ k (chartCoef (I := I) (M := M) G x₀ t i j m) y‖ :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ ≤ ‖coordExpCLM (E := E)‖ * ∑ _m : Fin (Module.finrank ℝ E),
            (2 * ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * (P * C)))) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun m _ =>
              chartCoef_jet_bound (I := I) (M := M) G σ T x₀ K hKt k C P hC hP hCb hPb ht hy i j m))
            (by positivity)
      _ = ‖coordExpCLM (E := E)‖ * ((Module.finrank ℝ E : ℝ) *
            (2 * ((Module.finrank ℝ E : ℝ) * ((2 : ℝ) ^ k * (P * C))))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Work.Diff.EXT
