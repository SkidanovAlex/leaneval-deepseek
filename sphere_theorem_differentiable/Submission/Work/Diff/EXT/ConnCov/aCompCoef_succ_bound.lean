import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aCompCoefDef
import Submission.Work.Diff.EXT.chartMat_fderiv_basis
import Submission.Work.Diff.EXT.chartMat_bounds_of_christoffel_bounds
import Submission.Work.Diff.EXT.chartData_contDiffOn
import Submission.Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

/-!
**The induction step** of `Work.Diff.EXT.ConnCov.chartMat_jets_of_aComp_jets`: uniform bounds of
order `≤ k` for the chart matrix entries, for the Christoffel entries of the *fixed* metric `G 0`
and for the chart array `aComp` of the lowered connection difference produce a uniform bound of
order `k+1` for the chart matrix entries.

The coefficient of the first derivative of the chart matrix is `Work.Diff.EXT.ConnCov.aCompCoef`
(defined in `Submission/Work/Diff/EXT/ConnCov/chartMat_jets_of_aComp_jets.lean`); `hderiv` is the
pointwise identity for it.  The proof is the same as that of
`Work.Diff.EXT.cmMatEntry_succ_bound` (whose auxiliary lemmas
`Work.Diff.EXT.norm_iteratedFDerivWithin_sum_two_mul_le'`,
`Work.Diff.EXT.sum_choose_mul_le` and `Work.Diff.EXT.coordExpCLM_apply_apply` should be reused
verbatim), with the Christoffel coefficient `Work.Diff.EXT.chartCoef` replaced by `aCompCoef`, which
is a sum of the `aComp` entries and of products `(cGam (G 0))·chartMat`; smoothness of the
coefficient on the chart target is supplied by `Work.Diff.EXT.chartData_contDiffOn`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1500000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The chart components of the lowered connection difference are `C^∞` functions of the chart
coordinate on the chart target.  They are sums of products of the chart matrix of `G t` with the
chart Christoffel entries of `G t` and of `G 0`, all of which are smooth on the chart target
(`Work.Diff.EXT.chartData_contDiffOn`). -/
lemma aComp_contDiffOn (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y i j k)
      (extChartAt I x₀).target := by
  obtain ⟨-, hcGam, hGram⟩ :=
    Work.Diff.EXT.chartData_contDiffOn (I := I) (M := M) G x₀ (extChartAt I x₀).target subset_rfl
  unfold Work.Diff.EXT.aComp
  refine ContDiffOn.sum (fun l _ => ?_)
  exact (hGram t k l).mul ((hcGam t i j l).sub (hcGam 0 i j l))

/-- **The first derivative of a chart matrix component**, expanded in the basis of the model space,
with the coefficient `aCompCoef`. -/
lemma fderiv_chartMat_eq (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j : Fin (Module.finrank ℝ E))
    (h : ∀ y ∈ (extChartAt I x₀).target, ∀ m : Fin (Module.finrank ℝ E),
      fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
          (Module.finBasis ℝ E m)
        = Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m y) :
    ∀ y ∈ (extChartAt I x₀).target,
      fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
        = Work.Diff.EXT.coordExpCLM (E := E)
            (fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m y) := by
  intro y hy
  ext v
  have hv : (∑ m : Fin (Module.finrank ℝ E),
      (((Module.finBasis ℝ E).coord m) v) • (Module.finBasis ℝ E m : E)) = v := by
    simpa [Module.Basis.coord_apply] using (Module.Basis.sum_repr (Module.finBasis ℝ E) v).symm
  calc (fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y) v
      = (fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y)
          (∑ m : Fin (Module.finrank ℝ E),
            (((Module.finBasis ℝ E).coord m) v) • Module.finBasis ℝ E m) := by
        conv_lhs => rw [← hv]
    _ = ∑ m : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord m) v) *
            (fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y)
              (Module.finBasis ℝ E m) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun m _ => by rw [map_smul, smul_eq_mul])
    _ = ∑ m : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord m) v)
            * Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m y :=
        Finset.sum_congr rfl (fun m _ => by rw [h y hy m])
    _ = (Work.Diff.EXT.coordExpCLM (E := E)
          (fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m y)) v := by
        rw [Work.Diff.EXT.coordExpCLM_apply_apply]
        exact Finset.sum_congr rfl (fun m _ => by ring)

/-- **The binomial bound for the coefficient `aCompCoef` of `∂_m g_{ij}`**, the analogue of
`Work.Diff.EXT.chartCoef_jet_bound` for the metric-compatibility identity with the Christoffel
symbols of `G t` replaced by the chart array `aComp` of the lowered connection difference and by the
Christoffel symbols of the fixed metric `G 0`.  The coefficient is

`aComp_{mij} + aComp_{mji} + Σ_p (g_{ip}Γ0^p_{mj} + g_{jp}Γ0^p_{mi})`,

whose `k`-jet is bounded by `2·Ac + n·2·(2^k·(P·C))` by additivity and the Leibniz rule. -/
lemma aCompCoef_jet_bound
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (k : ℕ) (C P Ac : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (hAc : 0 ≤ Ac)
    (hCb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖
        ≤ C)
    (hPb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (l i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖ ≤ P)
    (hAcb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖
        ≤ Ac)
    {t : ℝ} (ht : t ∈ Set.Ico σ T) {y : E} (hy : y ∈ K)
    (i j m : Fin (Module.finrank ℝ E)) :
    ‖iteratedFDeriv ℝ k (Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m) y‖
      ≤ 2 * Ac + (Module.finrank ℝ E : ℝ) * (2 * ((2 : ℝ) ^ k * (P * C))) := by
  classical
  have hUopen : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
  have hyU : y ∈ (extChartAt I x₀).target := hKt hy
  have hs : UniqueDiffOn ℝ (extChartAt I x₀).target := hUopen.uniqueDiffOn
  obtain ⟨-, hcGam, hGram⟩ :=
    Work.Diff.EXT.chartData_contDiffOn (I := I) (M := M) G x₀ (extChartAt I x₀).target subset_rfl
  set f1 : E → ℝ := fun z => Work.Diff.EXT.aComp G x₀ t z m i j with hf1
  set f2 : E → ℝ := fun z => Work.Diff.EXT.aComp G x₀ t z m j i with hf2
  set F : E → ℝ := fun z => ∑ p : Fin (Module.finrank ℝ E),
        (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ z) i p
          * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ z) p m j
        + Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ z) j p
          * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ z) p m i) with hF
  have hcoef_eq : Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m
      = (f1 + f2) + F := by
    unfold Work.Diff.EXT.ConnCov.aCompCoef
    rw [hf1, hf2, hF]
    funext z
    simp only [Pi.add_apply]
  have hsm1 : ContDiffOn ℝ (⊤ : ℕ∞) f1 (extChartAt I x₀).target := by
    rw [hf1]
    unfold Work.Diff.EXT.aComp
    refine ContDiffOn.sum (fun l _ => ?_)
    exact (hGram t j l).mul ((hcGam t m i l).sub (hcGam 0 m i l))
  have hsm2 : ContDiffOn ℝ (⊤ : ℕ∞) f2 (extChartAt I x₀).target := by
    rw [hf2]
    unfold Work.Diff.EXT.aComp
    refine ContDiffOn.sum (fun l _ => ?_)
    exact (hGram t i l).mul ((hcGam t m j l).sub (hcGam 0 m j l))
  have hsmF : ContDiffOn ℝ (⊤ : ℕ∞) F (extChartAt I x₀).target := by
    rw [hF]
    refine ContDiffOn.sum (fun p _ => ?_)
    exact ((hGram t i p).mul (hcGam 0 m j p)).add ((hGram t j p).mul (hcGam 0 m i p))
  have hk_le : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
  have h1' : ContDiffWithinAt ℝ (k : ℕ∞ω) f1 (extChartAt I x₀).target y :=
    (hsm1.contDiffWithinAt hyU).of_le hk_le
  have h2' : ContDiffWithinAt ℝ (k : ℕ∞ω) f2 (extChartAt I x₀).target y :=
    (hsm2.contDiffWithinAt hyU).of_le hk_le
  have hF' : ContDiffWithinAt ℝ (k : ℕ∞ω) F (extChartAt I x₀).target y :=
    (hsmF.contDiffWithinAt hyU).of_le hk_le
  have eadd1 : iteratedFDerivWithin ℝ k (f1 + f2) (extChartAt I x₀).target y
      = iteratedFDerivWithin ℝ k f1 (extChartAt I x₀).target y
        + iteratedFDerivWithin ℝ k f2 (extChartAt I x₀).target y :=
    iteratedFDerivWithin_add_apply h1' h2' hs hyU
  have eadd2 : iteratedFDerivWithin ℝ k ((f1 + f2) + F) (extChartAt I x₀).target y
      = iteratedFDerivWithin ℝ k (f1 + f2) (extChartAt I x₀).target y
        + iteratedFDerivWithin ℝ k F (extChartAt I x₀).target y :=
    iteratedFDerivWithin_add_apply (h1'.add h2') hF' hs hyU
  have hb1 : ‖iteratedFDerivWithin ℝ k f1 (extChartAt I x₀).target y‖ ≤ Ac := by
    rw [hf1, iteratedFDerivWithin_of_isOpen k hUopen hyU]
    exact hAcb t ht y hy k le_rfl m i j
  have hb2 : ‖iteratedFDerivWithin ℝ k f2 (extChartAt I x₀).target y‖ ≤ Ac := by
    rw [hf2, iteratedFDerivWithin_of_isOpen k hUopen hyU]
    exact hAcb t ht y hy k le_rfl m j i
  have hFb : ‖iteratedFDerivWithin ℝ k F (extChartAt I x₀).target y‖
      ≤ (Module.finrank ℝ E : ℝ) * (2 * ((2 : ℝ) ^ k * (P * C))) := by
    rw [hF]
    have hmain := Work.Diff.EXT.norm_iteratedFDerivWithin_sum_two_mul_le' (u := Finset.univ)
      (s := (extChartAt I x₀).target) (x := y) hs hyU (k := k)
      (A := fun p : Fin (Module.finrank ℝ E) => fun z : E =>
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ z) i p)
      (B := fun p => fun z => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ z) p m j)
      (A' := fun p => fun z => Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ z) j p)
      (B' := fun p => fun z => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ z) p m i)
      (fun p _ => hGram t i p) (fun p _ => hcGam 0 m j p)
      (fun p _ => hGram t j p) (fun p _ => hcGam 0 m i p)
    have hper : ∀ p : Fin (Module.finrank ℝ E),
        (∑ jj ∈ Finset.range (k + 1), (k.choose jj : ℝ) *
              ‖iteratedFDerivWithin ℝ jj (fun z : E => Work.Diff.GE.GramM G x₀ t
                (Work.Diff.EXT.pt (I := I) x₀ z) i p) (extChartAt I x₀).target y‖ *
            ‖iteratedFDerivWithin ℝ (k - jj) (fun z : E => Work.Diff.GE.cGam (G 0) x₀
                (Work.Diff.EXT.pt (I := I) x₀ z) p m j) (extChartAt I x₀).target y‖
          + ∑ jj ∈ Finset.range (k + 1), (k.choose jj : ℝ) *
              ‖iteratedFDerivWithin ℝ jj (fun z : E => Work.Diff.GE.GramM G x₀ t
                (Work.Diff.EXT.pt (I := I) x₀ z) j p) (extChartAt I x₀).target y‖ *
            ‖iteratedFDerivWithin ℝ (k - jj) (fun z : E => Work.Diff.GE.cGam (G 0) x₀
                (Work.Diff.EXT.pt (I := I) x₀ z) p m i) (extChartAt I x₀).target y‖)
        ≤ (2 : ℝ) ^ k * (C * P) + (2 : ℝ) ^ k * (C * P) := by
      intro p
      refine add_le_add ?_ ?_
      · refine Work.Diff.EXT.sum_choose_mul_le _ _ C P hC hP (fun k' hk' => ?_) (fun k' hk' => ?_)
        · rw [iteratedFDerivWithin_of_isOpen k' hUopen hyU]
          exact hCb t ht y hy k' hk' i p
        · rw [iteratedFDerivWithin_of_isOpen k' hUopen hyU]
          exact hPb t ht y hy k' hk' p m j
      · refine Work.Diff.EXT.sum_choose_mul_le _ _ C P hC hP (fun k' hk' => ?_) (fun k' hk' => ?_)
        · rw [iteratedFDerivWithin_of_isOpen k' hUopen hyU]
          exact hCb t ht y hy k' hk' j p
        · rw [iteratedFDerivWithin_of_isOpen k' hUopen hyU]
          exact hPb t ht y hy k' hk' p m i
    refine hmain.trans ?_
    refine (Finset.sum_le_sum (fun p _ => hper p)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  calc ‖iteratedFDeriv ℝ k (Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m) y‖
      = ‖iteratedFDerivWithin ℝ k (Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m)
          (extChartAt I x₀).target y‖ := by
        rw [iteratedFDerivWithin_of_isOpen k hUopen hyU]
    _ = ‖iteratedFDerivWithin ℝ k ((f1 + f2) + F) (extChartAt I x₀).target y‖ := by rw [hcoef_eq]
    _ = ‖iteratedFDerivWithin ℝ k (f1 + f2) (extChartAt I x₀).target y
          + iteratedFDerivWithin ℝ k F (extChartAt I x₀).target y‖ := by rw [eadd2]
    _ ≤ ‖iteratedFDerivWithin ℝ k (f1 + f2) (extChartAt I x₀).target y‖
          + ‖iteratedFDerivWithin ℝ k F (extChartAt I x₀).target y‖ := norm_add_le _ _
    _ = ‖iteratedFDerivWithin ℝ k f1 (extChartAt I x₀).target y
            + iteratedFDerivWithin ℝ k f2 (extChartAt I x₀).target y‖
          + ‖iteratedFDerivWithin ℝ k F (extChartAt I x₀).target y‖ := by rw [eadd1]
    _ ≤ (‖iteratedFDerivWithin ℝ k f1 (extChartAt I x₀).target y‖
            + ‖iteratedFDerivWithin ℝ k f2 (extChartAt I x₀).target y‖)
          + ‖iteratedFDerivWithin ℝ k F (extChartAt I x₀).target y‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (Ac + Ac) + (Module.finrank ℝ E : ℝ) * (2 * ((2 : ℝ) ^ k * (P * C))) :=
        add_le_add (add_le_add hb1 hb2) hFb
    _ = 2 * Ac + (Module.finrank ℝ E : ℝ) * (2 * ((2 : ℝ) ^ k * (P * C))) := by ring

end

theorem aCompCoef_succ_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hderiv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
          (Module.finBasis ℝ E m)
        = Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m y)
    (k : ℕ) (C P Ac : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (hAc : 0 ≤ Ac)
    (hCb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖
        ≤ C)
    (hPb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (l i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖ ≤ P)
    (hAcb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖
        ≤ Ac) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ (k + 1)
        (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C' := by
  classical
  refine ⟨‖Work.Diff.EXT.coordExpCLM (E := E)‖ * ((Module.finrank ℝ E : ℝ) *
      (2 * Ac + (Module.finrank ℝ E : ℝ) * (2 * ((2 : ℝ) ^ k * (P * C))))), ?_, ?_⟩
  · positivity
  · intro t ht y hy i j
    have hUopen : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
    have hyU : y ∈ (extChartAt I x₀).target := hKt hy
    obtain ⟨-, hcGam, hGram⟩ :=
      Work.Diff.EXT.chartData_contDiffOn (I := I) (M := M) G x₀ (extChartAt I x₀).target subset_rfl
    have hcoef : ∀ m : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞)
        (Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m)
        (extChartAt I x₀).target := by
      intro m
      unfold Work.Diff.EXT.ConnCov.aCompCoef
      refine ContDiffOn.add ?_ ?_
      · exact (aComp_contDiffOn (I := I) (M := M) G x₀ t m i j).add
          (aComp_contDiffOn (I := I) (M := M) G x₀ t m j i)
      · refine ContDiffOn.sum (fun p _ => ?_)
        exact ((hGram t i p).mul (hcGam 0 m j p)).add ((hGram t j p).mul (hcGam 0 m i p))
    have hCsm : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m z) y := by
      rw [contDiffAt_pi]
      intro m
      exact ((hcoef m).contDiffWithinAt hyU).contDiffAt (hUopen.mem_nhds hyU)
    have hk_le : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
    have hfd : fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j)
        =ᶠ[𝓝 y]
        (fun z => Work.Diff.EXT.coordExpCLM (E := E)
          (fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m z)) := by
      filter_upwards [hUopen.mem_nhds hyU] with z hz
      exact fderiv_chartMat_eq (I := I) (M := M) G x₀ t i j
        (fun z hz m => hderiv t ht z hz i j m) z hz
    have hbnd : ‖iteratedFDeriv ℝ k
          (fun z => fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m z) y‖
        ≤ ∑ m : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ k (Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m) y‖ :=
      Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum_gen hCsm hk_le
    calc ‖iteratedFDeriv ℝ (k + 1)
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖
        = ‖iteratedFDeriv ℝ k
            (fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j)) y‖ :=
          (norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
            (f := fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j)
            (x := y) (n := k)).symm
      _ = ‖iteratedFDeriv ℝ k (fun z => Work.Diff.EXT.coordExpCLM (E := E)
            (fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m z)) y‖ := by
          rw [(hfd.iteratedFDeriv ℝ k).eq_of_nhds]
      _ = ‖(Work.Diff.EXT.coordExpCLM (E := E)).compContinuousMultilinearMap
            (iteratedFDeriv ℝ k
              (fun z => fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m z)
              y)‖ := by
          rw [show (fun z : E => Work.Diff.EXT.coordExpCLM (E := E)
                (fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m z))
              = ((Work.Diff.EXT.coordExpCLM (E := E)) ∘
                (fun z => fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m z))
                from rfl]
          rw [ContinuousLinearMap.iteratedFDeriv_comp_left (Work.Diff.EXT.coordExpCLM (E := E)) hCsm hk_le]
      _ ≤ ‖Work.Diff.EXT.coordExpCLM (E := E)‖ * ‖iteratedFDeriv ℝ k
            (fun z => fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m z) y‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le (Work.Diff.EXT.coordExpCLM (E := E))
            (iteratedFDeriv ℝ k
              (fun z => fun m => Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m z) y)
      _ ≤ ‖Work.Diff.EXT.coordExpCLM (E := E)‖ * ∑ m : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ k (Work.Diff.EXT.ConnCov.aCompCoef (I := I) (M := M) G x₀ t i j m) y‖ :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ ≤ ‖Work.Diff.EXT.coordExpCLM (E := E)‖ * ∑ _m : Fin (Module.finrank ℝ E),
            (2 * Ac + (Module.finrank ℝ E : ℝ) * (2 * ((2 : ℝ) ^ k * (P * C)))) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun m _ =>
              aCompCoef_jet_bound (I := I) (M := M) G σ T x₀ K hKt k C P Ac hC hP hAc
                hCb hPb hAcb ht hy i j m)) (by positivity)
      _ = ‖Work.Diff.EXT.coordExpCLM (E := E)‖ * ((Module.finrank ℝ E : ℝ) *
            (2 * Ac + (Module.finrank ℝ E : ℝ) * (2 * ((2 : ℝ) ^ k * (P * C))))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Work.Diff.EXT.ConnCov
