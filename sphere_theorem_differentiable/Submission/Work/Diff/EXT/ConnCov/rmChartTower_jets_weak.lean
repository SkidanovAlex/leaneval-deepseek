import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.ConnCov.fderiv_rmChartTower_eq
import Submission.Work.Diff.EXT.ConnCov.chrCoord_contDiffAt
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_succ_le_basisSum_fderiv
import Submission.Work.Diff.EXT.chartData_step_aux
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_le_basisSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Jet bounds for the chart recursion of the moving curvature tower (weak Christoffel hypothesis)

`Work.Diff.EXT.ConnCov.rmChartTower` is the chart recursion for the iterated *moving* covariant
derivatives of the curvature (`∇^{G t, m}Rm`).  This file proves that the chart jets of the tower
levels are bounded on `K'` as soon as

* the *values* of all tower levels `m ≤ Mm` are bounded (`hval`),
* the chart jets of the Christoffel symbols `chrCoord` up to order `Mm - 1` are bounded (`hchr`),
* every tower level `m ≤ Mm` is smooth in the chart coordinate at each point of `K'` (`hsm`).

This is the statement needed by `Work.Diff.EXT.ConnCov.dAOfTower_chart_bound` and friends, where
the Christoffel jets are only available one order below the tower levels: bounding the `J`-th chart
derivative of a tower level `m` with `m + J ≤ Mm` trades each chart derivative for one tower level
*(and never for a derivative of `chrCoord` of order `J`)*.  Concretely, writing the recursion as

  `∂_a (level m) = level (m+1) + (Christoffel contractions of level m)`,

the `J`-th jet of `level m` sees tower levels up to `m + J ≤ Mm` and `chrCoord` derivatives only up
to order `J - 1 ≤ Mm - 1`.  The induction is on the order `J` of the chart derivative: products of
`chrCoord` with tower levels are handled by the Leibniz rule, the chart derivative in a general
direction by the expansion of the `(E →L ℝ)`-valued derivative in the canonical basis of `E`, and
the induction bottoms out at `J = 0`, where `hval` applies.

The proof is the same as that of `Work.Diff.EXT.ConnCov.rmChartTower_jets` (which assumes the
stronger `hchr` for `J ≤ Mm`); the extra order of `hchr` is never used there.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]




/-- **Leibniz bound with a common constant.**  If `f` and `g` are smooth at `x` and all their
iterated derivatives up to order `J` are bounded by `Cχ` resp. `CL`, then the `J`-th derivative of
the product is bounded by `2^J · max Cχ CL · max Cχ CL`. -/
private lemma jet_mul_le_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {x : E} {J : ℕ} {Cχ CL : ℝ} {f g : E → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hCf : ∀ k ≤ J, ‖iteratedFDeriv ℝ k f x‖ ≤ Cχ)
    (hCg : ∀ k ≤ J, ‖iteratedFDeriv ℝ k g x‖ ≤ CL) :
    ‖iteratedFDeriv ℝ J (fun z => f z * g z) x‖
      ≤ (2 : ℝ) ^ J * max Cχ CL * max Cχ CL := by
  have hCχ0 : 0 ≤ Cχ := le_trans (norm_nonneg _) (hCf 0 (Nat.zero_le J))
  have hCL0 : 0 ≤ CL := le_trans (norm_nonneg _) (hCg 0 (Nat.zero_le J))
  have hB0 : 0 ≤ max Cχ CL := le_trans hCχ0 (le_max_left _ _)
  exact Work.Diff.EXT.norm_iteratedFDeriv_mul_le_at_le (k := J) (m := J) le_rfl hf hg hB0
    (fun i hi => le_trans (hCf i hi) (le_max_left _ _))
    (fun i hi => le_trans (hCg i hi) (le_max_right _ _))

/-- **Jet bound for a finite sum of products.**  If every factor of every summand has all its jets
up to order `J` bounded by a common constant, the same holds for the sum. -/
private lemma jets_sum_prod_le_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {ι : Type*} [Fintype ι] {x : E} {J : ℕ} {Cχ CL : ℝ}
    (χ : ι → E → ℝ) (lam : ι → E → ℝ)
    (hχsm : ∀ i, ContDiffAt ℝ (⊤ : ℕ∞) (χ i) x)
    (hlamsm : ∀ i, ContDiffAt ℝ (⊤ : ℕ∞) (lam i) x)
    (hχb : ∀ i, ∀ k ≤ J, ‖iteratedFDeriv ℝ k (χ i) x‖ ≤ Cχ)
    (hlamb : ∀ i, ∀ k ≤ J, ‖iteratedFDeriv ℝ k (lam i) x‖ ≤ CL) :
    ‖iteratedFDeriv ℝ J (fun z => ∑ i, χ i z * lam i z) x‖
      ≤ (Fintype.card ι : ℝ) * ((2 : ℝ) ^ J * max Cχ CL * max Cχ CL) := by
  refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_sum_le_at (s := Finset.univ)
    (φ := fun i z => χ i z * lam i z) (x := x) (n := J)
    (C := (2 : ℝ) ^ J * max Cχ CL * max Cχ CL)
    (fun i _ => (hχsm i).mul (hlamsm i))
    (fun i _ => jet_mul_le_at (hχsm i) (hlamsm i) (hχb i) (hlamb i))) ?_
  rw [Finset.card_univ]

/-- **Additivity of the `J`-th jet for six summands.** -/
private lemma norm_iteratedFDeriv_add6_le_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {x : E} {J : ℕ} {f1 f2 f3 f4 f5 f6 : E → ℝ} {C1 C2 C3 C4 C5 C6 : ℝ}
    (h1 : ContDiffAt ℝ (⊤ : ℕ∞) f1 x) (h2 : ContDiffAt ℝ (⊤ : ℕ∞) f2 x)
    (h3 : ContDiffAt ℝ (⊤ : ℕ∞) f3 x) (h4 : ContDiffAt ℝ (⊤ : ℕ∞) f4 x)
    (h5 : ContDiffAt ℝ (⊤ : ℕ∞) f5 x) (h6 : ContDiffAt ℝ (⊤ : ℕ∞) f6 x)
    (hb1 : ‖iteratedFDeriv ℝ J f1 x‖ ≤ C1) (hb2 : ‖iteratedFDeriv ℝ J f2 x‖ ≤ C2)
    (hb3 : ‖iteratedFDeriv ℝ J f3 x‖ ≤ C3) (hb4 : ‖iteratedFDeriv ℝ J f4 x‖ ≤ C4)
    (hb5 : ‖iteratedFDeriv ℝ J f5 x‖ ≤ C5) (hb6 : ‖iteratedFDeriv ℝ J f6 x‖ ≤ C6) :
    ‖iteratedFDeriv ℝ J (fun z => f1 z + f2 z + f3 z + f4 z + f5 z + f6 z) x‖
      ≤ C1 + C2 + C3 + C4 + C5 + C6 := by
  have h12sm : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => f1 z + f2 z) x := h1.add h2
  have h12b : ‖iteratedFDeriv ℝ J (fun z => f1 z + f2 z) x‖ ≤ C1 + C2 :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ h1 h2 hb1 hb2
  have h123sm : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => f1 z + f2 z + f3 z) x := h12sm.add h3
  have h123b : ‖iteratedFDeriv ℝ J (fun z => f1 z + f2 z + f3 z) x‖ ≤ C1 + C2 + C3 :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ h12sm h3 h12b hb3
  have h1234sm : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => f1 z + f2 z + f3 z + f4 z) x := h123sm.add h4
  have h1234b : ‖iteratedFDeriv ℝ J (fun z => f1 z + f2 z + f3 z + f4 z) x‖
      ≤ C1 + C2 + C3 + C4 :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ h123sm h4 h123b hb4
  have h12345sm : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => f1 z + f2 z + f3 z + f4 z + f5 z) x :=
    h1234sm.add h5
  have h12345b : ‖iteratedFDeriv ℝ J (fun z => f1 z + f2 z + f3 z + f4 z + f5 z) x‖
      ≤ C1 + C2 + C3 + C4 + C5 :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ h1234sm h5 h1234b hb5
  exact Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ h12345sm h6 h12345b hb6

/-- **Jet bounds for the chart recursion of the curvature tower, with the Christoffel jets only up
to order `Mm - 1`.**  The chart jets of order `J ≤ Mm` of the tower levels `m ≤ Mm - J` are bounded
by a uniform constant on the compact-ish set `K'` (a subset of the chart target), assuming the
values of the tower levels `m ≤ Mm` are bounded, the chart jets of `chrCoord` up to order
`Mm - 1` are bounded, and every tower level is smooth at every point of `K'`. -/
theorem rmChartTower_jets_weak
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (σ T : ℝ) (K' : Set E) (Mm : ℕ)
    (hK't : K' ⊆ (extChartAt I x₀).target)
    (hval : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ m : ℕ, m ≤ Mm →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        |Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v i j k l y| ≤ C)
    (hchr : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ J : ℕ, J ≤ Mm - 1 →
      ∀ (p a b : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ J (fun y' : E => Work.Diff.GE.chrCoord (I := I) G x₀ p a b t
            (Work.Diff.EXT.pt (I := I) x₀ y')) y‖ ≤ C)
    (hsm : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ m : ℕ, m ≤ Mm →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E)),
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v i j k l y') y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ J : ℕ, J ≤ Mm → ∀ m : ℕ, m ≤ Mm - J →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ J
          (fun y' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v i j k l y') y‖ ≤ C := by
  classical
  obtain ⟨Cv, hCv0, hCv⟩ := hval
  obtain ⟨Cχ, hCχ0, hCχ⟩ := hchr
  obtain ⟨Cb, hCb0, hCb⟩ := Work.Diff.EXT.norm_iteratedFDeriv_succ_le_basisSum_fderiv (E := E) (Mm + 1)
  have key : ∀ J : ℕ, J ≤ Mm → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ i ≤ J, ∀ m, m ≤ Mm - J →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (a b c d : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ i (fun y' : E =>
          Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v a b c d y') y‖ ≤ B := by
    intro J
    induction J with
    | zero =>
      intro _
      refine ⟨max 1 Cv, le_trans zero_le_one (le_max_left _ _), ?_⟩
      intro t ht y hy i hi m hm v a b c d
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact le_trans (hCv t ht m hm v a b c d y hy) (le_max_right _ _)
    | succ J ih =>
      intro hJ1
      have hJ : J ≤ Mm := by omega
      have hJm : J ≤ Mm - 1 := by omega
      obtain ⟨BJ, hBJ0, hBJ⟩ := ih hJ
      -- ### constants
      set Cz : ℝ := max 1 Cχ with hCzdef
      have hCz1 : 1 ≤ Cz := le_max_left _ _
      have hCz0 : 0 ≤ Cz := le_trans zero_le_one hCz1
      have hCχCz : Cχ ≤ Cz := le_max_right _ _
      set Bm : ℝ := max Cz BJ with hBmdef
      have hBm0 : 0 ≤ Bm := le_trans hCz0 (le_max_left _ _)
      have hCzBm : Cz ≤ Bm := le_max_left _ _
      have hBJBm : BJ ≤ Bm := le_max_right _ _
      set X : ℝ := (2 : ℝ) ^ J * Bm * Bm with hXdef
      have hX0 : 0 ≤ X := by rw [hXdef]; positivity
      set NT : ℝ := (Module.finrank ℝ E : ℝ) with hNTdef
      have hNT0 : 0 ≤ NT := by rw [hNTdef]; positivity
      set NB : ℝ := ((Mm : ℝ) + 4) * NT with hNBdef
      have hNB0 : 0 ≤ NB := by rw [hNBdef]; positivity
      set Bψ : ℝ := BJ + NB * X with hBψdef
      have hBψ0 : 0 ≤ Bψ := by rw [hBψdef]; positivity
      set B' : ℝ := max BJ (Cb * (NT * Bψ)) with hB'def
      have hB'0 : 0 ≤ B' := le_trans hBJ0 (le_max_left _ _)
      refine ⟨B', hB'0, ?_⟩
      intro t ht y hy i hi m hm v a b c d
      rcases lt_or_eq_of_le hi with hlt | heq
      · exact le_trans (hBJ t ht y hy i (by omega) m (by omega) v a b c d) (le_max_left _ _)
      · subst heq
        have hmJ : m ≤ Mm - J := by omega
        have hm1 : m + 1 ≤ Mm - J := by omega
        have hLsm : ContDiffAt ℝ (⊤ : ℕ∞)
            (fun z : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t
              m v a b c d z) y :=
          hsm t ht y hy m (by omega) v a b c d
        -- ### the basis expansion of the `(J+1)`-st jet
        have h1 : ‖iteratedFDeriv ℝ (J + 1)
              (fun z : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t
                m v a b c d z) y‖
            ≤ Cb * ∑ a' : Fin (Module.finrank ℝ E),
              ‖iteratedFDeriv ℝ J (fun z : E =>
                fderiv ℝ (fun z' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M)
                  G x₀ t m v a b c d z') z (Work.Diff.GE.cBasis (E := E) a')) y‖ := by
          have h := hCb J (by omega)
            (fun z : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v a b c d z)
            y hLsm
          simpa only [Work.Diff.GE.cBasis] using h
        -- ### the bound for one summand
        have h2 : ∀ a' : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ J (fun z : E =>
              fderiv ℝ (fun z' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M)
                G x₀ t m v a b c d z') z (Work.Diff.GE.cBasis (E := E) a')) y‖ ≤ Bψ := by
          intro a'
          have hrec0 := Work.Diff.EXT.ConnCov.fderiv_rmChartTower_eq (I := I) (M := M) G x₀ t m v
            a' a b c d
          set T1 : E → ℝ := fun z : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t
            (m + 1) (Fin.cons a' v) a b c d z with hT1def
          set S1 : E → ℝ := fun z : E => ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p a' (v r) t (Work.Diff.EXT.pt (I := I) x₀ z)
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (Function.update v r p) a b c d z with hS1def
          set S2 : E → ℝ := fun z : E => ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p a' a t (Work.Diff.EXT.pt (I := I) x₀ z)
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v p b c d z
            with hS2def
          set S3 : E → ℝ := fun z : E => ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p a' b t (Work.Diff.EXT.pt (I := I) x₀ z)
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v a p c d z
            with hS3def
          set S4 : E → ℝ := fun z : E => ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p a' c t (Work.Diff.EXT.pt (I := I) x₀ z)
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v a b p d z
            with hS4def
          set S5 : E → ℝ := fun z : E => ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.chrCoord (I := I) G x₀ p a' d t (Work.Diff.EXT.pt (I := I) x₀ z)
              * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v a b c p z
            with hS5def
          have hrec : (fun z : E => fderiv ℝ (fun z' : E => Work.Diff.EXT.ConnCov.rmChartTower
                (I := I) (M := M) G x₀ t m v a b c d z') z (Work.Diff.GE.cBasis (E := E) a'))
              = fun z : E => T1 z + S1 z + S2 z + S3 z + S4 z + S5 z := by
            rw [hT1def, hS1def, hS2def, hS3def, hS4def, hS5def]
            exact hrec0
          rw [hrec]
          -- smoothness of the six pieces
          have hT1sm : ContDiffAt ℝ (⊤ : ℕ∞) T1 y := by
            rw [hT1def]
            exact hsm t ht y hy (m + 1) (by omega) (Fin.cons a' v) a b c d
          have hS1sm : ContDiffAt ℝ (⊤ : ℕ∞) S1 y := by
            rw [hS1def]
            refine ContDiffAt.sum (s := Finset.univ) fun r _ =>
              ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
            exact (Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy)
              p a' (v r)).mul (hsm t ht y hy m (by omega) (Function.update v r p) a b c d)
          have hS2sm : ContDiffAt ℝ (⊤ : ℕ∞) S2 y := by
            rw [hS2def]
            refine ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
            exact (Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy)
              p a' a).mul (hsm t ht y hy m (by omega) v p b c d)
          have hS3sm : ContDiffAt ℝ (⊤ : ℕ∞) S3 y := by
            rw [hS3def]
            refine ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
            exact (Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy)
              p a' b).mul (hsm t ht y hy m (by omega) v a p c d)
          have hS4sm : ContDiffAt ℝ (⊤ : ℕ∞) S4 y := by
            rw [hS4def]
            refine ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
            exact (Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy)
              p a' c).mul (hsm t ht y hy m (by omega) v a b p d)
          have hS5sm : ContDiffAt ℝ (⊤ : ℕ∞) S5 y := by
            rw [hS5def]
            refine ContDiffAt.sum (s := Finset.univ) fun p _ => ?_
            exact (Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy)
              p a' d).mul (hsm t ht y hy m (by omega) v a b c p)
          -- the jet bounds of the six pieces
          have hT1b : ‖iteratedFDeriv ℝ J T1 y‖ ≤ BJ := by
            rw [hT1def]
            exact hBJ t ht y hy J le_rfl (m + 1) hm1 (Fin.cons a' v) a b c d
          have hS1b : ‖iteratedFDeriv ℝ J S1 y‖ ≤ (m : ℝ) * (NT * X) := by
            rw [hS1def]
            refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_sum_le_at (s := Finset.univ)
              (φ := fun r : Fin m => fun z : E => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.chrCoord (I := I) G x₀ p a' (v r) t (Work.Diff.EXT.pt (I := I) x₀ z)
                  * Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                      (Function.update v r p) a b c d z)
              (x := y) (n := J) (C := NT * X) ?_ ?_) ?_
            · intro r _
              exact ContDiffAt.sum (s := Finset.univ) fun p _ =>
                (Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t (hK't hy)
                  p a' (v r)).mul (hsm t ht y hy m (by omega) (Function.update v r p) a b c d)
            · intro r _
              refine le_trans (jets_sum_prod_le_at (x := y) (J := J) (Cχ := Cz) (CL := BJ)
                (χ := fun p z => Work.Diff.GE.chrCoord (I := I) G x₀ p a' (v r) t
                  (Work.Diff.EXT.pt (I := I) x₀ z))
                (lam := fun p z => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                  (Function.update v r p) a b c d z)
                (fun p => Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t
                  (hK't hy) p a' (v r))
                (fun p => hsm t ht y hy m (by omega) (Function.update v r p) a b c d)
                (fun p k hk => le_trans (hCχ t ht k (le_trans hk hJm) p a' (v r) y hy) hCχCz)
                (fun p k hk => hBJ t ht y hy k hk m hmJ (Function.update v r p) a b c d)) ?_
              refine le_of_eq ?_
              simp only [Fintype.card_fin, hNTdef, hBmdef, hXdef]
            · have hcard : (Finset.univ : Finset (Fin m)).card = m := by
                rw [Finset.card_univ, Fintype.card_fin]
              rw [hcard]
          have hS2b : ‖iteratedFDeriv ℝ J S2 y‖ ≤ NT * X := by
            rw [hS2def]
            refine le_trans (jets_sum_prod_le_at (x := y) (J := J) (Cχ := Cz) (CL := BJ)
              (χ := fun p z => Work.Diff.GE.chrCoord (I := I) G x₀ p a' a t
                (Work.Diff.EXT.pt (I := I) x₀ z))
              (lam := fun p z => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                v p b c d z)
              (fun p => Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t
                (hK't hy) p a' a)
              (fun p => hsm t ht y hy m (by omega) v p b c d)
              (fun p k hk => le_trans (hCχ t ht k (le_trans hk hJm) p a' a y hy) hCχCz)
              (fun p k hk => hBJ t ht y hy k hk m hmJ v p b c d)) ?_
            refine le_of_eq ?_
            simp only [Fintype.card_fin, hNTdef, hBmdef, hXdef]
          have hS3b : ‖iteratedFDeriv ℝ J S3 y‖ ≤ NT * X := by
            rw [hS3def]
            refine le_trans (jets_sum_prod_le_at (x := y) (J := J) (Cχ := Cz) (CL := BJ)
              (χ := fun p z => Work.Diff.GE.chrCoord (I := I) G x₀ p a' b t
                (Work.Diff.EXT.pt (I := I) x₀ z))
              (lam := fun p z => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                v a p c d z)
              (fun p => Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t
                (hK't hy) p a' b)
              (fun p => hsm t ht y hy m (by omega) v a p c d)
              (fun p k hk => le_trans (hCχ t ht k (le_trans hk hJm) p a' b y hy) hCχCz)
              (fun p k hk => hBJ t ht y hy k hk m hmJ v a p c d)) ?_
            refine le_of_eq ?_
            simp only [Fintype.card_fin, hNTdef, hBmdef, hXdef]
          have hS4b : ‖iteratedFDeriv ℝ J S4 y‖ ≤ NT * X := by
            rw [hS4def]
            refine le_trans (jets_sum_prod_le_at (x := y) (J := J) (Cχ := Cz) (CL := BJ)
              (χ := fun p z => Work.Diff.GE.chrCoord (I := I) G x₀ p a' c t
                (Work.Diff.EXT.pt (I := I) x₀ z))
              (lam := fun p z => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                v a b p d z)
              (fun p => Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t
                (hK't hy) p a' c)
              (fun p => hsm t ht y hy m (by omega) v a b p d)
              (fun p k hk => le_trans (hCχ t ht k (le_trans hk hJm) p a' c y hy) hCχCz)
              (fun p k hk => hBJ t ht y hy k hk m hmJ v a b p d)) ?_
            refine le_of_eq ?_
            simp only [Fintype.card_fin, hNTdef, hBmdef, hXdef]
          have hS5b : ‖iteratedFDeriv ℝ J S5 y‖ ≤ NT * X := by
            rw [hS5def]
            refine le_trans (jets_sum_prod_le_at (x := y) (J := J) (Cχ := Cz) (CL := BJ)
              (χ := fun p z => Work.Diff.GE.chrCoord (I := I) G x₀ p a' d t
                (Work.Diff.EXT.pt (I := I) x₀ z))
              (lam := fun p z => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m
                v a b c p z)
              (fun p => Work.Diff.EXT.ConnCov.chrCoord_contDiffAt (I := I) (M := M) G x₀ t
                (hK't hy) p a' d)
              (fun p => hsm t ht y hy m (by omega) v a b c p)
              (fun p k hk => le_trans (hCχ t ht k (le_trans hk hJm) p a' d y hy) hCχCz)
              (fun p k hk => hBJ t ht y hy k hk m hmJ v a b c p)) ?_
            refine le_of_eq ?_
            simp only [Fintype.card_fin, hNTdef, hBmdef, hXdef]
          -- ### assembly
          refine le_trans (norm_iteratedFDeriv_add6_le_at (x := y) (J := J) (f1 := T1) (f2 := S1)
            (f3 := S2) (f4 := S3) (f5 := S4) (f6 := S5)
            (C1 := BJ) (C2 := (m : ℝ) * (NT * X)) (C3 := NT * X) (C4 := NT * X) (C5 := NT * X)
            (C6 := NT * X) hT1sm hS1sm hS2sm hS3sm hS4sm hS5sm hT1b hS1b hS2b hS3b hS4b hS5b) ?_
          rw [hBψdef, hNBdef]
          have hY : 0 ≤ NT * X := mul_nonneg hNT0 hX0
          have hstep : ((m : ℝ) + 4) * (NT * X) ≤ ((Mm : ℝ) + 4) * (NT * X) :=
            mul_le_mul_of_nonneg_right (by
              have hmle : (m : ℝ) ≤ (Mm : ℝ) := by exact_mod_cast (by omega : m ≤ Mm)
              linarith) hY
          nlinarith [hstep]
        -- ### the final estimate for this level
        calc ‖iteratedFDeriv ℝ (J + 1)
              (fun z : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t
                m v a b c d z) y‖
            ≤ Cb * ∑ a' : Fin (Module.finrank ℝ E),
              ‖iteratedFDeriv ℝ J (fun z : E =>
                fderiv ℝ (fun z' : E => Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M)
                  G x₀ t m v a b c d z') z (Work.Diff.GE.cBasis (E := E) a')) y‖ := h1
          _ ≤ Cb * (NT * Bψ) := by
              refine mul_le_mul_of_nonneg_left ?_ hCb0
              refine le_trans (Finset.sum_le_sum (fun a' _ => h2 a')) ?_
              rw [Finset.sum_const, nsmul_eq_mul]
              have hcard : ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) = NT := by
                rw [Finset.card_univ, Fintype.card_fin, hNTdef]
              rw [hcard]
          _ ≤ B' := le_max_right _ _
  have hmono : ∀ (m : ℕ) (C C' : ℝ),
      (∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ i ≤ m, ∀ m', m' ≤ Mm - m →
        ∀ (v : Fin m' → Fin (Module.finrank ℝ E)) (a b c d : Fin (Module.finrank ℝ E)),
          ‖iteratedFDeriv ℝ i (fun y' : E =>
            Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m' v a b c d y') y‖ ≤ C) →
      C ≤ C' →
      (∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ i ≤ m, ∀ m', m' ≤ Mm - m →
        ∀ (v : Fin m' → Fin (Module.finrank ℝ E)) (a b c d : Fin (Module.finrank ℝ E)),
          ‖iteratedFDeriv ℝ i (fun y' : E =>
            Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m' v a b c d y') y‖ ≤ C') :=
    fun m C C' h hC => fun t ht y hy i hi m' hm' v a b c d =>
      le_trans (h t ht y hy i hi m' hm' v a b c d) hC
  obtain ⟨C, hC0, hC⟩ := Work.Diff.EXT.exists_uniform_bound_of_le
    (P := fun m C => ∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ i ≤ m, ∀ m', m' ≤ Mm - m →
      ∀ (v : Fin m' → Fin (Module.finrank ℝ E)) (a b c d : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ i (fun y' : E =>
          Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m' v a b c d y') y‖ ≤ C)
    hmono Mm (fun J hJ => key J hJ)
  exact ⟨C, hC0, fun t ht J hJ m hm v a b c d y hy =>
    hC J hJ t ht y hy J le_rfl m hm v a b c d⟩

end Work.Diff.EXT.ConnCov
