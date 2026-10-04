import Mathlib
import Submission.Work.Diff.STE.Lead.mat_jet_bound
import Submission.Work.Diff.STE.Lead.MatJetDefs
import Submission.Work.Diff.STE.Lead.matA_jets
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.D.psi.abs_coord_factor_le
import Submission.Work.Diff.EXT.FrameKit.formInFrame_frameMat
import Submission.Work.Diff.EXT.glueDefs
import Submission.Work.Diff.STE.Lead.chartMatJetDefs
import Submission.Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.Lead.fderiv_flatAffine_pdR
import Submission.Work.Diff.STE.Lead.pdRList_mul_le
import Submission.Work.Diff.STE.Lead.pdRList_finset_sum_le
import Submission.Work.Diff.STE.Lead.Bmat_smooth_jets_le
import Submission.Work.Diff.STE.Lead.fderiv2_flatAffine_pdR

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open Filter
open Bundle
open scoped Manifold ContDiff

/-
ROUTE.  `hMat` is the *sharp* form (linear in `√(BNorm k h)`, uniform in `h`) of the jet bound for
the `g₀`-orthonormal-frame chart matrix `D.mat i h a b`.  Such a bound follows from the PROVED
`Work.Diff.STE.Lead.mat_jet_bound` by *scaling in `h`*: for `t > 0`, `BNorm k (t • h) = t ^ 2 *
BNorm k h`, `ChartData (t • h)` holds, and `pdRList l (D.mat i (t•h) a b) = t * pdRList l (D.mat i h a b)`,
so `mat_jet_bound` gives `t * |∂^l mat| ≤ C (1 + t ^ 2 * BNorm k h) / c ^ 3` for every `t > 0`;
minimising in `t` (put `t = 1/√(BNorm k h)`) yields `|∂^l mat| ≤ 2 C √(BNorm k h) / c ^ 3`.
The `c ^ 3` exponent is uniform in the order `l` (that is all this file needs).  You may of course
take `hMat` as a hypothesis.

The target is the corresponding statement for the chart matrix in the *coordinate* frame of the
chart at `x₀ i`, read in the model space `E` (this is the object that the jet-level DeTurck operator
`Work.Diff.STE.DeTurck.pPhiJet` sees, through `Work.Diff.STE.DeTurck.chartJet` /
`Work.Diff.EXT.chartMatFun`).  All three clauses use the exponent `c ^ 3`; since the only use of `c`
in the applications is `c = 1/√(card ι₀)` (fixed), this is all that is needed.

STEP 1 (frame change, flat coordinates).  Write `∂_a = Submission.Geodesic.frameVector (D.x₀ i) p
(Work.Diff.EXT.bB a)` and `e_p = D.e i p p`.  Expanding `∂_a` in the `g₀`-orthonormal frame `e`
(`Work.EXT.sum_inner_smul_eq_self_of_isONFrame`, valid for `‖z‖ ≤ 2 * D.σ i` by `D.heON`) and using
bilinearity of `h` gives, for `y = flatToE z`,

`D.chartMatOf h (D.x₀ i) y a b = Σ_{pq} B_{pa}(z) B_{qb}(z) * D.mat i h p q z`,
`B_{pa}(z) = g₀(e_p, ∂_a)(z)`.

The matrix `B` and its first and second flat derivatives are bounded by a fixed constant on the
compact ball `‖z‖ ≤ D.σ i` (smoothness of `z ↦ g₀(...)` from `D.hesm`, `D.contMDiffAt_pt`,
`Work.Diff.EXT.contMDiffAt_frameVector`/`FrameKit.contMDiffAt_frameCoords_frameVector`, then
compactness as in `Work.Diff.STE.D.psi.abs_coord_factor_le`; the region is inside the chart target by
`D.htarget`).  The Leibniz rule of order ≤ 2 for `pdRList` (prove it from `fderiv_mul`:
`pdR i (f*g) = f * pdR i g + pdR i f * g` and then differentiate once more, using that the pieces
are smooth) turns `hMat` into the same bound for `z ↦ D.chartMatOf h (D.x₀ i) (flatToE z) a b`, with
the same exponent `c ^ 3` and constant `C_M` times the frame-change constant.

STEP 2 (flat coordinates → model coordinates).  `flatToE (D.x₀ i)` is the affine map
`z ↦ (finBasis.equivFun)⁻¹ ((finBasis.equivFun) ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z)`, whose
derivative is the linear map `L := ((finBasis.equivFun).symm : (Fin n → ℝ) →ₗ[ℝ] E)`, with
`L (Pi.single p 1) = bB p`.  Hence for `F : E → ℝ`
`fderiv ℝ (fun y : E => F y) (flatToE z) (bB p) = pdR p (fun w => F (flatToE w)) z`
(`fderiv_comp` with the constant derivative) and
`(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => F y') y) (flatToE z) (bB p)) (bB q)
  = pdR q (pdR p (fun w => F (flatToE w))) z`
(`fderiv_clm_apply` for `fun y => fderiv ℝ F y`, then the previous identity twice; the nesting order
must be matched carefully).
-/

section FrameChange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The frame-change expansion of the chart matrix**: expanding the coordinate-frame vectors
`∂_a = frameVector (x₀ i) · (bB a)` in the `g₀`-orthonormal frame `D.e i` turns the chart matrix of
`h` in the coordinate frame into the double sum of the chart matrix in the orthonormal frame
against the frame-change coefficients `Bmat D i a p`. -/
lemma chartMatOf_eq_sum_Bmat
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ 2 * D.σ i) :
    Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) a b
      = ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          D.mat i h p q z * Bmat (I := I) (M := M) D i a p z
            * Bmat (I := I) (M := M) D i b q z := by
  have hsrc : D.pt i z ∈ (extChartAt I (D.x₀ i)).source :=
    (extChartAt I (D.x₀ i)).map_target (D.htarget i z hz)
  have hON : Submission.Diff.IsONFrame g₀ (D.pt i z) (fun a => D.e i a (D.pt i z)) :=
    D.heON i z hz
  have hmain := Work.Diff.STE.B3.apply_eq_sum_mat_free (I := I) (M := M) D i h hsrc hON
      (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z)
        (Work.Diff.EXT.bB (E := E) a))
      (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z)
        (Work.Diff.EXT.bB (E := E) b))
  rw [D.coord_pt i hz] at hmain
  rw [show Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) a b
      = h (D.pt i z)
          (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z)
            (Work.Diff.EXT.bB (E := E) a))
          (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z)
            (Work.Diff.EXT.bB (E := E) b))
      from rfl]
  simp only [Work.Diff.STE.Lead.Bmat_apply]
  exact hmain

/-- The frame-change expansion holds on a neighbourhood of every point of the closed `σ i`-ball. -/
lemma chartMatOf_eventuallyEq_sum_Bmat
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ D.σ i) :
    (fun w : Fin (Module.finrank ℝ E) → ℝ => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h
        (D.x₀ i) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) w) a b)
      =ᶠ[nhds z] (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          D.mat i h p q w * Bmat (I := I) (M := M) D i a p w
            * Bmat (I := I) (M := M) D i b q w) := by
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball z (D.σ i), Metric.ball_mem_nhds z (D.hσ i), fun w hw => ?_⟩
  have hwlt : ‖w - z‖ < D.σ i := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hw2 : ‖w‖ ≤ 2 * D.σ i := by
    have h1 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      conv_lhs => rw [show w = (w - z) + z by abel]
      exact norm_add_le _ _
    linarith [D.hσ i]
  exact chartMatOf_eq_sum_Bmat D h i a b hw2

/-- **The chart matrix in the coordinate frame is smooth in the chart coordinate**, as a function on
the model space `E`: it is the `(a,b)`-component of the `ChartData` function of `h`. -/
lemma contDiffAt_chartMatOf
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j₀ : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ (extChartAt I (D.x₀ j₀)).target) :
    ContDiffAt ℝ ∞
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j₀) y a b) y := by
  have h1 : ContDiffAt ℝ ∞
      (fun y : E => fun i j : Fin (Module.finrank ℝ E) =>
        h ((extChartAt I (D.x₀ j₀)).symm y)
          (Submission.Geodesic.frameVector (I := I) (D.x₀ j₀) ((extChartAt I (D.x₀ j₀)).symm y)
            (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) (D.x₀ j₀) ((extChartAt I (D.x₀ j₀)).symm y)
            (Work.Diff.EXT.bB (E := E) j))) y :=
    (hsm (D.x₀ j₀)).contDiffAt ((isOpen_extChartAt_target (I := I) (D.x₀ j₀)).mem_nhds hy)
  have h2 := (contDiffAt_pi.mp h1) a
  have h3 := (contDiffAt_pi.mp h2) b
  simpa only [Work.Diff.STE.D.chartMatOf_apply] using h3

/-- **The chart matrix in the orthonormal frame is smooth in the flat coordinate**, on the part of
the chart where the flat coordinate lies in the chart target. -/
lemma contDiffAt_mat_of_chartData
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (i : ι₀)
    (p q : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target) :
    ContDiffAt ℝ 2 (D.mat i h p q) z := by
  have hsec : ∀ x : M, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x :=
    fun x => Work.Diff.STE.B3.section_contMDiffAt_of_chartData (I := I) (M := M) hsm x
  have hmat : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x : M => h x (D.e i p x) (D.e i q x)) Set.univ := by
    intro x _
    have hψ := (hsec x).contMDiffWithinAt (s := Set.univ)
    have hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i p)) Set.univ x :=
      (D.hesm i p).contMDiffAt.contMDiffWithinAt
    have hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i q)) Set.univ x :=
      (D.hesm i q).contMDiffAt.contMDiffWithinAt
    have hres := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
    simp only [contMDiffWithinAt_totalSpace] at hres
    exact hres.2
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun y : E => h ((extChartAt I (D.x₀ i)).symm y)
        (D.e i p ((extChartAt I (D.x₀ i)).symm y))
        (D.e i q ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target :=
    hmat.comp (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞)))
      (fun y _ => Set.mem_univ _)
  have hsmOn : ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i h p q) (extChartAt I (D.x₀ i)).target :=
    hcomp.contDiffOn
  have hfl : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => D.matChart i h p q
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) z :=
    (hsmOn.contDiffAt ((isOpen_extChartAt_target (I := I) (D.x₀ i)).mem_nhds hzt)).comp z
      ((Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffAt)
  exact (hfl.of_le (by norm_num))

end FrameChange

/-- The absolute value of a double sum is at most the double sum of the absolute values. -/
private lemma abs_double_sum_le {n : ℕ} (X : Fin n → Fin n → ℝ) :
    |∑ p : Fin n, ∑ q : Fin n, X p q| ≤ ∑ p : Fin n, ∑ q : Fin n, |X p q| := by
  calc |∑ p : Fin n, ∑ q : Fin n, X p q|
      ≤ ∑ p : Fin n, |∑ q : Fin n, X p q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : Fin n, ∑ q : Fin n, |X p q| :=
        Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _

theorem chartMatJet_sharp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (hk : Module.finrank ℝ E + 8 < 2 * k)
    (C_M : ℝ) (hC_M : 0 ≤ C_M)
    (hMat : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (l : List (Fin (Module.finrank ℝ E)))
      (z : Fin (Module.finrank ℝ E) → ℝ) (c : ℝ),
      ‖z‖ ≤ D.σ i → 0 < c → c ≤ D.psi i z → l.length ≤ 2 →
      |Work.Diff.STE.pdRList l (D.mat i h a b) z| ≤ C_M * Real.sqrt (D.BNorm k h) / c ^ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) (c : ℝ),
      ‖z‖ ≤ D.σ i → 0 < c → c ≤ D.psi i z →
      (|Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) a b|
        ≤ C * Real.sqrt (D.BNorm k h) / c ^ 3)
    ∧ (∀ p : Fin (Module.finrank ℝ E),
        |(fderiv ℝ (fun y : E => (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y)
            a b) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) (Work.Diff.EXT.bB (E := E) p)|
          ≤ C * Real.sqrt (D.BNorm k h) / c ^ 3)
    ∧ (∀ p q : Fin (Module.finrank ℝ E),
        |(fderiv ℝ (fun y : E => (fderiv ℝ (fun y' : E =>
            (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y') a b) y))
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|
          ≤ C * Real.sqrt (D.BNorm k h) / c ^ 3) := by
  classical
  -- ## 0. The five analytic ingredients (proved in the sibling modules).
  have hMul : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f g : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ)
        (Kf Kg : ℝ),
        0 ≤ Kf → 0 ≤ Kg → ContDiffAt ℝ 2 f z → ContDiffAt ℝ 2 g z →
        (∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l f z| ≤ Kf) →
        (∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l g z| ≤ Kg) →
        ∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l (fun y => f y * g y) z| ≤ C * (Kf * Kg) :=
    pdRList_mul_le (d := Module.finrank ℝ E)
  obtain ⟨Cmul, hCmul_nn, hCmul⟩ := hMul
  have hSum : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : Finset (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)))
        (φ : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
        (z : Fin (Module.finrank ℝ E) → ℝ) (K : ℝ),
        0 ≤ K → (∀ i ∈ s, ContDiffAt ℝ 2 (φ i) z) →
        (∀ i ∈ s, ∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l (φ i) z| ≤ K) →
        ∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l (fun y => ∑ i ∈ s, φ i y) z| ≤ C * (s.card : ℝ) * K :=
    pdRList_finset_sum_le (d := Module.finrank ℝ E)
  obtain ⟨Csum, hCsum_nn, hCsum⟩ := hSum
  have hBmat : (∀ (i : ι₀) (a p : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
        ContDiffAt ℝ 2 (Bmat (I := I) (M := M) D i a p) z)
      ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : ι₀) (a p : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i →
        ∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l (Bmat (I := I) (M := M) D i a p) z| ≤ K :=
    Bmat_smooth_jets_le (I := I) (M := M) D
  obtain ⟨hBsm, K, hK_nn, hKb⟩ := hBmat
  have hDict1 : ∀ (c₀ : Fin (Module.finrank ℝ E) → ℝ) {F : E → ℝ}
      {z : Fin (Module.finrank ℝ E) → ℝ},
      ContDiffAt ℝ 2 F (flatAffine (E := E) c₀ z) → ∀ p : Fin (Module.finrank ℝ E),
      fderiv ℝ F (flatAffine (E := E) c₀ z) (Work.Diff.EXT.bB (E := E) p)
        = Work.Diff.STE.pdR p (fun w => F (flatAffine (E := E) c₀ w)) z :=
    fun c₀ F z hF p => fderiv_flatAffine_pdR (E := E) c₀ hF p
  have hDict2 : ∀ (c₀ : Fin (Module.finrank ℝ E) → ℝ) {F : E → ℝ}
      {z : Fin (Module.finrank ℝ E) → ℝ},
      ContDiffAt ℝ 2 F (flatAffine (E := E) c₀ z) → ∀ p q : Fin (Module.finrank ℝ E),
      (fderiv ℝ (fun y : E => fderiv ℝ F y) (flatAffine (E := E) c₀ z)
          (Work.Diff.EXT.bB (E := E) p)) (Work.Diff.EXT.bB (E := E) q)
        = Work.Diff.STE.pdR q (Work.Diff.STE.pdR p
            (fun w => F (flatAffine (E := E) c₀ w))) z :=
    fun c₀ F z hF p q => fderiv2_flatAffine_pdR (E := E) c₀ hF p q
  -- ## 1. The constant.
  have h1nn : (0 : ℝ) ≤ 1 + Csum * Cmul ^ 2 := by
    nlinarith [hCsum_nn, hCmul_nn, sq_nonneg Cmul]
  have h1ge : (1 : ℝ) ≤ 1 + Csum * Cmul ^ 2 := by
    nlinarith [hCsum_nn, hCmul_nn, sq_nonneg Cmul]
  have hA1_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M := by positivity
  have hA1_le : (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M
      ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M * (1 + Csum * Cmul ^ 2) := by
    calc (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M
        = (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M * 1 := (mul_one _).symm
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M * (1 + Csum * Cmul ^ 2) :=
          mul_le_mul_of_nonneg_left h1ge hA1_nn
  have hA2_le : (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M * (Csum * Cmul ^ 2)
      ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M * (1 + Csum * Cmul ^ 2) := by
    have h3 : Csum * Cmul ^ 2 ≤ 1 + Csum * Cmul ^ 2 := by
      nlinarith [hCsum_nn, hCmul_nn, sq_nonneg Cmul]
    exact mul_le_mul_of_nonneg_left h3 hA1_nn
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M * (1 + Csum * Cmul ^ 2), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hC_M) h1nn
  intro h hsm i a b z c hz hc hcl
  -- ## 2. The bulk of the work: bounds for the pieces.
  have hz2 : ‖z‖ ≤ 2 * D.σ i := by
    have hσ := D.hσ i
    linarith
  have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
    D.htarget i z hz2
  have hc3pos : (0 : ℝ) < c ^ 3 := by positivity
  have hBNN : 0 ≤ D.BNorm k h := by
    simp only [Work.Diff.STE.B3Data.BNorm]
    exact Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun a' _ =>
      Finset.sum_nonneg fun b' _ => Work.Diff.STE.CSq_nonneg k _
  have hW_nn : (0 : ℝ) ≤ Real.sqrt (D.BNorm k h) / c ^ 3 :=
    div_nonneg (Real.sqrt_nonneg _) hc3pos.le
  have hKmat_nn : (0 : ℝ) ≤ C_M * Real.sqrt (D.BNorm k h) / c ^ 3 :=
    div_nonneg (mul_nonneg hC_M (Real.sqrt_nonneg _)) hc3pos.le
  have hmat_bd : ∀ (p q : Fin (Module.finrank ℝ E)) (l : List (Fin (Module.finrank ℝ E))),
      l.length ≤ 2 → |Work.Diff.STE.pdRList l (D.mat i h p q) z|
        ≤ C_M * Real.sqrt (D.BNorm k h) / c ^ 3 :=
    fun p q l hl => hMat h hsm i p q l z c hz hc hcl hl
  have hB_bd : ∀ (a' p : Fin (Module.finrank ℝ E)) (l : List (Fin (Module.finrank ℝ E))),
      l.length ≤ 2 → |Work.Diff.STE.pdRList l (Bmat (I := I) (M := M) D i a' p) z| ≤ K :=
    fun a' p l hl => hKb i a' p z hz l hl
  have hmat_sm : ∀ p q : Fin (Module.finrank ℝ E), ContDiffAt ℝ 2 (D.mat i h p q) z :=
    fun p q => contDiffAt_mat_of_chartData (I := I) (M := M) D h hsm i p q hzt
  have hB_sm : ∀ (a' p : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ 2 (Bmat (I := I) (M := M) D i a' p) z :=
    fun a' p => hBsm i a' p z hz2
  -- the expansion of the chart matrix in the orthonormal frame
  set Φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    (fun w : Fin (Module.finrank ℝ E) → ℝ =>
      ∑ pq : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        D.mat i h pq.1 pq.2 w * Bmat (I := I) (M := M) D i a pq.1 w
          * Bmat (I := I) (M := M) D i b pq.2 w) with hΦdef
  have hev : (fun w : Fin (Module.finrank ℝ E) → ℝ => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h
        (D.x₀ i) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) w) a b) =ᶠ[nhds z] Φ := by
    filter_upwards [chartMatOf_eventuallyEq_sum_Bmat (I := I) (M := M) D h i a b hz]
      with w hw
    rw [hw, hΦdef]
    exact (Fintype.sum_prod_type (f := fun pq : Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) =>
        D.mat i h pq.1 pq.2 w * Bmat (I := I) (M := M) D i a pq.1 w
          * Bmat (I := I) (M := M) D i b pq.2 w)).symm
  -- the jet bound for `Φ`
  have hKtop_nn : (0 : ℝ) ≤ Cmul * ((Cmul * ((C_M * Real.sqrt (D.BNorm k h) / c ^ 3) * K)) * K) :=
    mul_nonneg hCmul_nn (mul_nonneg (mul_nonneg hCmul_nn (mul_nonneg hKmat_nn hK_nn)) hK_nn)
  have hΦbd : ∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
      |Work.Diff.STE.pdRList l Φ z|
        ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M * (Csum * Cmul ^ 2)
            * (Real.sqrt (D.BNorm k h) / c ^ 3) := by
    intro l hl
    -- the per-pair jet bound, obtained from the Leibniz rule applied twice
    have hper : ∀ pq ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E))),
        ∀ l' : List (Fin (Module.finrank ℝ E)), l'.length ≤ 2 →
        |Work.Diff.STE.pdRList l' (fun w : Fin (Module.finrank ℝ E) → ℝ =>
            D.mat i h pq.1 pq.2 w * Bmat (I := I) (M := M) D i a pq.1 w
              * Bmat (I := I) (M := M) D i b pq.2 w) z|
          ≤ Cmul * ((Cmul * ((C_M * Real.sqrt (D.BNorm k h) / c ^ 3) * K)) * K) := by
      intro pq _ l' hl'
      have hfirst : ∀ l : List (Fin (Module.finrank ℝ E)), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              D.mat i h pq.1 pq.2 w * Bmat (I := I) (M := M) D i a pq.1 w) z|
            ≤ Cmul * ((C_M * Real.sqrt (D.BNorm k h) / c ^ 3) * K) :=
        fun l hl2 => hCmul _ _ z _ K hKmat_nn hK_nn (hmat_sm pq.1 pq.2) (hB_sm a pq.1)
          (hmat_bd pq.1 pq.2) (fun l3 hl3 => hB_bd a pq.1 l3 hl3) l hl2
      exact hCmul _ _ z _ K (mul_nonneg hCmul_nn (mul_nonneg hKmat_nn hK_nn)) hK_nn
        ((hmat_sm pq.1 pq.2).mul (hB_sm a pq.1)) (hB_sm b pq.2)
        hfirst (fun l3 hl3 => hB_bd b pq.2 l3 hl3) l' hl'
    have hmain := hCsum Finset.univ
      (fun pq : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
        fun w : Fin (Module.finrank ℝ E) → ℝ =>
          D.mat i h pq.1 pq.2 w * Bmat (I := I) (M := M) D i a pq.1 w
            * Bmat (I := I) (M := M) D i b pq.2 w)
      z (Cmul * ((Cmul * ((C_M * Real.sqrt (D.BNorm k h) / c ^ 3) * K)) * K))
      hKtop_nn
      (fun pq _ => ((hmat_sm pq.1 pq.2).mul (hB_sm a pq.1)).mul (hB_sm b pq.2))
      hper l hl
    have hcard : ((Finset.univ : Finset (Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E))).card : ℝ)
        = (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc |Work.Diff.STE.pdRList l Φ z|
        ≤ Csum * ((Finset.univ : Finset (Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E))).card : ℝ)
            * (Cmul * ((Cmul * ((C_M * Real.sqrt (D.BNorm k h) / c ^ 3) * K)) * K)) := by
          simpa only [hΦdef] using hmain
      _ = (Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M * (Csum * Cmul ^ 2)
            * (Real.sqrt (D.BNorm k h) / c ^ 3) := by
          rw [hcard]; ring

  -- ## 3. The three clauses.
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1: the value
    rw [mul_div_assoc]
    calc |Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) a b|
        = |∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
              D.mat i h p q z * Bmat (I := I) (M := M) D i a p z
                * Bmat (I := I) (M := M) D i b q z| := by
            rw [chartMatOf_eq_sum_Bmat (I := I) (M := M) D h i a b hz2]
      _ ≤ ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
              |D.mat i h p q z * Bmat (I := I) (M := M) D i a p z
                * Bmat (I := I) (M := M) D i b q z| := abs_double_sum_le _
      _ ≤ ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
              (C_M * Real.sqrt (D.BNorm k h) / c ^ 3) * K * K := by
            apply Finset.sum_le_sum; intro p _
            apply Finset.sum_le_sum; intro q _
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul (hmat_bd p q [] (by simp)) (hB_bd a p [] (by simp))
                (abs_nonneg _) hKmat_nn) (hB_bd b q [] (by simp)) (abs_nonneg _)
              (mul_nonneg hKmat_nn hK_nn)
      _ = ((Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M) * (Real.sqrt (D.BNorm k h) / c ^ 3) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
      _ ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * K ^ 2 * C_M * (1 + Csum * Cmul ^ 2))
            * (Real.sqrt (D.BNorm k h) / c ^ 3) :=
            mul_le_mul_of_nonneg_right hA1_le hW_nn
  · -- clause 2: the first derivative
    intro p
    rw [mul_div_assoc]
    have hF2 : ContDiffAt ℝ 2 (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h
        (D.x₀ i) y a b) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) :=
      (contDiffAt_chartMatOf (I := I) (M := M) D h hsm i a b hzt).of_le (by norm_num)
    have hkey : fderiv ℝ (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h
          (D.x₀ i) y a b) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
          (Work.Diff.EXT.bB (E := E) p)
        = Work.Diff.STE.pdR p (fun w : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ i) w) a b) z :=
      hDict1 _ hF2 p
    rw [hkey]
    have hcongr : Work.Diff.STE.pdR p (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) w) a b) z
        = Work.Diff.STE.pdR p Φ z :=
      pdRList_congr' hev [p]
    rw [hcongr]
    exact le_trans (hΦbd [p] (by simp))
      (mul_le_mul_of_nonneg_right hA2_le hW_nn)
  · -- clause 3: the second derivative
    intro p q
    rw [mul_div_assoc]
    have hF2 : ContDiffAt ℝ 2 (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h
        (D.x₀ i) y a b) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) :=
      (contDiffAt_chartMatOf (I := I) (M := M) D h hsm i a b hzt).of_le (by norm_num)
    have hkey : (fderiv ℝ (fun y : E => (fderiv ℝ (fun y' : E =>
          Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i) y' a b) y))
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
          (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)
        = Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun w : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ i) w) a b)) z :=
      hDict2 _ hF2 p q
    rw [hkey]
    have hcongr : Work.Diff.STE.pdR q (Work.Diff.STE.pdR p
          (fun w : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ i)
              (Work.Diff.STE.flatToE (I := I) (D.x₀ i) w) a b)) z
        = Work.Diff.STE.pdR q (Work.Diff.STE.pdR p Φ) z :=
      pdRList_congr' hev [q, p]
    rw [hcongr]
    exact le_trans (hΦbd [q, p] (by simp))
      (mul_le_mul_of_nonneg_right hA2_le hW_nn)

end Work.Diff.STE.Lead
