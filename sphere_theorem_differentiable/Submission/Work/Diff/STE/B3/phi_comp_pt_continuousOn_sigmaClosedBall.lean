import Mathlib
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.dens_bound_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: continuity of `y ↦ Phi D i u k (pt i y)` on the closed `σ`-ball

The B3 adjunction `BPair (Rstar i u) k = CPair i u (R i k)` needs to know that the integrand
`y ↦ (ζ j (pt i y))^2 · dens i y · Phi D i u k (pt i y)` is continuous (indeed Lebesgue integrable)
on the flat `σ i`-ball; this file supplies the continuity of its most opaque factor.

**The mathematical content is a reduction.**  On the closed `σ i`-ball the chart `i` is genuine
(`D.htarget`, since `σ i ≤ 2 σ i`), the cut-off is one (`D.hχ1`), the flat coordinate of
`D.pt i y` is `y` (`D.coord_pt`), and the frame `D.e i ·` is `g₀`-orthonormal at `D.pt i y`
(`D.heON`, whose orthonormality neighbourhood has radius `2 σ i`).  Therefore the coefficient of
the reconstruction and the double frame contraction both collapse:

`Phi D i u k (pt i y) = ζ i (pt i y) · (√(dens i y))⁻¹ · ∑ a b, u a b y · D.mat i k a b y`.

Each factor on the right is continuous in `y` on the closed ball:
`y ↦ ζ i (pt i y)` because `pt i` is continuous (the inverse chart) and `ζ i` is `C^∞`;
`y ↦ (√(dens i y))⁻¹` because `dens i` is continuous on the chart target
(`Work.Diff.STE.B3.dens_continuousAt_of_mem_target`) and `√` and `(·)⁻¹` are continuous;
and `y ↦ ∑ a b, u a b y · D.mat i k a b y` because `u a b` is continuous (`hu`) and
`z ↦ D.mat i k a b z` is continuous on `{χ i ≠ 0} ⊇ σ`-ball (`hk`, `D.hχ1`).

Note that the density hypothesis `hdens` is not needed: continuity of `√(dens i ·)` never uses a
positive lower bound (`inv` is continuous on all of `ℝ`), and the pointwise identity above is
proved on the whole closed ball, where `√(dens i ·) > 0` anyway.
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

section Algebra

/-- **Collapsing a double sum against an orthonormal frame.**  The two coefficient functionals of an
orthonormal frame see only the diagonal term of the coefficient family `F`.

Local copy of `Work.Diff.STE.B3.sum_orth_of_isONFrame` (which lives in `B3/BPair_Rstar.lean`, a
module this file must not import); the proof is that all off-diagonal terms carry a factor
`g₀.inner p (e a) (e a') = 0`. -/
lemma phi_comp_pt_sum_orth_of_isONFrame {g₀ : Submission.Diff.SMet I M} {p : M}
    {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : Submission.Diff.IsONFrame g₀ p e)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (a b : Fin (Module.finrank ℝ E)) :
    (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        F a' b' * g₀.inner p (e a) (e a') * g₀.inner p (e b) (e b')) = F a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [hON a a, hON b b]
      simp
    · intro b' _ hb'
      have h : g₀.inner p (e b) (e b') = 0 := by
        rw [hON b b']
        simp [Ne.symm hb']
      simp [h]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · intro a' _ ha'
    have h : g₀.inner p (e a) (e a') = 0 := by
      rw [hON a a']
      simp [Ne.symm ha']
    simp [h]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

end Algebra

section Pointwise

variable (D : B3Data (I := I) (M := M) ι₀ g₀)

/-- **The intrinsic contraction in an orthonormal frame.**  At a point `p` where the frame `e i` is
`g₀`-orthonormal, `Phi D i u k p` is the coefficient
`ζ i p · χ i (coord i p) · (√(dens i (coord i p)))⁻¹` times the contraction of `u` against `k` in the
frame `e i`.

Local copy of `Work.Diff.STE.B3.Phi_apply_frame` (`B3/BPair_Rstar.lean`); the proof evaluates
`Rstar` with `Rstar_apply` and then collapses the frame sum with
`phi_comp_pt_sum_orth_of_isONFrame`. -/
lemma phi_comp_pt_Phi_apply_frame {i : ι₀}
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Bil (I := I) (M := M)) {p : M}
    (hON : IsONFrame g₀ p (fun a => D.e i a p)) :
    Phi D i u k p
      = (D.ζ i p * D.χ i (coord (I := I) (D.x₀ i) p)
          * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹)
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            u a b (coord (I := I) (D.x₀ i) p) * k p (D.e i a p) (D.e i b p)) := by
  have hcoeff : ∀ a b : Fin (Module.finrank ℝ E),
      D.Rstar i u p (D.e i a p) (D.e i b p)
        = (D.ζ i p * D.χ i (coord (I := I) (D.x₀ i) p)
            * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹)
          * u a b (coord (I := I) (D.x₀ i) p) := by
    intro a b
    rw [Rstar_apply D i u p (D.e i a p) (D.e i b p)]
    congr 1
    exact phi_comp_pt_sum_orth_of_isONFrame (g₀ := g₀) (p := p) hON
      (fun a' b' => u a' b' (coord (I := I) (D.x₀ i) p)) a b
  simp only [Phi, hcoeff]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **The pointwise identity on the closed `σ`-ball.**  For `‖y‖ ≤ σ i` the chart `i` is genuine,
the cut-off is one, the flat coordinate of `D.pt i y` is `y`, and the frame is orthonormal there, so

`Phi D i u k (pt i y) = ζ i (pt i y) · (√(dens i y))⁻¹ · ∑ a b, u a b y · D.mat i k a b y`. -/
lemma phi_comp_pt_Phi_pt_eq {i : ι₀}
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Bil (I := I) (M := M)) {y : Fin (Module.finrank ℝ E) → ℝ}
    (hy : ‖y‖ ≤ D.σ i) :
    Phi D i u k (D.pt i y)
      = D.ζ i (D.pt i y) * (Real.sqrt (D.dens i y))⁻¹
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            u a b y * D.mat i k a b y) := by
  have hz2 : ‖y‖ ≤ 2 * D.σ i := by have := D.hσ i; linarith
  have hON : IsONFrame g₀ (D.pt i y) (fun a => D.e i a (D.pt i y)) := D.heON i y hz2
  have hcoord : coord (I := I) (D.x₀ i) (D.pt i y) = y := D.coord_pt i hz2
  have hchi : D.χ i y = 1 := D.hχ1 i y hy
  rw [phi_comp_pt_Phi_apply_frame D (i := i) u k hON, hcoord, hchi, mul_one]
  simp only [B3Data.mat]

end Pointwise

-- Please prove this WITHOUT importing `Submission.Work.Diff.STE.B3.BPair_Rstar`:
-- that module is the *end user* of this lemma's consumer (`integrableOn_Npair_term`), so
-- importing it here would create an import cycle later. The needed ingredients
-- (`dens_bound_sigma`, `BPairSmooth`, `Rstar_apply`, `BPairDefs`) are all lower in the DAG.
theorem phi_comp_pt_continuousOn_sigmaClosedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j k a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0})
    (hdens : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (i : ι₀)
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → c ≤ D.dens i z ∧ D.dens i z ≤ C) :
    ContinuousOn (fun y => Work.Diff.STE.B3.Phi D i u k (D.pt i y))
      (Work.Diff.STE.B3.sigmaClosedBall D i) := by
  classical
  -- the closed `σ`-ball sits inside the region where the cut-off `χ i` does not vanish
  have hsub : sigmaClosedBall D i ⊆ {z : Fin (Module.finrank ℝ E) → ℝ | D.χ i z ≠ 0} :=
    fun z hz => chi_ne_zero_of_norm_le_sigma D hz
  -- the weight `ζ i ∘ pt i`
  have hcontζ : ContinuousOn (fun y => D.ζ i (D.pt i y)) (sigmaClosedBall D i) := by
    intro y hy
    have hyle : ‖y‖ ≤ D.σ i := hy
    have hz2 : ‖y‖ ≤ 2 * D.σ i := by have := D.hσ i; linarith
    have hflat : ContinuousAt
        (fun z : Fin (Module.finrank ℝ E) → ℝ => flatToE (I := I) (D.x₀ i) z) y :=
      (flatToE_contDiff (I := I) (M := M) (D.x₀ i)).continuous.continuousAt
    have hpt : ContinuousAt (D.pt i) y :=
      (continuousAt_extChartAt_symm'' (I := I) (D.htarget i y hz2)).comp hflat
    exact (((D.hζsm i).continuous.continuousAt).comp hpt).continuousWithinAt
  -- the inverse square root of the density
  have hcontdens : ContinuousOn (fun y => (Real.sqrt (D.dens i y))⁻¹)
      (sigmaClosedBall D i) := by
    intro y hy
    have hyle : ‖y‖ ≤ D.σ i := hy
    have hz2 : ‖y‖ ≤ 2 * D.σ i := by have := D.hσ i; linarith
    have htgt := D.htarget i y hz2
    have hd : ContinuousAt (D.dens i) y := dens_continuousAt_of_mem_target D i htgt
    have hsqrt : ContinuousAt (fun y => Real.sqrt (D.dens i y)) y :=
      Real.continuous_sqrt.continuousAt.comp hd
    have hne : Real.sqrt (D.dens i y) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (dens_pos_of_mem_target D i htgt))
    exact (ContinuousAt.inv₀ hsqrt hne).continuousWithinAt
  -- the contraction of `u` against the chart matrix of `k`
  have hcontmat : ContinuousOn
      (fun y => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        u a b y * D.mat i k a b y) (sigmaClosedBall D i) :=
    continuousOn_finsetSum Finset.univ fun a _ =>
      continuousOn_finsetSum Finset.univ fun b _ =>
        (hu a b).continuousOn.mul ((hk i a b).mono hsub)
  -- the product of the three continuous factors
  have hprod : ContinuousOn
      (fun y => D.ζ i (D.pt i y) * (Real.sqrt (D.dens i y))⁻¹
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            u a b y * D.mat i k a b y)) (sigmaClosedBall D i) :=
    (hcontζ.mul hcontdens).mul hcontmat
  refine hprod.congr fun y hy => ?_
  exact phi_comp_pt_Phi_pt_eq (i := i) D u k hy

end Work.Diff.STE.B3
