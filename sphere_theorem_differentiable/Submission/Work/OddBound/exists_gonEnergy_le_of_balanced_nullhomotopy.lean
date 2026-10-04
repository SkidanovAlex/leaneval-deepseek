import Mathlib
import Submission.Work.OddBound.PolygonModel
import Submission.Work.OddBound.design.Localisation
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.piecewiseDist
import Submission.Work.OddBound.liftPiecewise.exists_lift_of_piecewise_short
import Submission.Work.OddBound.piecewiseLen.riemannianDist_le_curveLength_piecewise_alt

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.OddBound

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

/-! ## The arclength-proportional parametrisation of a piecewise `C¹` curve

If the length function `s ↦ curveLength f 0 s` of a piecewise `C¹` curve `f` is *affine* on the
parameter (`curveLength f 0 s = s · curveLength f 0 1`, the "balanced" hypothesis of the null
homotopy), then the length of any sub-curve `[c,d] ⊆ [0,1]` is `(d - c) · curveLength f 0 1`. -/

theorem curveLength_balanced_sub
    {f : ℝ → M} {k : ℕ} {a : Fin (k + 1) → ℝ}
    (hamono : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last k) = 1)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 f (Set.Icc (a j.castSucc) (a j.succ)))
    (hbal : ∀ s : ℝ,
      Submission.Length.curveLength (I := I) f 0 s
        = s * Submission.Length.curveLength (I := I) f 0 1)
    {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    Submission.Length.curveLength (I := I) f c d
      = (d - c) * Submission.Length.curveLength (I := I) f 0 1 := by
  have hint : ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ 1 →
      IntervalIntegrable (Submission.Length.curveSpeed (I := I) f) MeasureTheory.volume c d :=
    fun c d hc hcd hd =>
      Work.OddBound.liftPiecewise.intervalIntegrable_curveSpeed_piecewise
        (I := I) (h := f) (S := 1) (k := k) (a := a) hamono ha0 ha1 hpiece c d hc hcd hd
  have hadd := Submission.Length.curveLength_add_of_integrable (I := I) f
    (hint 0 c le_rfl hc (le_trans hcd hd)) (hint c d hc hcd hd)
  have h1 := hbal c
  have h2 := hbal d
  have key : Submission.Length.curveLength (I := I) f c d
      = Submission.Length.curveLength (I := I) f 0 1 * d
        - Submission.Length.curveLength (I := I) f 0 1 * c := by
    linarith
  rw [key]; ring

/-! ## Vertices of the slice polygon -/

/-- **The vertices of the polygon of a slice.**  For a curve `s ↦ Hf s τ` that is `1`-periodic in
`s` and starts at `p` at `s = 0`, the vertices of the closed `N`-gon with interior vertices
`Hf ((i+1)/N) τ` are `Hf (j/N) τ`, `j = 0, …, N`. -/
theorem gonVert_slice {p : M} {N : ℕ} {τ : ℝ} {Hf : ℝ → ℝ → M}
    (hper : ∀ s t : ℝ, Hf (s + 1) t = Hf s t) (hbase : ∀ t : ℝ, Hf 0 t = p)
    (hN : 0 < N) :
    ∀ j : ℕ, j ≤ N →
      gonVert p (fun i : Fin (N - 1) => Hf (((i : ℕ) + 1) / N) τ) j = Hf ((j : ℝ) / N) τ := by
  intro j hj
  have h1p : Hf 1 τ = p := by
    have hh := hper 0 τ
    simpa using hh.trans (hbase τ)
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rw [gonVert_zero]
    simp only [Nat.cast_zero, zero_div]
    exact (hbase τ).symm
  · rcases eq_or_lt_of_le hj with heq | hlt
    · rw [heq, gonVert_of_le p _ le_rfl]
      have hNN : ((N : ℕ) : ℝ) / (N : ℝ) = 1 := div_self (by exact_mod_cast (ne_of_gt hN))
      rw [hNN, h1p]
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hi : i < N - 1 := by omega
      rw [gonVert_succ p _ hi]
      congr 1
      push_cast
      ring

end

/-! ## The `N`-independent energy bound for the slices of a balanced null homotopy -/

theorem exists_gonEnergy_le_of_balanced_nullhomotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {L : ℝ} (hL : 0 < L) {γ : ℝ → M} {Hf : ℝ → ℝ → M}
    (hcont : Continuous (fun q : ℝ × ℝ => Hf q.1 q.2))
    (hper : ∀ s t : ℝ, Hf (s + 1) t = Hf s t)
    (hbase : ∀ t : ℝ, Hf 0 t = p)
    (h0 : ∀ s : ℝ, Hf s 0 = γ (L * s))
    (h1 : ∀ s : ℝ, Hf s 1 = p)
    (hpiece : ∀ t : ℝ, ∃ (k : ℕ) (a : Fin (k + 1) → ℝ),
      StrictMono a ∧ a 0 = 0 ∧ a (Fin.last k) = 1 ∧
      ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => Hf s t)
        (Set.Icc (a j.castSucc) (a j.succ)))
    {B : ℝ} (hB : 0 < B)
    (hlen : ∀ t : ℝ, Submission.Length.curveLength (I := I) (fun s : ℝ => Hf s t) 0 1 ≤ B)
    (hbal : ∀ t s : ℝ,
      Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 s
        = s * Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 1) :
    ∀ N : ℕ, 3 ≤ N → ∀ τ ∈ Set.Icc (0:ℝ) 1,
      Work.OddBound.gonEnergy (I := I) p (fun i : Fin (N - 1) => Hf (((i : ℕ) + 1) / N) τ)
        ≤ B ^ 2 / 2 := by
  intro N hN τ hτ
  obtain ⟨k, a, hamono, ha0, ha1, hpiece'⟩ := hpiece τ
  set f : ℝ → M := fun r : ℝ => Hf r τ with hf
  have hpieceF : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 f (Set.Icc (a j.castSucc) (a j.succ)) := by
    intro j
    rw [hf]
    exact hpiece' j
  have hbalF : ∀ s : ℝ, Submission.Length.curveLength (I := I) f 0 s
      = s * Submission.Length.curveLength (I := I) f 0 1 := by
    intro s
    rw [hf]
    exact hbal τ s
  -- The piecewise distance-versus-length bound for the slice.
  have hQ : ∀ {c d : ℝ}, 0 ≤ c → c ≤ d → d ≤ 1 →
      Submission.Distance.riemannianDist (I := I) (f c) (f d)
        ≤ Submission.Length.curveLength (I := I) f c d := by
    intro c d hc hcd hd
    exact Work.OddBound.piecewiseLen.riemannianDist_le_curveLength_piecewise_alt
      (I := I) (f := f) hamono ha0 ha1 hpieceF hc hcd hd
  set W : Fin (N - 1) → M := fun i => Hf (((i : ℕ) + 1) / N) τ with hW
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hvert : ∀ j : ℕ, j ≤ N → gonVert p W j = Hf ((j : ℝ) / (N : ℝ)) τ :=
    fun j hj => gonVert_slice (p := p) (N := N) (τ := τ) (Hf := Hf) hper hbase
      (by omega : 0 < N) j hj
  have hside : ∀ i : Fin N, gonSideLen (I := I) p W i ≤ (1 / (N : ℝ)) * B := by
    intro i
    have hiN : (i : ℕ) < N := i.isLt
    have hc : (0 : ℝ) ≤ ((i : ℕ) : ℝ) / (N : ℝ) := div_nonneg (by positivity) hNpos.le
    have hstep : ((i : ℕ) : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hcd : ((i : ℕ) : ℝ) / (N : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right hstep hNpos.le
    have hd : (((i : ℕ) + 1 : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hNpos, one_mul]
      exact_mod_cast (by omega : (i : ℕ) + 1 ≤ N)
    rw [gonSideLen, hvert (i : ℕ) (le_of_lt hiN), hvert ((i : ℕ) + 1) (by omega)]
    refine le_trans (hQ (c := ((i : ℕ) : ℝ) / (N : ℝ))
      (d := (((i : ℕ) + 1 : ℕ) : ℝ) / (N : ℝ)) hc hcd hd) ?_
    rw [curveLength_balanced_sub (I := I) (f := f) hamono ha0 ha1 hpieceF hbalF hc hcd hd]
    rw [show (((i : ℕ) + 1 : ℕ) : ℝ) / (N : ℝ) - ((i : ℕ) : ℝ) / (N : ℝ) = 1 / (N : ℝ) from by
      field_simp
      push_cast
      ring]
    exact mul_le_mul_of_nonneg_left (hlen τ) (by positivity)
  have hsum : ∑ i : Fin N, (gonSideLen (I := I) p W i) ^ 2
      ≤ (N : ℝ) * ((1 / (N : ℝ)) * B) ^ 2 := by
    calc ∑ i : Fin N, (gonSideLen (I := I) p W i) ^ 2
        ≤ ∑ i : Fin N, ((1 / (N : ℝ)) * B) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact pow_le_pow_left₀ (Submission.Distance.riemannianDist_nonneg (I := I) _ _)
            (hside i) 2
      _ = (N : ℝ) * ((1 / (N : ℝ)) * B) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Work.OddBound.gonEnergy (I := I) p W
      = (N : ℝ) / 2 * ∑ i : Fin N, (gonSideLen (I := I) p W i) ^ 2 := rfl
    _ ≤ (N : ℝ) / 2 * ((N : ℝ) * ((1 / (N : ℝ)) * B) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B ^ 2 / 2 := by
        field_simp

end Work.OddBound
