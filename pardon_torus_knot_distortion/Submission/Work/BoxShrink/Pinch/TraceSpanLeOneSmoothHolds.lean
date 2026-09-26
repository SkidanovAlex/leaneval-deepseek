import Mathlib
import Submission.Work.BoxShrink.Pinch.TraceClass
import Submission.Work.BoxShrink.Pinch.DisjointLoopsWindingDet
import Submission.Work.BoxShrink.Pinch.Basic
import Submission.Work.Smooth.Morse.Flow
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq

/-!
# (K0) for the smooth tori: the trace of a transverse plane carries no two independent classes

`Work.BoxShrink.Pinch.TraceSpanLeOneSmooth` asks that for the smooth torus `F = ψ(F_standard)` of
the challenge and a plane `{y (σ 2) = c (σ 2) + u}` transverse to `F` along the whole trace, the
winding span of the trace `Z = F ∩ {y (σ 2) = c (σ 2) + u}` is at most one-dimensional.  This is
ingredient **(K0)** of Pardon's pinch: the trace of a plane carries no two loops with independent
winding vectors.

## The argument

Two loops `γ`, `δ` of the trace are, in general, *not* disjoint (they may run along the same
component of `Z`), so `Work.BoxShrink.Pinch.DisjointLoopsWindingDet` cannot be applied to them
directly.  The way out is to *push `γ` off the trace without changing its winding class*:

* `0` is a regular value of the plane coordinate `g = planeCoord c σ u` restricted to `F` — this is
  exactly the hypothesis `TransverseTrace`;
* the critical values of `g|_F` are closed (`Work.Smooth.Morse.Flow.RateBound.isClosed_criticalValues`),
  so a whole interval `(a,b) ∋ 0` is critical-free;
* the normalised gradient flow of `g|_F` (`Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region`)
  therefore homotopes any loop of `F ∩ {g < b}` — in particular `γ ⊆ {g = 0}` — to a loop `γ'` of
  `F ∩ {g < a}` with `a < 0`;  by `Work.SurgeryInvariance.WindingOf.homotopic_eq` the winding
  class is unchanged, and `γ'` is disjoint from `Z` (where `g = 0`);
* hence `γ'`, `δ` are disjoint loops of the torus, `DisjointLoopsWindingDet` gives
  `cross (winding γ') (winding δ) = 0`, and since the crossing form on `ℚ² = H₁(T²;ℚ)` is
  non-degenerate (`Work.BoxShrink.Pinch.cross_eq_zero_iff_eq_smul`) the spanning set of the trace
  lies in a line.

So the push-off of the loop — a strictly easier statement than the pinch itself, since it does not
have to keep the loop inside the box — replaces the missing "a loop of a component of the trace is
homotopic to a multiple of that component".
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **The winding vector of a closed curve of the torus, as a class of `ℚ² = H₁(T²;ℚ)`.**

This is the vector of which `Work.SurgeryInvariance.windingVectors` is the set:
`v ∈ windingVectors P X` iff `v = windingRat P γ` for some loop `γ` of `P` with values in `X`. -/
def windingRat (P : Work.CoreTopology.ParamTorus) (γ : Work.CoreTopology.ClosedCurve P) :
    ℚ × ℚ :=
  ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
    (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ))

theorem mem_windingVectors_iff {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    {v : ℚ × ℚ} :
    v ∈ Work.SurgeryInvariance.windingVectors P X ↔
      ∃ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) ∧ windingRat P γ = v :=
  Iff.rfl

/-! ## Pushing a loop of the trace off the trace -/

/-- **A loop of the trace of the cutting plane can be pushed off the trace without changing its
winding class.**

The plane is transverse to the surface along the whole trace, so `0` is a regular value of the
plane coordinate `g|_F`; the critical values of `g|_F` are closed, so an interval `(a,b) ∋ 0` is
critical-free, and the normalised gradient flow of `g|_F` carries the loop — which lies in
`{g = 0} ⊆ {g < b}` — to a loop of `F ∩ {g < a}` with `a < 0`, hence disjoint from the trace.  The
flow is a homotopy through loops of the surface, so the winding class is unchanged. -/
theorem exists_pushOff_planeTrace (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (hT : TransverseTrace ψ c σ u)
    (γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hγ : ∀ t : ℝ, γ t ∈ planeTrace (Work.Smooth.Morse.torus ψ) c σ u) :
    ∃ γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      (∀ t : ℝ, γ' t ∉ planeTrace (Work.Smooth.Morse.torus ψ) c σ u) ∧
      Work.SurgeryInvariance.windingOf (Work.Smooth.Morse.torus ψ) γ' =
        Work.SurgeryInvariance.windingOf (Work.Smooth.Morse.torus ψ) γ := by
  have hg2 : ContDiff ℝ 2 (Work.BoxShrink.Bubble.planeCoord c σ u) :=
    Work.BoxShrink.Bubble.contDiff_planeCoord c σ u
  have hg1 : ContDiff ℝ 1 (Work.BoxShrink.Bubble.planeCoord c σ u) :=
    hg2.of_le (by norm_num)
  -- `0` is a regular value of the plane coordinate: this is the transversality hypothesis
  have hreg0 : Work.Smooth.Morse.IsRegularValue ψ (Work.BoxShrink.Bubble.planeCoord c σ u) 0 := by
    rw [Work.Smooth.Morse.isRegularValue_iff]
    intro p hp
    exact hT p hp
  -- a whole interval around `0` is free of critical values
  obtain ⟨ε, hεpos, hε⟩ :=
    Metric.isOpen_iff.mp
      (Work.Smooth.Morse.Flow.RateBound.isClosed_criticalValues ψ hg1).isOpen_compl 0 hreg0
  have hreg : ∀ t ∈ Set.Icc (-(ε / 2)) (ε / 2),
      Work.Smooth.Morse.IsRegularValue ψ (Work.BoxShrink.Bubble.planeCoord c σ u) t := by
    intro t ht
    have hdist : dist t 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1, hεpos], by linarith [ht.2, hεpos]⟩
    exact hε (Metric.mem_ball.mpr hdist)
  have hab : -(ε / 2) ≤ ε / 2 := by linarith [hεpos]
  -- the loop lies below the level `ε / 2`
  have hγb : ∀ t : ℝ, γ t ∈ Work.Smooth.Morse.region ψ (Work.BoxShrink.Bubble.planeCoord c σ u)
      (ε / 2) := by
    intro t
    obtain ⟨hcar, hmem⟩ := (mem_planeTrace).mp (hγ t)
    refine (Work.Smooth.Morse.mem_region).mpr ⟨hcar, ?_⟩
    rw [Work.BoxShrink.Bubble.planeCoord_apply, hmem]
    linarith [hεpos]
  -- the gradient flow of the plane coordinate homotopes it into the negative plateau
  obtain ⟨γ', hγ'a, hhom⟩ :=
    Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region ψ hg2 hab hreg γ hγb
  refine ⟨γ', fun t ht => ?_, ?_⟩
  · have hlt : Work.BoxShrink.Bubble.planeCoord c σ u (γ' t) < -(ε / 2) :=
      ((Work.Smooth.Morse.mem_region).mp (hγ'a t)).2
    have hz : Work.BoxShrink.Bubble.planeCoord c σ u (γ' t) = 0 := by
      obtain ⟨-, hmem⟩ := (mem_planeTrace).mp ht
      rw [Work.BoxShrink.Bubble.planeCoord_apply, hmem]
      ring
    linarith [hlt, hz, hεpos]
  · exact (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm

/-! ## The crossing number of two classes of the trace vanishes -/

/-- **Two loops of the trace have vanishing crossing number.**  The first one is pushed off the
trace (with the same winding class), and then the two disjoint loops are handled by
`Work.BoxShrink.Pinch.DisjointLoopsWindingDet`. -/
theorem cross_windingRat_eq_zero (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (hT : TransverseTrace ψ c σ u)
    (γ δ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hγ : ∀ t : ℝ, γ t ∈ planeTrace (Work.Smooth.Morse.torus ψ) c σ u)
    (hδ : ∀ t : ℝ, δ t ∈ planeTrace (Work.Smooth.Morse.torus ψ) c σ u) :
    cross (windingRat (Work.Smooth.Morse.torus ψ) γ)
      (windingRat (Work.Smooth.Morse.torus ψ) δ) = 0 := by
  obtain ⟨γ', hγ'out, hw⟩ := exists_pushOff_planeTrace ψ c σ u hT γ hγ
  have hdisj : Disjoint (Set.range γ'.γ) (Set.range δ.γ) := by
    rw [Set.disjoint_left]
    rintro x ⟨t, ht⟩ ⟨t', ht'⟩
    exact hγ'out t ((ht.trans ht'.symm) ▸ hδ t')
  have hdet := DisjointLoopsWindingDet (Work.Smooth.Morse.torus ψ) γ' δ hdisj
  rw [hw] at hdet
  rw [windingRat, windingRat]
  simp only [cross]
  exact_mod_cast hdet

/-! ## The dimension bound -/

/-- **(K0) for the smooth tori.**  The winding span of the trace of a transverse plane on the
smooth torus is at most one-dimensional. -/
theorem TraceSpanLeOneSmoothHolds : Work.BoxShrink.Pinch.TraceSpanLeOneSmooth := by
  intro ψ c σ u hT
  rw [Work.SurgeryInvariance.WindingSpan]
  by_cases h : ∃ v : ℚ × ℚ,
      v ∈ Work.SurgeryInvariance.windingVectors (Work.Smooth.Morse.torus ψ)
        (planeTrace (Work.Smooth.Morse.torus ψ) c σ u) ∧ v ≠ 0
  · obtain ⟨v, hv, hv0⟩ := h
    obtain ⟨δ, hδ, hvδ⟩ := (mem_windingVectors_iff).mp hv
    have hsub : Work.SurgeryInvariance.windingVectors (Work.Smooth.Morse.torus ψ)
        (planeTrace (Work.Smooth.Morse.torus ψ) c σ u) ⊆
        Submodule.span ℚ ({v} : Set (ℚ × ℚ)) := by
      rintro w ⟨γ, hγ, rfl⟩
      have hcross : cross (windingRat (Work.Smooth.Morse.torus ψ) γ)
          (windingRat (Work.Smooth.Morse.torus ψ) δ) = 0 :=
        cross_windingRat_eq_zero ψ c σ u hT γ δ hγ hδ
      rw [hvδ] at hcross
      obtain ⟨a, ha⟩ := (cross_eq_zero_iff_eq_smul hv0).mp hcross
      simp only [windingRat] at ha
      rw [ha]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
    calc Module.finrank ℚ ↥(Submodule.span ℚ
          (Work.SurgeryInvariance.windingVectors (Work.Smooth.Morse.torus ψ)
            (planeTrace (Work.Smooth.Morse.torus ψ) c σ u)))
        ≤ Module.finrank ℚ ↥(Submodule.span ℚ ({v} : Set (ℚ × ℚ))) :=
          Submodule.finrank_mono (Submodule.span_le.mpr hsub)
      _ = 1 := finrank_span_singleton hv0
      _ ≤ 1 := le_rfl
  · have hbot : Submodule.span ℚ (Work.SurgeryInvariance.windingVectors (Work.Smooth.Morse.torus ψ)
        (planeTrace (Work.Smooth.Morse.torus ψ) c σ u)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      intro v hv
      by_contra hv0
      exact h ⟨v, hv, hv0⟩
    rw [hbot, finrank_bot]
    norm_num

end

end Work.BoxShrink.Pinch
