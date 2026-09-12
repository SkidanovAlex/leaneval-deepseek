import Submission.Model
import Submission.ModelCore
import Submission.ModelFlow
import Mathlib

/-!
# The linearized (Jacobi) equation along a fixed geodesic has solutions

Task: prove the final theorem `linearized_exists`.

## Statement (in words)

Let `z : ℝ → E × E` be a solution of the geodesic first-order system
`z' = V z` with `V := odeField g` (i.e. `HasDerivAt z (odeField g (z t)) t` on
`Ioo (-ε) ε`).  Then for any initial variation `w : E × E` the *linearized* initial value
problem

    J 0 = w,    HasDerivAt J ((fderiv ℝ (odeField g)) (z t) (J t)) t   (t ∈ Ioo (-ε) ε)

has a solution `J : ℝ → E × E`.

## Why true / proof route

This is a linear, non-autonomous ODE `J' = L(t) J` with `L(t) := fderiv ℝ (odeField g) (z t)`
(a continuous linear operator, since `z` is continuous and `odeField g` is `C¹` everywhere —
`Submission.ModelCore.odeField_contDiffAt` gives `ContDiffAt ℝ 1 (odeField g) x` at each `x`,
hence `DifferentiableAt`, so `fderiv` exists and is continuous along `z`).  Linear ODEs with
continuous bounded coefficients have global solutions on any closed interval, by the
Picard–Lindelöf theorem (the right hand side `(t, J) ↦ L t J` is Lipschitz in `J` with constant
`sup ‖L t‖ < ∞` on a compact interval, and continuous in `t`).  On the open interval
`Ioo (-ε) ε`, take a nested exhaustion by compact intervals around `0`; a solution on each, then
glue (they agree by uniqueness — or simply note Picard directly gives a solution on any
`symmetric closed interval Icc (-T) T` inside `Ioo (-ε) ε`, and since we only need existence
near `0`, state the conclusion on `Ioo (-T) T` for the `T` from the theorem).

## Available Mathlib facts

* `IsPicardLindelof` structure and existence theorems in `Mathlib/Analysis/ODE/PicardLindelof.lean`
  (read the header of that file and of `Mathlib/Analysis/ODE/ExistUnique.lean`).
* `ContDiffAt.exists_lipschitzOnWith` to get the Lipschitz constant of `V` near points, but here
  the *linear* structure gives the Lipschitz constant directly: `‖L t (J₁ - J₂)‖ ≤ ‖L t‖ * ‖J₁ - J₂‖`
  with `‖L t‖` bounded on a compact interval (use `ContinuousOn.norm` / `isCompact_Icc` +
  `ContinuousOn.isBounded` or just a global bound from continuity at each point and compactness).
* For a *time-dependent* linear field `f (t, J) := L t J`, apply
  `IsPicardLindelof` with `lipschitzOnWith` constant `K := sup ‖L t‖` and `norm_le` constant
  `Lb := sup ‖L t‖ * ‖w‖`-style (or simply note `‖L t J‖ ≤ K‖J‖` and solutions stay near `w`).
  The cleanest: use `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` or the
  `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`-style theorems
  from `ExistUnique.lean` with `f := fun t J => L t J` and `f` continuous in (t,J) — you may
  first prove the needed continuity/lipschitz lemmas yourself.

## Suggested concrete statement to prove (keep the signature)

    theorem linearized_exists (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
        (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε)
        {c vel : ℝ → E} {w : E × E}
        (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
        (hv : ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t) :
        ∃ T > 0, T < ε ∧ ∃ J : ℝ → E × E,
          J 0 = w ∧
          (∀ t ∈ Ioo (-T) T,
            HasDerivAt J ((fderiv ℝ (odeField g)) (c t, vel t) (J t)) t)

(Note: the linearized coefficients depend on `z t = (c t, vel t)`.)

You may add helper lemmas (e.g. first define `z := fun t => (c t, vel t)` and reduce the two
`HasDerivAt` hypotheses to one on `z`, as in `Submission/ModelUniq.lean`).  Do NOT change the
statement of `linearized_exists`.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- The linearized geodesic (Jacobi) equation along a fixed geodesic has solutions with any
initial variation. -/
theorem linearized_exists (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε)
    {c vel : ℝ → E} {w : E × E}
    (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t) :
    ∃ T > 0, T < ε ∧ ∃ J : ℝ → E × E,
      J 0 = w ∧
      (∀ t ∈ Ioo (-T) T,
        HasDerivAt J ((fderiv ℝ (odeField g)) (c t, vel t) (J t)) t) := by
  let z : ℝ → E × E := fun t => (c t, vel t)
  have hz (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt z (odeField g (z t)) t := by
    dsimp [z]
    exact ((hc t ht).prodMk (hv t ht)).congr_deriv (by simp [odeField])
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith
  have hdf (p : E × E) : ContinuousAt (fderiv ℝ (odeField g)) p := by
    exact (odeField_contDiffAt g hg hinv p.1 p.2).continuousAt_fderiv (by norm_num)
  have hcontD : Continuous (fderiv ℝ (odeField g)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact hdf p
  let L : ℝ → (E × E) →L[ℝ] (E × E) := fun t => fderiv ℝ (odeField g) (z t)
  have hL0 : ContinuousAt L 0 := by
    have hc' : ContinuousAt (fun t => fderiv ℝ (odeField g) (z t)) 0 :=
      (hdf (z 0)).comp (hz 0 h0).continuousAt
    simpa [L] using hc'
  -- a local uniform bound for the coefficient operator `L`
  let K : ℝ := ‖L 0‖ + 1
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  rcases Metric.continuousAt_iff.mp hL0 (1 : ℝ) zero_lt_one with ⟨δ, hδpos, hδ⟩
  have hnorm (t : ℝ) (ht : dist t 0 < δ) : ‖L t‖ ≤ K := by
    have hLt0 : dist (L t) (L 0) < 1 := hδ ht
    dsimp [K]
    have hsub : ‖L t‖ ≤ ‖L t - L 0‖ + ‖L 0‖ := by
      calc
        ‖L t‖ = ‖(L t - L 0) + L 0‖ := by abel_nf
        _ ≤ ‖L t - L 0‖ + ‖L 0‖ := norm_add_le _ _
    have hlt : ‖L t - L 0‖ + ‖L 0‖ ≤ 1 + ‖L 0‖ := by
      rw [← dist_eq_norm]
      linarith
    linarith
  let Lb : ℝ := K * (‖w‖ + 1)
  have hLbpos : 0 < Lb := by
    dsimp [Lb]
    positivity
  -- pick the time endpoint `T` small enough for all the estimates below
  let T : ℝ := min (min (ε / 2) (δ / 2)) (1 / (2 * Lb))
  have hTpos : 0 < T := by
    dsimp [T]
    exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hTltε : T < ε := by
    dsimp [T]
    calc
      min (min (ε / 2) (δ / 2)) (1 / (2 * Lb)) ≤ min (ε / 2) (δ / 2) := min_le_left _ _
      _ ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  have hTltδ : T < δ := by
    dsimp [T]
    calc
      min (min (ε / 2) (δ / 2)) (1 / (2 * Lb)) ≤ min (ε / 2) (δ / 2) := min_le_left _ _
      _ ≤ δ / 2 := min_le_right _ _
      _ < δ := by linarith
  have hTle : T ≤ 1 / (2 * Lb) := by
    dsimp [T]
    exact min_le_right _ _
  have hTmul : Lb * T ≤ 1 := by
    have hprod : Lb * T ≤ Lb * (1 / (2 * Lb)) :=
      mul_le_mul_of_nonneg_left hTle (le_of_lt hLbpos)
    have h2 : Lb * (1 / (2 * Lb)) = 1 / 2 := by
      field_simp [hLbpos.ne']
    linarith
  -- the coefficient map t ↦ L t is continuous on Icc (-T) T
  have hzcontOn : ContinuousOn z (Icc (-T) T) := by
    intro t ht
    have htI : t ∈ Ioo (-ε) ε := by
      constructor
      · linarith [ht.1, hTltε]
      · linarith [ht.2, hTltε]
    exact (hz t htI).continuousAt.continuousWithinAt
  have hLcontOn : ContinuousOn L (Icc (-T) T) := by
    have hc1 : ContinuousOn (fun t => fderiv ℝ (odeField g) (z t)) (Icc (-T) T) :=
      hcontD.comp_continuousOn hzcontOn
    simpa [L] using hc1
  have hnormI (t : ℝ) (ht : t ∈ Icc (-T) T) : ‖L t‖ ≤ K := by
    apply hnorm
    rw [dist_eq_norm]
    simp only [sub_zero]
    calc
      ‖t‖ ≤ T := by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ht
      _ < δ := hTltδ
  -- the time-dependent linear field of the linearized equation
  let F : ℝ → (E × E) → (E × E) := fun t J => L t J
  let Knn : NNReal := ⟨K, le_of_lt hKpos⟩
  let Lbnn : NNReal := ⟨Lb, le_of_lt hLbpos⟩
  have hmem0 : (0 : ℝ) ∈ Icc (-T) T := by
    constructor <;> linarith
  -- Picard--Lindelöf hypotheses for the linear field
  have hpl : IsPicardLindelof F (tmin := -T) (tmax := T) ⟨0, hmem0⟩ w (1 : NNReal) 0 Lbnn Knn := by
    refine IsPicardLindelof.mk ?lipschitzOnWith ?continuousOn ?norm_le ?mul_max_le
    · intro t ht
      have hKle : ‖L t‖₊ ≤ Knn := by
        dsimp [Knn]
        exact_mod_cast hnormI t ht
      have hlip : LipschitzOnWith Knn (L t) (closedBall w (1 : ℝ)) :=
        ((L t).lipschitz.weaken hKle).lipschitzOnWith
      simpa [F] using hlip
    · intro J hJ
      have heval : Continuous (fun A : (E × E) →L[ℝ] (E × E) => A J) := by
        fun_prop
      have h : ContinuousOn (fun t => (L t) J) (Icc (-T) T) := heval.comp_continuousOn hLcontOn
      simpa [F] using h
    · intro t ht J hJ
      have hdist : dist J w ≤ 1 := by simpa using hJ
      have hnormJ : ‖J‖ ≤ ‖w‖ + 1 := by
        calc
          ‖J‖ = ‖(J - w) + w‖ := by abel_nf
          _ ≤ ‖J - w‖ + ‖w‖ := norm_add_le _ _
          _ = dist J w + ‖w‖ := by rw [← dist_eq_norm J w]
          _ ≤ ‖w‖ + 1 := by linarith
      have hb1 : ‖L t J‖ ≤ ‖L t‖ * ‖J‖ := (L t).le_opNorm J
      have hb2 : ‖L t‖ * ‖J‖ ≤ K * ‖J‖ :=
        mul_le_mul_of_nonneg_right (hnormI t ht) (norm_nonneg J)
      have hb3 : K * ‖J‖ ≤ K * (‖w‖ + 1) :=
        mul_le_mul_of_nonneg_left hnormJ (le_of_lt hKpos)
      have hb4 : K * (‖w‖ + 1) = Lb := by dsimp [Lb]
      have hb5 : ‖L t J‖ ≤ Lb := by
        calc
          ‖L t J‖ ≤ ‖L t‖ * ‖J‖ := hb1
          _ ≤ K * ‖J‖ := hb2
          _ ≤ K * (‖w‖ + 1) := hb3
          _ = Lb := hb4
      dsimp [F, Lbnn]
      exact hb5
    · simp
      dsimp [Lbnn]
      change Lb * T ≤ (1 : ℝ)
      exact hTmul
  rcases hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ with ⟨J, hJ0, hJd⟩
  refine ⟨T, hTpos, hTltε, J, ?_, ?_⟩
  · simpa using hJ0
  · intro t ht
    have htIcc : t ∈ Icc (-T) T := Ioo_subset_Icc_self ht
    have hd := hJd t htIcc
    have hdAt : HasDerivAt J (F t (J t)) t := hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    simpa [F, L, z] using hdAt


end

end Submission.Model
