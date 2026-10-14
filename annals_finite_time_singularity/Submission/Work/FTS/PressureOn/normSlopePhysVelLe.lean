import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradIntegral
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.eq_const_of_weak_harmonic_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

theorem eq_const_of_weak_harmonic_smooth
    (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hV : ∀ n : ℕ, ContDiff ℝ n V)
    (hbdd : ∃ C : ℝ, ∀ x, ‖V x‖ ≤ C)
    (h : ∀ W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ n : ℕ, ContDiff ℝ n W) → HasCompactSupport W →
      ∫ x, inner ℝ (V x) (Work.FTS.PressureOn.laplaceTraceVec W x) = 0) :
    ∃ c : EuclideanSpace ℝ (Fin 3), ∀ x, V x = c := by
  -- `ΔV` (trace of the Hessian, componentwise) is continuous.
  have hcΔV : Continuous (Work.FTS.PressureOn.laplaceTraceVec V) := by
    unfold Work.FTS.PressureOn.laplaceTraceVec
    refine continuous_finsetSum _ (fun i _ => ?_)
    have hψ : ContDiff ℝ 1
        (fun w : Work.FTS.PressureOn.R3 => fderiv ℝ V w (FiniteTimeSingularity.e i)) := by
      fun_prop
    have hcont := hψ.continuous_fderiv (by norm_num)
    exact (ContinuousLinearMap.apply ℝ Work.FTS.PressureOn.R3
      (FiniteTimeSingularity.e i)).continuous.comp hcont
  -- Green's second identity turns the weak harmonicity of `V` into weak harmonicity of `ΔV`.
  have hweak : ∀ W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ n : ℕ, ContDiff ℝ n W) → HasCompactSupport W →
      ∫ x, inner ℝ (Work.FTS.PressureOn.laplaceTraceVec V x) (W x) = 0 := by
    intro W hW hWc
    rw [← Work.FTS.PressureOn.Auxiliary.integral_inner_laplaceTraceVec_comm V W hV hW hWc]
    exact h W hW hWc
  -- Testing against every smooth compactly supported field, `ΔV` must vanish identically.
  have hzero : ∀ x, Work.FTS.PressureOn.laplaceTraceVec V x = 0 :=
    Work.FTS.BSSwirl.eq_zero_of_forall_inner_test hcΔV hweak
  -- Hence each coordinate of `V` is a classical harmonic function.
  have hcoord : ∀ j : Fin 3, ∀ x,
      Work.FTS.PressureOn.laplaceTrace (fun y : EuclideanSpace ℝ (Fin 3) => V y j) x = 0 := by
    intro j x
    have h1 := Work.FTS.PressureOn.Green.IgslvAux.laplaceTraceVec_coord V (hV 2) x j
    rw [hzero x] at h1
    simpa using h1.symm
  obtain ⟨C, hC⟩ := hbdd
  have hbdd_coord : ∀ j : Fin 3, ∃ C' : ℝ,
      ∀ y : EuclideanSpace ℝ (Fin 3), |V y j| ≤ C' := by
    intro j
    refine ⟨C, fun y => ?_⟩
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (V y) j).trans (hC y)
  have hconst_coord : ∀ j : Fin 3, ∃ c : ℝ, ∀ y : EuclideanSpace ℝ (Fin 3), V y j = c := by
    intro j
    refine Work.FTS.PressureOn.Auxiliary.bounded_harmonic_const
      (fun y : EuclideanSpace ℝ (Fin 3) => V y j) (fun n => ?_) (hcoord j) (hbdd_coord j)
    have h := (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp (hV n)
    simpa [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using h
  choose c hc using hconst_coord
  exact ⟨WithLp.toLp 2 (fun j => c j), fun x => by
    apply WithLp.ofLp_injective
    exact funext (fun j => hc j x)⟩

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.lipschitz_time_lamb_strips =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **Joint Lipschitz dependence on time, of the vorticity and of the physical velocity.**

`Work.FTS.PressureOn.lipschitz_time_lamb_strips`.

Both conclusions are *uniform in the space variable* Lipschitz bounds on `[0,S]`, `S < T`, with
`t ∈ [0,S]` as the base point.

* **The vorticity.**  This is `Work.FTS.PressureOn.lipschitzTimeOmegaIcc`: `∂ₜω` is jointly
  continuous on the half-open strip `ℝ³ × [0,T)`, so it is bounded on the compact box
  `B(0,max R 0) × [0,S]`, and off that box the slice is identically `0` on `[0,S]`, so its right
  derivative vanishes there as well (the only point needing care is `s = 0`, where uniqueness of
  the one-sided derivative on the half-line is used); the mean value inequality
  (`Work.FTS.PressureOn.lipschitz_time_of_hasDerivWithinAt`) finishes.  The time-continuity of the
  curves `s ↦ ω x s` is `Work.FTS.PressureOn.continuousOn_time_omega_of_strips`.

* **The velocity.**  `physVel ω x s = BS(ω · s) x` is linear in the vorticity argument
  (`Work.StabilityFar.Decay.biotSavart_sub`), so the difference of the two slices is the
  Biot–Savart field of the *difference* vorticity, which is supported in `B(0,max R 0)` and
  bounded by `C |s - t|` by the vorticity bound.  The explicit-constant Biot–Savart estimate
  `Work.FTS.PressureOn.biotSavartDecayExplicit` then gives
  `‖BS(ω · s - ω · t) x‖ ≤ 3 (C|s-t|) R (1+4R²)/(1+‖x‖²) ≤ 3 C R (1+4R²) |s-t|`
  — the uniformity in `x` coming from the `(1+‖x‖²)⁻¹` decay of the Biot–Savart field of a
  compactly supported vorticity.  The inputs of the two additivity/decay lemmas (uniform bound
  and a.e. strong measurability of the slices on `[0,S]`) are
  `Work.FTS.PressureOn.omegaSliceRegularPos` on `(0,S]` together with the extension to `s = 0`
  `Work.FTS.PressureOn.aeStronglyMeasurableAndBoundAtZero`. -/
theorem lipschitz_time_lamb_strips {α : NNReal} {ω : R3 → ℝ → R3} {T S t : ℝ}
    (hS : S ∈ Set.Ioo 0 T) (ht : t ∈ Set.Icc 0 S)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s)
    (hsupp : ∃ R, ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => FiniteTimeSingularity.timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x s) (Set.Ici s) s) :
    (∃ C : ℝ, ∀ x : R3, ∀ s ∈ Set.Icc 0 S, ‖ω x s - ω x t‖ ≤ C * |s - t|) ∧
      (∃ C : ℝ, ∀ x : R3, ∀ s ∈ Set.Icc 0 S,
        ‖Work.FTS.Physical.physVel ω x s - Work.FTS.Physical.physVel ω x t‖ ≤ C * |s - t|) := by
  -- time-continuity of the vorticity curves on `[0,S]`
  have hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S) :=
    continuousOn_time_omega_of_strips hS hstrips hcurl
  -- (a) the vorticity is Lipschitz in time, uniformly in `x`
  obtain ⟨C, hC, hlip⟩ := lipschitzTimeOmegaIcc hS hsupp hcontDt hderiv hcontω
  refine ⟨⟨C, fun x s hs => hlip x s hs t ht⟩, ?_⟩
  -- the support radius, normalised to be nonnegative
  obtain ⟨R₀, hR₀⟩ := hsupp
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hsuppR : ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R := by
    intro s hs x hx
    rw [hRdef]
    exact le_trans (hR₀ s hs x hx) (le_max_left _ _)
  -- uniform bound and a.e. strong measurability of the vorticity slices on `[0,S]`
  obtain ⟨⟨M, hM, hbdd_pos⟩, hmeas_pos⟩ := omegaSliceRegularPos hS hstrips hcurl
  obtain ⟨hbdd0, hmeas0⟩ :=
    aeStronglyMeasurableAndBoundAtZero hS.1 hM hbdd_pos hmeas_pos hcontω
  have hbdd : ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M := by
    intro s hs x
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hbdd0 x
    · exact hbdd_pos s ⟨h, hs.2⟩ x
  have hmeas : ∀ s ∈ Set.Icc 0 S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hmeas0
    · exact hmeas_pos s ⟨h, hs.2⟩
  -- (b) the velocity is Lipschitz in time, uniformly in `x`
  refine ⟨3 * C * R * (1 + 4 * R ^ 2), fun x s hs => ?_⟩
  -- linearity of Biot–Savart on the difference of the two slices
  have hsub : Work.LWP.biotSavart (fun z => ω z s - ω z t) x
      = Work.LWP.biotSavart (fun z => ω z s) x - Work.LWP.biotSavart (fun z => ω z t) x := by
    have h := Work.StabilityFar.Decay.biotSavart_sub (f := fun z => ω z s) (g := fun z => ω z t)
      hR hM (fun z => hbdd s hs z) (fun z => hbdd t ht z)
      (fun z hz => by simpa [Metric.mem_closedBall, dist_eq_norm] using hsuppR s hs z hz)
      (fun z hz => by simpa [Metric.mem_closedBall, dist_eq_norm] using hsuppR t ht z hz)
      (hmeas s hs) (hmeas t ht) x
    rwa [show (fun z => ω z s) - (fun z => ω z t) = fun z => ω z s - ω z t from by
      funext z; rw [Pi.sub_apply]] at h
  have hdiff : Work.FTS.Physical.physVel ω x s - Work.FTS.Physical.physVel ω x t
      = Work.LWP.biotSavart (fun z => ω z s - ω z t) x := by
    rw [Work.FTS.Physical.physVel_apply ω x s, Work.FTS.Physical.physVel_apply ω x t, ← hsub]
  rw [hdiff]
  -- the difference field is supported in `B(0,R)`
  have hgsupp : ∀ z, ω z s - ω z t ≠ 0 → z ∈ Metric.closedBall (0 : R3) R := by
    intro z hz
    have h1 : ω z s ≠ 0 ∨ ω z t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz (by rw [hcon.1, hcon.2, sub_zero])
    rcases h1 with h | h
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hsuppR s hs z h
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hsuppR t ht z h
  -- the explicit-constant decay of the Biot–Savart field of the difference
  have hdec := biotSavartDecayExplicit (R := R) (M := C * |s - t|) hR
    (mul_nonneg hC (abs_nonneg _)) (fun z => hlip z s hs t ht) hgsupp x
  calc ‖Work.LWP.biotSavart (fun z => ω z s - ω z t) x‖
      ≤ 3 * (C * |s - t|) * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := hdec
    _ ≤ 3 * (C * |s - t|) * R * (1 + 4 * R ^ 2) :=
        div_le_self (by positivity) (by nlinarith [sq_nonneg ‖x‖])
    _ = (3 * C * R * (1 + 4 * R ^ 2)) * |s - t| := by ring

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.normSlopePhysVelLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

namespace Work.FTS.PressureOn

/-- **Slope bound for the Biot–Savart velocity in the time variable** (piece of
`tendsto_timeDeriv_physVel`).

If the vorticity slices `ω · s`, `s ∈ Icc 0 S`, are bounded by `M`, supported in `B(0,R)` and
a.e. strongly measurable, and if `ω` is Lipschitz in time on `[0,S]` with constant `C`, then for
`t ∈ Icc 0 S` and every `y ∈ (t,S)` the difference quotient of `physVel ω` in time is bounded
uniformly in `x` and `y` at the far-field rate `(1+‖x‖²)⁻¹`:

  `‖(y - t)⁻¹ • (physVel ω x y - physVel ω x t)‖ ≤ 3 C R (1 + 4 R²) / (1 + ‖x‖²)`.

Recipe:
* `physVel ω x s = biotSavart (ω · s) x` (`Work.FTS.Physical.physVel_apply`), and
  `Work.StabilityFar.Decay.biotSavart_sub` (f := `ω · y`, g := `ω · t`, both bounded by `M ≥ 0`,
  supported in `B(0,R)`, a.e. strongly measurable) gives
  `physVel ω x y - physVel ω x t = biotSavart (ω · y - ω · t) x`;
* the difference field is bounded by `C (y - t)` (`hlip` at `(y,t)`, `|y-t| = y-t > 0`) and is
  supported in `B(0,R)`;
* the explicit-constant far-field decay (state and prove the following helper in your own file,
  copying the proof of `Work.FTS.PressureOn.biotSavart_decay` from
  `Submission/Work/FTS/PressureOn/biotSavart_decay.lean`, which glues
  `Work.LWP.BiotSavart.norm_biotSavart_near` and `Work.LWP.BiotSavart.farField_decay_const`):
  for `M ≥ 0`, `R ≥ 0`, `∀ y, ‖g y‖ ≤ M`, `∀ y, g y ≠ 0 → y ∈ closedBall 0 R` and all `x`,
  `‖biotSavart g x‖ ≤ (3 * M * R * (1 + 4 * R ^ 2)) / (1 + ‖x‖ ^ 2)`
  (`Work.FTS.PressureOn.biotSavart_decay` only gives `∃ K`, so you need this explicit form);
* finish with `norm_smul`/`Real.norm_eq_abs`, `abs_of_pos (sub_pos.mpr hy.1)` and `field_simp`/
  `ring` on the arithmetic, using `0 < y - t` and `0 < 1 + ‖x‖ ^ 2`. -/
theorem normSlopePhysVelLe {ω : R3 → ℝ → R3} {S t M C R : ℝ}
    (ht : t ∈ Set.Icc 0 S) (hM : 0 ≤ M) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hsupp : ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hbdd : ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M)
    (hmeas : ∀ s ∈ Set.Icc 0 S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume)
    (hlip : ∀ x, ∀ s ∈ Set.Icc 0 S, ∀ s' ∈ Set.Icc 0 S, ‖ω x s - ω x s'‖ ≤ C * |s - s'|) :
    ∀ x : R3, ∀ y ∈ Set.Ioo t S,
      ‖(y - t)⁻¹ • (Work.FTS.Physical.physVel ω x y - Work.FTS.Physical.physVel ω x t)‖
        ≤ (3 * C * R * (1 + 4 * R ^ 2)) / (1 + ‖x‖ ^ 2) := by
  intro x y hy
  -- `y` lies in the time strip `[0,S]` as well
  have hyIcc : y ∈ Set.Icc 0 S := ⟨le_trans ht.1 (le_of_lt hy.1), le_of_lt hy.2⟩
  have hyt : 0 < y - t := sub_pos.mpr hy.1
  -- bounds and supports of the two vorticity slices
  have hfy : ∀ z, ‖ω z y‖ ≤ M := fun z => hbdd y hyIcc z
  have hft : ∀ z, ‖ω z t‖ ≤ M := fun z => hbdd t ht z
  have hsy : ∀ z, ω z y ≠ 0 → z ∈ Metric.closedBall (0 : R3) R := fun z hz =>
    by simpa [Metric.mem_closedBall, dist_eq_norm] using hsupp y hyIcc z hz
  have hst : ∀ z, ω z t ≠ 0 → z ∈ Metric.closedBall (0 : R3) R := fun z hz =>
    by simpa [Metric.mem_closedBall, dist_eq_norm] using hsupp t ht z hz
  -- additivity of the Biot–Savart operator on the difference of the two slices
  have hsub : Work.LWP.biotSavart (fun z => ω z y - ω z t) x
      = Work.LWP.biotSavart (fun z => ω z y) x - Work.LWP.biotSavart (fun z => ω z t) x := by
    have h := Work.StabilityFar.Decay.biotSavart_sub (f := fun z => ω z y) (g := fun z => ω z t)
      hR hM hfy hft hsy hst (hmeas y hyIcc) (hmeas t ht) x
    rwa [show (fun z => ω z y) - (fun z => ω z t) = fun z => ω z y - ω z t from by
      funext z; rw [Pi.sub_apply]] at h
  have hdiff : Work.FTS.Physical.physVel ω x y - Work.FTS.Physical.physVel ω x t
      = Work.LWP.biotSavart (fun z => ω z y - ω z t) x := by
    rw [Work.FTS.Physical.physVel_apply ω x y, Work.FTS.Physical.physVel_apply ω x t, ← hsub]
  -- the difference field is bounded by `C (y - t)` and supported in `B(0,R)`
  have hyM : (0 : ℝ) ≤ C * (y - t) := mul_nonneg hC (le_of_lt hyt)
  have hgbdd : ∀ z, ‖ω z y - ω z t‖ ≤ C * (y - t) := by
    intro z
    have h := hlip z y hyIcc t ht
    rwa [abs_of_pos hyt] at h
  have hgsupp : ∀ z, ω z y - ω z t ≠ 0 → z ∈ Metric.closedBall (0 : R3) R := by
    intro z hz
    rcases eq_or_ne (ω z y) 0 with h | h
    · refine hst z ?_
      intro h0
      exact hz (by rw [h, h0, sub_zero])
    · exact hsy z h
  -- the explicit-constant far-field decay of the difference field
  have hdec := biotSavartDecayExplicit hR hyM hgbdd hgsupp x
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyt)]
  calc (y - t)⁻¹ * ‖Work.LWP.biotSavart (fun z => ω z y - ω z t) x‖
      ≤ (y - t)⁻¹ * (3 * (C * (y - t)) * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hdec (inv_nonneg.mpr (le_of_lt hyt))
    _ = 3 * C * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := by
        have h1 : y - t ≠ 0 := ne_of_gt hyt
        have h2 : (1 : ℝ) + ‖x‖ ^ 2 ≠ 0 := by positivity
        field_simp

end Work.FTS.PressureOn

/-- **Slope bound for the Biot–Savart velocity in the time variable**, under its canonical
qualified name `Work.FTS.PressureOn.normSlopePhysVelLe` (the skeleton of this file opened the
namespace `Work.FTS.PressureOn` twice, which places the declaration above at
`Work.FTS.PressureOn.Work.FTS.PressureOn.normSlopePhysVelLe`; this is the same theorem, with the
name consumers use).  See the docstring above for the statement and the proof. -/
theorem normSlopePhysVelLe {ω : R3 → ℝ → R3} {S t M C R : ℝ}
    (ht : t ∈ Set.Icc 0 S) (hM : 0 ≤ M) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hsupp : ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hbdd : ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M)
    (hmeas : ∀ s ∈ Set.Icc 0 S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume)
    (hlip : ∀ x, ∀ s ∈ Set.Icc 0 S, ∀ s' ∈ Set.Icc 0 S, ‖ω x s - ω x s'‖ ≤ C * |s - s'|) :
    ∀ x : R3, ∀ y ∈ Set.Ioo t S,
      ‖(y - t)⁻¹ • (Work.FTS.Physical.physVel ω x y - Work.FTS.Physical.physVel ω x t)‖
        ≤ (3 * C * R * (1 + 4 * R ^ 2)) / (1 + ‖x‖ ^ 2) :=
  _root_.Work.FTS.PressureOn.Work.FTS.PressureOn.normSlopePhysVelLe
    ht hM hC hR hsupp hbdd hmeas hlip

end Work.FTS.PressureOn
end
