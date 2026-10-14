import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.LWP.Main
import Submission.Work.Stability.Cutoff
import Submission.Work.StabilityFar.Assembly
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
import Submission.Work.StabilityFar.St4
import Submission.Work.StabilityFar.St4Refine
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.SolutionDelivery.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- `ℝ³` (definitionally `Work.LWP.R3` and `Work.StabilityFar.R3`). -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The cut-off datum of `St1`

`Work.Stability.omegaCut L ω = χ(ρ/L) • ω` is the physical cut-off of `St1`: `χ` is a `C^∞` bump
equal to `1` on `[-1,1]` and `0` outside `(-2,2)`, and `ρ(x) = ‖x‖`.  The **cut-off datum** of the
construction is `χ(ρ/L)` times the paper's self-similar initial vorticity.  Its elementary
properties (support in `B(0,2L)`, boundedness, measurability, integrability, `α`-Hölder
regularity) are proved in `Work.SolutionDelivery.DatumCut`. -/

/-- **The cut-off datum vorticity of `St1`**: `ω₀ = χ(ρ/L) • ωS`. -/
def cutDatum (L : ℝ) (ωS : R3 → R3) : R3 → R3 := Work.Stability.omegaCut L ωS


/-! ## The extended window

The far-field chapter imposes everything on the two-sided window `window T = [-1, T+1]`, because
`∂ₜω` is a *two-sided* derivative.  The *core* regularity of the constructed vorticity, however,
is delivered by the construction on a genuine neighbourhood of that window (the self-similar
formula is smooth there), and the derivations below need one free time step on each side in order
to make the time-differentiation `∂ₜω` an honest derivative and to apply the mean value
inequality.  We therefore impose the core regularity on the *extended* window
`extWindow T = (-2, T+2) ⊇ window T`. -/

/-- The extended two-sided window `(-2, T+2)`, an open neighbourhood of `window T = [-1, T+1]`. -/
def extWindow (T : ℝ) : Set ℝ := Set.Ioo (-2) (T + 2)


theorem window_subset_extWindow (T : ℝ) : Work.StabilityFar.window T ⊆ extWindow T := by
  intro t ht
  rw [Work.StabilityFar.mem_window] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩



theorem isOpen_extWindow (T : ℝ) : IsOpen (extWindow T) := isOpen_Ioo


/-! ## The norm form of the Hölder condition

`HolderOnWith` is stated in `edist` coordinates; the derivations below use the norm form. -/

/-- The norm-coordinate form of `HolderOnWith`. -/
theorem norm_le_of_holderOnWith {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {C r : NNReal} {f : X → Y} {s : Set X} (h : HolderOnWith C r f s) :
    ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (r : ℝ) := by
  intro x hx y hy
  have h1 := h.edist_le hx hy
  rw [edist_dist, edist_dist, dist_eq_norm] at h1
  have hC : ((C : ℝ≥0∞)) = ENNReal.ofReal (C : ℝ) := ENNReal.coe_nnreal_eq _
  rw [hC] at h1
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity)] at h1
  rw [← ENNReal.ofReal_mul (by positivity)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1

/-! ## The input package: the constructed solution

Every field is a statement about the objects of a *different* chapter; the list of exactly which
chapter delivers each is in `NOTES.md` of this directory.  Nothing here is a restatement of a
field of `Work.StabilityFar.AssemblyInputs` except the ones explicitly marked "direct". -/

/-- **The constructed solution, at the level of the chapters that deliver it.**

The interface has been reduced as far as the workspace's own objects allow: the *solution* side is
the LWP chapter's maximal solution (`Work.LWP.MaximalSolution`, whose existence is itself an LWP
input applied to the datum), and the *datum* side is the concrete `St1` cut-off
`ω₀ = χ(ρ/L)·ωS` of the paper's self-similar initial vorticity `ωS`, whose elementary properties
are proved in `Work.SolutionDelivery.DatumCut`.

* `lwp` — the LWP chapter's analytic inputs;
* `R`, `hR`, `M`, `hM`, `M₁`, `hM₁` — the support radius and the `L^∞` bounds of the vorticity;
* `L`, `hL`, `ωS`, `ωS_meas`, `ωS_bdd`, `ωS_cdh` — the **paper's self-similar initial vorticity**
  and the three properties the construction gives it (measurability, the `L^∞` bound, `C^{1,α}`);
  the cut-off datum is `ω₀ := cutDatum L ωS = χ(ρ/L)·ωS`, and its integrability, support in
  `B(0,2L)`, bound and `α`-Hölder regularity are **derived** (`ω₀_int`, `ω₀_supp`, `ω₀_bdd`,
  `ω₀_holder`);
* `ωS_div`, `ωS_odd` — the two **`Cyl`/Biot–Savart dictionary** clauses for the cut-off datum:
  divergence-freeness (the vorticity is a `θ`-field and the cut-off is radial) and the oddness of
  its Biot–Savart field (`DatumOdd.lean` reduces the latter to axisymmetry + reflection parity);
* `T`, `hmax` — the maximal time and the LWP chapter's maximal solution with datum `u₀ = BS ω₀`;
  `hT`, `p`, `u`, `sol`, `odd` and the core regularity `coreU` are **derived** from `hmax`;
* `smooth` — `C¹` on a neighbourhood of the two-sided window (the construction's backward
  extension of the solution; `Work.LWP.MaximalSolution` only knows the forward strips);
* `ω`, `bsSliceExt` — the vorticity and the Biot–Savart reconstruction on the *open* extended
  window (from which `bsSlice` and, by differentiation under the integral, `bsTimeSlice` follow);
* `hSupp`, `hBdd`, `hBddDt`, `hDivω`, `hωcore` — the **boxes** of the vorticity: support radius,
  `L^∞` bounds for `ω` and `∂ₜω`, divergence-freeness of the slices, and the core `C^{1,α}`
  regularity of `ω` (from which `H`, `H₁`, the measurability of both fields and the
  differentiability of the slices are derived);
* `lam`, `hlam_pos`, `hlam_le`, `c₀`, `hc₀`, `hansatz` — the **`St5` interface**: the modulation
  `λ̄`, its bound `0 < λ̄(t) ≤ 2(T-t)`, and the pointwise lower bound coming from
  `|F_* + g| ≥ c₀α` somewhere (`Work.StabilityFar.Profile.exists_Fstar_add_ge`). -/
structure ConstructedSolution (α : NNReal) where
  /-- the analytic inputs of the LWP/continuation chapter -/
  lwp : Work.LWP.LWPInputs α
  /-- the support radius of the vorticity -/
  R : ℝ
  /-- `R > 0` -/
  hR : 0 < R
  /-- the `L^∞` bound for `ω` -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- the `L^∞` bound for `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- the cut-off parameter `L` of `St1` -/
  L : ℝ
  /-- `L > 0` -/
  hL : 0 < L
  /-- the paper's self-similar initial vorticity (before the cut-off) -/
  ωS : R3 → R3
  /-- `ωS` is measurable -/
  ωS_meas : MeasureTheory.AEStronglyMeasurable ωS MeasureTheory.volume
  /-- `ωS` is bounded by `M` -/
  ωS_bdd : ∀ x : R3, ‖ωS x‖ ≤ M
  /-- `ωS` is `C^{1,α}` -/
  ωS_cdh : IsContDiffHolder ℝ α ωS
  /-- the cut-off datum is divergence-free (the `Cyl` dictionary) -/
  ωS_div : ∀ x : R3, div (cutDatum L ωS) x = 0
  /-- the Biot–Savart field of the cut-off datum is odd (the `Cyl` parity dictionary) -/
  ωS_odd : IsOdd (Work.LWP.biotSavart (cutDatum L ωS))
  /-- the maximal time of the constructed solution -/
  T : ℝ
  /-- the LWP chapter's maximal solution with datum `u₀ = BS ω₀` -/
  hmax : Work.LWP.MaximalSolution α (Work.LWP.biotSavart (cutDatum L ωS)) T
  /-- `u.uncurry` is `C¹` on a neighbourhood of the two-sided window (the construction extends the
  solution backwards in time) -/
  smooth : ContDiffOn ℝ 1 hmax.u.uncurry (Set.univ ×ˢ extWindow T)
  /-- the vorticity of the constructed solution -/
  ω : R3 → ℝ → R3
  /-- `u(x,t) = BS(ω(·,t)) x` on the **open extended window** — the definition of the constructed
  velocity.  It is imposed on the extended window because it is used both on the physical window
  (giving `bsSlice` below) and, through one free time step on each side, to *derive*
  `∂ₜu(·,t) = BS(∂ₜω(·,t))` by differentiation under the integral
  (`Work.SolutionDelivery.isTimeBiotSavartSlice_of_extSlice`). -/
  bsSliceExt : ∀ t ∈ extWindow T, ∀ x : R3,
    hmax.u x t = Work.LWP.biotSavart (fun y => ω y t) x
  /-- the vorticity slices are supported in `B(0,R)` (transport of the cut-off support along the
  flow, `Work.LWP.Transport.support_transport` + the Grönwall bound on the flow) -/
  hSupp : ∀ t ∈ extWindow T, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R
  /-- `ω` is bounded by `M` (the `ℋ⁴`/profile bound of the bootstrap) -/
  hBdd : ∀ t ∈ extWindow T, ∀ y : R3, ‖ω y t‖ ≤ M
  /-- `∂ₜω` is bounded by `M₁` (idem) -/
  hBddDt : ∀ t ∈ extWindow T, ∀ y : R3, ‖timeDeriv ω y t‖ ≤ M₁
  /-- the vorticity slices are divergence-free -/
  hDivω : ∀ t ∈ extWindow T, div (ω · t) = 0
  /-- **the core `C^{1,α}` regularity of the vorticity** (`St0`–`St3`), on the slightly larger
  ball `B(0,R+1)` so that the boundary points of `B(0,R)` are interior points — this is what makes
  the time block `∂ₜω` of the derivative an honest derivative -/
  hωcore : IsContDiffHolderOn ℝ α ω.uncurry
    (Work.StabilityFar.coreRegion (R + 1) ×ˢ extWindow T)
  /-- the modulation `λ̄` of the self-similar ansatz -/
  lam : ℝ → ℝ
  /-- `λ̄ > 0` on `[0,T)` -/
  hlam_pos : ∀ t ∈ Set.Ico 0 T, 0 < lam t
  /-- `λ̄(t) ≤ 2(T-t)` on `[0,T)` (the upper bound of the bootstrap) -/
  hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)
  /-- the profile constant of `Work.StabilityFar.Profile.exists_Fstar_add_ge` -/
  c₀ : ℝ
  /-- `c₀ > 0` -/
  hc₀ : 0 < c₀
  /-- **the `St5` interface**: at every time there is a point where the self-similar profile is
  larger than `c₀α/λ̄(t)` (the ansatz `ω = λ̄^{-1}(F_*+g)(z,θ)` evaluated at the point where
  `|F_* + g| ≥ c₀α`) -/
  hansatz : ∀ t ∈ Set.Ico 0 T, ∃ x : R3, c₀ * (α : ℝ) ≤ lam t * ‖ω x t‖

namespace ConstructedSolution

variable {α : NNReal} (C : ConstructedSolution α)

/-- **The cut-off datum**: `ω₀ = χ(ρ/L)·ωS` (`St1`). -/
abbrev ω₀ (C : ConstructedSolution α) : R3 → R3 := cutDatum C.L C.ωS


/-- The pressure of the constructed solution (`hmax.p`). -/
abbrev p (C : ConstructedSolution α) : R3 → ℝ → ℝ := C.hmax.p

/-- The velocity of the constructed solution (`hmax.u`). -/
abbrev u (C : ConstructedSolution α) : R3 → ℝ → R3 := C.hmax.u

/-- `T > 0`. -/
theorem hT (C : ConstructedSolution α) : 0 < C.T := C.hmax.T_pos

/-- `(p,u)` solves the Euler equation on `[0,T*)` with datum `BS ω₀`. -/
theorem sol (C : ConstructedSolution α) :
    IsLocalEulerEquationSolution C.p (Work.LWP.biotSavart C.ω₀) C.T C.u := C.hmax.sol

/-- The solution is odd at every time. -/
theorem odd (C : ConstructedSolution α) : ∀ t ∈ Set.Ico 0 C.T, IsOdd (C.u · t) := C.hmax.odd


/-- The window is contained in the extended window. -/
theorem window_subset (C : ConstructedSolution α) :
    Work.StabilityFar.window C.T ⊆ extWindow C.T := window_subset_extWindow C.T

/-- The support box on the physical window (restriction of `hSupp`). -/
theorem hSupp_window (C : ConstructedSolution α) :
    ∀ t ∈ Work.StabilityFar.window C.T, ∀ y : R3,
      C.ω y t ≠ 0 → y ∈ Metric.closedBall 0 C.R :=
  fun t ht => C.hSupp t (C.window_subset ht)

/-- The `L^∞` box on the physical window. -/
theorem hBdd_window (C : ConstructedSolution α) :
    ∀ t ∈ Work.StabilityFar.window C.T, ∀ y : R3, ‖C.ω y t‖ ≤ C.M :=
  fun t ht => C.hBdd t (C.window_subset ht)


/-- **The two Biot–Savart dictionary clauses of the assembly.**

* `bsSlice` — `u(·,t) = BS(ω(·,t))`, the restriction of `bsSliceExt` to the physical window;
* `bsTimeSlice` (in `Work.SolutionDelivery.BiotSavartTime`) — `∂ₜu(·,t) = BS(∂ₜω(·,t))`,
  *derived* from `bsSliceExt` by differentiation under the Biot–Savart integral. -/
theorem bsSlice (C : ConstructedSolution α) : Work.StabilityFar.IsBiotSavartSlice C.u C.ω C.T :=
  fun t ht x => C.bsSliceExt t (C.window_subset ht) x


end ConstructedSolution

end Work.SolutionDelivery
end
end
-- ===== merged: Submission.Work.Stability.HolderOfBoundedLipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ENNReal NNReal

namespace Work.Stability


end Work.Stability
end
-- ===== merged: Submission.Work.Stability.HolderSmulRightOfSupport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- **The `dist`/`HolderWith` bridge.**  A pointwise bound of the form
`dist (f x) (f y) ≤ C * (dist x y) ^ α` with real exponent `α ≥ 0` upgrades to `HolderWith C α f`
(which is stated with `edist` and the `ennreal` power).  This is the form in which all the concrete
estimates of this layer are produced. -/
lemma holderWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : NNReal} {f : X → Y}
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) : HolderWith C r f := by
  intro x y
  rw [edist_nndist, edist_nndist]
  rw [← ENNReal.coe_rpow_of_nonneg (nndist x y) r.coe_nonneg, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, coe_nndist]
  exact h x y


end Work.Stability
end
-- ===== merged: Submission.Work.Stability.LipschitzOfBoundedFderiv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- A differentiable function with bounded derivative is Lipschitz (the mean value inequality
`lipschitzWith_of_nnnorm_fderiv_le`, applied to a bound extracted from `IsBoundedFun`). -/
theorem LipschitzOfBoundedFderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : Differentiable ℝ f) (hb : IsBoundedFun (fderiv ℝ f)) :
    ∃ K : NNReal, LipschitzWith K f := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le hf
  intro x
  exact (hC (fderiv ℝ f x) ⟨x, Set.mem_univ x, rfl⟩).trans (le_max_left _ _)

end Work.Stability
end
-- ===== merged: Submission.Work.Stability.OmegaCutSupport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability



end Work.Stability
end
