/-
Section 5 of Shankar--Yuan: the master estimate `∃ B, IsMasterBound B`, reduced to the two deep
inputs of the proof:

* the **Alexandrov input** (Proposition 3.1 of the paper): a viscosity solution of the
  `σ₂ = 1` equation with `Δu ≥ 0` in the viscosity sense is twice differentiable at some point of
  `ball 0 (1/3)`, and
* the **Savin input** (Savin's small perturbation theorem, [S, Theorem 1.3]): near a point of
  twice differentiability of a limit of solutions, all nearby solutions have bounded Laplacian on
  a small ball.

Everything else in Section 5 -- the compactness/contradiction argument, the passage to the limit,
the application of the doubling inequality (Corollary 2.5) -- is proved here.
-/
import Submission.MasterReduction
import Submission.Viscosity
import Submission.GOperator
import Submission.Commons.Analysis.Calculus.ArzelaAscoli.exists_strictMono_tendstoUniformlyOn
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian
import Submission.Commons.Analysis.Calculus.Taylor.taylor_two_isLittleO

open HessianEstimates
open Commons.Analysis.Calculus.FDeriv
open Commons.Analysis.Calculus.ArzelaAscoli
open Commons.Analysis.Calculus.Taylor
open Laplacian Metric MeasureTheory Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-! ## The two deep inputs -/

/-- `g` is twice differentiable in the Fréchet sense at `y`: there are a linear form and a
symmetric bilinear form such that `g(z) - g(y) - L(z-y) - Q(z-y)(z-y) = o(‖z-y‖²)`. -/
def IsTwiceDiffAt (g : ℝ⁴ → ℝ) (y : ℝ⁴) : Prop :=
  ∃ (L : ℝ⁴ →L[ℝ] ℝ) (Q : ℝ⁴ →L[ℝ] ℝ⁴ →L[ℝ] ℝ),
    (fun z => g z - g y - L (z - y) - Q (z - y) (z - y)) =o[𝓝 y] (fun z => ‖z - y‖ ^ 2)

/-- The continuous linear functional `M ↦ -tr M`; `IsViscSubsolution negTrace u s` is the
statement that `Δu ≥ 0` on `s` in the viscosity sense. -/
noncomputable def negTrace (M : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ := -LinearMap.trace ℝ ℝ⁴ (M.toLinearMap)

/-- **Alexandrov input** (Proposition 3.1 of Shankar--Yuan).  A *continuous* viscosity solution
of the `σ₂ = 1` equation on `ball 0 3` whose Laplacian is nonnegative in the viscosity sense is
twice differentiable at some point of `ball 0 (1/3)`.

The continuity hypothesis is not an extra assumption in the application: the function `g` in
`masterBound_exists` is a locally uniform limit of continuous functions, hence continuous (see
`extraction`).  It is however needed for the proof of the statement (through the fact that the
weak derivative data determine the second order Taylor expansion of `g`). -/
def AlexandrovInput : Prop :=
  ∀ (g : ℝ⁴ → ℝ), ContinuousOn g (closedBall 0 3) →
    IsViscSolution (fun M => -Gop M) g (ball 0 3) →
    IsViscSubsolution negTrace g (ball 0 3) →
    ∃ y ∈ ball 0 (1 / 3), IsTwiceDiffAt g y

/-- **Savin input** (Savin's small perturbation theorem, [S, Theorem 1.3], in the form in which
it is used in Section 5).  Let `g` be a viscosity solution of `-G(D²g) = 0` on `ball 0 3` which is
twice differentiable at `y ∈ ball 0 3`.  Then there are `ρ₀, η > 0` such that for every `ρ ≤ ρ₀`
there is `C > 0` so that every classical solution of `σ₂(D²u) = 1` with `Δu > 0` on a neighbourhood
of `closedBall 0 3` which is `η ρ²`-close to `g` on `ball y ρ` satisfies `Δu ≤ C` on
`closedBall y (ρ/2)`. -/
def SavinInput : Prop :=
  ∀ (g : ℝ⁴ → ℝ) (y : ℝ⁴), y ∈ ball (0 : ℝ⁴) 3 →
    IsViscSolution (fun M => -Gop M) g (ball (0 : ℝ⁴) 3) → IsTwiceDiffAt g y →
    ∃ (ρ₀ η : ℝ), 0 < ρ₀ ∧ 0 < η ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ ρ₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴), IsOpen s → closedBall 0 3 ⊆ s → ContDiffOn ℝ 4 u s →
            (∀ z ∈ s, σ₂ (H u s z) = 1) → (∀ z ∈ s, 0 < (Δ u) z) →
            ball y ρ ⊆ s →
            (∀ z ∈ ball y ρ, |u z - g z| ≤ η * ρ ^ 2) →
            (∀ z ∈ closedBall y (ρ / 2), (Δ u) z ≤ C)

/-! ## Auxiliary facts -/

/-- Membership in `closedBall y ρ` is monotone in `ρ`. -/
theorem closedBall_mono {y : ℝ⁴} {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    closedBall y ρ ⊆ closedBall y ρ' :=
  fun _ hz => by
    rw [Metric.mem_closedBall] at hz ⊢
    linarith

/-- The Hessian operator `H u s x` does not depend on the domain `s`, as long as `s` is a
neighbourhood of `x`. -/
theorem H_congr_of_mem_nhds {u : ℝ⁴ → ℝ} {s t : Set ℝ⁴} {x : ℝ⁴} (hs : s ∈ 𝓝 x)
    (ht : t ∈ 𝓝 x) : HessianEstimates.H u s x = HessianEstimates.H u t x := by
  show InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ u s) s x)
      = InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ u t) t x)
  rw [hessianWithin_eq_hessian hs, hessianWithin_eq_hessian ht]

/-- If two operators are ordered by their quadratic forms then their traces are ordered. -/
theorem trace_le_trace_of_forall_inner_le {M N : ℝ⁴ →L[ℝ] ℝ⁴}
    (h : ∀ v : ℝ⁴, ⟪M v, v⟫ ≤ ⟪N v, v⟫) :
    LinearMap.trace ℝ ℝ⁴ (M.toLinearMap) ≤ LinearMap.trace ℝ ℝ⁴ (N.toLinearMap) := by
  have h' : ∀ v : ℝ⁴, ⟪(M.toLinearMap) v, v⟫ ≤ ⟪(N.toLinearMap) v, v⟫ := h
  rw [LinearMap.trace_eq_sum_inner M.toLinearMap stdB,
    LinearMap.trace_eq_sum_inner N.toLinearMap stdB]
  refine Finset.sum_le_sum (fun i _ => ?_)
  simpa only [real_inner_comm ((M.toLinearMap) (stdB i)) (stdB i),
    real_inner_comm ((N.toLinearMap) (stdB i)) (stdB i)] using h' (stdB i)

/-- A classical solution with `Δu > 0` is a viscosity subsolution of `-tr = 0`, i.e. `Δu ≥ 0` in
the viscosity sense. -/
theorem isViscSubsolution_negTrace_of_classical {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s) (hΔ : ∀ x ∈ s, 0 < (Δ u) x) :
    IsViscSubsolution negTrace u s := by
  intro φ hφ x hx hloc
  have hmax : IsLocalMax (fun y => u y - φ y) x := by
    rw [IsLocalMax]
    rw [eventually_nhdsWithin_iff] at hloc
    filter_upwards [hloc, hs.mem_nhds hx] with y hy hys
    exact hy hys
  have hcd : ContDiffAt ℝ 2 (fun y => u y - φ y) x :=
    ((hu.contDiffWithinAt hx).sub (hφ.contDiffWithinAt hx)).contDiffAt (hs.mem_nhds hx)
  have hnonpos : ∀ v, (fderiv ℝ (fderiv ℝ (fun y => u y - φ y)) x) v v ≤ 0 :=
    fun v => fderiv_fderiv_nonpos_of_localMax hcd hmax v
  have hq : ∀ v, ⟪HessOp (fun y => u y - φ y) s x v, v⟫ ≤ 0 := by
    intro v
    have h1 : HessOp (fun y => u y - φ y) s x =
        InnerProductSpace.continuousLinearMapOfBilin
          (fderiv ℝ (fderiv ℝ (fun y => u y - φ y)) x) :=
      hessianWithin_eq_hessian (hs.mem_nhds hx)
    rw [h1, InnerProductSpace.continuousLinearMapOfBilin_apply]
    exact hnonpos v
  have hsubeq : HessOp (fun y => u y - φ y) s x = HessOp u s x - HessOp φ s x :=
    hessianWithin_sub_of_mem_nhds (hs.mem_nhds hx) (hu.contDiffWithinAt hx)
      (hφ.contDiffWithinAt hx)
  have hle : ∀ v, ⟪HessOp u s x v, v⟫ ≤ ⟪HessOp φ s x v, v⟫ := by
    intro v
    have h := hq v
    rw [hsubeq] at h
    simp only [sub_apply, inner_sub_left] at h
    linarith
  have htr := trace_le_trace_of_forall_inner_le hle
  have htrΔ : LinearMap.trace ℝ ℝ⁴ ((HessOp u s x).toLinearMap) = (Δ u) x :=
    (laplacian_eq_trace_hessian hs hx hu (stdOrthonormalBasis ℝ ℝ⁴)).symm
  change -LinearMap.trace ℝ ℝ⁴ ((HessOp φ s x).toLinearMap) ≤ 0
  linarith [hΔ x hx]

/-! ## The compactness extraction -/

/-- The hypotheses of the master estimate, packaged. -/
def Adm (Γ : ℝ) (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) : Prop :=
  IsOpen s ∧ closedBall 0 3 ⊆ s ∧ ContDiffOn ℝ 4 u s ∧
    (∀ y ∈ s, σ₂ (H u s y) = 1) ∧ (∀ y ∈ s, 0 < (Δ u) y) ∧
    (∀ z ∈ closedBall 0 3, |u z| ≤ Γ - 4) ∧
    (∀ z ∈ closedBall 0 3, ‖fderiv ℝ u z‖ ≤ Γ - 4)

theorem lipschitzWith_restrict_closedBall {f : ℝ⁴ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdiff : ∀ x, x ∈ closedBall (0 : ℝ⁴) 3 → DifferentiableAt ℝ f x)
    (hderiv : ∀ x, x ∈ closedBall (0 : ℝ⁴) 3 → ‖fderiv ℝ f x‖ ≤ C) :
    LipschitzWith (Real.toNNReal C) (fun x : ↥(closedBall (0 : ℝ⁴) 3) => f (x : ℝ⁴)) := by
  rw [lipschitzWith_iff_dist_le_mul, Real.coe_toNNReal C hC]
  intro x y
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hderiv
    (convex_closedBall (0 : ℝ⁴) 3) x.2 y.2
  calc dist (f ↑x) (f ↑y) = ‖f ↑y - f ↑x‖ := by
        rw [Real.dist_eq, abs_sub_comm, Real.norm_eq_abs]
    _ ≤ C * ‖(y : ℝ⁴) - (x : ℝ⁴)‖ := h
    _ = C * dist x y := by rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev]

/-- From a sequence of solutions with uniformly bounded `C¹` norm on `closedBall 0 3` we extract
a uniformly convergent subsequence whose elements are viscosity solutions of `-G(D²u) = 0` on
`ball 0 3`. -/
theorem extraction {Γ : ℝ} (hΓ : 4 ≤ Γ) {u : ℕ → ℝ⁴ → ℝ} {s : ℕ → Set ℝ⁴}
    (hadm : ∀ n, Adm Γ (u n) (s n)) :
    ∃ (φ : ℕ → ℕ) (g : ℝ⁴ → ℝ), StrictMono φ ∧
      (∀ δ > 0, ∀ᶠ k in atTop, ∀ z ∈ closedBall (0 : ℝ⁴) 3, |u (φ k) z - g z| < δ) ∧
      (∀ k, IsViscSolution (fun M => -Gop M) (u (φ k)) (ball 0 3)) ∧
      (∀ k, IsViscSubsolution negTrace (u (φ k)) (ball 0 3)) := by
  classical
  have hΓ4 : 0 ≤ Γ - 4 := by linarith
  have hdiff : ∀ n x, x ∈ closedBall (0 : ℝ⁴) 3 → DifferentiableAt ℝ (u n) x := by
    intro n x hx
    have hsub : closedBall (0 : ℝ⁴) 3 ⊆ s n := (hadm n).2.1
    have hx' : x ∈ s n := hsub hx
    have h4 : ContDiffOn ℝ 4 (u n) (s n) := (hadm n).2.2.1
    have h1 : ContDiffWithinAt ℝ 1 (u n) (s n) x :=
      (h4.contDiffWithinAt hx').of_le (m := 1) (by norm_num)
    exact (h1.differentiableWithinAt (by norm_num)).differentiableAt
      ((hadm n).1.mem_nhds hx')
  have hderiv : ∀ n x, x ∈ closedBall (0 : ℝ⁴) 3 → ‖fderiv ℝ (u n) x‖ ≤ Γ - 4 :=
    fun n x hx => (hadm n).2.2.2.2.2.2 x hx
  have hlip : ∀ n, LipschitzWith (Real.toNNReal (Γ - 4))
      (fun x : ↥(closedBall (0 : ℝ⁴) 3) => u n (x : ℝ⁴)) :=
    fun n => lipschitzWith_restrict_closedBall hΓ4 (hdiff n) (hderiv n)
  have hcontSub : ∀ n, Continuous (fun x : ↥(closedBall (0 : ℝ⁴) 3) => u n (x : ℝ⁴)) := by
    intro n
    have hsub : closedBall (0 : ℝ⁴) 3 ⊆ s n := (hadm n).2.1
    have hcont : ContinuousOn (u n) (s n) := ((hadm n).2.2.1).continuousOn
    exact (hcont.mono hsub).comp_continuous continuous_subtype_val (fun x => x.2)
  have hmem : ∀ n (x : ↥(closedBall (0 : ℝ⁴) 3)),
      u n (x : ℝ⁴) ∈ closedBall (0 : ℝ) (Γ - 4) := by
    intro n x
    have h := (hadm n).2.2.2.2.2.1 (x : ℝ⁴) x.2
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact h
  haveI : CompactSpace ↥(closedBall (0 : ℝ⁴) 3) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℝ⁴) 3)
  obtain ⟨φ, hφ, g₀, hg₀, hconv₀⟩ :=
    exists_strictMono_tendstoUniformlyOn_of_lipschitz
      (K := Real.toNNReal (Γ - 4)) (s := closedBall (0 : ℝ) (Γ - 4))
      (isCompact_closedBall (0 : ℝ) (Γ - 4)) hcontSub hmem hlip
  -- extend the limit to all of `ℝ⁴`
  set g : ℝ⁴ → ℝ := fun x => if hx : x ∈ closedBall (0 : ℝ⁴) 3 then g₀ ⟨x, hx⟩ else 0 with hgdef
  have hgval : ∀ x (hx : x ∈ closedBall (0 : ℝ⁴) 3), g x = g₀ ⟨x, hx⟩ := by
    intro x hx
    rw [hgdef]
    exact dif_pos hx
  have hconv : ∀ δ > 0, ∀ᶠ k in atTop, ∀ z ∈ closedBall (0 : ℝ⁴) 3,
      |u (φ k) z - g z| < δ := by
    intro δ hδ
    have h := Metric.tendstoUniformlyOn_iff.mp hconv₀ δ hδ
    filter_upwards [h] with k hk
    intro z hz
    have h1 := hk ⟨z, hz⟩ (Set.mem_univ _)
    rw [Real.dist_eq, abs_sub_comm] at h1
    simpa [hgval z hz] using h1
  refine ⟨φ, g, hφ, hconv, ?_, ?_⟩
  · intro k
    have hm := hadm (φ k)
    have hball : ball (0 : ℝ⁴) 3 ⊆ s (φ k) :=
      fun _ hx => hm.2.1 (ball_subset_closedBall hx)
    have h2 : ContDiffOn ℝ 2 (u (φ k)) (ball (0 : ℝ⁴) 3) :=
      ((hm.2.2.1).mono hball).of_le (m := 2) (by norm_num)
    refine isViscSolution_negGop_of_classical isOpen_ball h2 ?_ ?_
    · intro x hx
      have hxs : x ∈ s (φ k) := hball hx
      rw [H_congr_of_mem_nhds (isOpen_ball.mem_nhds hx) (hm.1.mem_nhds hxs)]
      exact hm.2.2.2.1 x hxs
    · intro x hx
      exact hm.2.2.2.2.1 x (hball hx)
  · intro k
    have hm := hadm (φ k)
    have hball : ball (0 : ℝ⁴) 3 ⊆ s (φ k) :=
      fun _ hx => hm.2.1 (ball_subset_closedBall hx)
    have h2 : ContDiffOn ℝ 2 (u (φ k)) (ball (0 : ℝ⁴) 3) :=
      ((hm.2.2.1).mono hball).of_le (m := 2) (by norm_num)
    exact isViscSubsolution_negTrace_of_classical isOpen_ball h2
      (fun x hx => hm.2.2.2.2.1 x (hball hx))


/-- The trace functional is continuous. -/
theorem continuous_trace_op :
    Continuous (fun M : ℝ⁴ →L[ℝ] ℝ⁴ => LinearMap.trace ℝ ℝ⁴ (M.toLinearMap)) := by
  rw [show (fun M : ℝ⁴ →L[ℝ] ℝ⁴ => LinearMap.trace ℝ ℝ⁴ (M.toLinearMap))
      = fun M => ∑ i : Fin 4, ⟪stdB i, M (stdB i)⟫ from by
    funext M
    rw [LinearMap.trace_eq_sum_inner M.toLinearMap stdB]
    simp]
  exact continuous_finsetSum _ (fun i _ =>
    continuous_const.inner ((ContinuousLinearMap.apply ℝ ℝ⁴ (stdB i)).continuous))

theorem continuous_negTrace : Continuous negTrace :=
  continuous_trace_op.neg

/-- **The master estimate of Section 5, reduced to the Alexandrov and Savin inputs.**  There is a
bound function `B` such that every solution of `σ₂(D²u) = 1` with `Δu > 0` on a neighbourhood of
`closedBall 0 3` whose `C¹` norm on `closedBall 0 3` is bounded by `Γ - 4` satisfies
`Δu 0 ≤ B Γ`. -/
theorem masterBound_exists (hAlex : AlexandrovInput) (hSavin : SavinInput) :
    ∃ B : ℝ → ℝ, IsMasterBound B := by
  classical
  have key : ∀ Γ : ℝ, 4 ≤ Γ → ∃ M : ℝ, ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴),
      Adm Γ u s → (Δ u) 0 ≤ M := by
    intro Γ hΓ
    by_contra hcon
    push_neg at hcon
    choose u s hadm hbig using fun n : ℕ => hcon (n : ℝ)
    obtain ⟨φ, g, hφ, hconv, hsol, hsub⟩ := extraction hΓ hadm
    have hc2 : ∀ k, ContDiffOn ℝ 2 (u (φ k)) (ball (0 : ℝ⁴) 3) := by
      intro k
      have hm := hadm (φ k)
      exact ((hm.2.2.1).mono (fun _ hx => hm.2.1 (ball_subset_closedBall hx))).of_le
        (m := 2) (by norm_num)
    have hcont : ∀ k, ContinuousOn (u (φ k)) (ball (0 : ℝ⁴) 3) := fun k => (hc2 k).continuousOn
    have hconvStab : ∀ K ⊆ ball (0 : ℝ⁴) 3, IsCompact K →
        TendstoUniformlyOn (fun k => u (φ k)) g atTop K := by
      intro K hK _
      rw [Metric.tendstoUniformlyOn_iff]
      intro δ hδ
      filter_upwards [hconv δ hδ] with k hk
      intro z hz
      have h1 := hk z (ball_subset_closedBall (hK hz))
      rw [Real.dist_eq]
      rwa [abs_sub_comm]
    have hvisc : IsViscSolution (fun M => -Gop M) g (ball (0 : ℝ⁴) 3) :=
      isViscSolution_of_tendstoUniformly continuous_Gop.neg isOpen_ball hcont hsol hconvStab
    have hsubharm : IsViscSubsolution negTrace g (ball (0 : ℝ⁴) 3) :=
      isViscSubsolution_of_tendstoUniformly continuous_negTrace isOpen_ball hcont hsub
        hconvStab
    -- `g` is continuous on `closedBall 0 3`, being a uniform limit of continuous functions
    have hgcont : ContinuousOn g (closedBall (0 : ℝ⁴) 3) := by
      have hunif : TendstoUniformlyOn (fun k => u (φ k)) g atTop (closedBall (0 : ℝ⁴) 3) := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro δ hδ
        filter_upwards [hconv δ hδ] with k hk
        intro z hz
        simpa [Real.dist_eq, abs_sub_comm] using hk z hz
      exact hunif.continuousOn (Eventually.of_forall fun k =>
        ((hadm (φ k)).2.2.1.mono (hadm (φ k)).2.1).continuousOn).frequently
    obtain ⟨y, hy, htwice⟩ := hAlex g hgcont hvisc hsubharm
    have hy3 : y ∈ ball (0 : ℝ⁴) 3 := ball_subset_ball (by norm_num) hy
    obtain ⟨ρ₀, η, hρ₀pos, hηpos, hS⟩ := hSavin g y hy3 hvisc htwice
    set ρ : ℝ := min ρ₀ (2 / 3) with hρdef
    have hρpos : 0 < ρ := lt_min hρ₀pos (by norm_num)
    have hρle : ρ ≤ ρ₀ := min_le_left _ _
    have hρ23 : ρ ≤ 2 / 3 := min_le_right _ _
    obtain ⟨C, hCpos, hSbound⟩ := hS ρ hρpos hρle
    have hy3 : ‖y‖ < 1 / 3 := by rw [mem_ball, dist_zero_right] at hy; exact hy
    have hyc : ball y ρ ⊆ closedBall (0 : ℝ⁴) 3 := by
      intro z hz
      rw [Metric.mem_ball] at hz
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖z‖ ≤ dist z y + ‖y‖ := by
        simpa only [dist_zero_right] using dist_triangle z y 0
      linarith
    have hev : ∀ᶠ k in atTop, ∀ z ∈ ball y ρ, |u (φ k) z - g z| ≤ η * ρ ^ 2 := by
      filter_upwards [hconv (η * ρ ^ 2) (by positivity)] with k hk
      intro z hz
      exact le_of_lt (hk z (hyc hz))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨k0, hk0⟩ := hev
    have hδpos : 0 < ρ / 2 := by positivity
    have hρ2lt : ρ / 2 < 4 / 3 := by linarith
    obtain ⟨C', hC'pos, hdouble⟩ :=
      doubling_moving_center_const (Γ := Γ) hΓ (ρ / 2) hδpos
    have hcontr : ∀ k ≥ k0, (Δ (u (φ k))) 0 ≤ C' * C := by
      intro k hk
      have hclose := hk0 k hk
      have hm := hadm (φ k)
      have hbound : ∀ z ∈ closedBall y (ρ / 2), (Δ (u (φ k))) z ≤ C :=
        hSbound (u (φ k)) (s (φ k)) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2.1
          (fun z hz => hm.2.1 (hyc hz)) hclose
      have hsup : sSup ((fun z : ℝ⁴ => (Δ (u (φ k))) z) '' ball y (ρ / 2)) ≤ C := by
        refine csSup_le ⟨(Δ (u (φ k))) y, y, mem_ball_self hδpos, rfl⟩ ?_
        rintro w ⟨z, hz, rfl⟩
        exact hbound z (ball_subset_closedBall hz)
      have h0 : (0 : ℝ⁴) ∈ ball (0 : ℝ⁴) 2 := by
        rw [Metric.mem_ball, dist_zero_right]; norm_num
      have hd := hdouble (u (φ k)) (s (φ k)) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2.1
        hm.2.2.2.2.2.1 hm.2.2.2.2.2.2 y hy (ρ / 2) le_rfl hρ2lt 0 h0
      have h1 : C' * sSup ((fun z : ℝ⁴ => (Δ (u (φ k))) z) '' ball y (ρ / 2)) ≤ C' * C :=
        mul_le_mul_of_nonneg_left hsup (le_of_lt hC'pos)
      linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (max (C' * C) (k0 : ℝ))
    have hk0k : k0 ≤ k := by exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
    have hbig' : (φ k : ℝ) < (Δ (u (φ k))) 0 := hbig (φ k)
    have hφk : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφ.id_le k
    have hck : C' * C < (φ k : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hk (by exact_mod_cast (hφ.id_le k)))
    linarith [hcontr k hk0k]
  refine ⟨fun Γ => if h : 4 ≤ Γ then Classical.choose (key Γ h) else 0, ?_⟩
  intro Γ hΓ u s hs hsub hu hσ hΔ hb1 hb2
  dsimp only
  rw [dif_pos hΓ]
  exact Classical.choose_spec (key Γ hΓ) u s ⟨hs, hsub, hu, hσ, hΔ, hb1, hb2⟩


end Submission
