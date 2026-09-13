/-
Viscosity solutions of a fully nonlinear second order equation `F(D²u) = 0` in `ℝ⁴`, and the
stability of viscosity subsolutions under locally uniform convergence (the appendix lemma
`lem:conv` of Shankar--Yuan).  This is the framework needed for the compactness argument of
Section 5 of the paper.
-/
import ChallengeDeps
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_hessian_op
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_neg
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_add_quadratic
import Submission.Commons.Analysis.Calculus.LocalMax.exists_max_perturb_ball_continuous

open Metric MeasureTheory Filter
open Commons.Analysis.Calculus.FDeriv Commons.Analysis.Calculus.LocalMax
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- The Hessian operator of `φ` within `s` at `x`: the self-adjoint operator representing the
second derivative `D²φ(x)` under the inner product, i.e. `⟪HessOp φ s x v, w⟫ = D²φ(x)(v,w)`. -/
noncomputable def HessOp (φ : ℝ⁴ → ℝ) (s : Set ℝ⁴) (x : ℝ⁴) : ℝ⁴ →L[ℝ] ℝ⁴ :=
  InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ φ s) s x)

/-- `u` is a viscosity subsolution of `F(D²u) = 0` on `s`: at every point where a smooth test
function `φ` touches `u` from above, `F(D²φ(x)) ≤ 0`. -/
def IsViscSubsolution (F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ) (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) : Prop :=
  ∀ (φ : ℝ⁴ → ℝ), ContDiffOn ℝ 2 φ s → ∀ x ∈ s,
    (∀ᶠ y in 𝓝[s] x, u y - φ y ≤ u x - φ x) → F (HessOp φ s x) ≤ 0

/-- `u` is a viscosity supersolution of `F(D²u) = 0` on `s`. -/
def IsViscSupersolution (F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ) (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) : Prop :=
  ∀ (φ : ℝ⁴ → ℝ), ContDiffOn ℝ 2 φ s → ∀ x ∈ s,
    (∀ᶠ y in 𝓝[s] x, u y - φ y ≥ u x - φ x) → 0 ≤ F (HessOp φ s x)

/-- `u` is a viscosity solution of `F(D²u) = 0` on `s`. -/
def IsViscSolution (F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ) (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) : Prop :=
  IsViscSubsolution F u s ∧ IsViscSupersolution F u s

/-- The Hessian of the quadratic perturbation `y ↦ φ y + ε * ‖y - x₀‖ ^ 2` is the Hessian of `φ`
plus `2ε • 1`. -/
theorem hessOp_add_quadratic {φ : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s) {x₀ : ℝ⁴} {x : ℝ⁴}
    (hx : x ∈ s) {ε : ℝ} (hφ : ContDiffWithinAt ℝ 2 φ s x) :
    HessOp (fun y => φ y + ε * ‖y - x₀‖ ^ 2) s x = HessOp φ s x + (2 * ε) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) :=
  hessianWithin_add_quadratic hs hx hφ

/-- **Stability of viscosity subsolutions** (appendix Lemma `lem:conv` of Shankar--Yuan).

If `u k` are viscosity subsolutions of `F(D²u) = 0` on the open set `s`, if `F` is continuous,
and if `u k` converges to `g` locally uniformly on `s`, then `g` is a viscosity subsolution of
`F(D²u) = 0` on `s`.

Given a test function `φ` touching `g` from above at `x₀`, perturb `φ` to `φ + ε‖· - x₀‖²`,
which makes the touching strict, so that for large `k` the function `u k - φ - ε‖· - x₀‖²`
attains its maximum at a point `x k` within distance `ε/2` of `x₀`.  The subsolution property
gives `F(D²φ(x k) + 2ε • 1) ≤ 0`, and the result follows by continuity letting `ε → 0`. -/
theorem isViscSubsolution_of_tendstoUniformly
    {F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ} (hF : Continuous F)
    {u : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hcont : ∀ k, ContinuousOn (u k) s)
    (hsub : ∀ k, IsViscSubsolution F (u k) s)
    (hconv : ∀ K ⊆ s, IsCompact K → TendstoUniformlyOn u g atTop K) :
    IsViscSubsolution F g s := by
  intro φ hφ x₀ hx₀ hmax
  -- Extract a radius `R > 0` with `closedBall x₀ R ⊆ s` and `g - φ ≤ g x₀ - φ x₀` there.
  obtain ⟨δ₁, hδ₁, hδ₁max⟩ : ∃ δ > 0, ∀ y, dist y x₀ < δ → y ∈ s →
      g y - φ y ≤ g x₀ - φ x₀ := by
    rw [eventually_nhdsWithin_iff] at hmax
    rw [Metric.eventually_nhds_iff] at hmax
    exact hmax
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ : ∃ δ > 0, ball x₀ δ ⊆ s := by
    have hmem : s ∈ 𝓝 x₀ := hs.mem_nhds hx₀
    rw [Metric.mem_nhds_iff] at hmem
    exact hmem
  set R : ℝ := min δ₁ δ₂ / 2 with hRdef
  have hRpos : 0 < R := by
    have : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    rw [hRdef]; linarith
  have hRlt₁ : R < δ₁ := by
    have : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    rw [hRdef]; linarith
  have hRlt₂ : R < δ₂ := by
    have : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    rw [hRdef]; linarith
  have hRsub : closedBall x₀ R ⊆ s := fun _ hy => hδ₂sub (closedBall_subset_ball hRlt₂ hy)
  have hRmax : ∀ y ∈ closedBall x₀ R, g y - φ y ≤ g x₀ - φ x₀ := by
    intro y hy
    have hy' := hy
    rw [Metric.mem_closedBall] at hy'
    exact hδ₁max y (lt_of_le_of_lt hy' hRlt₁) (hRsub hy)
  have hφcont : ContinuousOn φ (closedBall x₀ R) := hφ.continuousOn.mono hRsub
  have hRcont : ∀ k, ContinuousOn (u k) (closedBall x₀ R) := fun k => (hcont k).mono hRsub
  have hRcpt : IsCompact (closedBall x₀ R) := isCompact_closedBall _ _
  have hRconv : ∀ δ > 0, ∀ᶠ k in atTop, ∀ y ∈ closedBall x₀ R, |u k y - g y| < δ := by
    intro δ hδ
    have h := hconv (closedBall x₀ R) hRsub hRcpt
    rw [Metric.tendstoUniformlyOn_iff] at h
    filter_upwards [h δ hδ] with k hk
    intro y hy
    have := hk y hy
    rw [Real.dist_eq] at this
    rwa [abs_sub_comm] at this
  -- For each `j` the `ε j`-perturbed maximum is attained within `ε j / 2` of `x₀`.
  have key : ∀ j : ℕ, ∃ k : ℕ, ∃ x : ℝ⁴,
      x ∈ ball x₀ (R / (j + 2) / 2) ∧
      ∀ y ∈ closedBall x₀ (R / (j + 2)),
        u k y - φ y - (R / (j + 2)) * ‖y - x₀‖ ^ 2
          ≤ u k x - φ x - (R / (j + 2)) * ‖x - x₀‖ ^ 2 := by
    intro j
    have hε : 0 < R / (j + 2) := by positivity
    have hεR : R / (j + 2) < R := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < (j:ℝ) + 2)]
      nlinarith [hRpos]
    have hev := exists_max_perturb_ball_continuous (u := u) (g := g) (φ := φ) (x₀ := x₀)
      (R := R) (ε := R / (j + 2)) hRpos hε hεR hRcont hφcont hRconv hRmax
    rw [Filter.eventually_atTop] at hev
    obtain ⟨k, hk⟩ := hev
    obtain ⟨x, hx, hxmax⟩ := hk k le_rfl
    exact ⟨k, x, hx, hxmax⟩
  choose kf xf hxf hxmax using key
  -- The perturbed subsolution inequality.
  have hineq : ∀ j, F (HessOp φ s (xf j) + (2 * (R / (j + 2))) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) ≤ 0 := by
    intro j
    have hεpos : 0 < R / (j + 2) := by positivity
    have hdist : dist (xf j) x₀ < R / (j + 2) / 2 := by
      have := hxf j
      rwa [Metric.mem_ball] at this
    have hxs : xf j ∈ s := by
      apply hRsub
      rw [Metric.mem_closedBall]
      have h2 : R / (j + 2) / 2 ≤ R := by
        have h3 : R / (j + 2) ≤ R := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < (j:ℝ) + 2)]
          nlinarith [hRpos]
        linarith
      linarith
    have hquad : ContDiff ℝ 2 (fun y : ℝ⁴ => ‖y - x₀‖ ^ 2) :=
      (contDiff_id.sub contDiff_const).norm_sq ℝ
    have hψ : ContDiffOn ℝ 2 (fun y => φ y + (R / (j + 2)) * ‖y - x₀‖ ^ 2) s :=
      hφ.add ((hquad.const_smul (R / (j + 2))).contDiffOn)
    have hloc : ∀ᶠ y in 𝓝[s] (xf j),
        u (kf j) y - (fun y => φ y + (R / (j + 2)) * ‖y - x₀‖ ^ 2) y
          ≤ u (kf j) (xf j)
            - (fun y => φ y + (R / (j + 2)) * ‖y - x₀‖ ^ 2) (xf j) := by
      have hball : closedBall x₀ (R / (j + 2)) ∈ 𝓝[s] (xf j) := by
        rw [Metric.mem_nhdsWithin_iff]
        refine ⟨R / (j + 2) / 2, by positivity, ?_⟩
        rintro y ⟨hy1, hy2⟩
        rw [Metric.mem_closedBall]
        rw [Metric.mem_ball] at hy1
        have := dist_triangle y (xf j) x₀
        linarith
      filter_upwards [hball] with y hy
      have := hxmax j y hy
      linarith
    have hres := hsub (kf j) (fun y => φ y + (R / (j + 2)) * ‖y - x₀‖ ^ 2) hψ (xf j) hxs hloc
    rwa [hessOp_add_quadratic hs hxs (hφ.contDiffWithinAt hxs)] at hres
  -- `x j → x₀` and the perturbations vanish.
  have hx0 : Tendsto xf atTop (𝓝 x₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (g := fun j : ℕ => R / (j + 2) / 2) (fun j => dist_nonneg) (fun j => ?_) ?_
    · have := hxf j
      rw [Metric.mem_ball] at this
      exact le_of_lt this
    · have h1 : Tendsto (fun j : ℕ => R / (j + 2)) atTop (𝓝 0) := by
        have ha : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        have hb := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ha
        have hc := hb.const_mul R
        simpa [div_eq_mul_inv] using hc
      simpa using h1.div_const 2
  have hε0 : Tendsto (fun j : ℕ => (2 * (R / (j + 2))) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => 2 * (R / (j + 2))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun j : ℕ => R / (j + 2)) atTop (𝓝 0) := by
        have ha : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        have hb := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ha
        have hc := hb.const_mul R
        simpa [div_eq_mul_inv] using hc
      simpa using h2.const_mul 2
    have h3 : Tendsto (fun c : ℝ => c • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun c : ℝ => c • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) :=
        continuous_id.smul continuous_const
      have h := hc.tendsto (0 : ℝ)
      rw [show (0 : ℝ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) = 0 from by ext v; simp] at h
      exact h
    exact h3.comp h1
  have hlim : Tendsto (fun j : ℕ => HessOp φ s (xf j) + (2 * (R / (j + 2))) • (1 : ℝ⁴ →L[ℝ] ℝ⁴))
      atTop (𝓝 (HessOp φ s x₀)) := by
    have h1 : Tendsto (fun j : ℕ => HessOp φ s (xf j)) atTop (𝓝 (HessOp φ s x₀)) :=
      ((continuousOn_hessian_op hs hφ).continuousAt (hs.mem_nhds hx₀)).tendsto.comp hx0
    simpa using h1.add hε0
  have h2 : Tendsto (fun j : ℕ => F (HessOp φ s (xf j) + (2 * (R / (j + 2))) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)))
      atTop (𝓝 (F (HessOp φ s x₀))) := hF.continuousAt.tendsto.comp hlim
  exact le_of_tendsto h2 (Eventually.of_forall hineq)

/-- Supersolutions are precisely the subsolutions of the negated, sign-reversed operator applied
to the negated function. -/
theorem isViscSupersolution_iff {F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ} {u : ℝ⁴ → ℝ} {s : Set ℝ⁴}
    (hs : IsOpen s) :
    IsViscSupersolution F u s ↔ IsViscSubsolution (fun M => -F (-M)) (fun x => -u x) s := by
  constructor
  · intro h φ hφ x hx hloc
    have hψ : ContDiffOn ℝ 2 (fun y => -φ y) s := hφ.neg
    have hloc' : ∀ᶠ y in 𝓝[s] x, u y - (fun y => -φ y) y ≥ u x - (fun y => -φ y) x := by
      filter_upwards [hloc] with y hy
      linarith
    have hres := h (fun y => -φ y) hψ x hx hloc'
    have hneg : HessOp (fun y => -φ y) s x = -HessOp φ s x := hessianWithin_neg hs hx
    rw [hneg] at hres
    change -(F (-(HessOp φ s x))) ≤ 0
    linarith
  · intro h φ hφ x hx hloc
    have hψ : ContDiffOn ℝ 2 (fun y => -φ y) s := hφ.neg
    have hloc' : ∀ᶠ y in 𝓝[s] x,
        (fun x => -u x) y - (fun y => -φ y) y ≤ (fun x => -u x) x - (fun y => -φ y) x := by
      filter_upwards [hloc] with y hy
      linarith
    have hres := h (fun y => -φ y) hψ x hx hloc'
    have hneg : HessOp (fun y => -φ y) s x = -HessOp φ s x := hessianWithin_neg hs hx
    rw [hneg] at hres
    change -(F (-(-(HessOp φ s x)))) ≤ 0 at hres
    rw [neg_neg] at hres
    linarith

/-- **Stability of viscosity supersolutions**: the locally uniform limit of viscosity
supersolutions of a continuous operator is a viscosity supersolution. -/
theorem isViscSupersolution_of_tendstoUniformly
    {F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ} (hF : Continuous F)
    {u : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hcont : ∀ k, ContinuousOn (u k) s)
    (hsup : ∀ k, IsViscSupersolution F (u k) s)
    (hconv : ∀ K ⊆ s, IsCompact K → TendstoUniformlyOn u g atTop K) :
    IsViscSupersolution F g s := by
  rw [isViscSupersolution_iff hs]
  refine isViscSubsolution_of_tendstoUniformly (F := fun M => -F (-M))
    (u := fun k x => -(u k x)) (g := fun x => -g x) (s := s)
    (hF.neg.comp continuous_neg) hs ?_ ?_ ?_
  · intro k
    exact (hcont k).neg
  · intro k
    exact (isViscSupersolution_iff hs).mp (hsup k)
  · intro K hK hc
    exact (hconv K hK hc).neg

/-- **Stability of viscosity solutions**: the locally uniform limit of viscosity solutions of a
continuous operator is a viscosity solution. -/
theorem isViscSolution_of_tendstoUniformly
    {F : (ℝ⁴ →L[ℝ] ℝ⁴) → ℝ} (hF : Continuous F)
    {u : ℕ → ℝ⁴ → ℝ} {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hcont : ∀ k, ContinuousOn (u k) s)
    (hsol : ∀ k, IsViscSolution F (u k) s)
    (hconv : ∀ K ⊆ s, IsCompact K → TendstoUniformlyOn u g atTop K) :
    IsViscSolution F g s :=
  ⟨isViscSubsolution_of_tendstoUniformly hF hs hcont (fun k => (hsol k).1) hconv,
   isViscSupersolution_of_tendstoUniformly hF hs hcont (fun k => (hsol k).2) hconv⟩


end Submission
