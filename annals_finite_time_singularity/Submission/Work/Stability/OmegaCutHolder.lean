import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.CutFactorContDiff
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.CutFactorFderivLipschitz
import Submission.Work.Stability.HolderOfBoundedLipschitz
import Submission.Work.Stability.HolderSmulRightOfSupport
import Submission.Work.Stability.LipschitzOfBoundedFderiv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.Stability

set_option autoImplicit false

/-! ## The radial cut-off factor -/

/-- The radial cut-off factor of `ℝ³`: `x ↦ chi(ρ(x)/L)` with `ρ(x) = ‖x‖` and `chi` the `C^∞`
bump of `Work.Stability.Cutoff`.  `omegaCut L ω = cutFactor L • ω`. -/
noncomputable def cutFactor (L : ℝ) : Work.Cyl.R3 → ℝ :=
  fun x => chi (Work.Cyl.rho x / L)

theorem cutFactor_apply (L : ℝ) (x : Work.Cyl.R3) :
    cutFactor L x = chi (Work.Cyl.rho x / L) := rfl

/-- `omegaCut` is multiplication by the cut-off factor. -/
theorem omegaCut_eq_smul (L : ℝ) (ω : Work.Cyl.R3 → Work.Cyl.R3) :
    omegaCut L ω = cutFactor L • ω := rfl

/-! ## Elementary boundedness API -/

/-- A function with uniformly bounded norm is `IsBoundedFun`. -/
theorem isBoundedFun_of_forall_norm_le {X : Type*} [PseudoMetricSpace X] {E : Type*}
    [SeminormedAddCommGroup E] {f : X → E} {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C) : IsBoundedFun f :=
  isBounded_iff_forall_norm_le.mpr ⟨C, fun y hy => by
    obtain ⟨x, -, rfl⟩ := hy
    exact h x⟩

/-- An `IsBoundedFun` function has a uniform norm bound. -/
theorem exists_norm_le_of_isBoundedFun {X : Type*} [PseudoMetricSpace X] {E : Type*}
    [SeminormedAddCommGroup E] {f : X → E} (h : IsBoundedFun f) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp h
  exact ⟨C, fun x => hC (f x) ⟨x, Set.mem_univ x, rfl⟩⟩

/-- A continuous function vanishing outside the ball of radius `R` is bounded: its image is
contained in the image of the compact ball together with `{0}`. -/
theorem isBoundedFun_of_continuous_of_eq_zero_of_norm_gt {E : Type*} [NormedAddCommGroup E]
    [ProperSpace E] {F : Type*} [NormedAddCommGroup F] {f : E → F} {R : ℝ}
    (hf : Continuous f) (hz : ∀ x, R < ‖x‖ → f x = 0) : IsBoundedFun f := by
  have hbig : Bornology.IsBounded ((f '' Metric.closedBall (0 : E) R) ∪ ({0} : Set F)) :=
    Bornology.IsBounded.union ((isCompact_closedBall (0 : E) R).image hf).isBounded
      (isCompact_singleton (x := (0 : F))).isBounded
  refine hbig.subset ?_
  rintro y ⟨x, -, rfl⟩
  by_cases hx : R < ‖x‖
  · exact Or.inr (by simp [hz x hx])
  · refine Or.inl ⟨x, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact not_lt.mp hx

/-! ## Bounded Lipschitz times bounded Hölder is Hölder -/

/-- **The product estimate** (for `α ≤ 1`): the pointwise product of a bounded Lipschitz scalar
function `c` with a bounded `α`-Hölder function `A` is `α`-Hölder, with constant
`M_c C_A + M_A max K (2 M_c)`.  The point is that `|c x - c y| ≤ min (K d) (2 M_c)` while
`min (K d) (2 M_c) ≤ max K (2 M_c) · d^α` for `α ≤ 1` (`d ≤ d^α` for `d ≤ 1` and `1 ≤ d^α` for
`d ≥ 1`). -/
theorem holder_smul_of_bounded_lipschitz {X : Type*} [PseudoMetricSpace X] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {α : NNReal} (hα : α ≤ 1) {K : NNReal}
    {c : X → ℝ} {A : X → E} (hc : IsBoundedFun c) (hcl : LipschitzWith K c)
    (hb : IsBoundedFun A) (hA : Holder α A) : Holder α (c • A) := by
  obtain ⟨Mc₀, hMc₀⟩ := exists_norm_le_of_isBoundedFun hc
  obtain ⟨MA₀, hMA₀⟩ := exists_norm_le_of_isBoundedFun hb
  obtain ⟨CA, hCA⟩ := hA
  set Mc : ℝ := max Mc₀ 0 with hMcdef
  set MA : ℝ := max MA₀ 0 with hMAdef
  have hMc : ∀ x, ‖c x‖ ≤ Mc := fun x => le_trans (hMc₀ x) (le_max_left _ _)
  have hMA : ∀ x, ‖A x‖ ≤ MA := fun x => le_trans (hMA₀ x) (le_max_left _ _)
  have hMc0 : 0 ≤ Mc := le_max_right _ _
  have hMA0 : 0 ≤ MA := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hmax0 : 0 ≤ max (K : ℝ) (2 * Mc) := le_trans (by linarith) (le_max_right _ _)
  have hC0 : 0 ≤ Mc * (CA : ℝ) + MA * max (K : ℝ) (2 * Mc) :=
    add_nonneg (mul_nonneg hMc0 CA.coe_nonneg) (mul_nonneg hMA0 hmax0)
  refine ⟨⟨Mc * (CA : ℝ) + MA * max (K : ℝ) (2 * Mc), hC0⟩, holderWith_of_dist_le fun x y => ?_⟩
  have hcx : |c x| ≤ Mc := by
    have h := hMc x
    rwa [Real.norm_eq_abs] at h
  have hcy : |c y| ≤ Mc := by
    have h := hMc y
    rwa [Real.norm_eq_abs] at h
  have hAy : ‖A y‖ ≤ MA := hMA y
  have hdA : dist (A x) (A y) ≤ (CA : ℝ) * dist x y ^ (α : ℝ) := hCA.dist_le x y
  have hdc1 : |c x - c y| ≤ (K : ℝ) * dist x y := by
    have h := hcl.dist_le_mul x y
    rwa [Real.dist_eq] at h
  have hdc2 : |c x - c y| ≤ 2 * Mc := by
    calc |c x - c y| = dist (c x) (c y) := by rw [Real.dist_eq]
      _ ≤ dist (c x) 0 + dist 0 (c y) := dist_triangle _ _ _
      _ = |c x| + |c y| := by rw [Real.dist_eq, Real.dist_eq, sub_zero, zero_sub, abs_neg]
      _ ≤ 2 * Mc := by linarith
  have hdc : |c x - c y| ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) := by
    rcases lt_or_ge (dist x y) 1 with hd | hd
    · have hs : dist x y ≤ dist x y ^ (α : ℝ) :=
        Real.self_le_rpow_of_le_one dist_nonneg (le_of_lt hd) (by exact_mod_cast hα)
      calc |c x - c y| ≤ (K : ℝ) * dist x y := hdc1
        _ ≤ (K : ℝ) * dist x y ^ (α : ℝ) := mul_le_mul_of_nonneg_left hs hK0
        _ ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
    · have hs : (1 : ℝ) ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow hd α.coe_nonneg
      calc |c x - c y| ≤ 2 * Mc := hdc2
        _ ≤ (2 * Mc) * dist x y ^ (α : ℝ) := le_mul_of_one_le_right (by linarith) hs
        _ ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)
  have hdec : c x • A x - c y • A y = c x • (A x - A y) + (c x - c y) • A y := by
    rw [smul_sub, sub_smul]; abel
  calc dist (c x • A x) (c y • A y) = ‖c x • (A x - A y) + (c x - c y) • A y‖ := by
        rw [dist_eq_norm, hdec]
    _ ≤ ‖c x • (A x - A y)‖ + ‖(c x - c y) • A y‖ := norm_add_le _ _
    _ = |c x| * dist (A x) (A y) + |c x - c y| * ‖A y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, dist_eq_norm]
    _ ≤ Mc * ((CA : ℝ) * dist x y ^ (α : ℝ)) + (max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ)) * MA :=
        add_le_add (mul_le_mul hcx hdA dist_nonneg hMc0)
          (mul_le_mul hdc hAy (norm_nonneg _) (mul_nonneg hmax0 (Real.rpow_nonneg dist_nonneg _)))
    _ = (Mc * (CA : ℝ) + MA * max (K : ℝ) (2 * Mc)) * dist x y ^ (α : ℝ) := by ring

/-! ## Boundedness and Lipschitzness of the cut-off factor -/

/-- The derivative of the cut-off factor vanishes off the ball of radius `2L`. -/
theorem cutFactor_fderiv_eq_zero {L : ℝ} (hL : 0 < L) {x : Work.Cyl.R3}
    (hx : 2 * L < Work.Cyl.rho x) : fderiv ℝ (cutFactor L) x = 0 :=
  CutFactorFderivZero hL hx

/-- The derivative of the cut-off factor is Lipschitz. -/
theorem cutFactor_fderiv_lipschitz {L : ℝ} (hL : 0 < L) :
    ∃ K : NNReal, LipschitzWith K (fderiv ℝ (cutFactor L)) :=
  CutFactorFderivLipschitz hL

/-- The cut-off factor is bounded by `1` (`0 ≤ chi ≤ 1`). -/
theorem cutFactor_bounded (L : ℝ) : IsBoundedFun (cutFactor L) := by
  refine isBoundedFun_of_forall_norm_le (C := 1) fun x => ?_
  rw [Real.norm_eq_abs, cutFactor_apply, abs_le]
  exact ⟨by linarith [chi_nonneg (Work.Cyl.rho x / L)], chi_le_one (Work.Cyl.rho x / L)⟩

/-- The derivative of the cut-off factor is bounded: it is continuous (the cut-off factor is
`C^1`) and vanishes off the ball of radius `2L`. -/
theorem cutFactor_fderiv_bounded {L : ℝ} (hL : 0 < L) :
    IsBoundedFun (fderiv ℝ (cutFactor L)) := by
  refine isBoundedFun_of_continuous_of_eq_zero_of_norm_gt (R := 2 * L)
    ((CutFactorContDiff hL 1).continuous_fderiv one_ne_zero) fun x hx => ?_
  exact cutFactor_fderiv_eq_zero hL (by rw [Work.Cyl.rho_eq_norm]; exact hx)

/-- The cut-off factor is Lipschitz: it is differentiable with bounded derivative
(`cutFactor_fderiv_bounded`). -/
theorem cutFactor_lipschitz {L : ℝ} (hL : 0 < L) :
    ∃ K : NNReal, LipschitzWith K (cutFactor L) :=
  LipschitzOfBoundedFderiv ((CutFactorContDiff hL 1).differentiable one_ne_zero)
    (cutFactor_fderiv_bounded hL)

/-! ## The main theorem -/

/-- **The `C^{1,α}` class is preserved by the cut-off** (for `α ≤ 1`, the range of the paper: the
challenge asks for `∃α>0` and all the estimates live in `0 < α ≤ 1`).  The cut-off factor
`x ↦ chi(ρ(x)/L)` is a radial `C^∞` function of `ρ ∈ C^∞(ℝ³ \ {0})` which is `≡ 1` near the
origin (so it extends smoothly across `0`), and it is bounded with compactly supported bounded
derivative; multiplying a `C^{1,α}` field `ω` (not assumed bounded: only `fderiv ω` is) by such a
factor preserves `C^{1,α}`: the product is `C^1`, its derivative
`g • fderiv ω + (fderiv g).smulRight ω` is bounded (the second summand because `fderiv g` has
compact support and `ω` is continuous there) and `α`-Hölder (product of a bounded `α`-Hölder
factor with a bounded Lipschitz factor, which is where `α ≤ 1` is used). -/
theorem OmegaCutHolder {L : ℝ} (hL : 0 < L) {α : NNReal} (hα1 : α ≤ 1)
    {ω : Work.Cyl.R3 → Work.Cyl.R3} (h : IsContDiffHolder ℝ α ω) :
    IsContDiffHolder ℝ α (omegaCut L ω) := by
  have hω1 : ContDiff ℝ 1 ω := h.1
  have hωb : IsBoundedFun (fderiv ℝ ω) := h.2.1
  have hωh : Holder α (fderiv ℝ ω) := h.2.2
  have hφ1 : ContDiff ℝ 1 (cutFactor L) := CutFactorContDiff hL 1
  have hφdiff : Differentiable ℝ (cutFactor L) := hφ1.differentiable one_ne_zero
  have hωdiff : Differentiable ℝ ω := hω1.differentiable one_ne_zero
  obtain ⟨Bω, hBω⟩ := exists_norm_le_of_isBoundedFun hωb
  obtain ⟨Bφ, hBφ⟩ := exists_norm_le_of_isBoundedFun (cutFactor_fderiv_bounded hL)
  obtain ⟨Kφ, hKφ⟩ := cutFactor_lipschitz hL
  obtain ⟨KA, hKA⟩ := cutFactor_fderiv_lipschitz hL
  obtain ⟨Kω, hKω⟩ := LipschitzOfBoundedFderiv hωdiff hωb
  have hBφnn : 0 ≤ Bφ := le_trans (norm_nonneg _) (hBφ 0)
  have hfd : ∀ x, fderiv ℝ (cutFactor L • ω) x
      = cutFactor L x • fderiv ℝ ω x + (fderiv ℝ (cutFactor L) x).smulRight (ω x) :=
    fun x => fderiv_fun_smul hφdiff.differentiableAt hωdiff.differentiableAt
  have hcut : omegaCut L ω = cutFactor L • ω := omegaCut_eq_smul L ω
  set M : ℝ := ‖ω 0‖ + (Kω : ℝ) * (2 * L) with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hωball : ∀ x, Work.Cyl.rho x ≤ 2 * L → ‖ω x‖ ≤ M := by
    intro x hx
    have hx' : ‖x‖ ≤ 2 * L := by rw [← Work.Cyl.rho_eq_norm x]; exact hx
    have h1 : ‖ω x - ω 0‖ ≤ (Kω : ℝ) * (2 * L) := by
      have h2 : dist (ω x) (ω 0) ≤ (Kω : ℝ) * dist x 0 := hKω.dist_le_mul x 0
      rw [dist_eq_norm, dist_eq_norm, sub_zero] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left hx' (by positivity))
    calc ‖ω x‖ = ‖(ω x - ω 0) + ω 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖ω x - ω 0‖ + ‖ω 0‖ := norm_add_le _ _
      _ ≤ M := by rw [hM]; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hcut]
    exact hφ1.smul hω1
  · rw [hcut]
    refine isBoundedFun_of_forall_norm_le (C := 1 * Bω + Bφ * M) fun x => ?_
    rw [hfd x]
    have h1 : ‖cutFactor L x • fderiv ℝ ω x‖ ≤ 1 * Bω := by
      have hc : ‖cutFactor L x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, cutFactor_apply, abs_le]
        exact ⟨by linarith [chi_nonneg (Work.Cyl.rho x / L)], chi_le_one (Work.Cyl.rho x / L)⟩
      calc ‖cutFactor L x • fderiv ℝ ω x‖ ≤ ‖cutFactor L x‖ * ‖fderiv ℝ ω x‖ :=
            ContinuousLinearMap.opNorm_smul_le (cutFactor L x) (fderiv ℝ ω x)
        _ ≤ 1 * Bω := mul_le_mul hc (hBω x) (norm_nonneg _) (by norm_num)
    have h2 : ‖(fderiv ℝ (cutFactor L) x).smulRight (ω x)‖ ≤ Bφ * M := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      by_cases hx : 2 * L < Work.Cyl.rho x
      · rw [cutFactor_fderiv_eq_zero hL hx, norm_zero, zero_mul]
        positivity
      · exact mul_le_mul (hBφ x) (hωball x (le_of_not_gt hx)) (norm_nonneg _) hBφnn
    calc ‖cutFactor L x • fderiv ℝ ω x + (fderiv ℝ (cutFactor L) x).smulRight (ω x)‖
        ≤ ‖cutFactor L x • fderiv ℝ ω x‖ + ‖(fderiv ℝ (cutFactor L) x).smulRight (ω x)‖ :=
          norm_add_le _ _
      _ ≤ 1 * Bω + Bφ * M := add_le_add h1 h2
  · rw [hcut, funext hfd]
    obtain ⟨C1, hC1⟩ := holder_smul_of_bounded_lipschitz hα1 (cutFactor_bounded L) hKφ hωb hωh
    obtain ⟨C2, hC2⟩ := HolderSmulRightOfSupport (E := Work.Cyl.R3) (R := 2 * L) hα1 (by positivity)
      hBφnn hKA hBφ (fun x hx => cutFactor_fderiv_eq_zero hL (by rw [Work.Cyl.rho_eq_norm]; exact hx)) hKω
    exact ⟨C1 + C2, HolderWith.add hC1 hC2⟩

end Work.Stability
