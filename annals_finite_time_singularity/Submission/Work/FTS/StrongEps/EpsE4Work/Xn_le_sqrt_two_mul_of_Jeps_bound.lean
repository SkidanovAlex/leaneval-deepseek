import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkMem_add_smoothOpen
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Work

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two elementary closure facts for the `ℋ^k`-machinery

The main theorem below compares the `ℋ⁴`-norms of `g₀` and of its mollification `J_ε g₀` by the
triangle inequality, for which the difference `g₀ - J_ε g₀` must be *in* `ℋ⁴`.  Since both
summands are `C^∞` on the open quadrant and in `ℋ⁴`, this follows from the closure of `ℋ^k`
under addition together with the (unconditional) invariance of the `ℋ^k`-integrand under
negation. -/

/-- `SmoothOpen` is closed under pointwise negation. -/
private theorem smoothOpen_neg_of {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  have hfun : Function.uncurry (fun z θ => -f z θ) = -(Function.uncurry f) := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hf.neg

/-- `HkMem` is closed under pointwise negation: the `ℋ^k`-integrand of `-f` *equals* that of
`f` (`HkIntegrand_neg`), so no regularity hypothesis is needed. -/
private theorem hkMem_neg_of {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  have hI : ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ
      = Work.Spaces.HkIntegrand α k f z θ := by
    intro z θ
    exact congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  constructor
  · intro z hz
    refine IntegrableOn.congr_fun (hf.1 z hz) (fun θ _ => ?_) measurableSet_Icc
    exact (hI z θ).symm
  · have h : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ)
        = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hI z θ)
    rw [h]
    exact hf.2

/-- **`ℋ^k` is closed under subtraction** for data smooth on the open quadrant: write
`f - g = f + (-g)` and use the closure under addition plus the two facts above. -/
private theorem hkMem_sub_open_of {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hfun : (fun z θ => f z θ - g z θ) = (fun z θ => f z θ + -g z θ) := by
    funext z θ; ring
  rw [hfun]
  exact Work.FTS.EllipticEst.HkMem_add_open hf (smoothOpen_neg_of hg) hmf (hkMem_neg_of hmg)

/-- `HkSq` only sees the pointwise values of the profile. -/
private theorem hkSq_congr_pt {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, f z θ = g z θ) : Work.Spaces.HkSq α k f = Work.Spaces.HkSq α k g :=
  Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ _ _ _ => h z θ)

/-- `HkNorm` only sees the pointwise values of the profile. -/
private theorem hkNorm_congr_pt {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, f z θ = g z θ) : Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hkSq_congr_pt h]

/-- The `ℋ^k`-norm of a difference does not depend on the order of the two arguments. -/
private theorem hkNorm_neg_pt {α : ℝ} {k : ℕ} (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkNorm α k (fun z θ => -f z θ) = Work.Spaces.HkNorm α k f := by
  rw [show (fun z θ => -f z θ) = (-f) from rfl]
  exact Work.FTS.EllipticEst.HkNorm_neg α k f

private theorem hkSq_neg_pt {α : ℝ} {k : ℕ} (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => -f z θ) = Work.Spaces.HkSq α k f := by
  rw [show (fun z θ => -f z θ) = (-f) from rfl]
  exact Work.FTS.EllipticEst.HkSq_neg α k f

private theorem hkNorm_sub_swap {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ} :
    Work.Spaces.HkNorm α k (fun z θ => g z θ - f z θ)
      = Work.Spaces.HkNorm α k (fun z θ => f z θ - g z θ) := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  congr 1
  exact (hkSq_congr_pt (α := α) (k := k) (f := fun z θ => g z θ - f z θ)
      (g := fun z θ => -(f z θ - g z θ)) (fun z θ => by ring)).trans
    (hkSq_neg_pt (α := α) (k := k) (fun z θ => f z θ - g z θ))

/-- **E4, the `ε → 0` comparison step.**

If the mollified profiles `J_ε g₀` are uniformly bounded by `C₀ α²` in `ℋ⁴` for all small `ε`,
then `g₀` itself obeys the same bound up to the factor `√2` coming from the triangle inequality
(no rate of convergence of the approximation is needed: the approximation error only
contributes `C ε ‖g₀‖_{ℋ⁵}`, which is sent to `0`). -/
theorem Xn_le_sqrt_two_mul_of_Jeps_bound {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 ≤ C₀)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g₀)
    (h5 : Work.Spaces.HkMem α 5 g₀)
    (hsmJ : ∀ ε ∈ Set.Ioc 0 1, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε g₀))
    (hmem4 : ∀ ε ∈ Set.Ioc 0 1, Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε g₀))
    (hbd : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Set.Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Jeps ρ ε g₀) ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α g₀ ≤ Real.sqrt 2 * (C₀ * α ^ 2) := by
  show Work.Spaces.HkNorm α 4 g₀ ≤ Real.sqrt 2 * (C₀ * α ^ 2)
  -- the mollifier-approximation estimate, in the `ℋ⁴`-norm
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le ρ hρ.moll
  obtain ⟨ε₁, hε₁pos, hbnd⟩ := hbd
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  have hm4g : Work.Spaces.HkMem α 4 g₀ := Work.FTS.OpenPkg.HkMem_four_of_five hsm h5
  have hN5 : 0 ≤ Work.Spaces.HkNorm α 5 g₀ := Work.Spaces.HkNorm_nonneg α 5 g₀
  set K : ℝ := Real.sqrt 2 * C * Work.Spaces.HkNorm α 5 g₀ with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hCpos.le) hN5
  -- (★) the bound valid for every `ε` in the range where both hypotheses are available
  have hstar : ∀ ε ∈ Set.Ioc 0 (min ε₁ 1),
      Work.Spaces.HkNorm α 4 g₀ ≤ Real.sqrt 2 * (C₀ * α ^ 2) + K * ε := by
    intro ε hε
    have hε1 : ε ∈ Set.Ioc 0 1 := ⟨hε.1, le_trans hε.2 (min_le_right _ _)⟩
    have hεε₁ : ε ∈ Set.Ioc 0 ε₁ := ⟨hε.1, le_trans hε.2 (min_le_left _ _)⟩
    set J : ℝ → ℝ → ℝ := Work.FTS.StrongEps.Jeps ρ ε g₀ with hJdef
    have hJsm : Work.FTS.EllipticEst.SmoothOpen J := hsmJ ε hε1
    have hJmem : Work.Spaces.HkMem α 4 J := hmem4 ε hε1
    have hDsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => g₀ z θ - J z θ) :=
      Work.FTS.EllipticEst.smoothOpen_sub hsm hJsm
    have hDmem : Work.Spaces.HkMem α 4 (fun z θ => g₀ z θ - J z θ) :=
      hkMem_sub_open_of hsm hJsm hm4g hJmem
    -- the triangle inequality ‖g₀‖ ≤ √2 (‖J‖ + ‖g₀ - J‖)
    have htri : Work.Spaces.HkNorm α 4 (fun z θ => J z θ + (g₀ z θ - J z θ))
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 J
            + Work.Spaces.HkNorm α 4 (fun z θ => g₀ z θ - J z θ)) :=
      Work.FTS.EllipticEst.HkNorm_add_le α 4
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall J).mp hJsm)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hDsm) hJmem hDmem
    have hcongr : Work.Spaces.HkNorm α 4 g₀
        = Work.Spaces.HkNorm α 4 (fun z θ => J z θ + (g₀ z θ - J z θ)) :=
      hkNorm_congr_pt (fun z θ => by ring)
    -- the two summands, estimated separately
    have hJb : Work.Spaces.HkNorm α 4 J ≤ C₀ * α ^ 2 := hbnd ε hεε₁
    have hDb : Work.Spaces.HkNorm α 4 (fun z θ => g₀ z θ - J z θ)
        ≤ C * ε * Work.Spaces.HkNorm α 5 g₀ := by
      have happ : Work.Spaces.HkNorm α 4 (fun z θ => J z θ - g₀ z θ)
          ≤ C * ε * Work.Spaces.HkNorm α 5 g₀ :=
        hC α hαIoc 4 ε hε1 g₀
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall g₀).mp hsm) h5 (hmem4 ε hε1)
      exact (hkNorm_sub_swap (α := α) (k := 4)
        (f := fun z θ => J z θ) (g := fun z θ => g₀ z θ)).le.trans happ
    calc Work.Spaces.HkNorm α 4 g₀
        = Work.Spaces.HkNorm α 4 (fun z θ => J z θ + (g₀ z θ - J z θ)) := hcongr
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 J
            + Work.Spaces.HkNorm α 4 (fun z θ => g₀ z θ - J z θ)) := htri
      _ ≤ Real.sqrt 2 * (C₀ * α ^ 2 + C * ε * Work.Spaces.HkNorm α 5 g₀) :=
          mul_le_mul_of_nonneg_left (add_le_add hJb hDb) (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * (C₀ * α ^ 2) + K * ε := by
          rw [hKdef]; ring
  -- (★★) the error term is `K ε` with `ε` arbitrarily small, so it can be discarded
  have hδpos : 0 < min ε₁ 1 := lt_min hε₁pos one_pos
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hden : 0 < K + 1 := by linarith
  have hXpos : 0 < η / (K + 1) := div_pos hη hden
  have hmem : min (min ε₁ 1) (η / (K + 1)) / 2 ∈ Set.Ioc 0 (min ε₁ 1) := by
    refine ⟨by have h := lt_min hδpos hXpos; linarith, ?_⟩
    have h1 : min (min ε₁ 1) (η / (K + 1)) ≤ min ε₁ 1 := min_le_left _ _
    have h2 := lt_min hδpos hXpos
    linarith
  have hb := hstar _ hmem
  have hKe : K * (min (min ε₁ 1) (η / (K + 1)) / 2) ≤ η := by
    have h1 : min (min ε₁ 1) (η / (K + 1)) / 2 ≤ η / (K + 1) := by
      have h2 : min (min ε₁ 1) (η / (K + 1)) ≤ η / (K + 1) := min_le_right _ _
      have h3 := lt_min hδpos hXpos
      linarith
    have h3 : K * (min (min ε₁ 1) (η / (K + 1)) / 2) ≤ K * (η / (K + 1)) :=
      mul_le_mul_of_nonneg_left h1 hK0
    have h4 : K * (η / (K + 1)) ≤ η := by
      rw [show K * (η / (K + 1)) = K * η / (K + 1) by ring]
      rw [div_le_iff₀ hden]
      nlinarith
    linarith
  linarith [hb, hKe]

end Work.FTS.StrongEps.EpsE4Work
