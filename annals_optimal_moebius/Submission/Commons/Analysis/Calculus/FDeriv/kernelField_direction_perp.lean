import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2

open Topology
set_option autoImplicit false

noncomputable section
namespace Commons.Analysis.Calculus.FDeriv

/-- Auxiliary real algebra for `kernelField_direction_perp`. -/
lemma kernel_alg (aa bb cc A0 B0 C0 : ℝ)
    (h1 : aa * C0 + cc * A0 = 2 * bb * B0)
    (h2 : aa * cc = bb ^ 2) :
    aa * (bb * B0 - aa * C0) + bb * -(bb * A0 - aa * B0) = 0 := by
  have h2' : aa * cc = bb * bb := by simpa [pow_two] using h2
  have h1m : aa * (aa * C0 + cc * A0) = aa * (2 * bb * B0) := by
    exact congrArg (fun t : ℝ => aa * t) h1
  have h1' : aa * aa * C0 + aa * cc * A0 = 2 * aa * bb * B0 := by
    nlinarith [h1m]
  have h2'' : aa * cc * A0 = bb * bb * A0 := by
    rw [h2']
  have h1'' : aa * aa * C0 + bb * bb * A0 = 2 * aa * bb * B0 := by
    nlinarith [h1', h2'']
  calc
    aa * (bb * B0 - aa * C0) + bb * -(bb * A0 - aa * B0)
        = (2 * aa * bb * B0) - (aa * aa * C0 + bb * bb * A0) := by ring
    _ = 0 := by nlinarith [h1'']

theorem kernelField_direction_perp
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (a b c : EuclideanSpace ℝ (Fin 2) → ℝ)
    (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b U) (hc : ContDiffOn ℝ 1 c U)
    (hgauss : ∀ x ∈ U, a x * c x = (b x) ^ 2)
    (hcod1 : ∀ x ∈ U,
      fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) =
      fderiv ℝ b x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
    (hcod2 : ∀ x ∈ U,
      fderiv ℝ c x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
      fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) :
    ∀ x ∈ U, let w : EuclideanSpace ℝ (Fin 2) :=
        (b x) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-a x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
      a x * ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        (b y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-a y) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x w) (0 : Fin 2)) +
      b x * ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        (b y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-a y) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x w) (1 : Fin 2)) = 0 := by
  intro x hx
  let e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  let F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun y => (b y) • e0 + (-(a y)) • e1
  let w : EuclideanSpace ℝ (Fin 2) := (b x) • e0 + (-(a x)) • e1
  change a x * ((fderiv ℝ F x w) 0) + b x * ((fderiv ℝ F x w) 1) = 0
  have hda : DifferentiableAt ℝ a x := by
    exact (ha.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (IsOpen.mem_nhds hU hx)
  have hdb : DifferentiableAt ℝ b x := by
    exact (hb.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (IsOpen.mem_nhds hU hx)
  have hdc : DifferentiableAt ℝ c x := by
    exact (hc.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (IsOpen.mem_nhds hU hx)
  have hd0 : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (b y) • e0) x := by
    exact hdb.smul (differentiableAt_const e0)
  have hd1 : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (-(a y)) • e1) x := by
    exact hda.neg.smul (differentiableAt_const e1)
  have hf0 : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (b y) • e0) x = (fderiv ℝ b x).smulRight e0 := by
    exact fderiv_smul_const hdb e0
  have hf1 : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (-(a y)) • e1) x =
      (-(fderiv ℝ a x)).smulRight e1 := by
    have hc' : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => -(a y)) x := hda.neg
    have hsm := fderiv_smul_const hc' e1
    have hnegm : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => -(a y)) x = -fderiv ℝ a x := by
      simpa using (fderiv_neg (f := a) (x := x))
    calc
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (-(a y)) • e1) x
          = (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => -(a y)) x).smulRight e1 := hsm
      _ = (-(fderiv ℝ a x)).smulRight e1 := by rw [hnegm]
  have hFmap : fderiv ℝ F x = (fderiv ℝ b x).smulRight e0 + (-(fderiv ℝ a x)).smulRight e1 := by
    have hFdef : F = (fun y : EuclideanSpace ℝ (Fin 2) => (b y) • e0) +
        (fun y : EuclideanSpace ℝ (Fin 2) => (-(a y)) • e1) := by
      rfl
    calc
      fderiv ℝ F x = fderiv ℝ ((fun y : EuclideanSpace ℝ (Fin 2) => (b y) • e0) +
          (fun y : EuclideanSpace ℝ (Fin 2) => (-(a y)) • e1)) x := by rw [hFdef]
      _ = fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (b y) • e0) x +
          fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (-(a y)) • e1) x := fderiv_add hd0 hd1
      _ = (fderiv ℝ b x).smulRight e0 + (-(fderiv ℝ a x)).smulRight e1 := by rw [hf0, hf1]
  have hFw : fderiv ℝ F x w = (fderiv ℝ b x w) • e0 + (-(fderiv ℝ a x w)) • e1 := by
    calc
      fderiv ℝ F x w = ((fderiv ℝ b x).smulRight e0 + (-(fderiv ℝ a x)).smulRight e1) w := by
        rw [hFmap]
      _ = ((fderiv ℝ b x).smulRight e0) w + ((-(fderiv ℝ a x)).smulRight e1) w := by simp
      _ = (fderiv ℝ b x w) • e0 + (-(fderiv ℝ a x w)) • e1 := by
        simp [ContinuousLinearMap.smulRight_apply]
  have hF0 : (fderiv ℝ F x w) 0 = fderiv ℝ b x w := by
    rw [hFw]
    simp [e0, e1]
  have hF1 : (fderiv ℝ F x w) 1 = -(fderiv ℝ a x w) := by
    rw [hFw]
    simp [e0, e1]
  -- Gauss equation differentiated in direction e0
  have hG0 : (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a y * c y) x) e0 =
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (b y) ^ 2) x) e0 := by
    have heq : (fun y : EuclideanSpace ℝ (Fin 2) => a y * c y) =ᶠ[𝓝 x]
        (fun y : EuclideanSpace ℝ (Fin 2) => (b y) ^ 2) := by
      filter_upwards [IsOpen.mem_nhds hU hx] with y hy
      exact hgauss y hy
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => L e0)
      (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq)
  have hprod0 : (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a y * c y) x) e0 =
      a x * (fderiv ℝ c x e0) + c x * (fderiv ℝ a x e0) := by
    have hm := fderiv_mul hda hdc
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => L e0) hm
  have hsq0 : (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (b y) ^ 2) x) e0 =
      2 * b x * (fderiv ℝ b x e0) := by
    have hm := fderiv_pow 2 hdb
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => L e0) hm
    -- h : (fderiv ℝ (b ^ 2) x) e0 = ...
    -- convert function-level pow to pointwise pow
    have hfun : (fun y : EuclideanSpace ℝ (Fin 2) => (b y) ^ 2) = (b ^ 2 : EuclideanSpace ℝ (Fin 2) → ℝ) := by
      rfl
    rw [← hfun] at h
    simpa using h
  have hgauss0 : a x * (fderiv ℝ c x e0) + c x * (fderiv ℝ a x e0) =
      2 * b x * (fderiv ℝ b x e0) := by
    calc
      a x * (fderiv ℝ c x e0) + c x * (fderiv ℝ a x e0) =
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a y * c y) x) e0 := by
            rw [hprod0]
      _ = (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (b y) ^ 2) x) e0 := hG0
      _ = 2 * b x * (fderiv ℝ b x e0) := by rw [hsq0]
  -- linearity of fderiv in the direction w
  have hbw : fderiv ℝ b x w = (b x) * (fderiv ℝ b x e0) - (a x) * (fderiv ℝ b x e1) := by
    simp [w, map_add, map_smul]
    ring
  have haw : fderiv ℝ a x w = (b x) * (fderiv ℝ a x e0) - (a x) * (fderiv ℝ a x e1) := by
    simp [w, map_add, map_smul]
    ring
  -- algebra
  have hcod1x : fderiv ℝ a x e1 = fderiv ℝ b x e0 := hcod1 x hx
  have hcod2x : fderiv ℝ c x e0 = fderiv ℝ b x e1 := hcod2 x hx
  have hgaussx : a x * c x = (b x) ^ 2 := hgauss x hx
  rw [hF0, hF1]
  have hmw : a x * (fderiv ℝ b x w) + b x * (-(fderiv ℝ a x w)) = 0 := by
    rw [hbw, haw, hcod1x, ← hcod2x]
    exact kernel_alg (a x) (b x) (c x) (fderiv ℝ a x e0) (fderiv ℝ b x e0) (fderiv ℝ c x e0) hgauss0 hgaussx
  exact hmw

end Commons.Analysis.Calculus.FDeriv