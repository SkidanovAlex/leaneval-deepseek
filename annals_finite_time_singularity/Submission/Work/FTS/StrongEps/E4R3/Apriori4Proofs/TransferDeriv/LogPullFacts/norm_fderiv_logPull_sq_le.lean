import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `norm_fderiv_logPull_sq_le` — the size of the Fréchet derivative of the log-pull

In the log coordinates `(s, ζ) ↦ Ψ(s,ζ) = (e^s, arctan (e^ζ))` the transport operators
`D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` become the two partial derivatives of the pulled-back
profile: the directional derivative of `logPull g` in the `s`-direction is `D_z g`, and in the
`ζ`-direction it is `D_θ g / 2` (because `dθ/dζ = sin(2θ)/2` for `θ = arctan(e^ζ)`).

Since the norm on `ℝ × ℝ` is the sup norm, whose unit ball is the square, one has
`‖L‖ ≤ |L e₁| + |L e₂|` for every continuous linear functional `L`, hence

  `‖fderiv ℝ (logPull g) y‖² ≤ 2 (D_z g)² + 2 (D_θ g / 2)² ≤ 2 (D_z g)² + (D_θ g)²`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts

/-! ## Elementary one-dimensional facts -/

/-- `sin (2 arctan t) / 2 = t / (1 + t²)`: the elementary trigonometric identity behind the
change of coordinate `θ = arctan (e^ψ)`. -/
private lemma sin_two_arctan_div_two (t : ℝ) : Real.sin (2 * Real.arctan t) / 2 = t / (1 + t ^ 2) := by
  have hD : (0 : ℝ) ≤ 1 + t ^ 2 := by positivity
  have h2 : Real.sin (Real.arctan t) * Real.cos (Real.arctan t) = t / (1 + t ^ 2) := by
    rw [Real.sin_arctan, Real.cos_arctan, div_mul_div_comm, mul_one, Real.mul_self_sqrt hD]
  rw [Real.sin_two_mul]
  rw [show (2 : ℝ) * Real.sin (Real.arctan t) * Real.cos (Real.arctan t) / 2
        = Real.sin (Real.arctan t) * Real.cos (Real.arctan t) by ring]
  exact h2

/-- `d/dψ arctan (e^ψ) = sin (2 arctan (e^ψ)) / 2`. -/
private lemma hasDerivAt_arctan_exp (ψ : ℝ) :
    HasDerivAt (fun ψ' => Real.arctan (Real.exp ψ'))
      (Real.sin (2 * Real.arctan (Real.exp ψ)) / 2) ψ := by
  have h := (Real.hasDerivAt_arctan (Real.exp ψ)).comp ψ (Real.hasDerivAt_exp ψ)
  have hv : (1 / (1 + (Real.exp ψ) ^ 2)) * Real.exp ψ
      = Real.sin (2 * Real.arctan (Real.exp ψ)) / 2 := by
    rw [sin_two_arctan_div_two]
    rw [one_div, inv_mul_eq_div]
  rw [hv] at h
  exact h

/-- The `θ`-derivative of the `θ`-slice of a function smooth on the open quadrant.  (The
`z`-analogue is `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`.) -/
private lemma hasDerivAt_slice_th {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ :=
  ((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt

/-! ## The operator norm on `ℝ × ℝ` -/

/-- For a continuous linear functional on `ℝ × ℝ` (with the sup norm) the operator norm is
bounded by the sum of the absolute values of the two values on the standard basis.  Squaring
gives the form used below. -/
private lemma opNorm_sq_le_inl_inr (L : ℝ × ℝ →L[ℝ] ℝ) :
    ‖L‖ ^ 2 ≤ 2 * (L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) ^ 2
      + 2 * (L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) ^ 2 := by
  have hM : ‖L‖ ≤ |L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)| + |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)| := by
    refine ContinuousLinearMap.opNorm_le_bound L (by positivity) fun v => ?_
    have hv : v = v.1 • (ContinuousLinearMap.inl ℝ ℝ ℝ 1)
        + v.2 • (ContinuousLinearMap.inr ℝ ℝ ℝ 1) := by
      ext <;> simp [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
    have hLv : L v = v.1 • L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)
        + v.2 • L (ContinuousLinearMap.inr ℝ ℝ ℝ 1) := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul]
    rw [hLv]
    have h1 : |v.1| ≤ ‖v‖ := by
      have := norm_fst_le v
      rwa [Real.norm_eq_abs] at this
    have h2 : |v.2| ≤ ‖v‖ := by
      have := norm_snd_le v
      rwa [Real.norm_eq_abs] at this
    calc ‖v.1 • L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)
            + v.2 • L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)‖
        ≤ ‖v.1 • L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)‖
            + ‖v.2 • L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)‖ := norm_add_le _ _
      _ = |v.1| * |L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)|
            + |v.2| * |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)| := by
          simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ (|L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)|
              + |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)|) * ‖v‖ := by
          have hA : (0 : ℝ) ≤ |L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)| := abs_nonneg _
          have hB : (0 : ℝ) ≤ |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)| := abs_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right h1 hA, mul_le_mul_of_nonneg_right h2 hB]
  have h1 : ‖L‖ ^ 2
      ≤ (|L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)| + |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)|) ^ 2 := by
    nlinarith [norm_nonneg L]
  have h2 : (|L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)| + |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)|) ^ 2
      ≤ 2 * (L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) ^ 2
        + 2 * (L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) ^ 2 := by
    nlinarith [sq_nonneg (|L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)|
          - |L (ContinuousLinearMap.inr ℝ ℝ ℝ 1)|),
      sq_abs (L (ContinuousLinearMap.inl ℝ ℝ ℝ 1)),
      sq_abs (L (ContinuousLinearMap.inr ℝ ℝ ℝ 1))]
  linarith

/-! ## The two directional derivatives of `logPull` -/

/-- The directional derivative of `logPull g` along the `s`-direction is `D_z g`. -/
private lemma hasDerivAt_logPull_inl {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y.1 + t, y.2))
      (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) 0 := by
  have hSmooth : Work.FTS.EllipticEst.SmoothOpen g := Work.FTS.EllipticEst.smoothOpen_of_forall hg
  have hθ : Real.arctan (Real.exp y.2) ∈ Set.Ioo 0 (π / 2) :=
    ⟨Real.arctan_pos.mpr (Real.exp_pos y.2), Real.arctan_lt_pi_div_two _⟩
  have hslice : HasDerivAt (fun z' : ℝ => g z' (Real.arctan (Real.exp y.2)))
      (Work.Spaces.pz g (Real.exp (y.1 + 0)) (Real.arctan (Real.exp y.2)))
      (Real.exp (y.1 + 0)) :=
    hSmooth.hasDerivAt_slice hθ (Real.exp_pos _)
  have hinner : HasDerivAt (fun t : ℝ => Real.exp (y.1 + t)) (Real.exp (y.1 + 0) * 1) 0 :=
    (Real.hasDerivAt_exp (y.1 + 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_add y.1)
  have hc := hslice.comp 0 hinner
  refine hc.congr_deriv ?_
  simp only [Work.Spaces.Dz, Work.Spaces.pz, add_zero, mul_one]
  ring

/-- The directional derivative of `logPull g` along the `ζ`-direction is `D_θ g / 2`. -/
private lemma hasDerivAt_logPull_inr {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y.1, y.2 + t))
      (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2) 0 := by
  have hSmooth : Work.FTS.EllipticEst.SmoothOpen g := Work.FTS.EllipticEst.smoothOpen_of_forall hg
  have hθ : Real.arctan (Real.exp (y.2 + 0)) ∈ Set.Ioo 0 (π / 2) :=
    ⟨Real.arctan_pos.mpr (Real.exp_pos _), Real.arctan_lt_pi_div_two _⟩
  have hslice : HasDerivAt (fun θ' : ℝ => g (Real.exp y.1) θ')
      (Work.Spaces.pth g (Real.exp y.1) (Real.arctan (Real.exp (y.2 + 0))))
      (Real.arctan (Real.exp (y.2 + 0))) :=
    hasDerivAt_slice_th hSmooth (Real.exp_pos y.1) hθ
  have hinner : HasDerivAt (fun t : ℝ => Real.arctan (Real.exp (y.2 + t)))
      (Real.sin (2 * Real.arctan (Real.exp (y.2 + 0))) / 2 * 1) 0 :=
    (hasDerivAt_arctan_exp (y.2 + 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_add y.2)
  have hc := hslice.comp 0 hinner
  refine hc.congr_deriv ?_
  simp only [Work.Spaces.Dth, Work.Spaces.pth, add_zero, mul_one]
  ring

/-- `logPull g` is differentiable at every point (the quadrant is open, so `g` is smooth there). -/
private lemma differentiableAt_logPull {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    DifferentiableAt ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y := by
  have hΨ : DifferentiableAt ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi) y := by
    have hf : Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi
        = fun y : ℝ × ℝ => (Real.exp y.1, Real.arctan (Real.exp y.2)) := rfl
    rw [hf]
    exact ((differentiableAt_fst (p := y)).exp).prodMk (((differentiableAt_snd (p := y)).exp).arctan)
  have hQ0 : Work.FTS.EllipticEst.Q0
      ∈ 𝓝 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi y) :=
    Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi_mem_quad y)
  have hA : DifferentiableAt ℝ (Function.uncurry g)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPsi y) :=
    ((hg 1).differentiableOn (by norm_num)).differentiableAt hQ0
  exact hA.comp y hΨ

/-! ## The values of the Fréchet derivative on the standard basis -/

/-- The Fréchet derivative of `logPull g` at `y` sends the first basis vector to `D_z g`. -/
private lemma fderiv_logPull_inl {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
        (ContinuousLinearMap.inl ℝ ℝ ℝ 1)
      = Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2)) := by
  have hpt : (y.1 + 0, y.2) = y := by simp
  have hF : HasFDerivAt (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) (y.1 + 0, y.2))
      (y.1 + 0, y.2) :=
    (differentiableAt_logPull hg (y.1 + 0, y.2)).hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => y + t • (ContinuousLinearMap.inl ℝ ℝ ℝ 1))
      (ContinuousLinearMap.inl ℝ ℝ ℝ 1) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (ContinuousLinearMap.inl ℝ ℝ ℝ 1)).const_add y
    simpa using h
  have hfun : (fun t : ℝ => y + t • (ContinuousLinearMap.inl ℝ ℝ ℝ 1))
      = fun t : ℝ => (y.1 + t, y.2) := by
    funext t
    simp only [ContinuousLinearMap.inl_apply, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
    exact (Prod.add_def y (t, 0)).trans (by simp)
  rw [hfun] at hcurve
  have hcomp := hF.comp_hasDerivAt 0 hcurve
  rw [hpt] at hcomp
  exact hcomp.unique (hasDerivAt_logPull_inl hg y)

/-- The Fréchet derivative of `logPull g` at `y` sends the second basis vector to `D_θ g / 2`. -/
private lemma fderiv_logPull_inr {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
        (ContinuousLinearMap.inr ℝ ℝ ℝ 1)
      = Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2 := by
  have hpt : (y.1, y.2 + 0) = y := by simp
  have hF : HasFDerivAt (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)
      (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) (y.1, y.2 + 0))
      (y.1, y.2 + 0) :=
    (differentiableAt_logPull hg (y.1, y.2 + 0)).hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => y + t • (ContinuousLinearMap.inr ℝ ℝ ℝ 1))
      (ContinuousLinearMap.inr ℝ ℝ ℝ 1) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (ContinuousLinearMap.inr ℝ ℝ ℝ 1)).const_add y
    simpa using h
  have hfun : (fun t : ℝ => y + t • (ContinuousLinearMap.inr ℝ ℝ ℝ 1))
      = fun t : ℝ => (y.1, y.2 + t) := by
    funext t
    simp only [ContinuousLinearMap.inr_apply, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
    exact (Prod.add_def y (0, t)).trans (by simp)
  rw [hfun] at hcurve
  have hcomp := hF.comp_hasDerivAt 0 hcurve
  rw [hpt] at hcomp
  exact hcomp.unique (hasDerivAt_logPull_inr hg y)

/-- **The Fréchet derivative of the log-pull is bounded by `D_z g` and `D_θ g`.** -/
theorem norm_fderiv_logPull_sq_le {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (y : ℝ × ℝ) :
    ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2
      ≤ 2 * (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2
        + (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2 := by
  have h := opNorm_sq_le_inl_inr (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y)
  rw [fderiv_logPull_inl hg y, fderiv_logPull_inr hg y] at h
  have hsq : (2 : ℝ) * (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)) / 2) ^ 2
      ≤ (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2 := by
    nlinarith [sq_nonneg (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2)))]
  linarith

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts
