import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

namespace Work.FTS.EllipticEst

/-- **Pointwise algebra for the honest `I₄` upper bound.**  For `Φ` of class `C²` on the open
interval `(0, π/2)` — the angular slice of the stream function `Ψ` — the following four
elementary calculus identities hold at every `θ ∈ (0, π/2)`, with `ψ = Φ/cos θ`, `b = Φ''`,
`P = cos²θ·ψ'` and `σ = (sin 2θ)^{-η}`, `η = 99/100`:

* `u := ∂_θ(tan θ·Φ) = cos θ·ψ + sin θ·ψ'`,
* `Φ'' = cos θ·ψ'' - 2 sin θ·ψ' - cos θ·ψ`,
* `P' = cos θ·(Φ'' + Φ)`,
* `(½·sin θ/cos³θ·σ·P²)' = (sin θ/cos³θ)·σ·P·P' + ½·((1-η)cos²θ + (3+η)sin²θ)·σ·(ψ')²`.

The last is the key integration-by-parts primitive: `(sin θ/cos³θ·σ)' = Σ·σ/cos⁴θ` with
`Σ = (1-η)cos²θ + (3+η)sin²θ`, and `P² = cos⁴θ·(ψ')²`. -/
theorem I4SliceAlgebra (Φ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => Real.tan θ' * Φ θ') θ
          = Real.cos θ * (Φ θ / Real.cos θ)
            + Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ)
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (deriv Φ) θ
          = Real.cos θ * deriv (deriv (fun θ' => Φ θ' / Real.cos θ')) θ
            - 2 * Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ
            - Real.cos θ * (Φ θ / Real.cos θ))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
          = Real.cos θ * (deriv (deriv Φ) θ + Φ θ))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (1/2) * (Real.sin θ' / (Real.cos θ')^3)
            * (Real.sin (2*θ'))^(-(99/100:ℝ))
            * ((Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ')^2) θ
          = (Real.sin θ / (Real.cos θ)^3) * (Real.sin (2*θ))^(-(99/100:ℝ))
              * ((Real.cos θ)^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ)
              * deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
            + (1/2) * ((1 - 99/100) * (Real.cos θ)^2 + (3 + 99/100) * (Real.sin θ)^2)
              * (Real.sin (2*θ))^(-(99/100:ℝ))
              * (deriv (fun θ' => Φ θ' / Real.cos θ') θ)^2) := by
  set ψ : ℝ → ℝ := fun x => Φ x / Real.cos x with hψdef
  have hcosI : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi/2), 0 < Real.cos x := by
    intro x hx
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
  have hCψ_all : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), ContDiffAt ℝ 2 ψ θ := by
    intro θ hθ
    have hmem : Set.Ioo (0:ℝ) (Real.pi/2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hCF : ContDiffAt ℝ 2 Φ θ := hsm.contDiffAt hmem
    rw [hψdef]
    exact hCF.div Real.contDiff_cos.contDiffAt (ne_of_gt (hcosI θ hθ))
  have hDψ_all : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), DifferentiableAt ℝ ψ θ :=
    fun θ hθ => (hCψ_all θ hθ).differentiableAt (by norm_num)
  have hDψ'_all : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), DifferentiableAt ℝ (deriv ψ) θ := by
    intro θ hθ
    exact (ContDiffAt.derivWithin (hCψ_all θ hθ)
      (show (1:WithTop ℕ∞)+1 ≤ 2 from by norm_num)).differentiableAt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ
    have hmem : Set.Ioo (0:ℝ) (Real.pi/2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hψd : HasDerivAt ψ (deriv ψ θ) θ := (hDψ_all θ hθ).hasDerivAt
    have hfun : (fun θ' => Real.tan θ' * Φ θ') =ᶠ[𝓝 θ] (fun θ' => Real.sin θ' * ψ θ') := by
      filter_upwards [hmem] with x hx
      rw [Real.tan_eq_sin_div_cos, hψdef]
      have hc : Real.cos x ≠ 0 := ne_of_gt (hcosI x hx)
      field_simp
    have hderiv : deriv (fun θ' => Real.sin θ' * ψ θ') θ
        = Real.cos θ * ψ θ + Real.sin θ * deriv ψ θ :=
      ((Real.hasDerivAt_sin θ).mul hψd).deriv
    rw [Filter.EventuallyEq.deriv_eq hfun, hderiv]
  · intro θ hθ
    have hmem : Set.Ioo (0:ℝ) (Real.pi/2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hψd : HasDerivAt ψ (deriv ψ θ) θ := (hDψ_all θ hθ).hasDerivAt
    have hψ2d : HasDerivAt (deriv ψ) (deriv (deriv ψ) θ) θ := (hDψ'_all θ hθ).hasDerivAt
    have hdΦ : deriv Φ =ᶠ[𝓝 θ] (fun x => -Real.sin x * ψ x + Real.cos x * deriv ψ x) := by
      filter_upwards [hmem] with x hx
      have hmemx : Set.Ioo (0:ℝ) (Real.pi/2) ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
      have heq : Φ =ᶠ[𝓝 x] (fun y => Real.cos y * ψ y) := by
        filter_upwards [hmemx] with y hy
        rw [hψdef]
        field_simp [ne_of_gt (hcosI y hy)]
      rw [Filter.EventuallyEq.deriv_eq heq]
      exact ((Real.hasDerivAt_cos x).mul (hDψ_all x hx).hasDerivAt).deriv
    have hd2Φ : deriv (deriv Φ) θ
        = -Real.cos θ * ψ θ - 2 * Real.sin θ * deriv ψ θ + Real.cos θ * deriv (deriv ψ) θ := by
      rw [Filter.EventuallyEq.deriv_eq hdΦ]
      have h1 : HasDerivAt (fun x => -Real.sin x * ψ x)
          (-Real.cos θ * ψ θ + (-Real.sin θ) * deriv ψ θ) θ :=
        ((Real.hasDerivAt_sin θ).neg).mul hψd
      have h2 : HasDerivAt (fun x => Real.cos x * deriv ψ x)
          ((-Real.sin θ) * deriv ψ θ + Real.cos θ * deriv (deriv ψ) θ) θ :=
        (Real.hasDerivAt_cos θ).mul hψ2d
      rw [show (fun x => -Real.sin x * ψ x + Real.cos x * deriv ψ x)
          = ((fun x => -Real.sin x * ψ x) + fun x => Real.cos x * deriv ψ x) from by
        funext x; rfl]
      rw [(h1.add h2).deriv]
      ring
    rw [hd2Φ]
    simp only [hψdef]
    ring
  · intro θ hθ
    have hmem : Set.Ioo (0:ℝ) (Real.pi/2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hne : Real.cos θ ≠ 0 := ne_of_gt (hcosI θ hθ)
    have hψd : HasDerivAt ψ (deriv ψ θ) θ := (hDψ_all θ hθ).hasDerivAt
    have hψ2d : HasDerivAt (deriv ψ) (deriv (deriv ψ) θ) θ := (hDψ'_all θ hθ).hasDerivAt
    have hdΦ : deriv Φ =ᶠ[𝓝 θ] (fun x => -Real.sin x * ψ x + Real.cos x * deriv ψ x) := by
      filter_upwards [hmem] with x hx
      have hmemx : Set.Ioo (0:ℝ) (Real.pi/2) ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
      have heq : Φ =ᶠ[𝓝 x] (fun y => Real.cos y * ψ y) := by
        filter_upwards [hmemx] with y hy
        rw [hψdef]
        field_simp [ne_of_gt (hcosI y hy)]
      rw [Filter.EventuallyEq.deriv_eq heq]
      exact ((Real.hasDerivAt_cos x).mul (hDψ_all x hx).hasDerivAt).deriv
    have hd2Φ : deriv (deriv Φ) θ
        = -Real.cos θ * ψ θ - 2 * Real.sin θ * deriv ψ θ + Real.cos θ * deriv (deriv ψ) θ := by
      rw [Filter.EventuallyEq.deriv_eq hdΦ]
      have h1 : HasDerivAt (fun x => -Real.sin x * ψ x)
          (-Real.cos θ * ψ θ + (-Real.sin θ) * deriv ψ θ) θ :=
        ((Real.hasDerivAt_sin θ).neg).mul hψd
      have h2 : HasDerivAt (fun x => Real.cos x * deriv ψ x)
          ((-Real.sin θ) * deriv ψ θ + Real.cos θ * deriv (deriv ψ) θ) θ :=
        (Real.hasDerivAt_cos θ).mul hψ2d
      rw [show (fun x => -Real.sin x * ψ x + Real.cos x * deriv ψ x)
          = ((fun x => -Real.sin x * ψ x) + fun x => Real.cos x * deriv ψ x) from by
        funext x; rfl]
      rw [(h1.add h2).deriv]
      ring
    have hP : HasDerivAt (fun x => (Real.cos x)^2 * deriv ψ x)
        ((2:ℕ) * (Real.cos θ)^(2-1) * (-Real.sin θ) * deriv ψ θ + (Real.cos θ)^2 * deriv (deriv ψ) θ) θ :=
      ((Real.hasDerivAt_cos θ).pow 2).mul hψ2d
    rw [hP.deriv, hd2Φ]
    simp only [hψdef]
    field_simp
    ring_nf
  · intro θ hθ
    have hmem : Set.Ioo (0:ℝ) (Real.pi/2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hcp : 0 < Real.cos θ := hcosI θ hθ
    have hne : Real.cos θ ≠ 0 := ne_of_gt hcp
    have hsp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hsp' : Real.sin θ ≠ 0 := ne_of_gt hsp
    have hp2 : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hp2' : Real.sin (2*θ) ≠ 0 := ne_of_gt hp2
    set σ : ℝ := (Real.sin (2*θ))^(-(99/100:ℝ)) with hσdef
    have hψd : HasDerivAt ψ (deriv ψ θ) θ := (hDψ_all θ hθ).hasDerivAt
    have hψ2d : HasDerivAt (deriv ψ) (deriv (deriv ψ) θ) θ := (hDψ'_all θ hθ).hasDerivAt
    have hσfun : HasDerivAt (fun x => (Real.sin (2*x))^(-(99/100:ℝ)))
        (-(99/100:ℝ) * σ * (2 * (Real.cos (2*θ) / Real.sin (2*θ)))) θ := by
      have hinner : HasDerivAt (fun x => Real.sin (2*x)) (Real.cos (2*θ) * 2) θ := by
        have h1 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
          simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
        have h2 := (Real.hasDerivAt_sin (2*θ)).comp θ h1
        exact h2
      have hb := (Real.hasDerivAt_rpow_const (x := Real.sin (2*θ)) (p := -(99/100:ℝ))
        (Or.inl hp2')).comp θ hinner
      have hrw : (Real.sin (2*θ))^(-(99/100:ℝ)-1) = σ * (Real.sin (2*θ))⁻¹ := by
        rw [show -(99/100:ℝ)-1 = (-(99/100:ℝ)) + (-1) by ring, Real.rpow_add hp2,
          Real.rpow_neg_one, hσdef]
      have hv : (-(99/100:ℝ) * (Real.sin (2*θ))^(-(99/100:ℝ)-1) * (Real.cos (2*θ) * 2))
          = (-(99/100:ℝ) * σ * (2 * (Real.cos (2*θ) / Real.sin (2*θ)))) := by
        rw [hrw, div_eq_mul_inv]
        ring
      rwa [hv] at hb
    have hsc : HasDerivAt (fun x => Real.sin x * Real.cos x)
        (Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) θ :=
      (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)
    have hA : HasDerivAt (fun x => (1/2) * (Real.sin x * Real.cos x))
        ((1/2) * (Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ))) θ :=
      hsc.const_mul (1/2)
    have hB : HasDerivAt (fun x => (1/2) * (Real.sin x * Real.cos x) * (Real.sin (2*x))^(-(99/100:ℝ)))
        ((1/2) * (Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) * (Real.sin (2*θ))^(-(99/100:ℝ))
          + (1/2) * (Real.sin θ * Real.cos θ) * (-(99/100:ℝ) * σ * (2 * (Real.cos (2*θ) / Real.sin (2*θ))))) θ :=
      hA.mul hσfun
    have hC : HasDerivAt (fun x => (1/2) * (Real.sin x * Real.cos x) * (Real.sin (2*x))^(-(99/100:ℝ)) * (deriv ψ x)^2)
        (((1/2) * (Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) * (Real.sin (2*θ))^(-(99/100:ℝ))
            + (1/2) * (Real.sin θ * Real.cos θ) * (-(99/100:ℝ) * σ * (2 * (Real.cos (2*θ) / Real.sin (2*θ))))) * (deriv ψ θ)^2
          + ((1/2) * (Real.sin θ * Real.cos θ) * (Real.sin (2*θ))^(-(99/100:ℝ)))
              * ((2:ℕ) * (deriv ψ θ)^(2-1) * deriv (deriv ψ) θ)) θ :=
      hB.mul (hψ2d.pow 2)
    have hFG : (fun x => (1/2) * (Real.sin x / (Real.cos x)^3)
            * (Real.sin (2*x))^(-(99/100:ℝ))
            * ((Real.cos x)^2 * deriv ψ x)^2)
        =ᶠ[𝓝 θ] (fun x => (1/2) * (Real.sin x * Real.cos x) * (Real.sin (2*x))^(-(99/100:ℝ)) * (deriv ψ x)^2) := by
      filter_upwards [hmem] with x hx
      have hc : Real.cos x ≠ 0 := ne_of_gt (hcosI x hx)
      field_simp
    have hP : HasDerivAt (fun x => (Real.cos x)^2 * deriv ψ x)
        ((2:ℕ) * (Real.cos θ)^(2-1) * (-Real.sin θ) * deriv ψ θ + (Real.cos θ)^2 * deriv (deriv ψ) θ) θ :=
      ((Real.hasDerivAt_cos θ).pow 2).mul ((hDψ'_all θ hθ).hasDerivAt)
    rw [Filter.EventuallyEq.deriv_eq hFG, hC.deriv, ← hσdef, hP.deriv]
    rw [Real.sin_two_mul, Real.cos_two_mul']
    field_simp
    ring_nf


end Work.FTS.EllipticEst
