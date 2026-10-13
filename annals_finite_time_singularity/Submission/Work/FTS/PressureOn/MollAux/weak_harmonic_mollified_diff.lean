import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.MollDefs
import Submission.Work.FTS.PressureOn.MollAux.Dpair_convolution
import Submission.Work.FTS.PressureOn.MollAux.moll_smooth_bounded
import Submission.Work.FTS.PressureOn.MollAux.rho_props
import Submission.Work.FTS.PressureOn.MollAux.laplaceTraceVec_smooth_compact
import Submission.Work.FTS.PressureOn.Auxiliary.convolution_laplaceTraceVec_comm
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient
import Submission.Work.FTS.PressureOn.Weyl.dpair_laplaceTraceVec_eq_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory

/-- **The mollified pair is weakly harmonic.**

Let `q : ℝ³ → ℝ` and `Φ : ℝ³ → ℝ³` be continuous and such that the distribution
`D = Φ - ∇q` is annihilated by both `∇φ` (`hdiv`) and `∇×ψ` (`hcurl`).  Then, for every smooth
compactly supported `W`, the *mollified* field `mollV n Φ - ∇(moll n q)` is orthogonal to
`laplaceTraceVec W`.

The three ingredients of the proof are

* `Work.FTS.PressureOn.Weyl.dpair_laplaceTraceVec_eq_zero`: the un-mollified pair pairs to zero
  against `ΔV` for every smooth compactly supported `V`; applied to `V = mollV n W`, which is
  again smooth with compact support (a convolution of two compactly supported functions);
* `Dpair_convolution`: the pairing `Dpair q Φ f = ∫⟪Φ, f⟫ + ∫ q · div f` is invariant under
  replacing `(q, Φ)` by the mollified pair and `f` by `ρ ⋆ f`;
* `Auxiliary.convolution_laplaceTraceVec_comm`: `ρ ⋆ (ΔW) = Δ(ρ ⋆ W)`.

These give `Dpair (moll n q) (mollV n Φ) (laplaceTraceVec W) = 0`, and the final identity
`∫⟪mollV n Φ - ∇(moll n q), ΔW⟫ = Dpair (moll n q) (mollV n Φ) (ΔW)` is the integration by parts
`∫ f · div V = -∫⟪∇f, V⟫` (`Auxiliary.integral_mul_div_eq_neg_inner_gradient`). -/
theorem weak_harmonic_mollified_diff
    (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hdiv : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) →
      HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x)
        = -∫ x, q x * Work.FTS.PressureOn.laplaceTrace φ x)
    (hcurl : ∀ ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0)
    (n : ℕ) (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ m : ℕ, ContDiff ℝ m W) (hWc : HasCompactSupport W) :
    ∫ x, inner ℝ (Work.FTS.PressureOn.mollV n Φ x
        - gradient (Work.FTS.PressureOn.moll n q) x)
      (Work.FTS.PressureOn.laplaceTraceVec W x) = 0 := by
  -- the mollifier `rho n`
  have hρ : ∀ m : ℕ, ContDiff ℝ m (rho n) := (rho_props n).1
  have hρc : HasCompactSupport (rho n) := (rho_props n).2.1
  have hρeven : ∀ z, rho n (-z) = rho n z := (rho_props n).2.2.2.2.1
  -- the test field `ΔW` and its mollification `mollV n W`
  have hΔs : ∀ m : ℕ, ContDiff ℝ m (laplaceTraceVec W) :=
    (laplaceTraceVec_smooth_compact W hW).1
  have hΔc : HasCompactSupport (laplaceTraceVec W) :=
    (laplaceTraceVec_smooth_compact W hW).2 hWc
  have hWVs : ∀ m : ℕ, ContDiff ℝ m (mollV n W) :=
    MollSB.contDiff_mollV n W (hW 0).continuous
  have hWVc : HasCompactSupport (mollV n W) := by
    unfold mollV
    exact hρc.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hWc
  -- step 1: the un-mollified pair, tested against `Δ (mollV n W)`, pairs to zero
  have hWeyl := Work.FTS.PressureOn.Weyl.dpair_laplaceTraceVec_eq_zero q Φ hq hΦ hdiv hcurl
    (mollV n W) hWVs hWVc
  -- step 2: the pairing is invariant under the mollification
  have hconv : Dpair q Φ (mollV n (laplaceTraceVec W))
      = Dpair (moll n q) (mollV n Φ) (laplaceTraceVec W) :=
    Dpair_convolution q Φ (rho n) (laplaceTraceVec W) hρ hρc hρeven hΔs hΔc hq hΦ
  -- step 3: the Laplacian commutes with the convolution
  have hcomm : mollV n (laplaceTraceVec W) = laplaceTraceVec (mollV n W) :=
    Auxiliary.convolution_laplaceTraceVec_comm (rho n) W hρ hρc hW
  have hkey : Dpair (moll n q) (mollV n Φ) (laplaceTraceVec W) = 0 := by
    rw [← hconv, hcomm]
    exact hWeyl
  -- step 4: expand the pairing by integration by parts
  have hms : ∀ m : ℕ, ContDiff ℝ m (moll n q) := MollSB.contDiff_moll n q hq
  have hIBP := Auxiliary.integral_mul_div_eq_neg_inner_gradient (moll n q) (laplaceTraceVec W)
    hms hΔs hΔc
  have hint1 : Integrable (fun x => inner ℝ (mollV n Φ x) (laplaceTraceVec W x)) :=
    Continuous.integrable_of_hasCompactSupport
      (((MollSB.contDiff_mollV n Φ hΦ 0).continuous).inner (hΔs 0).continuous)
      (HasCompactSupport.intro hΔc (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_right]))
  have hint2 : Integrable (fun x => inner ℝ (gradient (moll n q) x) (laplaceTraceVec W x)) := by
    have h1 : (fun x => inner ℝ (gradient (moll n q) x) (laplaceTraceVec W x))
        = fun x => (fderiv ℝ (moll n q) x) (laplaceTraceVec W x) := by
      funext x
      rw [inner_gradient_left]
    rw [h1]
    exact Continuous.integrable_of_hasCompactSupport
      (((hms 1).continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk (hΔs 0).continuous))
      (HasCompactSupport.intro hΔc (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx, map_zero]))
  have hD : Dpair (moll n q) (mollV n Φ) (laplaceTraceVec W)
      = ∫ x, inner ℝ (mollV n Φ x - gradient (moll n q) x) (laplaceTraceVec W x) := by
    rw [Dpair, hIBP]
    rw [show (fun x => inner ℝ (mollV n Φ x - gradient (moll n q) x) (laplaceTraceVec W x))
        = fun x => inner ℝ (mollV n Φ x) (laplaceTraceVec W x)
            - inner ℝ (gradient (moll n q) x) (laplaceTraceVec W x) from
      funext fun x => inner_sub_left _ _ _]
    rw [integral_sub hint1 hint2]
    ring
  rw [← hD]
  exact hkey

end Work.FTS.PressureOn.MollAux
