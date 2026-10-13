/-
# The GALERKIN area: the compactness step (audit §4 N6, step 5)

The extraction of a convergent subsequence from the uniformly bounded Galerkin families is the field
`DynInputs.hCompact`; the present module contains the *provable* analytical layer around it:

* `convLocUnif_point`: locally uniform convergence on the fake-time slab gives pointwise convergence;
* `sq_le_HkSq_two_of_mem_four`, `linf_of_HkNorm_four`: a uniform `ℋ⁴`-bound gives a *pointwise*
  bound, via the paper's `Linf_H2` corollary (`Hilbert/sq_le_HkSq_two.lean`) and the inclusion
  `ℋ⁴ ⊆ ℋ²` (`Coercivity.HkMem_mono`, `Coercivity.HkSq_mono`).  This is the quantitative input that
  makes the Arzelà–Ascoli step meaningful;
* `gdot_pointwise_bound`, `tendsto_slice_of_derivBound`: the paper's conclusion that the fake-time
  family has a limit as `τ → ∞`, from the uniform `ℋ³`-bound `|∂_τ g|_{ℋ³} ≤ K exp(-cτ)` on the
  fake-time derivative (the pointwise version of
  `Compactness/tendsto_of_norm_derivWithin_le.lean`).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Galerkin.Basic
import Submission.Work.FTS.Galerkin.Compactness.convLocUnif_convPoint
import Submission.Work.FTS.Galerkin.Compactness.exists_strictMono_forall_tendsto_of_bounded
import Submission.Work.FTS.Galerkin.Compactness.tendsto_of_norm_derivWithin_le
import Submission.Work.FTS.Galerkin.Hilbert.sq_le_HkSq_two
import Submission.Work.FTS.Galerkin.GalerkinODE
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.Coercivity.HkSq_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-- Locally uniform convergence implies pointwise convergence (the form in which the compactness
output is consumed by the passage to the limit). -/
theorem convLocUnif_point {G : ℕ → Fam} {g : Fam} (h : ConvLocUnif G g) : ConvPoint G g :=
  Compactness.convLocUnif_convPoint h

/-- The constant `100/(γ-1)` of the paper's pointwise bound is nonnegative for `0 < α`. -/
theorem linf_const_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ 100 / (Spaces.gam α - 1) := by
  have h : 0 < Spaces.gam α - 1 := by rw [Spaces.gam_sub_one]; linarith
  positivity

/-- **A uniform `ℋ⁴`-bound gives a pointwise bound at order `2`**: for `f` in `ℋ⁴` (and smooth,
vanishing on the angular boundaries and decaying at `∞`), the pointwise square is controlled by the
`ℋ⁴`-norm squared, through the chain `ℋ⁴ ⊆ ℋ²` and the paper's `Linf_H2`. -/
theorem sq_le_HkSq_two_of_mem_four {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Spaces.SmoothNbhd f) (hv : Spaces.VanishTheta f) (hd : Spaces.DecayInZ 2 f)
    (hm : Spaces.HkMem α 4 f) (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    (f z θ) ^ 2 ≤ 100 / (Spaces.gam α - 1) * Spaces.HkSq α 4 f := by
  have hm3 : Spaces.HkMem α 3 f := Coercivity.HkMem_mono α 3 hsm hm
  have hm2 : Spaces.HkMem α 2 f := Coercivity.HkMem_mono α 2 hsm hm3
  have h1 : (f z θ) ^ 2 ≤ 100 / (Spaces.gam α - 1) * Spaces.HkSq α 2 f :=
    Hilbert.sq_le_HkSq_two hα hα1 hsm hv hd hm2 hz hθ
  have h2 : Spaces.HkSq α 2 f ≤ Spaces.HkSq α 4 f :=
    le_trans (Coercivity.HkSq_mono α 2 hm3) (Coercivity.HkSq_mono α 3 hm)
  have h3 := linf_const_nonneg hα
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

/-- The pointwise bound in terms of a *given* bound `B` for the `ℋ⁴`-norm: a uniform `ℋ⁴`-bound
`|f|_{ℋ⁴} ≤ B` gives `(f z θ)² ≤ 100/(γ-1) · B²` at every point of the closed quadrant. -/
theorem linf_of_HkNorm_four {α z θ B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hB0 : 0 ≤ B) {f : Fn}
    (hsm : Spaces.SmoothNbhd f) (hv : Spaces.VanishTheta f) (hd : Spaces.DecayInZ 2 f)
    (hm : Spaces.HkMem α 4 f) (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ)
    (hB : Spaces.HkNorm α 4 f ≤ B) :
    (f z θ) ^ 2 ≤ 100 / (Spaces.gam α - 1) * B ^ 2 := by
  have h1 := sq_le_HkSq_two_of_mem_four hα hα1 hsm hv hd hm hz hθ
  have h2 : Spaces.HkSq α 4 f ≤ B ^ 2 := by
    have h3 : Spaces.HkSq α 4 f = (Spaces.HkNorm α 4 f) ^ 2 := by
      rw [Spaces.HkNorm, Real.sq_sqrt (Spaces.HkSq_nonneg α 4 f)]
    rw [h3]
    exact sq_le_sq' (by linarith [Spaces.HkNorm_nonneg α 4 f]) hB
  have h4 := linf_const_nonneg hα
  linarith [mul_le_mul_of_nonneg_left h2 h4]

/-- **The pointwise decay of the fake-time derivative from its uniform `ℋ³`-bound**: if
`|∂_τG(τ)|_{ℋ³} ≤ K exp(-cτ)` for all `τ ≥ 0`, then at every point of the closed quadrant
`|∂_τG(τ)(z,θ)| ≤ √(100/(γ-1)) · K · exp(-cτ)`.  This is the quantitative form of the paper's
`|∂_τg|_{ℋ³} ≤ Cα² exp(-cτ)` used in the convergence of the fake-time family. -/
theorem gdot_pointwise_bound {α K c z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {G : Fam} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ)
    (hsm : ∀ τ, 0 ≤ τ → Spaces.SmoothNbhd (gdot G τ))
    (hvt : ∀ τ, 0 ≤ τ → Spaces.VanishTheta (gdot G τ))
    (hd : ∀ τ, 0 ≤ τ → Spaces.DecayInZ 2 (gdot G τ))
    (hm : ∀ τ, 0 ≤ τ → Spaces.HkMem α 3 (gdot G τ))
    (hbd : ∀ τ, 0 ≤ τ → Spaces.HkNorm α 3 (gdot G τ) ≤ K * Real.exp (-(c * τ))) :
    ∀ τ, 0 ≤ τ → ‖gdot G τ z θ‖ ≤ Real.sqrt (100 / (Spaces.gam α - 1)) * K * Real.exp (-(c * τ)) := by
  intro τ hτ
  have hm3 := hm τ hτ
  have hm2 : Spaces.HkMem α 2 (gdot G τ) :=
    Coercivity.HkMem_mono α 2 (hsm τ hτ) hm3
  have h1 : (gdot G τ z θ) ^ 2 ≤ 100 / (Spaces.gam α - 1) * Spaces.HkSq α 2 (gdot G τ) :=
    Hilbert.sq_le_HkSq_two hα hα1 (hsm τ hτ) (hvt τ hτ) (hd τ hτ) hm2 hz hθ
  have h2 : Spaces.HkSq α 2 (gdot G τ) ≤ Spaces.HkSq α 3 (gdot G τ) :=
    Coercivity.HkSq_mono α 2 hm3
  have h3 : Spaces.HkSq α 3 (gdot G τ) = (Spaces.HkNorm α 3 (gdot G τ)) ^ 2 := by
    rw [Spaces.HkNorm, Real.sq_sqrt (Spaces.HkSq_nonneg α 3 (gdot G τ))]
  have hb := hbd τ hτ
  have hexp : 0 ≤ K * Real.exp (-(c * τ)) := mul_nonneg hK (Real.exp_nonneg _)
  have h4 : (Spaces.HkNorm α 3 (gdot G τ)) ^ 2 ≤ (K * Real.exp (-(c * τ))) ^ 2 :=
    sq_le_sq' (by linarith [Spaces.HkNorm_nonneg α 3 (gdot G τ)]) hb
  have h5 : (gdot G τ z θ) ^ 2 ≤ 100 / (Spaces.gam α - 1) * (K * Real.exp (-(c * τ))) ^ 2 := by
    have h6 := mul_le_mul_of_nonneg_left h2 (linf_const_nonneg hα)
    rw [h3] at h6
    have h7 := mul_le_mul_of_nonneg_left h4 (linf_const_nonneg hα)
    linarith
  have h8 : ‖gdot G τ z θ‖ = Real.sqrt ((gdot G τ z θ) ^ 2) := by
    rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
  rw [h8]
  calc Real.sqrt ((gdot G τ z θ) ^ 2)
      ≤ Real.sqrt (100 / (Spaces.gam α - 1) * (K * Real.exp (-(c * τ))) ^ 2) :=
        Real.sqrt_le_sqrt h5
    _ = Real.sqrt (100 / (Spaces.gam α - 1)) * Real.sqrt ((K * Real.exp (-(c * τ))) ^ 2) := by
        rw [Real.sqrt_mul (linf_const_nonneg hα)]
    _ = Real.sqrt (100 / (Spaces.gam α - 1)) * K * Real.exp (-(c * τ)) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hexp]; ring

/-- **The fake-time family converges at `+∞`** (the paper's "`g` has a unique limit as
`τ → ∞`"): if the fake-time derivative of the family is differentiable in `τ` with the uniform
`ℋ³`-bound `|∂_τG(τ)|_{ℋ³} ≤ K exp(-cτ)` (`c > 0`), then at every point of the closed quadrant the
curve `τ ↦ G(z,θ,τ)` converges as `τ → ∞`. -/
theorem tendsto_slice_of_derivBound {α K c : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hc : 0 < c) {G : Fam}
    (hder : ∀ z θ τ, 0 ≤ τ →
      HasDerivWithinAt (fun s => G z θ s) (gdot G τ z θ) (Set.Ici 0) τ)
    (hsm : ∀ τ, 0 ≤ τ → Spaces.SmoothNbhd (gdot G τ))
    (hvt : ∀ τ, 0 ≤ τ → Spaces.VanishTheta (gdot G τ))
    (hd : ∀ τ, 0 ≤ τ → Spaces.DecayInZ 2 (gdot G τ))
    (hm : ∀ τ, 0 ≤ τ → Spaces.HkMem α 3 (gdot G τ))
    (hbd : ∀ τ, 0 ≤ τ → Spaces.HkNorm α 3 (gdot G τ) ≤ K * Real.exp (-(c * τ))) :
    ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      ∃ L : ℝ, Tendsto (fun τ => G z θ τ) atTop (𝓝 L) := by
  intro z hz θ hθ
  refine Compactness.tendsto_of_norm_derivWithin_le (fun τ => G z θ τ) (fun τ => gdot G τ z θ)
    (Real.sqrt (100 / (Spaces.gam α - 1)) * K) c hc (hder z θ) ?_
  exact gdot_pointwise_bound hα hα1 hK hz hθ hsm hvt hd hm hbd

/-- **Diagonal extraction for a family of profiles.**  Let `e : ℕ → ℝ × ℝ × ℝ` enumerate a
countable set of points of the fake-time slab.  If the values of a sequence of profiles at those
points are uniformly bounded, then a subsequence converges at every one of them.  This is the
combinatorial step of the compactness input `DynInputs.hCompact`; combined with the equicontinuity
coming from a uniform `ℋ⁴`-bound (`linf_of_HkNorm_four`) it upgrades to convergence on a dense
countable set of the slab, and hence (by continuity) to locally uniform convergence. -/
theorem exists_subseq_tendsto_values {G : ℕ → Fam} {e : ℕ → ℝ × ℝ × ℝ} {C : ℝ}
    (h : ∀ n k : ℕ, |G n (e k).1 (e k).2.1 (e k).2.2| ≤ C) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k : ℕ, ∃ L : ℝ,
      Tendsto (fun n => G (ψ n) (e k).1 (e k).2.1 (e k).2.2) atTop (𝓝 L) :=
  Compactness.exists_strictMono_forall_tendsto_of_bounded h

/-- **The pointwise bound on a Galerkin profile from the energy form of the a-priori estimate**:
if the coefficients of a Galerkin combination satisfy `∑ₖ cₖ² ≤ R²`, then at every point of the closed
quadrant its square is at most `100/(γ-1) R²`, by `HkNorm_galFun_le` and the paper's `Linf_H2`
(`linf_of_HkNorm_four`).  This is the quantitative content of the bundle's field `hProfileBdd`. -/
theorem profile_le_of_sq_sum_le {α z θ R : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hR : 0 ≤ R)
    {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} (hIP : IsH4Inner α IP) (hpair : IsIPOrthonormal IP φ)
    {n : ℕ} {c : Fin n → ℝ} (hadm : Coercivity.HkAdm α 4 (galFun φ c))
    (h : ∑ k : Fin n, (c k) ^ 2 ≤ R ^ 2)
    (hsm : Spaces.SmoothNbhd (galFun φ c)) (hv : Spaces.VanishTheta (galFun φ c))
    (hd : Spaces.DecayInZ 2 (galFun φ c)) (hm : Spaces.HkMem α 4 (galFun φ c))
    (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    (galFun φ c z θ) ^ 2 ≤ 100 / (Spaces.gam α - 1) * R ^ 2 :=
  linf_of_HkNorm_four hα hα1 hR hsm hv hd hm hz hθ (HkNorm_galFun_le hIP hpair hadm h hR)

end Work.FTS.Galerkin
