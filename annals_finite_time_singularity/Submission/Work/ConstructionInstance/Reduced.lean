/-
# `Work.ConstructionInstance.Reduced` — **every field about the vorticity, derived**

Given the profile/modulation data `D : ProfileData α` (`ProfileData.lean`), the vorticity of the
constructed solution is the *definition*

  `solVort D x t = λ̄(t)⁻¹·χ(ρ(x)/L)·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)`,   `p = profExp α = 3α`,

and **every** field of the input package that is a statement about it is a theorem:

| interface field | theorem here | derived from |
|---|---|---|
| the perturbation bound `|g| ≤ Cg` | `bdd_g` | `abs_le_of_linf_H2` + the `ℋ²`-bound `hCgbig` |
| `hSupp` (support `B(0,R)`, any `R ≥ 2L`) | `solVort_supp` | the cut-off's support |
| `hBdd` (`λ̄(t)‖ω(x,t)‖ ≤ M`) | `solVort_bdd` | `selfSimVort_bdd` + `hMprof` |
| `hBddDt` (`λ̄(t)²‖∂ₜω(x,t)‖ ≤ M₁`) | `solVort_bddDt` | `bddDt_selfSimVort` + `hM₁big` |
| `hansatz` (`St5`) | `solVort_hansatz` | `exists_omegaSz_low_radius` + the cut-off transparency `(2T)^{1/p} ≤ L` |
| `hDivω` | `solVort_div` | `div_selfSimVort` (the `Cyl` dictionary) |
| `hωcont` | `solVort_cont` | `continuousOn_selfSimVort` |
| `hTh` (time-Hölder) | `solVort_timeHolder` | `timeHolderOnBall_selfSimVort` |

The time-Hölder field is delivered in its **strip form** (`∀ S, 0 < S → S + 1 < T → ∃ H, …`): by
`not_timeHolderOnBall_window` (finding E) no uniform-in-`t` constant on a window straddling `T` can
coexist with `St5`, because the vorticity itself blows up like `1/λ̄(t)`; on every strip
`window S = [-1, S+1]`, `S + 1 < T`, it is Lipschitz in `t` with the constant
`K(20p + Cg + Cg')/m(S)²`, `m(S) = min_{window S} λ̄ > 0`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.ProfileData
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.abs_le_of_linf_H2
import Submission.Work.ConstructionInstance.bddDt_selfSimVort
import Submission.Work.ConstructionInstance.div_selfSimVort
import Submission.Work.ConstructionInstance.continuousOn_selfSimVort
import Submission.Work.ConstructionInstance.exists_omegaSz_low_radius
import Submission.Work.ConstructionInstance.timeHolderOnBall_selfSimVort

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The vorticity of the constructed solution**, as a *definition* from the profile/modulation
data: `ω(x,t) = λ̄(t)⁻¹·χ(ρ(x)/L)·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)`. -/
def solVort {α : NNReal} (D : ProfileData α) : R3 → ℝ → R3 :=
  selfSimVort (profExp α) D.g D.L D.lam

theorem solVort_apply {α : NNReal} (D : ProfileData α) (x : R3) (t : ℝ) :
    solVort D x t = (D.lam t)⁻¹ •
      (Work.Stability.chi (Work.Cyl.rho x / D.L) •
        omegaSz (profExp α) D.g (Work.Cyl.rho x ^ profExp α / D.lam t) x) :=
  rfl

/-- **The datum identity (finding G)**: with the design's normalisation `λ̄(0) = 1`, the ansatz at
`t = 0` is exactly the `St1` cut-off datum, `solVort P · 0 = ω₀ = χ(ρ/L)·omegaS p g`.  This is the
consistency condition that ties the pointwise ansatz to the datum of the maximal solution; without
`hlam0` the two differ and the interface would be inconsistent. -/
theorem solVort_zero_eq_cutDatum {α : NNReal} (D : ProfileData α) :
    ∀ x : R3, solVort D x 0 = omega₀ (profExp α) D.g D.L x := by
  intro x
  rw [solVort_apply, D.hlam0, omega₀_apply, omegaS_eq_omegaSz, inv_one, one_smul,
    div_one]

/-- **The perturbation bound**: `|g| ≤ Cg` follows from the `ℋ²`-bound of the construction
(`abs_le_of_linf_H2`). -/
theorem bdd_g {α : NNReal} (D : ProfileData α) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |D.g z θ| ≤ D.Cg := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro z θ hz hθ
  exact le_trans
    (abs_le_of_linf_H2 hp hp1 D.hsmooth D.hvt D.hdec D.hmem z θ hz hθ) D.hCgbig

/-- **`hSupp`**: the cut-off makes the vorticity vanish outside `B(0,2L) ⊆ B(0,R)`. -/
theorem solVort_supp {α : NNReal} (D : ProfileData α) :
    ∀ t : ℝ, ∀ y : R3, solVort D y t ≠ 0 → y ∈ Metric.closedBall 0 D.R :=
  selfSimVort_support D.hL D.hRbig

/-- **`hBdd`**: `λ̄(t)·‖ω(x,t)‖ ≤ M`. -/
theorem solVort_bdd {α : NNReal} (D : ProfileData α) :
    ∀ t ∈ preWindow D.T, ∀ y : R3, D.lam t * ‖solVort D y t‖ ≤ D.M := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro t ht y
  exact le_trans (selfSimVort_bdd hp hp1 D.hCg (bdd_g D) D.hL (D.hlam t ht) y) D.hMprof

/-- **`hBddDt`**: `λ̄(t)²·‖∂ₜω(x,t)‖ ≤ M₁`. -/
theorem solVort_bddDt {α : NNReal} (D : ProfileData α) :
    ∀ t ∈ preWindow D.T, ∀ y : R3,
      (D.lam t) ^ 2 * ‖timeDeriv (solVort D) y t‖ ≤ D.M₁ := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro t ht y
  exact le_trans
    (bddDt_selfSimVort hp hp1 (bdd_g D) D.hg2 D.hgdiff D.hK D.hlam D.hlamdif D.hlamd ht y)
    D.hM₁big

/-- **`hansatz` (`St5`)**: at every `t ∈ [0,T)` there is a point where
`λ̄(t)·‖ω(x,t)‖ ≥ c₀star α · α`.  The witness is the maximising profile scale `z = 1`; the
cut-off is transparent there because `λ̄(t)^{1/p} < (2T)^{1/p} ≤ L`. -/
theorem solVort_hansatz {α : NNReal} (D : ProfileData α) :
    ∀ t ∈ Set.Ico 0 D.T, ∃ x : R3,
      c₀star α * (α : ℝ) ≤ D.lam t * ‖solVort D x t‖ := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro t ht
  have htpre : t ∈ preWindow D.T := ⟨by linarith [ht.1], ht.2⟩
  have hlt : 0 < D.lam t := D.hlam t htpre
  have hle2 : D.lam t ≤ 2 * D.T := by
    have h := D.hlam_le t ht
    linarith [h, ht.1, D.hT]
  have hsL : (D.lam t) ^ (1 / profExp α) ≤ D.L := by
    have h1 : 0 < 1 / profExp α := by positivity
    calc (D.lam t) ^ (1 / profExp α) ≤ (2 * D.T) ^ (1 / profExp α) :=
          Real.rpow_le_rpow hlt.le hle2 h1.le
      _ ≤ D.L := D.hLbig
  obtain ⟨x, hxρ, hx⟩ := exists_omegaSz_low_radius hp hp1 (bdd_g D) D.hsmall hlt hsL
  refine ⟨x, ?_⟩
  have hchi : Work.Stability.chi (Work.Cyl.rho x / D.L) = 1 := by
    refine Work.Stability.chi_eq_one ?_
    rw [abs_of_nonneg (div_nonneg (Work.Cyl.rho_nonneg x) D.hL.le), div_le_one D.hL]
    exact hxρ
  have heq : D.lam t * ‖solVort D x t‖
      = ‖omegaSz (profExp α) D.g (Work.Cyl.rho x ^ profExp α / D.lam t) x‖ := by
    rw [solVort_apply, mul_norm_inv_smul hlt, hchi, one_smul]
  rw [heq]
  have hc : c₀star α * (α : ℝ)
      = profExp α * Work.Spaces.Gam (profExp α) (Real.pi / 4)
          / (4 * Work.Spaces.c (profExp α)) := by
    rw [c₀star, profExp]; ring
  rw [hc]
  exact hx

/-- **`hDivω`**: the vorticity is the divergence-free swirl field of the `Cyl` dictionary. -/
theorem solVort_div {α : NNReal} (D : ProfileData α) :
    ∀ t ∈ preWindow D.T, FiniteTimeSingularity.div (solVort D · t) = 0 := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro t ht
  funext x
  exact div_selfSimVort hp hp1 D.hvt D.hsmooth D.hL (D.hlam t ht) x

/-- **`hωcont`**: the vorticity is continuous on the core. -/
theorem solVort_cont {α : NNReal} (D : ProfileData α) :
    ContinuousOn (Function.uncurry (solVort D))
      (Work.StabilityFar.coreRegion (D.R + 1) ×ˢ preWindow D.T) := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  exact continuousOn_selfSimVort hp hp1 D.hvt D.hquad0 D.hsmooth D.hL D.hlam D.hlamdif
    (R := D.R + 1) (by linarith [D.hR])

/-- **`hTh` in strip form**: on every strip `window S`, `0 < S`, `S + 1 < T`, the vorticity is
`α`-Hölder in time on the support ball, with a strip-dependent constant. -/
theorem solVort_timeHolder {α : NNReal} (D : ProfileData α) :
    ∀ S : ℝ, 0 < S → S + 1 < D.T → ∃ H : ℝ, 0 ≤ H ∧
      Work.StabilityFar.TimeHolderOnBall (α : ℝ) (solVort D) D.R S H := by
  have hp : 0 < profExp α := profExp_pos D.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [D.hα13]
  intro S hS hST
  have h := timeHolderOnBall_selfSimVort (p := profExp α) hp hp1 (bdd_g D) D.hg2 D.hgdiff
    (L := D.L) (lam := D.lam) (T := D.T) D.hK D.hlam D.hlamdif D.hlamd (R := D.R) D.hR S hS hST
  simpa only [solVort, profExp_div_three] using h

end Work.ConstructionInstance
