/-
# `Work.FTS.Top.Rescale.Defs` — the time-only Euler rescaling

Node **N0** of the lead's audit (`FTS_AUDIT_LEAD.md` §4) for the paper

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887,

replaces the hypothesis `Work.StabilityFar.EulerScalingToUnit` (a *vacuous* interface, see the
audit §2.2/§3 and the docstring of `Work.SolutionDelivery.Scaling.Defs`) by a proved theorem that
moves a blow-up time `T` to the physical time `1`.

The scaling used here is the **time-only** Euler rescaling

  `u₁(x,t) = T · u(x, T·t)`,   `p₁(x,t) = T² · p(x, T·t)`.

It is a symmetry of the incompressible Euler equation, and it is the one that is convenient in
Lean: the *space* variable is untouched, so no spatial chain rule is needed.  (The classical
`u ↦ λ u(λ·, λ²·)`, used on paper, is also a symmetry; the difference is a pure `u`-scaling, which
we could equally well have used.  See the module `Work.FTS.Top.Rescale.Operators` for the
analytic laws and `Work.FTS.Top.Rescale.Blowup` for `blowupAt_one_of_blowupAt`.)

Contents of this file:

* `timeCLM c : (ℝ³ × ℝ) →L[ℝ] (ℝ³ × ℝ)`, the linear map `(x,t) ↦ (x, c·t)`;
* `smulCLM c : ℝ³ →L[ℝ] ℝ³`, the linear map `y ↦ c • y`;
* `timeScale c u` and `timeScaleP c p`, the rescaled velocity and pressure;
* the two structural identities `timeScale_uncurry`, `timeScaleP_uncurry`, which exhibit the
  rescaled spacetime field as a continuous-linear reparametrisation of the original one.  These are
  what lets the strip regularity (`IsContDiffHolderOn`) be transferred by the generic
  reparametrisation lemma `Work.SolutionDelivery.Scaling.isContDiffHolderOn_comp_clm`.
-/
import Submission.Work.FTS.Top.Defs
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.PerfectSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-! ## The two linear maps -/

/-- The time rescaling `(x,t) ↦ (x, c·t)` of spacetime, as a continuous linear map. -/
def timeCLM (c : ℝ) : (R3 × ℝ) →L[ℝ] (R3 × ℝ) :=
  (ContinuousLinearMap.fst ℝ R3 ℝ).prod (c • ContinuousLinearMap.snd ℝ R3 ℝ)

@[simp] theorem timeCLM_apply (c : ℝ) (z : R3 × ℝ) : timeCLM c z = (z.1, c * z.2) := rfl

/-- The scalar multiplication `y ↦ c • y` on the values, as a continuous linear map. -/
def smulCLM (c : ℝ) : R3 →L[ℝ] R3 := c • ContinuousLinearMap.id ℝ R3

@[simp] theorem smulCLM_apply (c : ℝ) (y : R3) : smulCLM c y = c • y := rfl

/-! ## The rescaled fields -/

/-- **The time-rescaled velocity**: `u₁(x,t) = c·u(x, c·t)`. -/
def timeScale (c : ℝ) (u : R3 → ℝ → R3) : R3 → ℝ → R3 := fun x t => c • u x (c * t)

@[simp] theorem timeScale_apply (c : ℝ) (u : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    timeScale c u x t = c • u x (c * t) := rfl

/-- **The pressure of the time-rescaled solution**: `p₁(x,t) = c²·p(x, c·t)` (the factor `c²` is
what makes `∂ₜu₁ + (u₁·∇)u₁ + ∇p₁ = 0`). -/
def timeScaleP (c : ℝ) (p : R3 → ℝ → ℝ) : R3 → ℝ → ℝ := fun x t => c ^ 2 * p x (c * t)

@[simp] theorem timeScaleP_apply (c : ℝ) (p : R3 → ℝ → ℝ) (x : R3) (t : ℝ) :
    timeScaleP c p x t = c ^ 2 * p x (c * t) := rfl

/-! ## The structural identities

`timeScale c u = smulCLM c ∘ u.uncurry ∘ timeCLM c` and
`timeScaleP c p = (c² ·) ∘ p.uncurry ∘ timeCLM c`: this is exactly the shape of the generic
reparametrisation lemma `Work.SolutionDelivery.Scaling.isContDiffHolderOn_comp_clm`, so the strip
`C^{1,α}` regularity transfers without any new chain rule. -/

theorem timeScale_uncurry (c : ℝ) (u : R3 → ℝ → R3) :
    (timeScale c u).uncurry = fun z : R3 × ℝ => smulCLM c (u.uncurry (timeCLM c z)) := rfl

theorem timeScaleP_uncurry (c : ℝ) (p : R3 → ℝ → ℝ) :
    (timeScaleP c p).uncurry = fun z : R3 × ℝ => c ^ 2 * p.uncurry (timeCLM c z) := rfl

/-- The strip `ℝ³ × [0,S]` is carried into `ℝ³ × [0, c·S]` by `timeCLM c` when `c ≥ 0`. -/
theorem mapsTo_timeCLM_Icc {c : ℝ} (hc : 0 ≤ c) (S : ℝ) :
    Set.MapsTo (timeCLM c) (Set.univ ×ˢ Set.Icc (0 : ℝ) S)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) (c * S)) := by
  rintro ⟨x, t⟩ ⟨-, ht⟩
  simp only [Set.mem_prod, Set.mem_univ, true_and, timeCLM_apply, Set.mem_Icc] at ht ⊢
  exact ⟨mul_nonneg hc ht.1, mul_le_mul_of_nonneg_left ht.2 hc⟩

/-- The half-open strip `ℝ³ × [0,S)` is carried into `ℝ³ × [0, c·S)` by `timeCLM c` when
`c > 0`. -/
theorem mapsTo_timeCLM_Ico {c : ℝ} (hc : 0 < c) (S : ℝ) :
    Set.MapsTo (timeCLM c) (Set.univ ×ˢ Set.Ico (0 : ℝ) S)
      (Set.univ ×ˢ Set.Ico (0 : ℝ) (c * S)) := by
  rintro ⟨x, t⟩ ⟨-, ht⟩
  simp only [Set.mem_prod, Set.mem_univ, true_and, timeCLM_apply, Set.mem_Ico] at ht ⊢
  exact ⟨mul_nonneg hc.le ht.1, mul_lt_mul_of_pos_left ht.2 hc⟩

/-- Every point of the strip `ℝ³ × [0,S]` with `S > 0` is a point of unique differentiability of
the strip (the spatial factor is all of `ℝ³`, and `Icc 0 S` has nonempty interior). -/
theorem uniqueDiffWithinAt_prod_Icc {S : ℝ} (hS : 0 < S) :
    ∀ z ∈ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)),
      UniqueDiffWithinAt ℝ (Set.univ ×ˢ Set.Icc (0 : ℝ) S) z := by
  rintro ⟨x, t⟩ ⟨-, ht⟩
  exact UniqueDiffWithinAt.prod uniqueDiffWithinAt_univ ((uniqueDiffOn_Icc hS) t ht)

/-! ## Scaling of the fixed differential operators on the values

The time rescaling `timeScale c u = fun x t => c • u x (c·t)` scales the *values* of the field by
`c` and does not touch the space variable.  The three operators of `ChallengeDeps` that are linear
in the field therefore obey unconditional scaling laws (`fderiv_const_smul_field` is
hypothesis-free in Mathlib), which is what makes the Euler equation, the divergence-freeness and
the vorticity decay of the rescaled solution immediate.
-/

/-- The pointwise form of Mathlib's `fderiv_const_smul_field`. -/
theorem fderiv_const_smul_apply (c : ℝ) (v : R3 → R3) (x : R3) :
    fderiv ℝ (fun y => c • v y) x = c • fderiv ℝ v x :=
  congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := v) c) x

/-- **The divergence of a scalar multiple of a field**: `div (c • v) = c · div v`. -/
theorem div_const_smul (c : ℝ) (v : R3 → R3) (x : R3) :
    div (fun y => c • v y) x = c * div v x := by
  simp only [div, fderiv_const_smul_apply, ContinuousLinearMap.toLinearMap_smul, map_smul,
    smul_eq_mul]

/-- **The vorticity of a scalar multiple of a field**: `∇×(c v) = c ∇×v`. -/
theorem vorticity_const_smul (c : ℝ) (v : R3 → R3) :
    vorticity (fun y => c • v y) = fun x => c • vorticity v x := by
  funext x
  have hderiv : fderiv ℝ (fun y => c • v y) x = c • fderiv ℝ v x := fderiv_const_smul_apply c v x
  simp only [FiniteTimeSingularity.vorticity]
  rw [hderiv]
  have hterm : ∀ i : Fin 3,
      crossProduct (FiniteTimeSingularity.e i) ((c • fderiv ℝ v x) (FiniteTimeSingularity.e i))
        = c • crossProduct (FiniteTimeSingularity.e i) (fderiv ℝ v x (FiniteTimeSingularity.e i)) :=
    fun i => by rw [ContinuousLinearMap.smul_apply, WithLp.ofLp_smul, map_smul]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [WithLp.toLp_sum]
  simp only [WithLp.toLp_smul]
  rw [← Finset.smul_sum, ← WithLp.toLp_sum]

/-! ## The scaling laws of the four operators of `ChallengeDeps`

`timeScale c u · t` is literally `fun y => c • (u · (c·t)) y`, so all the *space*-only operators
which are linear in the field are immediate from the value-scaling lemmas above. -/

/-- **`fderiv` of the rescaled slice**: `D_x u₁(·,t) = c · D_xu(·,c t)`. -/
theorem fderiv_timeScale (c : ℝ) (u : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    fderiv ℝ (timeScale c u · t) x = c • fderiv ℝ (u · (c * t)) x :=
  fderiv_const_smul_apply c (u · (c * t)) x

/-- **`div` of the rescaled slice**: `div u₁(·,t) = c · div u(·,c t)`. -/
theorem div_timeScale (c : ℝ) (u : R3 → ℝ → R3) (t : ℝ) :
    div (timeScale c u · t) = fun x => c * div (u · (c * t)) x := by
  funext x
  exact div_const_smul c (u · (c * t)) x

/-- **`vorticity` of the rescaled slice**: `∇×u₁(·,t) = c · (∇×u)(·,c t)`.  (No factor `c²`: the
space variable is *not* rescaled.) -/
theorem vorticity_timeScale (c : ℝ) (u : R3 → ℝ → R3) (t : ℝ) :
    vorticity (timeScale c u · t) = fun x => c • vorticity (u · (c * t)) x :=
  vorticity_const_smul c (u · (c * t))

/-- The convection term of the time-rescaled field: both the field and its derivative are scaled
by `c`, so the product scales by `c²`. -/
theorem directionalDeriv_timeScale (c : ℝ) (u : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    directionalDeriv (timeScale c u) (timeScale c u) x t
      = (c * c) • directionalDeriv u u x (c * t) := by
  have h1 : directionalDeriv (timeScale c u) (timeScale c u) x t
      = (c • fderiv ℝ (u · (c * t)) x) (timeScale c u x t) := by
    rw [directionalDeriv, fderiv_timeScale]
  rw [h1]
  show (c • fderiv ℝ (u · (c * t)) x) (c • u x (c * t))
      = (c * c) • fderiv ℝ (u · (c * t)) x (u x (c * t))
  rw [ContinuousLinearMap.smul_apply, map_smul, smul_smul]

/-- **`timeDeriv` of the rescaled field**: `∂ₜu₁ = c² · (∂ₜu)(·,c t)` (one factor `c` from the
value scaling and one from the chain rule for `t ↦ c·t`). -/
theorem timeDeriv_timeScale (c : ℝ) (u : R3 → ℝ → R3) (x : R3) (t : ℝ)
    (hd : DifferentiableAt ℝ (u x) (c * t)) :
    timeDeriv (timeScale c u) x t = (c * c) • timeDeriv u x (c * t) := by
  have hd1 : DifferentiableAt ℝ (fun s : ℝ => u x (c * s)) t :=
    hd.comp t (hasDerivAt_const_mul c).differentiableAt
  have h2 : timeDeriv (timeScale c u) x t = c • deriv (fun s : ℝ => u x (c * s)) t :=
    deriv_const_smul c hd1
  rw [h2, deriv_comp_mul_left c (u x) t, smul_smul]
  rfl

end Work.FTS.Top
