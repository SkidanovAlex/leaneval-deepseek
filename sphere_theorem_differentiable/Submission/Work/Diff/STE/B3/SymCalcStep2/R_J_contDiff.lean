import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.B3.BNorm_J_sub_le
import Submission.Work.Diff.STE.B3.bump_expansion_fixed
import Submission.Work.Diff.STE.B3.goodSet_smooth_noT2
import Submission.Work.Diff.STE.D.ChartData_jVec
import Submission.Work.Diff.STE.Lead.Gal.galE_J_bounded

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3, `SymCalcStep2`: the chart components of the Friedrichs mollifier are smooth

`D.J ρ ε` is the Friedrichs mollifier of the Layer-B3 vocabulary (`B3/Comp.lean`),

  `D.J ρ ε h = Σ_i R*_i (S_ε (R_i h))`,

and for a multiplier `ρ` vanishing outside the ball of radius `√2` the truncation `S_ε = STruncR ρ ε`
is a *trigonometric polynomial*: its Fourier coefficients are `ρ (ε m) · ĉ(m)`, and the hypothesis
`hρ0` on `ρ` cuts the series down to the finitely many frequencies `m` in the box `truncBox ε`
(`B3/J_finite_rank.lean`, `STruncR_eq_fintype_sum`).  Consequently `S_ε g` is smooth for *every*
`g` — a finite sum of the smooth modes `modeFun q` with constant coefficients — and no smoothness of
`g` and no bound on `ρ` is needed.

The remaining smoothness is that of the cross-chart expansion of `R_j (R*_i u)`
(`B3/bump_expansion_fixed.lean`): there is a smooth coefficient family `G` with topological support
inside the open set `goodSet` on which the chart transition `tMapFun` is smooth (`goodSet_smooth_noT2`)
and

  `(R_j (R*_i u) a b z : ℂ) = Σ_{cd} G_{cd} z · (u_{cd} (tMapFun z) : ℂ)`.

Since the components of `S_ε` are smooth (`contDiff_STruncR_of_rho0` below), so are the composed
functions `z ↦ S_ε (R_i h)_{cd} (tMapFun z)` (`Work.Diff.STE.Lead.Gal.contDiff_comp_tMapFun_noInst`)
and hence the sum.  This is the `ρ`-route to `Work.Diff.STE.Lead.R_J_contDiff`, which instead needs a
bound `‖ρ‖ ≤ 1` on the multiplier.

The hypothesis set is exactly the one of the requested statement: **no** `[T2Space M]`, no
`[I.Boundaryless]`, no compactness of `M`, and no `IsContMDiffRiemannianBundle`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3.SymCalcStep2

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The Friedrichs truncation of *any* function is smooth** when the multiplier `ρ` vanishes
outside the ball of radius `√2` of frequency space.  Indeed `STruncR_eq_fintype_sum` exhibits
`STruncR ρ ε f` as the finite real linear combination of the Fourier modes `modeFun q` attached to
the box `truncBox ε` (`B3/J_finite_rank.lean`), and each `modeFun q` is smooth.  No integrability,
periodicity or smoothness of `f` is used: the Fourier coefficients are just the (real numbers)
`scoeff ρ ε f q`. -/
lemma contDiff_STruncR_of_rho0
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (ε : ℝ) (hε : 0 < ε) (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => B3Data.STruncR ρ ε f z) := by
  have hfun : (fun z => B3Data.STruncR ρ ε f z)
      = fun z => ∑ q : QIdx (Module.finrank ℝ E) ε,
          scoeff (Module.finrank ℝ E) ρ ε f q * modeFun (Module.finrank ℝ E) q z := by
    funext z
    exact STruncR_eq_fintype_sum ρ ε hε hρ0 f z
  rw [hfun]
  exact ContDiff.sum fun q _ =>
    contDiff_const.mul (Work.Diff.STE.D.contDiff_modeFun (Module.finrank ℝ E) ε q)

/-- The truncated chart component `truncComp` is the real Friedrichs truncation `STruncR`: the
definitions differ only in the point at which the series is unfolded. -/
lemma truncComp_eq_STruncR (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (f : Bil (I := I) (M := M))
    (k : ι₀) (c d : Fin (Module.finrank ℝ E)) :
    truncComp D ρ ε f k c d = fun z => B3Data.STruncR ρ ε (D.R k f c d) z := rfl

/-- **The chart components of `J ρ ε f` are smooth**, from the finite-rank hypothesis `hρ0` on the
multiplier alone. -/
lemma R_J_contDiff_of_rho0
    (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (ε : ℝ) (hε : 0 < ε) (f : Bil (I := I) (M := M))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (D.R i (D.J ρ ε f) a b) := by
  have hJeq : D.J ρ ε f = ∑ k : ι₀, D.Rstar k (truncComp D ρ ε f k) := by
    rw [B3Data.J]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
  rw [hJeq]
  have hpt : ∀ z, D.R i (∑ k : ι₀, D.Rstar k (truncComp D ρ ε f k)) a b z
      = ∑ k : ι₀, D.R i (D.Rstar k (truncComp D ρ ε f k)) a b z := fun z => by
    simp only [B3Data.R, B3Data.mat, Finset.sum_apply, sum_apply, Finset.mul_sum]
  have hsum0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ∑ k : ι₀, D.R i (D.Rstar k (truncComp D ρ ε f k)) a b z) := by
    refine ContDiff.sum fun k _ => ?_
    obtain ⟨G, hGsm, _hGsupp, _hGcomp, hGgood, hid⟩ :=
      bump_expansion_fixed D k i a b (closure_Omega_goodSet D k i)
        ((goodSet_smooth_noT2 D k i).1)
        (fun c d => (goodSet_smooth_noT2 D k i).2.2 a b c d)
    have hsm2 : ∀ c d, ContDiff ℝ (⊤ : ℕ∞)
        (fun z => ((truncComp D ρ ε f k c d z : ℝ) : ℂ)) := fun c d => by
      have h1 : ContDiff ℝ (⊤ : ℕ∞)
          (fun z => ((B3Data.STruncR ρ ε (D.R k f c d) z : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_STruncR_of_rho0 ρ hρ0 ε hε (D.R k f c d))
      convert h1 using 1
      funext z
      simp only [truncComp_eq_STruncR]
    have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ c, ∑ d, G c d z *
        ((truncComp D ρ ε f k c d
          (Work.Diff.STE.D.tMapFun (I := I) (M := M) D k i z) : ℝ) : ℂ)) := by
      refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
      exact Work.Diff.STE.Lead.Gal.contDiff_comp_tMapFun_noInst (I := I) (M := M) D k i (G c d)
        (hGsm c d) (hGgood c d) _ (hsm2 c d)
    have hre0 : ContDiff ℝ (⊤ : ℕ∞) (⇑Complex.reCLM ∘ (fun z => ∑ c, ∑ d, G c d z *
        ((truncComp D ρ ε f k c d
          (Work.Diff.STE.D.tMapFun (I := I) (M := M) D k i z) : ℝ) : ℂ))) :=
      (Complex.reCLM.contDiff).comp hsum
    have hre : ContDiff ℝ (⊤ : ℕ∞) (fun z => (∑ c, ∑ d, G c d z *
        ((truncComp D ρ ε f k c d
          (Work.Diff.STE.D.tMapFun (I := I) (M := M) D k i z) : ℝ) : ℂ)).re) := by
      convert hre0 using 1
      funext z
      rfl
    convert hre using 1
    funext z
    have hz := hid (truncComp D ρ ε f k) z
    rw [← hz, Complex.ofReal_re]
  convert hsum0 using 1
  funext z
  exact hpt z

theorem R_J_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (ε : ℝ) (hε : 0 < ε) (f : Work.Diff.STE.Bil (I := I) (M := M))
    (hf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b)) :
    ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (D.J ρ ε f) a b) := by
  intro i a b
  exact R_J_contDiff_of_rho0 D ρ hρ0 ε hε f i a b

end Work.Diff.STE.B3.SymCalcStep2
