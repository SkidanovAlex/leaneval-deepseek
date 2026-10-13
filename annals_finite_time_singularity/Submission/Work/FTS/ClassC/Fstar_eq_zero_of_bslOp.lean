/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular moment `F_*(Ψ)` of a solution of (PolarBSL) vanishes

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible Euler
equations on `ℝ³`*, Annals of Math. **194** (2021), Step 1 of the proof of Proposition `prop:L2`
(tex 735–760): if `Ψ` solves (PolarBSL) with a *moment-free* source (`F_*(F) ≡ 0`), then `Ψ`
itself is moment free.

The argument has two halves, both isolated here:

* **the Euler ODE for `u = F_*Ψ`.**  `sin θ cos²θ` lies in the kernel of the adjoint of `L₀`
  (`Work.Elliptic.Lzero_orthogonal`), so the angular moment of the equation is
  `F_*(bslOp α Ψ) = -(α²z²)·F_*(∂_zzΨ) - α(5+α)z·F_*(∂_zΨ)` (`Fstar_bslOp_moment`);
  combined with the two weak-derivative identities `u' = F_*(∂_zΨ)` and
  `(F_*(∂_zΨ))' = F_*(∂_zzΨ)` produced by the chain rule for the moment
  (`Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open`, packaged for `∂_z` in
  `Fstar_chain_pz`), this says that `u` solves the Euler ODE `α²z²u'' + α(5+α)zu' = 0` in the
  *integrated* form, i.e. the pair `(u, v) = (F_*Ψ, F_*(∂_zΨ))` satisfies the two chains of
  `euler_weak_eq_zero_of_decay`;
* **the rigidity.**  The general solution is `u = B₁ + B₂z^{-5/α}`; decay at `+∞` kills `B₁`
  and the paper's condition `z²u → 0` at `0` kills `B₂` (`euler_weak_eq_zero_of_decay`, and the
  classical `C²` versions in `euler_ode_unique.lean`).

`Fstar_eq_zero_of_bslOp'` below is the assembly: from the vanishing of the moment of the
*equation*, the three slice-integrability facts and the two chains, it concludes
`F_*Ψ ≡ 0` on `(0,∞)`.  The hypotheses are exactly what the elliptic existence node
(`Work.FTS.PhiStar.bslOp_sol_exists`) supplies: `SmoothOpen` of `Ψ` and `∂_zΨ` gives the chains
(via `Fstar_chain_pz`), the `ℋ`-honesty of the solution's slots gives the integrability, and
`F_*(F) ≡ 0` with the equation gives `F_*(bslOp α Ψ) ≡ 0`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.ClassC.Fstar_bslOp_moment
import Submission.Work.FTS.ClassC.Fstar_chain_pz
import Submission.Work.FTS.EllipticEst.Cores.OrthCond_lambda_zero
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.FTS.ClassC.euler_weak_eq_zero_of_decay

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set MeasureTheory

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- **The angular moment of a solution of (PolarBSL) with moment-free equation vanishes.**

`u = F_*Ψ` solves the Euler ODE in the integrated form: its weak derivative is
`v = F_*(∂_zΨ)` (hypothesis `hchain0`) and `v` itself has weak derivative
`F_*(∂_zzΨ) = F_*(∂_z(∂_zΨ))` (hypothesis `hchain1`), while the moment identity
`Fstar_bslOp_moment` turns the vanishing of the moment of the equation (`hz0`) into the
pointwise relation `α²z²·F_*(∂_zzΨ) + α(5+α)z·F_*(∂_zΨ) = 0`.  Then
`euler_weak_eq_zero_of_decay` (decay at `+∞`, `z²u → 0` at `0`) gives `u ≡ 0`. -/
theorem Fstar_eq_zero_of_bslOp' {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα2 : α < 5 / 2)
    (hslice : ∀ z : ℝ, 0 < z → ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)))
    (h0 : ∀ z : ℝ, Ψ z 0 = 0) (h1 : ∀ z : ℝ, Ψ z (Real.pi / 2) = 0)
    (hz0 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) z = 0)
    (hIntA : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hIntB : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hIntL : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.Lzero Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hchain0 : ∀ s z : ℝ, 0 < s → s ≤ z →
      Work.Elliptic.Fstar Ψ z - Work.Elliptic.Fstar Ψ s
        = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r)
    (hchain1 : ∀ s z : ℝ, 0 < s → s ≤ z →
      Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z - Work.Elliptic.Fstar (Work.Spaces.pz Ψ) s
        = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.pz Ψ)) r)
    (hdec : Filter.Tendsto (Work.Elliptic.Fstar Ψ) Filter.atTop (nhds 0))
    (hzsq : Filter.Tendsto (fun z : ℝ => z ^ 2 * Work.Elliptic.Fstar Ψ z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar Ψ z = 0 := by
  -- the pointwise Euler relation `α²z²·F_*(∂_zzΨ) + α(5+α)z·F_*(∂_zΨ) = 0`
  have hode : ∀ z : ℝ, 0 < z →
      α ^ 2 * z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.pz Ψ)) z
        + α * (5 + α) * z * Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z = 0 := by
    intro z hz
    have hmom := Fstar_bslOp_moment (α := α) (Ψ := Ψ) (z := z) (hslice z hz) (h0 z) (h1 z)
      (hIntA z hz) (hIntB z hz) (hIntL z hz)
    rw [hz0 z hz] at hmom
    -- `pzIter 2 Ψ = pz (pz Ψ)`
    have hiter : Work.Spaces.pzIter 2 Ψ = Work.Spaces.pz (Work.Spaces.pz Ψ) := by
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
    rw [hiter] at hmom
    linarith [hmom]
  -- rewrite the second chain with the coefficient of the relation
  have hchain1' : ∀ s z : ℝ, 0 < s → s ≤ z →
      Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z - Work.Elliptic.Fstar (Work.Spaces.pz Ψ) s
        = ∫ r in s..z, (-(5 + α) / (α * r)) * Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r := by
    intro s z hs hsz
    rw [hchain1 s z hs hsz]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with r hr
    rw [Set.uIoc_of_le hsz] at hr
    have hrpos : 0 < r := lt_trans hs hr.1
    have h := hode r hrpos
    have h1 : Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.pz Ψ)) r
        = -(α * (5 + α) * r * Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r) / (α ^ 2 * r ^ 2) := by
      rw [eq_div_iff (by positivity)]
      linarith [h]
    rw [h1]
    field_simp
  exact euler_weak_eq_zero_of_decay hα hα2 hchain0 hchain1' hdec hzsq

/-- **The moment of the equation.**  If `bslOp α Ψ = F` on the *open* angular interval at the
radius `z`, then the two have the same angular moment at `z`: the two functions agree a.e. on
`Iθ` (they can differ only at `θ = 0` and `θ = π/2`), and a.e.-equal functions have equal
integrals.  (No measurability hypothesis is needed: `MeasureTheory.integral_congr_ae` is an
a.e.-congruence.) -/
theorem Fstar_bslOp_eq_Fstar {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (heq : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) z = Work.Elliptic.Fstar F z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  rw [MeasureTheory.ae_iff]
  have hset : {θ : ℝ | ¬ (θ ∈ Set.Icc 0 (Real.pi / 2)
      → Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ
        = F z θ * Work.Elliptic.sinCos2 θ)} ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp] at hθ
    obtain ⟨hIcc, hne⟩ := hθ
    by_contra hcon
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
    obtain ⟨h0, h1⟩ := hcon
    exact hne (by rw [heq θ (lt_of_le_of_ne hIcc.1 (Ne.symm h0))
      (lt_of_le_of_ne hIcc.2 h1)])
  refine MeasureTheory.measure_mono_null hset ?_
  have hset2 : ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [hset2]
  exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
    (MeasureTheory.measure_singleton _)

/-- **`F_*(bslOp α Ψ) ≡ 0` from a moment-free source.**  Immediate from
`Fstar_bslOp_eq_Fstar` and the vanishing of the moment of `F`; this is the `hz0` hypothesis of
`Fstar_eq_zero_of_bslOp'` in the form the elliptic existence node supplies it. -/
theorem Fstar_bslOp_eq_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hF : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) z = 0 :=
  fun z hz => by rw [Fstar_bslOp_eq_Fstar (heq z hz), hF z hz]

/-- **The moment conjunct `F_*(Ψ) ≡ 0` for a solution of (PolarBSL) with moment-free source.**

This is `Fstar_eq_zero_of_bslOp'` with the three slice-integrability hypotheses and the
vanishing of the moment of the equation *derived* rather than assumed:

* `F_*(bslOp α Ψ) ≡ 0` from `F_*(F) ≡ 0` and the equation (`Fstar_bslOp_eq_zero`);
* `∫_θ (α²z²·∂_zzΨ)·sinθcos²θ` and `∫_θ (α(5+α)z·∂_zΨ)·sinθcos²θ` are honest by the pointwise
  absorption `Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted` against the `ℋ⁰`-integrands of
  `z²∂_zzΨ` and `D_zΨ` (`Cores.integrableOn_slice_mul_sinCos2`);
* `∫_θ (Lzero Ψ z θ)·sinθcos²θ` is honest for every `C²` slice
  (`Work.Elliptic.integrableOn_Lzero_mul_sinCos2`, the antiderivative of `Lzero_orthogonal`). -/
theorem Fstar_eq_zero_of_bslOp {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα2 : α < 5 / 2)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hslice : ∀ z : ℝ, 0 < z → ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)))
    (h0 : ∀ z : ℝ, Ψ z 0 = 0) (h1 : ∀ z : ℝ, Ψ z (Real.pi / 2) = 0)
    (heq : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hF : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hmemA : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 Ψ))
    (hmemΨ : Work.Spaces.HkMem α 1 Ψ)
    (hsmd : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pz Ψ))
    (hmemd : Work.Spaces.HkMem α 1 (Work.Spaces.pz Ψ))
    (hdec : Filter.Tendsto (Work.Elliptic.Fstar Ψ) Filter.atTop (nhds 0))
    (hzsq : Filter.Tendsto (fun z : ℝ => z ^ 2 * Work.Elliptic.Fstar Ψ z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar Ψ z = 0 := by
  have hz0 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) z = 0 :=
    Fstar_bslOp_eq_zero heq hF
  -- the two weak-derivative identities of the moment, from the chain rule for `F_*`
  have hchain0 : ∀ s z : ℝ, 0 < s → s ≤ z →
      Work.Elliptic.Fstar Ψ z - Work.Elliptic.Fstar Ψ s
        = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r :=
    fun s z hs hsz => Fstar_chain_pz hsm hmemΨ hs hsz
  have hchain1 : ∀ s z : ℝ, 0 < s → s ≤ z →
      Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z - Work.Elliptic.Fstar (Work.Spaces.pz Ψ) s
        = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.pz Ψ)) r :=
    fun s z hs hsz => Fstar_chain_pz hsmd hmemd hs hsz
  refine Fstar_eq_zero_of_bslOp' hα hα2 hslice h0 h1 hz0 ?_ ?_ ?_ hchain0 hchain1 hdec hzsq
  · -- the `∂_zzΨ` slot
    intro z hz
    have hcont : ContinuousOn (Function.uncurry (fun z' θ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ))
        Work.FTS.EllipticEst.Q0 := by
      have hmul : Function.uncurry (fun z' θ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
          = (fun p : ℝ × ℝ => p.1 ^ 2) * Function.uncurry (Work.Spaces.pzIter 2 Ψ) := by
        funext p; rfl
      rw [hmul]
      exact (continuous_fst.continuousOn.pow 2).mul
        (fun x hx => ((hsm.pzIter 2) x hx).continuousWithinAt)
    have hg := Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2
      (g := fun z' θ => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) hcont hmemA hz
    refine hg.const_mul (α ^ 2) |>.congr ?_
    filter_upwards with θ
    ring
  · -- the `∂_zΨ` slot
    intro z hz
    have hg := Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2
      (g := Work.Spaces.DzIter 1 Ψ)
      (fun x hx => ((hsm.DzIter 1) x hx).continuousWithinAt) hmemB hz
    refine hg.const_mul (α * (5 + α)) |>.congr ?_
    filter_upwards with θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    ring
  · -- the `Lzero` slot
    intro z hz
    exact Work.Elliptic.integrableOn_Lzero_mul_sinCos2 Ψ z (hslice z hz)

end Work.FTS.ClassC
