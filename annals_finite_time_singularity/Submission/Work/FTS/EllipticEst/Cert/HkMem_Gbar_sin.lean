/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Ḡ(α,F)·sin 2θ ∈ ℋ^k` for the elliptic source `F = L(Ψ)`

This module proves `Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin`: the singular part
`Ḡ(α,F)(z)·sin 2θ` of the elliptic estimates of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

belongs to the weighted space `ℋ^k` (`Work.Spaces.HkMem`) for every datum
`Work.FTS.EllipticEst.EllHyp α k F Ψ`.

## Proof

The source `F = bslOp α Ψ` is *not* `SmoothNbhd` (the term `tan θ · Ψ` of `L₀` is not smooth
at `θ = π/2`), but it is `C^∞` on the **open** quadrant `Q0 = (0,∞) × (0,π/2)`, which is
exactly the hypothesis of the open-quadrant chain assembled in
`Cert/GbarSin/OpenCore.lean`.  Two reduction steps connect the abstract datum `(F, Ψ)` of
`EllHyp` with that chain:

* `Fstar_bslOp_eq_of_sol`: on `(0,∞)` the angular moment `F_*` of `F` agrees with that of
  `bslOp α Ψ` (the two integrands agree on the open angle interval, an a.e.-null set);
* consequently `Gbar α F = Gbar α (bslOp α Ψ)` on `(0,∞)`
  (`Gbar_congr_of_fstar_eq`), so the two targets agree on `(0,∞) × Iθ` and
  `Work.Coercivity.HkMem_congr_Ioi` transfers membership;
* `HkMem_congr_Q0` gives `bslOp α Ψ ∈ ℋ^k` from `F ∈ ℋ^k`, and `SmoothOpen_bslOp` gives the
  smoothness on the open quadrant.

For a `SmoothOpen` source the membership is produced here by
`Work.FTS.LocData.HkMem_of_majorant` with the majorant
`M z θ = (π/2)·Kang k·w(z)²·Σ_{j≤k} (D_z^j Ḡ z)²`:

* the pointwise domination `HkIntegrand (Ḡ·sin 2θ) ≤ Kang k·w²·Σ_j (D_z^j Ḡ)²` is
  `gbar_HkIntegrand_target_le`;
* the `θ`-slices of `M` are constant, and the integrability of `z ↦ ∫_θ M z θ` is
  `Gbar_rDzIter_bound` (the weighted Hardy estimate);
* the continuity of the integrand on `Q0` follows from the continuity of the radial
  derivatives of `Ḡ` (`continuousOn_HkIntegrand_GbarSin`), which rests on the exact radial
  identity `D_z^j Ḡ = -(3/(4α))·HarOp (5/α) (F_*(D_z^j F))` on `(0,∞)`
  (`rDzIter_Gbar_eq_open`) and on the continuity of the primitive of an `L¹`-function
  (`continuousOn_primitive_Ioi`).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Polynomial
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.OpenCore
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.Gbar_congr_of_fstar_eq
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Work.FTS.EllipticEst.Cert.GbarSin

/-! ## The reduction of the source to `bslOp α Ψ` -/

/-- **The angular moment of the source depends only on the open quadrant.**  If `F` solves
(PolarBSL) with stream function `Ψ`, i.e. `F = bslOp α Ψ` on the open quadrant, then for every
`s > 0` the angular moment `F_*` of `F` agrees with that of `bslOp α Ψ`: the two integrands
differ at most at the endpoints `θ = 0`, `θ = π/2` of `Iθ`, a null set. -/
theorem Fstar_bslOp_eq_of_sol (α : ℝ) {F Ψ : ℝ → ℝ → ℝ} (h : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ s, 0 < s → Work.Elliptic.Fstar F s = Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) s := by
  intro s hs
  have hae : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  calc Work.Elliptic.Fstar F s
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), F s θ * Work.Elliptic.sinCos2 θ := by
        rw [Work.Elliptic.Fstar]
        exact (MeasureTheory.setIntegral_congr_set hae).symm
    _ = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.bslOp α Ψ s θ * Work.Elliptic.sinCos2 θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
        rw [← h.1 s hs θ hθ.1 hθ.2]
    _ = Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) s := by
        rw [Work.Elliptic.Fstar]
        exact MeasureTheory.setIntegral_congr_set hae

/-- The two targets agree on the positive half-line as soon as the `Ḡ` agree there. -/
theorem target_eq_on_Ioi (α : ℝ) {F G : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → Work.Elliptic.Gbar α F z = Work.Elliptic.Gbar α G z) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      Work.Elliptic.Gbar α F z * Real.sin (2 * θ)
        = Work.Elliptic.Gbar α G z * Real.sin (2 * θ) := by
  intro z hz θ _
  rw [h z hz]

/-! ## Continuity of the radial derivatives of `Ḡ` -/

/-- **Continuity of the Hardy operator on `(0,∞)`** for an `L¹`-loc integrand: this is the
continuity of the primitive (`continuousOn_primitive_Ioi`) times the continuous factor
`z ↦ z^(-β)`.  In particular no continuity of `u` itself is needed. -/
theorem HarOp_continuousOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    ContinuousOn (fun z => HarOp (bet α) (Uj F j) z) (Set.Ioi 0) := by
  have hprim : ContinuousOn
      (fun z => ∫ s in (0 : ℝ)..z, s ^ (bet α - 1) * Uj F j s) (Set.Ioi 0) :=
    continuousOn_primitive_Ioi fun z hz => intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hj hz
  have hzpow : ContinuousOn (fun z : ℝ => z ^ (-(bet α))) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))
  have hfun : (fun z => HarOp (bet α) (Uj F j) z)
      = fun z => z ^ (-(bet α)) * ∫ s in (0 : ℝ)..z, s ^ (bet α - 1) * Uj F j s := by
    funext z; rfl
  rw [hfun]
  exact hzpow.mul hprim

/-- **The radial derivatives of `Ḡ` are continuous on `(0,∞)`**: by the exact radial identity
`D_z^j Ḡ = -(3/(4α))·HarOp (5/α)(F_*(D_z^j F))` and `HarOp_continuousOn`. -/
theorem rDzIter_Gbar_continuousOn (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    ContinuousOn (fun z => rDzIter j (Work.Elliptic.Gbar α F) z) (Set.Ioi 0) := by
  have hH := HarOp_continuousOn α hα hα1 k F hF hmem j hj
  refine (hH.const_mul (-(3 / (4 * α)))).congr ?_
  intro z hz
  exact rDzIter_Gbar_eq_open α hα hα1 k F hF hmem j hj hz

/-! ## Continuity of the `ℋ^k`-integrand of the target on the open quadrant -/

/-- The angular profile `D_θ^i (sin 2θ)` is continuous. -/
theorem continuousOn_sinIter (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => sinIter i p.2) Q0 := by
  have hpoly : Continuous (fun t : ℝ => (sinPoly i).eval t) := Polynomial.continuous _
  have hfun : (fun p : ℝ × ℝ => sinIter i p.2)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * (sinPoly i).eval (Real.cos (2 * p.2)) := by
    funext p; exact sinIter_eq_sinPoly i p.2
  rw [hfun]
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn.mul
    (hpoly.comp (Real.continuous_cos.comp (continuous_const.mul continuous_snd))).continuousOn

/-- The weight `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have h2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [h2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hfun]
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- **The `ℋ^k`-integrand of `Ḡ(α,F)·sin 2θ` is continuous on the open quadrant** for a source
`F` which is `C^∞` on `Q0` and lies in `ℋ^k`.

Indeed on `Q0` the factorisations
`D_z^i(Ḡ·sin 2θ) = (D_z^i Ḡ)·sin 2θ` and `D_z^j D_θ^i(Ḡ·sin 2θ) = (D_z^j Ḡ)·D_θ^i(sin 2θ)`
exhibit the integrand as a finite sum of products of continuous functions of `(z,θ)`. -/
theorem continuousOn_HkIntegrand_GbarSin (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ)
    (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) p.1 p.2) Q0 := by
  have hz : ∀ i, i ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => rDzIter i (Work.Elliptic.Gbar α F) p.1) Q0 := fun i hi =>
    (rDzIter_Gbar_continuousOn α hα hα1 k F hF hmem i hi).comp continuousOn_fst
      (fun p hp => hp.1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Q0 := by fun_prop
  have hwdiv : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1
        / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Q0 := continuousOn_wdivsin_Q0
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := continuousOn_Wt α
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), (rDzIter i (Work.Elliptic.Gbar α F) p.1
          * Real.sin (2 * p.2)
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (rDzIter j (Work.Elliptic.Gbar α F) p.1 * sinIter i p.2
                * Work.Spaces.Wt α p.1 p.2) ^ 2 else 0)) ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum _ fun i hi => ?_
      exact (((hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul hsin).mul hwdiv).pow 2
    · refine continuousOn_finsetSum _ fun i _ =>
        continuousOn_finsetSum _ fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact (((hz j (by omega)).mul (continuousOn_sinIter i)).mul hWt).pow 2
      · simp only [if_neg hc]
        exact continuousOn_const
  · intro p hp
    simp only [Work.Spaces.HkIntegrand]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [gbar_DzIter_target_eq α F i p.1 p.2]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, if_pos hc, gbar_mixed_target_eq α F j i p.1 p.2]
      · rw [if_neg hc, if_neg hc]

/-! ## Membership in `ℋ^k` for a `C^∞` source on the open quadrant -/

/-- **`Ḡ(α,F)·sin 2θ ∈ ℋ^k`** for a source `F` which is `C^∞` on the open quadrant and lies
in `ℋ^k`.

The majorant is `M z θ = Kang k·w(z)²·Σ_{j≤k}(D_z^j Ḡ z)²`, whose `θ`-slices are
constant (`integrableOn_const`) and whose slice integral is integrable by the per-order weighted
bound `Gbar_rDzIter_bound`. -/
theorem HkMem_target_of_smoothOpen (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  set M : ℝ → ℝ → ℝ := fun z θ => gbar_Kang k * (Work.Spaces.w z) ^ 2 *
    ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 with hM
  have hIθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine Work.FTS.LocData.HkMem_of_majorant (α := α) (k := k)
    (f := fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) (M := M)
    (continuousOn_HkIntegrand_GbarSin α hα hα1 k F hF hmem) ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are constant in `θ`
    intro z _
    exact MeasureTheory.integrableOn_const hIθ_ne_top
  · -- the slice integral of the majorant is integrable
    have hconst : ∀ z : ℝ, (fun θ : ℝ => M z θ) = fun _ : ℝ => gbar_Kang k *
        (Work.Spaces.w z) ^ 2 * ∑ j ∈ Finset.range (k + 1),
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
      intro z
      funext θ
      rw [hM]
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, M z θ)
        = fun z => (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) := by
      funext z
      rw [hconst z, gbar_integral_Iθ_const]
      ring
    rw [hfun]
    have hsum : Integrable (fun z => ∑ j ∈ Finset.range (k + 1),
        (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      gbar_integrable_finsetSum _ _ _ fun j hj =>
        ((Gbar_rDzIter_bound α hα hα1 k F hF hmem j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1.const_mul (gbar_Kang k)).const_mul _
    refine hsum.congr ?_
    filter_upwards with z
    simp only [Finset.mul_sum]
  · -- the pointwise domination
    intro z hz θ hθ
    exact gbar_HkIntegrand_target_le α hα hα1 k F z θ hz hθ

/-! ## The target theorem -/

theorem HkMem_Gbar_sin (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  have hα1 : α ≤ 1 := by linarith
  -- the source `bslOp α Ψ`, which is `C^∞` on the open quadrant and in `ℋ^k`
  have hOpen : SmoothOpen (Work.Elliptic.bslOp α Ψ) := SmoothOpen_bslOp_int α Ψ hHyp.smooth
  have hMem : Work.Spaces.HkMem α k (Work.Elliptic.bslOp α Ψ) :=
    HkMem_congr_Q0 α k hHyp.memF fun z hz θ hθ =>
      (hHyp.sol.1 z hz θ hθ.1 hθ.2).symm
  have hTarget := HkMem_target_of_smoothOpen α hα hα1 k (Work.Elliptic.bslOp α Ψ) hOpen hMem
  -- the `F_*`-agreement turns the two targets into one
  have hfs : ∀ s, 0 < s →
      Work.Elliptic.Fstar F s = Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) s :=
    Fstar_bslOp_eq_of_sol α hHyp.sol
  refine Work.Coercivity.HkMem_congr_Ioi α k hTarget ?_
  intro z hz θ hθ
  rw [Gbar_congr_of_fstar_eq α hfs z hz]

end Work.FTS.EllipticEst.Cert
