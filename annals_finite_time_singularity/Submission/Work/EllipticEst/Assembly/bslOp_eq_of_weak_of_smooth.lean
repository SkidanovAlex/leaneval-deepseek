/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise equality from the weak (test-function) form of the `bslOp` pairing

`Work.EllipticEst.Assembly.bslOp_eq_of_weak_of_smooth`: if `Φ` and `F` are `C^∞` on the open
quadrant `Q0 = (0,∞) × (0,π/2)` and the *weak* relation

  `∫_{Q0} Φ·(L φ)·w = ∫_{Q0} F·φ·w`,   `L = bslOp α`,   `w = z^{(5-α)/α} cos θ`,

holds for every `C^∞` compactly supported test function `φ` with `tsupport φ ⊆ Q0`, then `Φ`
solves the elliptic equation pointwise on the open quadrant: `L Φ = F`.

Proof.  `Work.EllipticEst.Assembly.bslOp_pairing_self` says that `L` is self-adjoint for the
weight `w` (the weight that puts `L` into divergence form), so the hypothesis collapses to

  `∫_{Q0} (L Φ - F)·φ·w = 0`  for every test function `φ`.

The weighted residual `G = (L Φ - F)·w` is continuous on the open quadrant, so the fundamental
lemma of the calculus of variations
(`Work.EllipticEst.Assembly.eq_zero_of_test_integral_zero`) gives `G = 0` on `Q0`, and `w > 0`
there, whence `L Φ = F` pointwise.  The only non-trivial point is the algebraic passage from
the equality of the two *integrals* `∫ (LΦ)φw` and `∫ Fφw` to the vanishing of
`∫ ((LΦ) - F)·φ·w`: both integrands are supported on the compact set `tsupport φ ⊆ Q0`, on
which they are continuous, so they are integrable there and the set integral is additive.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.EllipticEst.Assembly.bslOp_pairing_self
import Submission.Work.EllipticEst.Assembly.eq_zero_of_test_integral_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem bslOp_eq_of_weak_of_smooth {α : ℝ} (hα : 0 < α) {F Φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          Φ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
            F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = F z θ := by
  have hQ0 : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- The weighted residual is orthogonal to every test function.
  have hres : ∀ ψ : ℝ × ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      tsupport ψ ⊆ Work.FTS.EllipticEst.Q0 →
      ∫ x in Work.FTS.EllipticEst.Q0,
        ((Work.Elliptic.bslOp α Φ x.1 x.2 - F x.1 x.2)
          * (x.1 ^ ((5 - α) / α) * Real.cos x.2)) * ψ x = 0 := by
    intro ψ hψ hcψ hsubψ
    set φc : ℝ → ℝ → ℝ := Function.curry ψ with hφcdef
    have huncurry : Function.uncurry φc = ψ := by
      rw [hφcdef, Function.uncurry_curry]
    have huncurry_apply : ∀ p : ℝ × ℝ, φc p.1 p.2 = ψ p := fun p => by
      simpa only [Function.uncurry_def] using congrFun huncurry p
    have hweakφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φc) := fun n => by
      rw [huncurry]; exact hψ n
    have hφc_smooth : Work.FTS.EllipticEst.SmoothOpen φc := by
      refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
      rw [huncurry]
      exact (hψ n).contDiffOn
    have hcφc : HasCompactSupport (Function.uncurry φc) := by rw [huncurry]; exact hcψ
    have hsubφc : tsupport (Function.uncurry φc) ⊆ Work.FTS.EllipticEst.Q0 := by
      rw [huncurry]; exact hsubψ
    have hψcont : Continuous ψ := contDiff_zero.mp (hψ 0)
    -- the two pairing identities
    have hpair :=
      Work.EllipticEst.Assembly.bslOp_pairing_self hα hΦ hφc_smooth hcφc hsubφc
    have hwk := hweak φc hweakφ hcφc hsubφc
    -- ## the two integrands and their difference
    let A : ℝ × ℝ → ℝ := fun p => Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
    let B : ℝ × ℝ → ℝ := fun p => F p.1 p.2 * φc p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
    have hkey : (∫ p in Work.FTS.EllipticEst.Q0, A p) =
        ∫ p in Work.FTS.EllipticEst.Q0, B p := by
      show (∫ p in Work.FTS.EllipticEst.Q0,
          Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = _
      exact hpair.trans hwk
    -- ## continuity on the open quadrant
    have hcurry_cont : ContinuousOn (fun p : ℝ × ℝ => φc p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      rw [← Function.uncurry_def, huncurry]
      exact hψcont.continuousOn
    have hAcont : ContinuousOn A Work.FTS.EllipticEst.Q0 := by
      show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) _
      exact ((continuousOn_bslOp_smoothOpen hΦ).mul hcurry_cont).mul
        (continuousOn_pairWeight α)
    have hBcont : ContinuousOn B Work.FTS.EllipticEst.Q0 := by
      show ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 * φc p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) _
      exact (hF.continuousOn.mul hcurry_cont).mul (continuousOn_pairWeight α)
    -- ## vanishing off the compact support of `ψ`
    have hAsupp : ∀ p ∉ tsupport ψ, A p = 0 := by
      intro p hp
      have h0 : ψ p = 0 := image_eq_zero_of_notMem_tsupport hp
      show Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
      rw [huncurry_apply p, h0, mul_zero, zero_mul]
    have hBsupp : ∀ p ∉ tsupport ψ, B p = 0 := by
      intro p hp
      have h0 : ψ p = 0 := image_eq_zero_of_notMem_tsupport hp
      show F p.1 p.2 * φc p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
      rw [huncurry_apply p, h0, mul_zero, zero_mul]
    have hGsupp : ∀ p ∉ tsupport ψ,
        ((Work.Elliptic.bslOp α Φ p.1 p.2 - F p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) * ψ p = 0 := by
      intro p hp
      rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
    -- ## move the integrals to the compact support of `ψ`
    have hAK : (∫ p in Work.FTS.EllipticEst.Q0, A p) = ∫ p in tsupport ψ, A p :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ0 hsubψ
        (fun p hp => hAsupp p hp.2)
    have hBK : (∫ p in Work.FTS.EllipticEst.Q0, B p) = ∫ p in tsupport ψ, B p :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ0 hsubψ
        (fun p hp => hBsupp p hp.2)
    -- ## integrability on the compact support
    have hKcomp : IsCompact (tsupport ψ) := hcψ
    have hKmeas : MeasurableSet (tsupport ψ) := hKcomp.isClosed.measurableSet
    have hAKint : IntegrableOn A (tsupport ψ) :=
      (hAcont.mono hsubψ).integrableOn_compact hKcomp
    have hBKint : IntegrableOn B (tsupport ψ) :=
      (hBcont.mono hsubψ).integrableOn_compact hKcomp
    -- ## the conclusion
    have hzero : (∫ p in tsupport ψ,
        ((Work.Elliptic.bslOp α Φ p.1 p.2 - F p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) * ψ p) = 0 := by
      calc (∫ p in tsupport ψ,
            ((Work.Elliptic.bslOp α Φ p.1 p.2 - F p.1 p.2)
              * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) * ψ p)
          = ∫ p in tsupport ψ, (A p - B p) := by
              refine setIntegral_congr_fun hKmeas (fun p _ => ?_)
              show ((Work.Elliptic.bslOp α Φ p.1 p.2 - F p.1 p.2)
                  * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) * ψ p
                = Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
                    * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
                  - F p.1 p.2 * φc p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
              rw [huncurry_apply p]
              ring
        _ = (∫ p in tsupport ψ, A p) - ∫ p in tsupport ψ, B p :=
              integral_sub hAKint hBKint
        _ = (∫ p in Work.FTS.EllipticEst.Q0, A p)
              - ∫ p in Work.FTS.EllipticEst.Q0, B p := by rw [hAK, hBK]
        _ = 0 := by rw [hkey, sub_self]
    have hGK : (∫ x in Work.FTS.EllipticEst.Q0,
          ((Work.Elliptic.bslOp α Φ x.1 x.2 - F x.1 x.2)
            * (x.1 ^ ((5 - α) / α) * Real.cos x.2)) * ψ x)
        = ∫ x in tsupport ψ,
          ((Work.Elliptic.bslOp α Φ x.1 x.2 - F x.1 x.2)
            * (x.1 ^ ((5 - α) / α) * Real.cos x.2)) * ψ x :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ0 hsubψ
        (fun p hp => hGsupp p hp.2)
    rw [hGK]
    exact hzero
  -- ## the variational lemma
  have hcont : ContinuousOn (fun x : ℝ × ℝ =>
      (Work.Elliptic.bslOp α Φ x.1 x.2 - F x.1 x.2)
        * (x.1 ^ ((5 - α) / α) * Real.cos x.2)) Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_bslOp_smoothOpen hΦ).sub hF.continuousOn).mul (continuousOn_pairWeight α)
  have hzero := eq_zero_of_test_integral_zero Work.FTS.EllipticEst.isOpen_Q0 hcont hres
  intro z hz θ hθ0 hθ1
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have h1 : (Work.Elliptic.bslOp α Φ z θ - F z θ)
      * (z ^ ((5 - α) / α) * Real.cos θ) = 0 := hzero (z, θ) hmem
  have hw : z ^ ((5 - α) / α) * Real.cos θ ≠ 0 :=
    mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hz _))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩))
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hw)

end Work.EllipticEst.Assembly
